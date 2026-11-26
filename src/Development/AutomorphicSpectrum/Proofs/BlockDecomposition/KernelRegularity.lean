module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidFactorization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionFormula
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inner_cls_eq {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {a b : Mat n → V} (ha : MemLp (fun y : G n => a y.val) 2 μ)
    (hb : MemLp (fun y : G n => b y.val) 2 μ) :
    ⟪cls μ a, cls μ b⟫_ℂ = ∫ y : G n, ⟪a y.val, b y.val⟫_ℂ ∂μ := by
  have e1 : cls μ a = ha.toLp _ := dif_pos ha
  have e2 : cls μ b = hb.toLp _ := dif_pos hb
  rw [e1, e2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem integrable_inner_of_memLp {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {a b : G n → V} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun y => ⟪a y, b y⟫_ℂ) μ := by
  have h := L2.integrable_inner (𝕜 := ℂ) (ha.toLp _) (hb.toLp _)
  refine h.congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem integrable_adjoint_apply {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    {A : G n → (V →L[ℂ] V)} {φ : G n → V} (hA : ∀ v, MemLp (fun y => A y v) 2 μ) (hφ : MemLp φ 2 μ) :
    Integrable (fun y => ContinuousLinearMap.adjoint (A y) (φ y)) μ := by
  classical
  let b := stdOrthonormalBasis ℂ V
  have key : (fun y => ContinuousLinearMap.adjoint (A y) (φ y)) =
      fun y => ∑ i, ⟪A y (b i), φ y⟫_ℂ • b i := by
    funext y
    rw [← b.sum_repr' (ContinuousLinearMap.adjoint (A y) (φ y))]
    simp only [ContinuousLinearMap.adjoint_inner_right]
  rw [key]
  exact integrable_finsetSum _ fun i _ => (integrable_inner_of_memLp μ (hA (b i)) hφ).smul_const _

theorem actFormula (hLt : LtSob) (hComm : LtComm) : ActFormula := by
  intro n _ _ μ _ E _ Ω T F c hStd h A hRow f hf hCpt f' hSob' hSec' hcls x hx
  have hStd0 := hStd
  obtain ⟨hLg, hUni, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, -⟩ := hStd0
  obtain ⟨-, -, -, -, -, -, hCptSob, -⟩ := hCS
  have hdet : x.det ≠ 0 := hx
  let x₀ : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hdet
  have hx₀ : x₀.val = x := rfl
  have hfS : Sob μ f := (hCptSob n μ E.V hLg hRC f hf.1 hCpt).1
  have hmul : ∀ g ∈ GLs n, x * g ∈ GLs n := fun g hg => by
    have hg' : g.det ≠ 0 := hg
    show (x * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdet hg'
  have hφS : Sob μ (lTr x₀ f) := (hLt n μ E.V hLg hUni hRC x₀ f hfS).1
  have hψS : Sob μ (lTr x₀ f') := (hLt n μ E.V hLg hUni hRC x₀ f' hSob').1
  have hφE : IsSec E (lTr x₀ f) := fun g hg k => by
    show f (x₀.val * (g * k.1)) = E.ρ k⁻¹ (f (x₀.val * g))
    rw [hx₀, ← mul_assoc]
    exact hf.2 _ (hmul g hg) k
  have hψE : IsSec E (lTr x₀ f') := fun g hg k => by
    show f' (x₀.val * (g * k.1)) = E.ρ k⁻¹ (f' (x₀.val * g))
    rw [hx₀, ← mul_assoc]
    exact hSec' _ (hmul g hg) k
  have hclsT : cls μ (lTr x₀ f') = F.Φ h (cls μ (lTr x₀ f)) :=
    hComm n μ E Ω T F c hStd h x₀ f f' hfS hSob' hcls
  have hφL : MemLp (fun y : G n => lTr x₀ f y.val) 2 μ := hφS.2 []
  have hAL : ∀ v, MemLp (fun y : G n => A y.val v) 2 μ := fun v => (hRow v).1.2 []
  have hint : Integrable
      (fun y : G n => ContinuousLinearMap.adjoint (A y.val) (lTr x₀ f y.val)) μ :=
    integrable_adjoint_apply μ (A := fun y : G n => A y.val) hAL hφL
  refine ext_inner_left ℂ fun v => ?_
  have hrow := (hRow v).2.2 (lTr x₀ f) (lTr x₀ f') hφS hφE hψS hψE hclsT
  rw [inner_cls_eq μ (hAL v) hφL] at hrow
  have hval : lTr x₀ f' 1 = f' x := by
    show f' (x₀.val * 1) = f' x
    rw [hx₀, mul_one]
  rw [hval] at hrow
  rw [← hrow]
  show ⟪v, ∫ y : G n, ContinuousLinearMap.adjoint (A y.val) (f (x * y.val)) ∂μ⟫_ℂ = _
  have hint' : Integrable (fun y : G n => ContinuousLinearMap.adjoint (A y.val) (f (x * y.val))) μ := hint
  rw [← integral_inner hint' v]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show ⟪v, ContinuousLinearMap.adjoint (A y.val) (f (x * y.val))⟫_ℂ = ⟪A y.val v, f (x₀.val * y.val)⟫_ℂ
  rw [hx₀, ContinuousLinearMap.adjoint_inner_right]

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_action_formula : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm → GlobalTheory.CompanionTheory.KerFc.ActFormula := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.actFormula | exact GlobalTheory.CompanionTheory.KerFc.actFormula | (intros; apply GlobalTheory.CompanionTheory.KerFc.actFormula <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiResolventIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiResolventIdentity
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem toC0_eq_of_coe (p : C₀(ℝ, ℂ)) (f : ℝ → ℂ) (h : ∀ y, p y = f y) : toC0 f = p := by
  have hf : f = ⇑p := funext fun y => (h y).symm
  subst hf
  have hc : Continuous (⇑p) ∧ Tendsto (⇑p) (cocompact ℝ) (𝓝 0) := ⟨p.continuous, p.zero_at_infty'⟩
  unfold toC0
  rw [dite_eq_left hc]
  ext y
  rfl

theorem exists_resolvent_C0 : ∃ r : C₀(ℝ, ℂ), ∀ y, r y = (((1 + y ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hpos : ∀ y : ℝ, (1 + y ^ 2) ≠ 0 := fun y => by positivity
  have hcont : Continuous (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) := by
    refine Complex.continuous_ofReal.comp ?_
    exact (by fun_prop : Continuous fun y : ℝ => 1 + y ^ 2).inv₀ hpos
  have hat : Tendsto (fun y : ℝ => 1 + y ^ 2) (cocompact ℝ) atTop := by
    have h1 : Tendsto (fun y : ℝ => ‖y‖ ^ 2) (cocompact ℝ) atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_norm_cocompact_atTop
    have h2 : Tendsto (fun y : ℝ => 1 + ‖y‖ ^ 2) (cocompact ℝ) atTop :=
      tendsto_atTop_add_const_left _ 1 h1
    simpa using h2
  have htend : Tendsto (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) (cocompact ℝ) (𝓝 0) := by
    have h3 : Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) (cocompact ℝ) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hat
    have h4 : Tendsto (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) (cocompact ℝ) (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h3
    rwa [Complex.ofReal_zero] at h4
  exact ⟨⟨⟨_, hcont⟩, htend⟩, fun y => rfl⟩

theorem phiRes_holds : PhiRes := by
  intro n _ _ μ _ E _ Ω T F c hS g T₀ hb N _
  obtain ⟨-, -, -, -, -, -, -, -, -, hPW, -⟩ := hS
  have h0 := (hPW c g T₀ hb).1 0
  simp only [pow_zero, one_mul] at h0
  obtain ⟨r, hr⟩ := exists_resolvent_C0
  have hT : F.Φ r = T := F.res r hr
  let q : C₀(ℝ, ℂ) := ⟨⟨hg c g, h0.1⟩, h0.2⟩
  have hq : ∀ y, q y = hg c g y := fun y => rfl
  have key : ∀ M : ℕ, ∃ p : C₀(ℝ, ℂ),
      (∀ y, p y = ((((1 + y ^ 2) ^ M)⁻¹ : ℝ) : ℂ) * hg c g y) ∧ F.Φ p = F.Φ q * T ^ M := by
    intro M
    induction M with
    | zero => exact ⟨q, fun y => by simp [hq], by simp⟩
    | succ M ih =>
      obtain ⟨p, hp, hΦ⟩ := ih
      refine ⟨p * r, fun y => ?_, ?_⟩
      · have : (p * r) y = p y * r y := rfl
        rw [this, hp, hr, pow_succ (1 + y ^ 2) M, mul_inv]
        push_cast
        ring
      · rw [F.map_mul, hΦ, hT, pow_succ, mul_assoc]
  obtain ⟨p, hp, hΦ⟩ := key N
  rw [toC0_eq_of_coe p _ hp, toC0_eq_of_coe q _ hq, hΦ]

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiResolventIdentityStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_resolvent_identity : GlobalTheory.CompanionTheory.KerFc.PhiRes := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.phiRes_holds | exact GlobalTheory.CompanionTheory.KerFc.phiRes_holds | (intros; apply GlobalTheory.CompanionTheory.KerFc.phiRes_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentity
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem secondCountable_G (n : ℕ) : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Mat n)).secondCountableTopology

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n := by
  have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  exact this.ne_zero

theorem continuous_lg (hL : LgFacts) {n : ℕ} : Continuous (fun y : G n => lg y.val) := by
  have h1 : ContinuousOn (lg (n := n)) (GLs n) := ((hL n).2.2.2.1).continuousOn
  exact h1.comp_continuous Units.continuous_val val_mem_GLs

theorem locallyCompact_G (hL : LgFacts) (n : ℕ) : LocallyCompactSpace (G n) := by
  haveI : WeaklyLocallyCompactSpace (G n) := ⟨fun x => ⟨{y : G n | lg y.val ≤ lg x.val + 1},
    (hL n).2.2.2.2.1 _, by
      have : {y : G n | lg y.val < lg x.val + 1} ∈ 𝓝 x :=
        (isOpen_lt (continuous_lg hL) continuous_const).mem_nhds (by simp)
      exact Filter.mem_of_superset this (fun y (hy : lg y.val < _) => show lg y.val ≤ _ from le_of_lt hy)⟩⟩
  infer_instance

theorem sigmaCompact_G (hL : LgFacts) (n : ℕ) : SigmaCompactSpace (G n) := by
  refine ⟨⟨fun k : ℕ => {y : G n | lg y.val ≤ k}, fun k => (hL n).2.2.2.2.1 _, ?_⟩⟩
  ext y
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  obtain ⟨k, hk⟩ := exists_nat_ge (lg y.val)
  exact ⟨k, hk⟩

theorem cls_inner {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {f f' : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hf' : MemLp (fun y : G n => f' y.val) 2 μ) :
    ⟪cls μ f, cls μ f'⟫_ℂ = ∫ y : G n, ⟪f y.val, f' y.val⟫_ℂ ∂μ := by
  have e1 : cls μ f = hf.toLp _ := by
    unfold cls; exact dif_pos hf
  have e2 : cls μ f' = hf'.toLp _ := by
    unfold cls; exact dif_pos hf'
  rw [e1, e2, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hf'.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem bump_complex {g : ℝ → ℝ} {T₀ : ℝ} (hg : IsBump g T₀) :
    Continuous (fun t => (g t : ℂ)) ∧ HasCompactSupport (fun t => (g t : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp hg.1.continuous, ?_⟩
  refine HasCompactSupport.intro (isCompact_Icc (a := -|T₀|) (b := |T₀|)) (fun t ht => ?_)
  have h1 : |T₀| < |t| := by
    by_contra h
    exact ht (abs_le.1 (not_lt.1 h))
  have h2 : g t = 0 := hg.2.2 t (lt_of_le_of_lt (le_abs_self _) h1)
  simp [h2]

theorem phi_integral {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : C₀(ℝ, ℂ) →L[ℂ] (H →L[ℂ] H)) (b : H) (hFc : Fcurve) {g : ℝ → ℝ} {T₀ : ℝ} (hg : IsBump g T₀)
    (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∀ v : H, ⟪v, Φ (∫ t, (g t : ℂ) • toC0 (wv c N 0 t)) b⟫_ℂ =
      ∫ t, (g t : ℂ) * ⟪v, Φ (toC0 (wv c N 0 t)) b⟫_ℂ := by
  have hcurve : Continuous (fun t => toC0 (wv c N 0 t)) :=
    continuous_iff_continuousAt.2 fun t =>
      (hFc c N 0 (by omega) t).2.continuousAt
  have hi : Integrable (fun t => (g t : ℂ) • toC0 (wv c N 0 t)) :=
    ((bump_complex hg).1.smul hcurve).integrable_of_hasCompactSupport
      ((bump_complex hg).2.smul_right)
  let L : C₀(ℝ, ℂ) →L[ℂ] H := (ContinuousLinearMap.apply ℂ H b).comp Φ
  have hL : ∀ t, L ((g t : ℂ) • toC0 (wv c N 0 t)) = (g t : ℂ) • Φ (toC0 (wv c N 0 t)) b := by
    intro t
    simp [L]
  have hi' : Integrable (fun t => (g t : ℂ) • Φ (toC0 (wv c N 0 t)) b) := by
    simpa only [hL] using L.integrable_comp hi
  have e : Φ (∫ t, (g t : ℂ) • toC0 (wv c N 0 t)) b = ∫ t, (g t : ℂ) • Φ (toC0 (wv c N 0 t)) b := by
    have := L.integral_comp_comm hi
    simp only [hL] at this
    rw [this]
    rfl
  intro v
  rw [e, ← integral_inner hi' v]
  simp only [inner_smul_right]

theorem test_fubini {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (hLg : LgFacts) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {W : ℝ → G n → V} (hW : Continuous (Function.uncurry W)) {Ψ : G n → V} (hΨ : Continuous Ψ)
    (hΨc : HasCompactSupport Ψ) {γ : ℝ → ℂ} (hγ : Continuous γ) (hγc : HasCompactSupport γ) :
    ∫ y, ⟪Ψ y, ∫ t, γ t • W t y⟫_ℂ ∂μ = ∫ t, γ t * ∫ y, ⟪Ψ y, W t y⟫_ℂ ∂μ := by
  haveI := secondCountable_G n
  haveI := sigmaCompact_G hLg n
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  have h1 : ∀ y, ⟪Ψ y, ∫ t, γ t • W t y⟫_ℂ = ∫ t, γ t * ⟪Ψ y, W t y⟫_ℂ := by
    intro y
    have hc : Continuous (fun t => W t y) := hW.comp (by fun_prop : Continuous fun t : ℝ => (t, y))
    have hi : Integrable (fun t => γ t • W t y) :=
      (hγ.smul hc).integrable_of_hasCompactSupport hγc.smul_right
    rw [← integral_inner hi]
    simp only [inner_smul_right]
  simp only [h1]
  have hcont : Continuous (Function.uncurry fun (y : G n) (t : ℝ) => γ t * ⟪Ψ y, W t y⟫_ℂ) := by
    have h2 : Continuous (fun p : G n × ℝ => W p.2 p.1) :=
      hW.comp (by fun_prop : Continuous fun p : G n × ℝ => (p.2, p.1))
    have h3 : Continuous (fun p : G n × ℝ => Ψ p.1) := hΨ.comp continuous_fst
    exact (hγ.comp continuous_snd).mul (h3.inner h2)
  have hint : Integrable (Function.uncurry fun (y : G n) (t : ℝ) => γ t * ⟪Ψ y, W t y⟫_ℂ) (μ.prod volume) := by
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (hΨc.isCompact.prod hγc.isCompact) (fun p hp => ?_)
    rcases p with ⟨y, t⟩
    by_cases hy : y ∈ tsupport Ψ
    · have ht : t ∉ tsupport γ := fun ht => hp ⟨hy, ht⟩
      simp [Function.uncurry, image_eq_zero_of_notMem_tsupport ht]
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
  rw [integral_integral_swap hint]
  simp only [integral_const_mul]

theorem waveInt : WaveInt := by
  intro n _ _ μ _ E _ Ω T F c hS g T₀ hg N b U hN hW hU f' hf' hcls x hx
  obtain ⟨hLg, -, -, -, -, -, -, hCS, -, hPW, -⟩ := hS
  have hFc : Fcurve := hCS.2.2.1
  haveI := secondCountable_G n
  haveI := locallyCompact_G hLg n
  obtain ⟨hγ, hγc⟩ := bump_complex hg
  set γ : ℝ → ℂ := fun t => (g t : ℂ) with hγdef

  have hUc : Continuous (Function.uncurry fun (t : ℝ) (y : G n) => U t y.val) := by
    have h1 : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ GLs n) := hW.1.continuousOn
    exact h1.comp_continuous (f := fun p : ℝ × G n => (p.1, p.2.val))
      (continuous_fst.prodMk (Units.continuous_val.comp continuous_snd))
      (fun p => ⟨trivial, val_mem_GLs _⟩)
  have hfc : Continuous (fun y : G n => f' y.val) :=
    hf'.1.continuousOn.comp_continuous Units.continuous_val val_mem_GLs
  have hF₁ : Continuous (fun y : G n => ∫ t, γ t • U t y.val) := by
    have hc : Continuous (Function.uncurry fun (y : G n) (t : ℝ) => γ t • U t y.val) := by
      have h2 : Continuous (fun p : G n × ℝ => U p.2 p.1.val) :=
        hUc.comp (by fun_prop : Continuous fun p : G n × ℝ => (p.2, p.1))
      exact (hγ.comp continuous_snd).smul h2
    have h3 := continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ)) hc hγc.isCompact
    refine h3.congr (fun y => ?_)
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)
    simp [image_eq_zero_of_notMem_tsupport ht]

  have hMemU : ∀ t, MemLp (fun y : G n => U t y.val) 2 μ := fun t => (hU t).1.2 []
  have hMemf : MemLp (fun y : G n => f' y.val) 2 μ := hf'.2 []
  have hcalc := phi_integral F.Φ b hFc hg c hN
  have hpw := (hPW c g T₀ hg).2 N hN
  have test : ∀ ψ : Mat n → E.V, Continuous (fun y : G n => ψ y.val) →
      HasCompactSupport (fun y : G n => ψ y.val) →
      ∫ y : G n, ⟪ψ y.val, ∫ t, γ t • U t y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪ψ y.val, f' y.val⟫_ℂ ∂μ := by
    intro ψ hψ hψc
    have hMemψ : MemLp (fun y : G n => ψ y.val) 2 μ := hψ.memLp_of_hasCompactSupport hψc
    rw [test_fubini μ hLg hUc hψ hψc hγ hγc, ← cls_inner μ hMemψ hMemf, hcls, ← hpw, hcalc (cls μ ψ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [← (hU t).2, cls_inner μ hMemψ (hMemU t), hγdef]

  have hxu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)
  obtain ⟨xg, rfl⟩ := hxu
  set Dm : Mat n → E.V := fun y => (∫ t, γ t • U t y) - f' y with hDm
  have hD : Continuous (fun y : G n => Dm y.val) := hF₁.sub hfc
  set bc : G n → ℝ := fun y => max 0 (lg (1 : Mat n) + 1 - lg (xg⁻¹ * y).val) with hbc
  have hbcc : Continuous bc := by
    have h1 : Continuous (fun y : G n => lg (xg⁻¹ * y).val) :=
      (continuous_lg hLg).comp (continuous_const.mul continuous_id)
    exact continuous_const.max (continuous_const.sub h1)
  have hK : IsCompact ((fun y : G n => xg * y) '' {y : G n | lg y.val ≤ lg (1 : Mat n) + 1}) :=
    ((hLg n).2.2.2.2.1 _).image (continuous_const.mul continuous_id)
  have hbz : ∀ y, y ∉ ((fun y : G n => xg * y) '' {y : G n | lg y.val ≤ lg (1 : Mat n) + 1}) → bc y = 0 := by
    intro y hy
    have h1 : ¬ lg (xg⁻¹ * y).val ≤ lg (1 : Mat n) + 1 := fun h => hy ⟨xg⁻¹ * y, h, by simp⟩
    simp only [hbc]
    exact max_eq_left (by linarith [not_le.1 h1])
  set ψ : Mat n → E.V := fun y => ((max 0 (lg (1 : Mat n) + 1 - lg ((xg⁻¹ : G n).val * y)) : ℝ) : ℂ) • Dm y with hψdef
  have hψv : ∀ y : G n, ψ y.val = ((bc y : ℝ) : ℂ) • Dm y.val := by
    intro y
    simp only [hψdef, hbc, Units.val_mul]
  have hψ : Continuous (fun y : G n => ψ y.val) := by
    simp only [hψv]
    exact (Complex.continuous_ofReal.comp hbcc).smul hD
  have hψc : HasCompactSupport (fun y : G n => ψ y.val) := by
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    simp [hψv, hbz y hy]
  have hcomp : ∀ {f₁ : G n → E.V}, Continuous f₁ → Integrable (fun y : G n => ⟪ψ y.val, f₁ y⟫_ℂ) μ := by
    intro f₁ h₁
    refine (hψ.inner h₁).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    simp [hψv, hbz y hy]
  have hzero : ∫ y : G n, ⟪ψ y.val, Dm y.val⟫_ℂ ∂μ = 0 := by
    have h1 : ∀ y : G n, ⟪ψ y.val, Dm y.val⟫_ℂ =
        ⟪ψ y.val, ∫ t, γ t • U t y.val⟫_ℂ - ⟪ψ y.val, f' y.val⟫_ℂ := fun y => inner_sub_right _ _ _
    simp only [h1]
    rw [integral_sub (hcomp hF₁) (hcomp hfc), test ψ hψ hψc, sub_self]

  set hh : G n → ℝ := fun y => bc y * ‖Dm y.val‖ ^ 2 with hhdef
  have hhc : Continuous hh := hbcc.mul (hD.norm.pow 2)
  have hinn : ∀ y : G n, ⟪ψ y.val, Dm y.val⟫_ℂ = ((hh y : ℝ) : ℂ) := by
    intro y
    rw [hψv, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [hhdef]
  have hhz : ∫ y, hh y ∂μ = 0 := by
    simp only [hinn] at hzero
    rw [integral_complex_ofReal] at hzero
    exact_mod_cast hzero
  have hhi : Integrable hh μ := by
    refine hhc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    simp [hhdef, hbz y hy]
  have hh0 : 0 ≤ hh := fun y => mul_nonneg (le_max_left _ _) (by positivity)
  have hae := (integral_eq_zero_iff_of_nonneg hh0 hhi).1 hhz
  have hfun : hh = 0 := (Continuous.ae_eq_iff_eq μ hhc continuous_zero).1 hae
  have hat : hh xg = 0 := congrFun hfun xg
  have hb1 : bc xg = 1 := by
    simp [hbc]
  have hnorm : ‖Dm xg.val‖ = 0 := by
    have : ‖Dm xg.val‖ ^ 2 = 0 := by simpa [hhdef, hb1] using hat
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  exact sub_eq_zero.1 (norm_eq_zero.1 hnorm)

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentityStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_integral_identity : GlobalTheory.CompanionTheory.KerFc.WaveInt := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveInt | exact GlobalTheory.CompanionTheory.KerFc.waveInt | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveInt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveUniqueness
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveUniqueness
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Uniq

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := rfl
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

section Rd

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_congr (X : Mat n) {f f' : Mat n → V} (h : ∀ y ∈ GLs n, f y = f' y) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X f g = Rd X f' g := by
  have e : f =ᶠ[𝓝 g] f' := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) h
  simp only [Rd, e.fderiv_eq]

theorem rd_sub (X : Mat n) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (f - f') g = Rd X f g - Rd X f' g := by
  have ho := isOpen_GLs.mem_nhds hg
  have d1 : DifferentiableAt ℝ f g := (hf.contDiffAt ho).differentiableAt (by simp)
  have d2 : DifferentiableAt ℝ f' g := (hf'.contDiffAt ho).differentiableAt (by simp)
  have e := (d1.hasFDerivAt.sub d2.hasFDerivAt).fderiv
  exact DFunLike.congr_fun e (g * X)

theorem rd_rd_sub (hR : RCalc) (X Y : Mat n) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Rd Y (f - f')) g = Rd X (Rd Y f) g - Rd X (Rd Y f') g := by
  rw [rd_congr X (f' := Rd Y f - Rd Y f') (fun y hy => rd_sub Y hf hf' hy) hg]
  exact rd_sub X (((hR n).1 V f hf).1 Y) (((hR n).1 V f' hf').1 Y) hg

theorem om_sub (hO : OmFormula) (hR : RCalc) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) {g : Mat n} (hg : g ∈ GLs n) : Om (f - f') g = Om f g - Om f' g := by
  have hs : ContDiffOn ℝ ∞ (f - f') (GLs n) := hf.sub hf'
  rw [hO n V _ hs g hg, hO n V f hf g hg, hO n V f' hf' g hg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [rd_rd_sub hR _ _ hf hf' hg, rd_rd_sub hR _ _ hf hf' hg]
  abel

end Rd

theorem wave_line {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) {g : Mat n} (hg : g ∈ GLs n) :
    ContDiff ℝ ∞ (fun s => u s g) := by
  have h := hu.1.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := ∞) g).contDiffOn (s := Set.univ)
    (fun s _ => ⟨trivial, hg⟩)
  exact contDiffOn_univ.1 h

theorem wave_sub (hO : OmFormula) (hR : RCalc) {E : KMod n} {u u' : ℝ → Mat n → E.V} (hu : IsWave E u)
    (hu' : IsWave E u') : IsWave E (fun t => u t - u' t) := by
  refine ⟨hu.1.sub hu'.1, fun t => ⟨(hu.2.1 t).1.sub (hu'.2.1 t).1, fun g hg k => ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · show u t (g * k.1) - u' t (g * k.1) = E.ρ k⁻¹ (u t g - u' t g)
    rw [(hu.2.1 t).2 g hg k, (hu'.2.1 t).2 g hg k, map_sub]
  · have l := wave_line hu hg
    have l' := wave_line hu' hg
    have e : (fun s => (u s - u' s) g) = (fun s => u s g) - (fun s => u' s g) := rfl
    rw [e, iteratedDeriv_sub (contDiff_infty.1 l 2).contDiffAt (contDiff_infty.1 l' 2).contDiffAt,
      om_sub hO hR (hu.2.1 t).1 (hu'.2.1 t).1 hg, hu.2.2.1 t g hg, hu'.2.2.1 t g hg]
  · have d := (wave_line hu hg).differentiable (by simp)
    have d' := (wave_line hu' hg).differentiable (by simp)
    have e : (fun s => (u s - u' s) g) = (fun s => u s g) - (fun s => u' s g) := rfl
    rw [e, deriv_sub (d 0) (d' 0), hu.2.2.2 g hg, hu'.2.2.2 g hg, sub_zero]

end Uniq

theorem waveUniq : WaveUniq := by
  intro hS hC hR n E u u' hu hu' h0 t x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hO, -, -⟩ := hC
  obtain ⟨c, hc⟩ := hS n
  have h := hc E _ (Uniq.wave_sub hO hR hu hu') t x hx (fun y hy _ => by
    have hxy : x * y ∈ GLs n := by
      show (x * y).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero hx hy
    exact sub_eq_zero.2 (h0 _ hxy))
  exact sub_eq_zero.1 h

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveUniquenessStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_uniqueness : GlobalTheory.CompanionTheory.KerFc.WaveUniq := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveUniq | exact GlobalTheory.CompanionTheory.KerFc.waveUniq | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveUniq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveRepresentation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveRepresentation
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.WaveFc.Asm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.KerFc

variable {n : ℕ}

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

theorem coreRep (E : KMod n) [CompleteSpace E.V] {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hSG : SobG)
    (hAC : AbsCut) (hFc : Fcurve) (hW : WvAlg) (hC : ClsFacts) (hO : SobOps) (hCp : CptSob) (hP : PresSob)
    (hCJ : CurveJoint)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (hrep : ∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x)
    (hΩ : ∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f))
    (hT : ∀ x : Msob μ E.V, T ((x : Lp E.V 2 μ) + (Ω (Ω x) : Lp E.V 2 μ)) = x) (c : ℝ)
    (hc : ∀ f : Mat n → E.V, Sob μ f → IsSec E f → (⟪cls μ (Om f), cls μ f⟫_ℂ).re ≤ c * ‖cls μ f‖ ^ 2)
    {f : Mat n → E.V} (hf : f ∈ CE E) (hcf : Cpt f) :
    ∃ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N ∧ (T ^ N) b = cls μ f ∧ IsWave E U ∧
      (∀ x ∈ GLs n, U 0 x = f x) ∧ ∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b := by
  have hbp := fun N => Bn_props μ hL hR hCp E hf hcf N
  have hbS : ∀ N, Sob μ (Bn f N) := fun N => (hCp n μ E.V hL hR _ (hbp N).1.1 (hbp N).2).1
  have hbE : ∀ N, IsSec E (Bn f N) := fun N => (hbp N).1.2
  have hC0 : ∀ N j t, j + 2 ≤ 4 * N → (Continuous (wv c N j t) ∧ Tendsto (wv c N j t) (cocompact ℝ) (𝓝 0)) :=
    fun N j t hj => (hFc c N j hj t).1
  have hstep : ∀ N j t, j + 2 ≤ 4 * N →
      F.Φ (toC0 (wv c (N + 1) j t)) (cls μ (Bn f (N + 1))) = F.Φ (toC0 (wv c N j t)) (cls μ (Bn f N)) := by
    intro N j t hj
    rw [wv_step hW F (hC0 N j t hj) (hC0 (N + 1) j t (by omega)), ContinuousLinearMap.mul_apply]
    exact congrArg _ (T_B hC hO hL hU hR hΩ hT (hbS N))
  have hpres := fun g (N : ℕ) => pres hC hO hL hU hR hSG hP F hrep hΩ g (hbS N)
  have hex : ∀ (j : ℕ) (t : ℝ), ∃ u, Sob μ u ∧ IsSec E u ∧
      cls μ u = F.Φ (toC0 (wv c (j + 2) j t)) (cls μ (Bn f (j + 2))) ∧
      ∀ w, cls μ (Rw w u) = F.Φ (toC0 (wv c (j + 2) j t)) (cls μ (Rw w (Bn f (j + 2)))) := by
    intro j t
    obtain ⟨u, h1, h2, h3⟩ := hpres (toC0 (wv c (j + 2) j t)) (j + 2)
    exact ⟨u, h1, sec_pres E hC hO hL hU hR F hrep hΩ _ (hbS _) (hbE _) h1 h2, h2, h3⟩
  choose U hUS hUE hUc hUw using hex
  have hd : ∀ j w t, HasDerivAt (fun s => cls μ (Rw w (U j s))) (cls μ (Rw w (U (j + 1) t))) t := by
    intro j w t
    have e : (fun s => cls μ (Rw w (U j s))) =
        fun s => F.Φ (toC0 (wv c (j + 2) j s)) (cls μ (Rw w (Bn f (j + 2)))) := funext fun s => hUw j s w
    rw [e]
    have hd := curve_deriv hFc F c (N := j + 2) (j := j) (by omega) t (cls μ (Rw w (Bn f (j + 2))))
    obtain ⟨f'', hf'', hc'', hw''⟩ := hpres (toC0 (wv c (j + 2) (j + 1) t)) (j + 2)
    have e2 : cls μ (Rw w (U (j + 1) t)) = F.Φ (toC0 (wv c (j + 2) (j + 1) t)) (cls μ (Rw w (Bn f (j + 2)))) := by
      rw [← hw'' w]
      refine cls_congr hC hU (Rw_congr w (cls_eq_of_sob hC hU (hUS (j + 1) t) hf'' ?_))
      rw [hUc, hc'']
      exact hstep (j + 2) (j + 1) t (by omega)
    rw [e2]
    exact hd
  obtain ⟨hjoint, hder⟩ := hCJ n μ E.V U hL hR hSG hUS hd
  have hT2 : (T ^ 2) (cls μ (Bn f 2)) = cls μ f := by
    rw [pow_two, ContinuousLinearMap.mul_apply]
    have a1 : T (cls μ (Bn f 2)) = cls μ (Bn f 1) := T_B hC hO hL hU hR hΩ hT (hbS 1)
    have a2 : T (cls μ (Bn f 1)) = cls μ (Bn f 0) := T_B hC hO hL hU hR hΩ hT (hbS 0)
    rw [a1, a2]
    rfl
  refine ⟨2, cls μ (Bn f 2), U 0, by norm_num, hT2, ⟨hjoint, fun t => ⟨(hUS 0 t).1, hUE 0 t⟩, ?_, ?_⟩, ?_,
    fun t => ⟨hUS 0 t, hUc 0 t⟩⟩
  · intro t g hg
    have d1 : deriv (fun s => U 0 s g) = fun s => U 1 s g := funext fun s => (hder 0 s g hg).deriv
    have d2 : iteratedDeriv 2 (fun s => U 0 s g) t = U 2 t g := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, d1]
      exact (hder 1 t g hg).deriv
    rw [d2]
    have hOmS := (hO n μ E.V hL hU hR _ (hUS 0 t)).1
    have h0 : cls μ (U 0 t) = F.Φ (toC0 (wv c 4 0 t)) (cls μ (Bn f 4)) := by
      rw [hUc, hstep 3 0 t (by omega), hstep 2 0 t (by omega)]
    have hom := F.omega (toC0 (wv c 4 0 t)) (toC0 (wv c 4 2 t))
      (fun y => by
        rw [coe_toC0 (hC0 4 0 t (by omega)), coe_toC0 (hC0 4 2 t (by omega))]
        exact (hW c 4 t y).1)
      (cls μ (Bn f 4)) ⟨cls μ (U 0 t), cls_mem μ (hUS 0 t)⟩ h0
    rw [hΩ _ _ (hUS 0 t)] at hom
    exact cls_eq_of_sob hC hU (hUS 2 t) hOmS ((hUc 2 t).trans hom.symm) g hg
  · intro g hg
    rw [(hder 0 0 g hg).deriv]
    have hz : toC0 (wv c 3 1 0) = 0 := by
      ext y
      rw [coe_toC0 (hC0 3 1 0 (by omega))]
      exact (hW c 3 0 y).2.1
    have h1 : cls μ (U 1 0) = cls μ (0 : Mat n → E.V) := by
      rw [hUc, cls_zero]
      show F.Φ (toC0 (wv c 3 1 0)) _ = 0
      rw [hz, map_zero]
      rfl
    exact (hC n μ E.V hU).1 _ 0 (sob_cont (hUS 1 0)) continuousOn_const (sob_memLp (hUS 1 0)) MemLp.zero h1 g hg
  · have hcut : F.Φ (toC0 rf * toC0 rf - toC0 (wv c 2 0 0)) (cls μ (Bn f 2)) = 0 := by
      refine hAC (Lp E.V 2 μ) (Msob μ E.V) Ω T F c _ (fun g => ?_) _ (fun y hy => ?_)
      · obtain ⟨u, h1, h2, -⟩ := hpres g 2
        refine ⟨⟨cls μ u, cls_mem μ h1⟩, h2, ?_⟩
        rw [hΩ _ _ h1]
        exact hc u h1 (sec_pres E hC hO hL hU hR F hrep hΩ _ (hbS _) (hbE _) h1 h2)
      · have e1 := (hW c 2 0 y).2.2.1
        rw [cut_eq_one hy] at e1
        have e2 : (toC0 rf * toC0 rf - toC0 (wv c 2 0 0)) y = rf y * rf y - wv c 2 0 0 y := by
          rw [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.mul_apply, coe_toC0 resolvent_function_vanishes_at_infinity,
            coe_toC0 (hC0 2 0 0 (by omega))]
        rw [e2, e1, rf, ← Complex.ofReal_mul, sub_eq_zero]
        congr 1
        rw [one_mul, pow_two (1 + y ^ 2), mul_inv]
    have hr : F.Φ (toC0 rf * toC0 rf) (cls μ (Bn f 2)) = cls μ f := by
      rw [F.map_mul, F.res (toC0 rf) (fun y => by rw [coe_toC0 resolvent_function_vanishes_at_infinity]; rfl), ContinuousLinearMap.mul_apply]
      have a1 : T (cls μ (Bn f 2)) = cls μ (Bn f 1) := T_B hC hO hL hU hR hΩ hT (hbS 1)
      have a2 : T (cls μ (Bn f 1)) = cls μ (Bn f 0) := T_B hC hO hL hU hR hΩ hT (hbS 0)
      rw [a1, a2]
      rfl
    have hw : F.Φ (toC0 (wv c 2 0 0)) (cls μ (Bn f 2)) = cls μ f := by
      rw [map_sub, ContinuousLinearMap.sub_apply, hr, sub_eq_zero] at hcut
      exact hcut.symm
    exact cls_eq_of_sob hC hU (hUS 0 0) (hbS 0) ((hUc 0 0).trans hw)

end Main

theorem waveRep : WaveRep := by
  intro n _ _ μ _ E _ Ω T F c hStd f hf hcf
  obtain ⟨hL, hU, hR, hSG, -, -, -, hCS, -, -, hrep, -, -, hT, hΩ, hc⟩ := hStd
  obtain ⟨-, hAC, hFc, hW, hC, hO, hCp, -, hP, -, hCJ, -, -, -, -⟩ := hCS
  exact coreRep E hL hU hR hSG hAC hFc hW hC hO hCp hP hCJ F hrep hΩ hT c hc hf hcf

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveRepresentationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_representation : GlobalTheory.CompanionTheory.KerFc.WaveRep := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveRep | exact GlobalTheory.CompanionTheory.KerFc.waveRep | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveRep <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowMatrix
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowMatrix
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc.RowLin

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem sum_sec {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hCl : ClsFacts) (hOps : SobOps)
    {ι : Type} (f₀ : Mat n → E.V) (h₀ : Sob μ f₀) (f : ι → Mat n → E.V) (hS : ∀ i, Sob μ (f i))
    (hI : ∀ i, IsSec E (f i)) (a : ι → ℂ) (s : Finset ι) :
    Sob μ (fun y => ∑ i ∈ s, a i • f i y) ∧ IsSec E (fun y => ∑ i ∈ s, a i • f i y) ∧
      cls μ (fun y => ∑ i ∈ s, a i • f i y) = ∑ i ∈ s, a i • cls μ (f i) := by
  classical
  have hlin := (hCl n μ E.V hU).2.1
  have hadd : ∀ (b : ℂ) (g g' : Mat n → E.V), Sob μ g → Sob μ g' → Sob μ (b • g + g') := fun b g g' hg hg' =>
    ((hOps n μ E.V hLg hU hR g hg).2.2.2.1 b g' hg').1
  have hmem : ∀ g : Mat n → E.V, Sob μ g → MemLp (fun y : G n => g y.val) 2 μ := fun g hg => hg.2 []
  induction s using Finset.induction_on with
  | empty =>
    have hz : (fun _ : Mat n => (0 : E.V)) = (-1 : ℂ) • f₀ + f₀ := by
      funext y; simp
    simp only [Finset.sum_empty]
    refine ⟨hz ▸ hadd _ _ _ h₀ h₀, fun g _ k => by simp, ?_⟩
    rw [hz, hlin _ _ _ (hmem _ h₀) (hmem _ h₀)]
    simp
  | insert i s hi ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hz : (fun y => ∑ j ∈ insert i s, a j • f j y) = a i • f i + fun y => ∑ j ∈ s, a j • f j y := by
      funext y; simp [Finset.sum_insert hi]
    rw [hz, Finset.sum_insert hi]
    refine ⟨hadd _ _ _ (hS i) ih1, fun g hg k => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), map_smul]
      rw [hI i g hg k]
      exact congrArg (a i • (E.ρ k⁻¹) (f i g) + ·) (ih2 g hg k)
    · rw [hlin _ _ _ (hmem _ (hS i)) (hmem _ ih1), ih3]

end GlobalTheory.CompanionTheory.KerFc.RowLin

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rowMatrix_holds : RowMatrix := by
  intro n _ _ μ _ E _ Ω T F c hstd h hrow
  obtain ⟨hLg, hU, hR, -, -, -, -, hCS, -⟩ := hstd
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  let e := stdOrthonormalBasis ℂ E.V
  choose f hf using fun i => hrow (e i)
  obtain ⟨f₀, hf₀⟩ := hrow 0
  refine ⟨fun y => ∑ i, (innerSL ℂ (e i)).smulRight (f i y), fun v => ?_⟩
  have hA : (fun y => (∑ i, (innerSL ℂ (e i)).smulRight (f i y)) v) =
      fun y => ∑ i ∈ Finset.univ, (⟪e i, v⟫_ℂ) • f i y := by
    funext y
    simp [ContinuousLinearMap.sum_apply]
  obtain ⟨h1, h2, h3⟩ := RowLin.sum_sec μ E hLg hU hR hCl hOps f₀ hf₀.1 f (fun i => (hf i).1)
    (fun i => (hf i).2.1) (fun i => ⟪e i, v⟫_ℂ) Finset.univ
  show Row μ E F h v (fun y => (∑ i, (innerSL ℂ (e i)).smulRight (f i y)) v)
  rw [hA]
  refine ⟨h1, h2, fun φ f' hφ hφs hf' hf's hcl => ?_⟩
  rw [h3, sum_inner, ← (e.sum_inner_mul_inner v (f' 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_conj_symm, (hf i).2.2 φ f' hφ hφs hf' hf's hcl]

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowMatrixStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_matrix : GlobalTheory.CompanionTheory.KerFc.RowMatrix := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.rowMatrix_holds | exact GlobalTheory.CompanionTheory.KerFc.rowMatrix_holds | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowMatrix_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularity
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coe_toC0 {f : ℝ → ℂ} (h₁ : Continuous f) (h₂ : Tendsto f (cocompact ℝ) (𝓝 0)) (y : ℝ) : toC0 f y = f y := by
  have : Continuous f ∧ Tendsto f (cocompact ℝ) (𝓝 0) := ⟨h₁, h₂⟩
  simp only [toC0]
  rw [dite_eq_left this]
  rfl

theorem adj_rho {n : ℕ} (E : KMod n) [CompleteSpace E.V] (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ContinuousLinearMap.adjoint (E.ρ k⁻¹) = E.ρ k := by
  have hmul : ∀ v, E.ρ k (E.ρ k⁻¹ v) = v := fun v => by
    have := congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k k⁻¹)
    simpa using this.symm
  have hmul' : ∀ v, E.ρ k⁻¹ (E.ρ k v) = v := fun v => by
    have := congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k⁻¹ k)
    simpa using this.symm
  let I : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k).toLinearMap, fun v => E.iso k v⟩
  ext v
  refine ext_inner_right ℂ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := I.inner_map_map v (E.ρ k⁻¹ w)
  have e : ∀ z, I z = E.ρ k z := fun _ => rfl
  rw [e, e, hmul] at this
  exact this.symm

theorem kerCore_of (hFR : RowExists) (hRM : RowMatrix) (hAS : AdjSmooth) (hRL : RowLeft) (hAF : ActFormula)
    (hWR : WaveRep) (hWU : WaveUniq) (hPR : PhiRes) (hWI : WaveInt) (hSR : SupportRow) : KerCore := by
  intro n _ _ μ _ E g T₀ hb hLg hUn hRC hSG hAE hWS hWC hCS hSO hPW
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  obtain ⟨hAbsFC, hAbsCut, hFc, hWv, hCls, hSobOps, hCptSob, hSB, hPres, hConc, hCJ, hFr, hOmF, hIbp, hDD⟩ := id hCS
  obtain ⟨hMrep, Ω, T, hDense, hSym, hEx, hLeft, hOm⟩ :=
    hConc n μ E.V hLg hUn hRC hSG hPres hFr hCls hSobOps hCptSob hOmF hIbp hDD
  obtain ⟨F⟩ := hAbsFC _ _ Ω T hDense hSym hEx hLeft
  obtain ⟨c, hc⟩ := hSB n μ E hLg hUn hRC
  have hStd : Std μ E F c :=
    ⟨hLg, hUn, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, hMrep, hSym, hEx, hLeft, hOm, hc⟩
  have hPW1 := (hPW c g T₀ hb).1
  have hPW2 := (hPW c g T₀ hb).2
  have hC0 : ∀ y, toC0 (hg c g) y = hg c g y := fun y => by
    have := hPW1 0
    simp only [pow_zero, one_mul] at this
    exact coe_toC0 this.1 (by simpa using this.2) y
  have hR : Rapid (toC0 (hg c g)) := fun m =>
    ⟨toC0 (fun y : ℝ => (y : ℂ) ^ m * hg c g y), fun y => by
      rw [coe_toC0 (hPW1 m).1 (hPW1 m).2, hC0]⟩
  obtain ⟨A, hA⟩ := hRM n μ E Ω T F c hStd _ (hFR n μ E Ω T F c hStd _ hR)
  have hWV : ∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) → ∀ f', Sob μ f' → IsSec E f' →
      cls μ f' = F.Φ (toC0 (hg c g)) (cls μ f) → ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • u t x = f' x := by
    intro f hf hcpt u hu h0 f' hs _ hcl x hx
    obtain ⟨N, b, U, hN, hT, hUw, hU0, hUt⟩ := hWR n μ E Ω T F c hStd f hf hcpt
    have huU : ∀ t, u t x = U t x := fun t =>
      hWU hWS hCS hRC n E u U hu hUw (fun y hy => by rw [h0 y hy, hU0 y hy]) t x hx
    have hcl' : cls μ f' = F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) b := by
      rw [hPR n μ E Ω T F c hStd g T₀ hb N hN, hcl, ← hT]
      rfl
    have := hWI n μ E Ω T F c hStd g T₀ hb N b U hN hUw hUt f' hs hcl' x hx
    simpa only [huU] using this
  obtain ⟨R, hRsup⟩ := hSR n μ E Ω T F c hStd g T₀ _ hb hR hWV
  have hKdef : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, A (y * k.1) = E.ρ k⁻¹ * A y := by
    intro k y hy
    ext v
    exact (hA v).2.1 y hy k
  have hkG : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, k.1 * y ∈ GLs n := by
    intro k y hy
    have hk : (k.1 : Mat n).det ≠ 0 :=
      (Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.1 k.2)).ne_zero
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hy ⊢
    exact mul_ne_zero hk hy
  refine ⟨fun y => ContinuousLinearMap.adjoint (A y), hAS _ _ A _ fun v => (hA v).1.1, ⟨R, ?_⟩, ?_, ?_⟩
  · intro y hy hl
    have : A y = 0 := by
      ext v
      exact hRsup v _ (hA v) y hy hl
    simp [this]
  · intro y hy k₁ k₂
    have e1 : A (k₁.1 * y * k₂.1) = E.ρ k₂⁻¹ * A (k₁.1 * y) := hKdef k₂ _ (hkG k₁ y hy)
    have e2 : A (k₁.1 * y) = A y * E.ρ k₁⁻¹ := by
      ext v
      exact hRL n μ E Ω T F c hStd _ A hR hA k₁ y hy v
    show ContinuousLinearMap.adjoint (A (k₁.1 * y * k₂.1)) = _
    rw [e1, e2]
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.mul_def, adj_rho]
  · intro f hf hcpt u hu h0 x hx
    have hSf : Sob μ f := (hCptSob n μ E.V hLg hRC f hf.1 hcpt).1
    obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (toC0 (hg c g)) hR
    obtain ⟨f', hf's, hf'e, hf'c, -⟩ := hC (cls μ f) (subset_closure ⟨f, hSf, hf.2, rfl⟩)
    rw [hAF n μ E Ω T F c hStd _ A hA f hf hcpt f' hf's hf'e hf'c x hx,
      hWV f hf hcpt u hu h0 f' hf's hf'e hf'c x hx]

theorem kerCore : KerCore :=
  have hLC := GlobalTheory.T.left_translate_commutes GlobalTheory.T.left_translate_sobolev
  kerCore_of (GlobalTheory.T.kernel_row_exists GlobalTheory.T.rapid_factorization GlobalTheory.T.eigenvalue_adjoint_facts) GlobalTheory.T.kernel_row_matrix GlobalTheory.T.kernel_adjoint_smooth
    (GlobalTheory.T.kernel_row_left_invariant GlobalTheory.T.left_translate_sobolev hLC) (GlobalTheory.T.kernel_action_formula GlobalTheory.T.left_translate_sobolev hLC) GlobalTheory.T.wave_representation GlobalTheory.T.wave_uniqueness GlobalTheory.T.phi_resolvent_identity
    GlobalTheory.T.wave_integral_identity GlobalTheory.T.kernel_row_support

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularityStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_regularity : PositivityTheory.RgBcC.Fc.KerCore := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.kerCore | exact GlobalTheory.CompanionTheory.KerFc.kerCore | (intros; apply GlobalTheory.CompanionTheory.KerFc.kerCore <;> assumption)
end
