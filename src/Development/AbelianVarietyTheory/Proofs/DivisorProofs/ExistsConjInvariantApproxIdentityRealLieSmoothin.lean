module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldMaximalIdealDvdUniformizer
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGenericFibrePolarizationIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.AutGrowth.ApproxId

theorem tendsto_integral_of_concentrate {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] {ν : Measure V}
    {f : V → ℂ} {x₀ : V} (hf : ContinuousAt f x₀) (β : ℕ → V → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (h0 : ∀ n x, 0 ≤ β n x) (h1 : ∀ n, ∫ x, β n x ∂ν = 1) (hs : ∀ n x, β n x ≠ 0 → dist x x₀ < r n)
    (hi : ∀ n, Integrable (β n) ν) (hfi : ∀ n, Integrable (fun x => (β n x : ℂ) * f x) ν) :
    Tendsto (fun n => ∫ x, (β n x : ℂ) * f x ∂ν) atTop (𝓝 (f x₀)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.1 hf (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hr) δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hrn : r n < δ := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have e1 : ∫ x, (β n x : ℂ) * f x₀ ∂ν = f x₀ := by
    rw [integral_mul_const, integral_complex_ofReal, h1 n]; simp
  have e2 : ∫ x, (β n x : ℂ) * f x ∂ν - f x₀ = ∫ x, (β n x : ℂ) * (f x - f x₀) ∂ν := by
    conv_lhs => rw [← e1]
    refine (integral_sub (hfi n) ((hi n).ofReal.mul_const (f x₀))).symm.trans ?_
    congr 1; funext x; rw [mul_sub]; rfl
  rw [dist_eq_norm, e2]
  calc ‖∫ x, (β n x : ℂ) * (f x - f x₀) ∂ν‖ ≤ ∫ x, β n x * (ε / 2) ∂ν := by
        refine norm_integral_le_of_norm_le ((hi n).mul_const _) (.of_forall fun x => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 n x)]
        by_cases hx : β n x = 0
        · simp [hx]
        · exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact (hfδ ((hs n x hx).trans hrn)).le) (h0 n x)
    _ = ε / 2 := by rw [integral_mul_const, h1 n, one_mul]
    _ < ε := half_lt_self hε

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem sum_norm_sq_eq (N : Matrix (Fin a) (Fin a) (Cinf E)) (w : InfinitePlace E) :
    ∑ i, ∑ j, ‖N i j w‖ ^ 2 = (Matrix.trace (star N * N) w).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem trace_star_mul_conj (k : Kinf E a) (N : Matrix (Fin a) (Fin a) (Cinf E)) :
    Matrix.trace (star ((k : Matrix (Fin a) (Fin a) (Cinf E)) * N * star (k : Matrix (Fin a) (Fin a) (Cinf E))) *
      ((k : Matrix (Fin a) (Fin a) (Cinf E)) * N * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) =
      Matrix.trace (star N * N) := by
  have h1 : star (k : Matrix (Fin a) (Fin a) (Cinf E)) * k = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  set K : Matrix (Fin a) (Fin a) (Cinf E) := ↑k
  have e : star (K * N * star K) * (K * N * star K) = K * (star N * N * star K) := by
    rw [star_mul, star_mul, star_star]
    calc K * (star N * star K) * (K * N * star K) = K * star N * (star K * K) * N * star K := by
          simp only [mul_assoc]
      _ = K * (star N * N * star K) := by rw [h1, mul_one]; simp only [mul_assoc]
  rw [e, Matrix.trace_mul_comm, mul_assoc, h1, mul_one]


variable (E a) in
def frobSq (x : Lie E a) : ℝ := ∑ w, ∑ i, ∑ j, ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2

omit [_root_.NumberField.IsTotallyComplex E] in
theorem frobSq_eq (x : Lie E a) :
    frobSq E a x = ∑ w, ((Matrix.trace (star (Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) *
      (Matrix.of x - 1)) : Cinf E) w).re := by
  rw [frobSq]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← sum_norm_sq_eq]
  rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem frobSq_conj (k : Kinf E a) (x : Lie E a) :
    frobSq E a (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = frobSq E a x := by
  have h2 : (k : Matrix (Fin a) (Fin a) (Cinf E)) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 k.2
  have e : Matrix.of (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) - 1 =
      (k : Matrix (Fin a) (Fin a) (Cinf E)) * (Matrix.of x - 1) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) := by
    rw [Unitary.coe_star, mul_sub, sub_mul, mul_one, h2]
    rfl
  rw [frobSq_eq, frobSq_eq, e, trace_star_mul_conj]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiff_frobSq : ContDiff ℝ ∞ (frobSq E a) := by
  unfold frobSq
  refine ContDiff.sum fun w _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq ℝ).comp
    (((contDiff_apply ℝ (fun _ => ℂ) w).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i))).sub contDiff_const)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem frobSq_one : frobSq E a (oneL E a) = 0 := by
  simp [frobSq]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_sq_le_frobSq (x : Lie E a) (i j : Fin a) (w : InfinitePlace E) :
    ‖x i j w - oneL E a i j w‖ ^ 2 ≤ frobSq E a x := by
  unfold frobSq
  refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j,
    ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2) (fun w _ => by positivity) (Finset.mem_univ w))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j,
    ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ j)


variable (E a) in
def bumpR (m : ℝ) (x : Lie E a) : ℝ := Real.smoothTransition (1 - m ^ 2 * frobSq E a x)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiff_bumpR (m : ℝ) : ContDiff ℝ ∞ (bumpR E a m) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_frobSq))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem bumpR_nonneg (m : ℝ) (x : Lie E a) : 0 ≤ bumpR E a m x := Real.smoothTransition.nonneg _

omit [_root_.NumberField.IsTotallyComplex E] in
theorem bumpR_one (m : ℝ) : bumpR E a m (oneL E a) = 1 := by
  simp [bumpR, frobSq_one]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem dist_lt_of_bumpR_ne_zero {m : ℝ} (hm : 0 < m) {x : Lie E a} (h : bumpR E a m x ≠ 0) :
    dist x (oneL E a) < 1 / m := by
  have h1 : m ^ 2 * frobSq E a x < 1 := by
    by_contra hc
    exact h (Real.smoothTransition.zero_of_nonpos (by linarith))
  have hr : 0 < 1 / m := one_div_pos.2 hm
  rw [dist_pi_lt_iff hr]; intro i
  rw [dist_pi_lt_iff hr]; intro j
  rw [dist_pi_lt_iff hr]; intro w
  rw [Complex.dist_eq]
  have h2 := norm_sq_le_frobSq x i j w
  have h3 : (m * ‖x i j w - oneL E a i j w‖) ^ 2 < 1 := by
    rw [mul_pow]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
  have h4 : m * ‖x i j w - oneL E a i j w‖ < 1 := by
    have := abs_lt_of_sq_lt_sq' (h3.trans_eq (one_pow 2).symm) zero_le_one
    exact this.2
  rw [lt_div_iff₀ hm]
  linarith

omit [_root_.NumberField.IsTotallyComplex E] in
theorem bumpR_conj (m : ℝ) (k : Kinf E a) (x : Lie E a) :
    bumpR E a m (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = bumpR E a m x := by
  simp only [bumpR, frobSq_conj]

end GlobalTheory.AutGrowth.ApproxId

namespace GlobalTheory.AutGrowth.ApproxId

theorem exists_approx_identity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure], ∃ α : ℕ → Lie E a → ℂ,
      (∀ n, IsTest (invSet E a) (α n) ∧ KInv (α n)) ∧
      ∀ ψ ∈ Sm E a, ∀ g, Tendsto (fun n => smoothing ν (α n) ψ g) atTop (𝓝 (ψ g)) := by
  intro E _ _ _ a ν _
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_invSet (E := E) (a := a)) (oneL E a) isUnit_one
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  let m : ℕ → ℝ := fun n => (n : ℝ) + N + 1
  have hm : ∀ n, 0 < m n := fun n => by positivity
  have hmN : ∀ n, 1 / m n < ε := fun n =>
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by simp [m])) hN
  have hsub : ∀ n, Metric.closedBall (oneL E a) (1 / m n) ⊆ invSet E a := fun n =>
    (Metric.closedBall_subset_ball (hmN n)).trans hball
  have hsupp : ∀ n, Function.support (bumpR E a (m n)) ⊆ Metric.closedBall (oneL E a) (1 / m n) :=
    fun n x hx => Metric.mem_closedBall.2 (dist_lt_of_bumpR_ne_zero (hm n) hx).le
  have hcs : ∀ n, HasCompactSupport (bumpR E a (m n)) := fun n =>
    HasCompactSupport.intro (isCompact_closedBall (oneL E a) (1 / m n)) fun x hx => by
      by_contra h; exact hx (hsupp n h)
  have hpos : ∀ n, 0 < ∫ x, bumpR E a (m n) x ∂ν := fun n =>
    (contDiff_bumpR (m n)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs n)
      (fun x => bumpR_nonneg _ x) (x := oneL E a) (by rw [bumpR_one]; norm_num)
  let β : ℕ → Lie E a → ℝ := fun n x => (∫ y, bumpR E a (m n) y ∂ν)⁻¹ * bumpR E a (m n) x
  have hβs : ∀ n x, β n x ≠ 0 → dist x (oneL E a) < 1 / m n := fun n x h =>
    dist_lt_of_bumpR_ne_zero (hm n) (right_ne_zero_of_mul h)
  have hβc : ∀ n, ContDiff ℝ ∞ (β n) := fun n => contDiff_const.mul (contDiff_bumpR _)
  have hβcs : ∀ n, HasCompactSupport (β n) := fun n => (hcs n).mul_left
  have hT : ∀ n, IsTest (invSet E a) (fun x => (β n x : ℂ)) := fun n => by
    refine ⟨Complex.ofRealCLM.contDiff.comp (hβc n), ?_, ?_⟩
    · exact HasCompactSupport.intro (isCompact_closedBall (oneL E a) (1 / m n)) fun x hx => by
        by_contra h
        exact hx (Metric.mem_closedBall.2 (hβs n x (fun h' => h (by simp [h']))).le)
    · refine (closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall).trans (hsub n)
      exact Metric.mem_closedBall.2 (hβs n x (fun h' => hx (by simp [h']))).le
  refine ⟨fun n x => (β n x : ℂ), fun n => ⟨hT n, fun k x => ?_⟩, fun ψ hψ g => ?_⟩
  · simp only [β, bumpR_conj]
  · have hv : chart ψ g (oneL E a) = ψ g := by
      have := chart_val ψ g 1
      simpa using this
    have hf : ContinuousAt (chart ψ g) (oneL E a) := (contDiffAt_chart hψ g isUnit_one).continuousAt
    have hr : Tendsto (fun n => 1 / m n) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (one_div_pos.2 (hm n)).le) (fun n => ?_)
      exact one_div_le_one_div_of_le (by positivity) (by simp [m])
    have h1 : ∀ n, ∫ x, β n x ∂ν = 1 := fun n => by
      simp only [β]
      rw [integral_const_mul, inv_mul_cancel₀ (hpos n).ne']
    have key := tendsto_integral_of_concentrate hf β (fun n => 1 / m n) hr
      (fun n x => mul_nonneg (inv_nonneg.2 (hpos n).le) (bumpR_nonneg _ x)) h1 hβs
      (fun n => (hβc n).continuous.integrable_of_hasCompactSupport (hβcs n))
      (fun n => (hT n).integrable_mul ν isOpen_invSet (hψ g).continuousOn)
    rw [hv] at key
    exact key

end GlobalTheory.AutGrowth.ApproxId
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothinStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure], ∃ α : ℕ → Lie E a → ℂ, (∀ n, IsTest (invSet E a) (α n) ∧ KInv (α n)) ∧ ∀ ψ ∈ Sm E a, ∀ g, Tendsto (fun n => smoothing ν (α n) ψ g) atTop (𝓝 (ψ g)) := by
  first | exact @GlobalTheory.AutGrowth.ApproxId.exists_approx_identity | exact GlobalTheory.AutGrowth.ApproxId.exists_approx_identity | (intros; apply GlobalTheory.AutGrowth.ApproxId.exists_approx_identity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePair
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDict

theorem fock_isThetaFunO : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  ∀ T, IsThetaFunO X.ψ X.A X.B (X.fock T) := by
  intro D cc δ t0 Q P X hX T
  exact Formalism.IndefR.Fin.ptStable D X.ψ X.θ hX.2.weil.std hX.2.inf X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) X.vac _ hX.2.vac_theta

end GlobalTheory.NormDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePairStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vector_isThetaFunction_definite_pair : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  ∀ T, IsThetaFunO X.ψ X.A X.B (X.fock T) := by
  first | exact @GlobalTheory.NormDict.fock_isThetaFunO | exact GlobalTheory.NormDict.fock_isThetaFunO | (intros; apply GlobalTheory.NormDict.fock_isThetaFunO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormOrbit
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv

theorem exists_eq_normal_form_mul_of_rank_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) (hnd : n ≤ d)
    (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) :
    ∃ h : GL (Fin d) k, Y = GlobalTheory.FullRankCoinv.Y0 k n d * h.val := by
  let σ : Fin n ⊕ Fin (d - n) ≃ Fin d :=
    (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσ : ∀ i : Fin n, ((σ (Sum.inl i) : Fin d) : ℕ) = d - n + i := fun i => by
    simp [σ]
  have hX : X0 k σ = GlobalTheory.FullRankCoinv.Y0 k n d := by
    ext i j
    simp only [X0, GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply]
    congr 1
    apply propext
    rw [← hσ i, eq_comm]
    exact Fin.val_inj.symm
  have hc : Y.rank = Fintype.card (Fin n) := by simpa using hY
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ Y).1 hc
  exact ⟨invT h, by rw [hh, hX]⟩

end GlobalTheory.FullRankCoinv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormOrbitStatement
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_normal_form_orbit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ), n ≤ d →
    ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ h : GL (Fin d) k, Y = GlobalTheory.FullRankCoinv.Y0 k n d * h.val := by
  first | exact @GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq | exact GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq | (intros; apply GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchDerivativeOnPureTensorUniqueAdelicOperato
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchDerivativeOnPureTensorUniqueAdelicOperato
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.SDUnique

theorem proj_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x₀ : κ → AF F) :
    (LinearMap.proj x₀ : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x₀ i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem sd_unique : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ f₂ : SInf F κ}, SD T f f₁ → SD T f f₂ → f₁ = f₂ := by
  intro F _ _ κ _ T f f₁ f₂ h₁ h₂
  have hg := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  refine SchwartzMap.ext fun x => ?_
  let x₀ : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), 0)
  have h := (h₁ _ hg _ (proj_mem_adm x₀)).unique (h₂ _ hg _ (proj_mem_adm x₀))
  have h0 : (fun _ : κ => (0 : Af F)) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v =>
    zero_mem (v.adicCompletionIntegers F)
  have e : ∀ φ : SInf F κ, pureA F φ ((GlobalTheory.SchANonzero.intPts F κ).indicator 1) x₀ = φ x := fun φ => by
    have hx : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1) = x :=
      funext fun i => RingEquiv.apply_symm_apply _ _
    have h1 : (GlobalTheory.SchANonzero.intPts F κ).indicator (1 : (κ → Af F) → ℂ) (fun i => (x₀ i).2) = 1 :=
      Set.indicator_of_mem h0 _
    unfold pureA
    rw [hx]
    exact (congrArg (φ x * ·) h1).trans (mul_one _)
  exact (e f₁).symm.trans (h.trans (e f₂))

end GlobalTheory.SDUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchDerivativeOnPureTensorUniqueAdelicOperatoStatement
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    {f f₁ f₂ : SInf F κ}, SD T f f₁ → SD T f f₂ → f₁ = f₂ := by
  first | exact @GlobalTheory.SDUnique.sd_unique | exact GlobalTheory.SDUnique.sd_unique | (intros; apply GlobalTheory.SDUnique.sd_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenCoverFiniteTranslatesSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenCoverFiniteTranslatesSupport
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem GlobalTheory.FullRankCoinv.fullRk_support_finite_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (S : Set (Matrix (Fin n) (Fin d) k)), IsOpen S →
    (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ E : GL (Fin n) k, E.val * Y ∈ S) →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ s : Finset (GL (Fin n) k), ∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S := by
  intro k _ _ _ _ n d S hS hcov Ψ hΨ
  obtain ⟨⟨hlc, hcs⟩, hz⟩ := hΨ
  have hcl : IsClosed (Function.support Ψ) := by
    have h := (hlc.isOpen_fiber 0).isClosed_compl
    convert h using 1
    ext Y; simp [Function.mem_support]
  have hK : IsCompact (Function.support Ψ) :=
    IsCompact.of_isClosed_subset hcs hcl (subset_tsupport Ψ)
  have hU : ∀ E : GL (Fin n) k, IsOpen ((fun Y : Matrix (Fin n) (Fin d) k => E.val * Y) ⁻¹' S) := fun E =>
    hS.preimage (Continuous.matrix_mul continuous_const continuous_id)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun E : GL (Fin n) k => (fun Y : Matrix (Fin n) (Fin d) k => E.val * Y) ⁻¹' S) hU
    (by
      intro Y hY
      have hr : Y.rank = n := by
        by_contra h
        exact hY (hz Y h)
      obtain ⟨E, hE⟩ := hcov Y hr
      exact Set.mem_iUnion.2 ⟨E, hE⟩)
  refine ⟨t, fun Y hY => ?_⟩
  have := ht hY
  simp only [Set.mem_iUnion, Set.mem_preimage] at this
  obtain ⟨E, hEt, hE⟩ := this
  exact ⟨E, hEt, hE⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenCoverFiniteTranslatesSupportStatement
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cover_finite_translates_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (S : Set (Matrix (Fin n) (Fin d) k)), IsOpen S →
    (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ E : GL (Fin n) k, E.val * Y ∈ S) →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ s : Finset (GL (Fin n) k), ∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S := by
  first | exact @GlobalTheory.FullRankCoinv.fullRk_support_finite_cover | exact GlobalTheory.FullRankCoinv.fullRk_support_finite_cover | (intros; apply GlobalTheory.FullRankCoinv.fullRk_support_finite_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainRationalBlockUnipotentGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainRationalBlockUnipotentGL
noncomputable section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open Topology

namespace GlobalTheory.CuspRep

theorem discreteTopology_ratN (E : Type) [Field E] [NumberField E] (a s : ℕ) :
    DiscreteTopology (ratN E a s) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hU : IsOpen (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd (F := E)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => Formalism.IndefR.Eqv.G5.adl_isOpen_nbhd
  have h : ({0} : Set (ratN E a s)) =
      Subtype.val ⁻¹' (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd (F := E)) := by
    ext ⟨x, q, hq⟩
    constructor
    · intro hx p _
      have : x = 0 := congrArg Subtype.val hx
      subst this
      exact Formalism.IndefR.Eqv.G5.adl_zero_mem_nbhd
    · intro hx
      subst hq
      apply Subtype.ext
      funext p
      have h0 : q p = 0 := Formalism.IndefR.Eqv.G5.adl_eq_zero_of_mem_nbhd (q p) (hx p (Set.mem_univ _))
      show algebraMap E (Ad E) (q p) = 0
      rw [h0, map_zero]
  rw [h]
  exact hU.preimage continuous_subtype_val

theorem exists_isAddFundamentalDomain_ratN : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ) [MeasurableSpace (BlockIx a s → Ad E)] [BorelSpace (BlockIx a s → Ad E)] (μ : Measure (BlockIx a s → Ad E)) [μ.IsAddHaarMeasure], ∃ 𝓕 : Set (BlockIx a s → Ad E), IsAddFundamentalDomain (ratN E a s) 𝓕 μ ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 < ⊤ := by
  intro E _ _ _ a s _ _ μ _
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := discreteTopology_ratN E a s
  haveI := countable_ratN (E := E) (a := a) s
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (ratN E a s)
  haveI : MeasurableConstVAdd (ratN E a s) (BlockIx a s → Ad E) :=
    ⟨fun γ => (continuous_const.add continuous_id :
      Continuous fun x : BlockIx a s → Ad E => (γ : BlockIx a s → Ad E) + x).measurable⟩
  haveI : VAddInvariantMeasure (ratN E a s) (BlockIx a s → Ad E) μ :=
    ⟨fun γ t _ => measure_preimage_add μ (γ : BlockIx a s → Ad E) t⟩
  have hμ : μ ≠ 0 := fun h => by
    have := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    rw [h] at this
    exact this rfl
  exact ⟨D, hD μ, (hD μ).measure_ne_zero hμ, covol_lt_top μ D (hD μ)⟩

end GlobalTheory.CuspRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainRationalBlockUnipotentGLStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_rationalBlockUnipotentGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ) [MeasurableSpace (BlockIx a s → Ad E)] [BorelSpace (BlockIx a s → Ad E)] (μ : Measure (BlockIx a s → Ad E)) [μ.IsAddHaarMeasure], ∃ 𝓕 : Set (BlockIx a s → Ad E), IsAddFundamentalDomain (ratN E a s) 𝓕 μ ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 < ⊤ := by
  first | exact @GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN | exact GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN | (intros; apply GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenUnitMinorSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenUnitMinorSet
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.UnitMinor

theorem isClopen_setOf_valuation_eq_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsClopen {x : k | valuation k x = 1} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy
    rw [IsValuativeTopology.mem_nhds_iff']
    by_cases h0 : y = 0
    · subst h0
      refine ⟨1, fun z hz ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_one, sub_zero, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢
      exact hz.ne
    · have hv : valuation k y ≠ 0 := by simpa using h0
      refine ⟨Units.mk0 _ hv, fun z hz ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_mk0, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢
      have : z = y + (z - y) := by ring
      rw [this, (valuation k).map_add_eq_of_lt_left hz]
      exact hy
  · rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [IsValuativeTopology.mem_nhds_iff']
    refine ⟨1, fun z hz ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_one, Set.mem_setOf_eq] at hz hy ⊢
    have : z = y + (z - y) := by ring
    rw [this, (valuation k).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

theorem isClopen_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) : IsClopen (unitMinorSet k n d) := by
  have hI : IsClopen {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
    exact ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hU : IsClopen (⋃ f : Fin n ↪ Fin d,
      (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1}) := by
    refine isClopen_iUnion_of_finite fun f ↦ (isClopen_setOf_valuation_eq_one k).preimage ?_
    exact Continuous.matrix_det (Continuous.matrix_submatrix continuous_id _ _)
  have e : unitMinorSet k n d = {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} ∩ ⋃ f : Fin n ↪ Fin d,
      (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1} := by
    ext Y; simp [unitMinorSet]
  rw [e]; exact hI.inter hU

end GlobalTheory.FullRankCoinv.UnitMinor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenUnitMinorSetStatement
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_unit_minor_set : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ),
    IsClopen (GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d) := by
  first | exact @GlobalTheory.FullRankCoinv.UnitMinor.isClopen_unitMinorSet | exact GlobalTheory.FullRankCoinv.UnitMinor.isClopen_unitMinorSet | (intros; apply GlobalTheory.FullRankCoinv.UnitMinor.isClopen_unitMinorSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOfValuationRingFixedFieldInertia
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOfValuationRingFixedFieldInertia
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaFixedUniformizer

theorem valuation_uniformizer_lt_one {R K Ω : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring)
    {π : R} (hπ : Irreducible π) : V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 := by
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hle : V.valuation (algebraMap K Ω (algebraMap R K π)) ≤ 1 := by
    rw [V.valuation_le_one_iff]
    have : algebraMap R K π ∈ (V.toSubring).comap (algebraMap K Ω) := by
      rw [hV]; exact ⟨π, rfl⟩
    exact this
  refine lt_of_le_of_ne hle fun h1 => hπ.not_isUnit ?_
  have hinv : (algebraMap R K π)⁻¹ ∈ (V.toSubring).comap (algebraMap K Ω) := by
    change algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V
    rw [← V.valuation_le_one_iff, map_inv₀, map_inv₀, h1, inv_one]
  rw [hV] at hinv
  obtain ⟨u, hu⟩ := hinv
  refine IsUnit.of_mul_eq_one u (IsFractionRing.injective R K ?_)
  rw [map_mul, hu, mul_inv_cancel₀ hπ0, map_one]

theorem uniformizer_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π →
    V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 ∧
      ∀ y : IntermediateField.fixedField (inertia K V), V.valuation (y : Ω) < 1 →
        ∃ z : IntermediateField.fixedField (inertia K V), (z : Ω) ∈ V ∧
          y = algebraMap K _ (algebraMap R K π) * z := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ
  refine ⟨valuation_uniformizer_lt_one V hV hπ, fun y hy => ?_⟩
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hmem := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (y : Ω) y.2
    ((ValuationSubring.mem_nonunits_iff _).2 hy)
  refine ⟨y / algebraMap K _ (algebraMap R K π), ?_, ?_⟩
  · simpa using hmem
  · rw [mul_div_cancel₀]
    exact (map_ne_zero _).2 hπ0

end GlobalTheory.InertiaFixedUniformizer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOfValuationRingFixedFieldInertiaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_of_valuationRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π → V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 ∧ ∀ y : IntermediateField.fixedField (inertia K V), V.valuation (y : Ω) < 1 → ∃ z : IntermediateField.fixedField (inertia K V), (z : Ω) ∈ V ∧ y = algebraMap K _ (algebraMap R K π) * z := by
  first | exact @GlobalTheory.InertiaFixedUniformizer.uniformizer_fixedField_inertia | exact GlobalTheory.InertiaFixedUniformizer.uniformizer_fixedField_inertia | (intros; apply GlobalTheory.InertiaFixedUniformizer.uniformizer_fixedField_inertia <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMaps
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def leftInv : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g}
  zero_mem' _ _ := rfl
  add_mem' {ψ ψ'} h h' γ g := by simp [h γ g, h' γ g]
  smul_mem' c ψ h γ g := by simp [h γ g]

theorem lie_mem_leftInv (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ leftInv E a) : lie E a X ψ ∈ leftInv E a := by
  intro γ g
  have e : chart ψ.1 (ratGL E a γ * g) = chart ψ.1 g := by
    funext x
    simp only [chart, mul_assoc]
    split_ifs
    · exact h γ _
    · rfl
  simp only [lie_apply, lieD, e]


variable (E a) in
def fixL (L : Subgroup (GL (Fin a) (Af E))) : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ k ∈ L, finRep E a k ψ = ψ}
  zero_mem' k _ := map_zero _
  add_mem' {ψ ψ'} h h' k hk := by rw [map_add (f := _), h k hk, h' k hk]
  smul_mem' c ψ h k hk := by rw [map_smul, h k hk]

theorem lie_mem_fixL (L : Subgroup (GL (Fin a) (Af E))) (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ fixL E a L) :
    lie E a X ψ ∈ fixL E a L := by
  intro k hk
  have e := LinearMap.congr_fun (lie_rt_fin X k) ψ
  simp only [Module.End.mul_apply] at e
  change rt E a (finGL E a k) (lie E a X ψ) = lie E a X ψ
  rw [← e]
  exact congrArg (lie E a X) (h k hk)

theorem comp_mem_maps : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W)
    (T : W →ₗ[ℂ] Sm E a), T ∈ maps L W hW → ∀ z ∈ Zalg E a, z ∘ₗ T ∈ maps L W hW := by
  intro E _ _ _ a L W hW T hT z hz
  refine ⟨fun k w => ?_, fun w => ⟨?_, ?_, ?_⟩⟩
  · simp only [LinearMap.comp_apply, hT.1 k w]
    exact (LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E a k z hz) (T w))
  · exact Zalg_stable (V := tame E a) (fun X _ h => lie_mem_tame X h) hz _ (hT.2 w).1
  · exact Zalg_stable (V := leftInv E a) (fun X _ h => lie_mem_leftInv X h) hz _ (hT.2 w).2.1
  · exact Zalg_stable (V := fixL E a L) (fun X _ h => lie_mem_fixL L X h) hz _ (hT.2 w).2.2

end GlobalTheory.AutGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMapsStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_comp_mem_kinfEquivariantAutomorphicMaps : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) (T : W →ₗ[ℂ] Sm E a), T ∈ maps L W hW → ∀ z ∈ Zalg E a, z ∘ₗ T ∈ maps L W hW := by
  first | exact @GlobalTheory.AutGrowth.comp_mem_maps | exact GlobalTheory.AutGrowth.comp_mem_maps | (intros; apply GlobalTheory.AutGrowth.comp_mem_maps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGroupOfUnitMinorStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGroupOfUnitMinorStable
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adjugate_integral {n : ℕ} (X : Matrix (Fin n) (Fin n) k) (hX : ∀ i j, X i j ∈ 𝒪[k]) :
    ∀ i j, X.adjugate i j ∈ 𝒪[k] := by
  let X' : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨X i j, hX i j⟩
  have e : X = (algebraMap 𝒪[k] k).mapMatrix X' := by ext i j; rfl
  intro i j
  rw [e, ← RingHom.map_adjugate]
  exact (X'.adjugate i j).2

theorem mul_integral {a b c : ℕ} (X : Matrix (Fin a) (Fin b) k) (W : Matrix (Fin b) (Fin c) k)
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hW : ∀ i j, W i j ∈ 𝒪[k]) : ∀ i j, (X * W) i j ∈ 𝒪[k] := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hW l j)

theorem integral_of_mul {n d : ℕ} (M : Matrix (Fin n) (Fin n) k) (Z : Matrix (Fin n) (Fin d) k)
    (hZ : Z ∈ unitMinorSet k n d) (hMZ : ∀ i j, (M * Z) i j ∈ 𝒪[k]) : ∀ i j, M i j ∈ 𝒪[k] := by
  obtain ⟨hZi, f, hf⟩ := hZ
  set Zf := Z.submatrix id f with hZf
  have hsub : (M * Z).submatrix id f = M * Zf := by
    ext i j; simp [Zf, Matrix.mul_apply]
  have hdet : Zf.det ≠ 0 := by
    intro h0; rw [h0, map_zero] at hf; exact zero_ne_one hf
  have hM : M = (M * Z).submatrix id f * Zf⁻¹ := by
    rw [hsub, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.mul_one]
  have hZfi : ∀ i j, Zf i j ∈ 𝒪[k] := fun i j => hZi _ _
  have hinv : ∀ i j, Zf⁻¹ i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    refine Subring.mul_mem _ ?_ (adjugate_integral Zf hZfi i j)
    rw [Valuation.mem_integer_iff, map_inv₀, hf, inv_one]
  rw [hM]
  exact mul_integral _ _ (fun i j => hMZ _ _) hinv

theorem mem_KO_of_mul_mem_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k) (hY : Y ∈ unitMinorSet k n d)
    (hEY : E.val * Y ∈ unitMinorSet k n d) : E ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  refine (mem_KO_iff E).2 ⟨integral_of_mul _ Y hY hEY.1, integral_of_mul _ (E.val * Y) hEY ?_⟩
  rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  exact hY.1

end GlobalTheory.FullRankCoinv.UnitMinor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGroupOfUnitMinorStableStatement
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_group_of_unit_minor_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d →
    E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  first | exact @GlobalTheory.FullRankCoinv.UnitMinor.mem_KO_of_mul_mem_unitMinorSet | exact GlobalTheory.FullRankCoinv.UnitMinor.mem_KO_of_mul_mem_unitMinorSet | (intros; apply GlobalTheory.FullRankCoinv.UnitMinor.mem_KO_of_mul_mem_unitMinorSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNZOfPolAt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfPolarisedGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfPolarisedGenericFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

namespace GlobalTheory.ThetaDomain

theorem exists_sec_ne_zero_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) →
    ∃ (σ : LB.Sec t.PP.L) (k : t.PP.L.ι), σ.f k ≠ 0 := by
  intro E _ _ _ H R _ _ _ t hp
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨A, -, gen, -, hL, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt h₁ h₂ E H R t hp
  obtain ⟨O, hO, θ, hθ, -, nz⟩ := PushInv.pushInvertible_any h₂.secBaseChangeAny h₁.globalSectionsRank _ A
    (IsLocalRing.closedPoint (FractionRing R))
  obtain ⟨g, i, -, hi⟩ := nz _ hO
  obtain ⟨w, hw⟩ := LBIso.symm hL
  obtain ⟨s, hs⟩ := GlobalTheory.ThetaLocal.exists_sec_pull A.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom (jK R)))
    gen.hom.left w hw (O := A.A.hom ⁻¹ᵁ O) (fun z _ => by
      change A.A.hom (gen.hom.left z) ∈ O
      rwa [Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) (A.A.hom (gen.hom.left z))
        (IsLocalRing.closedPoint (FractionRing R))]) θ hθ
  have eg : gen.hom.left (gen.inv.left g) = g := congrArg (fun q : A.A ⟶ A.A => q.left g) gen.inv_hom_id
  obtain ⟨k, hk⟩ := hs (gen.inv.left g) i (by rw [eg]; exact hi)
  have hsk : s.f k ≠ 0 := fun e => by
    rw [e, Scheme.basicOpen_zero] at hk
    exact hk
  have := t.semi.separated
  have := t.semi.quasiCompact
  have : CompactSpace t.G.left := QuasiCompact.compactSpace_of_compactSpace t.G.hom
  have : QuasiSeparatedSpace t.G.left := quasiSeparatedSpace_of_quasiSeparated t.G.hom
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R (FractionRing R) (algebraMap R _)
    (RingHom.flat_algebraMap_iff.2 inferInstance) t.G.left t.G.hom _ _ _
    (IsPullback.of_hasPullback t.G.hom (jK R)) t.PP.L t.PP.isLB s
  by_contra hcon
  push Not at hcon
  refine hsk (fn_ext fun z hz => ?_)
  have hz' : pullback.fst t.G.hom (jK R) z ∈ t.PP.L.U (k PUnit.unit) := Set.mem_iInter.1 hz PUnit.unit
  rw [LBGerm.gs_zero _ z _ hz]
  refine (hu z (k PUnit.unit) hz').trans (Finset.sum_eq_zero fun i _ => ?_)
  rw [hcon, LBGerm.gs_zero _ z _ hz', mul_zero]

end GlobalTheory.ThetaDomain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfPolarisedGenericFibreStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_of_polarised_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → ∃ (σ : LB.Sec t.PP.L) (k : t.PP.L.ι), σ.f k ≠ 0 := by
  first | exact @GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt | exact GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt | (intros; apply GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ThetaNormal

theorem thetaNZ_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.admitted R (IsLocalRing.maximalIdeal R) → ∀ (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → GlobalTheory.LN.SplitOver t.G (IsLocalRing.maximalIdeal R) → GlobalTheory.LN.ThetaNZ t.G t.PP.L := by
  intro E _ _ _ H R _ _ _ hA t hpol hs
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨A, -, gen, hgen, hL, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt h1 h2 E H R t hpol
  have := hA.1.1
  obtain ⟨P, hPL, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric h1 R A t.G t.semi gen hgen t.PP t.cub t.sym
  have hσ : ∃ (σ : LB.Sec P.L.L) (k : P.L.L.ι), σ.f k ≠ 0 := by
    rw [hPL]; exact GlobalTheory.T.exists_nonzero_section_of_polarised_generic_fibre E H R t hpol
  obtain ⟨D, U, hUL, -⟩ := GlobalTheory.T.semiabelian_generic_fibre_polarization_iso R hA t.G P t.semi (hPL ▸ GlobalTheory.LN.UnifPrime.hypW_of_triple t) hs A gen hgen
    (hPL ▸ hL) hσ
  have key := GlobalTheory.T.exists_section_nonzero_on_closed_fibre_complete_local R hA.1.1 hA.1.2.2.1 hA.2.1 hA.2.2.1 D A t.G t.semi U
  rw [hUL, hPL] at key
  have := t.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint t.G _ key

end GlobalTheory.ThetaNormal
end
end
