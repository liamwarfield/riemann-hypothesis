module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCompChain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRemainderIsBigOAndTaylorFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRemainderIsBigOAndTaylorFlat
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_eq_partialSum {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) {f : (I → ℂ) → ℂ}
    {p : FormalMultilinearSeries ℂ (I → ℂ) ℂ} (hp : HasFPowerSeriesAt f p 0) (z : I → ℂ) :
    taylor N z f = p.partialSum (N + 1) z := by
  obtain ⟨r, hr⟩ := hp
  unfold taylor FormalMultilinearSeries.partialSum
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h1 := hr.factorial_smul z k
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 : (iteratedFDeriv ℂ k f 0 fun _ ↦ z) =
      ∑ s : Fin k → I, (∏ a, z (s a)) • iteratedFDeriv ℂ k f 0 fun a ↦ Pi.single (s a) 1 := by
    have hz : (fun _ : Fin k ↦ z) = fun _ ↦ ∑ i, z i • (Pi.single i (1 : ℂ) : I → ℂ) := by
      funext a j
      simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
  rw [h2, nsmul_eq_mul] at h1
  rw [← inv_mul_cancel_left₀ hk (p k fun _ ↦ z), h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [smul_eq_mul]
  ring

theorem diag_eq_zero_of_isBigO {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ) {f : E → ℂ}
    {p : FormalMultilinearSeries ℂ E ℂ} (hp : HasFPowerSeriesAt f p 0)
    (hf : f =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (N + 1)) (k : ℕ) : k ≤ N → ∀ y, (p k fun _ ↦ y) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have h1 := hp.isBigO_sub_partialSum_pow (k + 1)
    have hs : ∀ y, p.partialSum (k + 1) y = p k fun _ ↦ y := by
      intro y
      rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
        Finset.sum_eq_zero fun j hj ↦ ih j (Finset.mem_range.1 hj)
          (le_trans (Finset.mem_range.1 hj).le hk) y, zero_add]
    have h2 : (fun z : E ↦ ‖z‖ ^ (N + 1)) =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (k + 1) := by
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with z hz
      rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_of_le_one (norm_nonneg _) (by simpa using hz) (by omega)
    have h3 : (fun y : E ↦ p k fun _ ↦ y) =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (k + 1) := by
      refine ((hf.trans h2).sub h1).congr_left fun y ↦ ?_
      simp [hs]
    exact h3.continuousMultilinearMap_apply_eq_zero

theorem iteratedFDeriv_eq_zero_of_isBigO {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ)
    {f : E → ℂ} (ha : AnalyticAt ℂ f 0) (hf : f =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (N + 1)) {k : ℕ} (hk : k ≤ N)
    (v : Fin k → E) : iteratedFDeriv ℂ k f 0 v = 0 := by
  obtain ⟨p, hp⟩ := ha
  have h := diag_eq_zero_of_isBigO N hp hf k hk
  obtain ⟨r, hr⟩ := hp
  rw [hr.iteratedFDeriv_eq_sum_of_completeSpace, ← (p k).iteratedFDeriv_comp_diagonal 0 v]
  simp [h]

theorem taylor_remainder_and_flat : ∀ {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → ((fun z ↦ f z - GlobalTheory.PeriodFamily.taylor N z f) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) ∧ ((f =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) → ∀ {D : Type} [CommRing D] [Algebra ℂ D] (t : I → D), GlobalTheory.PeriodFamily.taylor N t f = 0) := by
  intro I _ _ N f ha
  refine ⟨?_, fun hf D _ _ t ↦ ?_⟩
  · obtain ⟨p, hp⟩ := ha
    refine (hp.isBigO_sub_partialSum_pow (N + 1)).congr_left fun z ↦ ?_
    rw [taylor_eq_partialSum N hp, zero_add]
  · unfold taylor
    refine Finset.sum_eq_zero fun k hk ↦ Finset.sum_eq_zero fun s _ ↦ ?_
    rw [iteratedFDeriv_eq_zero_of_isBigO N ha hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)), mul_zero,
      zero_smul]

end GlobalTheory.PeriodFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRemainderIsBigOAndTaylorFlatStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat : ∀ {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → ((fun z ↦ f z - GlobalTheory.PeriodFamily.taylor N z f) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) ∧ ((f =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) → ∀ {D : Type} [CommRing D] [Algebra ℂ D] (t : I → D), GlobalTheory.PeriodFamily.taylor N t f = 0) := by
  first | exact @GlobalTheory.PeriodFamily.taylor_remainder_and_flat | exact GlobalTheory.PeriodFamily.taylor_remainder_and_flat | (intros; apply GlobalTheory.PeriodFamily.taylor_remainder_and_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCompChain
set_option autoImplicit false

open Filter Topology

namespace GlobalTheory.PeriodFamily

section
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)

theorem taylor_finset_sum_chain {ι : Type} (S : Finset ι) (f : ι → (I → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    taylor N t (fun z ↦ ∑ i ∈ S, f i z) = ∑ i ∈ S, taylor N t (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.2.1 0
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [(GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).1 (f i) (fun z ↦ ∑ i ∈ S, f i z) (hf i)
      (Finset.analyticAt_fun_sum S fun j _ ↦ hf j), ih]

theorem taylor_finset_prod_chain (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) {ι : Type} (S : Finset ι)
    (f : ι → (I → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    taylor N t (fun z ↦ ∏ i ∈ S, f i z) = ∏ i ∈ S, taylor N t (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.2.1 1
  | insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    rw [GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht (f i) (fun z ↦ ∏ i ∈ S, f i z) (hf i)
      (Finset.analyticAt_fun_prod S fun j _ ↦ hf j), ih]

end

theorem taylor_comp_chain : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {K : Type} [Fintype K] [DecidableEq K] (Φ : (I → ℂ) → K → ℂ) (h : (K → ℂ) → ℂ), AnalyticAt ℂ Φ 0 → Φ 0 = 0 → AnalyticAt ℂ h 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (Φ z)) = GlobalTheory.PeriodFamily.taylor N (fun k ↦ GlobalTheory.PeriodFamily.taylor N t fun z ↦ Φ z k) h := by
  intro I _ _ D _ _ N t ht K _ _ Φ h hΦ h0 hh
  have hk : ∀ k, AnalyticAt ℂ (fun z ↦ Φ z k) 0 := fun k ↦ analyticAt_pi_iff.1 hΦ k
  have hhΦ : AnalyticAt ℂ (fun z ↦ h (Φ z)) 0 := AnalyticAt.comp (g := h) (f := Φ) (by rw [h0]; exact hh) hΦ
  have hprod : ∀ (k : ℕ) (s : Fin k → K), AnalyticAt ℂ (fun z ↦ ∏ a, Φ z (s a)) 0 := fun k s ↦
    Finset.analyticAt_fun_prod _ fun a _ ↦ hk (s a)
  set c : (k : ℕ) → (Fin k → K) → ℂ := fun k s ↦
    (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k h 0 fun a ↦ Pi.single (s a) 1 with hc
  have hP : (fun z ↦ taylor N (Φ z) h) =
      fun z ↦ ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a) := by
    funext z
    simp only [taylor, smul_eq_mul, hc]
  have hterm : ∀ (k : ℕ) (s : Fin k → K), AnalyticAt ℂ (fun z ↦ c k s * ∏ a, Φ z (s a)) 0 := fun k s ↦
    analyticAt_const.mul (hprod k s)
  have hin : ∀ k : ℕ, AnalyticAt ℂ (fun z ↦ ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)) 0 := fun k ↦
    Finset.analyticAt_fun_sum _ fun s _ ↦ hterm k s
  have hPa : AnalyticAt ℂ (fun z ↦ taylor N (Φ z) h) 0 := by
    rw [hP]
    exact Finset.analyticAt_fun_sum _ fun k _ ↦ hin k
  have hra : AnalyticAt ℂ (fun z ↦ h (Φ z) - taylor N (Φ z) h) 0 := hhΦ.sub hPa
  have htend : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have := hΦ.continuousAt.tendsto
    rwa [h0] at this
  have hO : Φ =O[𝓝 0] fun z : I → ℂ ↦ z := by
    have := hΦ.differentiableAt.isBigO_sub
    simpa [h0] using this
  have hr : (fun z ↦ h (Φ z) - taylor N (Φ z) h) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1) :=
    ((GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat N h hh).1.comp_tendsto htend).trans (hO.norm_norm.pow (N + 1))
  have hz : taylor N t (fun z ↦ h (Φ z) - taylor N (Φ z) h) = 0 := (GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat N _ hra).2 hr t
  have hsplit : (fun z ↦ h (Φ z)) = fun z ↦ (h (Φ z) - taylor N (Φ z) h) + taylor N (Φ z) h := by
    funext z; ring
  rw [hsplit, (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).1 _ _ hra hPa, hz, zero_add, hP,
    taylor_finset_sum_chain N t _ (fun k z ↦ ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)) hin]
  conv_rhs => rw [taylor]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [taylor_finset_sum_chain N t _ (fun s z ↦ c k s * ∏ a, Φ z (s a)) (hterm k)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [(GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.1 _ _ (hprod k s),
    taylor_finset_prod_chain N t ht _ (fun a z ↦ Φ z (s a)) fun a ↦ hk (s a)]

end GlobalTheory.PeriodFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCompChainStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_comp_eq_taylor_taylor_of_analyticAt : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {K : Type} [Fintype K] [DecidableEq K] (Φ : (I → ℂ) → K → ℂ) (h : (K → ℂ) → ℂ), AnalyticAt ℂ Φ 0 → Φ 0 = 0 → AnalyticAt ℂ h 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (Φ z)) = GlobalTheory.PeriodFamily.taylor N (fun k ↦ GlobalTheory.PeriodFamily.taylor N t fun z ↦ Φ z k) h := by
  first | exact @GlobalTheory.PeriodFamily.taylor_comp_chain | exact GlobalTheory.PeriodFamily.taylor_comp_chain | (intros; apply GlobalTheory.PeriodFamily.taylor_comp_chain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCoordAndEval
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCoordAndEval
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_coord_of_nilpotent {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D]
    [Algebra ℂ D] (N : ℕ) (t : I → D) (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (i : I) :
    taylor N t (fun z ↦ z i) = t i := by
  have hd : (fun y : I → ℂ ↦ fderiv ℂ (fun z : I → ℂ ↦ z i) y) =
      fun _ ↦ ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ↦ ℂ) i := by
    funext y
    exact (hasFDerivAt_apply i y).fderiv
  have h2 : ∀ (k : ℕ) (v : Fin (k + 1 + 1) → I → ℂ),
      iteratedFDeriv ℂ (k + 1 + 1) (fun z : I → ℂ ↦ z i) 0 v = 0 := by
    intro k v
    rw [iteratedFDeriv_succ_apply_right, hd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp
  have h1 : ∀ v : Fin 1 → I → ℂ, iteratedFDeriv ℂ 1 (fun z : I → ℂ ↦ z i) 0 v = v 0 i := by
    intro v
    rw [iteratedFDeriv_one_apply, congrFun hd 0]
    simp
  unfold taylor
  cases N with
  | zero =>
    have := ht fun _ ↦ i
    simp at this
    simp [this]
  | succ N =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [h2, mul_zero, zero_smul, Finset.sum_const_zero, zero_add, h1]
    rw [Finset.sum_eq_single (fun _ ↦ i)]
    · simp
    · intro s _ hs
      have : s 0 ≠ i := fun h ↦ hs (funext fun a ↦ by rw [Fin.fin_one_eq_zero a, h])
      simp [Pi.single_eq_of_ne' this]
    · simp

theorem taylor_coord_and_eval : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → (∀ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ z i) = t i) ∧ ∀ P : MvPolynomial I ℂ, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ MvPolynomial.eval z P) = MvPolynomial.aeval t P := by
  intro I _ _ D _ _ N t ht
  refine ⟨taylor_coord_of_nilpotent N t ht, fun P ↦ ?_⟩
  obtain ⟨hadd, -, hconst, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hc : ∀ i, AnalyticAt ℂ (fun z : I → ℂ ↦ z i) 0 := fun i ↦
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ↦ ℂ) i).analyticAt 0
  have han : ∀ Q : MvPolynomial I ℂ, AnalyticAt ℂ (fun z : I → ℂ ↦ MvPolynomial.eval z Q) 0 := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simpa using analyticAt_const
    | add p q hp hq => simpa using hp.fun_add hq
    | mul_X p i hp => simpa using hp.fun_mul (hc i)
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hconst a
  | add p q hp hq =>
    simp only [map_add (f := _)]
    rw [hadd _ _ (han p) (han q), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X]
    rw [GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht _ _ (han p) (hc i), hp, taylor_coord_of_nilpotent N t ht]

end GlobalTheory.PeriodFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCoordAndEvalStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_coord_and_taylor_eval_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → (∀ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ z i) = t i) ∧ ∀ P : MvPolynomial I ℂ, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ MvPolynomial.eval z P) = MvPolynomial.aeval t P := by
  first | exact @GlobalTheory.PeriodFamily.taylor_coord_and_eval | exact GlobalTheory.PeriodFamily.taylor_coord_and_eval | (intros; apply GlobalTheory.PeriodFamily.taylor_coord_and_eval <;> assumption)
end
end

open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_shear : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {g : ℕ} (h : (I → ℂ) × (Fin g → ℂ) → ℂ) (τ : (I → ℂ) → Fin g → ℂ) (w : Fin g → ℂ), AnalyticAt ℂ τ 0 → AnalyticAt ℂ h (0, w + τ 0) → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (z, w + τ z)) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun a ↦ GlobalTheory.PeriodFamily.taylor N t (fun z ↦ τ z a) - algebraMap ℂ D (τ 0 a)) (fun x : I ⊕ Fin g → ℂ ↦ h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a))) := by
  intro I _ _ D _ _ N t ht g h τ w hτ hh
  have hτa : ∀ a, AnalyticAt ℂ (fun z ↦ τ z a) 0 := fun a ↦ analyticAt_pi_iff.1 hτ a
  have hco : ∀ {J : Type} [Fintype J] (j : J) (x : J → ℂ), AnalyticAt ℂ (fun z : J → ℂ ↦ z j) x :=
    fun j x ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) j).analyticAt x
  have hΦ : AnalyticAt ℂ (fun z : I → ℂ ↦ (Sum.elim z (fun a ↦ τ z a - τ 0 a) : I ⊕ Fin g → ℂ)) 0 := by
    refine analyticAt_pi_iff.2 ?_
    rintro (i | a)
    · exact hco i 0
    · exact (hτa a).sub analyticAt_const
  have hΦ0 : (fun z : I → ℂ ↦ (Sum.elim z (fun a ↦ τ z a - τ 0 a) : I ⊕ Fin g → ℂ)) 0 = 0 := by
    funext k
    rcases k with i | a <;> simp
  have hH : AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
      h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a))) 0 := by
    have hin : AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
        ((fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a)) : (I → ℂ) × (Fin g → ℂ))) 0 := by
      refine AnalyticAt.prod (analyticAt_pi_iff.2 fun i ↦ hco _ 0) ?_
      refine analyticAt_pi_iff.2 fun a ↦ ?_
      exact (analyticAt_const (v := (w + τ 0) a)).add (hco (Sum.inr a) 0)
    refine AnalyticAt.comp_of_eq hh hin ?_
    ext <;> simp
  have key := GlobalTheory.T.taylor_comp_eq_taylor_taylor_of_analyticAt N t ht _ _ hΦ hΦ0 hH
  obtain ⟨hadd, -, hconst, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have e1 : (fun z : I → ℂ ↦ h (z, w + τ z)) = fun z : I → ℂ ↦
      (fun x : I ⊕ Fin g → ℂ ↦ h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a)))
        (Sum.elim z (fun a ↦ τ z a - τ 0 a)) := by
    funext z
    congr 1
    ext <;> simp
  rw [e1, key]
  congr 1
  funext k
  rcases k with i | a
  · exact (GlobalTheory.T.taylor_coord_and_taylor_eval_of_prod_eq_zero N t ht).1 i
  · have := hadd (fun z ↦ τ z a) (fun _ ↦ - τ 0 a) (hτa a) analyticAt_const
    rw [hconst, map_neg] at this
    simpa [sub_eq_add_neg] using this

end GlobalTheory.PeriodFamily
