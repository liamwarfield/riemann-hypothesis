module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureQuotientUnitaryJVectorStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwDelta

variable {n : ℕ}

theorem exists_cont_detOn (V : Submodule ℂ (Fin n → ℂ)) :
    ∃ D : Matrix (Fin n) (Fin n) ℂ → ℝ, Continuous D ∧
      ∀ X, (∀ y ∈ V, X *ᵥ y ∈ V) → detOn X V = D X := by
  obtain ⟨U, hVU⟩ := Submodule.exists_isCompl V
  let p := Submodule.projectionOnto V U hVU
  let b := Module.finBasis ℂ V
  refine ⟨fun X => ‖(Matrix.of fun i k => b.repr (p (X *ᵥ (b k : Fin n → ℂ))) i).det‖, ?_, ?_⟩
  · apply Continuous.norm
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i k
    have hlin : Continuous fun y : Fin n → ℂ => b.repr (p y) i :=
      ((b.coord i).comp p).continuous_of_finiteDimensional
    exact hlin.comp (continuous_id.matrix_mulVec continuous_const)
  · intro X hX
    have h' : ∀ y ∈ V, Matrix.toLin' X y ∈ V := fun y hy => by
      simpa [Matrix.toLin'_apply] using hX y hy
    have e : ∀ k, p (X *ᵥ (b k : Fin n → ℂ)) = (Matrix.toLin' X).restrict h' (b k) := by
      intro k
      have hp : p (X *ᵥ (b k : Fin n → ℂ)) = ⟨X *ᵥ (b k : Fin n → ℂ), hX _ (b k).2⟩ :=
        Submodule.projectionOnto_apply_left hVU ⟨X *ᵥ (b k : Fin n → ℂ), hX _ (b k).2⟩
      rw [hp]
      apply Subtype.ext
      simp [LinearMap.restrict_apply, Matrix.toLin'_apply]
    rw [detOn, dite_eq_left h', ← LinearMap.det_toMatrix b]
    congr 2
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.of_apply, e k]

theorem detOn_one (V : Submodule ℂ (Fin n → ℂ)) : detOn (1 : Matrix (Fin n) (Fin n) ℂ) V = 1 := by
  have h' : ∀ y ∈ V, Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ) y ∈ V := fun y hy => by simpa using hy
  rw [detOn, dite_eq_left h']
  have hid : (Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ)).restrict h' = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (by simp [LinearMap.restrict_apply])
  rw [hid, LinearMap.det_id, norm_one]

private theorem detOn_le_one_of_unitary_of_invariant (U : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ))
    (hU : Uᴴ * U = 1) (hV : ∀ y ∈ V, U *ᵥ y ∈ V) : detOn U V ≤ 1 := by
  obtain ⟨D, hDc, hD⟩ := exists_cont_detOn V
  have hKc : IsCompact {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * X = 1} := by
    have hcl : IsClosed {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * X = 1} :=
      isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
        Metric.closedBall (0 : ℂ) 1 : Set (Matrix (Fin n) (Fin n) ℂ)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    refine hbox.of_isClosed_subset hcl ?_
    intro X hX
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i k
    exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hX) i k
  have hUg : U ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hU
  have hpow : ∀ k : ℕ, (∀ y ∈ V, U ^ k *ᵥ y ∈ V) ∧ detOn (U ^ k) V = detOn U V ^ k := by
    intro k
    induction k with
    | zero => exact ⟨fun y hy => by simpa using hy, by simpa using detOn_one V⟩
    | succ k ih =>
      have hs : ∀ y ∈ V, U ^ (k + 1) *ᵥ y ∈ V := fun y hy => by
        rw [pow_succ, ← Matrix.mulVec_mulVec]
        exact ih.1 _ (hV y hy)
      refine ⟨hs, ?_⟩
      rw [pow_succ, GlobalTheory.FlagMeas.SizeMove.detOn_mul _ _ V ih.1 hV, ih.2, pow_succ]
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hDc.continuousOn
  by_contra hlt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.mp hlt)
  have hmem : (U ^ k)ᴴ * U ^ k = 1 := Matrix.mem_unitaryGroup_iff'.1 (pow_mem hUg k)
  have hb := hC (U ^ k) hmem
  rw [← hD _ (hpow k).1, (hpow k).2, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (GlobalTheory.FlagMeas.SizeMove.detOn_nonneg U V) k)] at hb
  linarith

theorem detOn_le_one {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    {l : Formalism.REAL.UJ ε} (hl : l ∈ maxK ε ∩ flagM ε W) (i : Fin (a + 1)) : detOn (uMat l) (W i) ≤ 1 := by
  have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
  exact detOn_le_one_of_unitary_of_invariant _ _ hl.1 (fun y hy => (hl2 i y hy).1)

theorem detOn_eq_one {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    {l : Formalism.REAL.UJ ε} (hl : l ∈ maxK ε ∩ flagM ε W) (i : Fin (a + 1)) : detOn (uMat l) (W i) = 1 := by
  have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
  have hU : (uMat l)ᴴ * uMat l = 1 := hl.1
  have hU' : (uMat l)ᴴᴴ * (uMat l)ᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have h1 := detOn_le_one hl i
  have h2 := detOn_le_one_of_unitary_of_invariant _ (W i) hU' (fun y hy => (hl2 i y hy).2)
  have hprod : detOn ((uMat l)ᴴ) (W i) * detOn (uMat l) (W i) = 1 := by
    rw [← GlobalTheory.FlagMeas.SizeMove.detOn_mul _ _ _ (fun y hy => (hl2 i y hy).2) (fun y hy => (hl2 i y hy).1), hU,
      detOn_one]
  have h3 := GlobalTheory.FlagMeas.SizeMove.detOn_nonneg (uMat l) (W i)
  have h4 := GlobalTheory.FlagMeas.SizeMove.detOn_nonneg ((uMat l)ᴴ) (W i)
  exact le_antisymm h1 (by nlinarith)

theorem measurable_layerProd {a : ℕ} (j : Fin a → ℕ) :
    Measurable fun τ : Fin a → ℝ => layerProd n 1 j τ id := by
  unfold layerProd
  fun_prop

theorem continuousAt_layerProd {a : ℕ} (j : Fin a → ℕ) :
    Filter.Tendsto (fun τ : Fin a → ℝ => layerProd n 1 j τ id) (nhds 1) (nhds 1) := by
  have hc : ContinuousAt (fun τ : Fin a → ℝ => layerProd n 1 j τ id) 1 := by
    unfold layerProd
    fun_prop (disch := simp)
  have h1 : layerProd n 1 j (1 : Fin a → ℝ) id = 1 := by simp [layerProd]
  simpa [h1] using hc.tendsto

open scoped Matrix.Norms.Frobenius in
theorem exists_ball {s : Set (Matrix (Fin n) (Fin n) ℂ)} (hs : s ∈ nhds 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ X, nrm (X - 1) < t → X ∈ s := by
  obtain ⟨t, ht, hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨t, ht, fun X hX => hsub ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, ← nrm_eq]
  exact hX

theorem dlt_props : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), Measurable (dlt (ε := ε) j W) ∧ (∀ l ∈ maxK ε ∩ flagM ε W, ∀ m ∈ flagM ε W, dlt j W (m * l) = dlt j W m) ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ m ∈ flagM ε W, nrm (uMat m - 1) < t → dlt j W m ≤ ENNReal.ofReal (1 + η) ∧ 1 ≤ ENNReal.ofReal (1 + η) * dlt j W m := by
  intro n ε a j W
  refine ⟨?_, ?_, ?_⟩
  · unfold dlt
    exact ENNReal.measurable_ofReal.comp ((measurable_layerProd j).comp
      (Measurable.of_eval fun i => measurable_locSize_uMat n ε a j W i))
  · intro l hl m hm
    have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
    have hm2 : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hmul : uMat (m * l) = uMat m * uMat l := rfl
    have hloc : locSize j W (uMat (m * l)) = locSize j W (uMat m) := by
      funext i
      simp only [locSize]
      rw [hmul,
        GlobalTheory.FlagMeas.SizeMove.detOn_mul (uMat m) (uMat l) (W i.succ) (fun y hy => (hm2 i.succ y hy).1)
          (fun y hy => (hl2 i.succ y hy).1),
        GlobalTheory.FlagMeas.SizeMove.detOn_mul (uMat m) (uMat l) (W i.castSucc) (fun y hy => (hm2 i.castSucc y hy).1)
          (fun y hy => (hl2 i.castSucc y hy).1),
        detOn_eq_one hl i.succ, detOn_eq_one hl i.castSucc, mul_one, mul_one]
    unfold dlt
    rw [hloc]
  · intro η hη
    choose D hDc hD using fun i : Fin (a + 1) => exists_cont_detOn (W i)
    have hD1 : ∀ i, D i 1 = 1 := fun i => by
      rw [← hD i 1 (fun y hy => by simpa using hy), detOn_one]
    set G : Matrix (Fin n) (Fin n) ℂ → Fin a → ℝ :=
      fun X i => (D i.succ X / D i.castSucc X) ^ (-(1 : ℝ) / j i) with hGdef
    have hG : Filter.Tendsto G (nhds 1) (nhds 1) := by
      rw [tendsto_pi_nhds]
      intro i
      have hc : ContinuousAt (fun X => (D i.succ X / D i.castSucc X) ^ (-(1 : ℝ) / j i)) 1 :=
        ((hDc _).continuousAt.div (hDc _).continuousAt (by simp [hD1])).rpow_const
          (Or.inl (by simp [hD1]))
      have ht := hc.tendsto
      simp only [hD1, div_one, Real.one_rpow] at ht
      exact ht
    have hF := (continuousAt_layerProd (n := n) j).comp hG
    have hpos : 0 < 1 + η := by linarith
    have hU : Set.Ioo (1 / (1 + η)) (1 + η) ∈ nhds (1 : ℝ) :=
      Ioo_mem_nhds ((div_lt_one hpos).2 (by linarith)) (by linarith)
    obtain ⟨t, ht, hball⟩ := exists_ball (Filter.tendsto_def.1 hF _ hU)
    refine ⟨t, ht, fun m hm hmt => ?_⟩
    have hm2 : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hin := hball _ hmt
    have hGm : G (uMat m) = locSize j W (uMat m) := by
      funext i
      simp only [hGdef, locSize]
      rw [hD i.succ _ (fun y hy => (hm2 i.succ y hy).1), hD i.castSucc _ (fun y hy => (hm2 i.castSucc y hy).1)]
    simp only [Set.mem_preimage, Function.comp_apply, hGm, Set.mem_Ioo] at hin
    obtain ⟨hlo, hhi⟩ := hin
    unfold dlt
    refine ⟨ENNReal.ofReal_le_ofReal hhi.le, ?_⟩
    rw [← ENNReal.ofReal_mul hpos.le, ENNReal.one_le_ofReal]
    rw [div_lt_iff₀ hpos] at hlo
    linarith [mul_comm (layerProd n 1 j (locSize j W (uMat m)) id) (1 + η)]

end GlobalTheory.IwDelta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusPropertiesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviFactorInverseModulus_properties : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), Measurable (dlt (ε := ε) j W) ∧ (∀ l ∈ maxK ε ∩ flagM ε W, ∀ m ∈ flagM ε W, dlt j W (m * l) = dlt j W m) ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ m ∈ flagM ε W, nrm (uMat m - 1) < t → dlt j W m ≤ ENNReal.ofReal (1 + η) ∧ 1 ≤ ENNReal.ofReal (1 + η) * dlt j W m := by
  first | exact @GlobalTheory.IwDelta.dlt_props | exact GlobalTheory.IwDelta.dlt_props | (intros; apply GlobalTheory.IwDelta.dlt_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeVolumeUnitaryGroupEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussDensSphere
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Sphere

private theorem norm_toLp_eq_sqrt_sum_norm_sq (n : ℕ) (y : Fin (n + 1) → ℂ) :
    ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin (n + 1)))‖ = Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
  simp [EuclideanSpace.norm_eq]

private theorem volume_complex_unit_ball_toReal (n : ℕ) :
    (volume {y : Fin (n + 1) → ℂ | Real.sqrt (∑ i, ‖y i‖ ^ 2) < 1}).toReal =
      Real.pi ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hset : {y : Fin (n + 1) → ℂ | Real.sqrt (∑ i, ‖y i‖ ^ 2) < 1} =
      {y : Fin (n + 1) → ℂ | ∑ i, ‖y i‖ ^ (2 : ℝ) < 1} := by
    ext y
    simp only [Set.mem_setOf_eq, Real.rpow_two]
    rw [Real.sqrt_lt' one_pos, one_pow]
  rw [hset, Complex.volume_sum_rpow_lt_one (Fin (n + 1)) (by norm_num : (1 : ℝ) ≤ 2)]
  have h2 : (2 : ℝ) / 2 + 1 = 2 := by norm_num
  have h3 : 2 * (Fintype.card (Fin (n + 1)) : ℝ) / 2 + 1 = ((n + 1 : ℕ) : ℝ) + 1 := by
    simp only [Fintype.card_fin]; push_cast; ring
  rw [h2, h3, Real.Gamma_two, Real.Gamma_nat_eq_factorial, mul_one, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

theorem integral_radial (n : ℕ) (f : ℝ → ℝ) :
    ∫ y : Fin (n + 1) → ℂ, f (Real.sqrt (∑ i, ‖y i‖ ^ 2)) =
      2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) * ∫ r in Set.Ioi (0 : ℝ), r ^ (2 * n + 1) * f r := by

  let e := MeasurableEquiv.toLp 2 (Fin (n + 1) → ℂ)
  let μ : Measure (EuclideanSpace ℂ (Fin (n + 1))) := (volume : Measure (Fin (n + 1) → ℂ)).map e
  haveI : μ.IsAddHaarMeasure := by
    have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℂ)).symm.isAddHaarMeasure_map
      (volume : Measure (Fin (n + 1) → ℂ))
    exact h
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) = 2 * (n + 1) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hball : μ.real (Metric.ball 0 1) = Real.pi ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    rw [Measure.real, MeasurableEquiv.map_apply, ← volume_complex_unit_ball_toReal n]
    congr 2
    ext y
    simp [e, norm_toLp_eq_sqrt_sum_norm_sq]
  have key := integral_fun_norm_addHaar μ f
  rw [integral_map_equiv] at key
  simp only [e, MeasurableEquiv.toLp_apply, norm_toLp_eq_sqrt_sum_norm_sq] at key
  rw [key, hdim, hball, show 2 * (n + 1) - 1 = 2 * n + 1 by omega, nsmul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  rw [Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem ball_integral (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ y in {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}, gauss y =
      2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) *
        ∫ r in (0 : ℝ)..Real.sqrt t, r ^ (2 * n + 1) * Real.exp (-r ^ 2) := by
  have hq (y : Fin (n + 1) → ℂ) : qEps (allPos (n + 1)) y = ∑ i, ‖y i‖ ^ 2 := by
    simp [qEps, allPos]
  have hmeas : MeasurableSet {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t} := by
    simp only [hq]
    exact measurableSet_le (by fun_prop) measurable_const

  have hind : {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}.indicator gauss =
      fun y => (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2))
        (Real.sqrt (∑ i, ‖y i‖ ^ 2)) := by
    funext y
    have hs : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
    by_cases hy : ∑ i, ‖y i‖ ^ 2 ≤ t
    · have hy' : Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt t := Real.sqrt_le_sqrt hy
      rw [Set.indicator_of_mem (by simpa [hq] using hy), Set.indicator_of_mem (show Real.sqrt (∑ i, ‖y i‖ ^ 2) ∈ Set.Iic (Real.sqrt t) from hy'),
        Real.sq_sqrt hs, gauss]
    · have hy' : ¬ Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt t := by
        intro h
        exact hy ((Real.sqrt_le_sqrt_iff ht.le).mp h)
      rw [Set.indicator_of_notMem (by simpa [hq] using hy), Set.indicator_of_notMem (show Real.sqrt (∑ i, ‖y i‖ ^ 2) ∉ Set.Iic (Real.sqrt t) from hy')]
  rw [← integral_indicator hmeas, hind,
    integral_radial n ((Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2))),
    intervalIntegral.integral_of_le (Real.sqrt_nonneg t)]
  congr 1
  have hfun : (fun r : ℝ => r ^ (2 * n + 1) *
      (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) r) =
      (Set.Iic (Real.sqrt t)).indicator (fun r => r ^ (2 * n + 1) * Real.exp (-r ^ 2)) := by
    funext r
    by_cases hr : r ∈ Set.Iic (Real.sqrt t)
    · simp [Set.indicator_of_mem hr]
    · simp [Set.indicator_of_notMem hr]
  rw [hfun, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]

theorem gaussDens_sphere (n : ℕ) :
    gaussDens (allPos (n + 1)) 1 = Real.pi ^ (n + 1) * Real.exp (-1) / (n.factorial : ℝ) := by
  set C : ℝ := 2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) with hC
  set h : ℝ → ℝ := fun r => r ^ (2 * n + 1) * Real.exp (-r ^ 2) with hh

  have hF : (fun t : ℝ => ∫ y in {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}, gauss y) =ᶠ[nhds 1]
      fun t => C * ∫ r in (0 : ℝ)..Real.sqrt t, h r := by
    filter_upwards [lt_mem_nhds one_pos] with t ht using ball_integral n ht
  have hcont : Continuous h := by rw [hh]; fun_prop
  have h1 := (hcont.integral_hasStrictDerivAt 0 (Real.sqrt 1)).hasDerivAt
  have h2 := Real.hasDerivAt_sqrt (one_ne_zero : (1 : ℝ) ≠ 0)
  have hd := (h1.comp (1 : ℝ) h2).const_mul C
  rw [gaussDens]
  refine (hF.deriv_eq.trans hd.deriv).trans ?_
  simp only [hh, hC, Real.sqrt_one, one_pow, one_mul]
  field_simp
  try ring

end GlobalTheory.GaussMean.Sphere
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeVolumeUnitaryGroupEq
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

namespace GlobalTheory.UnitaryVolume

theorem Jm_allPos (N : ℕ) : Formalism.REAL.Jm (allPos N) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem mul_conjTranspose_self {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) : uMat g * (uMat g)ᴴ = 1 := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm (allPos N) * uMat g = Formalism.REAL.Jm (allPos N) := g.2
  rw [Jm_allPos, Matrix.mul_one] at h
  exact mul_eq_one_comm.1 h

theorem row_norm {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) (i : Fin N) : ∑ k, ‖uMat g i k‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (mul_conjTranspose_self g) i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ k, ‖uMat g i k‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Complex.mul_conj' _).symm
  exact_mod_cast h2

theorem muG_univ_lt_top (N : ℕ) : Formalism.REAL.muG (allPos N) Set.univ < ⊤ := by
  have h := Formalism.REAL.ballFinite N (allPos N) N
  have e : {g : Formalism.REAL.UJ (allPos N) | Formalism.REAL.hsG g ≤ (N : ℝ)} = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    change ∑ i, ∑ k, ‖uMat g i k‖ ^ 2 ≤ (N : ℝ)
    simp [row_norm]
  rwa [e] at h

theorem muG_univ_ne_zero (N : ℕ) : Formalism.REAL.muG (allPos N) Set.univ ≠ 0 :=
  (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'

theorem gauss_inv_single {n : ℕ} (g : Formalism.REAL.UJ (allPos (n + 1))) :
    gauss ((uMat g)⁻¹ *ᵥ (Pi.single 0 1 : Fin (n + 1) → ℂ)) = Real.exp (-1) := by
  rw [Matrix.inv_eq_right_inv (mul_conjTranspose_self g), gauss]
  congr 2
  rw [← row_norm g 0]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mulVec_single_one, Matrix.conjTranspose_apply]

theorem volU_succ (n : ℕ) :
    volU (n + 1) = volU n * (2 ^ (n + 1) * Real.pi ^ (n + 1) / (n.factorial : ℝ)) := by
  have h : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right, Nat.choose_succ_succ' n 1]
    simp [add_comm]
  unfold volU sphV
  rw [Finset.prod_Icc_succ_top (by omega), h]
  simp only [Nat.add_sub_cancel]
  ring

theorem volU_pos (n : ℕ) : 0 < volU n := by
  unfold volU sphV
  have := Real.pi_pos
  exact mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem volume_zero (c : ℝ) (hc : IsGauge (allPos 0) c) :
    c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal = volU 0 := by
  have h1 : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (0 ^ 2))) 1)).toReal = 1 := by
    change (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal = 1
    have e : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1 = Set.univ :=
      Set.eq_univ_of_forall fun x => by rw [Subsingleton.elim x 0]; simp
    rw [e, ← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage MeasurableSet.univ.nullMeasurableSet]
    simp [volume_pi, Measure.pi_univ]
  unfold IsGauge at hc
  rw [h1] at hc
  have h2 : Filter.Tendsto (fun _ : ℝ => c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have e : {g : Formalism.REAL.UJ (allPos 0) | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} = Set.univ :=
      Set.eq_univ_of_forall fun g => by
        simpa [Formalism.REAL.hs] using le_of_lt hr
    rw [e]
    simp
  rw [tendsto_const_nhds_iff.1 h2]
  simp [volU, sphV]

theorem volume_unitary : ∀ (N : ℕ) (c : ℝ), IsGauge (allPos N) c →
    c * (Formalism.REAL.muG (allPos N) Set.univ).toReal = volU N := by
  intro N
  induction N with
  | zero => exact volume_zero
  | succ n ih =>
    intro c hc
    obtain ⟨c₀, hc₀, -, hu⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique (n + 1) (allPos (n + 1))
    have hcpos : 0 < c := by rw [hu c hc]; exact hc₀
    obtain ⟨c', hc'pos, hc', -⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique n (allPos n)
    have hv := ih c' hc'
    let x₀ : Fin (n + 1) → ℂ := Pi.single 0 1
    let B : Matrix (Fin (n + 1)) (Fin n) ℂ := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix id Fin.succ
    have hq : qEps (allPos (n + 1)) x₀ = sgn ℝ true := by
      simp [qEps, sgn, allPos, x₀, Fin.sum_univ_succ]
    have hx : star x₀ ᵥ* (Formalism.REAL.Jm (allPos (n + 1)) * B) = 0 := by
      rw [Jm_allPos, Matrix.one_mul]
      funext k
      simp [Matrix.vecMul, dotProduct, x₀, B, Fin.sum_univ_succ, Matrix.one_apply, (Fin.succ_ne_zero k).symm]
    have hB : Bᴴ * Formalism.REAL.Jm (allPos (n + 1)) * B = Formalism.REAL.Jm (allPos n) := by
      rw [Jm_allPos, Jm_allPos, Matrix.mul_one]
      ext a b
      simp [Matrix.mul_apply, B, Matrix.one_apply, eq_comm]
    obtain ⟨j, -, hj⟩ := GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal (n + 1) n _ _ true x₀ B rfl
      hq hx hB
    have hV : ENNReal.ofReal c' * Formalism.REAL.muG (allPos n) Set.univ = ENNReal.ofReal (volU n) := by
      rw [← hv, ENNReal.ofReal_mul hc'pos.le, ENNReal.ofReal_toReal (muG_univ_lt_top n).ne]
    have key := GlobalTheory.T.gauge_measure_quotient_unitaryJ_vector_stabiliser n _ _ true x₀ B j hq hx hB hj c c' hc hc'
      (fun _ => ENNReal.ofReal (volU n)⁻¹) measurable_const (fun g => by
        rw [lintegral_const, mul_left_comm, hV, ← ENNReal.ofReal_mul (inv_pos.2 (volU_pos n)).le,
          inv_mul_cancel₀ (volU_pos n).ne', ENNReal.ofReal_one])
    have hs : sgn ℝ true = 1 := by simp [sgn]
    simp only [x₀, gauss_inv_single, lintegral_const] at key
    rw [hs, GlobalTheory.GaussMean.Sphere.gaussDens_sphere] at key
    have k2 := congrArg ENNReal.toReal key
    have hp := volU_pos n
    have hπ := Real.pi_pos
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal (inv_pos.2 hp).le,
      ENNReal.toReal_ofReal (by positivity)] at k2
    rw [volU_succ]
    have he := Real.exp_pos (-1)
    have hf : (0 : ℝ) < n.factorial := by positivity
    field_simp at k2 ⊢
    linarith

end GlobalTheory.UnitaryVolume
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeVolumeUnitaryGroupEqStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq : ∀ (N : ℕ) (c : ℝ), IsGauge (allPos N) c → c * (Formalism.REAL.muG (allPos N) Set.univ).toReal = volU N := by
  first | exact @GlobalTheory.UnitaryVolume.volume_unitary | exact GlobalTheory.UnitaryVolume.volume_unitary | (intros; apply GlobalTheory.UnitaryVolume.volume_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianTermMeasurableAndStabilizerInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianTermMeasurableAndStabilizerInvariant
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem mem_lamX_mul_right (I : AutInst) (x : Fin I.n → I.E) (g : I.Gf) (k : I.Gf) (hk : k ∈ I.Kset) :
    x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g) := by
  have h := (GlobalTheory.PointLattice.lamX_selfDual I (1, g)).2.2.2.2 (1, k) hk
  rw [Prod.mk_mul_mk, mul_one] at h
  rw [h]

theorem uMat_inv_eq {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : (uMat g)⁻¹ = uMat g⁻¹ :=
  (Matrix.coe_units_inv (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)).symm

theorem gaussAt_meas_inv : ∀ (I : AutInst) (x : Fin I.n → I.E), IsOpen {h : I.Gf | x ∈ lamX I (1, h)} ∧ (∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x))) ∧ (∀ h g : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → (x ∈ lamX I (1, h * g) ↔ x ∈ lamX I (1, g))) ∧ (∀ g : I.Gf, ∀ k ∈ I.Kset, x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g)) ∧ ∀ v (h g : Formalism.REAL.UJ (I.ε v)), uMat h *ᵥ infVec I v x = infVec I v x → (uMat (h * g))⁻¹ *ᵥ infVec I v x = (uMat g)⁻¹ *ᵥ infVec I v x := by
  intro I x
  refine ⟨?_, fun v => ?_, fun h g hh => ?_, fun g k hk => mem_lamX_mul_right I x g k hk, fun v h g hh => ?_⟩
  · rw [isOpen_iff_mem_nhds]
    intro g hg
    have hK : IsOpen I.Kset := (GlobalTheory.adelicStab_isCompact_isOpen I).2.1
    have hc : Continuous fun h : I.Gf => g⁻¹ * h := continuous_const.mul continuous_id
    have h1 : (1 : I.Gf) ∈ I.Kset := (Ksub I).one_mem
    refine Filter.mem_of_superset ((hK.preimage hc).mem_nhds (by simpa using h1)) fun h hh => ?_
    have := (mem_lamX_mul_right I x g (g⁻¹ * h) hh).2 hg
    rwa [mul_inv_cancel_left] at this
  · refine Continuous.measurable (ENNReal.continuous_ofReal.comp ?_)
    have hc : Continuous fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹ := by
      simp only [uMat_inv_eq]
      exact Units.continuous_coe_inv.comp continuous_subtype_val
    have hc2 := hc.matrix_mulVec (continuous_const (y := infVec I v x))
    unfold gauss
    refine Real.continuous_exp.comp (Continuous.neg (continuous_finsetSum _ fun i _ => ?_))
    exact (((continuous_apply i).comp hc2).norm).pow 2
  · rw [(GlobalTheory.PointLattice.lamX_selfDual I (1, h * g)).1, (GlobalTheory.PointLattice.lamX_selfDual I (1, g)).1]
    have h1 : I.fmat g⁻¹ = I.fmat (h * g)⁻¹ * I.fmat h := by
      have : g⁻¹ = (h * g)⁻¹ * h := by simp
      rw [this]; rfl
    change I.fmat (h * g)⁻¹ *ᵥ afVec I x ∈ I.Lf ↔ I.fmat g⁻¹ *ᵥ afVec I x ∈ I.Lf
    rw [h1, ← Matrix.mulVec_mulVec, hh]
  · rw [uMat_inv_eq, uMat_inv_eq]
    have h1 : uMat g⁻¹ = uMat (h * g)⁻¹ * uMat h := by
      have : g⁻¹ = (h * g)⁻¹ * h := by simp
      rw [this]; rfl
    rw [h1, ← Matrix.mulVec_mulVec, hh]

end GlobalTheory.StabUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianTermMeasurableAndStabilizerInvariantStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianTerm_measurable_and_stabilizer_invariant : ∀ (I : AutInst) (x : Fin I.n → I.E), IsOpen {h : I.Gf | x ∈ lamX I (1, h)} ∧ (∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x))) ∧ (∀ h g : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → (x ∈ lamX I (1, h * g) ↔ x ∈ lamX I (1, g))) ∧ (∀ g : I.Gf, ∀ k ∈ I.Kset, x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g)) ∧ ∀ v (h g : Formalism.REAL.UJ (I.ε v)), uMat h *ᵥ infVec I v x = infVec I v x → (uMat (h * g))⁻¹ *ᵥ infVec I v x = (uMat g)⁻¹ *ᵥ infVec I v x := by
  first | exact @GlobalTheory.StabUnfold.gaussAt_meas_inv | exact GlobalTheory.StabUnfold.gaussAt_meas_inv | (intros; apply GlobalTheory.StabUnfold.gaussAt_meas_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagRadicalLowersLeviKeeps
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagRadicalLowersLeviKeeps
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.FlagMem

variable {n : ℕ} {ε : Fin n → Bool}

theorem form_mul (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star (uMat g⁻¹ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  simpa using GlobalTheory.FlagLeviGroup.form_inv g⁻¹ x y

theorem Jm_mul_self : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem Jm_mul_conjTranspose (m : Formalism.REAL.UJ ε) :
    Formalism.REAL.Jm ε * (uMat m)ᴴ = uMat m⁻¹ * Formalism.REAL.Jm ε := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, GlobalTheory.FlagLeviGroup.uMat_mul_inv, Matrix.mul_one]
  calc Formalism.REAL.Jm ε * (uMat m)ᴴ
      = Formalism.REAL.Jm ε * ((uMat m)ᴴ * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = _ := by rw [← h1, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem form_conjTranspose (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat m)ᴴ *ᵥ y)) = star ((uMat m⁻¹)ᴴ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Jm_mul_conjTranspose, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

theorem lowers_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ u ∈ flagN ε W, uMat u - 1 ∈ lowers ε W) ∧
      ∀ m ∈ flagM ε W, uMat m ∈ keeps ε W ∧ (uMat m)ᴴ ∈ keeps ε W := by
  intro n ε a j W hW
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · obtain ⟨N, hN⟩ := (GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW).1
    have hu' : u⁻¹ ∈ flagN ε W := by
      rw [← hN] at hu ⊢
      exact N.inv_mem hu
    simp only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into, Matrix.sub_mulVec, Matrix.one_mulVec]
    refine ⟨⟨hu.1, hu.2⟩, fun i y hy x hx => ?_⟩
    have h := hy _ (hu'.1 i x hx)
    rw [star_sub, sub_dotProduct] at h
    rw [Matrix.mulVec_sub, dotProduct_sub, form_mul]
    exact h
  · have hm' : m⁻¹ ∈ flagM ε W := (GlobalTheory.FlagLeviGroup.leviSub (ε := ε) W).inv_mem hm
    simp only [GlobalTheory.IwConst.keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]
    refine ⟨⟨fun i y hy => (hm i y hy).1, fun i y hy x hx => ?_⟩,
      ⟨fun i y hy => (hm i y hy).2, fun i y hy x hx => ?_⟩⟩
    · rw [form_mul]
      exact hy _ (hm' i x hx).1
    · rw [form_conjTranspose]
      exact hy _ (hm' i x hx).2

end GlobalTheory.IwConst.FlagMem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagRadicalLowersLeviKeepsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∀ u ∈ flagN ε W, uMat u - 1 ∈ lowers ε W) ∧ ∀ m ∈ flagM ε W, uMat m ∈ keeps ε W ∧ (uMat m)ᴴ ∈ keeps ε W := by
  first | exact @GlobalTheory.IwConst.FlagMem.lowers_keeps | exact GlobalTheory.IwConst.FlagMem.lowers_keeps | (intros; apply GlobalTheory.IwConst.FlagMem.lowers_keeps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraOfIsCutOutByRealMatrixAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraOfIsCutOutByRealMatrixAlgebra
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwTangent

variable {n : ℕ}

open scoped Matrix.Norms.Frobenius

theorem coe_smul_eq (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : (t : ℂ) • X = t • X := by
  ext i j; simp

theorem exp_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ A) :
    NormedSpace.exp X - 1 ∈ A := by
  have hp : ∀ k : ℕ, X ^ (k + 1) ∈ A := by
    intro k
    induction k with
    | zero => simpa using hX
    | succ k ih => rw [pow_succ]; exact hA _ ih _ hX
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hs' := (hasSum_nat_add_iff' 1).2 hs
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul] at hs'
  have hc : IsClosed (A : Set (Matrix (Fin n) (Fin n) ℂ)) := A.closed_of_finiteDimensional
  exact hc.mem_of_tendsto hs'.tendsto_sum_nat (Filter.Eventually.of_forall fun m =>
    A.sum_mem fun k _ => A.smul_mem _ (hp k))

theorem mem_of_exp_sub_one_mem (T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) - 1 ∈ T) : X ∈ T := by
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const X 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
  have hc : IsClosed (T : Set (Matrix (Fin n) (Fin n) ℂ)) := T.closed_of_finiteDimensional
  refine hc.mem_of_tendsto hd.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
  simp only [zero_add, zero_smul, NormedSpace.exp_zero]
  exact T.smul_mem _ (h t)

theorem exists_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (t : ℝ) :
    ∃ g : Formalism.REAL.UJ ε, uMat g = NormedSpace.exp (t • X) :=
  ⟨GlobalTheory.GaugeConst.expJ ε ⟨t • X, (GlobalTheory.GaugeConst.lieJ ε).smul_mem t hX⟩, rfl⟩

theorem lie_algebra_of_isCut : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → (∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ, ∃ g ∈ S, uMat g = NormedSpace.exp ((t : ℂ) • X)) ∧ (∀ T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ S, uMat g - 1 ∈ T) → ∀ i, E i ∈ T) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inG ε X → (∀ (t : ℝ) (g : Formalism.REAL.UJ ε), uMat g = NormedSpace.exp ((t : ℂ) • X) → g ∈ S) → X ∈ Submodule.span ℝ (Set.range E) := by
  rintro n ε S d E ⟨A, hA, -, hE, rfl⟩
  simp only [coe_smul_eq]
  have h1 : ∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ,
      ∃ g ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ A}, uMat g = NormedSpace.exp (t • X) := by
    intro X hX t
    obtain ⟨hXA, hXG⟩ := (hE X).2 hX
    obtain ⟨g, hg⟩ := exists_exp hXG t
    refine ⟨g, ?_, hg⟩
    change uMat g - 1 ∈ A
    rw [hg]
    exact exp_sub_one_mem A hA (A.smul_mem t hXA)
  refine ⟨h1, fun T hT i => mem_of_exp_sub_one_mem T _ fun t => ?_, fun X hX h => (hE X).1 ⟨?_, hX⟩⟩
  · obtain ⟨g, hg, hg'⟩ := h1 (E i) (Submodule.subset_span ⟨i, rfl⟩) t
    rw [← hg']
    exact hT g hg
  · refine mem_of_exp_sub_one_mem A _ fun t => ?_
    obtain ⟨g, hg⟩ := exists_exp hX t
    rw [← hg]
    exact h t g hg

end GlobalTheory.IwTangent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraOfIsCutOutByRealMatrixAlgebraStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → (∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ, ∃ g ∈ S, uMat g = NormedSpace.exp ((t : ℂ) • X)) ∧ (∀ T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ S, uMat g - 1 ∈ T) → ∀ i, E i ∈ T) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inG ε X → (∀ (t : ℝ) (g : Formalism.REAL.UJ ε), uMat g = NormedSpace.exp ((t : ℂ) • X) → g ∈ S) → X ∈ Submodule.span ℝ (Set.range E) := by
  first | exact @GlobalTheory.IwTangent.lie_algebra_of_isCut | exact GlobalTheory.IwTangent.lie_algebra_of_isCut | (intros; apply GlobalTheory.IwTangent.lie_algebra_of_isCut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceLoweringMulKeepingIsotropicFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceLoweringMulKeepingIsotropicFlag
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.FlagTrace

variable {n a : ℕ} {ε : Fin n → Bool} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}

theorem mem_lowers {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ lowers ε W ↔
    ((∀ i : Fin a, ∀ y ∈ W i.succ, X *ᵥ y ∈ W i.castSucc) ∧
      ∀ y ∈ perp ε (W (Fin.last a)), X *ᵥ y ∈ W (Fin.last a)) ∧
      ∀ i : Fin a, ∀ y ∈ perp ε (W i.castSucc), X *ᵥ y ∈ perp ε (W i.succ) := by
  simp only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into]

theorem mem_keeps {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ keeps ε W ↔
    (∀ i, ∀ y ∈ W i, X *ᵥ y ∈ W i) ∧ ∀ i, ∀ y ∈ perp ε (W i), X *ᵥ y ∈ perp ε (W i) := by
  simp only [keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]

theorem perp_anti {V V' : Submodule ℂ (Fin n → ℂ)} (h : V ≤ V') : perp ε V' ≤ perp ε V :=
  fun _ hy x hx => hy x (h hx)

theorem mul_mem_lowers {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lowers ε W) (hY : Y ∈ keeps ε W) :
    X * Y ∈ lowers ε W := by
  rw [mem_lowers] at hX ⊢
  rw [mem_keeps] at hY
  simp only [← Matrix.mulVec_mulVec]
  exact ⟨⟨fun i y hy => hX.1.1 i _ (hY.1 _ y hy), fun y hy => hX.1.2 _ (hY.2 _ y hy)⟩,
    fun i y hy => hX.2 i _ (hY.2 _ y hy)⟩

theorem isNilpotent_of_mem_lowers (h0 : W 0 = ⊥) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lowers ε W) :
    IsNilpotent X := by
  rw [mem_lowers] at hX
  have h1 : ∀ i : Fin (a + 1), ∀ y, X ^ (i : ℕ) *ᵥ y ∈ perp ε (W i) := by
    intro i
    induction i using Fin.induction with
    | zero => intro y x hx; rw [h0, Submodule.mem_bot] at hx; simp [hx]
    | succ i ih =>
      intro y
      rw [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec]
      exact hX.2 i _ (ih y)
  have h2 : ∀ i : Fin (a + 1), ∀ y ∈ W i, X ^ (i : ℕ) *ᵥ y = 0 := by
    intro i
    induction i using Fin.induction with
    | zero => intro y hy; rw [h0, Submodule.mem_bot] at hy; simp [hy]
    | succ i ih =>
      intro y hy
      rw [Fin.val_succ, pow_succ, ← Matrix.mulVec_mulVec]
      exact ih _ (hX.1.1 i y hy)
  refine ⟨a + 1 + a, ?_⟩
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, pow_add, pow_succ, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  exact h2 (Fin.last a) _ (hX.1.2 _ (h1 (Fin.last a) y))

theorem lowers_le_keeps {j : Fin a → ℕ} (h : IsIsoFlag ε j W) : lowers ε W ≤ keeps ε W := by
  obtain ⟨h0, hm, -, hi⟩ := h
  intro X hX
  rw [mem_lowers] at hX
  rw [mem_keeps]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · induction i using Fin.cases with
    | zero => intro y hy; rw [h0, Submodule.mem_bot] at hy; simp [hy]
    | succ i => exact fun y hy => hm (Fin.castSucc_le_succ i) (hX.1.1 i y hy)
  · induction i using Fin.lastCases with
    | last => exact fun y hy x hx => hi x hx _ (hX.1.2 y hy)
    | cast i => exact fun y hy => perp_anti (hm (Fin.castSucc_le_succ i)) (hX.2 i y hy)

theorem trace_lowers_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ X ∈ lowers ε W, ∀ Y ∈ keeps ε W, (X * Y).trace = 0) ∧ lowers ε W ≤ keeps ε W ∧
      (1 : Matrix (Fin n) (Fin n) ℂ) ∈ keeps ε W ∧ ∀ X ∈ keeps ε W, ∀ Y ∈ keeps ε W, X * Y ∈ keeps ε W := by
  intro n ε a j W h
  refine ⟨fun X hX Y hY => ?_, lowers_le_keeps h, ?_, fun X hX Y hY => ?_⟩
  · exact (Matrix.isNilpotent_trace_of_isNilpotent
      (isNilpotent_of_mem_lowers h.1 (mul_mem_lowers hX hY))).eq_zero
  · rw [mem_keeps]; simp
  · rw [mem_keeps] at hX hY ⊢
    simp only [← Matrix.mulVec_mulVec]
    exact ⟨fun i y hy => hX.1 i _ (hY.1 i y hy), fun i y hy => hX.2 i _ (hY.2 i y hy)⟩

end GlobalTheory.IwConst.FlagTrace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceLoweringMulKeepingIsotropicFlagStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∀ X ∈ lowers ε W, ∀ Y ∈ keeps ε W, (X * Y).trace = 0) ∧ lowers ε W ≤ keeps ε W ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ keeps ε W ∧ ∀ X ∈ keeps ε W, ∀ Y ∈ keeps ε W, X * Y ∈ keeps ε W := by
  first | exact @GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps | exact GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps | (intros; apply GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalDomainNormalisingConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalDomainNormalisingConstants
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.NormConst

theorem two_v_pos (D : D7) : 0 < 2 * D.host.v := by
  show 0 < 2 * (D.host.rdE / 2)
  unfold Formalism.BasicNotions.Host.rdE
  have h0 : (0:ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have := Real.rpow_pos_of_pos h0 (1 / (Module.finrank ℚ D.host.E : ℝ))
  linarith

theorem abs_discr_F (D : D7) : |(NumberField.discr D.host.F : ℝ)| = (2 * D.host.v) ^ D.R.f := by
  have h2v : 2 * D.host.v = D.host.rdE := by show 2 * (D.host.rdE / 2) = D.host.rdE; ring
  rw [h2v]
  obtain ⟨h1, -⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hn := GlobalTheory.RealPlaces.finrank_E D
  have hpos : Module.finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  have key : D.host.rdE ^ (2 * D.R.f) = |(NumberField.discr D.host.F : ℝ)| ^ 2 := by
    rw [← hn]
    unfold Formalism.BasicNotions.Host.rdE
    rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
    have h3 : |(NumberField.discr D.host.E : ℝ)| = (NumberField.discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
    rw [h3, sq_abs]
  have hr0 : 0 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.rdE; positivity
  rw [mul_comm, pow_mul] at key
  exact ((pow_left_inj₀ (pow_nonneg hr0 _) (abs_nonneg _) two_ne_zero).1 key).symm

theorem card_infinitePlace_E (D : D7) : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))).symm

theorem sum_range_closed (k : ℕ) : ∀ n : ℕ,
    (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (4 * ((i : ℝ) + 1) + 2 * k)) =
      2 * (n : ℝ) * (n + 1) * (2 * n + 1) / 3 + k * n * (n + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_closed k n]
    push_cast; ring

theorem sum_exponents (r k : ℕ) :
    (∑ a : Fin r, (((r - (a : ℕ)) * (4 * (r - (a : ℕ)) + 2 * k) : ℕ) : ℝ)) =
      2 * (r : ℝ) * (r + 1) * (2 * r + 1) / 3 + k * r * (r + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (((r - i) * (4 * (r - i) + 2 * k) : ℕ) : ℝ)) r,
    ← Finset.sum_range_reflect, ← sum_range_closed k r]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have e : r - (r - 1 - j) = j + 1 := by omega
  rw [e]; push_cast; ring

end GlobalTheory.CovDom.NormConst

namespace GlobalTheory.CovDom

theorem normalising_constants : ∀ (D : D7), (∀ a, 0 < sc D a) ∧ |(NumberField.discr D.host.F : ℝ)| ^ (-(((D.R.k : ℝ) + 1) * (D.R.rS : ℝ) ^ 2) - 4 * ((D.R.rS : ℝ) ^ 3 - D.R.rS) / 3 - 3 * (D.R.rS : ℝ) / 2) * (∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) ^ Fintype.card (InfinitePlace D.host.E) = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  intro D
  have hv := NormConst.two_v_pos D
  refine ⟨fun a => pow_pos hv _, ?_⟩
  rw [NormConst.card_infinitePlace_E, D.what₂.card_Tau, NormConst.abs_discr_F]
  have hprod : ∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k) =
      (2 * D.host.v) ^ (∑ a : Fin D.R.rS, (D.R.rS - (a : ℕ)) * (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) := by
    unfold sc
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← pow_mul]
  rw [hprod, ← pow_mul, ← Real.rpow_natCast (2 * D.host.v) D.R.f,
    ← Real.rpow_mul hv.le, ← Real.rpow_natCast (2 * D.host.v) (_ * D.R.f), ← Real.rpow_add hv]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sum, NormConst.sum_exponents]
  ring

end GlobalTheory.CovDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalDomainNormalisingConstantsStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_normalising_constants : ∀ (D : D7), (∀ a, 0 < sc D a) ∧ |(NumberField.discr D.host.F : ℝ)| ^ (-(((D.R.k : ℝ) + 1) * (D.R.rS : ℝ) ^ 2) - 4 * ((D.R.rS : ℝ) ^ 3 - D.R.rS) / 3 - 3 * (D.R.rS : ℝ) / 2) * (∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) ^ Fintype.card (InfinitePlace D.host.E) = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  first | exact @GlobalTheory.CovDom.normalising_constants | exact GlobalTheory.CovDom.normalising_constants | (intros; apply GlobalTheory.CovDom.normalising_constants <;> assumption)
end
end
