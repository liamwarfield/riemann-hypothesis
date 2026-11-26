module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarHaar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem cPQ_pos (ε : Fin n → Bool) : 0 < cPQ ε := by
  unfold cPQ
  positivity

theorem real_UJ_eq_UJ (ε : Fin n → Bool) : Formalism.REAL.UJ ε = UJ ε := by
  rfl

theorem comap_muPolarMat_isHaar (ε : Fin n → Bool) :
    ∀ (H : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ), H = UJ ε → ∀ (m : MeasurableSpace H), @BorelSpace H _ m →
      (Measure.comap (β := Fin n → Fin n → ℂ)
        (fun g : H => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
        (muPolarMat ε)).IsHaarMeasure := by
  intro H hH
  subst hH
  have key := muPolar_isHaar ε
  have h0 : (inferInstance : MeasurableSpace (UJ ε)) = borel (UJ ε) := BorelSpace.measurable_eq
  intro m hm
  have h1 : m = borel (UJ ε) := hm.measurable_eq
  have e : m = _ := h1.trans h0.symm
  subst e
  exact key

theorem muCD_isHaar (ε : Fin n → Bool) : (muCD ε).IsHaarMeasure := by

  haveI hH := comap_muPolarMat_isHaar ε (Formalism.REAL.UJ ε) (real_UJ_eq_UJ ε) inferInstance inferInstance
  unfold muCD
  have hc : ENNReal.ofReal (cPQ ε) ≠ 0 := (ENNReal.ofReal_pos.mpr (cPQ_pos ε)).ne'
  have ht : ENNReal.ofReal (cPQ ε) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact MeasureTheory.Measure.IsHaarMeasure.smul _ hc ht

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumNormAdjointSqEqHsOp
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

open CompactHaarProbability in
theorem fF_conj_pmat_eq_op_inv_mul_fF_mul_op {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : KType ε (lowK ε lam)) (k : KG ε) (z : PCoord ε → ℂ) :
    fF ε lam T (toMK k⁻¹ * pmat z * toMK k) = T.op k⁻¹ * fF ε lam T (pmat z) * T.op k := by
  rw [fF_eq_integral, fF_eq_integral]
  have h1 : ∀ (c : ℂ) (I : T.V →L[ℂ] T.V), T.op k⁻¹ * (c • I) * T.op k = c • conjE T k⁻¹ I := by
    intro c I
    rw [conjE_apply, inv_inv, mul_smul_comm, smul_mul_assoc]
  rw [h1, ← ContinuousLinearEquiv.integral_comp_comm]
  congr 1
  conv_rhs => rw [← integral_mul_left_eq_self _ k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hm : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun _ _ => rfl
  have he : toMK (k * x)⁻¹ * pmat z * toMK (k * x) = toMK x⁻¹ * (toMK k⁻¹ * pmat z * toMK k) * toMK x := by
    rw [_root_.mul_inv_rev, hm, hm]
    simp only [Matrix.mul_assoc]
  have hop : T.op k⁻¹ * (T.op (k * x) * projW T * T.op (k * x)⁻¹) * T.op k = T.op x * projW T * T.op x⁻¹ := by
    rw [_root_.mul_inv_rev, op_mul, op_mul]
    simp only [mul_assoc]
    rw [op_inv_mul, mul_one, ← mul_assoc (T.op k⁻¹), op_inv_mul, one_mul]
  beta_reduce
  rw [conjE_apply, inv_inv, mul_smul_comm, smul_mul_assoc, he, hop]

theorem sum_norm_adjoint_sq_eq_hsOp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [CompleteSpace V] (A : V →L[ℂ] V) :
    ∑ i, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V i)‖ ^ 2 = hsOp A := by
  unfold hsOp
  set b := stdOrthonormalBasis ℂ V
  have h1 : ∀ i, ‖(ContinuousLinearMap.adjoint A) (b i)‖ ^ 2 = ∑ j, ‖⟪b i, A (b j)⟫_ℂ‖ ^ 2 := by
    intro i
    rw [← b.sum_sq_norm_inner_right]
    refine sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  have h2 : ∀ j, ‖A (b j)‖ ^ 2 = ∑ i, ‖⟪b i, A (b j)⟫_ℂ‖ ^ 2 := fun j => (b.sum_sq_norm_inner_right _).symm
  simp_rw [h1, h2]
  exact sum_comm

theorem hsOp_ge_integral {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (A : T.V →L[ℂ] T.V) :
    (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ∂(dk ε) ≤ hsOp A := by
  set b := stdOrthonormalBasis ℂ T.V
  set B := ContinuousLinearMap.adjoint A
  have hc : Continuous fun k : KG ε => T.op k T.w := (KType_continuous_op T).clm_apply continuous_const
  have hpt : ∀ k : KG ε, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ≤ ∑ i, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 := by
    intro k
    have hn : ‖T.op k T.w‖ = 1 := by rw [KType_norm_op_apply, T.w_norm]
    have e : ∑ i, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 = ‖A (T.op k T.w)‖ ^ 2 := by
      rw [← b.sum_sq_norm_inner_right]
      refine sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.adjoint_inner_left]
    rw [e]
    have := norm_inner_le_norm (𝕜 := ℂ) (T.op k T.w) (A (T.op k T.w))
    rw [hn, one_mul] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hI1 : Integrable (fun k : KG ε => ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2) (dk ε) :=
    integrable_dk_of_continuous ((continuous_inner.comp (hc.prodMk (A.continuous.comp hc))).norm.pow 2)
  have hI2 : ∀ i, Integrable (fun k : KG ε => ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2) (dk ε) := fun i =>
    integrable_dk_of_continuous ((continuous_const.inner hc).norm.pow 2)
  have hmono := integral_mono hI1 (integrable_finsetSum _ fun i _ => hI2 i) hpt
  rw [integral_finsetSum _ fun i _ => hI2 i] at hmono
  have hd : (0 : ℝ) ≤ Module.finrank ℂ T.V := Nat.cast_nonneg _
  calc (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ∂(dk ε)
      ≤ (Module.finrank ℂ T.V : ℝ) * ∑ i, ∫ k, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 ∂(dk ε) :=
        mul_le_mul_of_nonneg_left hmono hd
    _ = ∑ i, ‖B (b i)‖ ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [kschur_coef, T.w_norm, one_pow, one_mul]
    _ = hsOp A := sum_norm_adjoint_sq_eq_hsOp A

open CompactHaarProbability in
theorem continuous_fF (ε : Fin n → Bool) (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Continuous fun z : PCoord ε → ℂ => fF ε lam T (pmat z) := by
  letI : IsProbabilityMeasure (dk ε) := ⟨by
    change (muK ε Set.univ)⁻¹ * muK ε Set.univ = 1
    exact ENNReal.inv_mul_cancel
      (ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).1.ne'
      (ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).2.ne⟩
  letI : IsFiniteMeasureOnCompacts (dk ε) := ⟨fun K hK =>
    (measure_mono (Set.subset_univ K)).trans_lt (measure_lt_top (dk ε) Set.univ)⟩
  have hf : Continuous (fun p : (PCoord ε → ℂ) × KG ε =>
      ((Real.exp (-Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) : ℝ) : ℂ) • (T.op p.2 * projW T * T.op p.2⁻¹)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_potential_conj_prod lam).neg)).smul
      ((cont_conj T _).comp continuous_snd)
  have h2 := continuous_parametric_integral_of_continuous (μ := dk ε)
    (f := fun z k => ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹))
    hf isCompact_univ
  simp only [Measure.restrict_univ] at h2
  have he : (fun z : PCoord ε → ℂ => fF ε lam T (pmat z)) = fun z => ((Module.finrank ℂ T.V : ℝ) : ℂ) •
      ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(dk ε) :=
    funext fun z => fF_eq_integral lam T _
  rw [he]
  exact (continuous_const : Continuous fun _ : PCoord ε → ℂ => ((Module.finrank ℂ T.V : ℝ) : ℂ)).smul h2

theorem inner_fF_conj {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : KType ε (lowK ε lam)) (k : KG ε)
    (z : PCoord ε → ℂ) :
    ⟪T.w, fF ε lam T (pmat (adK k⁻¹ z)) T.w⟫_ℂ = ⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ := by
  rw [← conj_pmat_eq_adK, fF_conj_pmat_eq_op_inv_mul_fF_mul_op, KType_op_inv_eq_adjoint, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem formal_degree_inequality {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal (cPQ ε) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 * Jac z) ≤
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) / d) := by
  letI : IsProbabilityMeasure (dk ε) := ⟨by
    change (muK ε Set.univ)⁻¹ * muK ε Set.univ = 1
    exact ENNReal.inv_mul_cancel
      (ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).1.ne'
      (ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).2.ne⟩
  letI : IsFiniteMeasureOnCompacts (dk ε) := ⟨fun K hK =>
    (measure_mono (Set.subset_univ K)).trans_lt (measure_lt_top (dk ε) Set.univ)⟩
  letI : SFinite (dk ε) := by infer_instance
  have hpos : 0 < (Module.finrank ℂ T.V : ℝ) := by
    have : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by
      have := T.w_norm; rw [h, norm_zero] at this; exact zero_ne_one this⟩⟩
    exact_mod_cast Module.finrank_pos
  have l6 := lemma6a hF hd
  set D : ℝ := (Module.finrank ℂ T.V : ℝ) with hD
  set G : (PCoord ε → ℂ) → ℝ := fun z => ‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 with hG
  set h : KG ε → (PCoord ε → ℂ) → ℝ :=
    fun k z => ‖⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ‖ ^ 2 * Jac z with hh
  have hFc := continuous_fF ε lam T
  have hJc := pb_jac_continuous ε
  have hGc : Continuous G := (continuous_const.inner (hFc.clm_apply continuous_const)).norm.pow 2
  have hc : Continuous fun k : KG ε => T.op k T.w := (KType_continuous_op T).clm_apply continuous_const
  have hhc : Continuous (Function.uncurry h) := by
    have a : Continuous fun p : KG ε × (PCoord ε → ℂ) => T.op p.1 T.w := hc.comp continuous_fst
    exact ((a.inner ((hFc.comp continuous_snd).clm_apply a)).norm.pow 2).mul (hJc.comp continuous_snd)
  have s1 : ∀ k : KG ε, ∫⁻ z, ENNReal.ofReal (h k z) = ∫⁻ z, ENNReal.ofReal (G z * Jac z) := by
    intro k
    have hm : Measurable fun z => ENNReal.ofReal (G z * Jac z) :=
      ENNReal.measurable_ofReal.comp (hGc.mul hJc).measurable
    rw [← (adK_measurePreserving k⁻¹).lintegral_comp hm]
    refine lintegral_congr fun z => ?_
    simp only [h, G, inner_fF_conj, jac_adK]
  have s2 : ∫⁻ z, ENNReal.ofReal (G z * Jac z) = ∫⁻ z, ∫⁻ k, ENNReal.ofReal (h k z) ∂(dk ε) := by
    have e : ∫⁻ z, ENNReal.ofReal (G z * Jac z) = ∫⁻ k, (∫⁻ z, ENNReal.ofReal (h k z)) ∂(dk ε) := by
      simp only [s1, lintegral_const]
      rw [measure_univ, mul_one]
    rw [e, lintegral_lintegral_swap (f := fun k z => ENNReal.ofReal (h k z)) (μ := dk ε) (ν := volume)
      (ENNReal.measurable_ofReal.comp hhc.measurable).aemeasurable]
  have s3 : ∀ z, ENNReal.ofReal D * ∫⁻ k, ENNReal.ofReal (h k z) ∂(dk ε) ≤
      ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
    intro z
    have hi : Integrable (fun k => ‖⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ‖ ^ 2) (dk ε) :=
      integrable_dk_of_continuous ((continuous_inner.comp (hc.prodMk ((fF ε lam T (pmat z)).continuous.comp hc))).norm.pow 2)
    rw [← ofReal_integral_eq_lintegral_ofReal (hi.mul_const _)
      (Filter.Eventually.of_forall fun k => mul_nonneg (by positivity) (jacobian_nonneg z)),
      integral_mul_const, ← ENNReal.ofReal_mul hpos.le, ← mul_assoc]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hsOp_ge_integral T _) (jacobian_nonneg z))
  have s4 : ENNReal.ofReal D * ∫⁻ z, ENNReal.ofReal (G z * Jac z) ≤
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
    rw [s2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono s3
  have s5 : ENNReal.ofReal D * (ENNReal.ofReal (cPQ ε) * ∫⁻ z, ENNReal.ofReal (G z * Jac z)) ≤
      ENNReal.ofReal D * ENNReal.ofReal (D / d) := by
    rw [← ENNReal.ofReal_mul hpos.le, show D * (D / d) = D ^ 2 / d by ring, l6, mul_left_comm]
    exact mul_le_mul_right s4 _
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top).1 s5

theorem lintegral_fF_coeff_sq_le_finrank_div_fdeg {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal (cPQ ε) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 * Jac z) ≤
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) / d) :=
  formal_degree_inequality hF hd

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdLowerA
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdl_inner_continuous {ε : Fin n → Bool} (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ) (u v : T.V) :
    Continuous (fun z : PCoord ε → ℂ => ⟪u, fF ε lam T (pmat z) v⟫_ℂ) := by
  have hpm : Continuous (fun z : PCoord ε → ℂ => pmat z) := by
    first
    | exact (JacB.pmatLin ε).continuous_of_finiteDimensional
    | exact (dpbE ε).continuous_of_finiteDimensional
    | (refine continuous_pi fun a => continuous_pi fun b => ?_
       unfold pmat
       split_ifs <;> fun_prop)
  have hmk : Continuous fun k : KG ε => toMK k := by
    first
    | fun_prop
    | (unfold toMK; fun_prop)
    | exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    | (unfold toMK toM; fun_prop)
  have hM : Continuous fun p : (PCoord ε → ℂ) × KG ε => toMK p.2⁻¹ * pmat p.1 * toMK p.2 :=
    ((hmk.comp continuous_snd.inv).matrix_mul (hpm.comp continuous_fst)).matrix_mul
      (hmk.comp continuous_snd)
  have hPh : Continuous fun p : (PCoord ε → ℂ) × KG ε => Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2) :=
    continuous_potential_comp lam hM (fun p => ⟨adK p.2⁻¹ p.1, conj_pmat_eq_adK p.2 p.1⟩)
  have hop : Continuous fun p : (PCoord ε → ℂ) × KG ε => T.op p.2 :=
    (continuous_subtype_val.comp T.cont).comp continuous_snd
  have hF : Continuous fun p : (PCoord ε → ℂ) × KG ε =>
      ((Real.exp (-Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) : ℝ) : ℂ) *
        (⟪T.op p.2 T.w, v⟫_ℂ * ⟪u, T.op p.2 T.w⟫_ℂ) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hPh.neg)).mul
      (((hop.clm_apply continuous_const).inner continuous_const).mul
        (continuous_const.inner (hop.clm_apply continuous_const)))
  have := CompactHaarProbability.dk_isProb ε
  have hI := continuous_parametric_integral_of_continuous (μ := dk ε)
    (f := fun (z : PCoord ε → ℂ) (k : KG ε) =>
      ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
        (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ)) hF isCompact_univ
  simp only [Measure.restrict_univ] at hI
  have he : (fun z : PCoord ε → ℂ => ⟪u, fF ε lam T (pmat z) v⟫_ℂ) = fun z =>
      ((Module.finrank ℂ T.V : ℝ) : ℂ) *
        ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
          (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ) ∂(dk ε) := by
    funext z
    exact inner_fF_eq_integral lam T z u v
  rw [he]
  exact continuous_const.mul hI

theorem fdl_lint_pi_ofReal {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (h0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi μ) = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf)
      (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => h0 i (x i)))),
    integral_fintype_prod_eq_prod]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))

theorem fdl_cgauss {c : ℝ} (hc : 0 < c) : ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2)) = Real.pi / c := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hc
  simp only [neg_mul, Complex.finrank_real_complex] at h
  rw [h]
  norm_num

theorem fdl_cgauss_int {c : ℝ} (hc : 0 < c) : Integrable (fun z : ℂ => Real.exp (-(c * ‖z‖ ^ 2))) := by
  apply Integrable.of_integral_ne_zero
  rw [fdl_cgauss hc]
  exact (div_pos Real.pi_pos hc).ne'

theorem fdl_wab_zero_pos {ε : Fin n → Bool} (ab : PCoord ε) : 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by
  obtain ⟨⟨a, b⟩, hab⟩ := ab
  have h : (b : ℕ) < (a : ℕ) := hab.1
  have h' : ((b : ℕ) : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast h
  show 0 < (0 : Fin n → ℝ) b - (0 : Fin n → ℝ) a + ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)
  simp only [Pi.zero_apply, sub_zero, zero_add]
  linarith

theorem fdl_gauss (ε : Fin n → Bool) :
    ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) = ENNReal.ofReal (PiW ε 0) := by
  have hw : ∀ ab : PCoord ε, 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := fdl_wab_zero_pos
  have h1 : ∀ y : PCoord ε → ℂ, Real.exp (-Qf (0 : Fin n → ℝ) y) =
      ∏ ab, Real.exp (-(wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖y ab‖ ^ 2)) := by
    intro y
    rw [Qf, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [h1]
  rw [MeasureTheory.volume_pi]
  rw [fdl_lint_pi_ofReal (E := fun _ : PCoord ε => ℂ) (μ := fun _ => volume)
    (fun (ab : PCoord ε) (x : ℂ) => Real.exp (-(wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖x‖ ^ 2)))
    (fun ab => fdl_cgauss_int (hw ab)) (fun _ _ => (Real.exp_pos _).le)]
  rw [PiW, ENNReal.ofReal_prod_of_nonneg (fun ab _ => (div_pos Real.pi_pos (hw ab)).le)]
  exact Finset.prod_congr rfl fun ab _ => by rw [fdl_cgauss (hw ab)]

end ReciprocityTheory.ChartRestriction.DS
end
end
