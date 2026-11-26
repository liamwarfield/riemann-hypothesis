module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

namespace CompactHaarProbability

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma muK_univ_ne_zero (ε : Fin n → Bool) : muK ε Set.univ ≠ 0 := ((ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).1).ne'

lemma muK_univ_ne_top (ε : Fin n → Bool) : muK ε Set.univ ≠ ⊤ := ((ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).2).ne

instance dk_isProb (ε : Fin n → Bool) : IsProbabilityMeasure (dk ε) := by
  rw [dk_def]
  letI : IsFiniteMeasure (muK ε) := ⟨(muK_univ_ne_top ε).lt_top⟩
  letI : NeZero (muK ε) := ⟨Measure.measure_univ_ne_zero.mp (muK_univ_ne_zero ε)⟩
  exact isProbabilityMeasureSMul (μ := muK ε)

instance dk_left (ε : Fin n → Bool) : (dk ε).IsMulLeftInvariant := by
  rw [dk_def]
  letI := kf_isHaar ε
  exact MeasureTheory.isMulLeftInvariant_smul (μ := muK ε) (muK ε Set.univ)⁻¹

instance dk_right (ε : Fin n → Bool) : (dk ε).IsMulRightInvariant := by
  rw [dk_def]
  letI := muK_rightInvariant ε
  exact MeasureTheory.isMulRightInvariant_smul (μ := muK ε) (muK ε Set.univ)⁻¹

lemma muK_inv (ε : Fin n → Bool) : Measure.map (fun x : KG ε => x⁻¹) (muK ε) = muK ε := by
  haveI := muK_rightInvariant ε
  set ν := Measure.map (fun x : KG ε => x⁻¹) (muK ε) with hν
  haveI : ν.IsMulLeftInvariant := by
    change (muK ε).inv.IsMulLeftInvariant
    infer_instance
  haveI : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have e := Measure.isMulInvariant_eq_smul_of_compactSpace ν (muK ε)
  have huniv : ν Set.univ = muK ε Set.univ := by
    rw [hν, Measure.map_apply measurable_inv MeasurableSet.univ, Set.preimage_univ]
  rw [e] at huniv
  rw [smul_apply, ENNReal.smul_def, smul_eq_mul] at huniv
  have hc : (ν.haarScalarFactor (muK ε) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_eq_right (muK_univ_ne_zero ε) (muK_univ_ne_top ε)).mp huniv
  rw [e, ENNReal.coe_eq_one.mp hc, one_smul]

lemma dk_inv (ε : Fin n → Bool) : Measure.map (fun x : KG ε => x⁻¹) (dk ε) = dk ε := by
  rw [dk_def, Measure.map_smul _ measurable_inv.aemeasurable, muK_inv]

end CompactHaarProbability


open CompactHaarProbability in
theorem dk_props (ε : Fin n → Bool) :
    IsProbabilityMeasure (dk ε) ∧ (∀ k : KG ε, Measure.map (fun x => k * x) (dk ε) = dk ε) ∧
      (∀ k : KG ε, Measure.map (fun x => x * k) (dk ε) = dk ε) ∧
      Measure.map (fun x : KG ε => x⁻¹) (dk ε) = dk ε := by
  refine ⟨inferInstance, fun k => map_mul_left_eq_self (dk ε) k, fun k => map_mul_right_eq_self (dk ε) k,
    dk_inv ε⟩

namespace CompactHaarProbability

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma op_mul (T : KType ε Λ) (a b : KG ε) : T.op (a * b) = T.op a * T.op b := by
  show ((T.τ (a * b) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
  rw [map_mul]
  rfl

lemma op_one (T : KType ε Λ) : T.op 1 = 1 := by
  show ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
  rw [map_one]
  rfl

lemma op_mul_inv (T : KType ε Λ) (a : KG ε) : T.op a * T.op a⁻¹ = 1 := by
  rw [← op_mul, mul_inv_cancel, op_one]

lemma op_inv_mul (T : KType ε Λ) (a : KG ε) : T.op a⁻¹ * T.op a = 1 := by
  rw [← op_mul, inv_mul_cancel, op_one]

def opE (T : KType ε Λ) (k : KG ε) : T.V ≃L[ℂ] T.V :=
  ContinuousLinearEquiv.equivOfInverse (T.op k) (T.op k⁻¹)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (op_inv_mul T k)
      simpa using this)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (op_mul_inv T k)
      simpa using this)

def conjE (T : KType ε Λ) (k : KG ε) : (T.V →L[ℂ] T.V) ≃L[ℂ] (T.V →L[ℂ] T.V) :=
  (opE T k).arrowCongr (opE T k)

lemma conjE_apply (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    conjE T k A = T.op k * A * T.op k⁻¹ := by
  exact ContinuousLinearMap.ext fun v => rfl

lemma schur (T : KType ε Λ) (A : T.V →L[ℂ] T.V) (hA : ∀ k, T.op k * A = A * T.op k) :
    ∃ c : ℂ, A = c • (1 : T.V →L[ℂ] T.V) := by
  by_cases hV : Nontrivial T.V
  · obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (A : T.V →ₗ[ℂ] T.V)
    have hinv : ∀ k : KG ε, ∀ v ∈ Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c,
        ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈
          Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c := by
      intro k v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have e := congrArg (fun B : T.V →L[ℂ] T.V => B v) (hA k)
      simp only [ContinuousLinearMap.mul_apply] at e
      change A (T.op k v) = c • T.op k v
      rw [← e]
      change T.op k ((A : T.V →ₗ[ℂ] T.V) v) = _
      rw [hv, map_smul]
    rcases T.irred _ hinv with h | h
    · obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      exact absurd ((Submodule.mem_bot ℂ).mp (h ▸ hv.1)) hv.2
    · refine ⟨c, ContinuousLinearMap.ext fun v => ?_⟩
      have hv : v ∈ Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c := h ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hv
      simpa using hv
  · haveI : Subsingleton T.V := not_nontrivial_iff_subsingleton.mp hV
    exact ⟨0, ContinuousLinearMap.ext fun v => Subsingleton.elim _ _⟩

lemma cont_op (T : KType ε Λ) : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont

lemma cont_conj (T : KType ε Λ) (P : T.V →L[ℂ] T.V) :
    Continuous fun k : KG ε => T.op k * P * T.op k⁻¹ := ((cont_op T).mul continuous_const).mul ((cont_op T).comp continuous_inv)

lemma integrable_conj (T : KType ε Λ) (P : T.V →L[ℂ] T.V) :
    Integrable (fun k : KG ε => T.op k * P * T.op k⁻¹) (dk ε) := by
  have h := (cont_conj T P).continuousOn.integrableOn_compact (μ := dk ε) isCompact_univ
  rwa [integrableOn_univ] at h

lemma int_conj (T : KType ε Λ) (P : T.V →L[ℂ] T.V) (k : KG ε) :
    T.op k * (∫ k', T.op k' * P * T.op k'⁻¹ ∂(dk ε)) * T.op k⁻¹ =
      ∫ k', T.op k' * P * T.op k'⁻¹ ∂(dk ε) := by
  rw [← conjE_apply, ← ContinuousLinearEquiv.integral_comp_comm]
  simp_rw [conjE_apply]
  have e : ∀ k' : KG ε, T.op k * (T.op k' * P * T.op k'⁻¹) * T.op k⁻¹ =
      T.op (k * k') * P * T.op (k * k')⁻¹ := by
    intro k'
    rw [op_mul, _root_.mul_inv_rev, op_mul]
    simp only [mul_assoc]
  simp_rw [e]
  exact integral_mul_left_eq_self (fun k' => T.op k' * P * T.op k'⁻¹) k

end CompactHaarProbability


open CompactHaarProbability in
theorem kschur_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (v : T.V) :
    ((Module.finrank ℂ T.V : ℝ) : ℂ) •
        ∫ k, T.op k * (innerSL ℂ v).smulRight v * T.op k⁻¹ ∂(dk ε) =
      ((‖v‖ ^ 2 : ℝ) : ℂ) • (1 : T.V →L[ℂ] T.V) := by
  set P : T.V →L[ℂ] T.V := (innerSL ℂ v).smulRight v with hP
  set I := ∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε) with hI
  have hcomm : ∀ k, T.op k * I = I * T.op k := by
    intro k
    have h := int_conj T P k
    calc T.op k * I = T.op k * I * (T.op k⁻¹ * T.op k) := by rw [op_inv_mul, mul_one]
      _ = (T.op k * I * T.op k⁻¹) * T.op k := by simp only [mul_assoc]
      _ = I * T.op k := by rw [h]
  obtain ⟨c, hc⟩ := schur T I hcomm
  let tr : (T.V →L[ℂ] T.V) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ T.V).comp (ContinuousLinearMap.coeLM ℂ)
  let trL : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap tr
  have htr : ∀ A : T.V →L[ℂ] T.V, trL A = LinearMap.trace ℂ T.V (A : T.V →ₗ[ℂ] T.V) := fun A => rfl
  have hconj : ∀ k : KG ε, trL (T.op k * P * T.op k⁻¹) = trL P := by
    intro k
    rw [htr, htr, ContinuousLinearMap.coe_mul, ContinuousLinearMap.coe_mul, mul_assoc,
      LinearMap.trace_mul_comm, mul_assoc, ← ContinuousLinearMap.coe_mul, op_inv_mul]
    simp
  have htrP : trL P = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [htr, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ T.V)]
    simp only [ContinuousLinearMap.coe_coe, hP, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      inner_smul_right]
    rw [OrthonormalBasis.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hItr : trL I = trL P := by
    rw [hI, ← ContinuousLinearMap.integral_comp_comm trL (integrable_conj T P)]
    simp_rw [hconj]
    rw [integral_const]
    simp
  have htr1 : trL (c • (1 : T.V →L[ℂ] T.V)) = c * (Module.finrank ℂ T.V : ℂ) := by
    rw [map_smul, htr]
    simp [LinearMap.trace_one]
  rw [hc, htr1, htrP] at hItr
  have key : ((Module.finrank ℂ T.V : ℝ) : ℂ) * c = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hItr]
    push_cast
    ring
  rw [hc, smul_smul, key]


open CompactHaarProbability in
theorem kschur_coef {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (u v : T.V) :
    (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪u, T.op k v⟫_ℂ‖ ^ 2 ∂(dk ε) = ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
  set P : T.V →L[ℂ] T.V := (innerSL ℂ v).smulRight v with hP
  have hop := kschur_op T v
  rw [← hP] at hop
  have hadj : ∀ k : KG ε, T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
    intro k
    show ((T.τ k⁻¹ : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
    rw [map_inv, ← ContinuousLinearMap.star_eq_adjoint]
    rfl
  have hpt : ∀ k : KG ε, ⟪u, (T.op k * P * T.op k⁻¹) u⟫_ℂ = ((‖⟪u, T.op k v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    simp only [ContinuousLinearMap.mul_apply, hP, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [hadj, ContinuousLinearMap.adjoint_inner_right, map_smul, inner_smul_right, ← inner_conj_symm,
      RCLike.conj_mul]
    push_cast
    rfl
  let E : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := (innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ T.V u)
  have hE : ∀ A : T.V →L[ℂ] T.V, E A = ⟪u, A u⟫_ℂ := fun A => rfl
  have hint : ((∫ k, ‖⟪u, T.op k v⟫_ℂ‖ ^ 2 ∂(dk ε) : ℝ) : ℂ) =
      ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ := by
    rw [← integral_complex_ofReal, ← hE, ← ContinuousLinearMap.integral_comp_comm E (integrable_conj T P)]
    simp_rw [hE, hpt]
  have hfin : ((Module.finrank ℂ T.V : ℝ) : ℂ) * ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ =
      ((‖v‖ ^ 2 * ‖u‖ ^ 2 : ℝ) : ℂ) := by
    calc ((Module.finrank ℂ T.V : ℝ) : ℂ) * ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ
        = ⟪u, (((Module.finrank ℂ T.V : ℝ) : ℂ) • ∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ := by
          rw [ContinuousLinearMap.smul_apply, inner_smul_right]
      _ = ⟪u, (((‖v‖ ^ 2 : ℝ) : ℂ) • (1 : T.V →L[ℂ] T.V)) u⟫_ℂ := by rw [hop]
      _ = ((‖v‖ ^ 2 : ℝ) : ℂ) * ⟪u, u⟫_ℂ := by
          rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]
      _ = _ := by
          have h : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
            apply Complex.ext
            · simpa using inner_self_eq_norm_sq (𝕜 := ℂ) u
            · simpa using inner_self_im (𝕜 := ℂ) u
          rw [h, ← Complex.ofReal_mul]
  rw [← hint] at hfin
  exact_mod_cast hfin

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma pmat_entry_cases {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a b : Fin n) :
    pmat z a b = 0 ∨ ε a ≠ ε b := by
  unfold pmat
  split_ifs with h h'
  · exact Or.inr h.2
  · exact Or.inr (Ne.symm h'.2)
  · exact Or.inl rfl

lemma jsgn_ne {x y : Bool} (h : x ≠ y) :
    ((if y then 1 else -1 : ℂ)) = -(if x then 1 else -1) := by
  cases x <;> cases y <;> simp at h ⊢

theorem pmat_inP {ε : Fin n → Bool} (z : PCoord ε → ℂ) : inP ε (pmat z) := by
  have h2 : pmat z * Jm ε = -(Jm ε * pmat z) := by
    ext a b
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
    rcases pmat_entry_cases z a b with h | h
    · rw [h]
      simp
    · rw [jsgn_ne h]
      ring
  refine ⟨?_, h2⟩
  unfold inG
  rw [(pmat_isHermitian z).eq, h2]
  simp

theorem pmat_coords {ε : Fin n → Bool} (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) :
    pmat (fun ab : PCoord ε => X ab.1.1 ab.1.2) = X := by
  obtain ⟨hG, hJ⟩ := hX
  unfold inG at hG
  have hent : ∀ a b, X a b * (if ε b then 1 else -1) = -((if ε a then 1 else -1) * X a b) := by
    intro a b
    have h := congrFun (congrFun hJ a) b
    simpa [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] using h
  have hzero : ∀ a b, ε a = ε b → X a b = 0 := by
    intro a b hab
    have h := hent a b
    rw [hab] at h
    cases hb : ε b <;> simp [hb] at h <;>
      first
        | exact h
        | linear_combination h / 2
        | linear_combination (-1 / 2 : ℂ) * h
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    cases ε a <;> simp
  have hH : Xᴴ = X := by
    have h1 : Xᴴ * Jm ε = X * Jm ε := by
      rw [hJ]
      exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = X * Jm ε * Jm ε := by rw [h1]
      _ = X := by rw [mul_assoc, hJJ, mul_one]
  ext a b
  unfold pmat
  split_ifs with h h'
  · rfl
  · have h3 := congrFun (congrFun hH a) b
    rw [Matrix.conjTranspose_apply] at h3
    exact h3
  · apply (hzero a b ?_).symm
    rcases lt_trichotomy a b with hab | hab | hab
    · by_contra hne
      exact h' ⟨hab, Ne.symm hne⟩
    · rw [hab]
    · by_contra hne
      exact h ⟨hab, hne⟩

def pmatHalfSq {ε : Fin n → Bool} (z : PCoord ε → ℂ) (ab : Fin n × Fin n) : ℝ :=
  if h : ab.2 < ab.1 ∧ ε ab.1 ≠ ε ab.2 then ‖z ⟨ab, h⟩‖ ^ 2 else 0

lemma norm_pmat_sq {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a b : Fin n) :
    ‖pmat z a b‖ ^ 2 = pmatHalfSq z (a, b) + pmatHalfSq z (b, a) := by
  unfold pmat pmatHalfSq
  dsimp only
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => lt_asymm h1.1 h.1
    simp only [dif_pos h1, dif_neg h2, add_zero]
  · by_cases h2 : a < b ∧ ε b ≠ ε a
    · simp only [dif_neg h1, dif_pos h2, norm_star, zero_add]
    · simp only [dif_neg h1, dif_neg h2, norm_zero, add_zero]
      norm_num

lemma sum_pmatHalfSq {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∑ ab : Fin n × Fin n, pmatHalfSq z ab = ∑ ab : PCoord ε, ‖z ab‖ ^ 2 := by
  classical
  have e1 : ∑ ab : Fin n × Fin n, pmatHalfSq z ab =
      ∑ ab ∈ univ.filter (fun ab : Fin n × Fin n => ab.2 < ab.1 ∧ ε ab.1 ≠ ε ab.2), pmatHalfSq z ab := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ab _ => ?_
    split_ifs with h
    · rfl
    · unfold pmatHalfSq
      rw [dif_neg h]
  rw [e1, Finset.sum_subtype (p := fun ab : Fin n × Fin n => ab.2 < ab.1 ∧ ε ab.1 ≠ ε ab.2) _
    (fun ab => by simp) (pmatHalfSq z)]
  refine Finset.sum_congr rfl fun ab _ => ?_
  unfold pmatHalfSq
  rw [dif_pos ab.2]

theorem hs_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : hs (pmat z) = 2 * ∑ ab, ‖z ab‖ ^ 2 := by
  unfold S7.hs
  have e : ∀ i j, ‖pmat z i j‖ ^ 2 = pmatHalfSq z (i, j) + pmatHalfSq z (j, i) := norm_pmat_sq z
  simp only [e, Finset.sum_add_distrib]
  have hprod : ∑ i, ∑ j, pmatHalfSq z (i, j) = ∑ ab : Fin n × Fin n, pmatHalfSq z ab :=
    (Fintype.sum_prod_type' (fun i j => pmatHalfSq z (i, j))).symm
  have hswap : ∑ i, ∑ j, pmatHalfSq z (j, i) = ∑ i, ∑ j, pmatHalfSq z (i, j) := Finset.sum_comm
  rw [hswap, hprod, sum_pmatHalfSq]
  ring

lemma pmat_diag_zero {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a : Fin n) : pmat z a a = 0 := by
  simp [pmat]

theorem sum_pev {ε : Fin n → Bool} (z : PCoord ε → ℂ) : ∑ a, pev z a = 0 := by
  have h := (pmat_isHermitian z).trace_eq_sum_eigenvalues
  have htr : (pmat z).trace = 0 := by simp [Matrix.trace, pmat_diag_zero]
  rw [htr] at h
  unfold pev
  have h2 : (((∑ i, (pmat_isHermitian z).eigenvalues i : ℝ)) : ℂ) = 0 := by
    rw [Complex.ofReal_sum]
    exact h.symm
  have h3 := Complex.ofReal_eq_zero.mp h2
  convert h3 using 2

theorem card_PCoord (ε : Fin n → Bool) : Fintype.card (PCoord ε) = pOf ε * qOf ε := by
  classical
  rw [Fintype.card_subtype, pOf, qOf, ← Finset.card_product]
  refine Finset.card_nbij' (fun ab => if ε ab.1 then ab else (ab.2, ab.1))
    (fun xy => (max xy.1 xy.2, min xy.1 xy.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h
    obtain ⟨hba, hne⟩ := h
    cases ha : ε a <;> cases hb : ε b <;> simp_all
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_setOf_eq] at h
    obtain ⟨hx, hy⟩ := h
    have hxy : x ≠ y := by
      intro e
      rw [e, hy] at hx
      exact Bool.false_ne_true hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [max_eq_right h.le, min_eq_left h.le]
      exact ⟨h, by rw [hx, hy]; decide⟩
    · rw [max_eq_left h.le, min_eq_right h.le]
      exact ⟨h, by rw [hx, hy]; decide⟩
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h
    obtain ⟨hba, hne⟩ := h
    cases ha : ε a
    · simp only [ha, Bool.false_eq_true, if_false]
      rw [max_eq_right hba.le, min_eq_left hba.le]
    · simp only [ha, if_true]
      rw [max_eq_left hba.le, min_eq_right hba.le]
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_setOf_eq] at h
    obtain ⟨hx, hy⟩ := h
    have hxy : x ≠ y := by
      intro e
      rw [e, hy] at hx
      exact Bool.false_ne_true hx
    dsimp only
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [max_eq_right h.le, min_eq_left h.le]
      simp [hy]
    · rw [max_eq_left h.le, min_eq_right h.le]
      simp [hx]

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def volU (M : ℕ) : ℝ := ∏ i ∈ range M, 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)

theorem volU_eq_pow_div (M : ℕ) : volU M = 2 ^ M * Real.pi ^ (∑ i ∈ range M, (i + 1)) /
    ∏ i ∈ range M, (i.factorial : ℝ) := by
  rw [volU, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Finset.prod_pow_eq_pow_sum]

theorem volU_sum_succ_add (p q : ℕ) : ∑ i ∈ range (p + q), (i + 1) =
    ∑ i ∈ range p, (i + 1) + ∑ i ∈ range q, (i + 1) + p * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← Nat.add_assoc, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem volU_factProd_pos (M : ℕ) : (0 : ℝ) < ∏ i ∈ range M, (i.factorial : ℝ) := Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos i)

theorem volU_ratio (p q m : ℕ) (h : p + q = m) :
    volU p * volU q / volU m = (∏ i ∈ range m, (i.factorial : ℝ)) /
      (Real.pi ^ (p * q) * (∏ i ∈ range p, (i.factorial : ℝ)) *
        ∏ i ∈ range q, (i.factorial : ℝ)) := by
  subst h
  have hp := volU_factProd_pos p
  have hq := volU_factProd_pos q
  have hn := volU_factProd_pos (p + q)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [volU_eq_pow_div, volU_eq_pow_div, volU_eq_pow_div, volU_sum_succ_add]
  simp only [pow_add]
  field_simp

theorem volU_factProd_mul_le (p q : ℕ) :
    (∏ i ∈ range p, i.factorial) * (∏ i ∈ range q, i.factorial) ≤
      ∏ i ∈ range (p + q), i.factorial := by
  rw [Finset.prod_range_add]
  exact Nat.mul_le_mul le_rfl
    (Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i _ => Nat.factorial_le (by omega)))

theorem volU_pOf_add_qOf (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have hone : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem cPQ_eq_volU (ε : Fin n → Bool) : cPQ ε = volU (pOf ε) * volU (qOf ε) / volU n := by
  rw [volU_ratio _ _ _ (volU_pOf_add_qOf ε)]
  rfl

theorem inv_pi_pow_le_cPQ (ε : Fin n → Bool) : (Real.pi ^ (pOf ε * qOf ε))⁻¹ ≤ cPQ ε := by
  have hle := volU_factProd_mul_le (pOf ε) (qOf ε)
  rw [volU_pOf_add_qOf ε] at hle
  have hle' : (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) ≤
      ∏ i ∈ range n, (i.factorial : ℝ) := by
    exact_mod_cast hle
  have hp := volU_factProd_pos (pOf ε)
  have hq := volU_factProd_pos (qOf ε)
  have hpi : 0 < Real.pi ^ (pOf ε * qOf ε) := pow_pos Real.pi_pos _
  have hD : 0 < Real.pi ^ (pOf ε * qOf ε) * (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
      ∏ i ∈ range (qOf ε), (i.factorial : ℝ) := mul_pos (mul_pos hpi hp) hq
  unfold cPQ
  rw [le_div_iff₀ hD]
  have he : (Real.pi ^ (pOf ε * qOf ε))⁻¹ * (Real.pi ^ (pOf ε * qOf ε) *
      (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ)) =
      (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) := by
    rw [mul_assoc, inv_mul_cancel_left₀ hpi.ne']
  linarith

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdDefs
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def Dvec (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) - ((a : ℕ) : ℝ)

def lamT (lam : Fin n → ℝ) (t : ℕ) : Fin n → ℝ := lam + (t : ℝ) • Dvec n

def Vand (lam : Fin n → ℝ) : ℝ := ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b)

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem sCoef_lamT (lam : Fin n → ℝ) (t : ℕ) {i : ℕ} (hi : i + 1 < n) :
    sCoef (lamT lam t) i = sCoef lam i + t := by
  simp only [sCoef, dif_pos hi, lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.val_mk]
  push_cast
  ring

theorem sCoef_zero_of (i : ℕ) (hi : i + 1 < n) : sCoef (0 : Fin n → ℝ) i = 1 := by
  simp [sCoef, hi]

theorem ph_lamT (lam : Fin n → ℝ) (t : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Ph (lamT lam t) X = Ph lam X + (t : ℝ) * Ph (0 : Fin n → ℝ) X := by
  unfold Ph
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i + 1 < n := by
    have := Finset.mem_range.mp hi
    omega
  rw [sCoef_lamT lam t hi', sCoef_zero_of i hi']
  ring

theorem dvec_antitone : Antitone (Dvec n) := by
  intro a b hab
  simp only [Dvec]
  have h1 : (a : ℕ) ≤ (b : ℕ) := hab
  have h2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

theorem lamT_apply (lam : Fin n → ℝ) (t : ℕ) (a : Fin n) :
    lamT lam t a = lam a + (t : ℝ) * ((n : ℝ) - 1 - ((a : ℕ) : ℝ)) := by
  simp only [lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem lamT_sub (lam : Fin n → ℝ) (t : ℕ) (a b : Fin n) :
    lamT lam t a - lamT lam t b = (lam a - lam b) + (t : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  rw [lamT_apply, lamT_apply]
  ring

theorem strictAnti_lamT {lam : Fin n → ℝ} (hlam : StrictAnti lam) (t : ℕ) : StrictAnti (lamT lam t) := by
  intro a b hab
  rw [lamT_apply, lamT_apply]
  have h1 := hlam hab
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast (show (a : ℕ) < b from hab)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  nlinarith

theorem isHCParam_lamT {lam : Fin n → ℝ} (hlam : IsHCParam lam) (t : ℕ) : IsHCParam (lamT lam t) := by
  refine ⟨strictAnti_lamT hlam.1 t, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hlam.2 a
  refine ⟨m + (t : ℤ) * ((n : ℤ) - 1 - ((a : ℕ) : ℤ)), ?_⟩
  rw [lamT_apply]
  push_cast
  linear_combination hm

theorem gap_lamT {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) (t : ℕ) : GapAtLeast ε (lamT lam t) (h + t) := by
  intro a b hab
  have hne : a ≠ b := fun e => hab (by rw [e])
  have hg := hgap a b hab
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  rw [lamT_sub]
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have hl := hlam h1
    have hab' : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast (show (a : ℕ) + 1 ≤ b from h1)
    rw [abs_of_pos (sub_pos.mpr hl)] at hg
    exact le_abs.mpr (Or.inl (by nlinarith))
  · have hl := hlam h1
    have hab' : ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ) := by exact_mod_cast (show (b : ℕ) + 1 ≤ a from h1)
    rw [abs_of_neg (sub_neg.mpr hl)] at hg
    exact le_abs.mpr (Or.inr (by nlinarith))

theorem lowK_lamT (ε : Fin n → Bool) (lam : Fin n → ℝ) (t : ℕ) :
    lowK ε (lamT lam t) = lowK ε lam + (t : ℝ) • Dvec n := by
  unfold lowK lamT
  abel

theorem vand_pos {lam : Fin n → ℝ} (hlam : StrictAnti lam) : 0 < Vand lam := by
  unfold Vand
  refine Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => ?_))
  have hab : a < b := (Finset.mem_filter.mp hb).2
  exact sub_pos.mpr (hlam hab)

theorem ratioV_eq_vand {μ : Fin n → ℝ} (hμ : StrictAnti μ) (s : Fin n) :
    ratioV μ s = Vand (μ + Pi.single s 1) / Vand μ := by
  have hne : ∀ a b : Fin n, a ≠ b → μ a - μ b ≠ 0 := fun a b h => sub_ne_zero.mpr (hμ.injective.ne h)
  have hV : Vand μ ≠ 0 := (vand_pos hμ).ne'
  have hfac : ∀ a ∈ (univ : Finset (Fin n)), ∀ b ∈ univ.filter (fun b : Fin n => a < b),
      (μ + Pi.single s (1 : ℝ) : Fin n → ℝ) a - (μ + Pi.single s (1 : ℝ) : Fin n → ℝ) b =
        (μ a - μ b) * ((if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1) *
          (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1)) := by
    intro a _ b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    have hab' : a ≠ b := ne_of_lt hab
    by_cases ha : a = s
    · subst ha
      have h1 : μ a - μ b ≠ 0 := hne a b hab'
      rw [if_pos rfl, if_neg hab'.symm, mul_one]
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab'.symm, add_zero]
      field_simp <;> ring
    · by_cases hb' : b = s
      · subst hb'
        have h2 : μ b - μ a ≠ 0 := hne b a hab'.symm
        rw [if_neg ha, if_pos rfl, one_mul]
        simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne ha, add_zero]
        field_simp <;> ring
      · rw [if_neg ha, if_neg hb', mul_one, mul_one]
        simp only [Pi.add_apply, Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb', add_zero]
  rw [eq_div_iff hV]
  have hsplit : Vand (μ + Pi.single s 1) = Vand μ *
      ((∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1)) *
        ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1)) := by
    unfold Vand
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun a ha => ?_)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun b hb => hfac a ha b hb)
  have hA : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1)) =
        ∏ b ∈ univ.filter (fun b : Fin n => s < b), (μ s + 1 - μ b) / (μ s - μ b) := by
    rw [Finset.prod_eq_single s]
    · exact Finset.prod_congr rfl (fun b _ => if_pos rfl)
    · intro a _ ha
      exact Finset.prod_eq_one (fun b _ => if_neg ha)
    · intro h
      exact absurd (Finset.mem_univ s) h
  have hB : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1)) =
        ∏ a ∈ univ.filter (fun a : Fin n => a < s), (μ s + 1 - μ a) / (μ s - μ a) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [Finset.prod_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsplit, hA, hB]
  unfold ratioV
  rw [← Finset.prod_filter_mul_prod_filter_not (univ.erase s) (fun x => x < s)]
  have e1 : (univ.erase s).filter (fun x => x < s) = univ.filter (fun x : Fin n => x < s) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
  have e2 : (univ.erase s).filter (fun x => ¬ x < s) = univ.filter (fun x : Fin n => s < x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h.2 (Ne.symm h.1), fun h => ⟨ne_of_gt h, le_of_lt h⟩⟩
  rw [e1, e2]
  ring

theorem prod_sub_lt_eq_factorial (b : Fin n) :
    ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = ((b : ℕ).factorial : ℝ) := by
  have gen : ∀ m : ℕ, ∏ k ∈ range m, ((m : ℝ) - (k : ℝ)) = (m.factorial : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ', Nat.factorial_succ, Nat.cast_mul, ← ih]
      have e : ∀ k ∈ range m, (((m + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) = (m : ℝ) - (k : ℝ) := by
        intro k _
        push_cast
        ring
      rw [Finset.prod_congr rfl e]
      push_cast
      ring
  have h1 : ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ k ∈ range (b : ℕ), (((b : ℕ) : ℝ) - (k : ℝ)) := by
    apply Finset.prod_nbij (fun a : Fin n => (a : ℕ))
    · intro a ha
      exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
    · intro a _ a' _ h
      exact Fin.ext h
    · intro k hk
      have hk' : k < (b : ℕ) := Finset.mem_range.mp hk
      refine ⟨⟨k, lt_trans hk' b.isLt⟩, ?_, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact hk'
    · intro a _
      rfl
  rw [h1, gen]

theorem prod_pairs_eq_factorial (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range n, (i.factorial : ℝ) := by
  rw [Finset.prod_comm' (t' := univ) (s' := fun b => univ.filter (fun a : Fin n => a < b))
    (by intro a b; simp)]
  rw [Finset.prod_congr rfl (fun b _ => prod_sub_lt_eq_factorial b)]
  exact Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) n

theorem dimVlam_eq_vand {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    dimVlam lam = Vand lam / ∏ i ∈ range n, (i.factorial : ℝ) := by
  unfold dimVlam Vand
  rw [prod_pairs_eq_factorial]
  congr 1
  refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b hb => ?_))
  exact abs_of_pos (sub_pos.mpr (hlam (Finset.mem_filter.mp hb).2))

end ReciprocityTheory.ChartRestriction.DS
end
end
