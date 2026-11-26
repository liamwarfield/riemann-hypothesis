module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCas
public import Formalism.FormalDegreeBessel.StatementIO
public import Formalism.FormalDegreeBessel.StatementDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PartialTrace

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma toMK_mul' (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

lemma toMK_one' : toMK (1 : KG ε) = 1 := rfl

lemma op_mul' (T : KType ε Λ) (k k' : KG ε) : T.op (k * k') = T.op k * T.op k' := by
  show ((T.τ (k * k') : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
  rw [map_mul]
  rfl

lemma op_one' (T : KType ε Λ) : T.op 1 = 1 := by
  show ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
  rw [map_one]
  rfl

lemma toMK_mul_inv' (k : KG ε) : toMK k * toMK k⁻¹ = 1 := by rw [← toMK_mul', mul_inv_cancel, toMK_one']

lemma toMK_inv_mul' (k : KG ε) : toMK k⁻¹ * toMK k = 1 := by rw [← toMK_mul', inv_mul_cancel, toMK_one']

theorem psiM_kexp (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    PsiM T μ (toMK k * NormedSpace.exp X) = T.op k * psM T μ (NormedSpace.exp X) := by
  have h : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧
      toMK k * NormedSpace.exp X = toMK k' * NormedSpace.exp X' := ⟨k, X, hX, rfl⟩
  obtain ⟨hk, hXX⟩ := polar_unique hX h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  rw [PsiM, dite_eq_left h, ← hXX, ← hk]

theorem psiM_equiv (T : KType ε Λ) (μ : Fin n → ℤ) (k₁ k₂ : KG ε) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    PsiM T μ (toMK k₁ * g * toMK k₂) = T.op k₁ * PsiM T μ g * T.op k₂ := by
  obtain ⟨k, X, hX, rfl⟩ := polar_exists hg
  obtain ⟨hX', hexp⟩ := inP_conj k₂⁻¹ hX
  rw [inv_inv] at hX' hexp
  have hc := psM_conj T μ k₂⁻¹ (NormedSpace.exp X)
  rw [inv_inv] at hc
  have hg' : toMK k₁ * (toMK k * NormedSpace.exp X) * toMK k₂ =
      toMK (k₁ * k * k₂) * NormedSpace.exp (toMK k₂⁻¹ * X * toMK k₂) := by
    rw [hexp, toMK_mul', toMK_mul']
    simp only [_root_.mul_assoc]
    rw [← _root_.mul_assoc (toMK k₂) (toMK k₂⁻¹), toMK_mul_inv', _root_.one_mul]
  rw [hg', psiM_kexp T μ _ hX', psiM_kexp T μ k hX, hexp, hc, op_mul', op_mul']
  simp only [_root_.mul_assoc]
  rw [← _root_.mul_assoc (T.op k₂) (T.op k₂⁻¹), ← op_mul', mul_inv_cancel, op_one', _root_.one_mul]

theorem psiM_one (T : KType ε Λ) (μ : Fin n → ℤ) : PsiM T μ 1 = 1 := by
  have h0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by
    first | exact ⟨by simp [inG], by simp⟩ | exact ⟨by first | exact inG_zero ε | exact inG_zero, by simp⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = toMK (1 : KG ε) * NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [toMK_one', NormedSpace.exp_zero, one_mul]
  rw [h1, psiM_kexp T μ 1 h0, op_one', one_mul, NormedSpace.exp_zero]
  first | exact psM_one T μ | exact psM_one | simp [psM_one]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiCapelliStatement
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def negL (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun z => -Lhol (Matrix.single a b 1) F z

def PsiCapelliStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ), IsMu lam μ →
    ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) (PsiM T μ) g =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • PsiM T μ g

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecPos
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

private abbrev dpP (T : KType ε Λ) (k : KG ε) : T.V →L[ℂ] T.V := T.op k * projW T * T.op k⁻¹

private lemma dp_op_inv (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
  exact op_inv_eq_adjoint T k

private lemma dpP_apply (T : KType ε Λ) (k : KG ε) (v : T.V) :
    dpP T k v = ⟪T.op k T.w, v⟫_ℂ • T.op k T.w := by
  show T.op k (projW T (T.op k⁻¹ v)) = _
  unfold projW
  rw [ContinuousLinearMap.smulRight_apply, map_smul, dp_op_inv]
  congr 1
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

private lemma dp_inner_P (T : KType ε Λ) (k : KG ε) (v : T.V) :
    ⟪v, dpP T k v⟫_ℂ = ((‖⟪T.op k T.w, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [dpP_apply, inner_smul_right, ← inner_conj_symm v (T.op k T.w)]
  first
  | (rw [RCLike.mul_conj]; rfl)
  | (rw [RCLike.mul_conj]; norm_cast)
  | (rw [RCLike.mul_conj]; push_cast; ring)
  | (rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring)
  | simp [RCLike.mul_conj]

private lemma dp_cont_P (T : KType ε Λ) : Continuous (dpP T) := by
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hinv : Continuous fun k : KG ε => T.op k⁻¹ := hop.comp continuous_inv
  exact (hop.mul continuous_const).mul hinv

private lemma dp_integrable (T : KType ε Λ) {g : KG ε → ℝ} (hg : Continuous g) :
    Integrable (fun k => ((g k : ℝ) : ℂ) • dpP T k) (muK ε) := by
  haveI := compactSpace_KG ε
  have hf : Continuous (fun k => ((g k : ℝ) : ℂ) • dpP T k) :=
    (Complex.continuous_ofReal.comp hg).smul (dp_cont_P T)
  exact integrableOn_univ.mp (ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn)

private lemma dp_isPositive (T : KType ε Λ) {c : ℝ} (hc : 0 ≤ c) {g : KG ε → ℝ} (hg : Continuous g)
    (hg0 : ∀ k, 0 ≤ g k) :
    ((c : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)).IsPositive := by
  have hI := dp_integrable T hg

  have key : ∀ u v : T.V, ⟪u, (∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) v⟫_ℂ =
      ∫ k, ((g k : ℝ) : ℂ) * ⟪u, dpP T k v⟫_ℂ ∂(muK ε) := by
    intro u v
    have hIv : Integrable (fun k => (((g k : ℝ) : ℂ) • dpP T k) v) (muK ε) :=
      (ContinuousLinearMap.apply ℂ T.V v).integrable_comp hI
    rw [ContinuousLinearMap.integral_apply hI, ← integral_inner hIv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right]

  have hsym : ∀ k (u v : T.V), ⟪dpP T k u, v⟫_ℂ = ⟪u, dpP T k v⟫_ℂ := by
    intro k u v
    rw [dpP_apply, dpP_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
    ring
  refine ⟨?_, ?_⟩
  · intro u v
    change ⟪(((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) u, v⟫_ℂ =
      ⟪u, (((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) v⟫_ℂ
    rw [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
      ← inner_conj_symm _ v, key, key, ← integral_conj, Complex.conj_ofReal]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [map_mul, Complex.conj_ofReal, inner_conj_symm, hsym]
  · intro v
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm, ContinuousLinearMap.smul_apply,
      inner_smul_right, key]
    have e : ∫ k, ((g k : ℝ) : ℂ) * ⟪v, dpP T k v⟫_ℂ ∂(muK ε) =
        ((∫ k, g k * ‖⟪T.op k T.w, v⟫_ℂ‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
      first
      | rw [← integral_complex_ofReal]
      | rw [← integral_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [dp_inner_P]
      push_cast
      ring
    rw [e, ← Complex.ofReal_mul]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    exact mul_nonneg hc (integral_nonneg fun k => mul_nonneg (hg0 k) (sq_nonneg _))

private lemma dp_posDef_conj (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  have hinj : Function.Injective (toMK k).mulVec := by
    intro a b h
    have h2 := congrArg ((toMK k)ᴴ).mulVec h
    simpa [Matrix.mulVec_mulVec, (toMK_facts k).1] using h2
  rw [toMK_inv]
  exact hx.conjTranspose_mul_mul_same hinj

private lemma dp_cont_phi (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    Continuous (fun k : KG ε => (PhiM μ (toMK k⁻¹ * x * toMK k)).re) := by
  have htoMK : Continuous (toMK : KG ε → Matrix (Fin n) (Fin n) ℂ) := by
    unfold toMK toM
    first
    | fun_prop
    | continuity
    | exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hcont : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k :=
    ((htoMK.comp continuous_inv).mul continuous_const).mul htoMK
  have hmem : ∀ k : KG ε, toMK k⁻¹ * x * toMK k ∈ OmegaSet n := by
    intro k
    first
    | exact posSet_subset_omega (dp_posDef_conj k hx)
    | exact posSet_subset_omega (by simpa [posSet] using dp_posDef_conj k hx)
  exact Complex.continuous_re.comp
    ((phiM_differentiableOn μ).continuousOn.comp_continuous hcont hmem)

theorem psM_norm_le (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) {B : ℝ}
    (hB : ∀ k : KG ε, (PhiM μ (toMK k⁻¹ * x * toMK k)).re ≤ B) : ‖psM T μ x‖ ≤ B := by
  set c : ℝ := (Module.finrank ℂ T.V : ℝ) / (muK ε Set.univ).toReal with hc_def
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (muK_univ_pos ε).le
  set g : KG ε → ℝ := fun k => (PhiM μ (toMK k⁻¹ * x * toMK k)).re with hg_def
  have hgc : Continuous g := dp_cont_phi μ hx
  have hg0 : ∀ k, 0 ≤ g k := fun k => (phiM_posDef μ (dp_posDef_conj k hx)).1.le
  have hPhi : ∀ k, PhiM μ (toMK k⁻¹ * x * toMK k) = ((g k : ℝ) : ℂ) := by
    intro k
    apply Complex.ext
    · simp [hg_def]
    · simp [(phiM_posDef μ (dp_posDef_conj k hx)).2]
  have hA : psM T μ x = ((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    unfold psM
    rw [hc_def]
    push_cast
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hPhi, dpP]
  have hone : (1 : T.V →L[ℂ] T.V) = ((c : ℝ) : ℂ) • ∫ k, (((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    rw [← psM_one T μ]
    unfold psM
    rw [hc_def]
    push_cast
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have h1 : toMK k⁻¹ * 1 * toMK k = 1 := by rw [Matrix.mul_one, toMK_inv, (toMK_facts k).1]
    simp only [h1, phiM_one, one_smul, dpP]
  have i1 := dp_integrable T (g := fun _ => (1 : ℝ)) continuous_const
  have i2 := dp_integrable T hgc
  have hlin : ∫ k, (((fun k => B - g k) k : ℝ) : ℂ) • dpP T k ∂(muK ε) =
      (B : ℂ) • (∫ k, (((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k ∂(muK ε)) -
        ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    have i1' : Integrable (fun k => (B : ℂ) • ((((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k)) (muK ε) :=
      i1.smul (B : ℂ)
    have e1 := integral_sub i1' i2
    rw [integral_smul] at e1
    refine (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)).trans e1
    beta_reduce
    rw [smul_smul, ← sub_smul]
    congr 1
    push_cast
    ring
  have hdiff : (B : ℂ) • (1 : T.V →L[ℂ] T.V) - psM T μ x =
      ((c : ℝ) : ℂ) • ∫ k, (((fun k => B - g k) k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    rw [hlin, smul_sub, smul_comm ((c : ℝ) : ℂ) (B : ℂ), ← hone, ← hA]
  have hpos1 := dp_isPositive T hc hgc hg0
  have hpos2 := dp_isPositive T hc (g := fun k => B - g k) (continuous_const.sub hgc)
    (fun k => sub_nonneg.mpr (hB k))
  have h0 : 0 ≤ psM T μ x := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, hA]
    exact hpos1
  have hle : psM T μ x ≤ (B : ℂ) • (1 : T.V →L[ℂ] T.V) := by
    rw [ContinuousLinearMap.le_def, hdiff]
    exact hpos2
  have hB0 : 0 ≤ B := (hg0 1).trans (hB 1)
  calc ‖psM T μ x‖ ≤ ‖(B : ℂ) • (1 : T.V →L[ℂ] T.V)‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hle h0
    _ ≤ ‖(B : ℂ)‖ * ‖(1 : T.V →L[ℂ] T.V)‖ := norm_smul_le _ _
    _ ≤ B * 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg hB0]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hB0
    _ = B := mul_one B

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPhiA
noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def smoothS (n : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {F | ContDiffOn ℂ ∞ F (OmegaSet n)}
  add_mem' hF hG := hF.add hG
  zero_mem' := contDiffOn_const
  smul_mem' c _ hF := hF.const_smul c

private theorem isOpen_OmegaSet' : IsOpen (OmegaSet n) := by
  show IsOpen {z : Matrix (Fin n) (Fin n) ℂ | ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0}
  rw [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_ne_fun ?_ continuous_const
  show Continuous fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z
  by_cases h : (i : ℕ) + 1 ≤ n
  · have e : (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z) =
        fun z => (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := funext fun z => dif_pos h
    rw [e]
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · have e : (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z) = fun _ => 0 :=
      funext fun z => dif_neg h
    rw [e]
    exact continuous_const

theorem lhol_congr {X : Matrix (Fin n) (Fin n) ℂ} {G H : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : Set.EqOn G H (OmegaSet n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol X G z = Lhol X H z := by
  show fderiv ℂ G z (X * z) = fderiv ℂ H z (X * z)
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (isOpen_OmegaSet'.mem_nhds hz) h)]

theorem lhol_mem {X : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) : ContDiffOn ℂ ∞ (Lhol X F) (OmegaSet n) := by
  have h1 :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_OmegaSet').1 hF).2
  have h2 : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => X * z) := by
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun c _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id c) b)
  exact h1.clm_apply h2.contDiffOn

def ltOp (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  (OmegaSet n).indicator (Lhol X F)

theorem ltOp_of_mem {X : Matrix (Fin n) (Fin n) ℂ} (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) : ltOp X F z = Lhol X F z := by
  exact Set.indicator_of_mem hz _

theorem ltOp_of_not_mem {X : Matrix (Fin n) (Fin n) ℂ} (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∉ OmegaSet n) : ltOp X F z = 0 := by
  simp [ltOp, hz]

theorem ltOp_mem {X : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) : ContDiffOn ℂ ∞ (ltOp X F) (OmegaSet n) := by
  exact (lhol_mem hF).congr fun z hz => ltOp_of_mem F hz

theorem differentiableAt_of_mem {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ F z := by
  exact ((hF.differentiableOn (by simp <;> exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) z hz).differentiableAt (isOpen_OmegaSet'.mem_nhds hz)

def eOp (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (smoothS n) where
  toFun F := ⟨ltOp X F, ltOp_mem F.2⟩
  map_add' F G := by
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp only [Submodule.coe_add, Pi.add_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (F.1 + G.1) z (X * z) = fderiv ℂ F.1 z (X * z) + fderiv ℂ G.1 z (X * z)
      erw [((differentiableAt_of_mem F.2 hz).hasFDerivAt.add (differentiableAt_of_mem G.2 hz).hasFDerivAt).fderiv]
      rfl
    · simp only [Submodule.coe_add, Pi.add_apply, ltOp_of_not_mem _ hz, add_zero]
  map_smul' c F := by
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (c • F.1) z (X * z) = c • fderiv ℂ F.1 z (X * z)
      erw [fderiv_const_smul (differentiableAt_of_mem F.2 hz)]
      rfl
    · simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, ltOp_of_not_mem _ hz, smul_zero]

theorem eOp_apply (X : Matrix (Fin n) (Fin n) ℂ) (F : smoothS n) :
    ((eOp X F : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) = ltOp X F := rfl

theorem eOp_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : eOp (X - Y) = eOp X - eOp Y := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext z
  show ltOp (X - Y) F.1 z = ltOp X F.1 z - ltOp Y F.1 z
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, ltOp_of_mem _ hz, ltOp_of_mem _ hz]
    show fderiv ℂ F.1 z ((X - Y) * z) = fderiv ℂ F.1 z (X * z) - fderiv ℂ F.1 z (Y * z)
    rw [Matrix.sub_mul, map_sub]
  · rw [ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, sub_zero]

theorem eOp_zero : eOp (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  apply LinearMap.ext; intro F
  apply Subtype.ext; funext z
  show ltOp 0 F z = 0
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz]
    show fderiv ℂ F.1 z (0 * z) = 0
    rw [Matrix.zero_mul, map_zero]
  · rw [ltOp_of_not_mem _ hz]

private theorem Lhol_commutator_on_OmegaSet {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : ContDiffOn ℂ ∞ F (OmegaSet n))
    (X Y : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol X (Lhol Y F) z - Lhol Y (Lhol X F) z = Lhol (Y * X - X * Y) F z := by
  have hc := hF.contDiffAt (isOpen_OmegaSet'.mem_nhds hz)
  have h1 := ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_OmegaSet').1 hF).2
  have hd := ((h1.differentiableOn (by simp <;> exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) z hz).differentiableAt
    (isOpen_OmegaSet'.mem_nhds hz) |>.hasFDerivAt
  have hs := hc.isSymmSndFDerivAt (by first | exact le_top | (simp; done) | (simp <;> exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) : ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω))) | (simp <;> decide))
  let LX : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun w => X * w
      map_add' := fun a b => Matrix.mul_add X a b
      map_smul' := fun c a => Matrix.mul_smul X c a }
  let LY : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun w => Y * w
      map_add' := fun a b => Matrix.mul_add Y a b
      map_smul' := fun c a => Matrix.mul_smul Y c a }
  show fderiv ℂ (fun w => fderiv ℂ F w (LY w)) z (X * z) -
      fderiv ℂ (fun w => fderiv ℂ F w (LX w)) z (Y * z) = fderiv ℂ F z ((Y * X - X * Y) * z)
  erw [(hd.clm_apply LY.hasFDerivAt).fderiv, (hd.clm_apply LX.hasFDerivAt).fderiv]
  show fderiv ℂ F z (Y * (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) -
      (fderiv ℂ F z (X * (Y * z)) + fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z)) = _
  rw [show fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) = fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z) from
    hs (X * z) (Y * z)]
  rw [Matrix.sub_mul, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  abel

theorem eOp_comm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    eOp X * eOp Y - eOp Y * eOp X = eOp (Y * X - X * Y) := by
  apply LinearMap.ext; intro F
  apply Subtype.ext; funext z
  show ltOp X (ltOp Y F) z - ltOp Y (ltOp X F) z = ltOp (Y * X - X * Y) F z
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, ltOp_of_mem _ hz, ltOp_of_mem _ hz,
      lhol_congr (fun w hw => ltOp_of_mem F hw) hz, lhol_congr (fun w hw => ltOp_of_mem F hw) hz]
    exact Lhol_commutator_on_OmegaSet F.2 X Y hz
  · rw [ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, sub_zero]

theorem isGlRep_eOp (X : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ a b c d, X c d * X a b - X a b * X c d =
      (if b = c then X a d else 0) - (if d = a then X c b else 0)) :
    IsGlRep (fun a b => eOp (X a b)) := by
  intro a b c d
  rw [eOp_comm, hX a b c d, eOp_sub]
  split_ifs <;> simp [eOp_zero]

theorem opPow_eqOn (X Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (c : ℂ)
    (hY : ∀ a b, Y a b = c • X (σ a) (σ b)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (hFG : Set.EqOn F G (OmegaSet n)) (k : ℕ) (a b : Fin n) :
    Set.EqOn (opPow (fun a b => Lhol (Y a b)) k a b F)
      (fun z => c ^ k * ((ePow (fun a b => eOp (X a b)) k (σ a) (σ b) G : smoothS n) :
        Matrix (Fin n) (Fin n) ℂ → ℂ) z) (OmegaSet n) := by
  unfold ePow
  simp only [Bl.ThirdBlockLemmaA.goal1]
  induction k generalizing a b with
  | zero =>
    intro z hz
    by_cases hab : a = b
    · subst hab
      simp [opPow, Matrix.one_apply, hFG hz]
    · have hs : σ a ≠ σ b := fun h => hab (σ.injective h)
      simp [opPow, Matrix.one_apply, hab, hs]
  | succ k ih =>
    intro z hz
    have hterm : ∀ d, Lhol (Y a d) (opPow (fun a b => Lhol (Y a b)) k d b F) z =
        c ^ (k + 1) * ((eOp (X (σ a) (σ d)) ((((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G) :
          smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
      intro d
      set g : smoothS n := (((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G with hg
      rw [lhol_congr (ih d b) hz, eOp_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (fun w => c ^ k * (g : Matrix (Fin n) (Fin n) ℂ → ℂ) w) z (Y a d * z) =
        c ^ (k + 1) * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (X (σ a) (σ d) * z)
      erw [fderiv_const_mul (differentiableAt_of_mem g.2 hz) (c ^ k)]
      rw [hY a d, Matrix.smul_mul]
      show c ^ k * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (c • (X (σ a) (σ d) * z)) = _
      rw [map_smul, smul_eq_mul]
      ring
    simp only [opPow, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun d _ => hterm d, pow_succ' (Matrix.of fun a b => eOp (X a b)) k,
      Matrix.mul_apply]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Module.End.mul_apply,
      Matrix.of_apply, Finset.mul_sum]
    exact Fintype.sum_equiv σ _ _ (fun d => rfl)

theorem opGelfand_eq (X Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (c : ℂ)
    (hY : ∀ a b, Y a b = c • X (σ a) (σ b)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (hFG : Set.EqOn F G (OmegaSet n)) (k : ℕ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    opGelfand (fun a b => Lhol (Y a b)) k F z =
      c ^ k * ((gelfand (fun a b => eOp (X a b)) k G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
  simp only [opGelfand, gelfand, Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum,
    Finset.mul_sum]
  exact Fintype.sum_equiv σ (fun a => opPow (fun a b => Lhol (Y a b)) k a a F z)
    (fun a => c ^ k * ((ePow (fun a b => eOp (X a b)) k a a G : smoothS n) :
      Matrix (Fin n) (Fin n) ℂ → ℂ) z)
    fun a => opPow_eqOn X Y σ c hY F G hFG k a a hz

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
