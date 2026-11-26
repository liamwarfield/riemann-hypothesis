module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCas
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCasB
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def casCoef (μ : Fin n → ℤ) (a b : Fin n) : ℝ :=
  (if a = b then (μ a : ℝ) ^ 2 else 0) + (if b < a then (μ a : ℝ) - μ b else 0)

theorem sum_casCoef (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∑ a, ∑ b, casCoef μ a b = casVal lam := by
  have hcard : ∀ a : Fin n, (((univ.filter fun b : Fin n => b < a).card : ℕ) : ℝ) -
      (((univ.filter fun b : Fin n => a < b).card : ℕ) : ℝ) = -2 * rho n a := by
    intro a
    rw [Finset.filter_gt_eq_Iio, Finset.filter_lt_eq_Ioi, Fin.card_Iio, Fin.card_Ioi]
    have ha : 1 + (a : ℕ) ≤ n := by have := a.isLt; omega
    rw [Nat.sub_sub, Nat.cast_sub ha]
    simp only [rho]
    push_cast
    ring
  have hrow : ∀ a, ∑ b, casCoef μ a b = (μ a : ℝ) ^ 2 +
      ∑ b, ((if b < a then (μ a : ℝ) else 0) - if b < a then (μ b : ℝ) else 0) := by
    intro a
    rw [show (μ a : ℝ) ^ 2 = ∑ b, (if a = b then (μ a : ℝ) ^ 2 else 0) by simp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold casCoef
    split_ifs <;> ring
  have hswap : ∑ a : Fin n, ∑ b : Fin n, (if b < a then (μ b : ℝ) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if a < b then (μ a : ℝ) else 0) := Finset.sum_comm
  have hA : ∀ a : Fin n, ∑ b : Fin n, (if b < a then (μ a : ℝ) else 0) =
      (μ a : ℝ) * (((univ.filter fun b : Fin n => b < a).card : ℕ) : ℝ) := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hB : ∀ a : Fin n, ∑ b : Fin n, (if a < b then (μ a : ℝ) else 0) =
      (μ a : ℝ) * (((univ.filter fun b : Fin n => a < b).card : ℕ) : ℝ) := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc ∑ a, ∑ b, casCoef μ a b = ∑ a, (μ a : ℝ) ^ 2 + ((∑ a, ∑ b, if b < a then (μ a : ℝ) else 0) -
        ∑ a, ∑ b, if b < a then (μ b : ℝ) else 0) := by
        simp only [hrow, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ a, ((μ a : ℝ) ^ 2 + (μ a : ℝ) * (-2 * rho n a)) := by
        rw [hswap, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hA, hB, ← hcard]
        ring
    _ = casVal lam := by
        simp only [casVal, nsq, dot, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hμ a]
        ring

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem isUpperTri_one : IsUpperTri (1 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Matrix.one_apply_ne h.ne'

private theorem diag_line (a l : Fin n) (t : ℂ) :
    (1 + t • Matrix.single a a (1 : ℂ)) l l = if l = a then 1 + t else 1 := by
  by_cases h : l = a
  · subst h
    simp
  · have : ¬(a = l ∧ a = l) := fun h' => h h'.1.symm
    simp [h, Matrix.single_apply_of_ne (h := this)]

private theorem diag_prod (μ : Fin n → ℤ) (a : Fin n) (t : ℂ) :
    ∏ l, ((if l = a then 1 + t else 1) : ℂ) ^ (-μ l) = (1 + t) ^ (-μ a) := by
  rw [Finset.prod_eq_single a (fun l _ hl => by simp [hl]) (by simp)]
  simp

private theorem hasDerivAt_scale (μ : Fin n → ℤ) (a : Fin n) (c : ℂ) :
    HasDerivAt (fun t : ℂ => (1 + t) ^ (-μ a) * c) (-(μ a : ℂ) * c) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => 1 + t) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℂ)).const_add 1
  have h2 := (hasDerivAt_zpow (-μ a) (1 + 0 : ℂ) (Or.inl (by simp))).comp (0 : ℂ) h1
  simpa [Function.comp_def] using h2.mul_const c

private theorem eventually_ne_line : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0 :=
  (continuous_const.add continuous_id).continuousAt.eventually_ne (by simp)

theorem lhol_phiM_lower (μ : Fin n → ℤ) {a b : Fin n} (hab : b < a) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : Lhol (Matrix.single a b 1) (PhiM μ) z = 0 := by
  have hconst : ∀ t : ℂ, PhiM μ (z + t • (Matrix.single a b 1 * z)) = PhiM μ z := by
    intro t
    have hc : IsLowerTri (1 + t • Matrix.single a b (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ b = j) := fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (hab.trans hij) (lt_irrefl _)
      simp [Matrix.one_apply_ne hij.ne, Matrix.single_apply_of_ne (h := this)]
    have hcd : ∀ l, (1 + t • Matrix.single a b (1 : ℂ)) l l = 1 := by
      intro l
      have : ¬(a = l ∧ b = l) := fun ⟨h1, h2⟩ => hab.ne' (h1.trans h2.symm)
      simp [Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ hc isUpperTri_one (fun l => by rw [hcd l]; exact one_ne_zero)
      (fun l => by simp) hz
    have e : (1 + t • Matrix.single a b (1 : ℂ)) * z * 1 = z + t • (Matrix.single a b 1 * z) := by
      rw [Matrix.mul_one, add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← e, h, Finset.prod_eq_one (fun l _ => by rw [hcd l, Matrix.one_apply_eq, mul_one, _root_.one_zpow]),
      one_mul]
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (Matrix.single a b 1 * z)
  have h0 : HasDerivAt (fun t : ℂ => PhiM μ (z + t • (Matrix.single a b 1 * z))) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  exact hd.unique h0

theorem lhol_phiM_diag (μ : Fin n → ℤ) (a : Fin n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol (Matrix.single a a 1) (PhiM μ) z = -(μ a : ℂ) * PhiM μ z := by
  have key : ∀ t : ℂ, 1 + t ≠ 0 →
      PhiM μ (z + t • (Matrix.single a a 1 * z)) = (1 + t) ^ (-μ a) * PhiM μ z := by
    intro t ht
    have hc : IsLowerTri (1 + t • Matrix.single a a (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ a = j) := fun ⟨h1, h2⟩ => hij.ne (h1.symm.trans h2)
      simp [Matrix.one_apply_ne hij.ne, Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ hc isUpperTri_one
      (fun l => by rw [diag_line]; split_ifs <;> simp [ht]) (fun l => by simp) hz
    have e : (1 + t • Matrix.single a a (1 : ℂ)) * z * 1 = z + t • (Matrix.single a a 1 * z) := by
      rw [Matrix.mul_one, add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← e, h]
    congr 1
    simp only [Matrix.one_apply_eq, mul_one, diag_line]
    exact diag_prod μ a t
  have hev : (fun t : ℂ => PhiM μ (z + t • (Matrix.single a a 1 * z))) =ᶠ[nhds 0]
      fun t => (1 + t) ^ (-μ a) * PhiM μ z := by
    filter_upwards [eventually_ne_line] with t ht using key t ht
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (Matrix.single a a 1 * z)
  exact hd.unique ((hasDerivAt_scale μ a _).congr_of_eventuallyEq hev)

theorem lhol_lhol_phiM (μ : Fin n → ℤ) (a b : Fin n) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) z =
      ((casCoef μ a b : ℝ) : ℂ) * PhiM μ z := by
  have hO : IsOpen (OmegaSet n) := isOpen_omega
  have hlow : ∀ a b : Fin n, b < a →
      Lhol (Matrix.single b a 1) (Lhol (Matrix.single a b 1) (PhiM μ)) z = 0 := by
    intro a b hab
    have hev : Lhol (Matrix.single a b (1 : ℂ)) (PhiM μ) =ᶠ[nhds z] fun _ => (0 : ℂ) := by
      filter_upwards [hO.mem_nhds hz] with w hw using lhol_phiM_lower μ hab hw
    show fderiv ℂ (Lhol (Matrix.single a b (1 : ℂ)) (PhiM μ)) z _ = 0
    rw [hev.fderiv_eq]
    simp
  have e1 := lhol_phiM_diag μ a hz
  have e2 := lhol_phiM_diag μ b hz
  unfold Lhol at e1 e2
  rcases lt_trichotomy a b with h | rfl | h
  · rw [hlow b a h, casCoef, if_neg h.ne, if_neg (not_lt.mpr h.le)]
    simp
  · have hev : Lhol (Matrix.single a a (1 : ℂ)) (PhiM μ) =ᶠ[nhds z] fun w => -(μ a : ℂ) * PhiM μ w := by
      filter_upwards [hO.mem_nhds hz] with w hw using lhol_phiM_diag μ a hw
    have hf : fderiv ℂ (fun w => -(μ a : ℂ) * PhiM μ w) z = -(μ a : ℂ) • fderiv ℂ (PhiM μ) z :=
      ((differentiableAt_phiM μ hz).hasFDerivAt.const_mul (-(μ a : ℂ))).fderiv
    show fderiv ℂ (Lhol (Matrix.single a a (1 : ℂ)) (PhiM μ)) z _ = _
    rw [hev.fderiv_eq]
    erw [hf]
    rw [_root_.smul_apply, smul_eq_mul, e1, casCoef, if_pos rfl, if_neg (lt_irrefl a)]
    push_cast
    ring
  · rw [lhol_comm (contDiffAt_phiM μ hz) _ _, hlow a b h]
    simp only [Matrix.single_mul_single_same, mul_one, sub_mul, map_sub]
    rw [e1, e2, casCoef, if_neg h.ne', if_pos h]
    push_cast
    ring

theorem casL_phiM (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : casL (PhiM μ) z = ((casVal lam : ℝ) : ℂ) * PhiM μ z := by
  show ∑ a, ∑ b, Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) z = _
  simp only [lhol_lhol_phiM μ _ _ hz, ← Finset.sum_mul]
  rw [← sum_casCoef μ lam hμ]
  push_cast
  rfl

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousConjProjection
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

private lemma toMatrix_mul_alt (a b : KG ε) : toMK (a * b) = toMK a * toMK b := rfl

private lemma toMatrix_one_alt : toMK (1 : KG ε) = 1 := rfl

private lemma toMatrix_inv_mul (a : KG ε) : toMK a⁻¹ * toMK a = 1 := by
  rw [← toMatrix_mul_alt, inv_mul_cancel, toMatrix_one_alt]

private lemma toMatrix_mul_inv (a : KG ε) : toMK a * toMK a⁻¹ = 1 := by
  rw [← toMatrix_mul_alt, mul_inv_cancel, toMatrix_one_alt]

private lemma kType_op_mul (T : KType ε Λ) (a b : KG ε) : T.op (a * b) = T.op a * T.op b := by
  unfold KType.op
  rw [map_mul]
  rfl

private lemma kType_op_one (T : KType ε Λ) : T.op 1 = 1 := by
  unfold KType.op
  rw [map_one]
  rfl

private lemma kType_op_mul_inv (T : KType ε Λ) (a : KG ε) : T.op a * T.op a⁻¹ = 1 := by
  rw [← kType_op_mul, mul_inv_cancel, kType_op_one]

private lemma kType_op_inv_mul (T : KType ε Λ) (a : KG ε) : T.op a⁻¹ * T.op a = 1 := by
  rw [← kType_op_mul, inv_mul_cancel, kType_op_one]

private def ps2E (T : KType ε Λ) (k : KG ε) : T.V ≃L[ℂ] T.V :=
  ContinuousLinearEquiv.equivOfInverse (T.op k) (T.op k⁻¹)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (kType_op_inv_mul T k)
      simpa using this)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (kType_op_mul_inv T k)
      simpa using this)

private def ps2C (T : KType ε Λ) (k : KG ε) : (T.V →L[ℂ] T.V) ≃L[ℂ] (T.V →L[ℂ] T.V) :=
  (ps2E T k).arrowCongr (ps2E T k)

private lemma conjAction_apply (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    ps2C T k A = T.op k * A * T.op k⁻¹ := by
  ext v
  rfl

private lemma kType_schur_lemma (T : KType ε Λ) (A : T.V →L[ℂ] T.V) (hA : ∀ k, T.op k * A = A * T.op k) :
    ∃ c : ℂ, A = c • (1 : T.V →L[ℂ] T.V) := by
  have hw : T.w ≠ 0 := fun h => by
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  haveI : Nontrivial T.V := ⟨⟨T.w, 0, hw⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (A : Module.End ℂ T.V)
  refine ⟨c, ?_⟩
  have key : ∀ k v, A (T.op k v) = T.op k (A v) := fun k v => by
    have := congrArg (fun B : T.V →L[ℂ] T.V => B v) (hA k)
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this.symm
  have hinv : ∀ k : KG ε, ∀ v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c,
      ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈
        Module.End.eigenspace (A : Module.End ℂ T.V) c := by
    intro k v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    change A (T.op k v) = c • T.op k v
    rw [key, show A v = c • v from hv, map_smul]
  rcases T.irred _ hinv with h | h
  · exfalso
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hv1 : v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c := by
      rw [Module.End.mem_eigenspace_iff]
      exact hv.apply_eq_smul
    rw [h] at hv1
    exact hv.2 ((Submodule.mem_bot ℂ).1 hv1)
  · ext v
    have hv : v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c := by
      rw [h]
      exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    simpa using hv

private lemma continuous_kType_op (T : KType ε Λ) : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont

private lemma continuous_conj_projection (T : KType ε Λ) :
    Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ := ((continuous_kType_op T).mul continuous_const).mul ((continuous_kType_op T).comp continuous_inv)

private lemma integral_conj_equivariant (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) (x : Matrix (Fin n) (Fin n) ℂ) :
    ∫ k', PhiM μ (toMK k'⁻¹ * (toMK k * x * toMK k⁻¹) * toMK k') • (T.op k' * projW T * T.op k'⁻¹) ∂(muK ε) =
      ps2C T k (∫ k', PhiM μ (toMK k'⁻¹ * x * toMK k') • (T.op k' * projW T * T.op k'⁻¹) ∂(muK ε)) := by
  haveI : (muK ε).IsMulLeftInvariant := by
    unfold muK
    infer_instance
  rw [← ContinuousLinearEquiv.integral_comp_comm (ps2C T k)]
  calc _ = ∫ k', PhiM μ (toMK (k * k')⁻¹ * (toMK k * x * toMK k⁻¹) * toMK (k * k')) •
        (T.op (k * k') * projW T * T.op (k * k')⁻¹) ∂(muK ε) :=
        (MeasureTheory.integral_mul_left_eq_self (fun k' => PhiM μ (toMK k'⁻¹ * (toMK k * x * toMK k⁻¹) *
          toMK k') • (T.op k' * projW T * T.op k'⁻¹)) k).symm
    _ = _ := by
        congr 1
        funext k'
        rw [map_smul, conjAction_apply]
        congr 1
        · congr 1
          rw [_root_.mul_inv_rev, toMatrix_mul_alt, toMatrix_mul_alt]
          calc _ = toMK k'⁻¹ * (toMK k⁻¹ * toMK k) * x * (toMK k⁻¹ * toMK k) * toMK k' := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [toMatrix_inv_mul, Matrix.mul_one, Matrix.mul_one]
        · rw [_root_.mul_inv_rev, kType_op_mul, kType_op_mul]
          simp only [mul_assoc]

theorem psM_conj (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) (x : Matrix (Fin n) (Fin n) ℂ) :
    psM T μ (toMK k * x * toMK k⁻¹) = T.op k * psM T μ x * T.op k⁻¹ := by
  simp only [psM]
  rw [integral_conj_equivariant, conjAction_apply, mul_smul_comm, smul_mul_assoc]

theorem psM_one (T : KType ε Λ) (μ : Fin n → ℤ) : psM T μ 1 = 1 := by
  have hw : T.w ≠ 0 := fun h => by
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  haveI : Nontrivial T.V := ⟨⟨T.w, 0, hw⟩⟩
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  haveI : IsFiniteMeasureOnCompacts (muK ε) := by
    unfold muK
    infer_instance
  have hPhi1 : PhiM μ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    unfold PhiM
    refine Finset.prod_eq_one fun i _ => ?_
    unfold lead
    rw [dite_eq_left (by have := i.isLt; omega), Matrix.submatrix_one _ (Fin.castLE_injective _),
      Matrix.det_one, _root_.one_zpow]
  have hcomm : ∀ k : KG ε, T.op k * psM T μ 1 = psM T μ 1 * T.op k := by
    intro k
    have h := psM_conj T μ k 1
    rw [Matrix.mul_one, toMatrix_mul_inv] at h
    calc T.op k * psM T μ 1 = T.op k * psM T μ 1 * (T.op k⁻¹ * T.op k) := by
          rw [kType_op_inv_mul, mul_one]
      _ = T.op k * psM T μ 1 * T.op k⁻¹ * T.op k := by simp only [mul_assoc]
      _ = psM T μ 1 * T.op k := by rw [← h]
  obtain ⟨c, hc⟩ := kType_schur_lemma T (psM T μ 1) hcomm
  obtain ⟨tr, htr⟩ : ∃ tr : (T.V →L[ℂ] T.V) →L[ℂ] ℂ,
      ∀ A, tr A = LinearMap.trace ℂ T.V (A : T.V →ₗ[ℂ] T.V) :=
    ⟨LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ T.V).comp (ContinuousLinearMap.coeLM ℂ)),
      fun A => rfl⟩
  have hP : LinearMap.trace ℂ T.V (projW T : T.V →ₗ[ℂ] T.V) = 1 := by
    have e2 : (projW T : T.V →ₗ[ℂ] T.V) =
        ((innerSL ℂ T.w : T.V →L[ℂ] ℂ) : T.V →ₗ[ℂ] ℂ).smulRight T.w := LinearMap.ext fun v => rfl
    rw [e2, LinearMap.trace_smulRight]
    simp [inner_self_eq_norm_sq_to_K, T.w_norm]
  have htrk : ∀ k, tr (T.op k * projW T * T.op k⁻¹) = 1 := by
    intro k
    rw [htr]
    have e1 : ((T.op k * projW T * T.op k⁻¹ : T.V →L[ℂ] T.V) : T.V →ₗ[ℂ] T.V) =
        (ps2E T k).toLinearEquiv.conj (projW T : T.V →ₗ[ℂ] T.V) := LinearMap.ext fun v => rfl
    rw [e1, LinearMap.trace_conj', hP]
  have hint : Integrable (fun k : KG ε => T.op k * projW T * T.op k⁻¹) (muK ε) :=
    (continuous_conj_projection T).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have hv : ((muK ε Set.univ).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (muK_univ_pos ε).ne'
  have hd : (Module.finrank ℂ T.V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h1 : tr (psM T μ 1) = c * (Module.finrank ℂ T.V : ℂ) := by
    rw [htr, hc]
    simp [LinearMap.trace_one]
  have hI : psM T μ 1 = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
      ∫ k, (T.op k * projW T * T.op k⁻¹) ∂(muK ε) := by
    simp only [psM]
    congr 1
    congr 1
    funext k
    rw [Matrix.mul_one, toMatrix_inv_mul, hPhi1, one_smul]
  have h2 : tr (psM T μ 1) = (Module.finrank ℂ T.V : ℂ) := by
    rw [hI, map_smul, ← ContinuousLinearMap.integral_comp_comm tr hint]
    simp only [htrk, integral_const, smul_eq_mul, Complex.real_smul, mul_one]
    exact div_mul_cancel₀ _ hv
  have hc1 : c = 1 := by
    have := h1.symm.trans h2
    exact mul_right_cancel₀ hd (this.trans (one_mul _).symm)
  rw [hc, hc1, one_smul]

private def ps2J (ε : Fin n → Bool) : KG ε :=
  ⟨⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, by
      show (Jm ε)ᴴ * Jm ε * Jm ε = Jm ε
      rw [Jm_conjTranspose, Jm_mul_self, Matrix.one_mul]⟩,
    by
      show Jm ε ∈ Kset ε
      refine ⟨?_, rfl⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Jm_conjTranspose, Jm_mul_self]⟩

private lemma toMatrix_signElement : toMK (ps2J ε) = Jm ε := rfl

private lemma signElement_inv : (ps2J ε)⁻¹ = ps2J ε := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show Jm ε * Jm ε = 1
  exact Jm_mul_self ε

private lemma signElement_central (k : KG ε) : ps2J ε * k = k * ps2J ε := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show Jm ε * toMK k = toMK k * Jm ε
  exact (show toMK k ∈ Kset ε from k.2).2.symm

theorem psM_exp_neg (T : KType ε Λ) (μ : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    psM T μ (NormedSpace.exp (-X)) = psM T μ (NormedSpace.exp X) := by
  have hJ : Jm ε * X * Jm ε = -X := by
    calc Jm ε * X * Jm ε = Jm ε * (X * Jm ε) := Matrix.mul_assoc _ _ _
      _ = Jm ε * -(Jm ε * X) := by rw [hX.2]
      _ = -X := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_self ε)
  have hU : IsUnit (Jm ε) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse (Jm_mul_self ε))
  have hE := Matrix.exp_conj (Jm ε) X hU
  rw [hinv, hJ] at hE
  have hE' : NormedSpace.exp (-X) = toMK (ps2J ε) * NormedSpace.exp X * toMK (ps2J ε)⁻¹ := by
    rw [signElement_inv, toMatrix_signElement]
    exact hE
  rw [hE', psM_conj]
  obtain ⟨c, hc⟩ := kType_schur_lemma T (T.op (ps2J ε)) (fun k => by
    rw [← kType_op_mul, ← kType_op_mul, signElement_central])
  have hm := kType_op_mul_inv T (ps2J ε)
  rw [hc] at hm ⊢
  calc c • (1 : T.V →L[ℂ] T.V) * psM T μ (NormedSpace.exp X) * T.op (ps2J ε)⁻¹ =
        psM T μ (NormedSpace.exp X) * (c • (1 : T.V →L[ℂ] T.V) * T.op (ps2J ε)⁻¹) := by
        simp only [smul_mul_assoc, one_mul, mul_smul_comm]
    _ = psM T μ (NormedSpace.exp X) := by rw [hm, mul_one]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DerivG
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_Gint {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y)
    (γ : ℝ → KG ε) (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) :
    HasDerivAt (fun t => Gint T μ x (k * γ t))
      (fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k)
          (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k)) •
          (T.op k * projW T * T.op k⁻¹) +
        PhiM μ (toMK k⁻¹ * x * toMK k) •
          (T.op k * (T.dτ Y * projW T - projW T * T.dτ Y) * T.op k⁻¹)) 0 := by
  have hm : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := by
    intro a b
    simp [toMK, toM]
  have hi : ∀ a : KG ε, toMK a⁻¹ * toMK a = 1 := by
    intro a
    simp [toMK, toM]
  have hop : ∀ a b : KG ε, T.op (a * b) = T.op a * T.op b := by
    intro a b
    simp [KType.op]
  have hop1 : ∀ a : KG ε, T.op a⁻¹ * T.op a = 1 := by
    intro a
    simp only [KType.op, map_inv]
    rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
  have hγ0 : γ 0 = 1 := by
    ext i j
    have h00 := congrFun (congrFun (hγ 0) i) j
    simpa [toMK, toM] using h00
  have hk2 : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ toMK k * Jm ε = Jm ε * toMK k := by
    simpa [KG, Kset, toM, toMK] using k.2
  have hst : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk2.1
  have hst' : toMK k * star (toMK k) = 1 := Matrix.mem_unitaryGroup_iff.1 hk2.1
  have hkinv : toMK k⁻¹ = (toMK k)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * star (toMK k)) := by rw [hst', mul_one]
      _ = (toMK k⁻¹ * toMK k) * star (toMK k) := by rw [mul_assoc]
      _ = star (toMK k) := by rw [hi, one_mul]
  have hinjk : Function.Injective (toMK k).mulVec := by
    intro v w hvw
    have h2 := congrArg (star (toMK k)).mulVec hvw
    simpa [Matrix.mulVec_mulVec, hst] using h2
  have hzP : toMK k⁻¹ * x * toMK k ∈ OmegaSet n := by
    apply posSet_subset_omega
    show (toMK k⁻¹ * x * toMK k).PosDef
    rw [hkinv]
    exact hx.conjTranspose_mul_mul_same hinjk
  have hexp : ∀ A : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
    intro A
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl A)), add_neg_cancel,
      NormedSpace.exp_zero]
  have hinvγ : ∀ t : ℝ, toMK (γ t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Y)) := by
    intro t
    calc toMK (γ t)⁻¹
        = toMK (γ t)⁻¹ * (NormedSpace.exp ((t : ℂ) • Y) * NormedSpace.exp (-((t : ℂ) • Y))) := by
          rw [hexp, mul_one]
      _ = (toMK (γ t)⁻¹ * toMK (γ t)) * NormedSpace.exp (-((t : ℂ) • Y)) := by
          rw [hγ t, mul_assoc]
      _ = _ := by rw [hi, one_mul]
  have hf : ∀ t : ℝ, toMK (k * γ t)⁻¹ * x * toMK (k * γ t) =
      NormedSpace.exp (-((t : ℂ) • Y)) * (toMK k⁻¹ * x * toMK k) * NormedSpace.exp ((t : ℂ) • Y) := by
    intro t
    rw [_root_.mul_inv_rev, hm, hm, hinvγ, hγ]
    simp only [mul_assoc]
  have hQe : ∀ t : ℝ, T.op (1 * (γ t)⁻¹) * T.op k⁻¹ = T.op (k * γ t)⁻¹ := by
    intro t
    rw [one_mul, _root_.mul_inv_rev, hop]
  have hfun : (fun t : ℝ => Gint T μ x (k * γ t)) = fun t : ℝ =>
      PhiM μ (NormedSpace.exp (-((t : ℂ) • Y)) * (toMK k⁻¹ * x * toMK k) *
        NormedSpace.exp ((t : ℂ) • Y)) •
        (T.op (k * γ t) * projW T * (T.op (1 * (γ t)⁻¹) * T.op k⁻¹)) := by
    funext t
    simp only [Gint]
    rw [hf t, hQe t]
  have hP := hasDerivAt_op T k hY γ hγ
  have hδ : ∀ t : ℝ, toMK ((fun s : ℝ => (γ s)⁻¹) t) = NormedSpace.exp ((t : ℂ) • (-Y)) := by
    intro t
    rw [smul_neg]
    exact hinvγ t
  have hQ := (hasDerivAt_op T 1 (inK_neg hY) (fun s : ℝ => (γ s)⁻¹) hδ).mul_const (T.op k⁻¹)
  have hM := (hP.mul_const (projW T)).mul hQ
  have hφ : HasDerivAt (fun t : ℝ => PhiM μ (NormedSpace.exp (-((t : ℂ) • Y)) *
      (toMK k⁻¹ * x * toMK k) * NormedSpace.exp ((t : ℂ) • Y)))
      (fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k)
        (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k))) 0 := by
    have hd := ((phiM_differentiableOn μ).differentiableAt (isOpen_omega.mem_nhds hzP)).hasFDerivAt
    have h0 : toMK k⁻¹ * x * toMK k = NormedSpace.exp (-(((0 : ℝ) : ℂ) • Y)) *
        (toMK k⁻¹ * x * toMK k) * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) := by
      simp
    exact (hd.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) (dga_path Y _) h0
  have hop1' : T.op 1 = 1 := by simp [KType.op]
  rw [hfun]
  convert hφ.smul hM using 1
  all_goals try rfl
  simp only [hγ0, mul_one, one_mul, inv_one, hop1', map_neg, Complex.ofReal_zero, zero_smul,
    neg_zero, NormedSpace.exp_zero]
  rw [add_comm]
  simp only [Pi.mul_apply, hγ0, mul_one, inv_one, hop1', one_mul]
  refine congrArg₂ (· + ·) (congrArg _ ?_) rfl
  noncomm_ring
end ReciprocityTheory.ChartRestriction.DS.S7
end
end
