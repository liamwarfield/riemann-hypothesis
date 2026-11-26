module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodPolynomialLimitAtCusp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitPolyOfPeriodicSlashFamilyConst
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitPolyOfPeriodicSlashFamilyConst
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.QConst

open Filter Topology

private theorem natDegree_lt_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) :
    p.natDegree < w + 1 := by
  rcases eq_or_ne p 0 with rfl | h
  · simp
  · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)

private theorem norm_eval_le_sum_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (x : ℂ) : ‖p.eval x‖ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j‖ * ‖x‖ ^ j := by
  rw [eval_eq_sum_range' (natDegree_lt_of_mem_degreeLT hp)]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [norm_mul, norm_pow]

private theorem eq_C_of_eval_add_natCast_eq {Q : ℂ[X]} {n : ℕ} (hn : 0 < n)
    (hQ : ∀ x : ℂ, Q.eval (x + n) = Q.eval x) : Q = C (Q.coeff 0) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hroot : ∀ k : ℕ, IsRoot (Q - C (Q.eval 0)) ((k : ℂ) * n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : ((k + 1 : ℕ) : ℂ) * n = (k : ℂ) * n + n := by push_cast; ring
      simp only [IsRoot.def, eval_sub, eval_C] at ih ⊢
      rw [hk, hQ]
      exact ih
  have hinf : Set.Infinite {x | IsRoot (Q - C (Q.eval 0)) x} :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ) * n)
      (fun a b hab => by exact_mod_cast mul_right_cancel₀ hn' hab) hroot
  rw [coeff_zero_eq_eval_zero]
  exact sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)

private theorem tendsto_exp_neg_mul_mul_add_pow_zero {c : ℝ} (hc : 0 < c) (b : ℝ) (m : ℕ) :
    Tendsto (fun y : ℝ => Real.exp (-c * y) * (b + y) ^ m) atTop (𝓝 0) := by
  have h1 := ((isLittleO_pow_exp_pos_mul_atTop m hc).comp_tendsto
    (tendsto_atTop_add_const_left atTop b tendsto_id)).tendsto_div_nhds_zero
  have h2 := h1.const_mul (Real.exp (c * b))
  rw [mul_zero] at h2
  refine h2.congr fun y => ?_
  simp only [Function.comp_apply, id]
  rw [mul_add, Real.exp_add, neg_mul, Real.exp_neg]
  field_simp

theorem _root_.GlobalTheory.HeckeFamilyMatrices.QConst.qconst : ∀ (w n : ℕ) (V : ℍ → ℂ[X]) (Q : ℂ[X]) (C' c : ℝ), 0 < n → 0 < c → Q ∈ degreeLT ℂ (w + 1) →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    Q = C (Q.coeff 0) := by
  intro w n V Q C' c hn hc hQ hV hper h
  have hT : _root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := by
    unfold _root_.GlobalTheory.HeckeFamilyMatrices.mat
    exact ModularGroup.coe_T_zpow _
  have htrans : ∀ (τ : ℍ) (x : ℂ),
      (V τ).eval x = (V (ModularGroup.T ^ (n : ℤ) • τ)).eval (x + n) := by
    intro τ x
    rw [← hper τ, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ x (hV _) (by rw [hT]; simp), hT]
    simp
  have hbound : ∀ τ : ℍ, 1 ≤ τ.im → ∀ b : ℝ, 1 + ‖(τ : ℂ)‖ ≤ b → ∀ x : ℂ,
      ‖(V τ - Q).eval x‖ ≤ C' * Real.exp (-c * τ.im) * b ^ w *
        ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j := by
    intro τ hτ b hb x
    have hC' : 0 ≤ C' := by
      have h0 := h τ hτ 0 (Nat.zero_le _)
      have : 0 < Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by positivity
      nlinarith [norm_nonneg ((V τ - Q).coeff 0)]
    rw [Finset.mul_sum]
    refine (norm_eval_le_sum_of_mem_degreeLT (Submodule.sub_mem _ (hV τ) hQ) x).trans
      (Finset.sum_le_sum fun j hj => ?_)
    have hj' : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact mul_le_mul_of_nonneg_right ((h τ hτ j hj').trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb w)
        (mul_nonneg hC' (Real.exp_pos _).le))) (by positivity)
  refine eq_C_of_eval_add_natCast_eq hn fun x => ?_
  set M : ℝ := ∑ j ∈ Finset.range (w + 1), ‖x + n‖ ^ j + ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j
  have hest : ∀ y : ℝ, 1 ≤ y → ‖Q.eval (x + n) - Q.eval x‖ ≤
      C' * M * (Real.exp (-c * y) * ((1 + n) + y) ^ w) := by
    intro y hy
    let τ : ℍ := ⟨(y : ℂ) * Complex.I, by simp; linarith⟩
    have hτim : τ.im = y := by simp [τ, UpperHalfPlane.im]
    have hτn : ‖(τ : ℂ)‖ = y := by
      simp [τ, abs_of_pos (show (0 : ℝ) < y by linarith)]
    have hτ'c : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = τ + n := by
      rw [ModularGroup.coe_T_zpow_smul_eq]
      simp
    have hτ'im : (ModularGroup.T ^ (n : ℤ) • τ).im = y := by
      rw [← hτim, ← UpperHalfPlane.coe_im, hτ'c, ← UpperHalfPlane.coe_im]
      simp
    have hτ'n : 1 + ‖((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ)‖ ≤ (1 + n) + y := by
      rw [hτ'c]
      have := norm_add_le (τ : ℂ) (n : ℂ)
      rw [hτn, Complex.norm_natCast] at this
      linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 := hbound τ (by rw [hτim]; exact hy) ((1 + n) + y) (by rw [hτn]; linarith) x
    have e2 := hbound _ (by rw [hτ'im]; exact hy) ((1 + n) + y) hτ'n (x + n)
    rw [hτim] at e1
    rw [hτ'im] at e2
    have hsplit : Q.eval (x + n) - Q.eval x =
        (V τ - Q).eval x - (V (ModularGroup.T ^ (n : ℤ) • τ) - Q).eval (x + n) := by
      simp only [eval_sub, htrans τ x]
      ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    simp only [M]
    ring
  have hlim := (tendsto_exp_neg_mul_mul_add_pow_zero hc (1 + n) w).const_mul (C' * M)
  rw [mul_zero] at hlim
  have hle : ‖Q.eval (x + n) - Q.eval x‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hest⟩)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

end GlobalTheory.HeckeFamilyMatrices.QConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitPolyOfPeriodicSlashFamilyConstStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_poly_of_periodic_slash_family_const : ∀ (w n : ℕ) (V : ℍ → ℂ[X]) (Q : ℂ[X]) (C' c : ℝ), 0 < n → 0 < c → Q ∈ degreeLT ℂ (w + 1) → (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) → Q = C (Q.coeff 0) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.QConst.qconst | exact GlobalTheory.HeckeFamilyMatrices.QConst.qconst | (intros; apply GlobalTheory.HeckeFamilyMatrices.QConst.qconst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEvalSmulMulImRpowPolyDegreeSlash
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEvalSmulMulImRpowPolyDegreeSlash
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem norm_eval_smul_mul_im_rpow : ∀ (w : ℕ) (σ : SL(2, ℤ)) (P : ℂ[X]) (τ : ℍ), P ∈ degreeLT ℂ (w + 1) → ‖P.eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-(w : ℝ) / 2) = ‖(slP w (mat σ) P).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
  intro w σ P τ hP
  have hden : denom σ τ = ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) := by
    rw [ModularGroup.denom_apply]
  have hj : ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have hc : ((σ • τ : ℍ) : ℂ) = (((mat σ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 0 1 : ℤ) : ℂ)) /
      (((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ)) := by
    rw [specialLinearGroup_apply]
    simp
  have him := ModularGroup.im_smul_eq_div_normSq σ τ
  rw [hden] at him
  rw [eval_polySlash w (mat σ) P τ hP hj, ← hc, him]
  set j := ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) with hjdef
  have hn : 0 < ‖j‖ := norm_pos_iff.2 hj
  have hτ : 0 < τ.im := τ.im_pos
  rw [Complex.normSq_eq_norm_sq, Real.div_rpow hτ.le (by positivity), norm_mul, norm_pow]
  have h2 : (‖j‖ ^ 2) ^ (-(w : ℝ) / 2) = (‖j‖ ^ w)⁻¹ := by
    rw [← Real.rpow_natCast ‖j‖ 2, ← Real.rpow_mul hn.le, ← Real.rpow_natCast ‖j‖ w,
      ← Real.rpow_neg hn.le]
    congr 1
    push_cast
    ring
  rw [h2, div_inv_eq_mul]
  ring

end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEvalSmulMulImRpowPolyDegreeSlashStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eval_smul_mul_im_rpow_polyDegreeSlash : ∀ (w : ℕ) (σ : SL(2, ℤ)) (P : ℂ[X]) (τ : ℍ), P ∈ degreeLT ℂ (w + 1) → ‖P.eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-(w : ℝ) / 2) = ‖(slP w (mat σ) P).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow | exact GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow | (intros; apply GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalDiagPolyValuedInvariantTranslationTZpowMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalDiagPolyValuedInvariantTranslationTZpowMul
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem evalDiag_T_step (w n : ℕ) (V : ℍ → ℂ[X]) (hV : ∀ τ, V τ ∈ degreeLT ℂ (w + 1))
    (hT : ∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ)
    (τ : ℍ) :
    (V (ModularGroup.T ^ (n : ℤ) • τ)).eval ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  have hm : mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := ModularGroup.coe_T_zpow _
  have hc : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (τ : ℂ) + n := by
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
    push_cast; ring
  rw [← hT τ, eval_polySlash w _ _ _ (hV _), hm, hc]
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    simp
  · rw [hm]
    simp

theorem evalDiag_T_invariant : ∀ (w n : ℕ) (V : ℍ → ℂ[X]), (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → ∀ (m : ℤ) (τ : ℍ), (V (ModularGroup.T ^ ((n : ℤ) * m) • τ)).eval ((ModularGroup.T ^ ((n : ℤ) * m) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  intro w n V hV hT m
  have step := evalDiag_T_step w n V hV hT
  simp only [zpow_mul]
  induction m using Int.induction_on with
  | zero => intro τ; simp
  | succ k ih =>
    intro τ
    rw [zpow_add_one, mul_smul, ih, step]
  | pred k ih =>
    intro τ
    have e : (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ) - 1) • τ =
        (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ)) • ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ) := by
      rw [zpow_sub_one, mul_smul]
    rw [e, ih, ← step ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ), smul_inv_smul]

end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalDiagPolyValuedInvariantTranslationTZpowMulStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalDiag_polyValued_invariant_translation_T_zpow_mul : ∀ (w n : ℕ) (V : ℍ → ℂ[X]), (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → ∀ (m : ℤ) (τ : ℍ), (V (ModularGroup.T ^ ((n : ℤ) * m) • τ)).eval ((ModularGroup.T ^ ((n : ℤ) * m) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant | exact GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant | (intros; apply GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripEvalPolynomialDecayMulImRpow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripEvalPolynomialDecayMulImRpow
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

open Filter Topology

private lemma norm_eval_add_C_le_of_coeff_le (w : ℕ) (a z : ℂ) (p : ℂ[X]) (K e : ℝ) (hK : 0 ≤ K)
    (he : 0 ≤ e) (hp : p ∈ degreeLT ℂ (w + 1))
    (hc : ∀ j ≤ w, ‖p.coeff j‖ ≤ K * e * (1 + ‖z‖) ^ w) :
    ‖(p + C a).eval z‖ ≤ ‖a‖ + (w + 1) * (K * e * (1 + ‖z‖) ^ (2 * w)) := by
  have hdeg : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hp)
  rw [eval_add, eval_C, eval_eq_sum_range' hdeg]
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hterm : ∀ j ∈ Finset.range (w + 1),
      ‖p.coeff j * z ^ j‖ ≤ K * e * (1 + ‖z‖) ^ (2 * w) := by
    intro j hj
    have hjw : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [norm_mul, norm_pow]
    have h1 : ‖z‖ ^ j ≤ (1 + ‖z‖) ^ w :=
      (pow_le_pow_left₀ (norm_nonneg z) (by linarith) j).trans (pow_le_pow_right₀ hz1 hjw)
    calc ‖p.coeff j‖ * ‖z‖ ^ j ≤ (K * e * (1 + ‖z‖) ^ w) * (1 + ‖z‖) ^ w :=
          mul_le_mul (hc j hjw) h1 (by positivity) (by positivity)
      _ = K * e * (1 + ‖z‖) ^ (2 * w) := by ring
  calc ‖∑ j ∈ Finset.range (w + 1), p.coeff j * z ^ j + a‖
      ≤ ‖∑ j ∈ Finset.range (w + 1), p.coeff j * z ^ j‖ + ‖a‖ := norm_add_le _ _
    _ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j * z ^ j‖ + ‖a‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (w + 1), K * e * (1 + ‖z‖) ^ (2 * w) + ‖a‖ := by
        gcongr with j hj; exact hterm j hj
    _ = ‖a‖ + (w + 1) * (K * e * (1 + ‖z‖) ^ (2 * w)) := by simp; ring

theorem strip_eval_decay : ∀ (w n : ℕ) (a : ℂ) (V : ℍ → ℂ[X]) (C' c : ℝ), 1 ≤ w → 0 < c →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    ∀ ε > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → 0 ≤ τ.re → τ.re ≤ n →
      ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) < ε := by
  intro w n a V C' c hw hc hV hcoef ε hε
  set K := max C' 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  have hwpos : (0 : ℝ) < (w : ℝ) / 2 := by
    have : (1 : ℝ) ≤ w := by exact_mod_cast hw
    linarith
  have h1 : Tendsto (fun y : ℝ => ‖a‖ * y ^ (-(w : ℝ) / 2)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hwpos).const_mul ‖a‖
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun y => ?_)
    simp only [neg_div]
  have h2 : Tendsto (fun y : ℝ => (w + 1) * (K * 4 ^ w) * (y ^ (2 * w) / Real.exp (c * y)))
      atTop (𝓝 0) := by
    have := ((isLittleO_pow_exp_pos_mul_atTop (2 * w) hc).tendsto_div_nhds_zero).const_mul
      ((w + 1) * (K * 4 ^ w))
    rwa [mul_zero] at this
  have e1 := h1.eventually (gt_mem_nhds (half_pos hε))
  have e2 := h2.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨A0, hA0⟩ := eventually_atTop.1 (e1.and e2)
  refine ⟨max A0 (1 + n), fun τ hA hre hren => ?_⟩
  have hpos : 0 < τ.im := τ.im_pos
  have hy0 : A0 ≤ τ.im := le_trans (le_max_left _ _) hA
  have hyn : 1 + (n : ℝ) ≤ τ.im := le_trans (le_max_right _ _) hA
  have hy1 : 1 ≤ τ.im := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨hf1, hf2⟩ := hA0 τ.im hy0
  have hz : ‖(τ : ℂ)‖ ≤ n + τ.im := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hr : |(τ : ℂ).re| ≤ n := by
      rw [UpperHalfPlane.coe_re, abs_of_nonneg hre]; exact hren
    have hi : |(τ : ℂ).im| = τ.im := by
      rw [UpperHalfPlane.coe_im, abs_of_pos hpos]
    linarith
  have hcb : ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ K * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
    intro j hj
    refine (hcoef τ hy1 j hj).trans ?_
    gcongr
    exact le_max_left _ _
  have hmem : V τ - C a ∈ degreeLT ℂ (w + 1) :=
    Submodule.sub_mem _ (hV τ)
      (mem_degreeLT.2 (lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos w)))
  have hmain := norm_eval_add_C_le_of_coeff_le w a (τ : ℂ) (V τ - C a) K (Real.exp (-c * τ.im)) hK
    (Real.exp_pos _).le hmem hcb
  rw [sub_add_cancel] at hmain
  have hnz : 1 + ‖(τ : ℂ)‖ ≤ 2 * τ.im := by linarith
  have hpow : (1 + ‖(τ : ℂ)‖) ^ (2 * w) ≤ 4 ^ w * τ.im ^ (2 * w) := by
    calc (1 + ‖(τ : ℂ)‖) ^ (2 * w) ≤ (2 * τ.im) ^ (2 * w) :=
          pow_le_pow_left₀ (by positivity) hnz _
      _ = 4 ^ w * τ.im ^ (2 * w) := by rw [mul_pow, pow_mul]; norm_num
  have hT : (w + 1) * (K * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (2 * w))
      ≤ (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
    rw [neg_mul, Real.exp_neg]
    calc (w + 1) * (K * (Real.exp (c * τ.im))⁻¹ * (1 + ‖(τ : ℂ)‖) ^ (2 * w))
        ≤ (w + 1) * (K * (Real.exp (c * τ.im))⁻¹ * (4 ^ w * τ.im ^ (2 * w))) := by gcongr
      _ = (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
        rw [div_eq_mul_inv]; ring
  have hT0 : 0 ≤ (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by positivity
  have hr0 : 0 ≤ τ.im ^ (-(w : ℝ) / 2) := Real.rpow_nonneg hpos.le _
  have hr1 : τ.im ^ (-(w : ℝ) / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hy1 ?_
    have : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    linarith
  calc ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2)
      ≤ (‖a‖ + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)))
          * τ.im ^ (-(w : ℝ) / 2) := by gcongr; linarith
    _ = ‖a‖ * τ.im ^ (-(w : ℝ) / 2)
          + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im))
            * τ.im ^ (-(w : ℝ) / 2) := by ring
    _ ≤ ‖a‖ * τ.im ^ (-(w : ℝ) / 2)
          + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
        exact add_le_add le_rfl (mul_le_of_le_one_right hT0 hr1)
    _ < ε / 2 + ε / 2 := add_lt_add hf1 hf2
    _ = ε := add_halves ε

end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripEvalPolynomialDecayMulImRpowStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strip_eval_polynomial_decay_mul_im_rpow : ∀ (w n : ℕ) (a : ℂ) (V : ℍ → ℂ[X]) (C' c : ℝ), 1 ≤ w → 0 < c → (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) → ∀ ε > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → 0 ≤ τ.re → τ.re ≤ n → ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) < ε := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.strip_eval_decay | exact GlobalTheory.HeckeFamilyMatrices.strip_eval_decay | (intros; apply GlobalTheory.HeckeFamilyMatrices.strip_eval_decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormSlashHoloDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormSlashHoloDecay
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
open scoped Manifold Pointwise

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_norm_le_exp_of_one_le_im (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] (k : ℤ)
    (g : CuspForm G k) :
    ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖g τ‖ ≤ C * Real.exp (-c * τ.im) := by
  obtain ⟨c, hc, hd⟩ := CuspFormClass.exp_decay_atImInfty' (Γ := G) (k := k) g
  obtain ⟨C₀, hC₀⟩ := CuspFormClass.petersson_bounded_left k G g g
  obtain ⟨D, hD, h⟩ := hd.exists_pos
  rw [Asymptotics.isBigOWith_iff, atImInfty, eventually_comap, eventually_atTop] at h
  obtain ⟨y, hy⟩ := h
  have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ UpperHalfPlane.I)
  set M : ℝ := 1 + C₀ * |y| ^ k.natAbs with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨max D (M * Real.exp (c * |y|)), c, hc, fun τ hτ => ?_⟩
  rcases le_total y τ.im with h1 | h1
  · have h2 := hy _ h1 τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · have hy' : τ.im ≤ |y| := h1.trans (le_abs_self y)
    have hp : ‖g τ‖ ^ 2 * τ.im ^ k ≤ C₀ := by
      have := hC₀ τ
      simp only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj, norm_zpow,
        Complex.norm_real, Real.norm_of_nonneg τ.im_pos.le] at this
      calc _ = ‖g τ‖ * ‖g τ‖ * τ.im ^ k := by ring
        _ ≤ C₀ := this
    have hpos := τ.im_pos
    have hk : 1 ≤ τ.im ^ k * τ.im ^ k.natAbs := by
      rw [← zpow_natCast, ← zpow_add₀ hpos.ne']
      exact one_le_zpow₀ hτ (by omega)
    have h4 : ‖g τ‖ ^ 2 ≤ C₀ * |y| ^ k.natAbs :=
      calc ‖g τ‖ ^ 2 ≤ ‖g τ‖ ^ 2 * (τ.im ^ k * τ.im ^ k.natAbs) :=
            le_mul_of_one_le_right (by positivity) hk
        _ = ‖g τ‖ ^ 2 * τ.im ^ k * τ.im ^ k.natAbs := by ring
        _ ≤ C₀ * |y| ^ k.natAbs := by gcongr
    have h5 : ‖g τ‖ ≤ M := by nlinarith [sq_nonneg (‖g τ‖ - 1), norm_nonneg (g τ)]
    have h3 : 1 ≤ Real.exp (c * |y|) * Real.exp (-c * τ.im) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc ‖g τ‖ ≤ M := h5
      _ ≤ M * (Real.exp (c * |y|) * Real.exp (-c * τ.im)) := le_mul_of_one_le_right hM0 h3
      _ = M * Real.exp (c * |y|) * Real.exp (-c * τ.im) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem cuspForm_slash_holo_decay : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex →
    ∀ (f : CuspForm Γ k) (σ : SL(2, ℤ)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] σ) ∧
      ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖(⇑f ∣[k] σ) τ‖ ≤ C * Real.exp (-c * τ.im) := by
  intro Γ k hΓ f σ
  have : ((ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹) • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Γ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ σ)⁻¹
  exact ⟨(CuspForm.translate f (σ : GL (Fin 2) ℝ)).holo',
    cuspForm_norm_le_exp_of_one_le_im _ k (CuspForm.translate f (σ : GL (Fin 2) ℝ))⟩

end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormSlashHoloDecayStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex → ∀ (f : CuspForm Γ k) (σ : SL(2, ℤ)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] σ) ∧ ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖(⇑f ∣[k] σ) τ‖ ≤ C * Real.exp (-c * τ.im) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay <;> assumption)
end
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Decay

theorem per_exists : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → ∀ σ : SL(2, ℤ), ∃ n : ℕ, 0 < n ∧ σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ ∈ Γ := by
  intro Γ hΓ σ
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero (σ * ModularGroup.T * σ⁻¹)
  refine ⟨n, hn, ?_⟩
  have : (σ * ModularGroup.T * σ⁻¹) ^ n = σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ := by
    rw [zpow_natCast, conj_pow]
  rwa [← this]

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  unfold eichler
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  have := Finset.mem_range.1 hj
  exact_mod_cast this

theorem per_cov (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (U : ℍ → ℂ[X]) (hU : ∀ τ, U τ ∈ degreeLT ℂ (w + 1))
    (heq : ∀ (γ : Γ) (τ : ℍ), slP w (mat γ) (U ((γ : SL(2, ℤ)) • τ)) = U τ) (σ : SL(2, ℤ)) (n : ℕ)
    (hγ : σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ ∈ Γ) (τ : ℍ) :
    slP w (mat (ModularGroup.T ^ (n : ℤ))) (slP w (mat σ) (U (σ • (ModularGroup.T ^ (n : ℤ) • τ)))) =
      slP w (mat σ) (U (σ • τ)) := by
  have h1 := heq ⟨_, hγ⟩ (σ • τ)
  have h2 : ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) • σ • τ = σ • (ModularGroup.T ^ (n : ℤ) • τ) := by
    simp only [← mul_smul]; congr 1; group
  rw [h2] at h1
  rw [← h1]
  have hm' : ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ = σ * ModularGroup.T ^ (n : ℤ) := by
    simp only [Subgroup.coe_mk]; group
  have e1 : slP w (mat (ModularGroup.T ^ (n : ℤ))) (slP w (mat σ) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))) =
      slP w (mat (σ * ModularGroup.T ^ (n : ℤ))) (U (σ • ModularGroup.T ^ (n : ℤ) • τ)) := by
    rw [show mat (σ * ModularGroup.T ^ (n : ℤ)) = mat σ * mat (ModularGroup.T ^ (n : ℤ)) from
      Matrix.SpecialLinearGroup.coe_mul _ _, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w _ _ _ (hU _)).2.1]
  have e2 : slP w (mat σ) (slP w (mat ((⟨_, hγ⟩ : Γ) : SL(2, ℤ))) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))) =
      slP w (mat (((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ)) (U (σ • ModularGroup.T ^ (n : ℤ) • τ)) := by
    rw [show mat (((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ) = mat ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * mat σ from
      Matrix.SpecialLinearGroup.coe_mul _ _, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w _ _ _ (hU _)).2.1]
  rw [e1, e2, hm']

theorem decay_at_cusp : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)) (p : ℂ[X]), p ∈ degreeLT ℂ (k - 1) → (∀ (γ : Γ) (τ : ℍ), slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ) - (eichler (k - 2) ⇑h ((γ : SL(2, ℤ)) • τ)).map (starRingEnd ℂ) - p) = eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p) → ∀ σ : SL(2, ℤ), Filter.Tendsto (fun τ : ℍ => ‖(eichler (k - 2) ⇑f (σ • τ) - (eichler (k - 2) ⇑h (σ • τ)).map (starRingEnd ℂ) - p).eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) UpperHalfPlane.atImInfty (nhds 0) := by
  intro Γ k hΓ hk f h p hp hequiv σ
  have hk2 : 2 ≤ k := by omega
  set w := k - 2 with hw
  have hw1 : 1 ≤ w := by omega
  set U : ℍ → ℂ[X] := fun τ =>
    eichler w ⇑f τ - (eichler w ⇑h τ).map (starRingEnd ℂ) - p with hU
  have hpw : p ∈ degreeLT ℂ (w + 1) := by
    rwa [show w + 1 = k - 1 by omega]
  have hUdeg : ∀ τ, U τ ∈ degreeLT ℂ (w + 1) := by
    intro τ
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (eichler_mem w _ τ) ?_) hpw
    have h0 := eichler_mem w (⇑h) τ
    rw [mem_degreeLT] at h0 ⊢
    exact (degree_map_le).trans_lt h0
  set V : ℍ → ℂ[X] := fun τ => slP w (mat σ) (U (σ • τ)) with hV
  have hVdeg : ∀ τ, V τ ∈ degreeLT ℂ (w + 1) := fun τ => (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat σ) 1 _ (hUdeg _)).1
  have hexp : (-((k : ℝ) - 2) / 2) = -(w : ℝ) / 2 := by
    rw [hw, Nat.cast_sub hk2]; push_cast; ring
  have hfun : (fun τ : ℍ => ‖(U (σ • τ)).eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) =
      fun τ => ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
    funext τ; rw [hexp]; exact GlobalTheory.T.norm_eval_smul_mul_im_rpow_polyDegreeSlash w σ (U (σ • τ)) τ (hUdeg _)
  change Filter.Tendsto (fun τ : ℍ => ‖(U (σ • τ)).eval ((σ • τ : ℍ) : ℂ)‖ *
    (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) _ _
  rw [hfun]
  obtain ⟨n, hn, hγ⟩ := per_exists Γ hΓ σ
  have hVper : ∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ :=
    fun τ => per_cov Γ w U hUdeg hequiv σ n hγ τ
  obtain ⟨hfd, Cf, cf, hcf, hfb⟩ := GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay Γ k hΓ f σ
  obtain ⟨hhd, Ch, ch, hch, hhb⟩ := GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay Γ k hΓ h σ
  obtain ⟨Q, C', c, hQ, hc, hQb⟩ := GlobalTheory.T.eichlerPeriodPolynomial_limit_at_cusp k (⇑f) (⇑h) p σ Cf cf Ch ch hk2 hcf hch
    (CuspFormClass.holo f) (CuspFormClass.holo h) hfd hhd hfb hhb hp
  have hQb' : ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w :=
    hQb
  have hQc := GlobalTheory.T.limit_poly_of_periodic_slash_family_const w n V Q C' c hn hc hQ hVdeg hVper hQb'
  rw [hQc] at hQb'
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨A, hA⟩ := GlobalTheory.T.strip_eval_polynomial_decay_mul_im_rpow w n (Q.coeff 0) V C' c hw1 hc hVdeg hQb' ε hε
  refine (atImInfty_mem _).2 ⟨A, fun τ hτ => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set m : ℤ := -⌊τ.re / n⌋ with hm
  set τ' : ℍ := ModularGroup.T ^ ((n : ℤ) * m) • τ with hτ'
  have hτ'v : τ' = ((((n : ℤ) * m : ℤ)) : ℝ) +ᵥ τ := modular_T_zpow_smul τ _
  have hre : τ'.re = τ.re + n * m := by
    rw [hτ'v]; simp [add_comm]
  have him : τ'.im = τ.im := by
    rw [hτ'v]; simp
  have hg := GlobalTheory.T.evalDiag_polyValued_invariant_translation_T_zpow_mul w n V hVdeg hVper m τ
  have hfl1 : (⌊τ.re / n⌋ : ℝ) ≤ τ.re / n := Int.floor_le _
  have hfl2 : τ.re / n < ⌊τ.re / n⌋ + 1 := Int.lt_floor_add_one _
  have hr1 : 0 ≤ τ'.re := by
    rw [hre, hm]; push_cast
    have := (le_div_iff₀ hnR).1 hfl1
    nlinarith
  have hr2 : τ'.re ≤ n := by
    rw [hre, hm]; push_cast
    have := (div_lt_iff₀ hnR).1 hfl2
    nlinarith
  have := hA τ' (him ▸ hτ) hr1 hr2
  rw [hg, him] at this
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (by positivity)]
  exact this

end GlobalTheory.HeckeFamilyMatrices.Decay
