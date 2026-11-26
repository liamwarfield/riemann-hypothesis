module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RemainderNormLeStrictUpper
public import Formalism.HermitianCurvature.StatementK
public import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionCriticalPoints

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FourierUniquenessMirabolic
open Matrix MeasureTheory

namespace Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic

open Formalism.FourierDecayAlt.G

private lemma wMat_mul_apply_eq_rev {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (r c : Fin m) :
    (wMat m * M) r c = M r.rev c := by
  simp [wMat, Matrix.mul_apply]

private lemma wMat_mulVec_apply_eq_rev {m : ℕ} (v : Fin m → ℂ) (r : Fin m) : (wMat m *ᵥ v) r = v r.rev := by
  simp [wMat, Matrix.mulVec, dotProduct]

private lemma finSumFinEquiv_symm_castSucc_eq_inl {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (Fin.castSucc i : Fin (n + 1)) = (Sum.inl i : Fin n ⊕ Fin 1) := by
  rw [Equiv.symm_apply_eq]; rfl

private lemma finSumFinEquiv_symm_last_eq_inr (n : ℕ) : finSumFinEquiv.symm (Fin.last n) = (Sum.inr 0 : Fin n ⊕ Fin 1) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem wM_succ_last {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) i.succ (Fin.last n) = B i := by
  rw [wMat_mul_apply_eq_rev]
  simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

theorem wM_succ_cast {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i j : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) i.succ j.castSucc = t * (1 : Matrix (Fin n) (Fin n) ℂ) i j + X i j := by
  rw [wMat_mul_apply_eq_rev]
  simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

theorem wM_zero_cast {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (j : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) 0 j.castSucc = ρ j := by
  rw [wMat_mul_apply_eq_rev]
  simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

theorem wM_zero_last {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    (wMat (n + 1) * Mcoord t X B ρ σ) 0 (Fin.last n) = σ := by
  rw [wMat_mul_apply_eq_rev]
  simp [Mcoord, blk, Fin.rev_succ, Fin.rev_zero, finSumFinEquiv_symm_castSucc_eq_inl, finSumFinEquiv_symm_last_eq_inr, wMat_mulVec_apply_eq_rev, wMat_mul_apply_eq_rev]

theorem diagonal_cons_succ {n : ℕ} (a b : ℂ) (x : Fin n → ℂ) (i : Fin n) (j : Fin (n + 1)) :
    Matrix.diagonal (Fin.cons a x : Fin (n + 1) → ℂ) i.succ j =
      Matrix.diagonal (Fin.cons b x : Fin (n + 1) → ℂ) i.succ j := by
  simp only [Matrix.diagonal_apply, Fin.cons_succ]

theorem xOf_redOf (m : ℕ) (p : XY m) (k : Fin (m + 1)) :
    xOf (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 k = p.1 k := by
  refine Fin.lastCases ?_ (fun k => ?_) k
  · rw [G6.xOf_last]
    simp [redOf, triXY, strictUpper, Fin.succ_last]
  · rw [G6.xOf_castSucc]
    have h : k.castSucc < k.succ := Fin.castSucc_lt_succ
    simp [redOf, triXY, strictUpper, h]

theorem wM_redOf (m : ℕ) (t ρ₁ : ℂ) (p : XY m) :
    wMat (m + 2) * Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
        (Fin.cons ρ₁ (redOf m p).2.1) (redOf m p).1 =
      t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ p.1 : Fin (m + 2) → ℂ) + strictUpper p.2 := by
  ext i j
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine Fin.cases ?_ (fun i => ?_) i
  · have hs : subShift (m + 2) 0 j = 0 := by simp [subShift]
    rw [hs, mul_zero, zero_add]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [wM_zero_last]
      simp [redOf, triXY]
    · rw [wM_zero_cast]
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [strictUpper]
      · have h : (0 : Fin (m + 2)) ≠ k.castSucc.succ := (Fin.succ_ne_zero _).symm
        simp [redOf, triXY, Matrix.diagonal_apply_ne _ h]
  · rw [diagonal_cons_succ ρ₁ 0]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [wM_succ_last]
      have hs : subShift (m + 2) i.succ (Fin.last (m + 1)) = 0 := by
        have := i.isLt
        simp only [subShift, Matrix.of_apply, Fin.val_last, Fin.val_succ]
        rw [if_neg (by omega)]
      rw [hs, mul_zero, zero_add]
      simp [redOf, triXY]
    · rw [wM_succ_cast]
      have hs : subShift (m + 2) i.succ j.castSucc = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i j := by
        simp only [subShift, Matrix.of_apply, Fin.val_castSucc, Fin.val_succ, Matrix.one_apply, Fin.ext_iff]
        by_cases h : (i : ℕ) = j
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      rw [hs, add_assoc]
      congr 1
      by_cases h : i < j
      · simp [redOf, triXY, strictUpper, h]
      · have h1 : i.succ ≠ j.castSucc := by
          intro e
          have := congrArg Fin.val e
          simp only [Fin.val_succ, Fin.val_castSucc] at this
          exact h (by rw [Fin.lt_def]; omega)
        have h2 : ¬ (i.succ < j.castSucc) := by
          intro e
          rw [Fin.lt_def] at e
          simp only [Fin.val_succ, Fin.val_castSucc] at e
          exact h (by rw [Fin.lt_def]; omega)
        simp [strictUpper, h, h2, Matrix.diagonal_apply_ne _ h1]

end Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic

theorem cofactor_lower_bound_radius : Formalism.FourierDecayAlt.G.CofLowerR := by
  intro m Kc hK h0 R hR
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0
  have hD : ∀ D ∈ Kc, d ≤ ‖D‖ := by
    intro D hDK
    by_contra hlt
    exact hball (by simpa [Metric.mem_ball] using not_le.mp hlt) hDK
  set R' : ℝ := max 1 R with hR'
  have hR1 : 1 ≤ R' := le_max_left _ _
  have hRR : R ≤ R' := le_max_right _ _
  have hR0 : 0 < R' := lt_of_lt_of_le one_pos hR1
  set Cm : ℝ := ((m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) ^ m) with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set q : ℝ := d / (2 * (Cm + 1) * R' ^ (m + 2)) with hq
  have hq0 : 0 < q := by positivity
  refine ⟨min 1 (q ^ 2), d / (2 * R'), by positivity, by positivity, ?_⟩
  intro ε hε hε2 D hDK t ht htle X B ρ₁ ρ' σ hS hX hB hρ₁ hρ' hσ hrel
  have hT : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hT1 : ‖t‖ ≤ 1 := le_trans htle (min_le_left _ _)
  have hTq : ‖t‖ ≤ q ^ 2 := le_trans htle (min_le_right _ _)
  set L₀ : ℝ := ‖t‖ ^ (-ε) with hL₀def
  have hL₀ : 1 ≤ L₀ := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hT hT1 (by linarith)
  have hL₀0 : 0 < L₀ := lt_of_lt_of_le one_pos hL₀
  set L : ℝ := R' * L₀ with hLdef
  have hL : 1 ≤ L := by nlinarith
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hRL : R * L₀ ≤ L := mul_le_mul_of_nonneg_right hRR hL₀0.le
  have hsq : L ^ (m + 2) * ‖t‖ ≤ R' ^ (m + 2) * q := by
    rw [hLdef, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (le_trans (G6.rpow_bound m hT hT1 hε2) (Real.sqrt_le_iff.mpr ⟨hq0.le, hTq⟩)) (by positivity)
  have hRb := G6.remainder_norm_le_strict_upper (t := t) hL hT1 hS (fun i j => (hX i j).trans hRL) (fun i => (hB i).trans hRL)
    (fun k => (hρ' k).trans hRL)
  have h1 : ‖t ^ (m + 1) * σ‖ ≤ L ^ (m + 2) * ‖t‖ := by
    rw [norm_mul, norm_pow, mul_comm]
    refine mul_le_mul (le_trans (hσ.trans hRL) (le_self_pow₀ hL (by omega)))
      (pow_le_of_le_one hT.le hT1 (by omega)) (by positivity) (by positivity)
  have h2 : ‖Cof X B t * ρ₁‖ ≤ ‖Cof X B t‖ * L := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hρ₁.trans hRL) (norm_nonneg _)
  have hDeq : D = t ^ (m + 1) * σ - Cof X B t * ρ₁ - R0 X B ρ' t := by
    rw [hrel]; ring
  have h3 : ‖D‖ ≤ L ^ (m + 2) * ‖t‖ + ‖Cof X B t‖ * L + Cm * (L ^ (m + 2) * ‖t‖) := by
    calc ‖D‖ = ‖t ^ (m + 1) * σ - Cof X B t * ρ₁ - R0 X B ρ' t‖ := by rw [← hDeq]
      _ ≤ ‖t ^ (m + 1) * σ‖ + ‖Cof X B t * ρ₁‖ + ‖R0 X B ρ' t‖ :=
          le_trans (norm_sub_le _ _) (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ _ := add_le_add (add_le_add h1 h2) hRb
  have h4 : (Cm + 1) * (L ^ (m + 2) * ‖t‖) ≤ d / 2 := by
    calc (Cm + 1) * (L ^ (m + 2) * ‖t‖) ≤ (Cm + 1) * (R' ^ (m + 2) * q) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = d / 2 := by rw [hq]; field_simp
  have h5 : d / 2 ≤ ‖Cof X B t‖ * L := by
    have := hD D hDK
    nlinarith
  have hinv : ‖t‖ ^ ε = L₀⁻¹ := by
    rw [hL₀def, Real.rpow_neg hT.le, inv_inv]
  have e : d / (2 * R') * L₀⁻¹ = d / 2 / L := by
    rw [hLdef]; field_simp
  rw [hinv, e, div_le_iff₀ hL0]
  exact h5

theorem amplitude_eq : Formalism.FourierDecayAlt.G.AmpEq := by
  intro m β D t ht V _ _ Φ p
  have hx := xOf_redOf m p
  unfold amp redIntegrand
  rw [smul_smul, ← mul_assoc, ← (additive_character_psi β _ _).1]
  congr 3
  unfold gRem g0 rhoXY
  simp only [hx]
  field_simp
  ring

theorem limit_coordinates_xy : Formalism.FourierDecayAlt.G.LimitCoordsXY := by
  intro m z y
  rw [wM_redOf m 0 z (fun _ => z, y)]
  congr 1
  rw [zero_smul, zero_add]
  ext i j
  by_cases h : i = j
  · subst h
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp [Matrix.diagonal, Matrix.smul_apply]
  · simp [Matrix.diagonal, h, Matrix.smul_apply]

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevExtremalPolynomials
namespace Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials

open Finset Polynomial Formalism.FourierDecayAlt.F7

lemma chebPt_eq (α β : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    Formalism.SA.C.chebPt α β n j = (α + β) / 2 + (β - α) / 2 * Chebyshev.node n j := by
  simp only [Formalism.SA.C.chebPt, Chebyshev.node, mul_comm Real.pi]

lemma lagCo_affine {d : ℕ} (c h : ℝ) (x : Fin (d + 1) → ℝ) (j : Fin (d + 1)) :
    lagCo (fun i => c + h * x i) j = (h⁻¹) ^ d * lagCo x j := by
  unfold lagCo
  have : ∀ i ∈ univ.erase j, ((c + h * x j) - (c + h * x i))⁻¹ = h⁻¹ * (x j - x i)⁻¹ := by
    intro i _
    rw [← mul_inv]; congr 1; ring
  rw [prod_congr rfl this, prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ j)]
  simp

noncomputable def nd (n : ℕ) (j : Fin (n + 1)) : ℝ := Chebyshev.node n j

lemma nd_injective (n : ℕ) : Function.Injective (nd n) := by
  intro i j hij
  have := (Chebyshev.strictAntiOn_node n).injOn
    (Finset.mem_coe.mpr (Finset.mem_range.mpr i.isLt)) (Finset.mem_coe.mpr (Finset.mem_range.mpr j.isLt)) hij
  exact Fin.ext this

lemma U_mul_sin_node (m : ℕ) (j : ℕ) :
    (Chebyshev.U ℝ (m:ℤ)).eval (Chebyshev.node (m + 1) j) * Real.sin (j * Real.pi / ((m + 1 : ℕ) : ℝ)) = 0 := by
  unfold Chebyshev.node
  rw [Chebyshev.U_real_cos]
  have : (((m:ℤ):ℝ) + 1) * (j * Real.pi / ((m + 1 : ℕ) : ℝ)) = j * Real.pi := by
    push_cast; field_simp
  rw [this]
  exact Real.sin_nat_mul_pi j

lemma nodal_eq (m : ℕ) :
    (X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ) = C ((2:ℝ) ^ m) * Lagrange.nodal univ (nd (m + 1)) := by
  have h2 : ((2:ℝ) ^ m) ≠ 0 := by positivity
  have hmon : (X ^ 2 - 1 : ℝ[X]).Monic := by
    have := monic_X_pow_sub_C (R := ℝ) (1:ℝ) (n := 2) (by norm_num)
    simpa using this
  have hdX : (X ^ 2 - 1 : ℝ[X]).degree = 2 := by
    have := degree_X_pow_sub_C (R := ℝ) (n := 2) (by norm_num) (1:ℝ)
    simpa using this
  have hdL : ((X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ)).degree = ((m + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, hdX, Chebyshev.degree_U_natCast]
    norm_cast; ring_nf
  have hdR : (C ((2:ℝ) ^ m) * Lagrange.nodal univ (nd (m + 1))).degree = ((m + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_C_mul h2, Lagrange.degree_nodal, card_univ, Fintype.card_fin]
  apply Polynomial.eq_of_degree_le_of_eval_index_eq univ (v := nd (m + 1))
    ((nd_injective (m + 1)).injOn)
  · rw [hdL, card_univ, Fintype.card_fin]
  · exact hdL.trans hdR.symm
  · rw [leadingCoeff_mul, hmon.leadingCoeff, Chebyshev.leadingCoeff_U_natCast, leadingCoeff_mul,
        leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff]; ring
  · intro i _
    rw [eval_mul, eval_mul, Lagrange.eval_nodal_at_node (mem_univ i), mul_zero]
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    have h := U_mul_sin_node m i
    have hs : (nd (m + 1) i) ^ 2 - 1 = - Real.sin (i * Real.pi / ((m + 1 : ℕ) : ℝ)) ^ 2 := by
      have := Real.sin_sq_add_cos_sq ((i:ℕ) * Real.pi / ((m + 1 : ℕ) : ℝ))
      unfold nd Chebyshev.node
      linarith
    rw [hs]
    unfold nd
    linear_combination (- Real.sin (i * Real.pi / ((m + 1 : ℕ) : ℝ))) * h

lemma deriv_eq (m : ℕ) :
    derivative ((X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ)) =
      ((m:ℝ[X]) + 1) * Chebyshev.T ℝ ((m:ℤ) + 1) + X * Chebyshev.U ℝ (m:ℤ) := by
  have h := Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℝ) (m:ℤ)
  rw [derivative_mul]
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, map_ofNat]
  push_cast at h
  linear_combination -h

lemma node_mul_U (m : ℕ) (j : Fin (m + 2)) :
    nd (m + 1) j * (Chebyshev.U ℝ (m:ℤ)).eval (nd (m + 1) j) =
      if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (-1) ^ (j:ℕ) * ((m:ℝ) + 1) else 0 := by
  by_cases h0 : (j:ℕ) = 0
  · have : nd (m + 1) j = 1 := by unfold nd; rw [h0]; exact Chebyshev.node_eq_one
    rw [this, if_pos (Or.inl h0), h0, Chebyshev.U_eval_one]; simp
  by_cases h1 : (j:ℕ) = m + 1
  · have : nd (m + 1) j = -1 := by unfold nd; rw [h1]; exact Chebyshev.node_eq_neg_one (by omega)
    rw [this, if_pos (Or.inr h1), h1, Chebyshev.U_eval_neg_one, Int.cast_negOnePow]
    push_cast
    rw [zpow_natCast, pow_succ]; ring
  · rw [if_neg (by tauto)]
    have h := U_mul_sin_node m j
    have hpos : 0 < Real.sin ((j:ℕ) * Real.pi / ((m + 1 : ℕ) : ℝ)) := by
      have hj : (0:ℝ) < (j:ℕ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hjm : ((j:ℕ):ℝ) < ((m + 1 : ℕ) : ℝ) := by
        have := j.isLt
        exact_mod_cast (by omega : (j:ℕ) < m + 1)
      have hm : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      apply Real.sin_pos_of_pos_of_lt_pi
      · have := Real.pi_pos; positivity
      · rw [div_lt_iff₀ hm, mul_comm]
        exact mul_lt_mul_of_pos_left hjm Real.pi_pos
    have : (Chebyshev.U ℝ (m:ℤ)).eval (nd (m + 1) j) = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hpos.ne'
    rw [this, mul_zero]

lemma prod_node (m : ℕ) (j : Fin (m + 2)) :
    (2:ℝ) ^ m * ∏ i ∈ univ.erase j, (nd (m + 1) j - nd (m + 1) i) =
      (-1) ^ (j:ℕ) * ((m:ℝ) + 1) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 2 else 1) := by
  have h1 := congrArg (fun p => eval (nd (m + 1) j) (derivative p)) (nodal_eq m)
  simp only [deriv_eq, derivative_C_mul, eval_mul, eval_C, eval_add, eval_X, eval_natCast, eval_one,
    Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ j), Lagrange.eval_nodal] at h1
  rw [← h1, node_mul_U]
  have hT : (Chebyshev.T ℝ ((m:ℤ) + 1)).eval (nd (m + 1) j) = (-1) ^ (j:ℕ) := by
    have := Chebyshev.eval_T_real_node (n := m + 1) (i := j) (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt))
    push_cast at this
    exact this
  rw [hT]
  split_ifs <;> ring

lemma lagCo_nd (m : ℕ) (j : Fin (m + 2)) :
    lagCo (nd (m + 1)) j =
      (-1) ^ (j:ℕ) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 1 / 2 else 1) * ((2:ℝ) ^ m / ((m:ℝ) + 1)) := by
  have h := prod_node m j
  unfold lagCo
  rw [prod_inv_distrib]
  have h2 : (2:ℝ) ^ m ≠ 0 := by positivity
  have hm : (m:ℝ) + 1 ≠ 0 := by positivity
  have hs : ((-1:ℝ) ^ (j:ℕ)) * ((-1:ℝ) ^ (j:ℕ)) = 1 := by
    rw [← mul_pow]; simp
  have hs0 : ((-1:ℝ) ^ (j:ℕ)) ≠ 0 := by positivity
  have hP : ∏ i ∈ univ.erase j, (nd (m + 1) j - nd (m + 1) i) =
      (-1) ^ (j:ℕ) * ((m:ℝ) + 1) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 2 else 1) / (2:ℝ) ^ m := by
    rw [← h]; field_simp
  rw [hP]
  split_ifs
  · field_simp; linear_combination -hs
  · field_simp; linear_combination -hs

theorem coValue : Formalism.FourierDecayAlt.F7.ChebCoValue := by
  intro α β n hαβ hn j
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd : 0 < β - α := by linarith
  have e : Formalism.SA.C.chebPt α β (m + 1) = fun i => (α + β) / 2 + (β - α) / 2 * nd (m + 1) i := by
    funext i; exact chebPt_eq α β (m + 1) i
  rw [e, lagCo_affine, lagCo_nd]
  have : ((β - α) / 2)⁻¹ = 2 / (β - α) := by rw [inv_div]
  rw [this, Nat.add_sub_cancel]
  push_cast
  ring

lemma sum_half (m : ℕ) :
    ∑ j : Fin (m + 2), (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) = (m:ℝ) + 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have : ∀ i : Fin m, (if ((i.castSucc.succ : Fin (m + 2)) : ℕ) = 0 ∨
      ((i.castSucc.succ : Fin (m + 2)) : ℕ) = m + 1 then (1 / 2 : ℝ) else 1) = 1 := by
    intro i
    rw [if_neg]
    have := i.isLt
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  rw [sum_congr rfl (fun i _ => this i)]
  simp
  ring

theorem sharp : Formalism.FourierDecayAlt.F7.ChebSharp := by
  intro α β n hαβ hn
  have hd : 0 < β - α := by linarith
  constructor
  · intro i j hij
    rw [chebPt_eq, chebPt_eq] at hij
    have h2 : Chebyshev.node n i = Chebyshev.node n j := by
      have : (β - α) / 2 * Chebyshev.node n i = (β - α) / 2 * Chebyshev.node n j := by linarith
      exact mul_left_cancel₀ (by positivity) this
    exact nd_injective n h2
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hv : ∀ j : Fin (m + 2), |lagCo (Formalism.SA.C.chebPt α β (m + 1)) j| =
        (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) *
          (((2 : ℝ) ^ m / ((m:ℝ) + 1)) * (2 / (β - α)) ^ (m + 1)) := by
      intro j
      rw [coValue α β (m + 1) hαβ hn j, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul, Nat.add_sub_cancel]
      have h1 : |(if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1)| =
          (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) := by
        apply abs_of_nonneg; split_ifs <;> norm_num
      rw [h1, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      push_cast; ring
    rw [sum_congr rfl (fun j _ => hv j), ← sum_mul, sum_half]
    have hm : (m:ℝ) + 1 ≠ 0 := by positivity
    rw [show (4:ℝ) / (β - α) = 2 * (2 / (β - α)) by ring, mul_pow, pow_succ (2:ℝ) m]
    field_simp

lemma sum_lagCo_mul_pow {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (k : ℕ)
    (hk : k ≤ d) : ∑ j, lagCo y j * y j ^ k = if k = d then 1 else 0 := by
  have hlt : ((X : ℝ[X]) ^ k).degree < (univ : Finset (Fin (d + 1))).card := by
    rw [degree_X_pow, card_univ, Fintype.card_fin]; exact_mod_cast Nat.lt_succ_of_le hk
  have h := Lagrange.coeff_eq_sum (s := univ) (v := y) hy.injOn hlt
  simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel, coeff_X_pow, eval_pow, eval_X] at h
  have e : (if k = d then (1:ℝ) else 0) = if d = k then 1 else 0 := by
    by_cases hkd : k = d
    · subst hkd; simp
    · rw [if_neg hkd, if_neg (Ne.symm hkd)]
  rw [e, h]
  refine sum_congr rfl fun i _ => ?_
  unfold lagCo
  rw [prod_inv_distrib, div_eq_mul_inv, mul_comm]

lemma lead_complex {V : Type} [AddCommGroup V] [Module ℂ V] {d : ℕ} (y : Fin (d + 1) → ℝ)
    (hy : Function.Injective y) (a : Fin (d + 1) → V) :
    a (Fin.last d) = ∑ j, ((lagCo y j : ℝ) : ℂ) • ∑ k : Fin (d + 1), ((y j : ℂ) ^ (k : ℕ)) • a k := by
  simp_rw [smul_sum, smul_smul]
  rw [sum_comm]
  simp_rw [← sum_smul]
  have : ∀ k : Fin (d + 1), (∑ j, ((lagCo y j : ℝ) : ℂ) * (y j : ℂ) ^ (k:ℕ)) =
      if k = Fin.last d then 1 else 0 := by
    intro k
    have h := sum_lagCo_mul_pow y hy k (Nat.lt_succ_iff.mp k.isLt)
    have h' := congrArg (fun r : ℝ => (r : ℂ)) h
    push_cast at h'
    rw [h']
    by_cases hk : k = Fin.last d
    · subst hk; simp
    · have hk' : ¬ ((k:ℕ) = d) := fun h0 => hk (Fin.ext (by simpa using h0))
      rw [if_neg hk, if_neg hk']; simp
  simp_rw [this]
  simp

end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials

namespace Formalism.FourierDecayAlt.P

theorem chebyshev_bound_sharp : Formalism.FourierDecayAlt.F7.ChebSharp := ChebyshevExtremalPolynomials.sharp

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleForm
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A5x1

theorem lamN_last {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (j : ℕ) (hj : j + 1 = n) : lamN R Z j = lamLin R Z := by
  unfold lamN lamTil lamLin rowN lastCoord
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  have : (a.val = j ↔ a.val + 1 = n) := by omega
  simp [this]

end Formalism.FourierDecayAlt.P.A5x1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x1

theorem tripleForm : Formalism.FourierDecayAlt.A5.TripleForm := by
  intro K _ R ψ w w' k hw hw'
  unfold Kp intTT pairTerm
  apply finsum_congr
  intro q
  congr 2
  split_ifs with hI
  · congr 1
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro φ
    constructor
    · intro hφ
      refine ⟨hφ, ?_⟩
      intro j hkj hjn
      have hj : j = k := by omega
      subst hj
      refine ⟨0, ?_⟩
      intro v v' hv
      have h2 := hφ.2 v v' hv
      rw [lamN_last R _ j hw'.symm, lamN_last R _ j hw.symm, h2]
      simp
    · exact fun h => h.1
  · rfl

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakApproximationGL
open Matrix MeasureTheory

namespace Formalism.FourierDecayAlt.P.WeakApproximationGL

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5

theorem tri_diag {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) (i : Fin (m + 1)) :
    triXY x y i.succ i.succ = x i := by
  simp [triXY, strictUpper]

theorem tri_lt {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) {i j : Fin (m + 2)} (h : i < j) :
    triXY x y i j = y ⟨(i, j), h⟩ := by
  simp [triXY, strictUpper, h, Matrix.diagonal_apply_ne _ h.ne]

theorem tri_gt {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) {i j : Fin (m + 2)} (h : j < i) :
    triXY x y i j = 0 := by
  simp [triXY, strictUpper, not_lt.mpr h.le, Matrix.diagonal_apply_ne _ h.ne']

abbrev FinalTheorems (m : ℕ) : Type := Fin (m + 1) ⊕ UT (m + 2)

abbrev Tgt (m : ℕ) : Type := Unit ⊕ (Fin m ⊕ (UT (m + 1) ⊕ Fin (m + 1)))

def cls {m : ℕ} (i : Fin (m + 1)) (j : Fin (m + 2)) (h : i.succ ≤ j) : FinalTheorems m :=
  if h' : i.succ = j then Sum.inl i else Sum.inr ⟨(i.succ, j), lt_of_le_of_ne h h'⟩

theorem elim_cls {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) (i : Fin (m + 1)) (j : Fin (m + 2))
    (h : i.succ ≤ j) : Sum.elim x y (cls i j h) = triXY x y i.succ j := by
  unfold cls
  split_ifs with h'
  · subst h'
    exact (tri_diag x y i).symm
  · exact (tri_lt x y _).symm

theorem succ_le_castSucc {m : ℕ} {i j : Fin (m + 1)} (h : i < j) : i.succ ≤ j.castSucc := by
  rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
  exact h

def idx (m : ℕ) : Tgt m → FinalTheorems m
  | Sum.inl _ => Sum.inr ⟨(0, Fin.last (m + 1)), Fin.last_pos⟩
  | Sum.inr (Sum.inl k) => Sum.inr ⟨(0, k.succ.castSucc), by
      rw [Fin.lt_def]; simp⟩
  | Sum.inr (Sum.inr (Sum.inl q)) => cls q.1.1 q.1.2.castSucc (succ_le_castSucc q.2)
  | Sum.inr (Sum.inr (Sum.inr i)) => cls i (Fin.last (m + 1)) (Fin.le_last _)

theorem idx_surjective (m : ℕ) : Function.Surjective (idx m) := by
  rintro (i | ⟨⟨a, b⟩, hab⟩)
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨(k.castSucc, k.succ), Fin.castSucc_lt_succ⟩)), ?_⟩
      show cls k.castSucc k.succ.castSucc (succ_le_castSucc Fin.castSucc_lt_succ) = Sum.inl k.castSucc
      unfold cls
      exact dif_pos rfl
    · exact ⟨Sum.inr (Sum.inr (Sum.inr (Fin.last m))), by simp [idx, cls]⟩
  · rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨c, rfl⟩ | rfl
      · rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨k, rfl⟩
        · simp at hab
        · exact ⟨Sum.inr (Sum.inl k), rfl⟩
      · exact ⟨Sum.inl (), rfl⟩
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨c, rfl⟩ | rfl
      · have hic : i < c := by
          rw [Fin.lt_def] at hab ⊢
          simp only [Fin.val_succ, Fin.val_castSucc] at hab
          omega
        exact ⟨Sum.inr (Sum.inr (Sum.inl ⟨(i, c), hic⟩)), by simp [idx, cls, ne_of_lt hab]⟩
      · exact ⟨Sum.inr (Sum.inr (Sum.inr i)), by simp [idx, cls, ne_of_lt hab]⟩

theorem card_eq (m : ℕ) : Fintype.card (Tgt m) = Fintype.card (FinalTheorems m) := by
  simp only [Tgt, FinalTheorems, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
    Formalism.FourierDecayAlt.P.G5.card_UT, Finset.sum_range_succ]
  ring

theorem idx_bijective (m : ℕ) : Function.Bijective (idx m) :=
  (Fintype.bijective_iff_surjective_and_card _).mpr ⟨idx_surjective m, card_eq m⟩

noncomputable def idxE (m : ℕ) : Tgt m ≃ FinalTheorems m := Equiv.ofBijective (idx m) (idx_bijective m)

def split (m : ℕ) (v : Tgt m → ℂ) : RedCoord m :=
  (v (Sum.inl ()), fun k => v (Sum.inr (Sum.inl k)), fun q => v (Sum.inr (Sum.inr (Sum.inl q))),
    fun i => v (Sum.inr (Sum.inr (Sum.inr i))))

theorem redOf_eq (m : ℕ) (p : XY m) : redOf m p = split m (Sum.elim p.1 p.2 ∘ idx m) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact tri_lt p.1 p.2 Fin.last_pos
  · funext k
    exact tri_lt p.1 p.2 _
  · funext q
    exact (elim_cls p.1 p.2 _ _ (succ_le_castSucc q.2)).symm
  · funext i
    exact (elim_cls p.1 p.2 _ _ (Fin.le_last _)).symm

theorem split_bijective (m : ℕ) : Function.Bijective (split m) := by
  refine ⟨fun v w h => ?_, fun q => ⟨Sum.elim (fun _ => q.1) (Sum.elim q.2.1 (Sum.elim q.2.2.1 q.2.2.2)), rfl⟩⟩
  simp only [split, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  funext s
  rcases s with ⟨⟩ | k | q | i
  · exact h1
  · exact congrFun h2 k
  · exact congrFun h3 q
  · exact congrFun h4 i

theorem elim_bijective (m : ℕ) :
    Function.Bijective (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) :=
  (Equiv.sumArrowEquivProdArrow _ _ ℂ).symm.bijective

theorem comp_bijective (m : ℕ) : Function.Bijective (fun v : FinalTheorems m → ℂ => v ∘ idx m) := by
  refine ⟨fun v w h => funext fun s => ?_, fun u => ⟨u ∘ (idxE m).symm, funext fun t => ?_⟩⟩
  · obtain ⟨t, rfl⟩ := idx_surjective m s
    exact congrFun h t
  · simp only [Function.comp_apply]
    congr 1
    exact (idxE m).symm_apply_apply t

theorem redOf_bijective (m : ℕ) : Function.Bijective (redOf m) := by
  have h : redOf m = split m ∘ (fun v : FinalTheorems m → ℂ => v ∘ idx m) ∘
      (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) := funext (redOf_eq m)
  rw [h]
  exact (split_bijective m).comp ((comp_bijective m).comp (elim_bijective m))

theorem mp_elim (β : ℂ) (m : ℕ) :
    MeasurePreserving (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) (muXY β m) (muPi β (FinalTheorems m)) := by
  have := Formalism.FourierDecayAlt.P.G5.sigmaFinite_mu β
  have h := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : FinalTheorems m => ℂ) (fun _ => mu β)
  have e : (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : FinalTheorems m => ℂ)).symm := by
    funext p i
    cases i <;> rfl
  rw [e]
  exact h

theorem mp_split (β : ℂ) (m : ℕ) : MeasurePreserving (split m) (muPi β (Tgt m)) (muRed β m) := by
  have := Formalism.FourierDecayAlt.P.G5.sigmaFinite_mu β
  have h3 := measurePreserving_sumPiEquivProdPi (X := fun _ : UT (m + 1) ⊕ Fin (m + 1) => ℂ)
    (fun _ => mu β)
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin m ⊕ (UT (m + 1) ⊕ Fin (m + 1)) => ℂ)
    (fun _ => mu β)
  have h1 := measurePreserving_sumPiEquivProdPi (X := fun _ : Tgt m => ℂ) (fun _ => mu β)
  have hu := measurePreserving_funUnique (mu β) Unit
  have key := (hu.prod ((MeasurePreserving.id _).prod h3 |>.comp h2)).comp h1
  convert key using 1 <;> rfl

theorem rhs_zero {m : ℕ} (t ρ₁ : ℂ) (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) {j : Fin (m + 2)} (h : 0 < j) :
    (t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ x : Fin (m + 2) → ℂ) + strictUpper y) 0 j =
      triXY x y 0 j := by
  simp [triXY, subShift, Matrix.diagonal_apply_ne _ h.ne]

theorem rhs_succ {m : ℕ} (t ρ₁ : ℂ) (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) (i : Fin (m + 1))
    (j : Fin (m + 2)) :
    (t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ x : Fin (m + 2) → ℂ) + strictUpper y) i.succ j =
      (if (j : ℕ) = i then t else 0) + triXY x y i.succ j := by
  simp only [triXY, subShift, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.diagonal_apply, Fin.val_succ, smul_eq_mul, Fin.cons_succ]
  have hiff : ((j : ℕ) + 1 = (i : ℕ) + 1) ↔ ((j : ℕ) = i) := by omega
  by_cases hj : (j : ℕ) = i
  · rw [if_pos (hiff.mpr hj), if_pos hj]
    ring
  · rw [if_neg (fun h => hj (hiff.mp h)), if_neg hj]
    ring

theorem wMat_mulVec_apply {n : ℕ} (B : Fin n → ℂ) (i : Fin n) : (wMat n *ᵥ B) i = B i.rev := by
  simp [wMat, Matrix.mulVec, dotProduct]

theorem xOf_redOf (m : ℕ) (p : XY m) (k : Fin (m + 1)) :
    xOf (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 k = p.1 k := by
  induction k using Fin.lastCases with
  | last =>
    simp only [xOf, Fin.succ_last, blk_cl]
    exact tri_diag p.1 p.2 (Fin.last m)
  | cast c =>
    simp only [xOf, Fin.succ_castSucc, blk_cc, strictUpper, Matrix.of_apply,
      dif_pos (Fin.castSucc_lt_succ (i := c))]
    exact tri_diag p.1 p.2 c.castSucc

theorem matrix_redOf (m : ℕ) (t ρ₁ : ℂ) (p : XY m) :
    wMat (m + 2) * Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
        (Fin.cons ρ₁ (redOf m p).2.1) (redOf m p).1 =
      t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ p.1 : Fin (m + 2) → ℂ) + strictUpper p.2 := by
  ext i j
  rw [wMat_mul_apply]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨r, rfl⟩
  ·
    rw [Fin.rev_zero]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨c, rfl⟩ | rfl
    · rw [Mcoord, blk_lc]
      rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨k, rfl⟩
      · simp [subShift, strictUpper]
      · rw [Fin.cons_succ, rhs_zero _ _ _ _ (by simp [Fin.lt_def])]
        rfl
    · rw [Mcoord, blk_ll, rhs_zero _ _ _ _ Fin.last_pos]
      rfl
  ·
    rw [Fin.rev_succ, rhs_succ]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨c, rfl⟩ | rfl
    · rw [Mcoord, blk_cc, wMat_mul_apply, Fin.rev_rev]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, strictUpper,
        Matrix.of_apply, Fin.val_castSucc, smul_eq_mul]
      by_cases hrc : r < c
      · have h1 : r ≠ c := ne_of_lt hrc
        have h2 : (c : ℕ) ≠ r := fun h => h1 (Fin.ext h.symm)
        rw [dif_pos hrc, if_neg h1, if_neg h2]
        simp only [mul_zero, zero_add]
        rfl
      · have hcr : c.castSucc < r.succ := by
          rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
          rw [not_lt, Fin.le_iff_val_le_val] at hrc
          omega
        rw [dite_eq_right hrc, tri_gt _ _ hcr]
        by_cases hrc' : r = c
        · subst hrc'
          simp
        · have h2 : (c : ℕ) ≠ r := fun h => hrc' (Fin.ext h.symm)
          simp [hrc', h2]
    · rw [Mcoord, blk_cl, wMat_mulVec_apply, Fin.rev_rev]
      have hne : ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) ≠ r := by
        simp only [Fin.val_last]
        have := r.isLt
        omega
      rw [if_neg hne, zero_add]
      rfl

theorem diag_const (m : ℕ) (z : ℂ) :
    Matrix.diagonal (Fin.cons z (fun _ : Fin (m + 1) => z) : Fin (m + 2) → ℂ) =
      z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) := by
  have hc : (Fin.cons z (fun _ : Fin (m + 1) => z) : Fin (m + 2) → ℂ) = fun _ => z := by
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩ <;> simp
  rw [hc, Matrix.smul_one_eq_diagonal]

end Formalism.FourierDecayAlt.P.WeakApproximationGL

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.WeakApproximationGL

theorem split_xy_coordinates : Formalism.FourierDecayAlt.G.SplitXY := by
  intro m β
  refine ⟨redOf_bijective m, ?_⟩
  have h : redOf m = split m ∘ (fun v : FinalTheorems m → ℂ => v ∘ idx m) ∘
      (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) := funext (redOf_eq m)
  rw [h]
  exact (mp_split β m).comp ((Formalism.FourierDecayAlt.P.G5.mp_comp_equiv β (idxE m)).comp (mp_elim β m))

theorem split_xy_matrix : Formalism.FourierDecayAlt.G.SplitXYMatrix :=
  fun m t ρ₁ p => ⟨xOf_redOf m p, matrix_redOf m t ρ₁ p⟩

end Formalism.FourierDecayAlt.P
end
