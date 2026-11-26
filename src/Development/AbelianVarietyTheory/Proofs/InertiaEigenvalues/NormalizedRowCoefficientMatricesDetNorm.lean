module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MoorePowSubSelfEqProd
noncomputable section

namespace GlobalTheory.PMonE

open Finset Polynomial

theorem moore_pow_sub_self_eq_prod {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (x : F) :
    x ^ p - x = ∏ c : ZMod p, (x - ((c.val : ℕ) : F)) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at hroots
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := Polynomial.natDegree_X_pow_sub_X (R := (ZMod p)) hp
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast hp
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hroots, hdeg]; simp)
  rw [hroots] at h
  have h2 : (X ^ p - X : (ZMod p)[X]) = ∏ c : ZMod p, (X - C c) := by
    rw [← h]; rfl
  have h3 := congrArg (Polynomial.aeval x) h2
  simp only [map_sub, map_pow, aeval_X, map_prod, aeval_C] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun c _ => ?_
  congr 1
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [map_natCast]

theorem moore_step_eq_prod {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (x t : F) :
    x ^ p - t ^ (p - 1) * x = ∏ c : ZMod p, (x - ((c.val : ℕ) : F) * t) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  by_cases ht : t = 0
  · subst ht
    rw [zero_pow (by omega)]
    simp
  · have h := moore_pow_sub_self_eq_prod p (x / t)
    have h1 : ∏ c : ZMod p, (x - ((c.val : ℕ) : F) * t) = ∏ c : ZMod p, (t * (x / t - ((c.val : ℕ) : F))) := by
      refine Finset.prod_congr rfl fun c _ => ?_
      field_simp
    rw [h1, Finset.prod_mul_distrib, ← h, Finset.prod_const, Finset.card_univ, ZMod.card]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, div_pow]
    field_simp
    ring

theorem moore_step_norm_ge {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] (x t : F) (r : ℝ)
    (hr : 0 ≤ r) (h : ∀ c : ℤ, r ≤ ‖x + (c : F) * t‖) : r ^ p ≤ ‖x ^ p - t ^ (p - 1) * x‖ := by
  rw [moore_step_eq_prod, norm_prod]
  have : r ^ p = ∏ _c : ZMod p, r := by simp
  rw [this]
  refine Finset.prod_le_prod₀ (fun _ _ => hr) fun c _ => ?_
  have := h (-(c.val : ℤ))
  simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, ← sub_eq_add_neg] using this

theorem moore_step_norm_le {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] (x t : F)
    (h : ‖t‖ ≤ ‖x‖) : ‖x ^ p - t ^ (p - 1) * x‖ ≤ ‖x‖ ^ p := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_pow]
  · rw [norm_neg, norm_mul, norm_pow]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    gcongr

theorem moore_step_sum {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {h : ℕ} (c : Fin h → ℤ)
    (x : Fin h → F) (t : F) :
    ∑ i, (c i : F) * (x i ^ p - t ^ (p - 1) * x i) =
      (∑ i, (c i : F) * x i) ^ p - t ^ (p - 1) * ∑ i, (c i : F) * x i := by
  rw [sum_pow_char, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (c i : F) ^ p = c i := by
    have := map_intCast (frobenius F p) (c i)
    rwa [frobenius_def] at this
  rw [mul_pow, this]
  ring

theorem moore_det_succ {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {k : ℕ} (lam : Fin (k + 1) → F) :
    (Matrix.of fun r j : Fin (k + 1) => lam j ^ p ^ (r : ℕ)).det =
      (-1) ^ k * lam (Fin.last k) * (Matrix.of fun r j : Fin k =>
        (lam j.castSucc ^ p - lam (Fin.last k) ^ (p - 1) * lam j.castSucc) ^ p ^ (r : ℕ)).det := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set t := lam (Fin.last k) with ht
  let B : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
    Matrix.of fun r j => Fin.cases (motive := fun _ => F) (lam j)
      (fun s => (lam j ^ p - t ^ (p - 1) * lam j) ^ p ^ (s : ℕ)) r
  have hB : (Matrix.of fun r j : Fin (k + 1) => lam j ^ p ^ (r : ℕ)).det = B.det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun s => (t ^ (p - 1)) ^ p ^ (s : ℕ)) ?_ ?_
    · intro j; simp [B]
    · intro i j
      simp only [B, Matrix.of_apply, Fin.cases_succ, Fin.val_succ, Fin.val_castSucc]
      rw [sub_pow_char_pow, mul_pow, ← pow_mul (lam j) p, pow_succ' p]
      ring
  have h0 : t ^ p - t ^ (p - 1) * t = 0 := by
    rw [← pow_succ, Nat.sub_add_cancel hp.le, sub_self]
  rw [hB, Matrix.det_succ_column B (Fin.last k), Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · congr 1
    · simp [B, ht]
    · congr 1
      ext r j
      simp [B]
  · intro i _
    have : B i.succ (Fin.last k) = 0 := by
      simp only [B, Matrix.of_apply, Fin.cases_succ, ← ht, h0]
      exact zero_pow (pow_ne_zero _ (by omega))
    rw [this]; simp

theorem mooreNorm : MooreNorm := by
  intro F _ _ p _ _ _ h
  induction h with
  | zero => intro lam _ _; simp
  | succ k ih =>
    intro lam hanti horth
    set t := lam (Fin.last k) with ht
    have hlow : ∀ (c : Fin k → ℤ) (j : Fin k), ¬ (p : ℤ) ∣ c j →
        ‖lam j.castSucc‖ ^ p ≤ ‖∑ i, (c i : F) * (lam i.castSucc ^ p - t ^ (p - 1) * lam i.castSucc)‖ := by
      intro c j hc
      rw [moore_step_sum p c (fun i => lam i.castSucc) t]
      refine moore_step_norm_ge p _ _ _ (norm_nonneg _) fun d => ?_
      have := horth (Fin.snoc (α := fun _ => ℤ) c d) j.castSucc (by simpa using hc)
      rw [Fin.sum_univ_castSucc] at this
      simpa using this
    have hnorm : ∀ j : Fin k, ‖lam j.castSucc ^ p - t ^ (p - 1) * lam j.castSucc‖ = ‖lam j.castSucc‖ ^ p := by
      intro j
      refine le_antisymm (moore_step_norm_le p _ _ (hanti (Fin.le_last _))) ?_
      have := hlow (Pi.single j 1) j (by
        simp only [Pi.single_eq_same]
        exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_dvd_one)
      rw [Finset.sum_eq_single j] at this
      · simpa using this
      · intro b _ hb; simp [hb]
      · simp
    have hih := ih (fun j => lam j.castSucc ^ p - t ^ (p - 1) * lam j.castSucc) (by
      intro a b hab
      simp only [hnorm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hanti (Fin.castSucc_le_castSucc_iff.mpr hab)) _) (by
      intro c j hc
      simp only [hnorm]
      exact hlow c j hc)
    rw [moore_det_succ, norm_mul, norm_mul, ← ht, hih, Fin.prod_univ_castSucc]
    simp only [hnorm, norm_pow, norm_neg, norm_one, one_pow, one_mul, Fin.val_last, Nat.add_sub_cancel,
      Nat.sub_self, pow_zero, pow_one, Fin.val_castSucc, ← ht]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_succ']
    congr 2
    have := j.isLt
    omega

end GlobalTheory.PMonE

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedRowCoefficientMatricesDetNorm
noncomputable section

namespace GlobalTheory.PMonE

open Finset

section Pw

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem coefDet_pw_natCast (n : ℕ) (x : F) : pw p (n : ℤ) x = x ^ p ^ n := by
  simp [pw]

theorem coefDet_pw_pow_p (k : ℤ) (x : F) : pw p k x ^ p = pw p (k + 1) x := by
  unfold pw
  by_cases hk : 0 ≤ k
  · rw [if_pos hk, if_pos (by omega), ← pow_mul, ← pow_succ]
    congr 2; omega
  · rw [if_neg hk]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (-k).toNat = n + 1 := ⟨(-k).toNat - 1, by omega⟩
    rw [hn, Function.iterate_succ_apply']
    have e : ((frobeniusEquiv F p).symm (((frobeniusEquiv F p).symm)^[n] x)) ^ p =
        ((frobeniusEquiv F p).symm)^[n] x := by
      have := frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[n] x)
      rwa [frobenius_def] at this
    rw [e]
    by_cases hk1 : 0 ≤ k + 1
    · rw [if_pos hk1]
      have hn0 : n = 0 := by omega
      have h0 : (k + 1).toNat = 0 := by omega
      rw [hn0, h0]; simp
    · rw [if_neg hk1]; congr 1; omega

theorem coefDet_pw_pow (k : ℤ) (x : F) (a : ℕ) : pw p k x ^ p ^ a = pw p (k + a) x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, ih, coefDet_pw_pow_p]
    congr 1; push_cast; ring

end Pw

section Det

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem coefDet_det_scaled {h : ℕ} (a lam y : Fin h → F) :
    (Matrix.of fun r j : Fin h => (a r * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ))).det =
      (∏ r, a r ^ p ^ (h - (r : ℕ))) * ((∏ j, y j ^ p ^ h) *
        (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det) := by
  rw [← Matrix.det_mul_row (fun j => y j ^ p ^ h), ← Matrix.det_mul_column (fun r => a r ^ p ^ (h - (r : ℕ)))]
  congr 1; ext r j
  simp only [Matrix.of_apply]
  have key : (y j ^ p ^ (r : ℕ)) ^ p ^ (h - (r : ℕ)) = y j ^ p ^ h := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' r.isLt.le]
  rw [mul_pow, mul_pow, key]
  ring

theorem coefDet_det_rev {h : ℕ} (lam : Fin h → F) :
    (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin h)) : ℤ) : F) *
        (Matrix.of fun r j : Fin h => (lam j ^ p) ^ p ^ (r : ℕ)).det := by
  rw [← Matrix.det_permute]
  congr 1; ext r j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply, Fin.val_rev, id]
  rw [← pow_mul, ← pow_succ']
  congr 2; have := r.isLt; omega

theorem coefDet_orth_pow {h : ℕ} (lam : Fin h → F) (hO : Orth p lam) : Orth p (fun j => lam j ^ p) := by
  intro c j hc
  have h1 := hO c j hc
  have e : (∑ i, (c i : F) * lam i) ^ p = ∑ i, (c i : F) * lam i ^ p := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← frobenius_def (R := F) p, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, frobenius_def]
  show ‖lam j ^ p‖ ≤ ‖∑ i, (c i : F) * lam i ^ p‖
  rw [← e, norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 p

theorem coefDet_norm_sign_cast {n : Type} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    ‖((Equiv.Perm.sign σ : ℤ) : F)‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]

end Det

end GlobalTheory.PMonE

end

namespace GlobalTheory.PMonE
open Finset

theorem coefB_det (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] (h : ℕ) (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hl : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hA : Antitone (fun j => ‖lam j‖)) (hO : Orth p lam) (L U : ℕ) :
    ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by
  set c : Fin h → F := fun r => lam r * π r ^ p ^ (r : ℕ) with hc
  have hc0 : ∀ r, c r ≠ 0 := fun r => mul_ne_zero (hl r) (pow_ne_zero _ (hπ r))
  have hA' : Antitone (fun j => ‖(fun j => lam j ^ p) j‖) := fun i j hij => by
    simp only [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hA hij) p
  have hDn : ‖(Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det‖ =
      ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - (j : ℕ)) := by
    rw [coefDet_det_rev, norm_mul, coefDet_norm_sign_cast, one_mul]
    have hM := mooreNorm F p h (fun j => lam j ^ p) hA' (coefDet_orth_pow p lam hO)
    rw [hM]
    refine prod_congr rfl fun j _ => ?_
    rw [norm_pow, ← pow_mul, ← pow_succ']; congr 2; have := j.isLt; omega
  have hD0 : (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det ≠ 0 := by
    rw [← norm_ne_zero_iff, hDn]
    exact (prod_pos fun j _ => pow_pos (norm_pos_iff.mpr (hl j)) _).ne'
  constructor
  · have e : coefB p ϖ lam π L U L = Matrix.of fun r j : Fin h =>
        ((c r)⁻¹ * (lam j * π j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) := by
      ext r j
      simp only [coefB, Matrix.of_apply, term, le_add_iff_nonneg_right, zero_le, if_true, sub_self, neg_zero,
        zpow_zero, mul_one, zero_mul, add_zero, coefDet_pw_natCast, hc]
      rw [div_eq_inv_mul]
    rw [e, coefDet_det_scaled, norm_mul, norm_mul, norm_prod, norm_prod, hDn]
    have hX : ∏ r : Fin h, ‖c r‖ ^ p ^ (h - (r : ℕ)) =
        (∏ j : Fin h, ‖π j‖ ^ p ^ h) * ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - (j : ℕ)) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun r _ => ?_
      rw [hc]
      simp only
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' r.isLt.le, mul_comm]
    have hX0 : ∏ r : Fin h, ‖c r‖ ^ p ^ (h - (r : ℕ)) ≠ 0 :=
      (prod_pos fun r _ => pow_pos (norm_pos_iff.mpr (hc0 r)) _).ne'
    simp only [norm_pow, norm_inv, inv_pow]
    rw [prod_inv_distrib, ← hX, inv_mul_cancel₀ hX0]
  · set y : Fin h → F := fun j => pw p (-((L : ℤ) * h)) (π j) with hy
    have hy0 : ∀ j, y j ≠ 0 := by
      intro j hyj
      have h1 := coefDet_pw_pow p (-((L : ℤ) * h)) (π j) (L * h)
      have h0 : pw p (0 : ℤ) (π j) = π j := by simp [pw]
      rw [show pw p (-((L : ℤ) * h)) (π j) = y j from rfl, hyj,
        zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at h1
      push_cast at h1
      rw [neg_add_cancel, h0] at h1
      exact hπ j h1.symm
    have e : coefB p ϖ lam π L U 0 = Matrix.of fun r j : Fin h =>
        ((ϖ ^ L / c r) * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) := by
      ext r j
      simp only [coefB, Matrix.of_apply, term, zero_le, if_true, hc, hy, coefDet_pw_pow]
      have e1 : ((r : ℕ) : ℤ) + (((0 : ℕ) : ℤ) - L) * h = -((L : ℤ) * h) + ((r : ℕ) : ℤ) := by
        push_cast; ring
      have e2 : ϖ ^ (-(((0 : ℕ) : ℤ) - L)) = ϖ ^ L := by
        rw [show -(((0 : ℕ) : ℤ) - L) = (L : ℤ) by push_cast; ring, zpow_natCast]
      rw [e1, e2]
      congr 1
      ring
    rw [e, coefDet_det_scaled]
    exact mul_ne_zero (prod_ne_zero_iff.mpr fun r _ => pow_ne_zero _ (div_ne_zero (pow_ne_zero _ hϖ) (hc0 r)))
      (mul_ne_zero (prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hy0 j)) hD0)

end GlobalTheory.PMonE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedRowCoefficientMatricesDetNormStatement
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedRowCoefficientMatrices_det_norm : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F), ϖ ≠ 0 → ∀ lam π : Fin h → F, (∀ j, lam j ≠ 0) → (∀ j, π j ≠ 0) → Antitone (fun j => ‖lam j‖) → Orth p lam → ∀ L U : ℕ, ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by
  first | exact @GlobalTheory.PMonE.coefB_det | exact GlobalTheory.PMonE.coefB_det | (intros; apply GlobalTheory.PMonE.coefB_det <;> assumption)
end
