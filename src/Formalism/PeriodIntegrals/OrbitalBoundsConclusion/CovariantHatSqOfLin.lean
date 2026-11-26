module

public import Formalism.PeriodIntegrals.ContractionsCovariantIff
public import Formalism.FormalDegreeBessel.FinalIO

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.QnCovHat2OfLin
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.SumSgnLProdCol
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.GGEq
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.SkipTwoOfGe
open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.FourierDecayAlt.Q

noncomputable def sgnL {r : ℕ} {α : Type*} [DecidableEq α] (x e : Fin r → α) : ℂ :=
  Matrix.det (Matrix.of fun k j => if x k = e j then (1 : ℂ) else 0)

theorem sum_fun_succ {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (f : (Fin (r + 1) → α) → M) :
    ∑ x, f x = ∑ x0 : α, ∑ y : Fin r → α, f (Fin.cons x0 y) := by
  rw [← (Fin.consEquiv fun _ : Fin (r + 1) => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sgnL_eq_sum {r : ℕ} {α : Type*} [DecidableEq α] (x e : Fin r → α) :
    sgnL x e = ∑ σ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (if x = e ∘ σ.symm then 1 else 0) := by
  unfold sgnL
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  congr 1
  simp only [Matrix.of_apply]
  rw [Finset.prod_boole]
  by_cases h : x = e ∘ σ.symm
  · rw [if_pos h, if_pos]
    intro i _
    rw [h]
    simp
  · rw [if_neg h, if_neg]
    intro H
    apply h
    funext j
    have h1 := H (σ.symm j) (Finset.mem_univ _)
    simpa using h1

theorem sum_sgnL {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin r → α) (g : (Fin r → α) → M) :
    ∑ x, sgnL x e • g x = ∑ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) • g (e ∘ π) := by
  simp_rw [sgnL_eq_sum, Finset.sum_smul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun σ => by simp [Equiv.Perm.sign_inv, Equiv.Perm.inv_def])

theorem sum_sgnL_alt {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin r → α) (F : (Fin r → α) → M)
    (hF : ∀ (x : Fin r → α) (π : Equiv.Perm (Fin r)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x) :
    ∑ x, sgnL x e • F x = (r.factorial : ℂ) • F e := by
  rw [sum_sgnL]
  have h1 : ∀ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) • F (e ∘ π) = F e := by
    intro π
    rw [hF, smul_smul]
    have h2 : ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign π : ℤ) : ℂ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    rw [h2, one_smul]
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ]

theorem sum_sgnL_succ {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin (r + 1) → α) (H : (Fin (r + 1) → α) → M) :
    ∑ x, sgnL x e • H x = ∑ j : Fin (r + 1), ((-1 : ℂ) ^ (j : ℕ)) •
      ∑ y : Fin r → α, sgnL y (e ∘ j.succAbove) • H (Fin.cons (e j) y) := by
  have hexp : ∀ (x0 : α) (y : Fin r → α), sgnL (Fin.cons x0 y : Fin (r + 1) → α) e =
      ∑ j : Fin (r + 1), (-1 : ℂ) ^ (j : ℕ) *
        ((if x0 = e j then 1 else 0) * sgnL y (e ∘ j.succAbove)) := by
    intro x0 y
    unfold sgnL
    rw [Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
    congr 2
    all_goals first
      | (simp [Matrix.of_apply]; done)
      | (congr 1; ext k j'; simp [Matrix.submatrix_apply, Matrix.of_apply])
  have step : ∀ (x0 : α) (y : Fin r → α),
      sgnL (Fin.cons x0 y : Fin (r + 1) → α) e • H (Fin.cons x0 y) =
        ∑ j : Fin (r + 1), if x0 = e j then
          ((-1 : ℂ) ^ (j : ℕ) • (sgnL y (e ∘ j.succAbove) • H (Fin.cons (e j) y))) else 0 := by
    intro x0 y
    rw [hexp, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · subst h
      rw [one_mul, mul_smul]
    · rw [zero_mul, mul_zero, zero_smul]
  rw [sum_fun_succ]
  simp_rw [step]
  conv_lhs => arg 2; ext x0; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp

theorem skip_two_of_lt {m : ℕ} (j : Fin (m + 2)) (j' : Fin (m + 1)) (h : Fin.castSucc j' < j) :
    (fun k : Fin m => j.succAbove (j'.succAbove k)) = skip2 (Fin.castSucc j') j := by
  funext k
  apply Fin.ext
  simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ] at h ⊢
  split_ifs <;> (try simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_mk, Fin.lt_def] at *) <;> omega

theorem skip_two_of_ge {m : ℕ} (j : Fin (m + 2)) (j' : Fin (m + 1)) (h : j ≤ Fin.castSucc j') :
    (fun k : Fin m => j.succAbove (j'.succAbove k)) = skip2 j j'.succ := by
  funext k
  apply Fin.ext
  simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.coe_castSucc, Fin.val_succ] at h ⊢
  split_ifs <;> (try simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_mk, Fin.lt_def, Fin.le_def] at *) <;> omega

theorem sum_two {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin (m + 2) → α) (F : (Fin m → α) → M)
    (hF : ∀ (x : Fin m → α) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x)
    (β β' : α → ℂ) :
    ∑ c : Fin (m + 2) → α, sgnL c e • ((β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ)) =
      ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
        ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β (e j) * β' (e (j.succAbove j'))) * (m.factorial : ℂ)) •
          F (fun k => e (j.succAbove (j'.succAbove k))) := by
  refine (sum_sgnL_succ e (fun c => (β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ))).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := sum_sgnL_succ (e ∘ j.succAbove)
    (fun y : Fin (m + 1) → α => (β (e j) * β' (y 0)) • F (fun k => y k.succ))
  simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Function.comp_apply] at h2 ⊢
  rw [h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  have h3 : ∑ z : Fin m → α, sgnL z ((e ∘ j.succAbove) ∘ j'.succAbove) •
      ((β (e j) * β' (e (j.succAbove j'))) • F z) =
      (β (e j) * β' (e (j.succAbove j'))) • ((m.factorial : ℂ) • F ((e ∘ j.succAbove) ∘ j'.succAbove)) := by
    simp_rw [smul_comm (sgnL _ _) (β (e j) * β' (e (j.succAbove j')))]
    rw [← Finset.smul_sum, sum_sgnL_alt _ F hF]
  rw [h3, smul_smul, smul_smul, smul_smul, pow_add]
  congr 1

theorem reindex_pairs {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → M) (β β' : Fin (m + 2) → ℂ) :
    ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
        ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β j * β' (j.succAbove j'))) •
          F (fun k => j.succAbove (j'.succAbove k)) =
      ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
          F (skip2 i i') else 0 := by
  have hR : ∀ i : Fin (m + 2), ∑ i' : Fin (m + 2),
      (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
        F (skip2 i i') else 0) =
      ∑ i' : Fin (m + 2), (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i)) •
        F (skip2 i i') else 0) -
      ∑ i' : Fin (m + 2), (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i * β' i')) •
        F (skip2 i i') else 0) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i' _ => ?_
    split_ifs
    · rw [mul_sub, sub_smul]
    · rw [sub_zero]
  have hL : ∀ j : Fin (m + 2), ∑ j' : Fin (m + 1),
      ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β j * β' (j.succAbove j'))) •
        F (fun k => j.succAbove (j'.succAbove k)) =
      ∑ i : Fin (m + 2), (if i < j then ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (β j * β' i)) •
        F (skip2 i j) else 0) -
      ∑ i' : Fin (m + 2), (if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ)) * (β j * β' i')) •
        F (skip2 j i') else 0) := by
    intro j
    rw [Fin.sum_univ_castSucc (f := fun i => if i < j then ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) *
        (β j * β' i)) • F (skip2 i j) else 0),
      Fin.sum_univ_succ (f := fun i' => if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ)) *
        (β j * β' i')) • F (skip2 j i') else 0)]
    simp only [not_lt.mpr (Fin.le_last j), Fin.not_lt_zero, if_false, add_zero, zero_add]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases h : Fin.castSucc j' < j
    · have h' : ¬ j < j'.succ := by
        rw [← Fin.le_castSucc_iff]
        exact not_le.mpr h
      rw [if_pos h, if_neg h', sub_zero, Fin.succAbove_of_castSucc_lt _ _ h, skip_two_of_lt j j' h,
        Fin.val_castSucc]
      congr 1
      ring
    · have hle : j ≤ Fin.castSucc j' := not_lt.mp h
      have h' : j < j'.succ := Fin.le_castSucc_iff.mp hle
      rw [if_neg h, if_pos h', zero_sub, Fin.succAbove_of_le_castSucc _ _ hle, skip_two_of_ge j j' hle,
        Fin.val_succ, ← neg_smul]
      congr 1
      ring
  rw [Finset.sum_congr rfl fun j _ => hL j, Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun i _ => hR i, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]

end PI.QnCovHat2W
end

open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem one_side {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → M)
    (hF : ∀ (x : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x)
    (β β' : Fin (m + 2) → ℂ) :
    ∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id • ((β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ)) =
      (m.factorial : ℂ) • ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
          F (skip2 i i') else 0 := by
  rw [sum_two id F hF, ← reindex_pairs F β β', Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp only [id, smul_smul]
  congr 1
  ring

noncomputable def GG {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M) (β β' a a' : Fin (m + 2) → ℂ) : M :=
  ∑ c : Fin (m + 2) → Fin (m + 2), ∑ d : Fin (m + 2) → Fin (m + 2),
    (sgnL c id * sgnL d id * (β (c 0) * β' (c 1)) * (a (d 0) * a' (d 1))) •
      F (fun k => c k.succ.succ) (fun k => d k.succ.succ)

theorem GG_eq {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M)
    (hR : ∀ (x y : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) y = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x y)
    (hC : ∀ (x y : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F x (y ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x y)
    (β β' a a' : Fin (m + 2) → ℂ) :
    GG F β β' a a' = ((m.factorial : ℂ) * m.factorial) •
      ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2), ∑ j : Fin (m + 2), ∑ j' : Fin (m + 2),
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (β i * β' i' - β i' * β' i) *
            (a j * a' j' - a j' * a' j)) • F (skip2 i i') (skip2 j j')
        else 0 := by
  let Φ : (Fin m → Fin (m + 2)) → M := fun x =>
    ∑ d : Fin (m + 2) → Fin (m + 2), sgnL d id • ((a (d 0) * a' (d 1)) • F x (fun k => d k.succ.succ))
  have hΦ : ∀ (x : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      Φ (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • Φ x := by
    intro x π
    simp only [Φ, hR, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm _ (sgnL d id), smul_comm ((Equiv.Perm.sign π : ℤ) : ℂ) (a (d 0) * a' (d 1))]
  have h1 : GG F β β' a a' =
      ∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id • ((β (c 0) * β' (c 1)) • Φ (fun k => c k.succ.succ)) := by
    unfold GG
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Φ, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    ring
  have h2 : ∀ i i' : Fin (m + 2), Φ (skip2 i i') = (m.factorial : ℂ) • ∑ j : Fin (m + 2), ∑ j' : Fin (m + 2),
      if j < j' then ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (a j' * a' j - a j * a' j')) •
        F (skip2 i i') (skip2 j j') else 0 := by
    intro i i'
    exact one_side (fun y => F (skip2 i i') y) (fun y π => hC _ y π) a a'
  rw [h1, one_side Φ hΦ β β', Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  by_cases hi : i < i'
  · simp only [hi, if_true, true_and, h2, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases hj : j < j'
    · simp only [hj, if_true, smul_smul]
      congr 1
      rw [pow_add, pow_add, pow_add, pow_add]
      ring
    · simp [hj]
  · simp [hi]

end PI.QnCovHat2W
end

open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem sum_rows {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (p : Fin (m + 2) → α → ℂ) (f g : α → ℂ) (Φ : (Fin m → α) → M) :
    ∑ x : Fin (m + 2) → α, (f (x 0) * g (x 1) * ∏ k, p k (x k)) • Φ (fun k => x k.succ.succ) =
      ((∑ z, f z * p 0 z) * (∑ z, g z * p 1 z)) •
        ∑ y : Fin m → α, (∏ k, p k.succ.succ (y k)) • Φ y := by
  rw [sum_fun_succ]
  simp_rw [sum_fun_succ (r := m)]
  simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Fin.prod_univ_succ, Fin.succ_zero_eq_one]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_smul, Finset.smul_sum, smul_smul]
  symm
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun x1 _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun y _ => ?_
  congr 1
  ring

theorem sum_sgnL_prod_row {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → Fin N) :
    ∑ c : Fin N → Fin N, sgnL c id * ∏ k, P (x k) (c k) = sgnL x id * P.det := by
  have h1 := sum_sgnL (M := ℂ) (id : Fin N → Fin N) (fun c => ∏ k, P (x k) (c k))
  simp only [smul_eq_mul] at h1
  rw [h1]
  have h2 : (Matrix.of fun i k => P (x k) i).det = sgnL x id * P.det := by
    have h3 : (Matrix.of fun i k => P (x k) i) =
        ((Matrix.of fun k j => if x k = id j then (1 : ℂ) else 0) * P).transpose := by
      ext i k
      simp [Matrix.mul_apply]
    rw [h3, Matrix.det_transpose, Matrix.det_mul]
    rfl
  rw [← h2, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp

theorem sum_sgnL_prod_col {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → Fin N) :
    ∑ d : Fin N → Fin N, sgnL d id * ∏ k, Q (d k) (y k) = sgnL y id * Q.det := by
  have h1 := sum_sgnL (M := ℂ) (id : Fin N → Fin N) (fun d => ∏ k, Q (d k) (y k))
  simp only [smul_eq_mul] at h1
  rw [h1]
  have h2 : (Matrix.of fun i k => Q i (y k)).det = sgnL y id * Q.det := by
    have h3 : (Matrix.of fun i k => Q i (y k)) =
        Q * (Matrix.of fun k j => if y k = id j then (1 : ℂ) else 0).transpose := by
      ext i k
      simp [Matrix.mul_apply]
    rw [h3, Matrix.det_mul, Matrix.det_transpose, mul_comm]
    rfl
  rw [← h2, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp

theorem sum_swap4 {ι κ : Type*} [Fintype ι] [Fintype κ] {M : Type*} [AddCommMonoid M]
    (f : ι → ι → κ → κ → M) :
    ∑ c, ∑ d, ∑ x, ∑ y, f c d x y = ∑ x, ∑ y, ∑ c, ∑ d, f c d x y := by
  calc ∑ c, ∑ d, ∑ x, ∑ y, f c d x y = ∑ c, ∑ x, ∑ d, ∑ y, f c d x y :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
    _ = ∑ x, ∑ c, ∑ d, ∑ y, f c d x y := Finset.sum_comm
    _ = ∑ x, ∑ c, ∑ y, ∑ d, f c d x y :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))
    _ = ∑ x, ∑ y, ∑ c, ∑ d, f c d x y := Finset.sum_congr rfl (fun x _ => Finset.sum_comm)

theorem GG_cov {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F F' : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M)
    (P Q : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
    (hLin : ∀ x y : Fin m → Fin (m + 2), F' x y =
      ∑ c : Fin m → Fin (m + 2), ∑ d : Fin m → Fin (m + 2),
        ((∏ k, P (c k) (x k)) * ∏ k, Q (y k) (d k)) • F c d)
    (β β' a a' : Fin (m + 2) → ℂ) :
    GG F' (β ᵥ* P) (β' ᵥ* P) (Q *ᵥ a) (Q *ᵥ a') = (P.det * Q.det) • GG F β β' a a' := by
  have hv : ∀ (v : Fin (m + 2) → ℂ) (i : Fin (m + 2)), (v ᵥ* P) i = ∑ z, v z * P z i := by
    intro v i
    simp [Matrix.vecMul, dotProduct]
  have hw : ∀ (v : Fin (m + 2) → ℂ) (i : Fin (m + 2)), (Q *ᵥ v) i = ∑ z, v z * Q i z := by
    intro v i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have key : ∀ c d : Fin (m + 2) → Fin (m + 2),
      (sgnL c id * sgnL d id * ((β ᵥ* P) (c 0) * (β' ᵥ* P) (c 1)) *
          ((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1))) •
        F' (fun k => c k.succ.succ) (fun k => d k.succ.succ) =
      ∑ x : Fin (m + 2) → Fin (m + 2), ∑ y : Fin (m + 2) → Fin (m + 2),
        (sgnL c id * (∏ k, P (x k) (c k)) * (sgnL d id * ∏ k, Q (d k) (y k)) *
          (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1)))) •
            F (fun k => x k.succ.succ) (fun k => y k.succ.succ) := by
    intro c d
    have e1 : ∀ x : Fin (m + 2) → Fin (m + 2),
        ∑ y : Fin (m + 2) → Fin (m + 2), (a (y 0) * a' (y 1) * ∏ k, Q (d k) (y k)) •
            F (fun k => x k.succ.succ) (fun k => y k.succ.succ) =
          ((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F (fun k => x k.succ.succ) y := by
      intro x
      rw [sum_rows (fun k z => Q (d k) z) a a' (fun y => F (fun k => x k.succ.succ) y), hw a, hw a']
    have e2 : ∑ x : Fin (m + 2) → Fin (m + 2), (β (x 0) * β' (x 1) * ∏ k, P (x k) (c k)) •
          (((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F (fun k => x k.succ.succ) y) =
        ((β ᵥ* P) (c 0) * (β' ᵥ* P) (c 1)) • ∑ x : Fin m → Fin (m + 2), (∏ k, P (x k) (c k.succ.succ)) •
          (((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F x y) := by
      rw [sum_rows (fun k z => P z (c k)) β β' (fun x => ((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F x y), hv β, hv β']
    have e3 : (∑ x : Fin (m + 2) → Fin (m + 2), ∑ y : Fin (m + 2) → Fin (m + 2),
        (sgnL c id * (∏ k, P (x k) (c k)) * (sgnL d id * ∏ k, Q (d k) (y k)) *
          (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1)))) •
            F (fun k => x k.succ.succ) (fun k => y k.succ.succ)) =
        (sgnL c id * sgnL d id) • ∑ x : Fin (m + 2) → Fin (m + 2),
          (β (x 0) * β' (x 1) * ∏ k, P (x k) (c k)) • ∑ y : Fin (m + 2) → Fin (m + 2),
            (a (y 0) * a' (y 1) * ∏ k, Q (d k) (y k)) •
              F (fun k => x k.succ.succ) (fun k => y k.succ.succ) := by
      simp only [Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      congr 1
      ring
    rw [e3]
    simp_rw [e1]
    rw [e2, hLin]
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    ring
  unfold GG
  simp_rw [key]
  rw [sum_swap4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [← Finset.sum_smul, smul_smul]
  congr 1
  have hcd : ∑ c : Fin (m + 2) → Fin (m + 2), ∑ d : Fin (m + 2) → Fin (m + 2),
      sgnL c id * (∏ k, P (x k) (c k)) * (sgnL d id * ∏ k, Q (d k) (y k)) *
        (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1))) =
      (∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id * ∏ k, P (x k) (c k)) *
        (∑ d : Fin (m + 2) → Fin (m + 2), sgnL d id * ∏ k, Q (d k) (y k)) *
          (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1))) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
  rw [hcd, sum_sgnL_prod_row, sum_sgnL_prod_col]
  ring

end PI.QnCovHat2W
end

open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem qminor_row_alt {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (u : ℂ)
    (x y : Fin m → Fin n) (π : Equiv.Perm (Fin m)) :
    qminor E (x ∘ π) y u = ((Equiv.Perm.sign π : ℤ) : ℂ) • qminor E x y u := by
  rw [quantumMinorRowSkew_holds A n m E x y π u, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem qminor_col_alt {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (u : ℂ) (x y : Fin m → Fin n) (π : Equiv.Perm (Fin m)) :
    qminor E x (y ∘ π) u = ((Equiv.Perm.sign π : ℤ) : ℂ) • qminor E x y u := by
  rw [quantumMinorColSkew_holds A n m E hE x y π u, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem qnCovHat2_of_lin (hLin : PI.QnCovLin) : PI.QnCovHat2 := by
  intro A _ _ n E P Q hE hQP hPQ u a a' β β'
  rcases n with _ | _ | m
  · simp [chat2A]
  · simp [chat2A]
  · have hE' : GlRel (Econj E P Q) := glRelAd A (m + 2) E P Q hE hQP
    have h1 := GG_eq (fun x y : Fin m → Fin (m + 2) => qminor E x y u)
      (fun x y π => qminor_row_alt E u x y π) (fun x y π => qminor_col_alt E hE u x y π) β β' a a'
    have h2 := GG_eq (fun x y : Fin m → Fin (m + 2) => qminor (Econj E P Q) x y u)
      (fun x y π => qminor_row_alt (Econj E P Q) u x y π)
      (fun x y π => qminor_col_alt (Econj E P Q) hE' u x y π) (β ᵥ* P) (β' ᵥ* P) (Q *ᵥ a) (Q *ᵥ a')
    have h3 := GG_cov (fun x y : Fin m → Fin (m + 2) => qminor E x y u)
      (fun x y : Fin m → Fin (m + 2) => qminor (Econj E P Q) x y u) P Q
      (fun x y => hLin A (m + 2) m E P Q hQP x y u) β β' a a'
    have hdet : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
    rw [hdet, one_smul, h1, h2] at h3
    have hne : ((m.factorial : ℂ) * m.factorial) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
        (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
    have h4 := congrArg (fun z => ((m.factorial : ℂ) * m.factorial)⁻¹ • z) h3
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
    exact h4

end PI.QnCovHat2W
end

theorem covariant_hat_sq_of_lin : PI.QnCovLin → PI.QnCovHat2 := PI.QnCovHat2W.qnCovHat2_of_lin
