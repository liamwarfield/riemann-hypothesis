module

public import Formalism.PeriodIntegrals.QmDefs
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantVectorMove.SumPermsSignSquared
section -- merged from Formalism.PeriodIntegrals.QmMove
namespace PI

def QmMove : Prop := MoveVec ∧ MoveCov

end PI
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantVectorMove.MoveOperatorCovariance
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantVectorMove.SumPermEqSumFirstColumnSplit
open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmMove

theorem prod_diff {A : Type*} [Ring A] {t : ℕ} (f g : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k) :
    (List.ofFn f).prod - (List.ofFn g).prod =
      ((List.ofFn f).take i).prod *
        (f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩ - g ⟨i, by omega⟩ * g ⟨i + 1, hi⟩) *
        ((List.ofFn f).drop (i + 2)).prod := by
  rw [prod_ofFn_split_pair f i hi, prod_ofFn_split_pair g i hi, take_ofFn_congr g f i (fun k hk => h k (by omega) (by omega)),
    drop_ofFn_congr g f (i + 2) (fun k hk => h k (by omega) (by omega))]
  noncomm_ring

theorem sgn_mul_swap {A : Type*} [Ring A] {t : ℕ} (s : Equiv.Perm (Fin t))
    (hs : Equiv.Perm.sign s = -1) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign (τ * s) : ℤ) : A) = -((Equiv.Perm.sign τ : ℤ) : A) := by
  rw [Equiv.Perm.sign_mul, hs]
  push_cast
  simp

theorem step {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (s : Equiv.Perm (Fin t))
    (hs : Equiv.Perm.sign s = -1) (P Q X : Equiv.Perm (Fin t) → A)
    (hX : ∀ τ, X (τ * s) = X τ) (hPQ : ∀ τ, P (τ * s) - Q τ = X τ) :
    ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * Q τ = -∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * P τ := by
  have hz : ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * X τ = 0 := by
    have h1 : ∑ τ, ((Equiv.Perm.sign (τ * s) : ℤ) : A) * X (τ * s) =
        ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * X τ :=
      Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun τ => rfl)
    simp only [hX, sgn_mul_swap s hs, neg_mul, Finset.sum_neg_distrib] at h1
    exact eq_zero_of_eq_neg_self_of_algebra_complex _ h1.symm
  have h2 : ∑ τ, ((Equiv.Perm.sign (τ * s) : ℤ) : A) * P (τ * s) =
      ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * P τ :=
    Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun τ => rfl)
  have hP : ∀ τ, P (τ * s) = Q τ + X τ := fun τ => by rw [← hPQ τ]; abel
  simp only [hP, sgn_mul_swap s hs, neg_mul, mul_add, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, hz] at h2
  rw [← h2]
  simp only [neg_zero, add_zero, neg_neg]

theorem chain {A : Type*} [Ring A] (S : ℕ → A) : ∀ m : ℕ, (∀ p < m, S (p + 1) = -S p) →
    S m = (((-1 : ℤ) ^ m : ℤ) : A) * S 0
  | 0, _ => by simp
  | m + 1, h => by
    rw [h m (by omega), chain S m (fun p hp => h p (by omega))]
    push_cast
    rw [pow_succ]
    simp [mul_neg, neg_mul]

def phi0 (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (Fin.cycleRange p.1).symm * Equiv.Perm.decomposeFin.symm (0, p.2)

theorem firstColumnSplit_zero (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) : phi0 m (j, ρ) 0 = j := by
  simp [phi0, Equiv.Perm.mul_apply]

theorem firstColumnSplit_succ (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) (k : Fin m) :
    phi0 m (j, ρ) k.succ = j.succAbove (ρ k) := by
  simp [phi0, Equiv.Perm.mul_apply]

theorem sign_firstColumnSplit (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (phi0 m (j, ρ)) = (-1) ^ (j : ℕ) * Equiv.Perm.sign ρ := by
  simp [phi0, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign]

theorem firstColumnSplit_bijective (m : ℕ) : Function.Bijective (phi0 m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    have hj : j = j' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ 0) h
      simpa [firstColumnSplit_zero] using this
    subst hj
    have : τ = τ' := by
      refine Equiv.ext fun k => ?_
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ k.succ) h
      simp only [firstColumnSplit_succ] at this
      exact Fin.succAbove_right_inj.mp this
    rw [this]
  · simp [Fintype.card_prod, Fintype.card_perm, Nat.factorial_succ]

theorem sum_perm_eq_sum_firstColumnSplit {M : Type*} [AddCommMonoid M] (m : ℕ) (g : Equiv.Perm (Fin (m + 1)) → M) :
    ∑ τ, g τ = ∑ j : Fin (m + 1), ∑ ρ : Equiv.Perm (Fin m), g (phi0 m (j, ρ)) := by
  rw [(Fintype.sum_bijective (phi0 m) (firstColumnSplit_bijective m) (fun p => g (phi0 m p)) g (fun _ => rfl)).symm,
    Fintype.sum_prod_type]

theorem sum_phiL {M : Type*} [AddCommMonoid M] (m : ℕ) (g : Equiv.Perm (Fin (m + 1)) → M) :
    ∑ τ, g τ = ∑ j : Fin (m + 1), ∑ ρ : Equiv.Perm (Fin m), g (lastColumnSplit m (j, ρ)) := by
  rw [(Fintype.sum_bijective (lastColumnSplit m) (lastColumnSplit_bijective m) (fun p => g (lastColumnSplit m p)) g
    (fun _ => rfl)).symm, Fintype.sum_prod_type]

theorem phiL_castSucc (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) (k : Fin m) :
    lastColumnSplit m (j, ρ) k.castSucc = j.succAbove (ρ k) := by
  simp [lastColumnSplit, Equiv.Perm.mul_apply, extendLast_castSucc, cycleToLast_castSucc]

theorem phiL_last (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    lastColumnSplit m (j, ρ) (Fin.last m) = j := by
  simp [lastColumnSplit, Equiv.Perm.mul_apply, extendLast_last, cycleToLast_last]

theorem phiL_sign (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (lastColumnSplit m (j, ρ)) = (-1) ^ (m - (j : ℕ)) * Equiv.Perm.sign ρ := by
  simp [lastColumnSplit, Equiv.Perm.sign_mul, sign_cycleToLast, sign_extendLast]

theorem fact_cancel {A : Type*} [Ring A] [Algebra ℂ A] (m : ℕ) (X Y : A)
    (h : (m.factorial : A) * X = (m.factorial : A) * Y) : X = Y := by
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have e : ∀ Z : A, Z = algebraMap ℂ A ((m.factorial : ℂ)⁻¹) * ((m.factorial : A) * Z) := by
    intro Z
    rw [← mul_assoc, ← map_natCast (algebraMap ℂ A), ← map_mul, inv_mul_cancel₀ hm, map_one, one_mul]
  rw [e X, e Y, h]

theorem neg_one_pow_sub (m j : ℕ) (hj : j ≤ m) :
    ((-1 : ℤ) ^ (m - j) : ℤ) = (-1) ^ m * (-1) ^ j := by
  rw [← pow_add]
  rw [show m + j = (m - j) + 2 * j by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

theorem icomm {A : Type*} [Ring A] (z : ℤ) (x : A) : (z : A) * x = x * (z : A) :=
  (Int.cast_commute z x).eq

end PI.UnitaryGroupMassFormula.QmMove
end
end

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmMove

def extN {n m : ℕ} (b : Fin m → Fin n) (d : Fin n) (k : ℕ) : Fin n :=
  if h : k < m then b ⟨k, h⟩ else d

theorem extN_lt {n m : ℕ} (b : Fin m → Fin n) (d : Fin n) (k : Fin m) : extN b d k = b k := by
  simp [extN, k.isLt]

theorem sgnlem {A : Type*} [Ring A] (z z' : ℤ) (x y : A) :
    ((z * z' : ℤ) : A) * (x * y) = (z : A) * (x * ((z' : A) * y)) := by
  rw [Int.cast_mul, mul_assoc, ← mul_assoc (z' : A) x y, (Int.cast_commute z' x).eq, mul_assoc]

section Cov
variable {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (η : Fin n → A)
  (a : Fin (m + 1) → Fin n) (b : Fin m → Fin n) (w : ℂ)

def Fc (p : ℕ) (τ : Equiv.Perm (Fin (m + 1))) (q : Fin (m + 1)) : A :=
  if (q : ℕ) = p then η (a (τ q))
  else Tm E (w - ((q : ℕ) : ℂ)) (a (τ q)) (extN b (a 0) (if (q : ℕ) < p then (q : ℕ) else (q : ℕ) - 1))

def Nc (p : ℕ) : A := ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * (List.ofFn (Fc E η a b w p τ)).prod


omit [Algebra ℂ A] in
def symC (d x c : Fin n) : A := (if x = d then η c else 0) + (if c = d then η x else 0)

theorem midC (hη : ∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0)
    (v v' : ℂ) (hv : v = v' + 1) (x d c : Fin n) :
    η c * Tm E v' x d - Tm E v x d * η c = -symC η d x c := by
  subst hv
  have h := hη x d c
  have hc : η c * algebraMap ℂ A v' = algebraMap ℂ A v' * η c := (Algebra.commutes _ _).symm
  have hk : η c * E x d = E x d * η c - (if c = d then η x else 0) := by
    have e : (if c = d then η x else 0) = (if d = c then η x else 0) := by
      by_cases hcd : c = d
      · rw [if_pos hcd, if_pos hcd.symm]
      · rw [if_neg hcd, if_neg (Ne.symm hcd)]
    rw [e, ← h]
    abel
  simp only [Tm, symC, mul_add, add_mul, hk]
  by_cases hxd : x = d
  · simp only [if_pos hxd]
    rw [hc, map_add (f := _), map_one, add_mul, one_mul]
    abel
  · simp only [if_neg hxd, mul_zero, zero_mul, zero_add]
    abel

private lemma list_prod_eq_take_mul_pair_mul_drop {M : Type*} [Monoid M] (l : List M) (i : ℕ) (h : i + 1 < l.length) :
    l.prod = (l.take i).prod * (l[i] * l[i + 1]) * (l.drop (i + 1 + 1)).prod := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero =>
      cases l with
      | nil => simp at h
      | cons y l =>
        rw [List.getElem_cons_succ, List.getElem_cons_zero, List.getElem_cons_zero, List.take_zero,
          List.drop_succ_cons, List.drop_succ_cons, List.drop_zero, List.prod_nil, one_mul,
          List.prod_cons, List.prod_cons, mul_assoc]
    | succ i =>
      have h' : i + 1 < l.length := by simp only [List.length_cons] at h; omega
      rw [List.prod_cons, ih i h', List.take_succ_cons, List.prod_cons, List.getElem_cons_succ,
        List.getElem_cons_succ, List.drop_succ_cons]
      simp only [mul_assoc]

private lemma sum_perm_eq_zero_of_mul_right_eq_neg {B : Type*} [Ring B] [Algebra ℂ B] {k : ℕ} (s : Equiv.Perm (Fin k))
    (G : Equiv.Perm (Fin k) → B) (h : ∀ τ, G (τ * s) = -G τ) : ∑ τ, G τ = 0 := by
  have h1 : ∑ τ, G τ = -∑ τ, G τ := by
    rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp (Equiv.mulRight s)]
    exact Finset.sum_congr rfl fun τ _ => h τ
  have h2 : ∑ τ, G τ + ∑ τ, G τ = 0 := by
    rw [← sub_neg_eq_add, ← h1, sub_self]
  calc ∑ τ, G τ = (2 : ℂ)⁻¹ • ((2 : ℂ) • ∑ τ, G τ) := by
        rw [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul]
    _ = 0 := by rw [two_smul, h2, smul_zero]

theorem stepC (hη : ∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0)
    (p : ℕ) (hp : p < m) : Nc E η a b w (p + 1) = -Nc E η a b w p := by
  have hp0 : p < m + 1 := by omega
  have hp1 : p + 1 < m + 1 := by omega
  obtain ⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin (m + 1)), s = Equiv.swap ⟨p, hp0⟩ ⟨p + 1, hp1⟩ := ⟨_, rfl⟩
  have hne : (⟨p, hp0⟩ : Fin (m + 1)) ≠ ⟨p + 1, hp1⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hsP : s ⟨p, hp0⟩ = ⟨p + 1, hp1⟩ := by rw [hs, Equiv.swap_apply_left]
  have hsP1 : s ⟨p + 1, hp1⟩ = ⟨p, hp0⟩ := by rw [hs, Equiv.swap_apply_right]
  have hsq : ∀ q : Fin (m + 1), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 → s q = q := by
    intro q h1 h2
    rw [hs]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))
  have hsgn : ∀ τ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign (τ * s) : ℤ) : A) = -((Equiv.Perm.sign τ : ℤ) : A) := by
    intro τ
    rw [hs, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, mul_neg_one, Units.val_neg, Int.cast_neg]
  have hoff : ∀ (τ : Equiv.Perm (Fin (m + 1))) (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fc E η a b w (p + 1) τ q = Fc E η a b w p (τ * s) q := by
    intro τ q h1 h2
    simp only [Fc, Equiv.Perm.mul_apply, hsq q h1 h2, if_neg h1, if_neg h2]
    by_cases hq : (q : ℕ) < p
    · rw [if_pos hq, if_pos (show (q : ℕ) < p + 1 by omega)]
    · rw [if_neg hq, if_neg (show ¬ (q : ℕ) < p + 1 by omega)]
  have hoff2 : ∀ (τ : Equiv.Perm (Fin (m + 1))) (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fc E η a b w (p + 1) (τ * s) q = Fc E η a b w (p + 1) τ q := by
    intro τ q h1 h2
    simp only [Fc, Equiv.Perm.mul_apply, hsq q h1 h2]
  have hT : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w p (τ * s))).take p =
      (List.ofFn (Fc E η a b w (p + 1) τ)).take p := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp only [List.length_take, List.length_ofFn] at h1
    exact (hoff τ _ (by show k ≠ p; omega) (by show k ≠ p + 1; omega)).symm
  have hD : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w p (τ * s))).drop (p + 1 + 1) =
      (List.ofFn (Fc E η a b w (p + 1) τ)).drop (p + 1 + 1) := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact (hoff τ _ (by show p + 1 + 1 + k ≠ p; omega) (by show p + 1 + 1 + k ≠ p + 1; omega)).symm
  have hT2 : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w (p + 1) (τ * s))).take p =
      (List.ofFn (Fc E η a b w (p + 1) τ)).take p := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp only [List.length_take, List.length_ofFn] at h1
    exact hoff2 τ _ (by show k ≠ p; omega) (by show k ≠ p + 1; omega)
  have hD2 : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w (p + 1) (τ * s))).drop (p + 1 + 1) =
      (List.ofFn (Fc E η a b w (p + 1) τ)).drop (p + 1 + 1) := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact hoff2 τ _ (by show p + 1 + 1 + k ≠ p; omega) (by show p + 1 + 1 + k ≠ p + 1; omega)
  have e1 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w (p + 1) τ ⟨p, hp0⟩ =
      Tm E (w - (p : ℂ)) (a (τ ⟨p, hp0⟩)) (extN b (a 0) p) := by
    intro τ; simp [Fc]
  have e2 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w (p + 1) τ ⟨p + 1, hp1⟩ =
      η (a (τ ⟨p + 1, hp1⟩)) := by
    intro τ; simp [Fc]
  have e3 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w p (τ * s) ⟨p, hp0⟩ =
      η (a (τ ⟨p + 1, hp1⟩)) := by
    intro τ; simp [Fc, hsP]
  have e4 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w p (τ * s) ⟨p + 1, hp1⟩ =
      Tm E (w - ((p : ℂ) + 1)) (a (τ ⟨p, hp0⟩)) (extN b (a 0) p) := by
    intro τ; simp [Fc, hsP1]
  have key : ∀ τ : Equiv.Perm (Fin (m + 1)),
      (List.ofFn (Fc E η a b w (p + 1) τ)).prod - (List.ofFn (Fc E η a b w p (τ * s))).prod =
        ((List.ofFn (Fc E η a b w (p + 1) τ)).take p).prod *
          symC η (extN b (a 0) p) (a (τ ⟨p, hp0⟩)) (a (τ ⟨p + 1, hp1⟩)) *
          ((List.ofFn (Fc E η a b w (p + 1) τ)).drop (p + 1 + 1)).prod := by
    intro τ
    rw [list_prod_eq_take_mul_pair_mul_drop (List.ofFn (Fc E η a b w (p + 1) τ)) p (by simp; omega),
      list_prod_eq_take_mul_pair_mul_drop (List.ofFn (Fc E η a b w p (τ * s))) p (by simp; omega), hT τ, hD τ,
      ← sub_mul, ← mul_sub]
    congr 2
    simp only [List.getElem_ofFn]
    rw [e1 τ, e2 τ, e3 τ, e4 τ]
    have h := congrArg Neg.neg (midC E η hη (w - (p : ℂ)) (w - ((p : ℂ) + 1)) (by ring)
      (a (τ ⟨p, hp0⟩)) (extN b (a 0) p) (a (τ ⟨p + 1, hp1⟩)))
    rw [neg_sub, neg_neg] at h
    exact h
  have hA : Nc E η a b w p = ∑ τ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign (τ * s) : ℤ) : A) * (List.ofFn (Fc E η a b w p (τ * s))).prod :=
    (Equiv.sum_comp (Equiv.mulRight s)
      (fun τ => ((Equiv.Perm.sign τ : ℤ) : A) * (List.ofFn (Fc E η a b w p τ)).prod)).symm
  rw [hA, Nc]
  simp only [hsgn, neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← mul_sub, key]
  apply sum_perm_eq_zero_of_mul_right_eq_neg s
  intro τ
  have hS2 : symC η (extN b (a 0) p) (a ((τ * s) ⟨p, hp0⟩)) (a ((τ * s) ⟨p + 1, hp1⟩)) =
      symC η (extN b (a 0) p) (a (τ ⟨p, hp0⟩)) (a (τ ⟨p + 1, hp1⟩)) := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsP, hsP1, symC, symC, add_comm]
  simp only [hsgn, hT2, hD2, hS2, neg_mul]

private lemma sum_perm_fin_succ_eq_sum_cycleRange_decomposeFin {M : Type*} [AddCommMonoid M] {k : ℕ} (π : Equiv.Perm (Fin (k + 1)))
    (F : Equiv.Perm (Fin (k + 1)) → M) :
    ∑ τ, F τ = ∑ j : Fin (k + 1), ∑ σ : Equiv.Perm (Fin k),
      F (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * π) := by
  have hb : Function.Bijective (fun x : Fin (k + 1) × Equiv.Perm (Fin k) =>
      x.1.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, x.2) * π) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [Fintype.card_perm, Nat.factorial_succ]⟩
    rintro ⟨j, σ⟩ ⟨j', σ'⟩ h
    have h1 : j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) =
        j'.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ') := mul_right_cancel h
    have hj : j = j' := by
      have := congrArg (fun e : Equiv.Perm (Fin (k + 1)) => e 0) h1
      simpa [Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero] using this
    subst hj
    have h3 := (Equiv.injective Equiv.Perm.decomposeFin.symm) (mul_left_cancel h1)
    rw [show σ = σ' from congrArg Prod.snd h3]
  rw [← Fintype.sum_prod_type']
  exact (hb.sum_comp F).symm

theorem Nc_zero : Nc E η a b w 0 = ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (η (a j) * qminor E (a ∘ j.succAbove) b (w - 1)) := by
  simp only [Nc, sum_perm_fin_succ_eq_sum_cycleRange_decomposeFin (1 : Equiv.Perm (Fin (m + 1))), mul_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminor, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hs : ((Equiv.Perm.sign (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ)) : ℤˣ) : ℤ) =
      (-1 : ℤ) ^ (j : ℕ) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign,
      if_pos rfl, one_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have h0 : Fc E η a b w 0 (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ)) 0 = η (a j) := by
    simp [Fc, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]
  have h1 : (fun i : Fin m => Fc E η a b w 0 (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ)) i.succ) =
      fun k : Fin m => Tm E (w - 1 - ((k : ℕ) : ℂ)) ((a ∘ j.succAbove) (σ k)) (b k) := by
    funext k
    have hw : w - ((((k : ℕ) + 1 : ℕ)) : ℂ) = w - 1 - ((k : ℕ) : ℂ) := by push_cast; ring
    simp only [Fc, Fin.val_succ, if_neg (Nat.succ_ne_zero _), if_neg (Nat.not_lt_zero _),
      Nat.add_sub_cancel, hw, extN_lt, Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_self, Equiv.refl_apply, Fin.cycleRange_symm_succ, Function.comp_apply]
  rw [List.ofFn_succ, List.prod_cons, hs, sgnlem, h0, h1]

theorem Nc_last : Nc E η a b w m = ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (m - (j : ℕ)) : ℤ) : A) * (qminor E (a ∘ j.succAbove) b w * η (a j)) := by
  simp only [Nc, sum_perm_fin_succ_eq_sum_cycleRange_decomposeFin (finRotate (m + 1))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminor, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hjm := j.isLt
  have hu : Equiv.Perm.sign (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1)) =
      (-1) ^ (m - (j : ℕ)) * Equiv.Perm.sign σ := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
      Equiv.Perm.decomposeFin.symm_sign, if_pos rfl, one_mul, sign_finRotate, Nat.add_sub_cancel, mul_right_comm, ← pow_add,
      show (j : ℕ) + m = (m - (j : ℕ)) + 2 * (j : ℕ) by omega, pow_add, pow_mul, Int.units_sq, one_pow,
      mul_one]
  have hs : ((Equiv.Perm.sign (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1)) : ℤˣ) : ℤ) =
      (-1 : ℤ) ^ (m - (j : ℕ)) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
    rw [hu, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have h0 : Fc E η a b w m (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1))
      (Fin.last m) = η (a j) := by
    simp [Fc, finRotate_last, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]
  have h1 : (fun i : Fin m => Fc E η a b w m
      (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1)) i.castSucc) =
      fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) ((a ∘ j.succAbove) (σ k)) (b k) := by
    funext k
    have hk := k.isLt
    have hr : finRotate (m + 1) k.castSucc = k.succ := by
      ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last k).ne]
      simp
    simp only [Fc, Fin.coe_castSucc, if_neg (Nat.ne_of_lt hk), if_pos hk, extN_lt, Equiv.Perm.mul_apply, hr,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, Fin.cycleRange_symm_succ,
      Function.comp_apply]
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
    hs, h0, h1]
  simp only [Int.cast_mul, mul_assoc]

end Cov

theorem move_operator_covariance : PI.MoveCov := by
  unfold PI.MoveCov
  intro A _ _ n t E η _ hη _ a b w
  have hit : ∀ p, p ≤ t → Nc E η a b w p = (-1 : A) ^ p * Nc E η a b w 0 := by
    intro p
    induction p with
    | zero => intro _; rw [pow_zero, one_mul]
    | succ p ih =>
      intro hp
      rw [stepC E η a b w hη p (by omega), ih (by omega), pow_succ, mul_neg_one, neg_mul]
  have h := hit t le_rfl
  rw [Nc_last, Nc_zero] at h
  have h2 : ∑ i : Fin (t + 1), (((-1 : ℤ) ^ (i : ℕ) : ℤ) : A) * (η (a i) * qminor E (a ∘ i.succAbove) b (w - 1)) =
      (-1 : A) ^ t * ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (t - (j : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ j.succAbove) b w * η (a j)) := by
    rw [h, ← mul_assoc ((-1 : A) ^ t), ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc ((-1 : A) ^ t)]
  congr 1
  have hj := j.isLt
  push_cast
  rw [← pow_add, show t + (t - (j : ℕ)) = (j : ℕ) + 2 * (t - (j : ℕ)) by omega, pow_add, pow_mul,
    neg_one_sq, one_pow, mul_one]

end PI.UnitaryGroupMassFormula.QmMove
end
end

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmMove

theorem rho_sum {A : Type*} [Ring A] (m : ℕ) (z : ℤ) (x D : A) :
    ∑ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      (x * (((Equiv.Perm.sign ρ : ℤ) : A) * D)) = (m.factorial : A) * ((z : A) * (x * D)) := by
  have h : ∀ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      (x * (((Equiv.Perm.sign ρ : ℤ) : A) * D)) = (z : A) * (x * D) := by
    intro ρ
    rw [sgnlem, ← mul_assoc ((Equiv.Perm.sign ρ : ℤ) : A), ← Int.cast_mul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => h ρ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

theorem sum_perms_sign_squared {A : Type*} [Ring A] (m : ℕ) (z : ℤ) (x D : A) :
    ∑ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      ((((Equiv.Perm.sign ρ : ℤ) : A) * D) * x) = (m.factorial : A) * ((z : A) * (D * x)) := by
  have h : ∀ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      ((((Equiv.Perm.sign ρ : ℤ) : A) * D) * x) = (z : A) * (D * x) := by
    intro ρ
    rw [Int.cast_mul, mul_assoc, ← mul_assoc ((Equiv.Perm.sign ρ : ℤ) : A) _ x,
      ← mul_assoc ((Equiv.Perm.sign ρ : ℤ) : A) ((Equiv.Perm.sign ρ : ℤ) : A) D, ← Int.cast_mul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => h ρ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

section Vec
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
  (a : Fin m → Fin n) (b : Fin (m + 1) → Fin n) (w : ℂ)

def Fv (p : ℕ) (τ : Equiv.Perm (Fin (m + 1))) (σ : Equiv.Perm (Fin m)) (q : Fin (m + 1)) : A :=
  if (q : ℕ) = p then y (b (τ q))
  else if (q : ℕ) < p then Tm E (w - 1 - ((q : ℕ) : ℂ)) (extN (a ∘ σ) (b 0) q) (b (τ q))
  else Tm E (w - (((q : ℕ) - 1 : ℕ) : ℂ)) (extN (a ∘ σ) (b 0) ((q : ℕ) - 1)) (b (τ q))

def Pv (p : ℕ) (τ : Equiv.Perm (Fin (m + 1))) : A :=
  ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn (Fv E y a b w p τ σ)).prod

def Mv (p : ℕ) : A := ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * Pv E y a b w p τ


omit [Algebra ℂ A] in
def symV (x c d : Fin n) : A := (if x = d then y c else 0) + (if x = c then y d else 0)

omit [Algebra ℂ A] in
theorem symV_comm (x c d : Fin n) : symV y x c d = symV y x d c := by
  simp only [symV]; abel

theorem midV (hy : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (v v' : ℂ) (hv : v = v' + 1) (x d c : Fin n) :
    y c * Tm E v x d - Tm E v' x d * y c = symV y x c d := by
  have h := hy x d c
  rw [sub_eq_iff_eq_add] at h
  have c2 : ∀ z, algebraMap ℂ A v' * y z = y z * algebraMap ℂ A v' := fun z => Algebra.commutes _ _
  subst hv
  simp only [Tm, symV]
  split_ifs at h ⊢
  all_goals
    simp only [map_add (f := _), map_one, mul_add, add_mul, mul_one, zero_add, add_zero, h, c2]
    try noncomm_ring

theorem stepV (hy : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (p : ℕ) (hp : p < m) : Mv E y a b w (p + 1) = -Mv E y a b w p := by
  set s : Equiv.Perm (Fin (m + 1)) := Equiv.swap ⟨p, by omega⟩ ⟨p + 1, by omega⟩ with hs_def
  have hs : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap (by simp [Fin.ext_iff])
  have hfix : ∀ q : Fin (m + 1), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 → s q = q := by
    intro q h1 h2
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; apply h1; rw [h]
    · intro h; apply h2; rw [h]
  have hoff : ∀ τ σ (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fv E y a b w p (τ * s) σ q = Fv E y a b w p τ σ q := by
    intro τ σ q h1 h2
    simp only [Fv, Equiv.Perm.mul_apply, hfix q h1 h2]
  have hoff2 : ∀ τ σ (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fv E y a b w (p + 1) τ σ q = Fv E y a b w p τ σ q := by
    intro τ σ q h1 h2
    have e1 : ((q : ℕ) < p + 1) ↔ ((q : ℕ) < p) := by omega
    simp only [Fv, if_neg h1, if_neg h2, e1]
  have htk : ∀ τ σ, (List.ofFn (Fv E y a b w p (τ * s) σ)).take p =
      (List.ofFn (Fv E y a b w p τ σ)).take p :=
    fun τ σ => take_ofFn_congr _ _ p (fun k hk => hoff τ σ k (by omega) (by omega))
  have hdr : ∀ τ σ, (List.ofFn (Fv E y a b w p (τ * s) σ)).drop (p + 2) =
      (List.ofFn (Fv E y a b w p τ σ)).drop (p + 2) :=
    fun τ σ => drop_ofFn_congr _ _ (p + 2) (fun k hk => hoff τ σ k (by omega) (by omega))
  have hsp : s ⟨p, by omega⟩ = ⟨p + 1, by omega⟩ := Equiv.swap_apply_left _ _
  have hsp1 : s ⟨p + 1, by omega⟩ = ⟨p, by omega⟩ := Equiv.swap_apply_right _ _
  have n1 : p + 1 ≠ p := by omega
  have n2 : p < p + 1 := by omega
  have n3 : ¬ (p + 1 < p) := by omega
  have n4 : p + 1 - 1 = p := by omega
  refine step s hs (fun τ => Pv E y a b w p τ) (fun τ => Pv E y a b w (p + 1) τ)
    (fun τ => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : A) *
      (((List.ofFn (Fv E y a b w p τ σ)).take p).prod *
        symV y (extN (a ∘ σ) (b 0) p) (b (τ ⟨p + 1, by omega⟩)) (b (τ ⟨p, by omega⟩)) *
        ((List.ofFn (Fv E y a b w p τ σ)).drop (p + 2)).prod)) ?_ ?_
  · intro τ
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [htk, hdr, Equiv.Perm.mul_apply, hsp, hsp1]
    rw [symV_comm]
  · intro τ
    simp only [Pv]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← mul_sub, prod_diff _ _ p (by omega)
      (fun k h1 h2 => (hoff2 τ σ k h1 h2).trans (hoff τ σ k h1 h2).symm), htk, hdr]
    congr 1
    congr 2
    simp only [Fv, Equiv.Perm.mul_apply, hsp, hsp1, if_true, if_neg n1, if_pos n2, if_neg n3, n4,
      if_neg n1.symm]
    exact midV E y hy _ _ (by push_cast; ring) _ _ _

theorem Pv_zero (τ : Equiv.Perm (Fin (m + 1))) :
    Pv E y a b w 0 τ = y (b (τ 0)) * qminor E a (fun k => b (τ k.succ)) w := by
  unfold Pv qminor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [List.ofFn_succ, List.prod_cons]
  have hf : Fv E y a b w 0 τ σ 0 = y (b (τ 0)) := by simp [Fv]
  have hg : (fun i : Fin m => Fv E y a b w 0 τ σ i.succ) =
      fun k : Fin m => Tm E (w - (k : ℂ)) (a (σ k)) (b (τ k.succ)) := by
    funext k
    simp only [Fv, Fin.val_succ]
    rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel, extN_lt] <;> rfl
  rw [hf, hg, ← mul_assoc, ← mul_assoc, icomm]

theorem Pv_last (τ : Equiv.Perm (Fin (m + 1))) :
    Pv E y a b w m τ = qminor E a (fun k => b (τ k.castSucc)) (w - 1) * y (b (τ (Fin.last m))) := by
  unfold Pv qminor
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  have hf : Fv E y a b w m τ σ (Fin.last m) = y (b (τ (Fin.last m))) := by simp [Fv]
  have hg : (fun i : Fin m => Fv E y a b w m τ σ i.castSucc) =
      fun k : Fin m => Tm E (w - 1 - (k : ℂ)) (a (σ k)) (b (τ k.castSucc)) := by
    funext k
    simp only [Fv, Fin.val_castSucc]
    rw [if_neg (by have := k.isLt; omega), if_pos k.isLt, extN_lt] <;> rfl
  rw [hf, hg]
  exact (mul_assoc _ _ _).symm

theorem Mv_zero (hE : GlRel E) : Mv E y a b w 0 = (m.factorial : A) * ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (y (b j) * qminor E a (b ∘ j.succAbove) w) := by
  unfold Mv
  rw [sum_perm_eq_sum_firstColumnSplit m, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hP : ∀ ρ, Pv E y a b w 0 (phi0 m (j, ρ)) =
      y (b j) * (((Equiv.Perm.sign ρ : ℤ) : A) * qminor E a (b ∘ j.succAbove) w) := by
    intro ρ
    rw [Pv_zero, firstColumnSplit_zero, ← quantumMinorColSkew_holds A n m E hE a (b ∘ j.succAbove) ρ w]
    congr 2
    funext k
    simp [firstColumnSplit_succ]
  simp only [hP, sign_firstColumnSplit, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  exact rho_sum m _ _ _

theorem Mv_last (hE : GlRel E) : Mv E y a b w m = (m.factorial : A) * ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (m - (j : ℕ)) : ℤ) : A) * (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j)) := by
  unfold Mv
  rw [sum_phiL m, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hP : ∀ ρ, Pv E y a b w m (lastColumnSplit m (j, ρ)) =
      (((Equiv.Perm.sign ρ : ℤ) : A) * qminor E a (b ∘ j.succAbove) (w - 1)) * y (b j) := by
    intro ρ
    rw [Pv_last, phiL_last, ← quantumMinorColSkew_holds A n m E hE a (b ∘ j.succAbove) ρ (w - 1)]
    congr 2
    funext k
    simp [phiL_castSucc]
  simp only [hP, phiL_sign, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  exact sum_perms_sign_squared m _ _ _

end Vec

theorem move_operator_vector : PI.MoveVec := by
  intro A _ _ n t E y hE hy _ a b w
  have hc := chain (Mv E y a b w) t (fun p hp => stepV E y a b w hy p hp)
  rw [Mv_last E y a b w hE, Mv_zero E y a b w hE] at hc
  have hs : ∀ X : Fin (t + 1) → A, ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (t - (j : ℕ)) : ℤ) : A) * X j =
      (((-1 : ℤ) ^ t : ℤ) : A) * ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * X j := by
    intro X
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [neg_one_pow_sub t j (Nat.lt_succ_iff.mp j.isLt), Int.cast_mul, mul_assoc]
  rw [hs, ← mul_assoc (((-1 : ℤ) ^ t : ℤ) : A), icomm ((-1 : ℤ) ^ t) (t.factorial : A), mul_assoc] at hc
  have h2 := fact_cancel t _ _ hc
  have hsq : (((-1 : ℤ) ^ t : ℤ) : A) * (((-1 : ℤ) ^ t : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, Int.cast_one]
  calc _ = ((((-1 : ℤ) ^ t : ℤ) : A) * (((-1 : ℤ) ^ t : ℤ) : A)) * ∑ j : Fin (t + 1),
        (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (y (b j) * qminor E a (b ∘ j.succAbove) w) := by
        rw [hsq, one_mul]
    _ = _ := by rw [mul_assoc, ← h2, ← mul_assoc, hsq, one_mul]

end PI.UnitaryGroupMassFormula.QmMove
end
end

theorem quantum_minor_move : PI.QmMove := ⟨PI.UnitaryGroupMassFormula.QmMove.move_operator_vector, PI.UnitaryGroupMassFormula.QmMove.move_operator_covariance⟩
