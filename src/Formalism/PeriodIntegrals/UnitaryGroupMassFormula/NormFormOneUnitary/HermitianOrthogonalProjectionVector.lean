module

public import Formalism.HermitianCurvature.StatementJF

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.UnitaryP
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.PRowWSColW
open Matrix Finset Formalism.QuantumDeterminants

noncomputable section

namespace NFOne

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩

@[simp] theorem sg_val (k r : ℕ) (i : Fin (2 * r + k + 1)) : (sg k r i).val = 2 * r + k - i.val := rfl

theorem sg_sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  apply Fin.ext
  simp only [sg_val]
  have := i.isLt
  omega

def dW (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem star_dW (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (dW k r i) = dW k r i := by
  unfold dW
  split_ifs <;> simp

theorem Hpk_eq (k r : ℕ) (p l : Fin (2 * r + k + 1)) :
    Hpk k r p l = if r ≤ p.val ∧ p.val ≤ r + k then (if l = p then dW k r p else 0)
      else (if l = sg k r p then 1 else 0) := by
  have := p.isLt
  have := l.isLt
  simp only [Hpk, dW, Fin.ext_iff, sg_val]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_symm (k r : ℕ) (p l : Fin (2 * r + k + 1)) : Hpk k r p l = Hpk k r l p := by
  have := p.isLt
  have := l.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_row (k r : ℕ) (p : Fin (2 * r + k + 1)) (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ l, Hpk k r p l * f l =
      if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * f p else f (sg k r p) := by
  by_cases h : r ≤ p.val ∧ p.val ≤ r + k
  · simp [Hpk_eq, h, ite_mul]
  · simp [Hpk_eq, h, ite_mul]

theorem Hpk_mulVec (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) p = if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * v p else v (sg k r p) := by
  exact H_row k r p v

theorem herm_eq (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ i, star (w i) * (Hpk k r *ᵥ v) i := rfl

def Pm (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun p q =>
  if p.val < r then
    (if r ≤ q.val ∧ q.val ≤ r + k then -(dW k r q * star (V p.val q))
     else if r + k < q.val then
       (if (sg k r q).val < j then V (sg k r q).val p else -star (V p.val (sg k r q)))
     else 0)
  else if r ≤ p.val ∧ p.val ≤ r + k then
    (if r + k < q.val then V (sg k r q).val p else 0)
  else 0

theorem P_colX (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hq : q.val < r) : Pm k r j V p q = 0 := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem P_rowS (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : r + k < p.val) : Pm k r j V p q = 0 := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem P_rowWS_colW (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : r ≤ p.val) (hq : q.val ≤ r + k) : Pm k r j V p q = 0 := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem P_WS (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp1 : r ≤ p.val) (hp2 : p.val ≤ r + k) (hq : r + k < q.val) :
    Pm k r j V p q = V (sg k r q).val p := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem P_XW (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : p.val < r) (hq1 : r ≤ q.val) (hq2 : q.val ≤ r + k) :
    Pm k r j V p q = -(dW k r q * star (V p.val q)) := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem P_XS (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : p.val < r) (hq : r + k < q.val) :
    Pm k r j V p q = if (sg k r q).val < j then V (sg k r q).val p else -star (V p.val (sg k r q)) := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem HP_apply (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * Pm k r j V) p q = if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * Pm k r j V p q
      else Pm k r j V (sg k r p) q := by
  rw [Matrix.mul_apply]
  exact H_row k r p (fun l => Pm k r j V l q)

theorem PH_apply (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * Hpk k r) p q = if r ≤ q.val ∧ q.val ≤ r + k then dW k r q * star (Pm k r j V q p)
      else star (Pm k r j V (sg k r q) p) := by
  have h : ∑ l, Hpk k r q l * star (Pm k r j V l p) =
      if r ≤ q.val ∧ q.val ≤ r + k then dW k r q * star (Pm k r j V q p)
      else star (Pm k r j V (sg k r q) p) := H_row k r q (fun l => star (Pm k r j V l p))
  rw [Matrix.mul_apply, ← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, Hpk_symm k r l q, mul_comm]

theorem PHP_apply (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) p q = ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
      dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HP_apply, Matrix.conjTranspose_apply]
  have hi := i.isLt
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    by_cases h2 : i.val < r
    · rw [P_rowS k r j V (sg k r i) q (by simp only [sg_val]; omega), mul_zero]
    · rw [P_rowS k r j V i p (by omega), star_zero, zero_mul]

end NFOne
end
end

open Matrix Finset Formalism.QuantumDeterminants

noncomputable section

namespace NFOne

theorem K_iso (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (p q : Fin (2 * r + k + 1)) (hp : r + k < p.val) (hq : r + k < q.val)
    (hb : (sg k r q).val < j) (hc : (sg k r p).val < j) :
    herm (Hpk k r) (V (sg k r q).val) (V (sg k r p).val) =
      star (V (sg k r p).val (sg k r q)) + V (sg k r q).val (sg k r p) +
      ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
        dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
  have hp' := p.isLt; have hq' := q.isLt
  rw [herm_eq]
  have pt : ∀ i : Fin (2 * r + k + 1),
      star (V (sg k r p).val i) * (Hpk k r *ᵥ V (sg k r q).val) i =
        (if i = sg k r q then star (V (sg k r p).val (sg k r q)) else 0) +
        (if i = p then V (sg k r q).val (sg k r p) else 0) +
        (if r ≤ i.val ∧ i.val ≤ r + k then
          dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
    intro i
    have hi := i.isLt
    rw [Hpk_mulVec]
    by_cases h1 : i.val < r
    · rw [if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
        if_neg (show ¬ (i = p) from fun h => by rw [h] at h1; omega),
        if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega), add_zero, add_zero]
      rw [Vs _ hb (sg k r i) (by simp only [sg_val]; omega)]
      by_cases h2 : i = sg k r q
      · rw [if_pos (show (sg k r (sg k r i)).val = (sg k r q).val by rw [h2, sg_sg]), if_pos h2,
          mul_one, h2]
      · rw [if_neg (show ¬ ((sg k r (sg k r i)).val = (sg k r q).val) by
            intro h; apply h2; ext; simp only [sg_val] at h ⊢; omega), if_neg h2, mul_zero]
    · by_cases h3 : i.val ≤ r + k
      · rw [if_pos (show r ≤ i.val ∧ i.val ≤ r + k from ⟨by omega, h3⟩),
          if_neg (show ¬ (i = sg k r q) from fun h => by rw [h] at h1; simp only [sg_val] at h1; omega),
          if_neg (show ¬ (i = p) from fun h => by rw [h] at h3; omega),
          if_pos (show r ≤ i.val ∧ i.val ≤ r + k from ⟨by omega, h3⟩)]
        ring
      · rw [if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
          if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
          if_neg (show ¬ (i = sg k r q) from fun h => by rw [h] at h3; simp only [sg_val] at h3; omega),
          zero_add, add_zero]
        rw [Vs _ hc i (by omega)]
        by_cases h2 : i = p
        · rw [if_pos (show (sg k r i).val = (sg k r p).val by rw [h2]), if_pos h2, h2]; simp
        · rw [if_neg (show ¬ ((sg k r i).val = (sg k r p).val) by
            intro h; apply h2; ext; simp only [sg_val] at h; omega), if_neg h2]; simp
  rw [Finset.sum_congr rfl (fun i _ => pt i), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem E_zero (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0)
    (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * Hpk k r) p q + (Hpk k r * Pm k r j V) p q +
      ((Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) p q = 0 := by
  have hp2 := p.isLt
  have hq2 := q.isLt
  rw [PH_apply, HP_apply, PHP_apply]
  have hC : ¬ (r + k < p.val ∧ r + k < q.val) →
      ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
        dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) = 0 := by
    intro hpq
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hi
    · by_cases hp : r + k < p.val
      · rw [P_rowWS_colW k r j V i q hi.1 (by omega), mul_zero]
      · rw [P_rowWS_colW k r j V i p hi.1 (by omega), star_zero, mul_zero, zero_mul]
    · rfl
  by_cases hpX : p.val < r
  · have hpW : ¬ (r ≤ p.val ∧ p.val ≤ r + k) := by omega
    have hA : ∀ x : Fin (2 * r + k + 1), Pm k r j V x p = 0 := fun x => P_colX k r j V x p hpX
    have hB : Pm k r j V (sg k r p) q = 0 := P_rowS k r j V (sg k r p) q (by rw [sg_val]; omega)
    rw [if_neg hpW, hB, hC (by omega), hA, hA]
    simp
  · by_cases hpW : r ≤ p.val ∧ p.val ≤ r + k
    · rw [if_pos hpW, hC (by omega), add_zero]
      by_cases hqX : q.val < r
      · have hqW : ¬ (r ≤ q.val ∧ q.val ≤ r + k) := by omega
        rw [if_neg hqW, P_rowS k r j V (sg k r q) p (by rw [sg_val]; omega), P_colX k r j V p q hqX]
        simp
      · by_cases hqW : r ≤ q.val ∧ q.val ≤ r + k
        · rw [if_pos hqW, P_rowWS_colW k r j V q p hqW.1 hpW.2, P_rowWS_colW k r j V p q hpW.1 hqW.2]
          simp
        · have hqS : r + k < q.val := by omega
          rw [if_neg hqW, P_XW k r j V (sg k r q) p (by rw [sg_val]; omega) hpW.1 hpW.2,
            P_WS k r j V p q hpW.1 hpW.2 hqS, star_neg, star_mul', star_star, star_dW]
          ring
    · have hpS : r + k < p.val := by omega
      rw [if_neg hpW]
      by_cases hqX : q.val < r
      · have hqW : ¬ (r ≤ q.val ∧ q.val ≤ r + k) := by omega
        rw [if_neg hqW, P_rowS k r j V (sg k r q) p (by rw [sg_val]; omega),
          P_colX k r j V (sg k r p) q hqX, hC (by omega)]
        simp
      · by_cases hqW : r ≤ q.val ∧ q.val ≤ r + k
        · rw [if_pos hqW, P_WS k r j V q p hqW.1 hqW.2 hpS,
            P_XW k r j V (sg k r p) q (by rw [sg_val]; omega) hqW.1 hqW.2, hC (by omega)]
          ring
        · have hqS : r + k < q.val := by omega
          rw [if_neg hqW]
          have hC' : ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
              dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) =
              ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
                dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs with hi
            · rw [P_WS k r j V i p hi.1 hi.2 hpS, P_WS k r j V i q hi.1 hi.2 hqS]
            · rfl
          rw [hC', P_XS k r j V (sg k r q) p (by rw [sg_val]; omega) hpS,
            P_XS k r j V (sg k r p) q (by rw [sg_val]; omega) hqS]
          by_cases hbp : (sg k r p).val < j
          · by_cases hbq : (sg k r q).val < j
            · rw [if_pos hbp, if_pos hbq]
              have hK := K_iso k r j V Vs p q hpS hqS hbq hbp
              rw [Viso _ _ hbq hbp] at hK
              exact hK.symm
            · have h0 := V0 _ (Nat.le_of_not_lt hbq)
              rw [if_pos hbp, if_neg hbq, h0]
              simp
          · have h0 := V0 _ (Nat.le_of_not_lt hbp)
            rw [if_neg hbp, h0]
            by_cases hbq : (sg k r q).val < j
            · rw [if_pos hbq]
              simp
            · have h0' := V0 _ (Nat.le_of_not_lt hbq)
              rw [if_neg hbq, h0']
              simp

theorem unitary_P (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0) :
    (1 + Pm k r j V)ᴴ * Hpk k r * (1 + Pm k r j V) = Hpk k r := by
  have hE : (Pm k r j V)ᴴ * Hpk k r + Hpk k r * Pm k r j V +
      (Pm k r j V)ᴴ * (Hpk k r * Pm k r j V) = 0 := by
    ext p q
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact E_zero k r j V V0 Vs Viso p q
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  calc (1 + (Pm k r j V)ᴴ) * Hpk k r * (1 + Pm k r j V)
      = Hpk k r + ((Pm k r j V)ᴴ * Hpk k r + Hpk k r * Pm k r j V +
          (Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
        abel
    _ = Hpk k r := by rw [hE, add_zero]

end NFOne
end
end

open Matrix Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

noncomputable section

namespace NFOne

private theorem herm_sum_smul_left' {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (v : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ a, α a • v a) w = ∑ a, α a * herm H (v a) w := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => by ring

private theorem herm_sum_smul_right' {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} [Fintype ι]
    (β : ι → ℂ) (v : Fin n → ℂ) (w : ι → Fin n → ℂ) :
    herm H v (∑ a, β a • w a) = ∑ a, star (β a) * herm H v (w a) := by
  unfold herm
  simp only [dotProduct, Pi.star_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

theorem herm_comb (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hyy : ∀ a a', herm (Hpk k r) (y a) (y a') = 0) (α β : Fin j → ℂ) :
    herm (Hpk k r) (∑ a, α a • y a) (∑ a, β a • y a) = 0 := by
  rw [herm_sum_smul_left']
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [herm_sum_smul_right']
  simp [hyy]

theorem herm_Hpk_of_inWb_eq_sum_wI (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r + k + 1) → ℂ)
    (hzy : ∀ a, herm (Hpk k r) z' (y a) = 0) (β : Fin j → ℂ) :
    herm (Hpk k r) z' (∑ a, β a • y a) = 0 := by
  rw [herm_sum_smul_right']
  simp [hzy]

theorem cols_X (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (1 + Pm k r j V) *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
  funext p
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  have h : (Pm k r j V *ᵥ bvec (eI k r a)) p = 0 := by
    rw [show (Pm k r j V *ᵥ bvec (eI k r a)) p = ∑ q, Pm k r j V p q * bvec (eI k r a) q from rfl]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : q = eI k r a
    · subst hq
      rw [P_colX k r j V p _ a.isLt, zero_mul]
    · simp [bvec, Pi.single_apply, hq]
  rw [h, add_zero]

theorem z_fix (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z') (Vz : ∀ c, herm (Hpk k r) z' (V c) = 0) :
    (1 + Pm k r j V) *ᵥ z' = z' := by
  funext p
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  suffices h : (Pm k r j V *ᵥ z') p = 0 by rw [h, add_zero]
  have hterm : ∀ q : Fin (2 * r + k + 1), Pm k r j V p q * z' q =
      if p.val < r then -(star (V p.val q) * (Hpk k r *ᵥ z') q) else 0 := by
    intro q
    have hq2 := q.isLt
    by_cases hW : r ≤ q.val ∧ q.val ≤ r + k
    · rw [Hpk_mulVec, if_pos hW]
      by_cases hp : p.val < r
      · rw [P_XW k r j V p q hp hW.1 hW.2, if_pos hp]
        ring
      · rw [P_rowWS_colW k r j V p q (by omega) hW.2, if_neg hp, zero_mul]
    · have hzq : z' q = 0 := hz q (by omega)
      have hz2 : z' (sg k r q) = 0 := hz (sg k r q) (by simp only [sg_val]; omega)
      rw [hzq, mul_zero, Hpk_mulVec, if_neg hW, hz2, mul_zero, neg_zero, ite_self]
  rw [show (Pm k r j V *ᵥ z') p = ∑ q, Pm k r j V p q * z' q from rfl]
  simp only [hterm]
  by_cases hp : p.val < r
  · simp only [if_pos hp, Finset.sum_neg_distrib, neg_eq_zero]
    have := Vz p.val
    rw [herm_eq] at this
    exact this
  · simp [if_neg hp]

end NFOne
