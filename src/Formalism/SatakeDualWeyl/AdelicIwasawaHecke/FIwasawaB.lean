module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard

@[expose] public section

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaA
open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaGen

variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}

def fIwasawaH (x y : Fin n → L) : L := ∑ j, σ (x (Fin.rev j)) * y j

def fIwasawaUn (M : Matrix (Fin n) (Fin n) L) : Prop := cT σ M * antiJ L n * M = antiJ L n

theorem fIwasawa_antiJ (i j : Fin n) : antiJ L n i j = if j = Fin.rev i then 1 else 0 := by
  unfold antiJ
  try simp only [Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  have hiff : ((i : ℕ) + (j : ℕ) + 1 = n) ↔ (j = Fin.rev i) := by
    rw [Fin.ext_iff, Fin.val_rev]; omega
  by_cases h : j = Fin.rev i
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

private theorem cT_apply' (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) : cT σ M i j = σ (M j i) := by
  first | rfl | simp [cT] | (unfold cT; simp)

private theorem cT_mul_adelic_iwasawa_hecke (A B : Matrix (Fin n) (Fin n) L) : cT σ (A * B) = cT σ B * cT σ A := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cT_apply', Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem fIwasawa_gram (M : Matrix (Fin n) (Fin n) L) (a b : Fin n) :
    (cT σ M * antiJ L n * M) a b = fIwasawaH σ (fun i => M i a) (fun i => M i b) := by
  unfold fIwasawaH
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev k)]
  · simp [fIwasawa_antiJ, cT_apply']
  · intro l _ hl
    have : k ≠ Fin.rev l := fun h => hl (by rw [h, Fin.rev_rev])
    simp [fIwasawa_antiJ, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem fIwasawa_H_single_left (p : Fin n) (w : Fin n → L) :
    fIwasawaH σ (Pi.single p 1) w = w (Fin.rev p) := by
  unfold fIwasawaH
  rw [Finset.sum_eq_single (Fin.rev p)]
  · simp
  · intro j _ hj
    have : Fin.rev j ≠ p := fun h => hj (by rw [← h, Fin.rev_rev])
    simp [Pi.single_apply, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem fIwasawa_un_of_isometry (M : Matrix (Fin n) (Fin n) L)
    (h : ∀ x y, fIwasawaH σ (M *ᵥ x) (M *ᵥ y) = fIwasawaH σ x y) : fIwasawaUn σ M := by
  have hc : ∀ a : Fin n, (fun i => M i a) = M *ᵥ Pi.single a 1 := by
    intro a; ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold fIwasawaUn
  ext a b
  rw [fIwasawa_gram, hc a, hc b, h, fIwasawa_H_single_left, fIwasawa_antiJ]
  by_cases hb : b = Fin.rev a
  · subst hb; simp
  · simp [Pi.single_apply, hb, Ne.symm hb]

theorem fIwasawa_un_mul (A B : Matrix (Fin n) (Fin n) L) (hA : fIwasawaUn σ A) (hB : fIwasawaUn σ B) :
    fIwasawaUn σ (A * B) := by
  unfold fIwasawaUn at *
  rw [cT_mul_adelic_iwasawa_hecke, show cT σ B * cT σ A * antiJ L n * (A * B) = cT σ B * (cT σ A * antiJ L n * A) * B by
    simp only [Matrix.mul_assoc], hA, hB]

theorem fIwasawa_antiJ_mul_antiJ : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · rw [fIwasawa_antiJ, fIwasawa_antiJ, Fin.rev_rev]
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  · intro k _ hk
    simp [fIwasawa_antiJ, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

def fIwasawaInv (M : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  antiJ L n * cT σ M * antiJ L n

theorem fIwasawa_inv_mul (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    fIwasawaInv σ M * M = 1 := by
  unfold fIwasawaInv
  unfold fIwasawaUn at hM
  rw [show antiJ L n * cT σ M * antiJ L n * M = antiJ L n * (cT σ M * antiJ L n * M) by
    simp only [Matrix.mul_assoc], hM, fIwasawa_antiJ_mul_antiJ]

theorem fIwasawa_mul_inv (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    M * fIwasawaInv σ M = 1 := by
  have h := fIwasawa_inv_mul σ M hM
  first
  | exact mul_eq_one_comm.mp h
  | (rw [← Matrix.inv_eq_left_inv h]; exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h))

def fIwasawaMk (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) : GU σ n :=
  ⟨⟨M, fIwasawaInv σ M, fIwasawa_mul_inv σ M hM, fIwasawa_inv_mul σ M hM⟩, hM⟩

theorem fIwasawa_mk_val (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    (((fIwasawaMk σ M hM : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = M := rfl

theorem fIwasawa_mem_un (g : GU σ n) :
    fIwasawaUn σ (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := g.2

end FIwasawaGen

end Formalism.UG.P
end

open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaMat

variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}

def fIwasawaP (π : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => if π i = j then 1 else 0

theorem permMatrix_mulVec₂ (π : Equiv.Perm (Fin n)) (w : Fin n → L) :
    fIwasawaP π *ᵥ w = fun i => w (π i) := by
  funext i
  simp [fIwasawaP, Matrix.mulVec, dotProduct]

theorem permMatrix_mul_apply₂ (π : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (fIwasawaP π * M : Matrix (Fin n) (Fin n) L) i j = M (π i) j := by
  simp [fIwasawaP, Matrix.mul_apply]

theorem permMatrix_isUnitary_of_commute_rev (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (Fin.rev i) = Fin.rev (π i)) :
    fIwasawaUn σ (fIwasawaP (L := L) π) := by
  apply fIwasawa_un_of_isometry
  intro x y
  simp only [fIwasawaH, permMatrix_mulVec₂, hπ]
  exact Equiv.sum_comp π (fun k => σ (x (Fin.rev k)) * y k)

def fIwasawaE (e z : Fin n → L) (c : L) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => (if i = j then 1 else 0) + z i * σ (e (Fin.rev j)) - e i * σ (z (Fin.rev j)) +
    c * e i * σ (e (Fin.rev j))

theorem fIwasawa_E_mulVec (e z : Fin n → L) (c : L) (w : Fin n → L) :
    fIwasawaE σ e z c *ᵥ w = w + fIwasawaH σ e w • z - fIwasawaH σ z w • e +
      (c * fIwasawaH σ e w) • e := by
  funext i
  simp only [fIwasawaE, fIwasawaH, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum, Finset.sum_mul]
  ring_nf

theorem fIwasawa_E_un (hσ : ∀ x, σ (σ x) = x) (e z : Fin n → L) (c : L)
    (hee : fIwasawaH σ e e = 0) (hez : fIwasawaH σ e z = 0)
    (hc : c + σ c + fIwasawaH σ z z = 0) : fIwasawaUn σ (fIwasawaE σ e z c) := by
  have Hal : ∀ x x' y : Fin n → L, fIwasawaH σ (x + x') y = fIwasawaH σ x y + fIwasawaH σ x' y := by
    intro x x' y
    simp [fIwasawaH, add_mul, Finset.sum_add_distrib]
  have Hsl : ∀ x x' y : Fin n → L, fIwasawaH σ (x - x') y = fIwasawaH σ x y - fIwasawaH σ x' y := by
    intro x x' y
    simp [fIwasawaH, sub_mul, Finset.sum_sub_distrib]
  have Hml : ∀ (t : L) (x y : Fin n → L), fIwasawaH σ (t • x) y = σ t * fIwasawaH σ x y := by
    intro t x y
    simp [fIwasawaH, Finset.mul_sum, mul_assoc]
  have Har : ∀ x y y' : Fin n → L, fIwasawaH σ x (y + y') = fIwasawaH σ x y + fIwasawaH σ x y' := by
    intro x y y'
    simp [fIwasawaH, mul_add, Finset.sum_add_distrib]
  have Hsr : ∀ x y y' : Fin n → L, fIwasawaH σ x (y - y') = fIwasawaH σ x y - fIwasawaH σ x y' := by
    intro x y y'
    simp [fIwasawaH, mul_sub, Finset.sum_sub_distrib]
  have Hmr : ∀ (t : L) (x y : Fin n → L), fIwasawaH σ x (t • y) = t * fIwasawaH σ x y := by
    intro t x y
    simp only [fIwasawaH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have Hsym : ∀ x y : Fin n → L, fIwasawaH σ y x = σ (fIwasawaH σ x y) := by
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [fIwasawaH, map_sum, map_mul, hσ]
    exact (Fintype.sum_equiv Fin.revPerm _ _ fun j => by simp [mul_comm]).symm
  apply fIwasawa_un_of_isometry
  intro w w'
  rw [fIwasawa_E_mulVec, fIwasawa_E_mulVec]
  simp only [Hal, Hsl, Hml, Har, Hsr, Hmr, map_mul]
  simp only [Hsym z w, Hsym e w, Hsym e z, hez, hee, map_zero]
  linear_combination (σ (fIwasawaH σ e w) * fIwasawaH σ e w') * hc

end FIwasawaMat

section FIwasawaInt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}

def fIwasawaInt (M : Matrix (Fin n) (Fin n) L) : Prop := ∀ i j, Valued.v (M i j) ≤ 1

theorem fIwasawa_int_mul (A B : Matrix (Fin n) (Fin n) L) (hA : fIwasawaInt A) (hB : fIwasawaInt B) :
    fIwasawaInt (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by rw [map_mul]; exact mul_le_one' (hA i k) (hB k j)

theorem fIwasawa_int_one : fIwasawaInt (1 : Matrix (Fin n) (Fin n) L) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem fIwasawa_int_inv (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaInt M) : fIwasawaInt (fIwasawaInv σ M) := by
  have hJ : fIwasawaInt (antiJ L n) := by
    intro i j
    simp only [antiJ]
    split_ifs <;> simp
  have hcT : fIwasawaInt (cT σ M) := by
    intro i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [hσv]
    exact hM j i
  unfold fIwasawaInv
  exact fIwasawa_int_mul _ _ (fIwasawa_int_mul _ _ hJ hcT) hJ

theorem fIwasawa_int_E (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (e z : Fin n → L) (c : L)
    (he : ∀ i, Valued.v (e i) ≤ 1) (hz : ∀ i, Valued.v (z i) ≤ 1) (hc : Valued.v c ≤ 1) :
    fIwasawaInt (fIwasawaE σ e z c) := by
  intro i j
  simp only [fIwasawaE, Matrix.of_apply]
  have h1 : Valued.v (if i = j then (1 : L) else 0) ≤ 1 := by split_ifs <;> simp
  refine Valuation.map_add_le _ (Valuation.map_sub_le _ (Valuation.map_add_le _ h1 ?_) ?_) ?_
  · rw [map_mul, hσv]
    exact mul_le_one' (hz i) (he _)
  · rw [map_mul, hσv]
    exact mul_le_one' (he i) (hz _)
  · rw [map_mul, map_mul, hσv]
    exact mul_le_one' (mul_le_one' hc (he i)) (he _)

theorem fIwasawa_mk_mem_K (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaUn σ M) (hI : fIwasawaInt M) : fIwasawaMk σ M hM ∈ KU σ n := by
  have hinvI := fIwasawa_int_inv σ hσv M hI
  rw [KU, Subgroup.mem_subgroupOf]
  refine Subgroup.mem_inf.2 ⟨(fIwasawaMk σ M hM).2, ?_⟩
  let A : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨M i j, hI i j⟩
  let B : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨fIwasawaInv σ M i j, hinvI i j⟩
  have hinj : Function.Injective
      (RingHom.mapMatrix (intL L).subtype : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have hA : RingHom.mapMatrix (intL L).subtype A = M := by ext i j; rfl
  have hB : RingHom.mapMatrix (intL L).subtype B = fIwasawaInv σ M := by ext i j; rfl
  have hAB : A * B = 1 := hinj (by rw [map_mul, hA, hB, map_one, fIwasawa_mul_inv σ M hM])
  have hBA : B * A = 1 := hinj (by rw [map_mul, hA, hB, map_one, fIwasawa_inv_mul σ M hM])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  show RingHom.mapMatrix (intL L).subtype A = _
  rw [hA]
  exact (fIwasawa_mk_val σ M hM).symm

end FIwasawaInt

end Formalism.UG.P
