module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminorStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsCentralCharacter
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.GelfandOfCapelli

open Finset Polynomial
open GlobalTheory.Dec (gelfVal)

theorem main_succ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (F : Fin (m+1) → Fin (m+1) → A)
    (χ : Fin (m+1) → ℂ) (hF : GlRel F)
    (hq : ∀ w : ℂ, qdet F w = algebraMap ℂ A ((GlobalTheory.CapelliNewton.capQ m χ).eval w)) (N : ℕ) :
    etr F N = algebraMap ℂ A (gelfVal χ N) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  set Q := GlobalTheory.CapelliNewton.capQ m χ with hQ
  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → A, ∀ w : ℂ,
      qminor F (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap A (m + 1) m F (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let Rc : ℕ → A := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * cm i j d * epow F (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
      qminor F (Fin.succAbove j) (Fin.succAbove i) w * epow F (N + 1) j i
      = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  let Rp : ℂ[X] := ∑ d ∈ range (m + 1), C (φ (Rc d)) * X ^ d
  have hRp : ∀ w : ℂ, φ (∑ d ∈ range (m + 1), w ^ d • Rc d) = Rp.eval w := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Rp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_sum, map_smul, smul_eq_mul]
    exact sum_congr rfl fun d _ => mul_comm _ _
  have hRpdeg : Rp.natDegree ≤ m := natDegree_sum_le_of_forall_le _ _ fun i hi =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hφa : ∀ c : ℂ, φ (algebraMap ℂ A c) = c * φ 1 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * (Q.eval (w + 1) - Q.eval w) * φ 1 + (-1) ^ N * Rp.eval w
      = Q.eval w * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * φ (etr F k) := by
    intro w
    have h1 := congrArg φ (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse A m F hF w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    simp only [hq, ← Algebra.smul_def, map_add (f := _), map_smul, smul_eq_mul, hRp] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mul_sum, map_sum, map_smul, map_sub, smul_eq_mul, hφa] at h1
    rw [mul_sum]
    linear_combination h1
  obtain ⟨rs, hrs, hrsE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m N χ
  let S : ℂ[X] := ∑ k ∈ range (N + 1),
    C ((-1) ^ k * (φ (etr F k) - gelfVal χ k * φ 1)) * (X - C (m : ℂ)) ^ (N - k)
  have hSe : ∀ w : ℂ, S.eval w = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * φ (etr F k))
      - φ 1 * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k := by
    intro w
    simp only [S, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hQS : Q * S = C ((-1) ^ N) * Rp + C (φ 1) * rs := by
    refine Polynomial.funext fun w => ?_
    have h2 := hrsE w
    rw [← GlobalTheory.CapelliNewton.capQ_eval m χ (w + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ w, ← hQ] at h2
    simp only [eval_mul, eval_add, eval_C, hSe]
    linear_combination -hrec w + φ 1 * h2
  have hS0 : S = 0 := by
    by_contra hne
    have hd := (GlobalTheory.CapelliNewton.capQ_monic m χ).natDegree_mul' hne
    rw [← hQ, hQS, GlobalTheory.CapelliNewton.capQ_natDegree] at hd
    have hle : (C ((-1 : ℂ) ^ N) * Rp + C (φ 1) * rs).natDegree ≤ m :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hRpdeg)
        ((natDegree_C_mul_le _ _).trans hrs))
    omega
  have h0 := congrArg (eval (m : ℂ)) hS0
  simp only [S, eval_zero, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self] at h0
  rw [sum_eq_single N (fun b hb hbN => by
      rw [zero_pow (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hb)) hbN)), mul_zero])
    (fun h => absurd (self_mem_range_succ N) h)] at h0
  rw [Nat.sub_self, pow_zero, mul_one] at h0
  have hne : ((-1 : ℂ)) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [map_sub, hφa]
  exact mul_left_cancel₀ hne (by linear_combination h0)

theorem gelfand_of_capelli : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (F : Fin n → Fin n → A) (χ : Fin n → ℂ),
    GlRel F → (∀ u : ℂ, qdet F (u + ((n : ℂ) - 1) / 2) = algebraMap ℂ A (∏ s, (u + χ s))) →
    ∀ k : ℕ, etr F (k + 1) = algebraMap ℂ A (GlobalTheory.Dec.gelfVal χ (k + 1)) := by
  intro A _ _ n F χ hF hq k
  cases n with
  | zero => simp [etr, gelfVal]
  | succ m =>
    refine main_succ A m F χ hF (fun w => ?_) (k + 1)
    calc qdet F w = qdet F ((w - (m : ℂ) / 2) + (((m + 1 : ℕ) : ℂ) - 1) / 2) := by congr 1; push_cast; ring
      _ = algebraMap ℂ A (∏ s, ((w - (m : ℂ) / 2) + χ s)) := hq _
      _ = _ := by rw [GlobalTheory.CapelliNewton.capQ_eval]

end GlobalTheory.GelfandOfCapelli
end

open Finset Formalism.REAL

namespace PositivityTheory.Rg.Cz.J

theorem natSub_cast {n : ℕ} (k : Fin n) : ((n - 1 - (k : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - ((k : ℕ) : ℂ) := by
  have h' : (n - 1 - (k : ℕ) : ℕ) + (k : ℕ) + 1 = n := by omega
  have := congrArg (Nat.cast (R := ℂ)) h'
  push_cast at this
  linear_combination this

theorem gelfVal_one_eq {n : ℕ} (χ : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal χ 1 = ∑ a : Fin n, (χ a + ((n : ℂ) - 1) / 2 - ((n - 1 - (a : ℕ) : ℕ) : ℂ)) := by
  simp only [GlobalTheory.Dec.gelfVal, pow_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : ∀ b : Fin n, (Amat (fun c => χ c + ((n : ℂ) - 1) / 2)) a b =
      (if a = b then χ a + ((n : ℂ) - 1) / 2 else 0) - (if b ∈ Finset.Ioi a then 1 else 0) := by
    intro b
    simp only [Amat, Matrix.of_apply, Finset.mem_Ioi]
    by_cases h1 : a = b
    · subst h1; simp
    · by_cases h2 : a < b
      · simp [h1, h2]
      · simp [h1, h2]
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi, mul_one]

theorem casVal_holds : CasVal := by
  intro n M _ _ F l hF hC
  set χ : Fin n → ℂ := fun k => l k + ((n : ℂ) - 1) / 2 with hχ
  have hq : ∀ u : ℂ, qdet F (u + ((n : ℂ) - 1) / 2) =
      algebraMap ℂ (Module.End ℂ M) (∏ s, (u + χ s)) := by
    intro u
    rw [hC]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [hχ]
    ring
  have h1 := GlobalTheory.GelfandOfCapelli.gelfand_of_capelli (Module.End ℂ M) n F χ hF hq 0
  have h2 := GlobalTheory.GelfandOfCapelli.gelfand_of_capelli (Module.End ℂ M) n F χ hF hq 1
  refine ⟨?_, ?_⟩
  · have e : etr F (0 + 1) = ∑ i, F i i := by
      simp [etr, epow]
    rw [← e, h1]
    congr 1
    rw [zero_add, gelfVal_one_eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [natSub_cast k]
    simp only [hχ]
    ring
  · have e : etr F (1 + 1) = ∑ i, ∑ j, F i j * F j i := by
      simp [etr, epow, ite_mul, Finset.sum_ite_eq]
    rw [← e, h2]
    congr 1
    rw [show (1 + 1 : ℕ) = 2 from rfl, GlobalTheory.CasimirEigen.gelfVal_two_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hχ, Formalism.QuantumDeterminants.rhoStd]
    push_cast
    ring

end PositivityTheory.Rg.Cz.J
