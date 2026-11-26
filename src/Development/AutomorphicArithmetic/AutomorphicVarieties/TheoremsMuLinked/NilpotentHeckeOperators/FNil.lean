module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.FNil
theorem UpperTheory.V.Th.fNil :
    ∀ (K S : Type) [CommRing K] [IsDomain K] [CommRing S] (f : K →+* S) (n N q : ℕ) (α : Fin n → K) (U : Fin n → S), (∀ k, (U k - f (α k)) ^ N = 0) → ¬ (∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (q : K) * α i') → (∏ i : Fin n, ∏ i' ∈ Finset.univ.erase i, (U i - U i') * (U i - (q : S) * U i')) ^ (2 * N) = 0 := by
  intro K S _ _ _ f n N q α U hU hne
  simp only [not_forall] at hne
  obtain ⟨i, i', hii', hα⟩ := hne
  have hcase : (U i - U i') ^ (2 * N) = 0 ∨ (U i - (q : S) * U i') ^ (2 * N) = 0 := by
    have ha : (U i - f (α i)) ^ N = 0 := hU i
    have hb : (U i' - f (α i')) ^ N = 0 := hU i'
    by_cases he : α i = α i'
    · left
      have hnb : (-(U i' - f (α i'))) ^ N = 0 := by rw [neg_pow, hb, mul_zero]
      have hx : U i - U i' = (U i - f (α i)) + -(U i' - f (α i')) := by
        rw [he]
        ring
      rw [hx]
      exact Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (Commute.all _ _) ha hnb
        (by omega)
    · right
      have hq : α i = (q : K) * α i' := by
        by_contra h'
        exact hα ⟨he, h'⟩
      have hnb : (-(q : S) * (U i' - f (α i'))) ^ N = 0 := by rw [mul_pow, hb, mul_zero]
      have hx : U i - (q : S) * U i' = (U i - f (α i)) + -(q : S) * (U i' - f (α i')) := by
        rw [hq, map_mul, map_natCast]
        ring
      rw [hx]
      exact Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (Commute.all _ _) ha hnb
        (by omega)
  have hY : ((U i - U i') * (U i - (q : S) * U i')) ^ (2 * N) = 0 := by
    rw [mul_pow]
    rcases hcase with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  have hdvd : (U i - U i') * (U i - (q : S) * U i') ∣
      ∏ j : Fin n, ∏ j' ∈ Finset.univ.erase j, (U j - U j') * (U j - (q : S) * U j') :=
    (Finset.dvd_prod_of_mem (fun j' => (U i - U j') * (U i - (q : S) * U j'))
      (Finset.mem_erase.2 ⟨hii'.symm, Finset.mem_univ _⟩)).trans
      (Finset.dvd_prod_of_mem
        (fun j => ∏ j' ∈ Finset.univ.erase j, (U j - U j') * (U j - (q : S) * U j'))
        (Finset.mem_univ i))
  exact zero_dvd_iff.1 (hY ▸ pow_dvd_pow_of_dvd hdvd (2 * N))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.PowRel
open Polynomial in
private theorem UpperTheory.V.Th.product_factors_aeval {S : Type} [CommRing S] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) S) (V : Fin n → S) (i : Fin n) :
    (List.ofFn fun k => if k = i then 1 else Q - V k • (1 : Matrix (Fin n) (Fin n) S)).prod
      = aeval Q (∏ k, if k = i then (1 : S[X]) else X - C (V k)) := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  refine congrArg _ (congrArg _ (funext fun k => ?_))
  simp only [Function.comp_apply]
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]

open Polynomial in
theorem UpperTheory.V.Th.powRel :
    ∀ (K S : Type) [CommRing K] [CommRing S] (f : K →+* S) (n N E : ℕ) (P T : Matrix (Fin n) (Fin n) K) (α : Fin n → K) (β : K) (U : Fin n → S) (i : Fin n), N ≤ E + 1 → (∀ k, (U k - f (α k)) ^ N = 0) → (List.ofFn fun k => if k = i then 1 else P - α k • (1 : Matrix (Fin n) (Fin n) K)).prod * (T - β • (1 : Matrix (Fin n) (Fin n) K)) = 0 → (List.ofFn fun k => if k = i then 1 else P.map f - U k • (1 : Matrix (Fin n) (Fin n) S)).prod ^ (E + 1) * (T.map f - f β • (1 : Matrix (Fin n) (Fin n) S)) = 0 := by
  intro K S _ _ f n N E P T α β U i hN hU h
  have hsm : ∀ a : K, (a • (1 : Matrix (Fin n) (Fin n) K)).map f = f a • (1 : Matrix (Fin n) (Fin n) S) := by
    intro a
    ext p q
    by_cases hpq : p = q <;> simp [Matrix.one_apply, hpq]
  have e1 : (⇑f.mapMatrix ∘ fun k => if k = i then 1 else P - α k • (1 : Matrix (Fin n) (Fin n) K))
      = fun k => if k = i then 1 else P.map f - f (α k) • (1 : Matrix (Fin n) (Fin n) S) := by
    funext k
    simp only [Function.comp_apply]
    split_ifs
    · simp
    · simp [Matrix.map_sub, hsm]
  have hL : (List.ofFn fun k => if k = i then 1 else P.map f - f (α k) • (1 : Matrix (Fin n) (Fin n) S)).prod
      * (T.map f - f β • (1 : Matrix (Fin n) (Fin n) S)) = 0 := by
    have h2 := congrArg f.mapMatrix h
    rw [map_mul, map_list_prod, List.map_ofFn, map_zero, e1] at h2
    have e2 : f.mapMatrix (T - β • (1 : Matrix (Fin n) (Fin n) K)) = T.map f - f β • (1 : Matrix (Fin n) (Fin n) S) := by
      simp [Matrix.map_sub, hsm]
    rw [e2] at h2
    exact h2
  have hdvd : (∏ k, if k = i then (1 : S[X]) else X - C (f (α k))) ∣
      (∏ k, if k = i then (1 : S[X]) else X - C (U k)) ^ (E + 1) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_dvd_prod_of_dvd
    intro k _
    split_ifs
    · simp
    · rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_pow]
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      have : (f (α k) - U k) ^ N = 0 := by
        rw [← neg_sub, neg_pow, hU k, mul_zero]
      exact pow_eq_zero_of_le hN this
  obtain ⟨G, hG⟩ := hdvd
  rw [UpperTheory.V.Th.product_factors_aeval, ← map_pow, hG, mul_comm, map_mul, mul_assoc,
    ← UpperTheory.V.Th.product_factors_aeval (P.map f) (fun k => f (α k)) i, hL, mul_zero]
end
