module

public import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
public import Formalism.WachModuleLifts.StatementW

@[expose] public section

section -- merged from Formalism.WindowSums.AnnihilatorPolynomials.Lagrange
noncomputable section

namespace Formalism.WindowSums

open Polynomial

private lemma aeval_prod_X_sub_C_eq_zero_of_subset {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
    (T : Module.End R V) {ι : Type} [DecidableEq ι] (A B : Finset ι) (γ : ι → R) (x : V)
    (hAB : A ⊆ B) (hA : aeval T (∏ k ∈ A, (X - C (γ k))) x = 0) :
    aeval T (∏ k ∈ B, (X - C (γ k))) x = 0 := by
  rw [← Finset.prod_sdiff hAB, map_mul, Module.End.mul_apply, hA, map_zero]

theorem lagrange_annihilation : Lagrange := by
  intro R _ _ V _ _ T ι _ I S γ d x hSI hinj hS hIS hdiv
  classical
  rcases I.eq_empty_or_nonempty with hI | hI
  · subst hI
    have hS0 : S = ∅ := Finset.subset_empty.mp hSI
    subst hS0
    simp at hS
    simp [hS]
  choose! c hc using hdiv

  have key : ∑ k ∈ I, C (c k) * ∏ m ∈ I.erase k, (X - C (γ m)) = C d := by
    rw [← sub_eq_zero]
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (I.image γ)
    · intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      rw [eval_sub, eval_finsetSum, eval_C, sub_eq_zero]
      rw [Finset.sum_eq_single j]
      · rw [eval_mul, eval_C, eval_prod]
        simp only [eval_sub, eval_X, eval_C]
        rw [hc j hj, mul_comm]
      · intro k hk hkj
        rw [eval_mul, eval_prod]
        apply mul_eq_zero_of_right
        apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨fun h => hkj h.symm, hj⟩)
        simp
      · intro hj'; exact absurd hj hj'
    · rw [Finset.card_image_of_injOn hinj]
      have hpos : 0 < I.card := Finset.card_pos.mpr hI
      have hdeg : ∀ k ∈ I, (C (c k) * ∏ m ∈ I.erase k, (X - C (γ m))).natDegree ≤ I.card - 1 := by
        intro k hk
        refine (natDegree_C_mul_le _ _).trans ?_
        refine (natDegree_prod_le _ _).trans ?_
        simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
        rw [Finset.card_erase_of_mem hk]
      refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
      rw [natDegree_C, max_lt_iff]
      refine ⟨lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ hdeg) (by omega), hpos⟩
  have h := congrArg (fun p => aeval T p x) key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, aeval_C] at h
  rw [LinearMap.sum_apply] at h
  rw [Module.algebraMap_end_apply] at h
  rw [← h]
  apply Finset.sum_eq_zero
  intro k hk
  rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply]
  by_cases hkS : k ∈ S
  · have : I \ S ⊆ I.erase k := by
      intro m hm
      rw [Finset.mem_sdiff] at hm
      exact Finset.mem_erase.mpr ⟨fun h => hm.2 (h ▸ hkS), hm.1⟩
    rw [aeval_prod_X_sub_C_eq_zero_of_subset T _ _ γ x this hIS, smul_zero]
  · have : S ⊆ I.erase k := by
      intro m hm
      exact Finset.mem_erase.mpr ⟨fun h => hkS (h ▸ hm), hSI hm⟩
    rw [aeval_prod_X_sub_C_eq_zero_of_subset T _ _ γ x this hS, smul_zero]

end Formalism.WindowSums
end
end

section -- merged from Formalism.WindowSums.AnnihilatorPolynomials.WindowSum
noncomputable section

namespace Formalism.WindowSums

open Finset

lemma windowSum_count (a : ℤ) (L : ℕ) (r : ℤ) (hr : 0 < r) :
    ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℝ) ≤ (L : ℝ) / (r : ℝ) + 1 := by
  have hmaps : ∀ x ∈ (Finset.Ico a (a + L)).filter (fun x => r ∣ x),
      (x - a) / r ∈ Finset.Icc (0 : ℤ) ((L : ℤ) / r) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    simp only [Finset.mem_Icc]
    exact ⟨Int.ediv_nonneg (by linarith) hr.le, Int.ediv_le_ediv hr (by linarith)⟩
  have hinj : Set.InjOn (fun x => (x - a) / r)
      ((Finset.Ico a (a + L)).filter (fun x => r ∣ x) : Set ℤ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    obtain ⟨k, rfl⟩ := hx.2
    obtain ⟨m, rfl⟩ := hy.2
    simp only at hxy
    rw [show r * k - a = -a + r * k by ring, show r * m - a = -a + r * m by ring,
      Int.add_mul_ediv_left _ _ hr.ne', Int.add_mul_ediv_left _ _ hr.ne'] at hxy
    have : k = m := by linarith
    rw [this]
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have hq0 : 0 ≤ (L : ℤ) / r := Int.ediv_nonneg (by positivity) hr.le
  rw [Int.card_Icc, sub_zero] at hcard
  have hc : ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℝ) ≤
      (((L : ℤ) / r : ℤ) : ℝ) + 1 := by
    have h1 : ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℤ) ≤ (L : ℤ) / r + 1 := by
      have := Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ (L : ℤ) / r + 1)
      omega
    exact_mod_cast h1
  have hdiv : (((L : ℤ) / r : ℤ) : ℝ) ≤ (L : ℝ) / (r : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hr)]
    exact_mod_cast Int.ediv_mul_le (L : ℤ) hr.ne'
  linarith

private theorem sum_range_one_div_pow_succ_eq (x : ℝ) (hx : 1 < x) (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / x ^ (k + 1) = (1 - 1 / x ^ K) / (x - 1) := by
  have hx0 : x - 1 ≠ 0 := by linarith
  have hxp : x ≠ 0 := by linarith
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring

theorem sum_padicValInt_le : WindowSum := by
  intro ℓ _ a L D S hS h0 hD
  have hℓ : ℓ.Prime := Fact.out
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hL0 : (0 : ℝ) ≤ (L : ℝ) / ((ℓ : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) (by linarith)
  rcases Nat.eq_zero_or_pos D with rfl | hDpos
  · have hzero : ∑ i ∈ S, padicValInt ℓ i = 0 := Finset.sum_eq_zero fun i hi =>
      (h0 ((abs_nonpos_iff.1 (by exact_mod_cast hD i hi)) ▸ hi)).elim
    rw [hzero]
    simpa [Real.logb_zero] using hL0
  have hv : ∀ i ∈ S, padicValInt ℓ i =
      ((Finset.range (Nat.log ℓ D)).filter (fun k => (ℓ : ℤ) ^ (k + 1) ∣ i)).card := by
    intro i hi
    have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)

    have hvK : padicValInt ℓ i ≤ Nat.log ℓ D := by
      have hdvd : (ℓ : ℤ) ^ padicValInt ℓ i ∣ i := (padicValInt_dvd_iff _ _).2 (Or.inr le_rfl)
      have h1 : ℓ ^ padicValInt ℓ i ∣ i.natAbs := by
        rw [← Int.natCast_dvd]
        exact_mod_cast hdvd
      have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hi0) h1
      have h3 : i.natAbs ≤ D := by
        have h4 := hD i hi
        rw [← Int.natCast_natAbs] at h4
        exact_mod_cast h4
      exact Nat.le_log_of_pow_le hℓ.one_lt (h2.trans h3)
    have hf : (Finset.range (Nat.log ℓ D)).filter (fun k => (ℓ : ℤ) ^ (k + 1) ∣ i) =
        Finset.range (padicValInt ℓ i) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, padicValInt_dvd_iff, hi0, false_or]
      omega
    rw [hf, Finset.card_range]
  have hcount : ∀ k, ((S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card : ℝ) ≤
      (L : ℝ) / (ℓ : ℝ) ^ (k + 1) + 1 := by
    intro k
    have h1 := windowSum_count a L ((ℓ : ℤ) ^ (k + 1)) (pow_pos (by exact_mod_cast hℓ.pos) _)
    push_cast at h1
    refine le_trans ?_ h1
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hS)
  have hsum : ∑ i ∈ S, padicValInt ℓ i = ∑ k ∈ Finset.range (Nat.log ℓ D),
      (S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card := by
    rw [Finset.sum_congr rfl hv]
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlog : ((Nat.log ℓ D : ℕ) : ℝ) ≤ Real.logb ℓ D := by
    rw [Real.le_logb_iff_rpow_le hℓ1 (by exact_mod_cast hDpos), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self ℓ hDpos.ne'
  have h1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hy : 0 ≤ 1 / (ℓ : ℝ) ^ Nat.log ℓ D := by positivity
  have hgeo : (L : ℝ) * ((1 - 1 / (ℓ : ℝ) ^ Nat.log ℓ D) / ((ℓ : ℝ) - 1)) ≤
      (L : ℝ) / ((ℓ : ℝ) - 1) := by
    rw [← mul_div_assoc, div_le_div_iff₀ h1 h1]
    nlinarith [Nat.cast_nonneg (α := ℝ) L, mul_nonneg (Nat.cast_nonneg (α := ℝ) L) hy]
  rw [hsum]
  push_cast
  calc ∑ k ∈ Finset.range (Nat.log ℓ D), ((S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card : ℝ)
      ≤ ∑ k ∈ Finset.range (Nat.log ℓ D), ((L : ℝ) / (ℓ : ℝ) ^ (k + 1) + 1) :=
        Finset.sum_le_sum fun k _ => hcount k
    _ = (L : ℝ) * ∑ k ∈ Finset.range (Nat.log ℓ D), 1 / (ℓ : ℝ) ^ (k + 1) + (Nat.log ℓ D : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
        rw [sum_range_one_div_pow_succ_eq _ hℓ1]
        linarith

end Formalism.WindowSums
end
end

section -- merged from Formalism.WindowSums.AnnihilatorPolynomials.EvalOneSmulDecomposition
namespace Formalism.WindowSums

open Polynomial

theorem annihilatorPoly_kills : KillerKills := by
  intro ℓ _ c ell JJ V _ _ T
  refine ⟨?_, ?_⟩
  · rintro x ⟨i, hi, hx⟩
    have hsplit : PP ℓ c ell JJ = ((∏ k ∈ (JJ.erase 0).erase i, (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (k * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
        ∑ k ∈ Finset.range (ℓ ^ ell), Polynomial.X ^ k) * (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
      unfold PP
      rw [← Finset.mul_prod_erase _ _ hi]
      ring
    have hk : Polynomial.aeval T (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) x = 0 := by
      simp [hx]
    rw [hsplit, map_mul, Module.End.mul_apply, hk, map_zero]
  · intro v hv
    have hS : Polynomial.aeval T (∑ k ∈ Finset.range (ℓ ^ ell), (Polynomial.X : Polynomial ℤ_[ℓ]) ^ k)
        (T v - v) = 0 := by
      have h1 : T v - v = Polynomial.aeval T (Polynomial.X - 1 : Polynomial ℤ_[ℓ]) v := by simp
      rw [h1, ← Module.End.mul_apply, ← map_mul, geom_sum_mul]
      simp [hv]
    unfold PP
    rw [map_mul, Module.End.mul_apply, hS, map_zero]

end Formalism.WindowSums
end

namespace Formalism.WindowSums

theorem arc_ZpowVal : ZpowVal := valuation_zpow_sub_one
theorem arc_ValProd : ValProd := valProd_of valuation_zpow_sub_one
theorem arc_KillerVal : KillerVal := killerVal_of valuation_zpow_sub_one
theorem arc_KillerKills : KillerKills := annihilatorPoly_kills
theorem arc_WindowSum : WindowSum := sum_padicValInt_le
theorem arc_Lagrange : Lagrange := lagrange_annihilation

end Formalism.WindowSums
