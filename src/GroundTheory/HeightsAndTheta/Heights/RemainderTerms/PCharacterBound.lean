module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCharacterBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

noncomputable section

theorem symmetricGroupCharacter_eq_cf {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho = cf (fun i => lam i + stair m i) (alternantPsum m rho) :=
  rfl

theorem CharacterBound.proof (h1 : CombTableEqWords.Statement) (h2 : CombCfBound.Statement) :
    CharacterBound.Statement := by
  intro m lam rho hlam hrho
  rw [symmetricGroupCharacter_eq_cf]
  refine (h2 m rho hrho lam hlam).trans ?_
  by_cases hs : ∑ i, lam i = rho.sum
  · rw [h1 m lam hlam, hs]
  · rw [latticeWords_eq_empty_of_sum_ne _ _ hs, Finset.card_empty, Nat.cast_zero]
    exact Nat.cast_nonneg _

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowPrefix
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowPrefix.proof : CombTableauRowPrefix.Statement := by
  intro m lam T hT t
  set c := T.symm t with hc
  have hTc : T c = t := by simp [hc]
  have key : ∀ p : youngCells lam, p.1.1 = c.1.1 →
      ((T p : ℕ) < (t : ℕ) ↔ p.1.2 < c.1.2) := by
    intro p hp
    constructor
    · intro hlt
      by_contra hle'
      have hle := not_lt.mp hle'
      have h := hT c p hp.symm.le hle
      rw [hTc] at h
      exact absurd hlt (not_lt.mpr (Fin.le_def.mp h))
    · intro hlt
      have hle : T p ≤ T c := hT p c hp.le hlt.le
      have hne : p ≠ c := by
        intro h
        rw [h] at hlt
        exact lt_irrefl _ hlt
      have hne' : T p ≠ T c := fun h => hne (T.injective h)
      rw [hTc] at hle hne'
      exact Fin.lt_def.mp (lt_of_le_of_ne hle hne')
  have hcmem : c.1 ∈ youngCells lam := c.2
  simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range] at hcmem
  rw [show (univ.filter fun p : youngCells lam => p.1.1 = c.1.1 ∧ (T p : ℕ) < (t : ℕ)) =
      univ.filter fun p : youngCells lam => p.1.1 = c.1.1 ∧ p.1.2 < c.1.2 from
    filter_congr fun p _ => and_congr_right (key p)]
  refine Eq.trans ?_ (card_range c.1.2)
  refine card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    exact mem_range.mpr hp.2
  · intro p hp q hq hpq
    simp only [mem_filter, mem_univ, true_and] at hp hq
    exact Subtype.ext (Prod.ext (hp.1.trans hq.1.symm) hpq)
  · intro k hk
    rw [mem_range] at hk
    refine ⟨⟨(c.1.1, k), ?_⟩, ?_, rfl⟩
    · simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range]
      exact ⟨by omega, by omega⟩
    · simp [hk]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfUpdateZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Comb

theorem CombCfUpdateZero.proof : CombCfUpdateZero.Statement := by
  intro m A hA lam hlam i hpos hcase

  have key : (i : ℕ) + 1 < m ∧ ∀ h : (i : ℕ) + 1 < m, lam ⟨i + 1, h⟩ = lam i := by
    by_cases h0 : lam i = 0
    · have hs : 1 ≤ stair m i := by omega
      simp only [stair] at hs
      refine ⟨by omega, fun h => ?_⟩
      have := hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))
      omega
    · have hna : ¬ Antitone (Function.update lam i (lam i - 1)) := by
        rcases hcase with h | h
        · exact absurd h h0
        · exact h
      have hK : ∃ b : Fin m, i < b ∧ lam i ≤ lam b := by
        by_contra hK
        push Not at hK
        apply hna
        intro a b hab
        simp only [Function.update_apply]
        split_ifs with hb ha ha
        · exact le_rfl
        · have := hlam (show a ≤ i from hb ▸ hab)
          omega
        · have hib : i < b := lt_of_le_of_ne (ha ▸ hab) (fun e => hb e.symm)
          have := hK b hib
          omega
        · exact hlam hab
      obtain ⟨b, hib, hb⟩ := hK
      have hib' : (i : ℕ) < b := hib
      have hm : (i : ℕ) + 1 < m := by have := b.isLt; omega
      refine ⟨hm, fun h => ?_⟩
      have h1 := hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))
      have h2 := hlam (show (⟨i + 1, h⟩ : Fin m) ≤ b from Fin.le_iff_val_le_val.mpr (by simp; omega))
      omega
  obtain ⟨hm, heq⟩ := key
  have hne : i ≠ (⟨i + 1, hm⟩ : Fin m) := by
    intro e
    have := congrArg Fin.val e
    simp at this
  apply cf_eq_zero_of_eq hA hne
  rw [Function.update_self, Function.update_of_ne hne.symm, heq hm]
  simp only [stair] at hpos ⊢
  omega

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfVandermondePsumOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

theorem CombCfVandermondePsumOne.proof (h1 : CombCfMonomialPsumOne.Statement)
    (h2 : CombDetDescFactorial.Statement) : CombCfVandermondePsumOne.Statement := by
  intro m n l hl
  have hA : alternantPsum m (List.replicate n 1) = alt (stair m) * psum (Fin m) ℚ 1 ^ n := by
    simp only [alternantPsum, List.map_replicate, List.prod_replicate, vandermondeOf_X_eq_alt]
  have hterm : ∀ σ : Perm (Fin m),
      cf l (monomial (ex (stair m ∘ σ.symm)) (1 : ℚ) * psum (Fin m) ℚ 1 ^ n) =
        ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) *
          ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) := by
    intro σ
    rw [h1]
    have hsum : ∑ i, l i = ∑ i, (stair m ∘ σ.symm) i + n := by
      rw [hl, Function.comp_def, Equiv.sum_comp σ.symm (stair m)]
    by_cases hle : ∀ i, (stair m ∘ σ.symm) i ≤ l i
    · rw [if_pos ⟨hle, hsum⟩]
      have hd : ∀ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) =
          ((l i).factorial : ℚ) / ((l i - stair m (σ.symm i)).factorial : ℚ) := by
        intro i
        rw [eq_div_iff (by positivity), mul_comm]
        exact_mod_cast Nat.factorial_mul_descFactorial (hle i)
      simp only [hd, Finset.prod_div_distrib, Function.comp_apply]
      have hp : (∏ i, ((l i).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
      have hq : (∏ i, ((l i - stair m (σ.symm i)).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
      field_simp
    · rw [if_neg (fun h => hle h.1)]
      push Not at hle
      obtain ⟨i, hi⟩ := hle
      simp only [Function.comp_apply] at hi
      have h0 : ∏ j, ((l j).descFactorial (stair m (σ.symm j)) : ℚ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi])
      rw [h0, mul_zero]
  have hdet : ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℚ) *
      ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) = vandermondeOf (fun i => (l i : ℚ)) := by
    rw [← h2 m l, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, ← Equiv.prod_comp σ]
    simp
  rw [hA, alt_eq_sum, Finset.sum_mul, cf_sum]
  simp_rw [smul_mul_assoc, cf_zsmul, hterm]
  calc _ = ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) * ∑ σ : Perm (Fin m),
        ((Perm.sign σ : ℤ) : ℚ) * ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [hdet]; ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Equiv

namespace Comb

theorem add_index_le_of_strictAnti {m : ℕ} {f : Fin m → ℕ} (hf : StrictAnti f) (a b : Fin m)
    (hab : a ≤ b) : f b + (b : ℕ) ≤ f a + (a : ℕ) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have h1 := ih (by omega)
    have h2 : f ⟨n + 1, hb⟩ < f ⟨n, by omega⟩ := hf (by simp [Fin.lt_def])
    simp only at h1 ⊢
    omega

theorem CombSortShift.proof (h1 : CombSortLe.Statement) : CombSortShift.Statement := by
  intro m lam hlam q i hq hinj
  set u := Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) with hu
  obtain ⟨σ, hσ⟩ := exists_perm_strictAnti hinj
  have hge : ∀ k : Fin m, stair m k ≤ u (σ k) := by
    intro k
    have hk := add_index_le_of_strictAnti hσ k ⟨m - 1, by have := k.isLt; omega⟩ (by rw [Fin.le_def]; exact Nat.le_sub_one_of_lt k.isLt)
    simp only [Function.comp_apply] at hk
    simp only [stair]
    omega
  refine ⟨σ, fun k => u (σ k) - stair m k, ?_, ?_, ?_⟩
  · intro a b hab
    have h := add_index_le_of_strictAnti hσ a b hab
    have ha := hge a
    have hb := hge b
    simp only [Function.comp_apply, stair] at h ha hb ⊢
    omega
  · intro k
    have hl : Antitone (fun j => lam j + stair m j) := by
      intro a b hab
      have := hlam hab
      simp only [stair]
      have : (a : ℕ) ≤ b := hab
      omega
    have hul : ∀ j, u j ≤ lam j + stair m j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [hu]
      · simp [hu, Function.update_of_ne hj]
    have := h1 m u (fun j => lam j + stair m j) σ hl hul hσ.antitone k
    show u (σ k) - stair m k ≤ lam k
    omega
  · intro k
    have := hge k
    show u (σ k) = u (σ k) - stair m k + stair m k
    omega

end Comb

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfAtStair
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

theorem Comb.stair_strictAnti (m : ℕ) : StrictAnti (stair m) := by
  intro a b hab
  have hb := b.isLt
  have hab' : (a : ℕ) < b := hab
  simp only [stair]
  omega

theorem CombCfAtStair.proof (h1 : CombCfUpdateZero.Statement) : CombCfAtStair.Statement := by
  intro m n
  induction n with
  | zero =>
    intro lam hlam
    have hs := Comb.stair_strictAnti m
    have hl : StrictAnti (fun i => lam i + stair m i) := by
      intro a b hab
      have h2 := hlam hab.le
      have h3 := hs hab
      simp only
      omega
    simp only [alternantPsum, List.replicate_zero, List.map_nil, List.prod_nil, mul_one,
      vandermondeOf_X_eq_alt]
    rw [cf_alt_of_strictAnti hl hs]
    by_cases h0 : lam = 0
    · subst h0
      have hu : latticeWords 0 (0 : Fin m → ℕ) = univ := by
        rw [Finset.eq_univ_iff_forall]
        intro w
        simp only [latticeWords, mem_filter, mem_univ, true_and]
        refine ⟨fun t ht i j _ => ?_, fun i => pcnt_zero w i⟩
        have ht0 : t = 0 := by omega
        subst ht0
        rw [pcnt_zero, pcnt_zero]
      rw [hu, Finset.card_univ]
      simp
    · have hne : (fun i => lam i + stair m i) ≠ stair m := by
        intro h
        apply h0
        funext i
        have := congrFun h i
        show lam i = 0
        omega
      rw [if_neg hne, latticeWords_eq_empty_of_sum_ne]
      · simp
      · intro hsum
        apply h0
        funext i
        have := (Finset.sum_eq_zero_iff.mp hsum) i (mem_univ i)
        simpa using this
  | succ n ih =>
    intro lam hlam
    have hsplit : alternantPsum m (List.replicate (n + 1) 1) =
        alternantPsum m (List.replicate n 1) * psum (Fin m) ℚ 1 := by
      simp only [alternantPsum, List.replicate_succ', List.map_append, List.prod_append,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rw [hsplit, cf_mul_psum, card_latticeWords_succ n lam hlam, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_ite, Nat.cast_zero]
    by_cases hgood : 1 ≤ lam i ∧ Antitone (Function.update lam i (lam i - 1))
    · rw [if_pos (by omega), if_pos hgood.1]
      have hup : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - 1) =
          fun j => Function.update lam i (lam i - 1) j + stair m j := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [Function.update_self]
          omega
        · simp only [Function.update_of_ne hj]
      rw [hup]
      exact ih _ hgood.2
    · have hR : (if 1 ≤ lam i then
          (((latticeWords n (Function.update lam i (lam i - 1))).card : ℕ) : ℚ) else 0) = 0 := by
        split_ifs with hi
        · rw [latticeWords_eq_empty_of_not_antitone n _ (fun h => hgood ⟨hi, h⟩)]
          simp
        · rfl
      rw [hR]
      split_ifs with hL
      · refine h1 m _ (isAlt_vandermonde_mul_prod _) lam hlam i hL ?_
        by_cases hi : lam i = 0
        · exact Or.inl hi
        · exact Or.inr fun h => hgood ⟨by omega, h⟩
      · rfl

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

namespace CombCfBound

theorem abs_cf_perm {m : ℕ} {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (σ : Perm (Fin m))
    (v : Fin m → ℕ) : |cf (v ∘ σ.symm) P| = |cf v P| := by
  rw [cf_perm hP σ v, abs_mul]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]

theorem alternantPsum_cons (m q : ℕ) (ρ : List ℕ) :
    alternantPsum m (q :: ρ) = alternantPsum m ρ * psum (Fin m) ℚ q := by
  unfold alternantPsum
  simp only [List.map_cons, List.prod_cons]
  ring

theorem isAlt_alternantPsum (m : ℕ) (ρ : List ℕ) : IsAlt (alternantPsum m ρ) :=
  isAlt_vandermonde_mul_prod ρ

theorem stair_strictAnti (m : ℕ) : StrictAnti (stair m) := by
  intro i j h
  have hij : (i : ℕ) < j := h
  have := j.isLt
  simp only [stair]
  omega

theorem bound_nil (m : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    |cf (fun i => lam i + stair m i) (alternantPsum m [])| ≤ ((latticeWords 0 lam).card : ℚ) := by
  have hA : alternantPsum m [] = alt (stair m) := by
    simp [alternantPsum, vandermondeOf_X_eq_alt]
  have hl : StrictAnti (fun i => lam i + stair m i) := fun i j h =>
    Nat.add_lt_add_of_le_of_lt (hlam h.le) (stair_strictAnti m h)
  rw [hA, cf_alt_of_strictAnti hl (stair_strictAnti m)]
  split_ifs with h
  · have h0 : lam = 0 := by
      funext i
      have := congrFun h i
      show lam i = 0
      omega
    subst h0
    have hne : (latticeWords 0 (0 : Fin m → ℕ)).Nonempty := by
      refine ⟨Fin.elim0, ?_⟩
      simp only [latticeWords, mem_filter, mem_univ, true_and]
      refine ⟨fun t _ i j _ => ?_, fun i => ?_⟩
      · simp [pcnt]
      · simp [pcnt]
    rw [abs_one, Nat.one_le_cast]
    exact Finset.card_pos.mpr hne
  · simp

theorem proof (h1 : CombCfAtStair.Statement) (h2 : CombSortShift.Statement)
    (h3 : CombStripSum.Statement) : CombCfBound.Statement := by
  intro m ρ
  induction ρ with
  | nil => intro _ lam hlam; exact bound_nil m lam hlam
  | cons q ρ ih =>
    intro hpos lam hlam
    have hq : 1 ≤ q := hpos q (by simp)
    have ih' := ih (fun r hr => hpos r (List.mem_cons_of_mem _ hr))
    have hterm : ∀ i : Fin m,
        |(if q ≤ lam i + stair m i then
          cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m ρ) else 0)| ≤
        (if q ≤ lam i + stair m i then
          |cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m (List.replicate ρ.sum 1))| else 0) := by
      intro i
      split_ifs with hqi
      · by_cases hinj :
            Function.Injective (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
        · obtain ⟨σ, μ, hμ, -, hσ⟩ := h2 m lam hlam q i hqi hinj
          have hu : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) =
              (fun k => μ k + stair m k) ∘ σ.symm := by
            funext k
            have := hσ (σ.symm k)
            rwa [Equiv.apply_symm_apply] at this
          rw [hu, abs_cf_perm (isAlt_alternantPsum m ρ), abs_cf_perm (isAlt_alternantPsum m _),
            h1 m ρ.sum μ hμ, Nat.abs_cast]
          exact ih' μ hμ
        · simp only [Function.Injective, not_forall] at hinj
          obtain ⟨a, b, hab, hne⟩ := hinj
          rw [cf_eq_zero_of_eq (isAlt_alternantPsum m ρ) hne hab, abs_zero]
          exact abs_nonneg _
      · simp
    rw [alternantPsum_cons, cf_mul_psum]
    calc _ ≤ ∑ i : Fin m, |(if q ≤ lam i + stair m i then
          cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m ρ) else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ((latticeWords (ρ.sum + q) lam).card : ℚ) := h3 m ρ.sum q lam hlam hq
      _ = ((latticeWords (q :: ρ).sum lam).card : ℚ) := by rw [List.sum_cons, add_comm]

end CombCfBound

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombExtendWord
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

noncomputable section

open scoped Classical

namespace CombExtendWord

theorem snoc_mem {m n : ℕ} (lam : Fin m → ℕ) (hlam : Antitone lam) (k : Fin m) (hk : 1 ≤ lam k)
    (v : Fin n → Fin m) (hv : v ∈ latticeWords n (Function.update lam k (lam k - 1))) :
    (Fin.snoc v k : Fin (n + 1) → Fin m) ∈ latticeWords (n + 1) lam := by
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hv ⊢
  obtain ⟨hlat, hcont⟩ := hv
  refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
  · rcases Nat.lt_or_ge t (n + 1) with htn | htn
    · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
      exact hlat t (by omega) i j hij
    · have ht' : t = n + 1 := by omega
      subst ht'
      rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam k i hk,
        update_pred_sub lam k j hk]
      exact hlam hij
  · rw [pcnt_snoc_last, hcont, update_pred_sub lam k i hk]

theorem exists_word {m : ℕ} (h1 : CombPcntAppend.Statement) (μ : Fin m → ℕ) (hμ : Antitone μ) :
    ∀ (q : ℕ) (lam : Fin m → ℕ), Antitone lam → (∀ i, μ i ≤ lam i) →
      ∑ i, lam i = ∑ i, μ i + q →
        ∃ s : Fin q → Fin m, ∀ n, ∀ w ∈ latticeWords n μ,
          Fin.append w s ∈ latticeWords (n + q) lam := by
  intro q
  induction q with
  | zero =>
    intro lam _ hle hsum
    have heq : ∀ i, μ i = lam i := by
      have := (Finset.sum_eq_sum_iff_of_le (s := univ) (fun i _ => hle i)).mp (by simpa using hsum.symm)
      exact fun i => this i (mem_univ i)
    refine ⟨Fin.elim0, fun n w hw => ?_⟩
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
    have hp : ∀ t i, pcnt (Fin.append w (Fin.elim0 : Fin 0 → Fin m)) t i = pcnt w t i := by
      intro t i
      rw [h1]
      have : pcnt (Fin.elim0 : Fin 0 → Fin m) (t - n) i = 0 := by unfold pcnt; simp
      omega
    refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
    · rw [hp, hp]; exact hw.1 t ht i j hij
    · rw [hp, Nat.add_zero, hw.2 i, heq i]
  | succ q ih =>
    intro lam hlam hle hsum
    have hne : (univ.filter (fun i => μ i < lam i)).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      have : ∑ i, lam i ≤ ∑ i, μ i :=
        Finset.sum_le_sum fun i _ => not_lt.mp (hemp (mem_univ i))
      omega
    obtain ⟨k, hk, hkmax⟩ : ∃ k, μ k < lam k ∧ ∀ j, μ j < lam j → j ≤ k :=
      ⟨_, (mem_filter.mp (max'_mem _ hne)).2,
        fun j hj => le_max' _ j (mem_filter.mpr ⟨mem_univ j, hj⟩)⟩
    have hgt : ∀ j, k < j → lam j = μ j := by
      intro j hj
      by_contra hne'
      exact absurd (hkmax j (lt_of_le_of_ne (hle j) (Ne.symm hne'))) (not_le.mpr hj)
    have hanti : Antitone (Function.update lam k (lam k - 1)) := by
      intro i j hij
      by_cases hik : i = k <;> by_cases hjk : j = k
      · rw [hik, hjk]
      · rw [hik, Function.update_self, Function.update_of_ne hjk]
        have hkj : k < j := lt_of_le_of_ne (hik ▸ hij) (Ne.symm hjk)
        rw [hgt j hkj]
        have := hμ (hik ▸ hij)
        omega
      · rw [hjk, Function.update_self, Function.update_of_ne hik]
        have := hlam (hjk ▸ hij)
        omega
      · rw [Function.update_of_ne hik, Function.update_of_ne hjk]
        exact hlam hij
    have hle' : ∀ i, μ i ≤ Function.update lam k (lam k - 1) i := by
      intro i
      by_cases hik : i = k
      · rw [hik, Function.update_self]; omega
      · rw [Function.update_of_ne hik]; exact hle i
    have hsum' : ∑ i, Function.update lam k (lam k - 1) i = ∑ i, μ i + q := by
      have h2 : ∀ i, Function.update lam k (lam k - 1) i + (if k = i then 1 else 0) = lam i :=
        fun i => update_pred_sub lam k i (by omega)
      have : ∑ i, lam i = ∑ i, Function.update lam k (lam k - 1) i + 1 := by
        rw [← Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib, Finset.sum_ite_eq]
        simp
      omega
    obtain ⟨s', hs'⟩ := ih _ hanti hle' hsum'
    refine ⟨Fin.snoc s' k, fun n w hw => ?_⟩
    rw [Fin.append_snoc]
    exact snoc_mem lam hlam k (by omega) _ (hs' n w hw)

theorem proof (h1 : CombPcntAppend.Statement) : CombExtendWord.Statement := by
  intro m n q μ lam hμ hlam hle hsum
  obtain ⟨s, hs⟩ := exists_word h1 μ hμ q lam hlam hle hsum
  exact ⟨s, hs n⟩

end CombExtendWord

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfMonomialPsumOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

namespace CombCfMonomialPsumOne

theorem sum_update_sub_one {m : ℕ} (l : Fin m → ℕ) (i : Fin m) (h : 1 ≤ l i) :
    ∑ j, Function.update l i (l i - 1) j + 1 = ∑ j, l j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) l]
  omega

theorem prod_factorial_update_sub_one {m : ℕ} (l v : Fin m → ℕ) (i : Fin m) (hi : v i < l i) :
    (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) * ((l i - v i : ℕ) : ℚ) =
      ∏ j, ((l j - v j).factorial : ℚ) := by
  have hf : (fun j => ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) =
      Function.update (fun j => ((l j - v j).factorial : ℚ)) i ((l i - 1 - v i).factorial : ℚ) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j => ((l j - v j).factorial : ℚ))]
  have h : l i - v i = (l i - 1 - v i) + 1 := by omega
  rw [h, Nat.factorial_succ]
  push_cast
  ring

end CombCfMonomialPsumOne


open CombCfMonomialPsumOne in
theorem CombCfMonomialPsumOne.proof : CombCfMonomialPsumOne.Statement := by
  intro m n v l
  induction n generalizing l with
  | zero =>
    rw [pow_zero, mul_one, cf_monomial]
    by_cases h : l = v
    · subst h; simp
    · rw [if_neg h, if_neg]
      rintro ⟨hle, hs⟩
      apply h
      funext i
      have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => hle i)).1
        (by simpa using hs.symm)
      exact (this i (Finset.mem_univ _)).symm
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, cf_mul_psum]
    simp only [ih]
    by_cases hC : (∀ i, v i ≤ l i) ∧ ∑ i, l i = ∑ i, v i + (n + 1)
    · rw [if_pos hC]
      obtain ⟨hle, hs⟩ := hC
      have hP : (∏ j, ((l j - v j).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ => by positivity
      rw [Finset.sum_congr rfl (g := fun i => (n.factorial : ℚ) * ((l i - v i : ℕ) : ℚ) /
          ∏ j, ((l j - v j).factorial : ℚ)) ?_]
      · rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum]
        have hsub : ∑ i, (l i - v i) + ∑ i, v i = ∑ i, l i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
        rw [show ∑ i, (l i - v i) = n + 1 by omega, Nat.factorial_succ]
        push_cast
        ring
      · intro i _
        by_cases hi : v i < l i
        · have h1 : 1 ≤ l i := by omega
          have hle' : ∀ j, v j ≤ Function.update l i (l i - 1) j := fun j => by
            by_cases hj : j = i
            · subst hj; simp; omega
            · simp [Function.update_of_ne hj, hle j]
          have hs' := sum_update_sub_one l i h1
          rw [if_pos h1, if_pos ⟨hle', by omega⟩, ← prod_factorial_update_sub_one l v i hi]
          have hne : ((l i - v i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : l i - v i ≠ 0)
          have hQ : (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) ≠ 0 :=
            Finset.prod_ne_zero_iff.2 fun j _ => by positivity
          field_simp
        · have heq : l i = v i := le_antisymm (not_lt.1 hi) (hle i)
          rw [show ((l i - v i : ℕ) : ℚ) = 0 by rw [heq]; simp, mul_zero, zero_div]
          by_cases h1 : 1 ≤ l i
          · rw [if_pos h1, if_neg]
            rintro ⟨h, _⟩
            have := h i
            simp at this
            omega
          · rw [if_neg h1]
    · rw [if_neg hC]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h1 : 1 ≤ l i
      · rw [if_pos h1]
        by_cases h2 : (∀ j, v j ≤ Function.update l i (l i - 1) j) ∧
            ∑ j, Function.update l i (l i - 1) j = ∑ j, v j + n
        · exfalso
          apply hC
          obtain ⟨hle', hs'⟩ := h2
          have hle : ∀ j, v j ≤ l j := fun j => (hle' j).trans (by
            by_cases hj : j = i
            · subst hj; simp
            · simp [Function.update_of_ne hj])
          have := sum_update_sub_one l i h1
          exact ⟨hle, by omega⟩
        · rw [if_neg h2]
      · rw [if_neg h1]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombStripSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

theorem CombStripSum.proof (h1 : CombCfAtStair.Statement) (h2 : CombSortShift.Statement)
    (h3 : CombSortShiftDistinct.Statement) (h4 : CombExtendWord.Statement) :
    CombStripSum.Statement := by
  classical
  intro m n q lam hlam hq
  set l : Fin m → ℕ := fun j => lam j + stair m j with hl
  have hAlt : IsAlt (alternantPsum m (List.replicate n 1)) := isAlt_vandermonde_mul_prod _
  have hl_inj : Function.Injective l := by
    intro a b hab
    simp only [hl, stair] at hab
    have ha := a.isLt
    have hb := b.isLt
    rcases lt_trichotomy a b with h | h | h
    · have h' := hlam h.le
      have : (a : ℕ) < b := h
      omega
    · exact h
    · have h' := hlam h.le
      have : (b : ℕ) < a := h
      omega

  have key : ∀ i : Fin m, q ≤ l i → Function.Injective (Function.update l i (l i - q)) →
      ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m,
        (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧
        |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| =
          ((latticeWords n μ).card : ℚ) ∧
        ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam := by
    intro i hqi hinj
    obtain ⟨σ, μ, hμ, hμle, hσ0⟩ := h2 m lam hlam q i hqi hinj
    have hσ : ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k := hσ0
    have hsum : ∑ k, lam k = ∑ k, μ k + q := by
      have e1 : ∑ k, (μ k + stair m k) = ∑ k, Function.update l i (l i - q) k := by
        rw [← Equiv.sum_comp σ (Function.update l i (l i - q))]
        exact Finset.sum_congr rfl fun k _ => (hσ k).symm
      have e4 : ∑ k, l k = ∑ k, lam k + ∑ k, stair m k := Finset.sum_add_distrib
      have e3 : ∀ k, l k = Function.update l i (l i - q) k + if k = i then q else 0 := by
        intro k
        by_cases hk : k = i
        · subst hk; simp only [Function.update_self, if_true]; omega
        · simp [hk]
      have e2 : ∑ k, l k = ∑ k, Function.update l i (l i - q) k + q := by
        rw [Finset.sum_congr rfl (fun k _ => e3 k), Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [Finset.sum_add_distrib] at e1
      omega
    obtain ⟨s, hs⟩ := h4 m n q μ lam hμ hlam hμle hsum
    refine ⟨μ, s, ⟨σ, hσ⟩, ?_, hs⟩
    have hu : Function.update l i (l i - q) = (fun k => μ k + stair m k) ∘ σ.symm := by
      funext k
      rw [Function.comp_apply, ← hσ (σ.symm k), Equiv.apply_symm_apply]
    rw [hu, cf_perm hAlt, abs_mul, h1 m n μ hμ]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
  have key' : ∀ i : Fin m, ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m,
      (q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) →
        (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧
        |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| =
          ((latticeWords n μ).card : ℚ) ∧
        ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam := by
    intro i
    by_cases h : q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))
    · obtain ⟨μ, s, hs⟩ := key i h.1 h.2
      exact ⟨μ, s, fun _ => hs⟩
    · exact ⟨fun _ => 0, fun _ => i, fun h' => absurd h' h⟩
  choose μ s hμs using key'
  set S := univ.filter
    (fun i : Fin m => q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) with hS
  change ∑ i : Fin m, (if q ≤ l i then
      |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) ≤ _
  have hsum_eq : ∑ i : Fin m, (if q ≤ l i then
      |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) =
      ∑ i ∈ S, ((latticeWords n (μ i)).card : ℚ) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hqi : q ≤ l i
    · by_cases hinj : Function.Injective (Function.update l i (l i - q))
      · rw [if_pos hqi, if_pos ⟨hqi, hinj⟩, (hμs i ⟨hqi, hinj⟩).2.1]
      · rw [if_pos hqi, if_neg (fun h => hinj h.2)]
        simp only [Function.Injective, not_forall] at hinj
        obtain ⟨a, b, hab, hne⟩ := hinj
        rw [cf_eq_zero_of_eq hAlt hne hab, abs_zero]
    · rw [if_neg hqi, if_neg (fun h => hqi h.1)]
  rw [hsum_eq]
  have hcard : ∑ i ∈ S, (latticeWords n (μ i)).card ≤ (latticeWords (n + q) lam).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn (fun x => Fin.append x.2 (s x.1)) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_sigma] at hx
      exact (hμs x.1 (Finset.mem_filter.mp hx.1).2).2.2 x.2 hx.2
    · rintro ⟨i, w⟩ hx ⟨j, w'⟩ hy hxy
      rw [Finset.mem_coe, Finset.mem_sigma] at hx hy
      simp only at hxy hx hy
      have hw : w = w' := by
        funext k
        have := congrFun hxy (Fin.castAdd q k)
        simpa only [Fin.append_left] using this
      subst hw
      have hμij : μ i = μ j := by
        funext k
        have a1 := (Finset.mem_filter.mp hx.2).2.2 k
        have a2 := (Finset.mem_filter.mp hy.2).2.2 k
        rw [← a1, ← a2]
      have hSi := (Finset.mem_filter.mp hx.1).2
      have hSj := (Finset.mem_filter.mp hy.1).2
      have hij : i = j := by
        by_contra hij
        obtain ⟨σ, hσ⟩ := (hμs i hSi).1
        obtain ⟨τ, hτ⟩ := (hμs j hSj).1
        refine h3 m l hl_inj q hq i j hij hSi.1 hSj.1 σ τ ?_
        funext k
        rw [Function.comp_apply, Function.comp_apply, hσ k, hτ k, hμij]
      subst hij
      rfl
  exact_mod_cast hcard

end

end GroundTheory.Heights₂.Heights.RestTerms
end
