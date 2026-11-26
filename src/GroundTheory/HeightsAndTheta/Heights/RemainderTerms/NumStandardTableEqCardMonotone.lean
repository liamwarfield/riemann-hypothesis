module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Expand

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics

open MvPolynomial Finset

theorem card_monotone_equiv_congr {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
    {n n' : ℕ} (h : n = n') :
    Nat.card {T : α ≃ Fin n // Monotone T} = Nat.card {T : β ≃ Fin n' // Monotone T} := by
  subst h
  exact Nat.card_congr
    { toFun := fun T => ⟨e.symm.toEquiv.trans T.1, fun a b hab => T.2 (e.symm.monotone hab)⟩
      invFun := fun T => ⟨e.toEquiv.trans T.1, fun a b hab => T.2 (e.monotone hab)⟩
      left_inv := fun T => by ext x; simp
      right_inv := fun T => by ext x; simp }

theorem mem_youngCells {m : ℕ} (lam : Fin m → ℕ) (x : Fin m × ℕ) :
    x ∈ RestTerms.youngCells lam ↔ x.2 < lam x.1 := by
  unfold RestTerms.youngCells
  simp only [mem_filter, mem_product, mem_univ, mem_range, true_and]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨lt_of_lt_of_le h (Finset.single_le_sum (fun i _ => Nat.zero_le (lam i))
      (mem_univ x.1)), h⟩

theorem mem_shapeCells {r : ℕ} (la : Fin r → ℕ) (x : ℕ × ℕ) :
    x ∈ IndefiniteRowSideFullHecke.RestTerms.shapeCells la ↔ ∃ h : x.1 < r, x.2 < la ⟨x.1, h⟩ := by
  unfold IndefiniteRowSideFullHecke.RestTerms.shapeCells
  simp only [mem_biUnion, mem_univ, true_and, mem_image, mem_range]
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a.2, hb⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x.1, h⟩, x.2, hx, rfl⟩

def cellIso {r : ℕ} (la : Fin r → ℕ) :
    RestTerms.youngCells la ≃o IndefiniteRowSideFullHecke.RestTerms.shapeCells la where
  toFun p := ⟨((p.1.1 : ℕ), p.1.2),
    (mem_shapeCells la _).2 ⟨p.1.1.2, (mem_youngCells la _).1 p.2⟩⟩
  invFun q := ⟨(⟨q.1.1, ((mem_shapeCells la _).1 q.2).1⟩, q.1.2),
    (mem_youngCells la _).2 ((mem_shapeCells la _).1 q.2).2⟩
  left_inv p := rfl
  right_inv q := rfl
  map_rel_iff' := by
    rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨c, d⟩, hq⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Prod.mk_le_mk, Fin.le_def]

theorem numStandardTable_eq_card_monotone {m : ℕ} (lam : Fin m → ℕ) :
    RestTerms.numStandardTable lam =
      Nat.card {T : RestTerms.youngCells lam ≃ Fin (RestTerms.youngCells lam).card //
        Monotone T} := by
  unfold RestTerms.numStandardTable
  refine Nat.card_congr (Equiv.subtypeEquivRight fun T => ?_)
  constructor
  · intro h p q hpq
    have h' := Prod.le_def.1 (Subtype.coe_le_coe.2 hpq)
    exact h p q h'.1 h'.2
  · intro h p q h1 h2
    exact h (Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h1, h2⟩))

theorem numSYT_eq {r : ℕ} (la : Fin r → ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.numSYT la = RestTerms.numStandardTable la := by
  rw [numStandardTable_eq_card_monotone]
  unfold IndefiniteRowSideFullHecke.RestTerms.numSYT
  refine (card_monotone_equiv_congr (cellIso la) ?_).symm
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (cellIso la).toEquiv

theorem shapeCells_hookShape (r k b : ℕ) (hb : b < r) :
    IndefiniteRowSideFullHecke.RestTerms.shapeCells (IndefiniteRowSideFullHecke.RestTerms.hookShape k b) =
      IndefiniteRowSideFullHecke.RestTerms.shapeCells (RestTerms.hookShape r k b) := by
  ext x
  rw [mem_shapeCells, mem_shapeCells]
  simp only [RestTerms.hookShape, IndefiniteRowSideFullHecke.RestTerms.hookShape]
  constructor
  · rintro ⟨h, hx⟩
    refine ⟨by omega, ?_⟩
    split_ifs at hx ⊢ <;> omega
  · rintro ⟨h, hx⟩
    have h' : x.1 < b + 1 := by
      by_contra hc
      split_ifs at hx <;> omega
    refine ⟨h', ?_⟩
    split_ifs at hx ⊢ <;> omega

theorem numSYT_hookShape (r k b : ℕ) (hb : b < r) :
    IndefiniteRowSideFullHecke.RestTerms.numSYT (IndefiniteRowSideFullHecke.RestTerms.hookShape k b) =
      RestTerms.numStandardTable (RestTerms.hookShape r k b) := by
  rw [← numSYT_eq]
  unfold IndefiniteRowSideFullHecke.RestTerms.numSYT
  rw [shapeCells_hookShape r k b hb]

end GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Lattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.Comb

open MvPolynomial Finset Equiv

noncomputable section

open scoped Classical

variable {m : ℕ}

def pcnt {n : ℕ} (w : Fin n → Fin m) (t : ℕ) (i : Fin m) : ℕ :=
  (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = i)).card

def IsLattice {n : ℕ} (w : Fin n → Fin m) : Prop :=
  ∀ t ≤ n, ∀ i j : Fin m, i ≤ j → pcnt w t j ≤ pcnt w t i

def latticeWords (n : ℕ) (lam : Fin m → ℕ) : Finset (Fin n → Fin m) :=
  univ.filter (fun w => IsLattice w ∧ ∀ i, pcnt w n i = lam i)

theorem pcnt_castSucc_snoc {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (t : ℕ) (ht : t ≤ n) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) t i = pcnt w t i := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  rw [if_neg (by omega), add_zero]

theorem pcnt_snoc_last {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) (n + 1) i = pcnt w n i + if a = i then 1 else 0 := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    have := s.isLt
    by_cases h : w s = i <;> simp [h, this, Nat.lt_succ_of_lt this]
  · simp

theorem pcnt_zero {n : ℕ} (w : Fin n → Fin m) (i : Fin m) : pcnt w 0 i = 0 := by
  unfold pcnt; simp

theorem pcnt_le_of_le {n : ℕ} (w : Fin n → Fin m) {t t' : ℕ} (h : t ≤ t') (i : Fin m) :
    pcnt w t i ≤ pcnt w t' i := by
  unfold pcnt
  exact Finset.card_le_card (fun s => by simp only [mem_filter, mem_univ, true_and]; omega)

theorem sum_pcnt {n : ℕ} (w : Fin n → Fin m) : ∑ i, pcnt w n i = n := by
  unfold pcnt
  rw [← Finset.card_biUnion]
  · have : (univ : Finset (Fin m)).biUnion (fun i => univ.filter (fun s : Fin n => (s : ℕ) < n ∧ w s = i))
        = univ := by
      ext s; simp
    rw [this, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_filter]
    rintro s _ ⟨_, h1⟩ ⟨_, h2⟩
    exact hij (h1 ▸ h2)

theorem update_pred_sub (lam : Fin m → ℕ) (a i : Fin m) (h : 1 ≤ lam a) :
    Function.update lam a (lam a - 1) i + (if a = i then 1 else 0) = lam i := by
  by_cases hai : a = i
  · subst hai; simp; omega
  · simp [Function.update_of_ne (Ne.symm hai), hai]

theorem card_latticeWords_succ (n : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (latticeWords (n + 1) lam).card =
      ∑ a : Fin m, if 1 ≤ lam a then (latticeWords n (Function.update lam a (lam a - 1))).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => w (Fin.last n)) (t := univ)
    (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · refine Finset.card_nbij' (fun w => Fin.init w) (fun w => Fin.snoc w a) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨⟨hlat, hcont⟩, hlast⟩ := hw
      have hw' : w = Fin.snoc (Fin.init w) a := by
        rw [← hlast]; exact (Fin.snoc_init_self w).symm
      refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
      · have := hlat t (by omega) i j hij
        rwa [hw', pcnt_castSucc_snoc _ _ _ ht, pcnt_castSucc_snoc _ _ _ ht] at this
      · have := hcont i
        rw [hw', pcnt_snoc_last] at this
        have h2 := update_pred_sub lam a i ha
        omega
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨hlat, hcont⟩ := hw
      refine ⟨⟨fun t ht i j hij => ?_, fun i => ?_⟩, by simp⟩
      · rcases Nat.lt_or_ge t (n + 1) with htn | htn
        · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
          exact hlat t (by omega) i j hij
        · have ht' : t = n + 1 := by omega
          subst ht'
          rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam a i ha,
            update_pred_sub lam a j ha]
          exact hlam hij
      · rw [pcnt_snoc_last, hcont, update_pred_sub lam a i ha]
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq] at hw
      rw [← hw.2]; exact Fin.snoc_init_self w
    · intro w hw
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw hlast
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
    have := hw.2 a
    have h1 : 1 ≤ pcnt w (n + 1) a := by
      unfold pcnt
      exact Finset.card_pos.mpr ⟨Fin.last n, by simp [hlast]⟩
    omega

theorem latticeWords_eq_empty_of_sum_ne (n : ℕ) (lam : Fin m → ℕ) (h : ∑ i, lam i ≠ n) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  rw [← sum_pcnt w]
  exact Finset.sum_congr rfl fun i _ => (hw.2 i).symm

theorem latticeWords_eq_empty_of_not_antitone (n : ℕ) (lam : Fin m → ℕ) (h : ¬ Antitone lam) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  intro i j hij
  rw [← hw.2 i, ← hw.2 j]
  exact hw.1 n le_rfl i j hij

end

end GroundTheory.Heights₂.Heights.RestTerms.Comb
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PrimeWeightEqZeroOfLt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

namespace Elem

def primeWeight (B : ℝ) (i : ℕ) : ℝ := if i.Prime ∧ B < i then Real.log i else 0

theorem primeWeight_nonneg (B : ℝ) (i : ℕ) : 0 ≤ primeWeight B i := by
  unfold primeWeight
  split_ifs
  · exact Real.log_natCast_nonneg i
  · exact le_rfl

theorem sum_primeWeight_le (B : ℝ) (K : ℕ) :
    ∑ i ∈ range (K + 1), primeWeight B i ≤ K * Real.log 4 := by
  have hθ := ChebyshevThetaBound.intersectionNumber_baseChange (K : ℝ) (Nat.cast_nonneg K)
  rw [Nat.floor_natCast] at hθ
  refine le_trans ?_ hθ
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  unfold primeWeight
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd h1.1 h2
  · exact Real.log_natCast_nonneg i
  · exact le_rfl

theorem primeWeight_eq_zero_of_lt (B : ℝ) (hB : 0 ≤ B) {i : ℕ} (hi : i < ⌊B⌋₊ + 1) :
    primeWeight B i = 0 := by
  unfold primeWeight
  rw [if_neg]
  rintro ⟨_, h⟩
  have : (i : ℝ) ≤ B := by
    have := Nat.le_floor_iff hB |>.mp (Nat.lt_succ_iff.mp hi)
    exact this
  linarith

theorem abel_step (B : ℝ) (hB : 0 < B) (j : ℕ) :
    (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i / (i : ℝ) ^ 2) -
        (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i) / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ) ^ 2 ≤
      2 * Real.log 4 * (1 / ((⌊B⌋₊ + 1 : ℕ) : ℝ) - 1 / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ)) := by
  set M := ⌊B⌋₊ + 1 with hM
  induction j with
  | zero =>
    have h0 : ∀ i ∈ range (M + 0), primeWeight B i = 0 := fun i hi =>
      primeWeight_eq_zero_of_lt B hB.le (by have := Finset.mem_range.mp hi; omega)
    rw [Finset.sum_eq_zero (fun i hi => by rw [h0 i hi, zero_div]),
      Finset.sum_eq_zero h0]
    simp
  | succ j ih =>
    set K := M + j with hK
    have hK1 : (1 : ℝ) ≤ K := by
      have : 1 ≤ K := by omega
      exact_mod_cast this
    have hKpos : (0 : ℝ) < K := by linarith
    rw [show M + (j + 1) = K + 1 by omega] at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    set S := ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2
    set G := ∑ i ∈ range K, primeWeight B i
    set g := primeWeight B K
    have hG1 : G + g ≤ K * Real.log 4 := by
      have := sum_primeWeight_le B K
      rw [Finset.sum_range_succ] at this
      exact this
    have hG1nn : 0 ≤ G + g := by
      have : 0 ≤ ∑ i ∈ range (K + 1), primeWeight B i :=
        Finset.sum_nonneg (fun i _ => primeWeight_nonneg B i)
      rw [Finset.sum_range_succ] at this
      exact this
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    push_cast at ih ⊢

    have hdiff : (S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2) -
        (S - G / (K : ℝ) ^ 2) = (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) := by
      field_simp
      ring
    have hnn : 0 ≤ 1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2 := by
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hstep : (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) ≤
        2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by
      calc (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2)
          ≤ (K * Real.log 4) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_right hG1 hnn
        _ = Real.log 4 * ((2 * K + 1) / (K * ((K : ℝ) + 1) ^ 2)) := by
            field_simp
            ring
        _ ≤ Real.log 4 * (2 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left _ hlog4
            rw [show (2 : ℝ) * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) = 2 / (K * ((K : ℝ) + 1)) by
              field_simp; ring]
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
        _ = 2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by ring
    have ih' : S - G / (K : ℝ) ^ 2 ≤ 2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / (K : ℝ)) := by
      simpa using ih
    have : S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2 ≤
        2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / ((K : ℝ) + 1)) := by
      linarith
    simpa using this

theorem prime_partial_le (B : ℝ) (hB : 0 < B) (K : ℕ) :
    ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2 ≤ 2 * Real.log 4 / B := by
  set M := ⌊B⌋₊ + 1 with hM
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hMB : B < (M : ℝ) := by
    rw [hM]; push_cast; exact Nat.lt_floor_add_one B
  have hMpos : (0 : ℝ) < M := lt_trans hB hMB
  have hfinal : 2 * Real.log 4 / (M : ℝ) ≤ 2 * Real.log 4 / B :=
    div_le_div_of_nonneg_left (by positivity) hB hMB.le
  rcases lt_or_ge K M with hK | hK
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro i hi
      rw [primeWeight_eq_zero_of_lt B hB.le (lt_trans (Finset.mem_range.mp hi) hK), zero_div]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
    have hW := abel_step B hB j
    rw [← hM] at hW
    set K := M + j
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : (M : ℝ) ≤ K := by exact_mod_cast (Nat.le_add_right M j)
      linarith
    have hG : ∑ i ∈ range K, primeWeight B i ≤ K * Real.log 4 := by
      calc ∑ i ∈ range K, primeWeight B i ≤ ∑ i ∈ range (K + 1), primeWeight B i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun i _ _ => primeWeight_nonneg B i)
        _ ≤ K * Real.log 4 := sum_primeWeight_le B K
    have hGK : (∑ i ∈ range K, primeWeight B i) / (K : ℝ) ^ 2 ≤ Real.log 4 / K := by
      rw [div_le_div_iff₀ (by positivity) hKpos]
      nlinarith
    have h1 : 0 ≤ Real.log 4 / K := by positivity
    calc ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2
        ≤ 2 * Real.log 4 * (1 / (M : ℝ) - 1 / (K : ℝ)) + Real.log 4 / K := by linarith
      _ = 2 * Real.log 4 / (M : ℝ) - Real.log 4 / K := by ring
      _ ≤ 2 * Real.log 4 / (M : ℝ) := by linarith
      _ ≤ 2 * Real.log 4 / B := hfinal

end Elem


namespace Elem

end Elem


end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestInnerTsumBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestInnerTsumBound.proof : RestInnerTsumBound.Statement := by
  intro p k c M hp hk hc
  obtain ⟨hsum, hle⟩ := GeometricTail.intersectionNumber_baseChange p k hp hk
  have hM : 0 ≤ M := (abs_nonneg (c 0)).trans (hc 0)
  have hnn : ∀ n : ℕ, 0 ≤ (p ^ ((n + 1) * k))⁻¹ := fun n => by
    have : (0 : ℝ) ≤ p := by linarith
    positivity
  have hbound : ∀ n : ℕ, ‖(p ^ ((n + 1) * k))⁻¹ * c n‖ ≤ (p ^ ((n + 1) * k))⁻¹ * M := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn n)]
    exact mul_le_mul_of_nonneg_left (hc n) (hnn n)
  have hsumM : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * M) := hsum.mul_right M
  have hS : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * c n) :=
    Summable.of_norm_bounded hsumM hbound
  refine ⟨hS, ?_⟩
  calc |∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n|
      = ‖∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖(p ^ ((n + 1) * k))⁻¹ * c n‖ := norm_tsum_le_tsum_norm hS.norm
    _ ≤ ∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * M := hS.norm.tsum_le_tsum hbound hsumM
    _ = (∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹) * M := tsum_mul_right
    _ ≤ (2 * (p ^ k)⁻¹) * M := mul_le_mul_of_nonneg_right hle hM
    _ = M * (2 * (p ^ k)⁻¹) := mul_comm _ _

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem choose_two_add (r a : ℕ) :
    (r + a) * (r + a - 1) / 2 = r * (r - 1) / 2 + a * (a - 1) / 2 + r * a := by
  rw [← Finset.sum_range_id, ← Finset.sum_range_id, ← Finset.sum_range_id, Finset.sum_range_add,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

theorem RestPolynomialHomogeneous.proof (h1 : VandermondeOfHomogeneous.Statement) :
    RestPolynomialHomogeneous.Statement := by
  intro f r a c
  have hy : ∀ τ i, (yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)
  have hz : ∀ τ i, (zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X ℚ (zIndex f r a c τ i)
  have hmu : (smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i
  have hfib : (fibreClass f r a c).IsHomogeneous
      (∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2)) :=
    IsHomogeneous.prod _ _ _ fun τ _ =>
      (h1 _ ℚ r (yRoot f r a c τ) (hy τ)).mul (h1 _ ℚ a (zRoot f r a c τ) (hz τ))
  have hF := (hmu.pow (f * (r * a) + 1)).mul hfib
  have hdeg : 1 * (f * (r * a) + 1) + ∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2) =
      topDegree f (r + a) + 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, topDegree,
      choose_two_add]
    ring
  rw [← hdeg]
  exact hF

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.BlockValue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

def gmf (f r a : ℕ) (c : SmallBlock) (q : Fin f → ℕ) (e : ℕ) : RootRing f (r + a) :=
  (∏ σ, blockEmb f (r + a) σ (yEval r a c (extraFactor r (q σ)))) * smallBlockMu f r a c ^ e *
    fibreClass f r a c

def gmfOut (f r a : ℕ) (c : SmallBlock) (κ : ℚ) (q : Fin f → ℕ) (e : ℕ) : RootRing f (r + a) :=
  ∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e,
    (Nat.multinomial Finset.univ m : ℚ) •
      ∏ σ, blockEmb f (r + a) σ (blockOut r a c κ (q σ) (m σ))

theorem hasDD_gmf (hF : FrobeniusCharacterFormula.Statement) (f r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (q : Fin f → ℕ) (e : ℕ) :
    HasDD f (r + a) (gmf f r a c q e) (gmfOut f r a c κ q e) := by
  rw [gmf, expand_blocks, gmfOut]
  refine hasDD_sum _ fun m _ => hasDD_smul _ (hasDD_prod f (r + a) _ _ fun σ => ?_)
  exact hasDD_block hF r a c κ hκ (q σ) (m σ)

def toN (N : ℕ) : RootRing 1 N →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  aeval (fun p : Fin 1 × Fin N => X p.2)

theorem restrictToBlock_blockEmb (f N : ℕ) (τ σ : Fin f) (P : RootRing 1 N) :
    restrictToBlock f N τ (blockEmb f N σ P) =
      if σ = τ then toN N P else C (constantCoeff P) := by
  have key : (restrictToBlock f N τ).comp (blockEmb f N σ) =
      aeval (fun p : Fin 1 × Fin N => if σ = τ then X p.2 else 0) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [restrictToBlock, blockEmb]
  have := congrArg (fun φ : RootRing 1 N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ P) key
  simp only [AlgHom.comp_apply] at this
  rw [this]
  split_ifs with h
  · rfl
  · rw [show (fun _ : Fin 1 × Fin N => (0 : MvPolynomial (Fin N) ℚ)) = 0 from rfl,
      MvPolynomial.aeval_zero, MvPolynomial.algebraMap_eq]

theorem toN_xSign (r a : ℕ) (c : SmallBlock) (p : MvPolynomial (Fin (r + a)) ℚ) :
    toN (r + a) (xSign r a c p) = aeval (fun i : Fin (r + a) => C c.sign * X i) p := by
  have key : (toN (r + a)).comp (xSign r a c) =
      aeval (fun i : Fin (r + a) => C c.sign * X i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [toN, xSign]
  exact congrArg (fun φ : MvPolynomial (Fin (r + a)) ℚ →ₐ[ℚ] MvPolynomial (Fin (r + a)) ℚ => φ p) key

def mstar (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f) : Fin f → ℕ :=
  fun σ => if σ = τ then e - ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') else r * a - q σ

theorem mstar_mem (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f)
    (he : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') ≤ e) :
    mstar f r a q e τ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e := by
  rw [Finset.mem_piAntidiag]
  refine ⟨?_, fun i _ => Finset.mem_univ i⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ)]
  have : ∑ x ∈ Finset.univ.erase τ, mstar f r a q e τ x =
      ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') :=
    Finset.sum_congr rfl fun x hx => by simp [mstar, Finset.ne_of_mem_erase hx]
  rw [this]
  simp only [mstar, if_true]
  omega

theorem eq_mstar_of (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f) (m : Fin f → ℕ)
    (hm : m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e)
    (h : ∀ σ, σ ≠ τ → m σ = r * a - q σ) : m = mstar f r a q e τ := by
  funext σ
  by_cases hσ : σ = τ
  · subst hσ
    rw [Finset.mem_piAntidiag] at hm
    have hs := hm.1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ)] at hs
    have : ∑ x ∈ Finset.univ.erase σ, m x = ∑ σ' ∈ Finset.univ.erase σ, (r * a - q σ') :=
      Finset.sum_congr rfl fun x hx => h x (Finset.ne_of_mem_erase hx)
    simp only [mstar, if_true]
    omega
  · simp [mstar, hσ, h σ hσ]

theorem restrict_gmfOut (f r a : ℕ) (c : SmallBlock) (κ : ℚ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f)
    (hq : ∀ σ, σ ≠ τ → q σ ≤ r * a)
    (he : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') ≤ e) :
    restrictToBlock f (r + a) τ (gmfOut f r a c κ q e) =
      ((Nat.multinomial Finset.univ (mstar f r a q e τ) : ℚ) *
          ∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ)) •
        toN (r + a) (blockOut r a c κ (q τ) (mstar f r a q e τ τ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gmfOut, map_sum]
  rw [Finset.sum_eq_single (mstar f r a q e τ)]
  · rw [map_smul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
    rw [restrictToBlock_blockEmb, if_pos rfl]
    have : ∏ x ∈ Finset.univ.erase τ, restrictToBlock f (r + a) τ
        (blockEmb f (r + a) x (blockOut r a c κ (q x) (mstar f r a q e τ x))) =
        C (∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun σ hσ => ?_
      have hne := Finset.ne_of_mem_erase hσ
      rw [restrictToBlock_blockEmb, if_neg hne, constantCoeff_blockOut]
      simp only [mstar, if_neg hne]
      rw [if_pos (by have := hq σ hne; omega)]
    rw [this, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_natCast]
    ring
  · intro m hm hne
    obtain ⟨σ, hστ, hσ⟩ : ∃ σ, σ ≠ τ ∧ m σ ≠ r * a - q σ := by
      by_contra hcon
      push Not at hcon
      exact hne (eq_mstar_of f r a q e τ m hm hcon)
    rw [map_smul, map_prod, Finset.prod_eq_zero (Finset.mem_univ σ), smul_zero]
    rw [restrictToBlock_blockEmb, if_neg hστ, constantCoeff_blockOut, if_neg, map_zero]
    have := hq σ hστ
    omega
  · intro h
    exact absurd (mstar_mem f r a q e τ he) h

theorem mem_partitionsOf_iff {m n : ℕ} (lam : Fin m → ℕ) :
    lam ∈ partitionsOf m n ↔ ∑ i, lam i = n ∧ Antitone lam := by
  simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  exact Iff.rfl

theorem toN_blockOut (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m k : ℕ) (hk : q + m = k + r * a) :
    toN (r + a) (blockOut r a c κ q m) =
      C κ * ∑ nu ∈ partitionsOf r k, C (blockCoeff q m (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [blockOut, map_sum, Finset.mul_sum]
  have hterm : ∀ lam ∈ partitionsOf r (q + m),
      toN (r + a) (blockCoeff q m lam • pushOut r a c κ lam) =
        if ∀ i, a ≤ lam i then C κ * (C (blockCoeff q m lam) *
          aeval (fun i : Fin (r + a) => C c.sign * X i)
            (schur (Fin (r + a)) (fun i => lam i - a))) else 0 := by
    intro lam _
    rw [map_smul, pushOut]
    split_ifs
    · rw [map_mul, toN_xSign, smul_eq_C_mul]
      simp only [toN, aeval_C, algebraMap_eq]
      ring
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun nu i => a + nu i) (fun lam i => lam i - a) ?_ ?_ ?_ ?_ ?_
  · intro nu hnu
    rw [mem_partitionsOf_iff] at hnu
    rw [Finset.mem_filter, mem_partitionsOf_iff]
    refine ⟨⟨?_, fun i j hij => Nat.add_le_add_left (hnu.2 hij) a⟩, fun i => Nat.le_add_right a _⟩
    rw [Finset.sum_add_distrib, hnu.1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  · intro lam hlam
    rw [Finset.mem_filter, mem_partitionsOf_iff] at hlam
    rw [mem_partitionsOf_iff]
    refine ⟨?_, fun i j hij => Nat.sub_le_sub_right (hlam.1.2 hij) a⟩
    have h1 : ∑ i, (lam i - a) + ∑ i : Fin r, a = ∑ i, lam i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlam.2 i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    omega
  · intro nu _
    funext i
    simp
  · intro lam hlam
    rw [Finset.mem_filter] at hlam
    funext i
    exact Nat.add_sub_cancel' (hlam.2 i)
  · intro nu _
    simp

theorem blockOut_rect (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ) (h : q + m = r * a) :
    blockOut r a c κ q m = C (blockCoeff q m (rectangle r a) * κ) := by
  rw [blockOut, Finset.sum_eq_single (rectangle r a)]
  · have h0 : (fun i : Fin r => rectangle r a i - a) = 0 := funext fun i => by simp [rectangle]
    rw [pushOut, if_pos (fun i => by simp [rectangle]), h0, schur_zero, map_one, mul_one, smul_eq_C_mul,
      ← C_mul, mul_comm]
  · intro lam hlam hne
    rw [pushOut, if_neg, smul_zero]
    intro hall
    apply hne
    rw [mem_partitionsOf_iff] at hlam
    have h1 : ∑ i, (lam i - a) + ∑ i : Fin r, a = ∑ i, lam i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hall i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 : ∑ i, (lam i - a) = 0 := by omega
    funext i
    have := Finset.sum_eq_zero_iff.mp h2 i (Finset.mem_univ i)
    have := hall i
    simp only [rectangle]
    omega
  · intro h'
    exact absurd ((rectangle_mem_partitionsOf r a _).mpr h) h'

theorem gmfOut_zero (f r a : ℕ) (c : SmallBlock) (κ : ℚ) :
    gmfOut f r a c κ 0 (f * (r * a)) =
      C ((Nat.multinomial Finset.univ (fun _ : Fin f => r * a) : ℚ) *
        (blockCoeff 0 (r * a) (rectangle r a) * κ) ^ f) := by
  rw [gmfOut, Finset.sum_eq_single (fun _ : Fin f => r * a)]
  · simp only [Pi.zero_apply]
    rw [Finset.prod_congr rfl fun σ _ => by rw [blockOut_rect r a c κ 0 (r * a) (by simp)]]
    simp only [blockEmb, rename_C, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [smul_eq_C_mul, ← C_pow, ← C_mul]
  · intro m hm hne
    obtain ⟨σ, hσ⟩ : ∃ σ, m σ < r * a := by
      by_contra hcon
      push Not at hcon
      apply hne
      rw [Finset.mem_piAntidiag] at hm
      have hle : ∀ σ ∈ (Finset.univ : Finset (Fin f)), (fun _ => r * a) σ ≤ m σ :=
        fun σ _ => hcon σ
      have hsum : ∑ σ : Fin f, (fun _ => r * a) σ = ∑ σ, m σ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        rw [hm.1]
      funext σ
      exact ((Finset.sum_eq_sum_iff_of_le hle).mp hsum σ (Finset.mem_univ σ)).symm
    rw [Finset.prod_eq_zero (Finset.mem_univ σ), smul_zero]
    rw [Pi.zero_apply, blockOut_eq_zero_of_lt r a c κ 0 (m σ) (by omega), map_zero]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    refine ⟨by simp, fun i _ => Finset.mem_univ i⟩

end

end Top

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.InhabitantsElem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem flagIntegral_C_mul (f N : ℕ) (b : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C b * Φ) = b * flagIntegral f N Φ := by
  simp only [flagIntegral, coeff_C_mul, Finset.mul_sum, mul_assoc]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPrimeBoundOfFactor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

theorem RestPrimeBoundOfFactor.proof (h₁ : RestInnerTsumBound.Statement)
    (h₂ : RestKSumBound.Statement) : RestPrimeBoundOfFactor.Statement := by
  intro f r a c B₀ hf hr ha hB Q hT s e he p hp hpB
  set Y : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hY
  set X : ℝ := (restX r a : ℝ) with hX
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hX0 : 0 ≤ X := by rw [hX]; unfold restX; positivity
  have hN : 2 ≤ r + a := by omega
  have hXp : X ≤ 3 / 8 * (p : ℝ) := by
    have := XOverPrime.intersectionNumber_baseChange f r a B₀ p hf hN hB hpB
    rw [div_le_iff₀ hp0] at this
    linarith
  have hY0 : 0 ≤ Y := by positivity

  have hterm : ∀ τ : Fin f, ∀ k ∈ Finset.Icc 2 (r + a),
      |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
        ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
          (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)| ≤
        (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹) := by
    intro τ k hk
    rw [Finset.mem_Icc] at hk
    refine (h₁ (p : ℝ) k _ _ hp2 (by omega) ?_).2
    intro n
    have hb := hT k hk.1 hk.2 τ (s p (n + 1) τ)
    have habs : |e p (n + 1) τ k * restTerm f (r + a) Q k τ
        (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| =
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| := by
      rw [abs_mul]
      rcases he p (n + 1) τ k with h | h <;> simp [h]
    rw [← Rat.cast_abs, habs]
    calc ((|restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| : ℚ) : ℝ)
        ≤ ((((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ) : ℚ) : ℝ) := Rat.cast_le.mpr hb
      _ = Y * X ^ (k - 1) / (k.factorial : ℝ) := by
        rw [hY, hX]; push_cast; ring
  have hsumk := h₂ (p : ℝ) X (r + a) hp0 hX0 hXp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  unfold restPrimeModel
  rw [abs_mul, abs_of_nonneg hlog]
  calc Real.log p * |∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a), ∑' n : ℕ,
        ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
          ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
            (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)|
      ≤ Real.log p * ∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a),
          (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hlog
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact hterm τ k hk
    _ = Real.log p * ((f : ℝ) * (Y * ∑ k ∈ Finset.Icc 2 (r + a),
          2 * ((p : ℝ) ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ Real.log p * ((f : ℝ) * (Y * (1.5 * X / (p : ℝ) ^ 2))) := by
        gcongr
    _ = 1.5 * (f : ℝ) * X * (Real.log p / (p : ℝ) ^ 2) * Y := by ring
    _ = 1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by
        rw [hY, hX]; ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end
