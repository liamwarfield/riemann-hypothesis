module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnDegrees
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivationProdPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbLEqEmbOptL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthAddLeOfDisjoint
open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm

theorem exists_length_of_antitone {α : ℕ → ℕ} (hα : Antitone α) {m : ℕ}
    (hm : ∀ i, m ≤ i → α i = 0) : ∃ t, t ≤ m ∧ ∀ i, α i = 0 ↔ t ≤ i := by
  classical
  have h : ∃ i, α i = 0 := ⟨m, hm m le_rfl⟩
  refine ⟨Nat.find h, Nat.find_min' h (hm m le_rfl), fun i => ⟨fun hi => Nat.find_min' h hi,
    fun hi => ?_⟩⟩
  have := hα hi
  rw [Nat.find_spec h] at this
  exact Nat.le_zero.1 this

theorem length_add_le_of_disjoint {α β : ℕ → ℕ} {t u n : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i)
    (hu : ∀ i, β i = 0 ↔ u ≤ i) (htn : t ≤ n) (hun : u ≤ n)
    (h : ∀ i : Fin n, α i = 0 ∨ β i.rev = 0) : t + u ≤ n := by
  by_contra hc
  have h1 := h ⟨t - 1, by omega⟩
  rw [ht, hu, Fin.val_rev] at h1
  simp only at h1
  omega

def posList (α : ℕ → ℕ) (t : ℕ) : List ℤ := (List.range t).map fun i => (α i : ℤ)

def negList (β : ℕ → ℕ) (t : ℕ) : List ℤ := ((List.range t).map fun i => -(β i : ℤ)).reverse

@[simp] theorem length_posList (α : ℕ → ℕ) (t : ℕ) : (posList α t).length = t := by
  simp [posList]

@[simp] theorem length_negList (β : ℕ → ℕ) (t : ℕ) : (negList β t).length = t := by
  simp [negList]

theorem posList_pos {α : ℕ → ℕ} {t : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i) :
    ∀ v ∈ posList α t, 0 < v := by
  intro v hv
  simp only [posList, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have := ht i
  omega

theorem negList_neg {β : ℕ → ℕ} {t : ℕ} (ht : ∀ i, β i = 0 ↔ t ≤ i) :
    ∀ v ∈ negList β t, v < 0 := by
  intro v hv
  simp only [negList, List.mem_reverse, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have := ht i
  omega

theorem posList_pairwise {α : ℕ → ℕ} (hα : Antitone α) (t : ℕ) :
    (posList α t).Pairwise (· ≥ ·) := by
  rw [posList, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} h => ?_
  have := hα h.le
  omega

theorem negList_pairwise {β : ℕ → ℕ} (hβ : Antitone β) (t : ℕ) :
    (negList β t).Pairwise (· ≥ ·) := by
  rw [negList, List.pairwise_reverse, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} h => ?_
  have := hβ h.le
  omega

theorem getD_pad_posList_negList {α β : ℕ → ℕ} {t u n : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i)
    (hu : ∀ i, β i = 0 ↔ u ≤ i) (hn : t + u ≤ n) (i : Fin n) :
    (pad (posList α t) (n - (posList α t).length - (negList β u).length) (negList β u)).getD i 0
      = (α i : ℚ) - β i.rev := by
  obtain ⟨i, hi⟩ := i
  simp only [length_posList, length_negList, Fin.val_rev]
  have hlen : i < (pad (posList α t) (n - t - u) (negList β u)).length := by
    simp [pad]; omega
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [pad, List.getElem_map, List.getElem_append, List.length_append, length_posList,
    List.length_replicate, List.getElem_replicate]
  split_ifs with h1 h2
  · rw [(hu _).2 (by omega)]
    simp [posList]
  · rw [(hu _).2 (by omega), (ht _).2 (by omega)]
    simp
  · rw [(ht _).2 (by omega)]
    simp only [negList, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range]
    have : u - 1 - (i - (t + (n - t - u))) = n - (i + 1) := by omega
    rw [this]
    simp

theorem jointShape_of_fnShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
    (h : FnShape p q r s μ μ') : JointShape p q r s μ μ' := by
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, zα, zβ, zγ, zδ, d1, d2, d3, d4, e1, e2, e3, e4⟩ := h
  obtain ⟨a, ha, ta⟩ := exists_length_of_antitone hα zα
  obtain ⟨b, hb, tb⟩ := exists_length_of_antitone hβ zβ
  obtain ⟨c, hc, tc⟩ := exists_length_of_antitone hγ zγ
  obtain ⟨d, hd, td⟩ := exists_length_of_antitone hδ zδ
  rw [le_min_iff] at ha hb hc hd
  have l1 := length_add_le_of_disjoint ta tb ha.1 hb.1 d1
  have l2 := length_add_le_of_disjoint tc td hc.1 hd.1 d2
  have l3 := length_add_le_of_disjoint ta td ha.2 hd.2 d3
  have l4 := length_add_le_of_disjoint tc tb hc.2 hb.2 d4
  refine ⟨posList α a, negList β b, posList γ c, negList δ d, posList_pos ta, posList_pos tc,
    negList_neg tb, negList_neg td, posList_pairwise hα a, negList_pairwise hβ b,
    posList_pairwise hγ c, negList_pairwise hδ d, by simpa using l1, by simpa using l2,
    by simpa using l3, by simpa using l4, ?_, ?_⟩
  · funext x
    rcases x with i | i
    · exact (e1 i).trans (getD_pad_posList_negList ta tb l1 i).symm
    · exact (e2 i).trans (getD_pad_posList_negList tc td l2 i).symm
  · funext x
    rcases x with i | i
    · exact (e3 i).trans (getD_pad_posList_negList ta td l3 i).symm
    · exact (e4 i).trans (getD_pad_posList_negList tc tb l4 i).symm

end GlobalTheory.JointHarm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowColWeightsAgree
noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.BlockWeights

def extZero {p : ℕ} (a : Fin p → ℕ) (i : ℕ) : ℕ := if h : i < p then a ⟨i, h⟩ else 0

theorem sum_range_extZero {p : ℕ} (a : Fin p → ℕ) (i : ℕ) :
    ∑ j ∈ Finset.range i, extZero a j =
      ∑ b ∈ Finset.univ.filter (fun b : Fin p => (b : ℕ) < i), a b := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : n < p
    · have hset : Finset.univ.filter (fun b : Fin p => (b : ℕ) < n + 1) =
          insert ⟨n, h⟩ (Finset.univ.filter (fun b : Fin p => (b : ℕ) < n)) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hset, Finset.sum_insert (by simp), add_comm]
      simp only [extZero, dif_pos h]
    · have hset : Finset.univ.filter (fun b : Fin p => (b : ℕ) < n + 1) =
          Finset.univ.filter (fun b : Fin p => (b : ℕ) < n) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hset]
      simp only [extZero, dif_neg h, add_zero]

theorem partial_sum_le {σ : Type} [DecidableEq σ] {p r : ℕ} (z : Fin p × Fin r → σ)
    (hz : Function.Injective z) (P : MvPolynomial σ ℂ) (a : Fin p → ℕ) (a' : Fin r → ℕ)
    (hP : P ≠ 0) (hrow : ∀ i j : Fin p, i < j → rowOp ℂ z i j P = 0)
    (ha : ∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) (ha' : ∀ i, colOp ℂ z i i P = (a' i : ℂ) • P)
    (i : ℕ) :
    ∑ j ∈ Finset.range i, extZero a' j ≤ ∑ j ∈ Finset.range i, extZero a j := by

  have hinv : ∀ b c : Fin p, b < c → ∀ t : ℂ,
      bind₁ (fun s => X s + ∑ k, if s = z (c, k) then C t * X (z (b, k)) else 0) P = P := by
    intro b c hbc t
    have hw : Function.Injective (fun k : Fin r => z (c, k)) :=
      fun k l h => congrArg Prod.snd (hz h)
    have huw : ∀ k l : Fin r, z (b, k) ≠ z (c, l) := by
      intro k l h
      exact (ne_of_lt hbc) (congrArg Prod.fst (hz h))
    have hT := GlobalTheory.rowAdd_invariant_iff (K := ℂ) (fun k : Fin r => z (b, k))
      (fun k : Fin r => z (c, k)) hw huw P
    have h0 : ∑ k, X (z (b, k)) * pderiv (z (c, k)) P = 0 := by
      rw [← GlobalTheory.Capelli.rowOp_apply]
      exact hrow b c hbc
    have h23 := hT.out 2 3
    exact h23.mpr h0 t

  have hrowdeg : ∀ b, ∀ m ∈ P.support, ∑ k, m (z (b, k)) = a b := by
    intro b m hm
    exact_mod_cast (GlobalTheory.JointHarm.rowOp_eq_smul_iff z b P _).mp (ha b) m hm
  have hcoldeg : ∀ k, ∀ m ∈ P.support, ∑ b, m (z (b, k)) = a' k := by
    intro k m hm
    exact_mod_cast (GlobalTheory.JointHarm.colOp_eq_smul_iff z k P _).mp (ha' k) m hm
  obtain ⟨m, hm⟩ : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hP
  have key := GlobalTheory.column_degree_le z hz P a hrowdeg hinv
    (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)) m hm
  have hcard : (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card ≤ i := by
    calc (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card
        = ((Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).map Fin.valEmbedding).card :=
          (Finset.card_map _).symm
      _ ≤ (Finset.range i).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.valEmbedding_apply] at hx
          obtain ⟨k, hk, hkx⟩ := hx
          rw [Finset.mem_range, ← hkx]
          exact hk
      _ = i := Finset.card_range i
  rw [sum_range_extZero, sum_range_extZero]
  calc ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), a' k
      = ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), ∑ b, m (z (b, k)) :=
        Finset.sum_congr rfl (fun k _ => (hcoldeg k m hm).symm)
    _ = ∑ b, ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), m (z (b, k)) :=
        Finset.sum_comm
    _ ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin p =>
          (b : ℕ) < (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card), a b := key
    _ ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin p => (b : ℕ) < i), a b := by
        apply Finset.sum_le_sum_of_subset
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        omega

theorem row_col_weights_agree : ∀ (σ : Type) [DecidableEq σ] (p r : ℕ) (z : Fin p × Fin r → σ), Function.Injective z → ∀ (P : MvPolynomial σ ℂ) (a : Fin p → ℕ) (a' : Fin r → ℕ), P ≠ 0 → Antitone a → (∀ i j : Fin p, i < j → rowOp ℂ z i j P = 0) → (∀ i j : Fin r, i < j → colOp ℂ z i j P = 0) → (∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) → (∀ i, colOp ℂ z i i P = (a' i : ℂ) • P) → ∃ α : ℕ → ℕ, Antitone α ∧ (∀ i, min p r ≤ i → α i = 0) ∧ (∀ i : Fin p, a i = α i) ∧ ∀ i : Fin r, a' i = α i := by
  intro σ _ p r z hz P a a' hP hanti hrow hcol ha ha'
  have h1 : ∀ i, ∑ j ∈ Finset.range i, extZero a' j ≤ ∑ j ∈ Finset.range i, extZero a j :=
    partial_sum_le z hz P a a' hP hrow ha ha'

  have h2 : ∀ i, ∑ j ∈ Finset.range i, extZero a j ≤ ∑ j ∈ Finset.range i, extZero a' j := by
    have hz' : Function.Injective (fun w : Fin r × Fin p => z w.swap) :=
      hz.comp Prod.swap_injective
    have e : ∀ k l : Fin r,
        rowOp ℂ (fun w : Fin r × Fin p => z w.swap) k l = colOp ℂ z k l :=
      fun k l => GlobalTheory.Capelli.rowOp_eq_colOp _ k l
    have e' : ∀ b c : Fin p,
        colOp ℂ (fun w : Fin r × Fin p => z w.swap) b c = rowOp ℂ z b c :=
      fun b c => (GlobalTheory.Capelli.rowOp_eq_colOp z b c).symm
    exact partial_sum_le (fun w : Fin r × Fin p => z w.swap) hz' P a' a hP
      (fun k l hkl => by rw [e]; exact hcol k l hkl) (fun k => by rw [e]; exact ha' k)
      (fun b => by rw [e']; exact ha b)
  have hsum : ∀ i, ∑ j ∈ Finset.range i, extZero a j = ∑ j ∈ Finset.range i, extZero a' j :=
    fun i => le_antisymm (h2 i) (h1 i)

  have heq : ∀ j, extZero a j = extZero a' j := by
    intro j
    have hj := hsum (j + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hsum j] at hj
    omega
  refine ⟨extZero a, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    unfold extZero
    by_cases hj : j < p
    · rw [dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
      exact hanti (Fin.mk_le_mk.mpr hij)
    · rw [dif_neg hj]
      exact Nat.zero_le _
  · intro i hi
    by_cases hp : p ≤ i
    · simp [extZero, show ¬ i < p by omega]
    · rw [heq i]
      simp [extZero, show ¬ i < r by omega]
  · intro i
    simp [extZero]
  · intro i
    rw [heq]
    simp [extZero]

end GlobalTheory.JointHarm.BlockWeights
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FnShapeOfJointShape
open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.ListShape

def posFn (x : List ℤ) (i : ℕ) : ℕ := (x.getD i 0).toNat

def negFn (y : List ℤ) (i : ℕ) : ℕ := posFn (y.reverse.map fun v => -v) i

theorem posFn_eq_zero {x : List ℤ} {i : ℕ} (h : x.length ≤ i) : posFn x i = 0 := by
  unfold posFn
  rw [List.getD_eq_default _ _ h]
  simp

theorem negFn_eq_zero {y : List ℤ} {i : ℕ} (h : y.length ≤ i) : negFn y i = 0 := by
  unfold negFn
  exact posFn_eq_zero (by simpa using h)

theorem posFn_antitone {x : List ℤ} (h : x.Pairwise (· ≥ ·)) : Antitone (posFn x) := by
  intro i j hij
  by_cases hj : j < x.length
  · have hi : i < x.length := lt_of_le_of_lt hij hj
    simp only [posFn, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    apply Int.toNat_le_toNat
    rcases hij.lt_or_eq with hlt | heq
    · exact List.pairwise_iff_getElem.mp h i j hi hj hlt
    · subst heq
      exact le_rfl
  · rw [posFn_eq_zero (not_lt.mp hj)]
    exact Nat.zero_le _

theorem negFn_antitone {y : List ℤ} (h : y.Pairwise (· ≥ ·)) : Antitone (negFn y) := by
  show Antitone (posFn (y.reverse.map fun v => -v))
  apply posFn_antitone
  rw [List.pairwise_map, List.pairwise_reverse]
  exact h.imp fun hab => neg_le_neg hab

theorem posFn_cast {x : List ℤ} (hx : ∀ v ∈ x, 0 < v) {i : ℕ} (hi : i < x.length) :
    (posFn x i : ℚ) = (x[i] : ℤ) := by
  have hp : 0 < x[i] := hx _ (List.getElem_mem hi)
  simp only [posFn, List.getD_eq_getElem _ _ hi]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hp.le]

theorem negFn_cast {y : List ℤ} (hy : ∀ v ∈ y, v < 0) {i : ℕ} (hi : i < y.length) :
    (negFn y i : ℚ) = -((y[y.length - 1 - i] : ℤ) : ℚ) := by
  have hl : i < (y.reverse.map fun v => -v).length := by simpa using hi
  have hk : y.length - 1 - i < y.length := by omega
  have hv : y[y.length - 1 - i] < 0 := hy _ (List.getElem_mem hk)
  simp only [negFn, posFn, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_reverse]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]

theorem disj {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) (i : Fin n) :
    posFn x i = 0 ∨ negFn y i.rev = 0 := by
  have hn := i.isLt
  by_cases hi : x.length ≤ (i : ℕ)
  · exact Or.inl (posFn_eq_zero hi)
  · right
    apply negFn_eq_zero
    rw [Fin.val_rev]
    omega

private lemma getD_map_intCast (l : List ℤ) (i : ℕ) :
    (l.map (fun v : ℤ => (v : ℚ))).getD i 0 = ((l.getD i 0 : ℤ) : ℚ) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem pad_getD {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) {n : ℕ}
    (h : x.length + y.length ≤ n) (i : Fin n) :
    (pad x (n - x.length - y.length) y).getD i 0 = (posFn x i : ℚ) - negFn y i.rev := by
  have hn := i.isLt
  unfold pad
  rw [getD_map_intCast, List.append_assoc, Fin.val_rev]
  by_cases h1 : (i : ℕ) < x.length
  · rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, posFn_cast hx h1,
      negFn_eq_zero (by omega)]
    simp
  · rw [List.getD_append_right _ _ _ _ (not_lt.mp h1), posFn_eq_zero (not_lt.mp h1)]
    by_cases h2 : (i : ℕ) - x.length < n - x.length - y.length
    · rw [List.getD_append _ _ _ _ (by simpa using h2), negFn_eq_zero (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, h2]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_replicate]
      have hj : n - ((i : ℕ) + 1) < y.length := by omega
      rw [negFn_cast hy hj]
      have e : (i : ℕ) - x.length - (n - x.length - y.length) = y.length - 1 - (n - ((i : ℕ) + 1)) := by
        omega
      rw [e, List.getD_eq_getElem _ _ (by omega)]
      simp

end GlobalTheory.JointHarm.ListShape

namespace GlobalTheory.JointHarm


open ListShape in
theorem fnShape_of_jointShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
    (h : JointShape p q r s μ μ') : FnShape p q r s μ μ' := by
  obtain ⟨a, b, c, d, ha, hc, hb, hd, ha', hb', hc', hd', hab, hcd, had, hcb, hμ, hμ'⟩ := h
  refine ⟨posFn a, negFn b, posFn c, negFn d, posFn_antitone ha', negFn_antitone hb',
    posFn_antitone hc', negFn_antitone hd', fun i hi => posFn_eq_zero (by omega),
    fun i hi => negFn_eq_zero (by omega), fun i hi => posFn_eq_zero (by omega),
    fun i hi => negFn_eq_zero (by omega), disj hab, disj hcd, disj had, disj hcb,
    fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hμ]
    exact pad_getD ha hb hab i
  · rw [hμ]
    exact pad_getD hc hd hcd i
  · rw [hμ']
    exact pad_getD ha hd had i
  · rw [hμ']
    exact pad_getD hc hb hcb i

end GlobalTheory.JointHarm
end

noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.JointHarm

theorem exists_sep {σ : Type} [Fintype σ] {k l n : ℕ} {z : Fin k × Fin n → σ}
    {y : Fin l × Fin n → σ} (hz : Function.Injective z) (hy : Function.Injective y)
    (hzy : ∀ u w, z u ≠ y w) {P : MvPolynomial σ ℂ} {ν : Fin n → ℚ} (hP : P ≠ 0)
    (hh : P ∈ harmSub z y) (hup : ∀ i j, i < j → mixedOp ℂ z y i j P = 0)
    (hwt : ∀ t, mixedOp ℂ z y t t P = (ν t : ℂ) • P) :
    ∃ A B : Fin n → ℕ, Antitone A ∧ Monotone B ∧ (∀ t, A t = 0 ∨ B t = 0) ∧
      (∀ t, ν t = (A t : ℚ) - B t) ∧ Sep z y A B P := by
  classical
  obtain ⟨m₀, hm₀⟩ := support_nonempty.2 hP
  let κ : Fin n → ℤ := fun t => ((∑ i, m₀ (z (i, t)) : ℕ) : ℤ) - (∑ j, m₀ (y (j, t)) : ℕ)
  have hκ : ∀ t, ν t = κ t := fun t => by
    rw [mixed_weight z y (hwt t) hm₀]; simp [κ]
  obtain ⟨ha, hdeg⟩ := ColumnDegree.column_degrees σ k l n z y hz hy hzy P κ hP hh hup
    fun t => by rw [hwt, hκ, Rat.cast_intCast]
  refine ⟨fun t => (κ t).toNat, fun t => (-κ t).toNat, fun i j h => Int.toNat_le_toNat (ha h),
    fun i j h => Int.toNat_le_toNat (neg_le_neg (ha h)), fun t => by dsimp only; omega, fun t => ?_,
    sep_of_degrees hz hzy (fun m hm t => ?_) (fun m hm t => ?_) hup⟩
  · rw [hκ]
    exact_mod_cast (Int.toNat_sub_toNat_neg (κ t)).symm
  · have := (hdeg m hm t).1
    rw [← Nat.cast_sum] at this
    omega
  · have := (hdeg m hm t).2
    rw [← Nat.cast_sum] at this
    omega

theorem mixedOp_homog {σ : Type} {k l n : ℕ} (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ)
    (a b : Fin n) {d : ℕ} {P : MvPolynomial σ ℂ} (hP : P ∈ homog σ d) :
    mixedOp ℂ z y a b P ∈ homog σ d := by
  have h : ∀ u v : σ, X u * pderiv v P ∈ homog σ d := by
    intro u v
    rcases d with _ | d
    · rw [totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hP), pderiv_C,
        mul_zero]
      exact Submodule.zero_mem _
    · have := (isHomogeneous_X ℂ u).mul (IsHomogeneous.pderiv (i := v) hP)
      rwa [Nat.add_sub_cancel, add_comm] at this
  rw [mixedOp_apply]
  exact Submodule.sub_mem _ (Submodule.sum_mem _ fun _ _ => h _ _)
    (Submodule.sum_mem _ fun _ _ => h _ _)

section Side

variable {σ : Type} [Fintype σ] {p q r s : ℕ} {e : Ln p q r s → σ}
  {act : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}

theorem IsSide.exists_sep (he : Function.Injective e) (h : IsSide e act) {μ : Ix p q → ℚ}
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) (hw : P ∈ hwSub act μ)
    (hh : P ∈ harmSub (zA e) (zB e) ⊓ harmSub (zC e) (zD e)) :
    (∃ A B : Fin p → ℕ, Antitone A ∧ Monotone B ∧ (∀ t, A t = 0 ∨ B t = 0) ∧
      (∀ t, shiftNu (cPair r s) μ (.inl t) = (A t : ℚ) - B t) ∧ Sep (zA e) (zB e) A B P) ∧
    ∃ A B : Fin q → ℕ, Antitone A ∧ Monotone B ∧ (∀ t, A t = 0 ∨ B t = 0) ∧
      (∀ t, shiftNu (cPair r s) μ (.inr t) = (A t : ℚ) - B t) ∧ Sep (zC e) (zD e) A B P := by
  obtain ⟨h1, h2, h3⟩ := (h.mem_hwSub μ P).1 hw
  obtain ⟨h4, h5⟩ := (h.mem_wtSub μ P).1 h1
  exact ⟨GlobalTheory.JointHarm.exists_sep (zA_inj he) (zB_inj he) (zAB he) hP hh.1 h2 h4,
    GlobalTheory.JointHarm.exists_sep (zC_inj he) (zD_inj he) (zCD he) hP hh.2 h3 h5⟩

omit [Fintype σ] in
theorem IsSide.of_sep (h : IsSide e act) {μ : Ix p q → ℚ} {P : MvPolynomial σ ℂ}
    {A B : Fin p → ℕ} {C D : Fin q → ℕ} (hAB : ∀ t, A t = 0 ∨ B t = 0)
    (hCD : ∀ t, C t = 0 ∨ D t = 0)
    (h1 : ∀ t, shiftNu (cPair r s) μ (.inl t) = (A t : ℚ) - B t)
    (h2 : ∀ t, shiftNu (cPair r s) μ (.inr t) = (C t : ℚ) - D t)
    (s1 : Sep (zA e) (zB e) A B P) (s2 : Sep (zC e) (zD e) C D P) :
    P ∈ hwSub act μ ∧ P ∈ harmSub (zA e) (zB e) ⊓ harmSub (zC e) (zD e) := by
  obtain ⟨a1, a2, a3⟩ := s1.mixed hAB
  obtain ⟨b1, b2, b3⟩ := s2.mixed hCD
  refine ⟨(h.mem_hwSub μ P).2 ⟨(h.mem_wtSub μ P).2 ⟨fun t => ?_, fun t => ?_⟩, a2, b2⟩, a1, b1⟩
  · rw [a3, h1]; push_cast; rfl
  · rw [b3, h2]; push_cast; rfl

theorem abs_sub_of_disjoint {a b : ℕ} (h : a = 0 ∨ b = 0) : |(a : ℚ) - b| = (a + b : ℕ) := by
  rcases h with rfl | rfl <;> simp

theorem IsSide.homog_of_hw (he : Function.Bijective e) (h : IsSide e act) {μ : Ix p q → ℚ}
    {P : MvPolynomial σ ℂ} (hw : IsHW act μ P)
    (hh : P ∈ harmSub (zA e) (zB e) ⊓ harmSub (zC e) (zD e)) :
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog σ d := by
  obtain ⟨⟨A, B, -, -, h1, h2, h3⟩, C, D, -, -, h4, h5, h6⟩ := h.exists_sep he.1 hw.1 hw.2 hh
  refine ⟨∑ t, (A t + B t) + ∑ t, (C t + D t), ?_, fun m hm => ?_⟩
  · rw [degW, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_sum, Nat.cast_sum]
    simp only [h2, h5, abs_sub_of_disjoint (h1 _), abs_sub_of_disjoint (h4 _)]
  · have hm' := mem_support_iff.2 hm
    have g : ∀ {k n : ℕ} {z : Fin k × Fin n → σ} {t : Fin n} {c : ℕ},
        colOp ℂ z t t P = (c : ℂ) • P → ∑ i, m (z (i, t)) = c := fun hz =>
      Nat.cast_injective ((colOp_eq_smul_iff _ _ _ _).1 hz m hm')
    refine (DFunLike.congr_fun Finsupp.degree_eq_weight_one m).symm.trans ?_
    rw [degree_eq_blocks he]
    simp only [g (h3.1 _), g (h3.2.1 _), g (h6.1 _), g (h6.2.1 _)]

omit [Fintype σ] in
theorem IsSide.exists_hw (he : Function.Injective e) (h : IsSide e act)
    (W : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ W]
    (h1 : ∀ a b, ∀ w ∈ W, mixedOp ℂ (zA e) (zB e) a b w ∈ W)
    (h2 : ∀ a b, ∀ w ∈ W, mixedOp ℂ (zC e) (zD e) a b w ∈ W) (h0 : W ≠ ⊥) :
    ∃ ν, ∃ v ∈ W, IsHW act ν v := by
  obtain ⟨v, hv, hv0, u1, u2, κ, κ', w1, w2⟩ := exists_highest_pair _ _
    (mixedOp_lie _ (zA_inj he) _ (zB_inj he) (zAB he))
    (mixedOp_lie _ (zC_inj he) _ (zD_inj he) (zCD he))
    (commute_mixedOp_mixedOp _ _ _ _ (zAC he) (zAD he) (zBC he) (zBD he))
    (mixed_diag _ _) (mixed_diag _ _) W h1 h2 h0
  refine ⟨Sum.elim (fun i => κ i + cPair r s) (fun i => κ' i - cPair r s), v, hv, hv0,
    (h.mem_hwSub _ _).2 ⟨(h.mem_wtSub _ _).2 ⟨fun a => ?_, fun a => ?_⟩, u1, u2⟩⟩
  · simp [shiftNu, w1]
  · simp [shiftNu, w2]

theorem IsSide.homog_of_type [DecidableEq σ] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι)
    (hinj : Function.Injective ι) (he : Function.Bijective e) (h : IsSide e act) {μ : Ix p q → ℚ}
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) (ht : OfType act μ P)
    (hh : P ∈ harmSub (zA e) (zB e) ⊓ harmSub (zC e) (zD e)) :
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog σ d := by
  obtain ⟨W, hfin, hPW, hst, hμ⟩ := ht
  have kc : ∀ a b : Ix p q, sameBlock a b → IsKC (Eab a b) := by
    intro a b hab c d hcd
    rw [Eab, Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd hab
  let W₁ := W ⊓ (harmSub (zA e) (zB e) ⊓ harmSub (zC e) (zD e))
  have : FiniteDimensional ℂ W₁ := Submodule.finiteDimensional_of_le inf_le_left
  have s1 : ∀ a b, ∀ w ∈ W₁, mixedOp ℂ (zA e) (zB e) a b w ∈ W₁ := fun a b w hw => by
    refine ⟨?_, harmSub_mixedOp (zA_inj he.1) (zB_inj he.1) (zAB he.1) a b hw.2.1,
      harmSub_mixedOp' (fun _ _ => (zAC he.1 _ _).symm) (fun _ _ => (zBC he.1 _ _).symm)
        (fun _ _ => (zAD he.1 _ _).symm) (fun _ _ => (zBD he.1 _ _).symm) a b hw.2.2⟩
    rw [← sub_eq_iff_eq_add.2 (h.1 a b w)]
    exact W.sub_mem (hst _ (kc (.inl a) (.inl b) trivial) w hw.1) (W.smul_mem _ hw.1)
  have s2 : ∀ a b, ∀ w ∈ W₁, mixedOp ℂ (zC e) (zD e) a b w ∈ W₁ := fun a b w hw => by
    refine ⟨?_, harmSub_mixedOp' (zAC he.1) (zAD he.1) (zBC he.1) (zBD he.1) a b hw.2.1,
      harmSub_mixedOp (zC_inj he.1) (zD_inj he.1) (zCD he.1) a b hw.2.2⟩
    rw [← eq_sub_iff_add_eq.1 (h.2 a b w)]
    exact W.add_mem (hst _ (kc (.inr a) (.inr b) trivial) w hw.1) (W.smul_mem _ hw.1)
  obtain ⟨ν, v, hv, hvw⟩ := h.exists_hw he.1 W₁ s1 s2
    fun h0 => hP ((Submodule.eq_bot_iff _).1 h0 P ⟨hPW, hh⟩)
  obtain rfl := hμ ν v hv.1 hvw
  obtain ⟨d, hd, -⟩ := h.homog_of_hw he hvw hv.2
  refine ⟨d, hd, ?_⟩
  let U := W₁ ⊓ homog σ d
  have : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le inf_le_left
  let K : Submodule ℂ (MvPolynomial σ ℂ) := W₁ ⊓ ((U.map ι)ᗮ).comap ι
  have : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  have mK : ∀ w, w ∈ K ↔ w ∈ W₁ ∧ ∀ u ∈ U, inner ℂ (ι u) (ι w) = 0 := fun w => by
    simp only [K, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_orthogonal]
    exact and_congr_right fun _ => ⟨fun h u hu => h _ (Submodule.mem_map_of_mem hu), by
      rintro h _ ⟨u, hu, rfl⟩; exact h u hu⟩
  have hK : K = ⊥ := by
    by_contra h0
    obtain ⟨ν', v', hv', hvw'⟩ := h.exists_hw he.1 K
      (fun a b w hw => (mK _).2 ⟨s1 a b w hw.1, fun u hu => by
        rw [← inner_mixedOp hι]
        exact ((mK _).1 hw).2 _ ⟨s1 b a u hu.1, mixedOp_homog _ _ _ _ hu.2⟩⟩)
      (fun a b w hw => (mK _).2 ⟨s2 a b w hw.1, fun u hu => by
        rw [← inner_mixedOp hι]
        exact ((mK _).1 hw).2 _ ⟨s2 b a u hu.1, mixedOp_homog _ _ _ _ hu.2⟩⟩) h0
    obtain rfl := hμ ν' v' hv'.1.1 hvw'
    obtain ⟨d', hd', hv''⟩ := h.homog_of_hw he hvw' hv'.1.2
    obtain rfl : d' = d := by exact_mod_cast hd'.trans hd.symm
    have := ((mK _).1 hv').2 v' ⟨hv'.1, hv''⟩
    rw [inner_self_eq_zero] at this
    exact hvw'.1 (hinj (this.trans (map_zero ι).symm))
  obtain ⟨u, hu, ho⟩ := exists_orth ι U P
  have : P - u ∈ K := (mK _).2 ⟨W₁.sub_mem ⟨hPW, hh⟩ hu.1, ho⟩
  rw [hK, Submodule.mem_bot, sub_eq_zero] at this
  exact this ▸ hu.2

end Side

section Joint

variable {p q r s : ℕ}

def rv {σ : Type} {m n : ℕ} (z : Fin m × Fin n → σ) : Fin m × Fin n → σ :=
  fun w => z (w.1.rev, w.2.rev)

theorem rv_inj {σ : Type} {m n : ℕ} {z : Fin m × Fin n → σ} (hz : Function.Injective z) :
    Function.Injective (rv z) := fun u w h => by
  simpa [Prod.ext_iff] using hz h

theorem colOp_rv {σ : Type} {m n : ℕ} (z : Fin m × Fin n → σ) (k l : Fin n) :
    colOp ℂ (rv z) k l = colOp ℂ z k.rev l.rev :=
  Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl

theorem rowOp_rv {σ : Type} {m n : ℕ} (z : Fin m × Fin n → σ) (k l : Fin m) :
    rowOp ℂ (rv z) k l = rowOp ℂ z k.rev l.rev :=
  Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl

theorem blockHW_rv_iff {σ : Type} {m n : ℕ} (z : Fin m × Fin n → σ) (β : ℕ → ℕ)
    (P : MvPolynomial σ ℂ) : BlockHW (rv z) β P ↔
      (∀ a b : Fin m, a < b → rowOp ℂ z b a P = 0) ∧ (∀ a b : Fin n, a < b → colOp ℂ z b a P = 0) ∧
      (∀ a : Fin m, rowOp ℂ z a a P = (β a.rev : ℂ) • P) ∧
        ∀ a : Fin n, colOp ℂ z a a P = (β a.rev : ℂ) • P := by
  simp only [BlockHW, colOp_rv, rowOp_rv]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun a b h => by simpa using h1 b.rev a.rev (Fin.rev_lt_rev.2 h),
      fun a b h => by simpa using h2 b.rev a.rev (Fin.rev_lt_rev.2 h),
      fun a => by simpa using h3 a.rev, fun a => by simpa using h4 a.rev⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun a b h => h1 _ _ (Fin.rev_lt_rev.2 h), fun a b h => h2 _ _ (Fin.rev_lt_rev.2 h),
      fun a => by rw [h3, Fin.rev_rev], fun a => by rw [h4, Fin.rev_rev]⟩

abbrev bA (p q r s : ℕ) : Fin r × Fin p → Ln p q r s := zA id

abbrev bB (p q r s : ℕ) : Fin s × Fin p → Ln p q r s := zB id

abbrev bC (p q r s : ℕ) : Fin s × Fin q → Ln p q r s := zC id

abbrev bD (p q r s : ℕ) : Fin r × Fin q → Ln p q r s := zD id

def jointHW (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Submodule ℂ (Pol p q r s) :=
  hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
    ((harmSub (zA Prod.swap) (zB Prod.swap) ⊓ harmSub (zC Prod.swap) (zD Prod.swap)) ⊓
      (harmSub (zA id) (zB id) ⊓ harmSub (zC id) (zD id)))

def ShapeData (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (α β γ δ : ℕ → ℕ) : Prop :=
  Antitone α ∧ Antitone β ∧ Antitone γ ∧ Antitone δ ∧
    (∀ i, min p r ≤ i → α i = 0) ∧ (∀ i, min p s ≤ i → β i = 0) ∧
    (∀ i, min q s ≤ i → γ i = 0) ∧ (∀ i, min q r ≤ i → δ i = 0) ∧
    (∀ i : Fin p, α i = 0 ∨ β i.rev = 0) ∧ (∀ i : Fin q, γ i = 0 ∨ δ i.rev = 0) ∧
    (∀ i : Fin r, α i = 0 ∨ δ i.rev = 0) ∧ (∀ i : Fin s, γ i = 0 ∨ β i.rev = 0) ∧
    (∀ i : Fin p, shiftNu (cPair r s) μ (.inl i) = (α i : ℚ) - β i.rev) ∧
    (∀ i : Fin q, shiftNu (cPair r s) μ (.inr i) = (γ i : ℚ) - δ i.rev) ∧
    (∀ i : Fin r, shiftNu (cPair p q) μ' (.inl i) = (α i : ℚ) - δ i.rev) ∧
    (∀ i : Fin s, shiftNu (cPair p q) μ' (.inr i) = (γ i : ℚ) - β i.rev)

def FourHW (α β γ δ : ℕ → ℕ) (P : Pol p q r s) : Prop :=
  BlockHW (bA p q r s) α P ∧ BlockHW (rv (bB p q r s)) β P ∧ BlockHW (bC p q r s) γ P ∧
    BlockHW (rv (bD p q r s)) δ P

theorem pair_unique {n : ℕ} {α β α' β' : ℕ → ℕ} (h1 : ∀ i, n ≤ i → α i = 0)
    (h2 : ∀ i, n ≤ i → β i = 0) (h1' : ∀ i, n ≤ i → α' i = 0) (h2' : ∀ i, n ≤ i → β' i = 0)
    (h : ∀ i : Fin n, α i = 0 ∨ β i.rev = 0) (h' : ∀ i : Fin n, α' i = 0 ∨ β' i.rev = 0)
    (e : ∀ i : Fin n, (α i : ℚ) - β i.rev = α' i - β' i.rev) : α = α' ∧ β = β' := by
  have key : ∀ i : Fin n, α i = α' i ∧ β i.rev = β' i.rev := fun i => by
    have h3 : (α i : ℤ) - β i.rev = α' i - β' i.rev := by exact_mod_cast e i
    have := h i
    have := h' i
    omega
  constructor <;> funext i <;> by_cases hi : i < n
  · exact (key ⟨i, hi⟩).1
  · rw [h1 i (by omega), h1' i (by omega)]
  · simpa only [Fin.rev_rev] using (key (Fin.rev ⟨i, hi⟩)).2
  · rw [h2 i (by omega), h2' i (by omega)]

theorem ShapeData.unique {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {α β γ δ α' β' γ' δ' : ℕ → ℕ}
    (h : ShapeData μ μ' α β γ δ) (h' : ShapeData μ μ' α' β' γ' δ') :
    α = α' ∧ β = β' ∧ γ = γ' ∧ δ = δ' := by
  obtain ⟨-, -, -, -, a1, a2, a3, a4, a5, a6, -, -, a7, a8, -, -⟩ := h
  obtain ⟨-, -, -, -, b1, b2, b3, b4, b5, b6, -, -, b7, b8, -, -⟩ := h'
  have m : ∀ {a b : ℕ} {f : ℕ → ℕ}, (∀ i, min a b ≤ i → f i = 0) → ∀ i, a ≤ i → f i = 0 :=
    fun h i hi => h i ((min_le_left _ _).trans hi)
  obtain ⟨e1, e2⟩ := pair_unique (m a1) (m a2) (m b1) (m b2) a5 b5 fun i => (a7 i).symm.trans (b7 i)
  obtain ⟨e3, e4⟩ := pair_unique (m a3) (m a4) (m b3) (m b4) a6 b6 fun i => (a8 i).symm.trans (b8 i)
  exact ⟨e1, e2, e3, e4⟩

theorem weights_rv {σ : Type} [DecidableEq σ] {m n : ℕ} {z : Fin m × Fin n → σ}
    (hz : Function.Injective z) {P : MvPolynomial σ ℂ} {a : Fin m → ℕ} {a' : Fin n → ℕ}
    (hP : P ≠ 0) (ha : Monotone a) (h1 : ∀ i j : Fin m, i < j → rowOp ℂ z j i P = 0)
    (h2 : ∀ i j : Fin n, i < j → colOp ℂ z j i P = 0) (h3 : ∀ i, rowOp ℂ z i i P = (a i : ℂ) • P)
    (h4 : ∀ i, colOp ℂ z i i P = (a' i : ℂ) • P) :
    ∃ β : ℕ → ℕ, Antitone β ∧ (∀ i, min m n ≤ i → β i = 0) ∧ (∀ i : Fin m, a i = β i.rev) ∧
      ∀ i : Fin n, a' i = β i.rev := by
  obtain ⟨β, b1, b2, b3, b4⟩ := BlockWeights.row_col_weights_agree σ m n (rv z) (rv_inj hz) P
    (fun i => a i.rev) (fun i => a' i.rev) hP (fun i j h => ha (Fin.rev_le_rev.2 h))
    (fun i j h => by rw [rowOp_rv]; exact h1 _ _ (Fin.rev_lt_rev.2 h))
    (fun i j h => by rw [colOp_rv]; exact h2 _ _ (Fin.rev_lt_rev.2 h))
    (fun i => by rw [rowOp_rv, h3]) (fun i => by rw [colOp_rv, h4])
  exact ⟨β, b1, b2, fun i => by simpa only [Fin.rev_rev] using b3 i.rev,
    fun i => by simpa only [Fin.rev_rev] using b4 i.rev⟩

theorem four_of_joint {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s} (hP : P ≠ 0)
    (h : P ∈ jointHW μ μ') : ∃ α β γ δ, ShapeData μ μ' α β γ δ ∧ FourHW α β γ δ P := by
  have hid : Function.Injective (id : Ln p q r s → Ln p q r s) := Function.injective_id
  obtain ⟨⟨A, B, -, -, hAB, eAB, sAB⟩, C, D, -, -, hCD, eCD, sCD⟩ :=
    isSide_one.exists_sep hid hP h.1.1 h.2.2
  obtain ⟨⟨A', D', mA, mD, hAD, eAD, sAD⟩, C', B', mC, mB, hCB, eCB, sCB⟩ :=
    isSide_two.exists_sep Prod.swap_injective hP h.1.2 h.2.1
  obtain ⟨α, a1, a2, a3, a4⟩ := BlockWeights.row_col_weights_agree _ r p (bA p q r s) (zA_inj hid)
    P A' A hP mA sAD.2.2.1 sAB.2.2.1 sAD.1 sAB.1
  obtain ⟨γ, c1, c2, c3, c4⟩ := BlockWeights.row_col_weights_agree _ s q (bC p q r s) (zC_inj hid)
    P C' C hP mC sCB.2.2.1 sCD.2.2.1 sCB.1 sCD.1
  obtain ⟨β, b1, b2, b3, b4⟩ := weights_rv (z := bB p q r s) (zB_inj hid) hP mB sCB.2.2.2 sAB.2.2.2
    sCB.2.1 sAB.2.1
  obtain ⟨δ, d1, d2, d3, d4⟩ := weights_rv (z := bD p q r s) (zD_inj hid) hP mD sAD.2.2.2 sCD.2.2.2
    sAD.2.1 sCD.2.1
  rw [min_comm] at a2 b2 c2 d2
  refine ⟨α, β, γ, δ, ⟨a1, b1, c1, d1, a2, b2, c2, d2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨sAD.2.2.1, sAB.2.2.1, fun i => a3 i ▸ sAD.1 i, fun i => a4 i ▸ sAB.1 i⟩,
    (blockHW_rv_iff _ _ _).2
      ⟨sCB.2.2.2, sAB.2.2.2, fun i => b3 i ▸ sCB.2.1 i, fun i => b4 i ▸ sAB.2.1 i⟩,
    ⟨sCB.2.2.1, sCD.2.2.1, fun i => c3 i ▸ sCB.1 i, fun i => c4 i ▸ sCD.1 i⟩,
    (blockHW_rv_iff _ _ _).2
      ⟨sAD.2.2.2, sCD.2.2.2, fun i => d3 i ▸ sAD.2.1 i, fun i => d4 i ▸ sCD.2.1 i⟩⟩ <;> intro i
  · rw [← a4, ← b4]; exact hAB i
  · rw [← c4, ← d4]; exact hCD i
  · rw [← a3, ← d3]; exact hAD i
  · rw [← c3, ← b3]; exact hCB i
  · rw [← a4, ← b4]; exact eAB i
  · rw [← c4, ← d4]; exact eCD i
  · rw [← a3, ← d3]; exact eAD i
  · rw [← c3, ← b3]; exact eCB i

theorem joint_of_four {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {α β γ δ : ℕ → ℕ} {P : Pol p q r s}
    (h : ShapeData μ μ' α β γ δ) (h4 : FourHW α β γ δ P) : P ∈ jointHW μ μ' := by
  obtain ⟨-, -, -, -, -, -, -, -, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  obtain ⟨A, B, C, D⟩ := h4
  rw [blockHW_rv_iff] at B D
  obtain ⟨u1, u2⟩ := isSide_one.of_sep a1 a2 a5 a6 ⟨A.2.2.2, B.2.2.2, A.2.1, B.2.1⟩
    ⟨C.2.2.2, D.2.2.2, C.2.1, D.2.1⟩
  obtain ⟨v1, v2⟩ := isSide_two.of_sep a3 a4 a7 a8 ⟨A.2.2.1, D.2.2.1, A.1, D.1⟩
    ⟨C.2.2.1, B.2.2.1, C.1, B.1⟩
  exact ⟨⟨u1, v1⟩, v2, u2⟩

theorem BlockHW.mul {σ : Type} {m n : ℕ} {z : Fin m × Fin n → σ} {α : ℕ → ℕ}
    {P Q : MvPolynomial σ ℂ} (h : BlockHW z α P) (hQ : ∀ w, pderiv (z w) Q = 0) :
    BlockHW z α (P * Q) := by
  have h1 : ∀ a b, rowOp ℂ z a b (P * Q) = rowOp ℂ z a b P * Q := fun a b => by
    simp only [rowOp_apply, Derivation.leibniz, hQ, smul_zero, zero_add, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∀ a b, colOp ℂ z a b (P * Q) = colOp ℂ z a b P * Q := fun a b => by
    simp only [colOp_apply, Derivation.leibniz, hQ, smul_zero, zero_add, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  exact ⟨fun a b hab => by rw [h1, h.1 a b hab, zero_mul],
    fun a b hab => by rw [h2, h.2.1 a b hab, zero_mul],
    fun a => by rw [h1, h.2.2.1, smul_mul_assoc], fun a => by rw [h2, h.2.2.2, smul_mul_assoc]⟩

theorem finrank_jointHW {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {α β γ δ : ℕ → ℕ}
    (h : ShapeData μ μ' α β γ δ) : Module.finrank ℂ (jointHW μ μ') = 1 := by
  have hid : Function.Injective (id : Ln p q r s → Ln p q r s) := Function.injective_id
  have ⟨a1, b1, c1, d1, a2, b2, c2, d2, _⟩ := h
  rw [min_comm] at a2 b2 c2 d2
  have iA := zA_inj hid
  have iB := rv_inj (zB_inj hid)
  have iC := zC_inj hid
  have iD := rv_inj (zD_inj hid)
  obtain ⟨nA, vA, hA⟩ := Minor.minorPoly_highest _ _ _ (bA p q r s) iA α a1 a2
  obtain ⟨nB, vB, hB⟩ := Minor.minorPoly_highest _ _ _ (rv (bB p q r s)) iB β b1 b2
  obtain ⟨nC, vC, hC⟩ := Minor.minorPoly_highest _ _ _ (bC p q r s) iC γ c1 c2
  obtain ⟨nD, vD, hD⟩ := Minor.minorPoly_highest _ _ _ (rv (bD p q r s)) iD δ d1 d2
  let B : Fin 4 → Set (Ln p q r s) := ![Set.range (bA p q r s), Set.range (rv (bB p q r s)),
    Set.range (bC p q r s), Set.range (rv (bD p q r s))]
  let D : Fin 4 → Pol p q r s := ![minorPoly (bA p q r s) α, minorPoly (rv (bB p q r s)) β,
    minorPoly (bC p q r s) γ, minorPoly (rv (bD p q r s)) δ]
  have hB4 : ∀ i j, i ≠ j → ∀ v ∈ B i, v ∉ B j := by
    intro i j hij v
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (rintro ⟨u, rfl⟩ ⟨w, e⟩; simp [zA, zB, zC, zD, rv] at e)
  have hv4 : ∀ j, ∀ v ∈ (D j).vars, v ∈ B j := by
    intro j
    fin_cases j
    exacts [vA, vB, vC, vD]
  have hd : ∀ i, ∀ v ∈ B i, pderiv v (∏ j ∈ Finset.univ.erase i, D j) = 0 := by
    intro i v hv
    refine pderiv_eq_zero_of_notMem_vars fun h' => ?_
    obtain ⟨j, hj, h''⟩ := Finset.mem_biUnion.1 (vars_prod _ h')
    exact hB4 i j (Finset.ne_of_mem_erase hj).symm v hv (hv4 j v h'')
  have hm := fun i => Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)
  have hΦ : FourHW α β γ δ (∏ j, D j) :=
    ⟨hm 0 ▸ hA.mul fun w => hd 0 _ ⟨w, rfl⟩, hm 1 ▸ hB.mul fun w => hd 1 _ ⟨w, rfl⟩,
      hm 2 ▸ hC.mul fun w => hd 2 _ ⟨w, rfl⟩, hm 3 ▸ hD.mul fun w => hd 3 _ ⟨w, rfl⟩⟩
  have hΦ0 : ∏ j, D j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => by
    fin_cases j
    exacts [nA, nB, nC, nD]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, eval x₀ (∏ j, D j) ≠ 0 := by
    by_contra! h0
    exact hΦ0 (MvPolynomial.funext fun x => by rw [h0, map_zero])
  rw [finrank_eq_one_iff_of_nonzero' (⟨_, joint_of_four h hΦ⟩ : jointHW μ μ')
    fun e => hΦ0 (congrArg Subtype.val e)]
  rintro ⟨P, hP⟩
  by_cases h0 : P = 0
  · exact ⟨0, Subtype.ext (by simp [h0])⟩
  obtain ⟨α', β', γ', δ', h', qA, qB, qC, qD⟩ := four_of_joint h0 hP
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h.unique h'
  refine ⟨eval x₀ P / eval x₀ (∏ j, D j), Subtype.ext (MvPolynomial.funext fun x => ?_)⟩
  have key := GlobalTheory.Harm.HighestUnique.eval_mul_prod_eq B hB4 D
    (fun j x x' hx => GlobalTheory.Harm.HighestUnique.eval_congr_vars fun v hv => hx v (hv4 j v hv)) P ?_ ?_
    x₀ x
  · rw [← map_prod, ← map_prod] at key
    change eval x (_ • ∏ j, D j) = eval x P
    rw [smul_eval, div_mul_eq_mul_div, ← key, mul_div_cancel_right₀ _ hx₀]
  · have g : ∀ {m n : ℕ} {z : Fin m × Fin n → Ln p q r s} {F : Pol p q r s},
        (∃ Q : Pol p q r s, (∀ w, z w ∉ Q.vars) ∧ P = Q * F) →
        ∃ Q : Pol p q r s, (∀ v ∈ Set.range z, v ∉ Q.vars) ∧ P = Q * F := by
      rintro m n z F ⟨Q, h1, h2⟩
      exact ⟨Q, by rintro _ ⟨w, rfl⟩; exact h1 w, h2⟩
    intro j
    fin_cases j
    exacts [g (exists_eq_mul_minorPoly _ _ _ _ iA α a1 a2 P qA),
      g (exists_eq_mul_minorPoly _ _ _ _ iB β b1 b2 P qB),
      g (exists_eq_mul_minorPoly _ _ _ _ iC γ c1 c2 P qC),
      g (exists_eq_mul_minorPoly _ _ _ _ iD δ d1 d2 P qD)]
  · rintro ⟨a | a, c | c⟩ -
    · exact ⟨0, (c, a), rfl⟩
    · exact ⟨1, (c.rev, a.rev), by simp [rv, zB]⟩
    · exact ⟨3, (c.rev, a.rev), by simp [rv, zD]⟩
    · exact ⟨2, (c, a), rfl⟩

theorem span_jointHarm : Submodule.span ℂ (jointHarm p q r s) =
    (harmSub (zA Prod.swap) (zB Prod.swap) ⊓ harmSub (zC Prod.swap) (zD Prod.swap)) ⊓
      (harmSub (zA id) (zB id) ⊓ harmSub (zC id) (zD id)) := by
  rw [← Submodule.span_eq (_ ⊓ _)]
  congr 1
  ext P
  exact and_congr (mem_harm2 P) (mem_harm1 P)

theorem joint_harmonics (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) :
    (JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s)) = 1) ∧
    (¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s) = ⊥) := by
  rw [span_jointHarm]
  constructor
  · intro h
    obtain ⟨α, β, γ, δ, h'⟩ := fnShape_of_jointShape p q r s μ μ' h
    exact finrank_jointHW h'
  · intro h
    refine (Submodule.eq_bot_iff _).2 fun P hP => by_contra fun h0 => h ?_
    obtain ⟨α, β, γ, δ, h', -⟩ := four_of_joint h0 hP
    exact jointShape_of_fnShape p q r s μ μ' ⟨α, β, γ, δ, h'⟩

end Joint


open Formalism.MainNotions.SchurIrreducible in
theorem fock_polynomials (X : ProvA) : admH2 X := by
  intro p q r s
  have hι := isFockIsometry_of_fockData (X.fock p q r s)
  have hinj := (X.fock p q r s).ι_inj
  refine ⟨fun d μ P hd hP => isSide_one.degW_le Function.bijective_id hd hP,
    fun d μ P hd hP => isSide_two.degW_le Prod.swap_bijective hd hP,
    fun μ P h0 ht hh => isSide_one.homog_of_type hι hinj Function.bijective_id h0 ht
      ((mem_harm1 P).1 hh),
    fun μ P h0 ht hh => isSide_two.homog_of_type hι hinj Prod.swap_bijective h0 ht
      ((mem_harm2 P).1 hh),
    fun μ μ' => joint_harmonics μ μ', fun u1 u2 _ d => ?_⟩
  refine fischer hι hinj {M | (u1 = true ∧ ∃ Z, IsPC Z ∧ M = kron1 r s Z) ∨
    (u2 = true ∧ ∃ Z, IsPC Z ∧ M = kron2 p q Z)} ?_ ?_ d _ _ (fun P hP => ?_) fun P => ?_
  · rintro _ (⟨-, Z, hZ, rfl⟩ | ⟨-, Z, hZ, rfl⟩)
    exacts [odd_kron1 hZ, odd_kron2 hZ]
  · rintro _ (⟨h, Z, hZ, rfl⟩ | ⟨h, Z, hZ, rfl⟩)
    exacts [⟨_, .inl ⟨h, _, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩,
      ⟨_, .inr ⟨h, _, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩]
  · exact ⟨fun h Z hZ => hP _ (.inl ⟨h, Z, hZ, rfl⟩), fun h Z hZ => hP _ (.inr ⟨h, Z, hZ, rfl⟩)⟩
  · constructor
    · rintro ⟨Q, hQ, ⟨h, Z, hZ, rfl⟩ | ⟨h, Z, hZ, rfl⟩⟩
      exacts [⟨Q, hQ, _, .inl ⟨h, Z, hZ, rfl⟩, rfl⟩, ⟨Q, hQ, _, .inr ⟨h, Z, hZ, rfl⟩, rfl⟩]
    · rintro ⟨Q, hQ, _, ⟨h, Z, hZ, rfl⟩ | ⟨h, Z, hZ, rfl⟩, rfl⟩
      exacts [⟨Q, hQ, .inl ⟨h, Z, hZ, rfl⟩⟩, ⟨Q, hQ, .inr ⟨h, Z, hZ, rfl⟩⟩]

end GlobalTheory.JointHarm
