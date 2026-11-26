module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumRowDegreeEqOfHarmonicHighestCasimir
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumRowDegreeEqOfHarmonicHighestCasimir
open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.HarmRowDegree

open GlobalTheory.Harm GlobalTheory.Harm.HighestUnique

private theorem sum_range_eq_sum_range_of_eventually_zero {n p : ℕ} (F : ℕ → ℤ) (hn : ∀ j, n ≤ j → F j = 0)
    (hp : ∀ j, p ≤ j → F j = 0) : ∑ j ∈ Finset.range n, F j = ∑ j ∈ Finset.range p, F j := by
  rcases le_total n p with h | h
  · exact Finset.sum_subset (Finset.range_mono h) fun j _ hj => hn j (by simpa using hj)
  · exact (Finset.sum_subset (Finset.range_mono h) fun j _ hj => hp j (by simpa using hj)).symm

theorem sum_pad {n p : ℕ} (f : Fin p → ℤ) (hf : ∀ i : Fin p, n ≤ i → f i = 0) :
    ∑ k : Fin n, (if h : (k : ℕ) < p then f ⟨k, h⟩ else 0) = ∑ k, f k := by
  have h1 : ∑ k : Fin n, (if h : (k : ℕ) < p then f ⟨k, h⟩ else 0) =
      ∑ j ∈ Finset.range n, (if h : j < p then f ⟨j, h⟩ else 0) :=
    Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) n
  have h2 : ∑ k : Fin p, f k = ∑ j ∈ Finset.range p, (if h : j < p then f ⟨j, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) p]
    exact Finset.sum_congr rfl fun k _ => by simp
  rw [h1, h2]
  apply sum_range_eq_sum_range_of_eventually_zero
  · intro j hj
    by_cases h : j < p
    · simp only [h, dite_true]
      exact hf ⟨j, h⟩ hj
    · simp [h]
  · intro j hj
    simp [not_lt.mpr hj]

theorem sum_pad_rev {n q : ℕ} (f : Fin q → ℤ) (hf : ∀ i : Fin q, n ≤ i → f i = 0) :
    ∑ k : Fin n, (if h : n - 1 - (k : ℕ) < q then f ⟨n - 1 - k, h⟩ else 0) = ∑ k, f k := by
  calc ∑ k : Fin n, (if h : n - 1 - (k : ℕ) < q then f ⟨n - 1 - k, h⟩ else 0)
      = ∑ j ∈ Finset.range n, (fun j => if h : j < q then f ⟨j, h⟩ else 0) (n - 1 - j) :=
        Fin.sum_univ_eq_sum_range (fun j => (fun j => if h : j < q then f ⟨j, h⟩ else 0) (n - 1 - j)) n
    _ = ∑ j ∈ Finset.range n, (fun j => if h : j < q then f ⟨j, h⟩ else 0) j :=
        Finset.sum_range_reflect (fun j => if h : j < q then f ⟨j, h⟩ else 0) n
    _ = ∑ k : Fin n, (if h : (k : ℕ) < q then f ⟨k, h⟩ else 0) :=
        (Fin.sum_univ_eq_sum_range (fun j => if h : j < q then f ⟨j, h⟩ else 0) n).symm
    _ = ∑ k, f k := sum_pad f hf

private theorem sum_filter_lt_eq_sum_range_min (n i : ℕ) (G : ℕ → ℤ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < i), G k =
      ∑ j ∈ Finset.range (min n i), G j := by
  rw [sum_filter_lt_eq_sum_range (fun k : Fin n => G k) i]
  have hs : Finset.range (min n i) = (Finset.range i).filter (fun j => j < n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    exact And.comm
  rw [hs, Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> rfl

theorem sum_filter_pad' {n p : ℕ} (a : Fin p → ℕ) (ha : ∀ i : Fin p, n ≤ i → a i = 0) (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < i),
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin p => (j : ℕ) < min n i), (a j : ℤ) := by
  rw [sum_filter_lt_eq_sum_range (fun j : Fin p => (a j : ℤ)) (min n i)]
  exact sum_filter_lt_eq_sum_range_min n i (fun j => if h : j < p then (a ⟨j, h⟩ : ℤ) else 0)

private theorem sum_filter_not_lt_eq_sum_range_sub (n i : ℕ) (G : ℕ → ℤ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (k : ℕ) < i), G (n - 1 - k) =
      ∑ j ∈ Finset.range (n - i), G j := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun j => if ¬ j < i then G (n - 1 - j) else 0) n]
  rw [← Finset.sum_range_reflect (fun j => if ¬ j < i then G (n - 1 - j) else 0) n]
  rw [← Finset.sum_subset (Finset.range_mono (Nat.sub_le n i)) ?_]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have e1 : ¬ (n - 1 - j < i) := by omega
    have e2 : n - 1 - (n - 1 - j) = j := by omega
    rw [if_pos e1, e2]
  · intro j hj hj'
    have h1 := Finset.mem_range.mp hj
    have h2 : ¬ j < n - i := fun h => hj' (Finset.mem_range.mpr h)
    have e1 : n - 1 - j < i := by omega
    rw [if_neg (not_not.mpr e1)]

theorem sum_filter_pad_rev' {n q : ℕ} (b : Fin q → ℕ) (hb : ∀ i : Fin q, n ≤ i → b i = 0)
    (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (k : ℕ) < i),
      (if h : n - 1 - (k : ℕ) < q then (b ⟨n - 1 - k, h⟩ : ℤ) else 0) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin q => (j : ℕ) < n - i), (b j : ℤ) := by
  rw [sum_filter_lt_eq_sum_range (fun j : Fin q => (b j : ℤ)) (n - i)]
  exact sum_filter_not_lt_eq_sum_range_sub n i (fun j => if h : j < q then (b ⟨j, h⟩ : ℤ) else 0)

private theorem casimir_sum_pad_eq_sum_range {n p : ℕ} (a : Fin p → ℕ) (ha : ∀ i : Fin p, n ≤ i → a i = 0) :
    ∑ i : Fin p, (a i : ℤ) * (a i + p - 1 - 2 * (i : ℕ)) + ((n : ℤ) - p) * ∑ i, (a i : ℤ) =
      ∑ j ∈ Finset.range n, (if h : j < p then (a ⟨j, h⟩ : ℤ) else 0) *
        ((if h : j < p then (a ⟨j, h⟩ : ℤ) else 0) + n - 1 - 2 * (j : ℤ)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [sum_range_eq_sum_range_of_eventually_zero (p := p) _ ?_ ?_]
  · rw [← Fin.sum_univ_eq_sum_range (fun j => (if h : j < p then (a ⟨j, h⟩ : ℤ) else 0) *
      ((if h : j < p then (a ⟨j, h⟩ : ℤ) else 0) + n - 1 - 2 * (j : ℤ))) p]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.is_lt, dite_true, Fin.eta]
    ring
  · intro j hj
    by_cases h : j < p
    · simp [h, ha ⟨j, h⟩ hj]
    · simp [h]
  · intro j hj
    simp [not_lt.mpr hj]

private theorem casimir_sum_sub_reverse_eq_add_sum_range (n : ℕ) (A B : ℕ → ℤ) :
    ∑ k : Fin n, (A k - B (n - 1 - k)) * (A k - B (n - 1 - k) + n - 1 - 2 * ((k : ℕ) : ℤ)) +
        2 * ∑ k : Fin n, A k * B (n - 1 - k) =
      ∑ j ∈ Finset.range n, A j * (A j + n - 1 - 2 * (j : ℤ)) +
        ∑ j ∈ Finset.range n, B j * (B j + n - 1 - 2 * (j : ℤ)) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (A j - B (n - 1 - j)) *
      (A j - B (n - 1 - j) + n - 1 - 2 * (j : ℤ))) n,
    Fin.sum_univ_eq_sum_range (fun j => A j * B (n - 1 - j)) n]
  rw [← Finset.sum_range_reflect (fun j => B j * (B j + n - 1 - 2 * (j : ℤ))) n]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have e : ((n - 1 - j : ℕ) : ℤ) = (n : ℤ) - 1 - j := by omega
  rw [e]
  ring

theorem casimir_value_pad {n p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ)
    (ha : ∀ i : Fin p, n ≤ i → a i = 0) (hb : ∀ i : Fin q, n ≤ i → b i = 0) :
    (∑ i : Fin p, (a i : ℤ) * (a i + p - 1 - 2 * (i : ℕ)) + ((n : ℤ) - p) * ∑ i, (a i : ℤ)) +
      (∑ i : Fin q, (b i : ℤ) * (b i + q - 1 - 2 * (i : ℕ)) + ((n : ℤ) - q) * ∑ i, (b i : ℤ)) =
    ∑ k : Fin n, mixedWeight n a b k * (mixedWeight n a b k + n - 1 - 2 * (k : ℕ)) +
      2 * ∑ k : Fin n, (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) *
        (if h : n - 1 - (k : ℕ) < q then (b ⟨n - 1 - k, h⟩ : ℤ) else 0) := by
  rw [casimir_sum_pad_eq_sum_range a ha, casimir_sum_pad_eq_sum_range b hb]
  simp only [mixedWeight_apply]
  exact (casimir_sum_sub_reverse_eq_add_sum_range n (fun j => if h : j < p then (a ⟨j, h⟩ : ℤ) else 0)
    (fun j => if h : j < q then (b ⟨j, h⟩ : ℤ) else 0)).symm

theorem row_degree_eq_zero {K σ : Type*} [Field K] [CharZero K] [DecidableEq σ] {p n : ℕ}
    (z : Fin p × Fin n → σ) (hz : Function.Injective z) {P : MvPolynomial σ K} (hP : P ≠ 0)
    (a : Fin p → ℕ) (hrow : ∀ i, ∀ m ∈ P.support, ∑ k, m (z (i, k)) = a i)
    (hinv : ∀ i j : Fin p, i < j → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (j, k) then C t * X (z (i, k)) else 0) P = P)
    (i : Fin p) (hi : n ≤ i) : a i = 0 := by
  obtain ⟨m, hm⟩ : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h => hP (MvPolynomial.support_eq_empty.mp h)
  have h := column_degree_le z hz P a hrow hinv Finset.univ m hm
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hsum : ∑ j, ∑ k ∈ Finset.univ, m (z (j, k)) = ∑ j, a j :=
    Finset.sum_congr rfl fun j _ => hrow j m hm
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin p => (j : ℕ) < n)] at h
  have h2 : ∑ j ∈ Finset.univ.filter (fun j : Fin p => ¬ (j : ℕ) < n), a j = 0 := by omega
  exact (Finset.sum_eq_zero_iff.mp h2) i (by simp [hi])

theorem sum_row_degree_eq : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (k l n : ℕ) (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ), Function.Injective z → Function.Injective y → (∀ u w, z u ≠ y w) → ∀ (P : MvPolynomial σ ℂ) (a : Fin k → ℕ) (b : Fin l → ℕ) (κ : Fin n → ℤ), P ≠ 0 → Antitone a → Antitone b → Antitone κ → (∀ i j, i < j → rowOp ℂ z i j P = 0) → (∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) → (∀ i j, i < j → rowOp ℂ y i j P = 0) → (∀ i, rowOp ℂ y i i P = (b i : ℂ) • P) → (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = 0) → (∀ i j, i < j → mixedOp ℂ z y i j P = 0) → (∀ t, mixedOp ℂ z y t t P = (κ t : ℂ) • P) → ∑ i, (a i : ℤ) = ∑ t, max (κ t) 0 := by
  intro σ _ _ k l n z y hz hy hzy P a b κ hP ha hb hκ hzu hzd hyu hyd hharm hup hwt
  have hrz : ∀ i, ∀ m ∈ P.support, ∑ t, m (z (i, t)) = a i := fun i m hm => by
    have := (rowOp_eq_smul_iff z i P (a i : ℂ)).mp (hzd i) m hm
    exact_mod_cast this
  have hry : ∀ i, ∀ m ∈ P.support, ∑ t, m (y (i, t)) = b i := fun i m hm => by
    have := (rowOp_eq_smul_iff y i P (b i : ℂ)).mp (hyd i) m hm
    exact_mod_cast this
  have hiz : ∀ i j : Fin k, i < j → ∀ t : ℂ,
      bind₁ (fun s => X s + ∑ t', if s = z (j, t') then C t * X (z (i, t')) else 0) P = P := by
    intro i j hij
    have hw : Function.Injective fun t : Fin n => z (j, t) := fun t t' h => by
      simpa using hz h
    have huw : ∀ t t' : Fin n, z (i, t) ≠ z (j, t') := fun t t' h => by
      have := hz h
      simp only [Prod.mk.injEq] at this
      exact (ne_of_lt hij) this.1
    have := (rowAdd_invariant_iff (K := ℂ) (fun t => z (i, t)) (fun t => z (j, t)) hw huw P).out 2 3
    exact this.mpr ((rowOp_apply z i j P).symm.trans (hzu i j hij))
  have hiy : ∀ i j : Fin l, i < j → ∀ t : ℂ,
      bind₁ (fun s => X s + ∑ t', if s = y (j, t') then C t * X (y (i, t')) else 0) P = P := by
    intro i j hij
    have hw : Function.Injective fun t : Fin n => y (j, t) := fun t t' h => by
      simpa using hy h
    have huw : ∀ t t' : Fin n, y (i, t) ≠ y (j, t') := fun t t' h => by
      have := hy h
      simp only [Prod.mk.injEq] at this
      exact (ne_of_lt hij) this.1
    have := (rowAdd_invariant_iff (K := ℂ) (fun t => y (i, t)) (fun t => y (j, t)) hw huw P).out 2 3
    exact this.mpr ((rowOp_apply y i j P).symm.trans (hyu i j hij))
  have ha0 : ∀ i : Fin k, n ≤ i → a i = 0 := row_degree_eq_zero z hz hP a hrz hiz
  have hb0 : ∀ i : Fin l, n ≤ i → b i = 0 := row_degree_eq_zero y hy hP b hry hiy
  have hC1 := casimir_on_highest (mixedOp ℂ z y) (mixedOp_lie z hz y hy hzy) P κ hup hwt
  have hC2 := casimir_mixedOp z hz y hy hzy P
  have hcross : ∑ i, ∑ j, (∑ t, X (z (i, t)) * X (y (j, t))) *
      ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = (0 : MvPolynomial σ ℂ) := by
    simp [hharm]
  rw [casimir_rows z hz a hrz hiz, casimir_rows y hy b hry hiy, hcross, smul_zero, sub_zero,
    ← add_smul] at hC2
  have hCint : ∑ i, κ i * (κ i + n - 1 - 2 * (i : ℕ)) =
      (∑ i : Fin k, (a i : ℤ) * (a i + k - 1 - 2 * (i : ℕ)) + ((n : ℤ) - k) * ∑ i, (a i : ℤ)) +
      (∑ i : Fin l, (b i : ℤ) * (b i + l - 1 - 2 * (i : ℕ)) + ((n : ℤ) - l) * ∑ i, (b i : ℤ)) := by
    have := smul_left_injective ℂ hP (hC1.symm.trans hC2)
    exact_mod_cast this
  have hpad := casimir_value_pad a b ha0 hb0
  have hpair : 0 ≤ ∑ t : Fin n, (if h : (t : ℕ) < k then (a ⟨t, h⟩ : ℤ) else 0) * (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) :=
    Finset.sum_nonneg fun t _ => mul_nonneg (by split_ifs <;> simp) (by split_ifs <;> simp)
  obtain ⟨m, hm⟩ : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h => hP (MvPolynomial.support_eq_empty.mp h)
  have hw : ∀ t, ∑ j, (m (z (j, t)) : ℤ) - ∑ j, (m (y (j, t)) : ℤ) = κ t := fun t => weight_of_mem_support z y (hwt t) hm
  have hzs : ∑ t, ∑ j, (m (z (j, t)) : ℤ) = ∑ i, (a i : ℤ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by exact_mod_cast hrz i m hm
  have hys : ∑ t, ∑ j, (m (y (j, t)) : ℤ) = ∑ i, (b i : ℤ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by exact_mod_cast hry i m hm
  have hcard : ∀ i : ℕ, (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)).card = min n i := by
    intro i
    have e : (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)).map Fin.valEmbedding = Finset.range (min n i) := by
      ext j
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_range, lt_min_iff]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t.isLt, ht⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨j, h1⟩, h2, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, e, Finset.card_range]
  have hcard' : ∀ i : ℕ, (Finset.univ.filter (fun t : Fin n => ¬ (t : ℕ) < i)).card = n - i := by
    intro i
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun t : Fin n => (t : ℕ) < i)
    rw [hcard i, Finset.card_univ, Fintype.card_fin] at h
    omega
  have hb0' : ∀ j : Fin l, n ≤ j → (b j : ℤ) = 0 := fun j hj => by simp [hb0 j hj]
  have ha0' : ∀ j : Fin k, n ≤ j → (a j : ℤ) = 0 := fun j hj => by simp [ha0 j hj]
  have hle : ∀ i : ℕ, ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), κ t ≤ ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), mixedWeight n a b t := by
    intro i
    have f1 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), κ t = ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), ∑ j, (m (z (j, t)) : ℤ) - ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), ∑ j, (m (y (j, t)) : ℤ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => (hw t).symm
    have f2 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), ∑ j, (m (z (j, t)) : ℤ) ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin k => (j : ℕ) < min n i), (a j : ℤ) := by
      have h := column_degree_le z hz P a hrz hiz (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)) m hm
      rw [hcard i] at h
      rw [Finset.sum_comm]
      exact_mod_cast h
    have f3 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), ∑ j, (m (y (j, t)) : ℤ) + ∑ t ∈ (Finset.univ.filter (fun t : Fin n => ¬ (t : ℕ) < i)), ∑ j, (m (y (j, t)) : ℤ) = ∑ j, (b j : ℤ) := by
      rw [Finset.sum_filter_add_sum_filter_not, hys]
    have f4 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => ¬ (t : ℕ) < i)), ∑ j, (m (y (j, t)) : ℤ) ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin l => (j : ℕ) < n - i), (b j : ℤ) := by
      have h := column_degree_le y hy P b hry hiy (Finset.univ.filter (fun t : Fin n => ¬ (t : ℕ) < i)) m hm
      rw [hcard' i] at h
      rw [Finset.sum_comm]
      exact_mod_cast h
    have f5 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), mixedWeight n a b t = ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), (if h : (t : ℕ) < k then (a ⟨t, h⟩ : ℤ) else 0) - ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => mixedWeight_apply n a b t
    have f6 := sum_filter_pad' a ha0 i
    have f7 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) + ∑ t ∈ (Finset.univ.filter (fun t : Fin n => ¬ (t : ℕ) < i)), (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) = ∑ j, (b j : ℤ) := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact sum_pad_rev (fun j => (b j : ℤ)) hb0'
    have f8 := sum_filter_pad_rev' b hb0 i
    linarith
  have hsum : ∑ t, κ t = ∑ t, mixedWeight n a b t := by
    have e1 : ∑ t, κ t = ∑ i, (a i : ℤ) - ∑ j, (b j : ℤ) := by
      rw [← hzs, ← hys, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => (hw t).symm
    have e2 : ∑ t, mixedWeight n a b t = ∑ t : Fin n, (if h : (t : ℕ) < k then (a ⟨t, h⟩ : ℤ) else 0) - ∑ t : Fin n, (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => mixedWeight_apply n a b t
    rw [e1, e2, sum_pad (fun j => (a j : ℤ)) ha0', sum_pad_rev (fun j => (b j : ℤ)) hb0']
  have hCle : ∑ t, mixedWeight n a b t * (mixedWeight n a b t + n - 1 - 2 * (t : ℕ)) ≤
      ∑ t, κ t * (κ t + n - 1 - 2 * (t : ℕ)) := by
    linarith
  have hκμ : κ = mixedWeight n a b :=
    casimir_value_strict κ (mixedWeight n a b) hκ (antitone_mixedWeight n ha hb) hle hsum hCle
  subst hκμ
  have hpair0 : ∑ t : Fin n, (if h : (t : ℕ) < k then (a ⟨t, h⟩ : ℤ) else 0) * (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) = 0 := by linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ =>
    mul_nonneg (by split_ifs <;> simp) (by split_ifs <;> simp))).mp hpair0
  rw [← sum_pad (fun j => (a j : ℤ)) ha0']
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [mixedWeight_apply]
  have hA : 0 ≤ (if h : (t : ℕ) < k then (a ⟨t, h⟩ : ℤ) else 0) := by split_ifs <;> simp
  have hB : 0 ≤ (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) := by split_ifs <;> simp
  rcases mul_eq_zero.mp (hterm t ht) with h | h
  · rw [h, zero_sub, max_eq_right (by linarith)]
  · rw [h, sub_zero, max_eq_left hA]

end GlobalTheory.HarmRowDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumRowDegreeEqOfHarmonicHighestCasimirStatement
open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_row_degree_eq_of_harmonic_highest_casimir : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (k l n : ℕ) (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ), Function.Injective z → Function.Injective y → (∀ u w, z u ≠ y w) → ∀ (P : MvPolynomial σ ℂ) (a : Fin k → ℕ) (b : Fin l → ℕ) (κ : Fin n → ℤ), P ≠ 0 → Antitone a → Antitone b → Antitone κ → (∀ i j, i < j → rowOp ℂ z i j P = 0) → (∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) → (∀ i j, i < j → rowOp ℂ y i j P = 0) → (∀ i, rowOp ℂ y i i P = (b i : ℂ) • P) → (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = 0) → (∀ i j, i < j → mixedOp ℂ z y i j P = 0) → (∀ t, mixedOp ℂ z y t t P = (κ t : ℂ) • P) → ∑ i, (a i : ℤ) = ∑ t, max (κ t) 0 := by
  first | exact @GlobalTheory.HarmRowDegree.sum_row_degree_eq | exact GlobalTheory.HarmRowDegree.sum_row_degree_eq | (intros; apply GlobalTheory.HarmRowDegree.sum_row_degree_eq <;> assumption)
end
end

noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.ColumnDegree

theorem polar_mem {σ : Type} (u v : σ) (N : ℕ) (Q : MvPolynomial σ ℂ)
    (hQ : Q ∈ restrictTotalDegree σ ℂ N) : polar ℂ u v Q ∈ restrictTotalDegree σ ℂ N := by
  classical
  have hQN : Q.totalDegree ≤ N := by rwa [mem_restrictTotalDegree] at hQ
  have hadd : ∀ a b : σ →₀ ℕ, ((a + b).sum fun _ e => e) = (a.sum fun _ e => e) + (b.sum fun _ e => e) :=
    fun a b => Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  have hone : ∀ w : σ, ((Finsupp.single w 1).sum fun _ e => e) = 1 :=
    fun w => Finsupp.sum_single_index rfl
  have key : ∀ s ∈ Q.support,
      X u * pderiv v (monomial s (AddMonoidAlgebra.coeff Q s)) ∈ restrictTotalDegree σ ℂ N := by
    intro s hs
    have hsN : (s.sum fun _ e => e) ≤ N := (le_totalDegree hs).trans hQN
    rw [pderiv_monomial]
    by_cases hv : s v = 0
    · rw [hv]; simp
    · have hle : Finsupp.single v 1 ≤ s := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hv)
      rw [mem_restrictTotalDegree, X, monomial_mul, one_mul]
      refine (totalDegree_monomial_le _ _).trans ?_
      have e1 : s = (s - Finsupp.single v 1) + Finsupp.single v 1 := (tsub_add_cancel_of_le hle).symm
      have h1 := hadd (s - Finsupp.single v 1) (Finsupp.single v 1)
      rw [← e1, hone] at h1
      have h2 := hadd (Finsupp.single u 1) (s - Finsupp.single v 1)
      rw [hone] at h2
      change ((Finsupp.single u 1 + (s - Finsupp.single v 1)).sum fun _ e => e) ≤ N
      omega
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polar_apply, Q.as_sum, map_sum, Finset.mul_sum]
  exact Submodule.sum_mem _ key

theorem colOp_mem {σ I J : Type} [Fintype I] (z : I × J → σ) (a b : J) (N : ℕ)
    (Q : MvPolynomial σ ℂ) (hQ : Q ∈ restrictTotalDegree σ ℂ N) :
    colOp ℂ z a b Q ∈ restrictTotalDegree σ ℂ N := by
  rw [colOp_apply]
  exact Submodule.sum_mem _ fun i _ => by
    simpa only [polar_apply] using polar_mem (z (i, a)) (z (i, b)) N Q hQ

theorem rowOp_mem {σ I J : Type} [Fintype J] (z : I × J → σ) (a b : I) (N : ℕ)
    (Q : MvPolynomial σ ℂ) (hQ : Q ∈ restrictTotalDegree σ ℂ N) :
    rowOp ℂ z a b Q ∈ restrictTotalDegree σ ℂ N := by
  rw [rowOp_apply]
  exact Submodule.sum_mem _ fun t _ => by
    simpa only [polar_apply] using polar_mem (z (a, t)) (z (b, t)) N Q hQ

theorem harmonic_rowOp {σ I I' J : Type} [Fintype J] (z : I × J → σ) (y : I' × J → σ)
    (hz : Function.Injective z) (hzy : ∀ u w, z u ≠ y w) (Q : MvPolynomial σ ℂ)
    (hQ : ∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) Q) = 0) (a b : I) (i : I) (j : I') :
    ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) (rowOp ℂ z a b Q)) = 0 := by
  classical
  have hexp : ∀ t k, pderiv (z (i, t)) (pderiv (y (j, t)) (X (z (a, k)) * pderiv (z (b, k)) Q)) =
      X (z (a, k)) * pderiv (z (i, t)) (pderiv (y (j, t)) (pderiv (z (b, k)) Q)) +
        (if i = a ∧ t = k then pderiv (y (j, t)) (pderiv (z (b, k)) Q) else 0) := by
    intro t k
    rw [pderiv_X_mul', if_neg (fun h => hzy _ _ h.symm), add_zero, pderiv_X_mul']
    congr 1
    simp only [hz.eq_iff, Prod.mk.injEq]
  have hA : ∑ t, ∑ k, X (z (a, k)) * pderiv (z (i, t)) (pderiv (y (j, t)) (pderiv (z (b, k)) Q))
      = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum]
    have hsw : ∀ t, pderiv (z (i, t)) (pderiv (y (j, t)) (pderiv (z (b, k)) Q)) =
        pderiv (z (b, k)) (pderiv (z (i, t)) (pderiv (y (j, t)) Q)) := by
      intro t
      rw [pderiv_swap (y (j, t)) (z (b, k)), pderiv_swap (z (i, t)) (z (b, k))]
    simp only [hsw]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hQ i j, map_zero, mul_zero]
  have hB : ∑ t, ∑ k, (if i = a ∧ t = k then pderiv (y (j, t)) (pderiv (z (b, k)) Q) else 0)
      = 0 := by
    by_cases hia : i = a
    · simp only [hia, true_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← hQ b j]
      exact Finset.sum_congr rfl fun t _ => pderiv_swap _ _ _
    · simp [hia]
  rw [rowOp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hexp, Finset.sum_add_distrib, hA, hB, add_zero]

private theorem coeff_apply_of_diagonal_on_monomials' {σ : Type} (g : Module.End ℂ (MvPolynomial σ ℂ))
    (w : (σ →₀ ℕ) → ℂ) (hg : ∀ u, g (monomial u 1) = w u • monomial u 1) (m : σ →₀ ℕ)
    (Q : MvPolynomial σ ℂ) : AddMonoidAlgebra.coeff (g Q) m = w m * AddMonoidAlgebra.coeff Q m := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial u c =>
    have hc : (monomial u c : MvPolynomial σ ℂ) = c • monomial u 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hc, map_smul, hg, smul_smul]
    simp only [coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · subst h; ring
    · ring
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem coeff_euler {σ : Type} {k n : ℕ} (z : Fin k × Fin n → σ) (m : σ →₀ ℕ)
    (Q : MvPolynomial σ ℂ) :
    AddMonoidAlgebra.coeff ((∑ i, rowOp ℂ z i i) Q) m = ((∑ i, ∑ t, (m (z (i, t)) : ℤ) : ℤ) : ℂ) * AddMonoidAlgebra.coeff Q m := by
  refine coeff_apply_of_diagonal_on_monomials' _ (fun u => ((∑ i, ∑ t, (u (z (i, t)) : ℤ) : ℤ) : ℂ)) (fun u => ?_) m Q
  rw [LinearMap.sum_apply]
  simp only [rowOp_monomial]
  rw [← Finset.sum_smul]
  push_cast
  rfl

theorem commute_euler {σ : Type} {k n : ℕ} (z : Fin k × Fin n → σ) (hz : Function.Injective z)
    (a b : Fin k) : Commute (∑ i, rowOp ℂ z i i) (rowOp ℂ z a b) := by
  show (∑ i, rowOp ℂ z i i) * rowOp ℂ z a b = rowOp ℂ z a b * ∑ i, rowOp ℂ z i i
  rw [← sub_eq_zero, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [rowOp_lie z hz, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]

theorem weight_nat {σ : Type} {k n : ℕ} (z : Fin k × Fin n → σ) (v : MvPolynomial σ ℂ)
    (hv : v ≠ 0) (a : Fin k → ℤ) (ha : ∀ i, rowOp ℂ z i i v = (a i : ℂ) • v) :
    ∃ a' : Fin k → ℕ, ∀ i, (a' i : ℤ) = a i := by
  classical
  have hne : v.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hv
  obtain ⟨m, hm⟩ := hne
  refine ⟨fun i => ∑ t, m (z (i, t)), fun i => ?_⟩
  have h := (rowOp_eq_smul_iff z i v (a i : ℂ)).1 (ha i) m hm
  exact_mod_cast h

theorem column_degrees (σ : Type) [Fintype σ] [DecidableEq σ] (k l n : ℕ)
    (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ) (hz : Function.Injective z)
    (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w) (P : MvPolynomial σ ℂ) (κ : Fin n → ℤ)
    (hP0 : P ≠ 0) (hharm : ∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = 0)
    (hup : ∀ i j, i < j → mixedOp ℂ z y i j P = 0)
    (hwt : ∀ t, mixedOp ℂ z y t t P = (κ t : ℂ) • P) :
    Antitone κ ∧ ∀ m ∈ P.support, ∀ t, ∑ i, (m (z (i, t)) : ℤ) = max (κ t) 0 ∧
      ∑ j, (m (y (j, t)) : ℤ) = max (-κ t) 0 := by
  classical
  have hPV : P ∈ restrictTotalDegree σ ℂ P.totalDegree := by rw [mem_restrictTotalDegree]
  have hmixV : ∀ i j, ∀ Q ∈ restrictTotalDegree σ ℂ P.totalDegree,
      mixedOp ℂ z y i j Q ∈ restrictTotalDegree σ ℂ P.totalDegree := by
    intro i j Q hQ
    rw [mixedOp_apply, ← colOp_apply (K := ℂ) z i j Q, ← colOp_apply (K := ℂ) y j i Q]
    exact Submodule.sub_mem _ (colOp_mem z i j _ Q hQ) (colOp_mem y j i _ Q hQ)
  have hκ : Antitone κ :=
    highest_weight_antitone (mixedOp ℂ z y) (mixedOp_lie z hz y hy hzy)
      (restrictTotalDegree σ ℂ P.totalDegree) hmixV P hPV hP0 κ hup hwt

  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ (MvPolynomial σ ℂ), ∀ Q, Q ∈ W ↔
      (Q ∈ restrictTotalDegree σ ℂ P.totalDegree ∧
        (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) Q) = 0) ∧
        (∀ i j, i < j → mixedOp ℂ z y i j Q = 0) ∧ ∀ t, mixedOp ℂ z y t t Q = (κ t : ℂ) • Q) :=
    ⟨{ carrier := {Q | Q ∈ restrictTotalDegree σ ℂ P.totalDegree ∧
          (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) Q) = 0) ∧
          (∀ i j, i < j → mixedOp ℂ z y i j Q = 0) ∧ ∀ t, mixedOp ℂ z y t t Q = (κ t : ℂ) • Q}
       add_mem' := by
         rintro Q R ⟨h1, h2, h3, h4⟩ ⟨g1, g2, g3, g4⟩
         refine ⟨Submodule.add_mem _ h1 g1, fun i j => ?_, fun i j hij => ?_, fun t => ?_⟩
         · simp only [map_add (f := _), Finset.sum_add_distrib, h2 i j, g2 i j, add_zero]
         · rw [map_add (f := _), h3 i j hij, g3 i j hij, add_zero]
         · rw [map_add (f := _), h4 t, g4 t, smul_add]
       zero_mem' := ⟨Submodule.zero_mem _, fun i j => by simp, fun i j _ => map_zero _,
         fun t => by simp⟩
       smul_mem' := by
         rintro c Q ⟨h1, h2, h3, h4⟩
         refine ⟨Submodule.smul_mem _ c h1, fun i j => ?_, fun i j hij => ?_, fun t => ?_⟩
         · simp only [Derivation.map_smul, ← Finset.smul_sum, h2 i j, smul_zero]
         · rw [map_smul, h3 i j hij, smul_zero]
         · rw [map_smul, h4 t, smul_comm] }, fun Q => Iff.rfl⟩
  have hPW : P ∈ W := (hW P).2 ⟨hPV, hharm, hup, hwt⟩
  have hWz : ∀ a b, ∀ Q ∈ W, rowOp ℂ z a b Q ∈ W := by
    intro a b Q hQ
    obtain ⟨h1, h2, h3, h4⟩ := (hW Q).1 hQ
    refine (hW _).2 ⟨rowOp_mem z a b _ Q h1, fun i j => harmonic_rowOp z y hz hzy Q h2 a b i j,
      fun i j hij => ?_, fun t => ?_⟩
    · rw [← Module.End.mul_apply, ← (commute_rowOp_left_mixedOp z hz y hzy a b i j).eq,
        Module.End.mul_apply, h3 i j hij, map_zero]
    · rw [← Module.End.mul_apply, ← (commute_rowOp_left_mixedOp z hz y hzy a b t t).eq,
        Module.End.mul_apply, h4 t, map_smul]
  have hWy : ∀ a b, ∀ Q ∈ W, rowOp ℂ y a b Q ∈ W := by
    intro a b Q hQ
    obtain ⟨h1, h2, h3, h4⟩ := (hW Q).1 hQ
    have h2' : ∀ i j, ∑ t, pderiv (y (i, t)) (pderiv (z (j, t)) Q) = 0 := by
      intro i j
      rw [← h2 j i]
      exact Finset.sum_congr rfl fun t _ => pderiv_swap _ _ _
    refine (hW _).2 ⟨rowOp_mem y a b _ Q h1, fun i j => ?_, fun i j hij => ?_, fun t => ?_⟩
    · rw [← harmonic_rowOp y z hy (fun u w h => hzy w u h.symm) Q h2' a b j i]
      exact Finset.sum_congr rfl fun t _ => pderiv_swap _ _ _
    · rw [← Module.End.mul_apply, ← (commute_rowOp_right_mixedOp z y hy hzy a b i j).eq,
        Module.End.mul_apply, h3 i j hij, map_zero]
    · rw [← Module.End.mul_apply, ← (commute_rowOp_right_mixedOp z y hy hzy a b t t).eq,
        Module.End.mul_apply, h4 t, map_smul]

  obtain ⟨E, hE⟩ : ∃ E : Module.End ℂ (MvPolynomial σ ℂ), E = ∑ i, rowOp ℂ z i i := ⟨_, rfl⟩
  obtain ⟨zdeg, hzdeg⟩ : ∃ f : (σ →₀ ℕ) → ℤ, ∀ m, f m = ∑ i, ∑ t, (m (z (i, t)) : ℤ) :=
    ⟨_, fun _ => rfl⟩
  have hcoeffE : ∀ m Q, AddMonoidAlgebra.coeff (E Q) m = (zdeg m : ℂ) * AddMonoidAlgebra.coeff Q m := by
    intro m Q
    rw [hE, hzdeg]
    exact coeff_euler z m Q
  have hWE : ∀ Q ∈ W, E Q ∈ W := by
    intro Q hQ
    rw [hE, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ => hWz i i Q hQ

  have hkey : ∀ Q ∈ W, Q ≠ 0 → ∀ μ : ℂ, E Q = μ • Q → μ = ((∑ t, max (κ t) 0 : ℤ) : ℂ) := by
    intro Q hQW hQ0 μ hμ
    obtain ⟨W', hW'⟩ : ∃ W' : Submodule ℂ (MvPolynomial σ ℂ), ∀ R, R ∈ W' ↔ (R ∈ W ∧ E R = μ • R) :=
      ⟨{ carrier := {R | R ∈ W ∧ E R = μ • R}
         add_mem' := by
           rintro R R' ⟨h1, h2⟩ ⟨g1, g2⟩
           exact ⟨W.add_mem h1 g1, by rw [map_add (f := _), h2, g2, smul_add]⟩
         zero_mem' := ⟨W.zero_mem, by simp⟩
         smul_mem' := by
           rintro c R ⟨h1, h2⟩
           exact ⟨W.smul_mem c h1, by rw [map_smul, h2, smul_comm]⟩ }, fun R => Iff.rfl⟩
    have hW'V : W' ≤ restrictTotalDegree σ ℂ P.totalDegree := fun R hR =>
      ((hW R).1 ((hW' R).1 hR).1).1
    have : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hW'V
    have hEz : ∀ a b, Commute E (rowOp ℂ z a b) := by
      intro a b; rw [hE]; exact commute_euler z hz a b
    have hEy : ∀ a b, Commute E (rowOp ℂ y a b) := by
      intro a b; rw [hE]
      exact Commute.sum_left _ _ _ fun i _ => commute_rowOp_rowOp z y hzy i i a b
    have hW'z : ∀ a b, ∀ R ∈ W', rowOp ℂ z a b R ∈ W' := by
      intro a b R hR
      obtain ⟨h1, h2⟩ := (hW' R).1 hR
      refine (hW' _).2 ⟨hWz a b R h1, ?_⟩
      rw [← Module.End.mul_apply, (hEz a b).eq, Module.End.mul_apply, h2, map_smul]
    have hW'y : ∀ a b, ∀ R ∈ W', rowOp ℂ y a b R ∈ W' := by
      intro a b R hR
      obtain ⟨h1, h2⟩ := (hW' R).1 hR
      refine (hW' _).2 ⟨hWy a b R h1, ?_⟩
      rw [← Module.End.mul_apply, (hEy a b).eq, Module.End.mul_apply, h2, map_smul]
    have hQW' : Q ∈ W' := (hW' Q).2 ⟨hQW, hμ⟩
    have hW'0 : W' ≠ ⊥ := by
      intro h
      rw [h] at hQW'
      exact hQ0 ((Submodule.mem_bot ℂ).1 hQW')
    obtain ⟨v, hvW, hv0, hvz, hvy, a, b, ha, hb⟩ :=
      exists_highest_pair (rowOp ℂ z) (rowOp ℂ y) (rowOp_lie z hz) (rowOp_lie y hy)
        (commute_rowOp_rowOp z y hzy)
        (iSup_eigenspace_eq_top (fun i => rowOp ℂ z i i) (fun m i => ∑ t, (m (z (i, t)) : ℤ))
          (fun m i => rowOp_monomial z i m))
        (iSup_eigenspace_eq_top (fun i => rowOp ℂ y i i) (fun m i => ∑ t, (m (y (i, t)) : ℤ))
          (fun m i => rowOp_monomial y i m))
        W' hW'z hW'y hW'0
    obtain ⟨hvW1, hvE⟩ := (hW' v).1 hvW
    obtain ⟨-, hvH, hvU, hvK⟩ := (hW v).1 hvW1
    obtain ⟨a', ha'⟩ := weight_nat z v hv0 a ha
    obtain ⟨b', hb'⟩ := weight_nat y v hv0 b hb
    have haa : Antitone a := highest_weight_antitone (rowOp ℂ z) (rowOp_lie z hz) W' hW'z v hvW hv0 a hvz ha
    have hbb : Antitone b := highest_weight_antitone (rowOp ℂ y) (rowOp_lie y hy) W' hW'y v hvW hv0 b hvy hb
    have ha'a : Antitone a' := fun i j hij => by
      have h := haa hij
      rw [← ha' i, ← ha' j] at h
      exact_mod_cast h
    have hb'b : Antitone b' := fun i j hij => by
      have h := hbb hij
      rw [← hb' i, ← hb' j] at h
      exact_mod_cast h
    have hza : ∀ i, rowOp ℂ z i i v = (a' i : ℂ) • v := fun i => by
      rw [ha i, ← ha' i, Int.cast_natCast]
    have hyb : ∀ i, rowOp ℂ y i i v = (b' i : ℂ) • v := fun i => by
      rw [hb i, ← hb' i, Int.cast_natCast]
    have hT := GlobalTheory.T.sum_row_degree_eq_of_harmonic_highest_casimir σ k l n z y hz hy hzy v a' b' κ hv0 ha'a hb'b hκ hvz hza hvy hyb hvH hvU hvK
    have hEv : E v = ((∑ i, (a' i : ℤ) : ℤ) : ℂ) • v := by
      rw [hE, LinearMap.sum_apply]
      simp only [hza]
      rw [← Finset.sum_smul]
      push_cast
      rfl
    have hzero : (μ - ((∑ i, (a' i : ℤ) : ℤ) : ℂ)) • v = 0 := by
      rw [sub_smul, ← hvE, hEv, sub_self]
    rcases smul_eq_zero.1 hzero with h | h
    · rw [← hT]; exact sub_eq_zero.1 h
    · exact absurd h hv0

  have hdeg : ∀ m ∈ P.support, zdeg m = ∑ t, max (κ t) 0 := by
    intro m0 hm0
    by_contra hne
    have hiter : ∀ s : Finset ℤ, ∃ Q ∈ W, ∀ m,
        AddMonoidAlgebra.coeff Q m = (∏ D ∈ s, ((zdeg m : ℂ) - (D : ℂ))) * AddMonoidAlgebra.coeff P m := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨P, hPW, fun m => by simp⟩
      | insert D s hD ih =>
        obtain ⟨Q, hQW, hQ⟩ := ih
        refine ⟨E Q - (D : ℂ) • Q, W.sub_mem (hWE Q hQW) (W.smul_mem _ hQW), fun m => ?_⟩
        rw [coeff_sub, coeff_smul, hcoeffE, hQ, Finset.prod_insert hD, smul_eq_mul]
        ring
    obtain ⟨Q, hQW, hQ⟩ := hiter ((P.support.image zdeg).erase (zdeg m0))
    have hQm0 : AddMonoidAlgebra.coeff Q m0 ≠ 0 := by
      rw [hQ]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun D hD => sub_ne_zero.2 ?_)
        (mem_support_iff.1 hm0)
      intro h
      exact (Finset.mem_erase.1 hD).1 (by exact_mod_cast h.symm)
    have hQ0 : Q ≠ 0 := fun h => hQm0 (by simp [h])
    have hEQ : E Q = (zdeg m0 : ℂ) • Q := by
      ext m
      rw [hcoeffE, coeff_smul, smul_eq_mul]
      by_cases hm : AddMonoidAlgebra.coeff Q m = 0
      · rw [hm, mul_zero, mul_zero]
      · have hmP : m ∈ P.support := by
          rw [mem_support_iff]
          intro h
          apply hm
          rw [hQ, h, mul_zero]
        have hmm : zdeg m = zdeg m0 := by
          by_contra hne'
          apply hm
          rw [hQ]
          refine mul_eq_zero_of_left (Finset.prod_eq_zero (i := zdeg m)
            (f := fun D : ℤ => (zdeg m : ℂ) - (D : ℂ))
            (Finset.mem_erase.2 ⟨hne', Finset.mem_image_of_mem _ hmP⟩) (sub_self (zdeg m : ℂ))) _
        rw [hmm]
    exact hne (by exact_mod_cast hkey Q hQW hQ0 _ hEQ)
  refine ⟨hκ, fun m hm t => ?_⟩
  have hcol : ∀ t, (∑ i, (m (z (i, t)) : ℤ)) - ∑ j, (m (y (j, t)) : ℤ) = κ t := by
    intro t
    have h1 : AddMonoidAlgebra.coeff (mixedOp ℂ z y t t P) m =
        (((∑ i, (m (z (i, t)) : ℤ)) - ∑ j, (m (y (j, t)) : ℤ) : ℤ) : ℂ) * AddMonoidAlgebra.coeff P m := by
      refine coeff_apply_of_diagonal_on_monomials' _
        (fun u => (((∑ i, (u (z (i, t)) : ℤ)) - ∑ j, (u (y (j, t)) : ℤ) : ℤ) : ℂ))
        (fun u => ?_) m P
      rw [mixedOp_apply, ← colOp_apply (K := ℂ) z t t, ← colOp_apply (K := ℂ) y t t,
        colOp_monomial, colOp_monomial, ← sub_smul]
      push_cast
      rfl
    rw [hwt t, coeff_smul, smul_eq_mul] at h1
    have hc : AddMonoidAlgebra.coeff P m ≠ 0 := mem_support_iff.1 hm
    exact_mod_cast (mul_right_cancel₀ hc h1).symm
  have hsum : ∑ t, (∑ i, (m (z (i, t)) : ℤ)) = ∑ t, max (κ t) 0 := by
    rw [Finset.sum_comm, ← hzdeg]
    exact hdeg m hm
  have hle : ∀ t ∈ (Finset.univ : Finset (Fin n)), max (κ t) 0 ≤ ∑ i, (m (z (i, t)) : ℤ) := by
    intro t _
    have h0 : 0 ≤ ∑ j, (m (y (j, t)) : ℤ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h0' : 0 ≤ ∑ i, (m (z (i, t)) : ℤ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h := hcol t
    exact max_le (by linarith) h0'
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm t (Finset.mem_univ t)
  have h := hcol t
  refine ⟨heq.symm, ?_⟩
  rcases le_total 0 (κ t) with hk | hk
  · rw [max_eq_left hk] at heq
    rw [max_eq_right (by linarith)]
    linarith
  · rw [max_eq_right hk] at heq
    rw [max_eq_left (by linarith)]
    linarith

end GlobalTheory.JointHarm.ColumnDegree
