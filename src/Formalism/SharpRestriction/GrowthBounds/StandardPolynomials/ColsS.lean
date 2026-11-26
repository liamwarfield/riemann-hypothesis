module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColDef
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SymbolEq
section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NotCostlyZero
section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.KGShift
noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.LemmaBAlt.B2

namespace Formalism.MainNotions.ColumnSystems.Pf.Col

section Hom

variable {σ R : Type} [CommRing R]

def HomG (φ : (σ →₀ ℕ) →+ ℕ) (d : ℕ) (P : MvPolynomial σ R) : Prop := ∀ m ∈ P.support, φ m = d

theorem HomG.zero (φ : (σ →₀ ℕ) →+ ℕ) (d : ℕ) : HomG φ d (0 : MvPolynomial σ R) := by
  intro m hm
  simp at hm

theorem HomG.add {φ : (σ →₀ ℕ) →+ ℕ} {d : ℕ} {P Q : MvPolynomial σ R} (hP : HomG φ d P) (hQ : HomG φ d Q) :
    HomG φ d (P + Q) := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hP m h
  · exact hQ m h

theorem HomG.sum {φ : (σ →₀ ℕ) →+ ℕ} {d : ℕ} {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ R)
    (h : ∀ i ∈ s, HomG φ d (P i)) : HomG φ d (∑ i ∈ s, P i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using HomG.zero (R := R) φ d) ?_
  intro i s hi ih h
  rw [Finset.sum_insert hi]
  exact HomG.add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem HomG.mul {φ : (σ →₀ ℕ) →+ ℕ} {d d' : ℕ} {P Q : MvPolynomial σ R} (hP : HomG φ d P) (hQ : HomG φ d' Q) :
    HomG φ (d + d') (P * Q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hm)
  rw [map_add (f := _), hP a ha, hQ b hb]

theorem HomG.one (φ : (σ →₀ ℕ) →+ ℕ) : HomG φ 0 (1 : MvPolynomial σ R) := by
  intro m hm
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply] at hm
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm), map_zero]

theorem HomG.sign {φ : (σ →₀ ℕ) →+ ℕ} {d : ℕ} {P : MvPolynomial σ R} (hP : HomG φ d P) (n : ℕ) :
    HomG φ d ((-1) ^ n * P) := by
  have hc : ((-1 : MvPolynomial σ R) ^ n) = MvPolynomial.C ((-1 : R) ^ n) := by simp
  intro m hm
  apply hP m
  rw [hc, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)

theorem KG_hom {n : ℕ} (φ : (σ →₀ ℕ) →+ ℕ) (c : ℤ) (hs : ℕ → ℕ) (x : ℕ → Fin n → MvPolynomial σ R) (ω : ℕ → ℕ)
    (hx : ∀ j b, HomG φ (ω j) (x j b)) :
    ∀ (t : ℕ) (J : Finset (Fin n)), HomG φ (∑ j ∈ range t, if hs j = hs (j + 1) then 0 else ω j) (KG c hs x t J)
  | 0, J => by
    show HomG φ _ (extOne J)
    unfold extOne
    split_ifs
    · simpa using HomG.one (R := R) φ
    · exact HomG.zero φ _
  | t + 1, J => by
    have ih := KG_hom φ c hs x ω hx t
    rw [Finset.sum_range_succ]
    by_cases h : hs t = hs (t + 1)
    · rw [KG_eq h, if_pos h, add_zero]; exact ih J
    · rw [if_neg h]
      show HomG φ _ (colStep c (hs t) (hs (t + 1)) (x t) (KG c hs x t) J)
      unfold colStep wedgeR contrR
      split_ifs
      all_goals first
        | omega
        | exact HomG.sum _ _ fun m _ => by
            rw [mul_assoc, add_comm]; exact ((hx t m).mul (ih _)).sign _

end Hom

section Shift

variable {n : ℕ} {P : Type} [CommRing P]

theorem KG_shift (c : ℤ) (hs : ℕ → ℕ) (x : ℕ → Fin n → P) (h0 : hs 0 = hs 1) :
    ∀ t, KG c hs x (t + 1) = KG c (fun j => hs (j + 1)) (fun j => x (j + 1)) t
  | 0 => by rw [KG_eq h0]; rfl
  | t + 1 => by
    show colStep c (hs (t + 1)) (hs (t + 1 + 1)) (x (t + 1)) (KG c hs x (t + 1)) =
      colStep c (hs (t + 1)) (hs (t + 1 + 1)) (x (t + 1)) (KG c (fun j => hs (j + 1)) (fun j => x (j + 1)) t)
    rw [KG_shift c hs x h0 t]

theorem KG_congr (c : ℤ) {hs hs' : ℕ → ℕ} {x x' : ℕ → Fin n → P} :
    ∀ t, (∀ j, j ≤ t → hs j = hs' j) → (∀ j, j < t → x j = x' j) → KG c hs x t = KG c hs' x' t
  | 0, _, _ => rfl
  | t + 1, h1, h2 => by
    show colStep c (hs t) (hs (t + 1)) (x t) (KG c hs x t) = colStep c (hs' t) (hs' (t + 1)) (x' t) (KG c hs' x' t)
    rw [KG_congr c t (fun j hj => h1 j (by omega)) (fun j hj => h2 j (by omega)), h1 t (by omega), h1 (t + 1) le_rfl,
      h2 t (by omega)]

theorem KG_one (c : ℤ) (ν : ℕ → ℤ) (h0 : ν 0 = 0) (hm : ∀ t, ν t ≤ ν (t + 1)) (hs : ℕ → ℕ)
    (hhs : ∀ t, hs t = if c ≤ ν t then 1 else 0) (x : ℕ → Fin 1 → P) :
    ∀ t, KG c hs x t (if 1 ≤ c ∧ c ≤ ν t then {0} else ∅) = ∏ i ∈ range t, if ν i < c ∧ c ≤ ν (i + 1) then x i 0 else 1
  | 0 => by
    have : ¬ (1 ≤ c ∧ c ≤ ν 0) := by rw [h0]; omega
    rw [if_neg this]
    show extOne ∅ = _
    simp [extOne]
  | t + 1 => by
    have ih := KG_one c ν h0 hm hs hhs x t
    have hnn : ∀ t, 0 ≤ ν t := by
      intro t
      induction t with
      | zero => rw [h0]
      | succ t iht => exact le_trans iht (hm t)
    rw [Finset.prod_range_succ, ← ih]
    by_cases h1 : c ≤ ν t
    · have h2 : c ≤ ν (t + 1) := le_trans h1 (hm t)
      have e : hs t = hs (t + 1) := by rw [hhs, hhs, if_pos h1, if_pos h2]
      have hn : ¬ (ν t < c ∧ c ≤ ν (t + 1)) := by omega
      rw [KG_eq e, if_neg hn, mul_one]
      by_cases hc : 1 ≤ c
      · rw [if_pos ⟨hc, h2⟩, if_pos ⟨hc, h1⟩]
      · rw [if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]
    · by_cases h2 : c ≤ ν (t + 1)
      · have hc : 1 ≤ c := by have := hnn t; omega
        have e : hs t < hs (t + 1) := by rw [hhs, hhs, if_neg h1, if_pos h2]; omega
        have hp1 : 1 ≤ c ∧ c ≤ ν (t + 1) := ⟨hc, h2⟩
        have hn2 : ¬ (1 ≤ c ∧ c ≤ ν t) := fun h => h1 h.2
        have hp3 : ν t < c ∧ c ≤ ν (t + 1) := ⟨by omega, h2⟩
        rw [KG_rise_pos hc e, if_pos hp1, if_neg hn2, if_pos hp3]
        unfold wedgeR
        simp [mul_comm, Finset.filter_singleton]
      · have e : hs t = hs (t + 1) := by rw [hhs, hhs, if_neg h1, if_neg h2]
        have hn : ¬ (ν t < c ∧ c ≤ ν (t + 1)) := fun h => h2 h.2
        have hn1 : ¬ (1 ≤ c ∧ c ≤ ν (t + 1)) := fun h => h2 h.2
        have hn2 : ¬ (1 ≤ c ∧ c ≤ ν t) := fun h => h1 h.2
        rw [KG_eq e, if_neg hn, if_neg hn1, if_neg hn2, mul_one]

end Shift

end Formalism.MainNotions.ColumnSystems.Pf.Col
end
end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.LemmaBAlt.B2

namespace Formalism.MainNotions.ColumnSystems.Pf.Col

variable {N K : ℕ}

def kaS (ka : Fin (N + 1) → Fin K → ℤ) : Fin (N + 1 + 1) → Fin K → ℤ := Fin.cons 0 ka

def muP (nu : ℕ → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) : Fin (N + 1 + 1) → Fin (1 + K) → ℤ :=
  joinPT (fun t _ => nu t.val) (kaS ka)

structure PH (vecc : Fin N → Bool) (B : Fin N → ℕ) (ka : Fin (N + 1) → Fin K → ℤ) (nu : ℕ → ℤ) : Prop where
  ka0 : ka 0 = 0
  kadom : ∀ i, Dominant (ka i)
  kastep : ∀ i : Fin N, if vecc i then HStrip (ka i.castSucc) (ka i.succ) (B i) else HStrip (ka i.succ) (ka i.castSucc) (B i)
  nu0 : nu 0 = 0
  numono : ∀ t, nu t ≤ nu (t + 1)
  nucov : ∀ i : Fin N, vecc i = false → nu (i.val + 2) = nu (i.val + 1)
  C : ∀ i : Fin N, vecc i = true → ∀ b, ka i.succ b ≤ nu (i.val + 1)
  hK : N < K

theorem colH_muP (nu : ℕ → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) (t : Fin (N + 1 + 1)) (c : ℤ) :
    colH (muP nu ka t) c = (if c ≤ nu t.val then 1 else 0) + colH (kaS ka t) c := by
  simp only [colH, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp [muP, joinPT]

theorem colH_zero (c : ℤ) : colH (0 : Fin K → ℤ) c = if c ≤ 0 then K else 0 := by
  unfold colH
  split_ifs with hc <;> simp [hc]

theorem H0 (nu : ℕ → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) (c : ℤ) :
    colH (muP nu ka 0) c = (if c ≤ nu 0 then 1 else 0) + (if c ≤ 0 then K else 0) := by
  rw [colH_muP, Fin.val_zero]
  congr 1
  simp only [kaS, Fin.cons_zero]
  exact colH_zero c

theorem HS (nu : ℕ → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) (i : Fin (N + 1)) (c : ℤ) :
    colH (muP nu ka i.succ) c = (if c ≤ nu (i.val + 1) then 1 else 0) + colH (ka i) c := by
  rw [colH_muP]; rfl

variable {vecc : Fin N → Bool} {B : Fin N → ℕ} {ka : Fin (N + 1) → Fin K → ℤ} {nu : ℕ → ℤ}

theorem PH.nonneg (h : PH vecc B ka nu) : ∀ t, 0 ≤ nu t := by
  intro t
  induction t with
  | zero => exact h.nu0.ge
  | succ t ih => exact ih.trans (h.numono t)

theorem PH.ka_le (h : PH vecc B ka nu) : ∀ (i : Fin (N + 1)) (b : Fin K), ka i b ≤ nu (i.val + 1) := by
  intro i
  induction i using Fin.induction with
  | zero =>
    intro b
    simpa [h.ka0] using h.nonneg 1
  | succ j ih =>
    intro b
    have hs := h.kastep j
    by_cases hv : vecc j = true
    · have h1 : ka j.succ b ≤ nu (j.val + 1) := h.C j hv b
      have h2 : nu (j.val + 1) ≤ nu (j.val + 1 + 1) := h.numono _
      exact h1.trans h2
    · rw [if_neg hv] at hs
      have h1 : ka j.succ b ≤ ka j.castSucc b := hs.1 b
      have h2 : ka j.castSucc b ≤ nu (j.val + 1) := ih b
      have h3 : nu (j.val + 1) ≤ nu (j.val + 1 + 1) := h.numono _
      exact h1.trans (h2.trans h3)

theorem pos_of_colH {n : ℕ} {mu : Fin n → ℤ} {c : ℤ} (h : 1 ≤ colH mu c) : ∃ b, c ≤ mu b := by
  unfold colH at h
  obtain ⟨b, hb⟩ := Finset.card_pos.1 h
  exact ⟨b, (Finset.mem_filter.1 hb).2⟩

theorem PH.pos_le (h : PH vecc B ka nu) (i : Fin (N + 1)) {c : ℤ} (hc : 1 ≤ colH (ka i) c) : c ≤ nu (i.val + 1) := by
  obtain ⟨b, hb⟩ := pos_of_colH hc
  exact hb.trans (h.ka_le i b)

private theorem colH_le_le_add_one_of_HStrip {n : ℕ} {a b : Fin n → ℤ} {m : ℕ} (hs : HStrip a b m) (c : ℤ) :
    colH a c ≤ colH b c ∧ colH b c ≤ colH a c + 1 := by
  obtain ⟨h1, h2, -⟩ := hs
  unfold colH
  constructor
  · exact Finset.card_le_card fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.trans (h1 x)
  · have hsplit : (Finset.univ.filter fun x : Fin n => c ≤ b x) ⊆
        (Finset.univ.filter fun x : Fin n => x.val = 0) ∪
          (Finset.univ.filter fun x : Fin n => 0 < x.val ∧ c ≤ b x) := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      by_cases hx0 : x.val = 0
      · exact Or.inl hx0
      · exact Or.inr ⟨Nat.pos_of_ne_zero hx0, hx⟩
    have hz : (Finset.univ.filter fun x : Fin n => x.val = 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact Fin.ext (hx.trans hy.symm)
    have hinj : (Finset.univ.filter fun x : Fin n => 0 < x.val ∧ c ≤ b x).card ≤
        (Finset.univ.filter fun x : Fin n => c ≤ a x).card := by
      refine Finset.card_le_card_of_injOn
        (fun x => ⟨x.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩) ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        have hlt : x.val - 1 + 1 < n := by have := x.isLt; omega
        have hb := h2 ⟨x.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩ hlt
        have e : (⟨x.val - 1 + 1, hlt⟩ : Fin n) = x := Fin.ext (by simp only; omega)
        rw [e] at hb
        exact hx.2.trans hb
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        have := congrArg Fin.val hxy
        simp only at this
        exact Fin.ext (by omega)
    calc _ ≤ _ := Finset.card_le_card hsplit
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ _ := by omega

theorem PH.stepV (h : PH vecc B ka nu) (i : Fin N) (hv : vecc i = true) (c : ℤ) :
    colH (ka i.castSucc) c ≤ colH (ka i.succ) c ∧ colH (ka i.succ) c ≤ colH (ka i.castSucc) c + 1 ∧
      (colH (ka i.castSucc) c < colH (ka i.succ) c → c ≤ nu (i.val + 1)) := by
  have hs := h.kastep i
  rw [if_pos hv] at hs
  obtain ⟨s1, s2⟩ := colH_le_le_add_one_of_HStrip hs c
  refine ⟨s1, s2, fun hlt => ?_⟩
  obtain ⟨b, hb⟩ := pos_of_colH (c := c) (mu := ka i.succ) (by omega)
  exact hb.trans (h.C i hv b)

theorem PH.stepC (h : PH vecc B ka nu) (i : Fin N) (hv : vecc i = false) (c : ℤ) :
    colH (ka i.succ) c ≤ colH (ka i.castSucc) c ∧ colH (ka i.castSucc) c ≤ colH (ka i.succ) c + 1 := by
  have hs := h.kastep i
  rw [if_neg (by simp [hv])] at hs
  exact colH_le_le_add_one_of_HStrip hs c

theorem PH.dualLow (h : PH vecc B ka nu) {c : ℤ} (hc : c ≤ 0) : ∀ i : Fin (N + 1), K ≤ colH (ka i) c + i.val := by
  intro i
  induction i using Fin.induction with
  | zero => rw [h.ka0, colH_zero, if_pos hc]; simp
  | succ i ih =>
    simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
    by_cases hv : vecc i = true
    · have := (h.stepV i hv c).1; omega
    · have := (h.stepC i (by simpa using hv) c).2; omega

theorem PH.dual1 (h : PH vecc B ka nu) {c : ℤ} (hc : c ≤ 0) (i : Fin (N + 1)) : 1 ≤ colH (ka i) c := by
  have h1 := h.dualLow hc i
  have h2 := i.isLt
  have h3 := h.hK
  omega

theorem PH.heights (_h : PH vecc B ka nu) (i : Fin N) (c : ℤ) :
    colH (muP nu ka i.succ.castSucc) c = (if c ≤ nu (i.val + 1) then 1 else 0) + colH (ka i.castSucc) c ∧
    colH (muP nu ka i.succ.succ) c = (if c ≤ nu (i.val + 2) then 1 else 0) + colH (ka i.succ) c := by
  refine ⟨?_, ?_⟩
  · rw [← Fin.succ_castSucc]
    exact HS nu ka i.castSucc c
  · exact HS nu ka i.succ c

theorem PH.heights0 (h : PH vecc B ka nu) (c : ℤ) :
    colH (muP nu ka (0 : Fin (N + 1)).castSucc) c = (if c ≤ 0 then 1 else 0) + (if c ≤ 0 then K else 0) ∧
    colH (muP nu ka (0 : Fin (N + 1)).succ) c = (if c ≤ nu 1 then 1 else 0) + (if c ≤ 0 then K else 0) := by
  refine ⟨?_, ?_⟩
  · have e := H0 nu ka c
    rw [h.nu0] at e
    simpa using e
  · rw [HS, h.ka0, colH_zero]
    try simp

theorem PH.not_costly_zero (h : PH vecc B ka nu) (c : ℤ) : ¬ IsCostly (muP nu ka) c 0 := by
  unfold IsCostly
  obtain ⟨h1, h2⟩ := h.heights0 c
  rw [h1, h2]
  have := h.nonneg 1
  have := h.hK
  split_ifs <;> omega

theorem PH.costly_succ (h : PH vecc B ka nu) (i : Fin N) (c : ℤ) :
    IsCostly (muP nu ka) c i.succ ↔ colH (ka i.castSucc) c < colH (ka i.succ) c := by
  obtain ⟨e1, e2⟩ := h.heights i c
  have hm : nu (i.val + 1) ≤ nu (i.val + 2) := h.numono _
  have p1 : 1 ≤ colH (ka i.castSucc) c → c ≤ nu (i.val + 1) := fun hc => h.pos_le i.castSucc hc
  unfold IsCostly
  rw [e1, e2]
  cases hv : vecc i
  · have hc := h.nucov i hv
    have := h.stepC i hv c
    rw [hc]
    by_cases hx : 1 ≤ colH (ka i.castSucc) c
    · have := p1 hx
      split_ifs <;> omega
    · split_ifs <;> omega
  · obtain ⟨s1, s2, s3⟩ := h.stepV i hv c
    by_cases hlt : colH (ka i.castSucc) c < colH (ka i.succ) c
    · have := s3 hlt
      split_ifs <;> omega
    · by_cases hx : 1 ≤ colH (ka i.castSucc) c
      · have := p1 hx
        split_ifs <;> omega
      · split_ifs <;> omega

theorem PH.oc_eq (h : PH vecc B ka nu) (om : Fin (N + 1) → ℕ) (c : ℤ) :
    oc om (muP nu ka) c = ∑ i : Fin N, if colH (ka i.castSucc) c < colH (ka i.succ) c then om i.succ else 0 := by
  classical
  unfold oc
  rw [Fin.sum_univ_succ, if_neg (h.not_costly_zero c), zero_add]
  exact Finset.sum_congr rfl fun i _ => if_congr (h.costly_succ i c) rfl rfl

theorem PH.dom (h : PH vecc B ka nu) (t : Fin (N + 1 + 1)) : Dominant (muP nu ka t) := by
  have hv : Antitone (kaS ka t) := by
    induction t using Fin.cases with
    | zero =>
      simp only [kaS, Fin.cons_zero]
      exact fun _ _ _ => le_rfl
    | succ i =>
      simp only [kaS, Fin.cons_succ]
      exact h.kadom i
  have hb : ∀ b, kaS ka t b ≤ nu t.val := by
    induction t using Fin.cases with
    | zero =>
      intro b
      simp [kaS, h.nu0]
    | succ i =>
      intro b
      simp only [kaS, Fin.cons_succ, Fin.val_succ]
      exact h.ka_le i b
  unfold Dominant
  intro a b hab
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j => simp [muP, joinPT]
    | right j =>
      simp only [muP, joinPT, Fin.append_left, Fin.append_right]
      exact hb j
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      exfalso
      rw [Fin.le_def] at hab
      simp only [Fin.coe_natAdd, Fin.coe_castAdd] at hab
      have := j.isLt
      omega
    | right j =>
      simp only [muP, joinPT, Fin.append_right]
      apply hv
      rw [Fin.le_def] at hab ⊢
      simp only [Fin.coe_natAdd] at hab
      omega

private theorem colH_muP_succ_ne_castSucc_iff_vec (h : PH vecc B ka nu) (LL : LiftLetters (Fin (N + 1))) (hv0 : LL.vec 0 = true)
    (hvs : ∀ i : Fin N, LL.vec i.succ = vecc i) (c : ℤ) (i : Fin (N + 1)) :
    (colH (muP nu ka i.castSucc) c < colH (muP nu ka i.succ) c →
      LL.vec i = true ∧ colH (muP nu ka i.succ) c = colH (muP nu ka i.castSucc) c + 1) ∧
    (colH (muP nu ka i.succ) c < colH (muP nu ka i.castSucc) c →
      LL.vec i = false ∧ colH (muP nu ka i.castSucc) c = colH (muP nu ka i.succ) c + 1) := by
  induction i using Fin.cases with
  | zero =>
    obtain ⟨e1, e2⟩ := h.heights0 c
    have := h.nonneg 1
    rw [e1, e2, hv0]
    refine ⟨fun hlt => ⟨rfl, ?_⟩, fun hlt => ?_⟩
    · split_ifs at hlt ⊢ <;> omega
    · exfalso
      split_ifs at hlt <;> omega
  | succ k =>
    obtain ⟨e1, e2⟩ := h.heights k c
    have hm : nu (k.val + 1) ≤ nu (k.val + 2) := h.numono _
    have p1 : 1 ≤ colH (ka k.castSucc) c → c ≤ nu (k.val + 1) := fun hc => h.pos_le k.castSucc hc
    rw [e1, e2, hvs]
    cases hv : vecc k
    · have hc := h.nucov k hv
      have := h.stepC k hv c
      rw [hc]
      refine ⟨fun hlt => ?_, fun hlt => ⟨rfl, ?_⟩⟩
      · exfalso
        split_ifs at hlt <;> omega
      · split_ifs at hlt ⊢ <;> omega
    · obtain ⟨s1, s2, s3⟩ := h.stepV k hv c
      refine ⟨fun hlt => ⟨rfl, ?_⟩, fun hlt => ?_⟩
      · by_cases hx : colH (ka k.castSucc) c < colH (ka k.succ) c
        · have := s3 hx
          split_ifs at hlt ⊢ <;> omega
        · split_ifs at hlt ⊢ <;> omega
      · exfalso
        split_ifs at hlt <;> omega

private theorem one_lt_colH_muP_of_PH_of_lt_one (h : PH vecc B ka nu) {c : ℤ} (hc : ¬ 1 ≤ c) (t : Fin (N + 1 + 1)) :
    1 < colH (muP nu ka t) c := by
  induction t using Fin.cases with
  | zero =>
    rw [H0, h.nu0]
    have := h.hK
    split_ifs <;> omega
  | succ i =>
    rw [HS]
    have h1 := h.nonneg (i.val + 1)
    have h2 := h.dual1 (c := c) (by omega) i
    split_ifs <;> omega

theorem PH.colOK (h : PH vecc B ka nu) (LL : LiftLetters (Fin (N + 1))) (hv0 : LL.vec 0 = true)
    (hvs : ∀ i : Fin N, LL.vec i.succ = vecc i) (c : ℤ) : ColOK LL (muP nu ka) c := by
  refine ⟨fun j hj hlt => (colH_muP_succ_ne_castSucc_iff_vec h LL hv0 hvs c ⟨j, hj⟩).1 hlt,
    fun j hj hlt => (colH_muP_succ_ne_castSucc_iff_vec h LL hv0 hvs c ⟨j, hj⟩).2 hlt, fun hc => ?_,
    fun hc j hj => one_lt_colH_muP_of_PH_of_lt_one h hc ⟨j, by omega⟩⟩
  have e := H0 nu ka c
  rw [h.nu0] at e
  have e0 : (⟨0, by omega⟩ : Fin (N + 1 + 1)) = 0 := Fin.ext (by simp)
  rw [e0, e]
  split_ifs <;> omega

theorem PH.posc (h : PH vecc B ka nu) (LL : LiftLetters (Fin (N + 1))) (hvs : ∀ i : Fin N, LL.vec i.succ = vecc i)
    (hpos : ∀ i i' : Fin (N + 1), i < i' → LL.vec i' = true → LL.pos i < LL.pos i') (c : ℤ) :
    ∀ i i' : Fin (N + 1), i < i' → IsUsed (muP nu ka) c i → IsCostly (muP nu ka) c i' → LL.pos i < LL.pos i' := by
  intro i i' hii' _ hc
  apply hpos i i' hii'
  induction i' using Fin.cases with
  | zero => exact absurd hc (h.not_costly_zero c)
  | succ k =>
    rw [hvs]
    rw [h.costly_succ] at hc
    cases hv : vecc k
    · have := (h.stepC k hv c).1
      exfalso
      omega
    · rfl

end Formalism.MainNotions.ColumnSystems.Pf.Col
end
end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.LemmaBAlt.B2

namespace Formalism.MainNotions.ColumnSystems.Pf.Col

variable {N K : ℕ} {vecc : Fin N → Bool} {B : Fin N → ℕ} {ka : Fin (N + 1) → Fin K → ℤ} {nu : ℕ → ℤ}

def Jc (nu : ℕ → ℤ) (N : ℕ) (c : ℤ) (I'' : Finset (Fin K)) : Finset (Fin (1 + K)) :=
  joinI (fun _ => if 1 ≤ c ∧ c ≤ nu (N + 1) then ({0} : Finset (Fin 1)) else ∅) (fun _ => I'') c

theorem colH_one (a c : ℤ) : colH (fun _ : Fin 1 => a) c = if c ≤ a then 1 else 0 := by
  unfold colH
  split_ifs with h
  · rw [Finset.filter_true_of_mem (fun m _ => h)]; simp
  · rw [Finset.filter_false_of_mem (fun m _ => h)]; simp

theorem hsOf_kaS (ka : Fin (N + 1) → Fin K → ℤ) (c : ℤ) (j : ℕ) : hsOf (kaS ka) c (j + 1) = hsOf ka c j := by
  unfold hsOf
  have : (⟨min (j + 1) (N + 1), by omega⟩ : Fin (N + 1 + 1)) = Fin.succ ⟨min j N, by omega⟩ :=
    Fin.ext (by simp [Nat.succ_min_succ])
  rw [this]; rfl

theorem symbol_eq (h : PH vecc B ka nu) (R : Type) [CommRing R] {P : Type} [CommRing P]
    (Ψ : MvPolynomial (Fin (N + 1) × Fin (1 + K)) R →+* P) (c : ℤ) (I'' : Finset (Fin K)) :
    Ψ (plTanCol R (muP nu ka) c (Jc nu N c I'')) =
      (∏ t ∈ range (N + 1), if nu t < c ∧ c ≤ nu (t + 1) then Ψ (xOf R (N + 1) (1 + K) t (Fin.castAdd K 0)) else 1) *
        KG c (hsOf ka c) (fun a b => Ψ (xOf R (N + 1) (1 + K) (a + 1) (Fin.natAdd 1 b))) N I'' := by
  unfold plTanCol Jc
  rw [joinI_pl, joinI_tan, map_mul]
  have hpl : plPart (muP nu ka) = fun t _ => nu t.val := by
    funext t a; simp [plPart, muP, joinPT]
  have htan : tanPart (muP nu ka) = kaS ka := tanPart_join _ _
  rw [hpl, htan]
  congr 1
  ·
    rw [Kcol_eq_KG R (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c (N + 1) le_rfl]
    have e1 := map_KG (Ψ.comp (rename (plVar (N := N + 1) (r := 1) (K := K))).toRingHom) c
      (hsOf (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c) (xOf R (N + 1) 1) (N + 1)
      (if 1 ≤ c ∧ c ≤ nu (N + 1) then ({0} : Finset (Fin 1)) else ∅)
    have e1' : Ψ (rename (plVar (N := N + 1) (r := 1) (K := K)) (KG c
        (hsOf (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c) (xOf R (N + 1) 1) (N + 1)
        (if 1 ≤ c ∧ c ≤ nu (N + 1) then ({0} : Finset (Fin 1)) else ∅))) = _ := e1
    rw [e1']
    have e2 := KG_one (P := P) c (fun t => nu (min t (N + 1))) (by simpa using h.nu0)
      (fun t => by
        rcases Nat.lt_or_ge t (N + 1) with ht | ht
        · rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]; exact h.numono t
        · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)])
      (hsOf (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c)
      (fun t => by unfold hsOf; exact colH_one _ _)
      (fun j m => (Ψ.comp (rename (plVar (N := N + 1) (r := 1) (K := K))).toRingHom) (xOf R (N + 1) 1 j m)) (N + 1)
    simp only [Nat.min_self] at e2
    rw [e2]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' : t < N + 1 := Finset.mem_range.1 ht
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    congr 1
    simp [xOf, ht', plVar]
  ·
    rw [Kcol_eq_KG R (kaS ka) c (N + 1) le_rfl]
    have e1 := map_KG (Ψ.comp (rename (tanVar (N := N + 1) (r := 1) (K := K))).toRingHom) c
      (hsOf (kaS ka) c) (xOf R (N + 1) K) (N + 1) I''
    have e1' : Ψ (rename (tanVar (N := N + 1) (r := 1) (K := K)) (KG c (hsOf (kaS ka) c) (xOf R (N + 1) K) (N + 1) I'')) = _ := e1
    rw [e1']
    have h01 : hsOf (kaS ka) c 0 = hsOf (kaS ka) c 1 := by
      rw [hsOf_kaS]
      unfold hsOf
      show colH (0 : Fin K → ℤ) c = colH (ka ⟨min 0 N, by omega⟩) c
      have : (⟨min 0 N, by omega⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
      rw [this, h.ka0]
    rw [KG_shift c _ _ h01 N]
    have e3 := KG_congr (P := P) c (hs := fun j => hsOf (kaS ka) c (j + 1)) (hs' := hsOf ka c)
      (x := fun j => (fun m => (Ψ.comp (rename (tanVar (N := N + 1) (r := 1) (K := K))).toRingHom) (xOf R (N + 1) K (j + 1) m)))
      (x' := fun a b => Ψ (xOf R (N + 1) (1 + K) (a + 1) (Fin.natAdd 1 b))) N
      (fun j _ => hsOf_kaS ka c j)
      (fun j hj => by
        funext m
        have : j + 1 < N + 1 := by omega
        simp [xOf, this, tanVar])
    rw [e3]

end Formalism.MainNotions.ColumnSystems.Pf.Col
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.ColumnSystems.Pf.Col

section

variable (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT))

def zxS (l : Fin (segS X.TT j)) : ℕ :=
  coarseA X.p (X.seg C0 CE1 CE2 j) (β j) l -
    (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w l else (β j).o l)

def a0Z : ℤ :=
  ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - mu⌋ -
    ∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg l : ℤ) else 0)

def nuS (T : ℕ) : ℤ :=
  if T = 0 then 0 else a0Z C0 CE1 CE2 mu X β j +
    ∑ l : Fin (segS X.TT j), (if 2 * (l : ℕ) + 2 ≤ T then (zxS C0 CE1 CE2 X β j l : ℤ) else 0)

end

def PS (X : Loc) (j : Fin (numSeg X.TT)) (t : Fin (2 * segS X.TT j + 1 + 1)) : ℕ := X.p ^ (zS X j - posS X j t).toNat

section

variable (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT))
  (ka : Fin (2 * segS X.TT j + 1 + 1) → Fin X.m → ℤ)

def colsS : Finset ℤ := colRange ka ∪ Finset.Icc 1 (nuS C0 CE1 CE2 mu X β j (2 * segS X.TT j + 1 + 1))

def plS (c : ℤ) : MonH X :=
  ∑ t : Fin (2 * segS X.TT j + 1 + 1),
    if nuS C0 CE1 CE2 mu X β j t.val < c ∧ c ≤ nuS C0 CE1 CE2 mu X β j (t.val + 1) then
      Finsupp.single (phiS X j (t, Fin.castAdd X.m 0)) (PS X j t) else 0

def dKS (c : ℤ) (i : Fin (2 * segS X.TT j + 1)) : ℕ := if colH (ka i.castSucc) c = colH (ka i.succ) c then 0 else 1

def oCS (c : ℤ) : ℕ := oc (PS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c

def dgCS (c : ℤ) (l : X.TT × Bool) : ℕ :=
  ∑ t : Fin (2 * segS X.TT j + 1 + 1), if lamS X j t = l then
    dgS X.p (posS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c (2 * segS X.TT j + 1 + 1) (zS X j) t else 0

def fCS [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (I'' : ℤ → Finset (Fin X.m)) (c : ℤ) :
    RHH O X :=
  rename (phiS X j) (KKc X.p X.n' (O := O) (LLseg X j) 1 (zS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c
    (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))

end

end Formalism.MainNotions.ColumnSystems.Pf
