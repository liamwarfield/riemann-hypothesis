module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BigCellCommuteFrameElement
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MulVecApplyOfRow
open Matrix

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def block (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∀ i j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) → g i j = if i = j then 1 else 0) ∧
  (∀ i j : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → g i j = if i = j then 1 else 0)

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem isUnit_of_uh {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * gᴴ * Hpk k r)
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem uh_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hu := isUnit_of_uh hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem col_of_fix {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {c : Fin (2 * r + k + 1)} (hc : h *ᵥ bvec c = bvec c) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  have := congrFun hc p
  simp only [bvec, Matrix.mulVec, dotProduct_single, mul_one, Pi.single_apply] at this
  exact this

theorem row_of_fixed_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : h ∈ UH (Hpk k r)) (c : Fin (2 * r + k + 1))
    (hc : ∀ p, h p c = if p = c then 1 else 0) (j : Fin (2 * r + k + 1)) :
    h (tau k r c) j = if tau k r c = j then 1 else 0 := by
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have e := congrFun (congrFun hU' c) j
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single c] at e
  · rw [conjTranspose_apply, hc c, if_pos rfl, star_one, one_mul, hpk_mul_apply, hpk_row] at e
    have hs : sgn k r c ≠ 0 := by
      intro h0
      have := sgn_mul_self (k := k) (r := r) c
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    by_cases hj : j = tau k r c
    · rw [if_pos hj] at e
      rw [if_pos hj.symm]
      exact mul_left_cancel₀ hs (e.trans (mul_one _).symm)
    · rw [if_neg hj] at e
      rw [if_neg (Ne.symm hj)]
      exact (mul_eq_zero.1 e).resolve_left hs
  · intro p _ hp
    rw [conjTranspose_apply, hc p, if_neg hp, star_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem uw_fixed_col {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (c : Fin (2 * r + k + 1)) (hc : c.val < r ∨ r + k < c.val) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  by_cases hcr : c.val < r
  · have e : eI k r ⟨c.val, hcr⟩ = c := Fin.ext rfl
    have := (hh.2.1 ⟨c.val, hcr⟩).1
    rw [e] at this
    exact col_of_fix this p
  · have ha : 2 * r + k - c.val < r := by omega
    have e : esI k r ⟨2 * r + k - c.val, ha⟩ = c := by
      apply Fin.ext
      simp only [esI]
      omega
    have := (hh.2.1 ⟨2 * r + k - c.val, ha⟩).2
    rw [e] at this
    exact col_of_fix this p

theorem tau_out (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (tau k r i).val < r ∨ r + k < (tau k r i).val := by
  unfold tau
  simp only
  split_ifs
  omega

theorem uw_block {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    block k r h := by
  refine ⟨fun i j hj => uw_fixed_col hh j hj i, fun i j hi => ?_⟩
  have := row_of_fixed_col hh.1 (tau k r i) (uw_fixed_col hh _ (tau_out i hi)) j
  rw [tau_tau] at this
  exact this

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  have hu := isUnit_of_uh hh.1
  have fix : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨uh_inv hh.1, fun a => ⟨fix _ (hh.2.1 a).1, fix _ (hh.2.1 a).2⟩, fix _ hh.2.2⟩

theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ}
    {h h' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hh' : h' ∈ UWset k r z) : h * h' ∈ UWset k r z := by
  refine ⟨uh_mul hh.1 hh'.1, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hh'.2.1 a).1, (hh.2.1 a).1]
  · rw [← Matrix.mulVec_mulVec, (hh'.2.1 a).2, (hh.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, hh'.2.2, hh.2.2]

theorem mul_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h * M) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hrow, if_pos rfl, one_mul]
  · intro p _ hp
    rw [hrow, if_neg (Ne.symm hp), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mul_apply_of_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hcol : ∀ q, h q j = if q = j then 1 else 0) : (M * h) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hcol, if_pos rfl, mul_one]
  · intro q _ hq
    rw [hcol, if_neg hq, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mulVec_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h *ᵥ v) i = v i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [hrow, if_pos rfl, one_mul]
  · intro p _ hp
    rw [hrow, if_neg (Ne.symm hp), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem ell_conj (z : Fin (2 * r + k + 1) → ℂ)
    {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) :
    ell k r z (h * g * h') = ell k r z g := by
  unfold ell
  apply Finset.sum_congr rfl
  intro a _
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 _ p (by simp only [eI]; omega)
  by_cases ha : a.val + 1 < r
  · rw [dite_eq_left ha, dite_eq_left ha, mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (by simp only [eI]; omega)),
      mul_apply_of_row _ _ _ hrow]
  · rw [dite_eq_right ha, dite_eq_right ha, ← Matrix.mulVec_mulVec, hz, ← Matrix.mulVec_mulVec,
      mulVec_apply_of_row _ _ hrow]

abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : Fin (k + 1) := ⟨i.val - r, by have := hi; omega⟩

lemma wI_midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : wI k r (midx hi) = i := by
  have := hi
  apply Fin.ext
  simp only [wI, midx]
  omega

lemma mid_wI (m : Fin (k + 1)) : mid k r (wI k r m) := by
  have := m.isLt
  constructor <;> simp only [wI] <;> omega

lemma wI_inj {a b : Fin (k + 1)} (h : wI k r a = wI k r b) : a = b := by
  have := congrArg Fin.val h
  simp only [wI] at this
  apply Fin.ext; omega

lemma emb_out_col (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dite_eq_right (fun h => hj h.2)]
  by_cases h : q = j
  · subst h; rw [if_pos ⟨rfl, hj⟩, if_pos rfl]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma emb_out_row (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : ¬ mid k r q) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dite_eq_right (fun h => hq h.1)]
  by_cases h : q = j
  · rw [if_pos ⟨h, hq⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : mid k r q) (hj : mid k r j) :
    embWb k r μ q j = μ (midx hq) (midx hj) := by
  unfold embWb
  rw [dite_eq_left ⟨hq, hj⟩]
  rfl

def Em (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (k + 1)) ℂ := fun i m => if i = wI k r m then 1 else 0

lemma Em_mul_mid {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : mid k r i) :
    (Em k r * A) i x = A (midx hi) x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hi)]
  · rw [Em, if_pos (wI_midx hi).symm, one_mul]
  · intro b _ hb
    rw [Em, if_neg, zero_mul]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hi, h]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma Em_mul_out {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : ¬ mid k r i) :
    (Em k r * A) i x = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Em, if_neg, zero_mul]
  intro h
  exact hi (h ▸ mid_wI b)

lemma mul_EmT_mid {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : mid k r j) :
    (A * (Em k r)ᵀ) x j = A x (midx hj) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hj)]
  · rw [Matrix.transpose_apply, Em, if_pos (wI_midx hj).symm, mul_one]
  · intro b _ hb
    rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hj, h]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma mul_EmT_out {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : ¬ mid k r j) :
    (A * (Em k r)ᵀ) x j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
  intro h
  exact hj (h ▸ mid_wI b)

lemma EmT_Em : (Em k r)ᵀ * Em k r = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (wI k r a)]
  · simp only [Matrix.transpose_apply, Em, if_true, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (fun h => hab (wI_inj h)), if_neg hab, mul_zero]
  · intro i _ hi
    simp only [Matrix.transpose_apply, Em]
    rw [if_neg hi (c := i = wI k r a), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma emb_eq (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r μ = Em k r * μ * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
  by_cases hj : mid k r j
  · rw [mul_EmT_mid _ j i hj, mul_EmT_mid _ j i hj]
    by_cases hi : mid k r i
    · rw [Em_mul_mid _ i _ hi, emb_mid μ i j hi hj]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero]
    · rw [Em_mul_out _ i _ hi, emb_out_row μ i j hi]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero, if_neg (fun h => hi (by rw [h]; exact hj))]
  · rw [mul_EmT_out _ j i hj, mul_EmT_out _ j i hj, emb_out_col μ i j hj]
    ring

lemma EmT_Q : (Em k r)ᵀ * (1 - Em k r * (Em k r)ᵀ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, EmT_Em, Matrix.one_mul, sub_self]

lemma Q_Em : (1 - Em k r * (Em k r)ᵀ) * Em k r = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, EmT_Em, Matrix.mul_one, sub_self]

lemma sandwich (a b N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (M : Mat k r)
    (h1 : M * Em k r = Em k r * N) (h2 : (Em k r)ᵀ * M = N * (Em k r)ᵀ) :
    embWb k r a * M * embWb k r b =
      Em k r * (a * N * b) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * M * (1 - Em k r * (Em k r)ᵀ) := by
  rw [emb_eq, emb_eq]
  set E := Em k r with hE
  set Q := 1 - E * Eᵀ with hQ
  have t1 : E * a * Eᵀ * M * (E * b * Eᵀ) = E * (a * N * b) * Eᵀ := by
    calc E * a * Eᵀ * M * (E * b * Eᵀ) = E * a * (Eᵀ * M) * E * b * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = E * a * N * (Eᵀ * E) * b * Eᵀ := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = E * (a * N * b) * Eᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have t2 : E * a * Eᵀ * M * Q = 0 := by
    calc E * a * Eᵀ * M * Q = E * a * (Eᵀ * M) * Q := by simp only [Matrix.mul_assoc]
      _ = E * a * N * (Eᵀ * Q) := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [EmT_Q, Matrix.mul_zero]
  have t3 : Q * M * (E * b * Eᵀ) = 0 := by
    calc Q * M * (E * b * Eᵀ) = Q * (M * E) * b * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = (Q * E) * N * b * Eᵀ := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Q_Em]; simp only [Matrix.zero_mul]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, add_zero, zero_add]

lemma emb_one : embWb k r 1 = 1 := by
  rw [emb_eq, Matrix.mul_one, add_sub_cancel]

lemma emb_mul (a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : embWb k r (a * b) = embWb k r a * embWb k r b := by
  have h := sandwich (r := r) a b 1 1 (by rw [Matrix.one_mul, Matrix.mul_one]) (by rw [Matrix.one_mul, Matrix.mul_one])
  rw [Matrix.mul_one] at h
  rw [h, emb_eq, Matrix.mul_one, Matrix.mul_one]
  congr 1
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Q_Em, Matrix.zero_mul, sub_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
end
end

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

lemma Hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

lemma unit_of_frame {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : γᴴ * Hb k * γ = Hb k) : IsUnit γ.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hb k * γᴴ * Hb k)
  calc Hb k * γᴴ * Hb k * γ = Hb k * (γᴴ * Hb k * γ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Hb_mul_self]

lemma emb_inv {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) :
    (embWb k r γ)⁻¹ = embWb k r γ⁻¹ :=
  Matrix.inv_eq_right_inv (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])

lemma emb_unit {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) : IsUnit (embWb k r γ).det :=
  Matrix.isUnit_det_of_right_inverse (B := embWb k r γ⁻¹) (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])

section gbar

variable (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det)
include hE

lemma gbar_mul (g h : Mat k r) : gbar k r γ (g * h) = gbar k r γ g * gbar k r γ h := by
  unfold gbar
  have e : (embWb k r γ)⁻¹ * (g * h) * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * h * embWb k r γ) := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE]
  rw [e, Matrix.map_mul]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE]

lemma gbar_one : gbar k r γ 1 = 1 := by
  unfold gbar
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hE, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hE]

lemma gbar_gbar (g : Mat k r) : gbar k r γ (gbar k r γ g) = g := by
  unfold gbar
  have h1 : (embWb k r γ)⁻¹ * (embWb k r γ * ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) *
      (embWb k r γ)⁻¹) * embWb k r γ = ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE, Matrix.nonsing_inv_mul _ hE,
      Matrix.mul_one]
  rw [h1]
  have h2 : (((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      (embWb k r γ)⁻¹ * g * embWb k r γ := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Complex.conj_conj]
  rw [h2]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE, Matrix.mul_nonsing_inv _ hE,
    Matrix.mul_one]

lemma gbar_mul_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x * gbar k r γ x⁻¹ = 1 := by
  rw [← gbar_mul γ hE, Matrix.mul_nonsing_inv _ hx, gbar_one γ hE]

lemma gbar_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x⁻¹ = (gbar k r γ x)⁻¹ :=
  (Matrix.inv_eq_right_inv (gbar_mul_inv γ hE hx)).symm

lemma gbar_unit {x : Mat k r} (hx : IsUnit x.det) : IsUnit (gbar k r γ x).det :=
  Matrix.isUnit_det_of_right_inverse (gbar_mul_inv γ hE hx)

lemma th_five {a b g c d : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (hg : th k r γ g = g) :
    th k r γ (a⁻¹ * b⁻¹ * g * c * d) =
      (gbar k r γ d)⁻¹ * (gbar k r γ c)⁻¹ * g * gbar k r γ b * gbar k r γ a := by
  unfold th at hg ⊢
  rw [gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_inv γ hE ha, gbar_inv γ hE hb]
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE ha),
    Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hb), hg, Matrix.mul_assoc]

lemma th_mul_inv {h h' : Mat k r} (hh' : IsUnit h'.det) :
    th k r γ (h * h'⁻¹) = gbar k r γ h' * (gbar k r γ h)⁻¹ := by
  unfold th
  rw [gbar_mul γ hE, gbar_inv γ hE hh', Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hh')]

end gbar

lemma psi_conj (z : Fin (2 * r + k + 1) → ℂ) {a : Mat k r} (ha : a ∈ UWset k r z) (c : ℂ) (n : Mat k r) :
    psi k r z c (a * n * a⁻¹) = psi k r z c n := by
  unfold psi
  rw [ell_conj z (uw_block ha) (uw_block (uw_inv ha)) (uw_inv ha).2.2]

lemma tau_wI (j : Fin (k + 1)) : tau k r (wI k r j) = wI k r j := by
  have := j.isLt
  unfold tau wI
  apply Fin.ext
  simp only
  split_ifs with h <;> omega

lemma mud_off (d : ℂ) (x y : Fin (k + 1)) (h : (x ≠ 0 ∧ x ≠ Fin.last k) ∨ (y ≠ 0 ∧ y ≠ Fin.last k)) :
    mud k d x y = if x = y then 1 else 0 := by
  unfold mud
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

lemma emb_mud_off (d : ℂ) (i j : Fin (2 * r + k + 1))
    (h : (i ≠ wI k r 0 ∧ i ≠ wI k r (Fin.last k)) ∨ (j ≠ wI k r 0 ∧ j ≠ wI k r (Fin.last k))) :
    embWb k r (mud k d) i j = if i = j then 1 else 0 := by
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · rw [emb_mid _ i j hi hj, mud_off]
      · by_cases e : i = j
        · subst e; simp
        · rw [if_neg e, if_neg (fun h' => e (by rw [← wI_midx hi, ← wI_midx hj, h']))]
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          exact ⟨fun h' => h1 (by rw [← wI_midx hi, h']), fun h' => h2 (by rw [← wI_midx hi, h'])⟩
        · right
          exact ⟨fun h' => h1 (by rw [← wI_midx hj, h']), fun h' => h2 (by rw [← wI_midx hj, h'])⟩
    · exact emb_out_col _ i j hj
  · exact emb_out_row _ i j hi

lemma comm_mud (hk : 1 ≤ k) {R : Mat k r} (hR : R ∈ UH (Hpk k r))
    (h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0)) (hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)))
    (d : ℂ) : R * embWb k r (mud k d) = embWb k r (mud k d) * R := by
  set a := wI k r 0
  set b := wI k r (Fin.last k)
  have hne : a ≠ b := fun h => by
    have := congrArg Fin.val (wI_inj h)
    simp at this
    omega
  have c0 := col_of_fix h0
  have cL := col_of_fix hL
  have r0 : ∀ j, R a j = if a = j then 1 else 0 := by
    intro j
    have := row_of_fixed_col hR a c0 j
    rwa [tau_wI] at this
  have rL : ∀ j, R b j = if b = j then 1 else 0 := by
    intro j
    have := row_of_fixed_col hR b cL j
    rwa [tau_wI] at this
  set P : Mat k r := embWb k r (mud k d) - 1 with hPdef
  have hM : embWb k r (mud k d) = 1 + P := by rw [hPdef]; abel
  have hP : ∀ i j, ((i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b)) → P i j = 0 := by
    intro i j h
    rw [hPdef, Matrix.sub_apply, emb_mud_off d i j h, Matrix.one_apply, sub_self]
  have RP : R * P = P := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP l j (Or.inl hl), mul_zero]),
      c0, cL]
    by_cases ha : i = a
    · subst ha; rw [if_pos rfl, if_neg hne, one_mul, zero_mul, add_zero]
    · by_cases hb : i = b
      · subst hb; rw [if_neg (Ne.symm hne), if_pos rfl, one_mul, zero_mul, zero_add]
      · rw [if_neg ha, if_neg hb, zero_mul, zero_mul, add_zero, hP i j (Or.inl ⟨ha, hb⟩)]
  have PR : P * R = P := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP i l (Or.inr hl), zero_mul]),
      r0, rL]
    by_cases ha : j = a
    · subst ha; rw [if_pos rfl, if_neg (Ne.symm hne), mul_one, mul_zero, add_zero]
    · by_cases hb : j = b
      · subst hb; rw [if_neg hne, if_pos rfl, mul_one, mul_zero, zero_add]
      · rw [if_neg (Ne.symm ha), if_neg (Ne.symm hb), mul_zero, mul_zero, add_zero, hP i j (Or.inr ⟨ha, hb⟩)]
  rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, RP, PR]

lemma big_cell_commute_frame_element (hBCF : BigCellFactor) (hUWb : UWbFacts) (hk : 1 ≤ k) {z : Fin (2 * r + k + 1) → ℂ}
    {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsZFrame k r z γ) {u : Mat k r} (hu : u ∈ UUset k r z γ)
    (c : Fin r → ℂ) (d : ℂ) : u * g0 k r γ c d = g0 k r γ c d * u := by
  have hγu := unit_of_frame hγ.1
  have hEu : IsUnit (embWb k r γ).det := emb_unit hγu
  have hEW : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
  have hEG : embWb k r γ ∈ UH (Hpk k r) := hEW.1
  have huW : u ∈ UWb k r := (hUWb k r).2.1 z hu.1
  set E := embWb k r γ with hEdef
  set R := E⁻¹ * u * E with hRdef
  have hR : R ∈ UH (Hpk k r) := uh_mul (uh_mul (uh_inv hEG) hu.1.1) hEG
  have fixR : ∀ v, E *ᵥ v = v → True := fun _ _ => trivial
  have h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0) := by
    rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change E⁻¹ *ᵥ (u *ᵥ w1 k r γ) = _
    rw [hu.2, w1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
  have hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)) := by
    rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.2, Matrix.mulVec_smul, hu.1.2.2, ← hγ.2,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
  have hRM := comm_mud hk hR h0 hL d
  have hu' : u = E * R * E⁻¹ := by
    rw [hRdef]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hEu, Matrix.mul_nonsing_inv _ hEu,
      Matrix.mul_one]
  have key : u * (E * embWb k r (mud k d) * E⁻¹) = E * embWb k r (mud k d) * E⁻¹ * u := by
    rw [hu']
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hEu]
    rw [← Matrix.mul_assoc R, hRM, Matrix.mul_assoc]
  unfold g0
  rw [(hBCF k r c _).1, emb_mul, emb_mul, ← emb_inv hγu]
  have hc := (hUWb k r).2.2 c u huW
  calc u * (bigCell k r c 1 * (E * embWb k r (mud k d) * E⁻¹))
      = bigCell k r c 1 * (u * (E * embWb k r (mud k d) * E⁻¹)) := by rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
    _ = bigCell k r c 1 * (E * embWb k r (mud k d) * E⁻¹) * u := by rw [key]; simp only [Matrix.mul_assoc]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
end
end

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

variable {k r : ℕ}

lemma cont_lmul (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply l))

def sandM (A B : Mat k r) (x : Mt k r) : Mt k r := A * Matrix.of x * B

lemma cont_sand (A B : Mat k r) : Continuous (sandM (k := k) (r := r) A B) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [sandM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun m _ => (continuous_finsetSum _ fun l _ =>
    continuous_const.mul ((continuous_apply m).comp (continuous_apply l))).mul continuous_const

def gb (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : Mt k r) : Mt k r := fun i j => gbar k r γ (Matrix.of x) i j

lemma cont_gb (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Continuous (gb (k := k) (r := r) γ) := by
  have h1 := cont_sand (k := k) (r := r) (embWb k r γ)⁻¹ (embWb k r γ)
  have h2 : Continuous (fun x : Mt k r => (fun i j => starRingEnd ℂ (sandM (embWb k r γ)⁻¹ (embWb k r γ) x i j) :
      Mt k r)) :=
    continuous_pi fun i => continuous_pi fun j =>
      Complex.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp h1))
  exact (cont_sand (k := k) (r := r) (embWb k r γ) (embWb k r γ)⁻¹).comp h2

def mEquiv {α : Type*} [MeasurableSpace α] (f g : α → α) (hf : Measurable f) (hg : Measurable g)
    (h1 : Function.LeftInverse g f) (h2 : Function.RightInverse g f) : α ≃ᵐ α :=
  { toFun := f, invFun := g, left_inv := h1, right_inv := h2, measurable_toFun := hf, measurable_invFun := hg }

lemma sfin {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

def Sab (a b : Mat k r) (p : SS k r) : SS k r :=
  ((lmulM a p.1.1, conjM a p.1.2), (lmulM b p.2.1, conjM b p.2.2))

lemma meas_Sab (a b : Mat k r) : Measurable (Sab (k := k) (r := r) a b) :=
  (((cont_lmul a).measurable.comp (measurable_fst.comp measurable_fst)).prodMk
    ((cont_sand a a⁻¹).measurable.comp (measurable_snd.comp measurable_fst))).prodMk
    (((cont_lmul b).measurable.comp (measurable_fst.comp measurable_snd)).prodMk
    ((cont_sand b b⁻¹).measurable.comp (measurable_snd.comp measurable_snd)))

lemma Sab_inv {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (p : SS k r) :
    Sab a⁻¹ b⁻¹ (Sab a b p) = p := by
  have l : ∀ c : Mat k r, IsUnit c.det → ∀ x : Mt k r, lmulM c⁻¹ (lmulM c x) = x := by
    intro c hc x
    exact Matrix.nonsing_inv_mul_cancel_left (A := c) (Matrix.of x) hc
  have m : ∀ c : Mat k r, IsUnit c.det → ∀ x : Mt k r, conjM c⁻¹ (conjM c x) = x := by
    intro c hc x
    show c⁻¹ * (c * Matrix.of x * c⁻¹) * c⁻¹⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hc]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hc, Matrix.nonsing_inv_mul _ hc,
      Matrix.mul_one]
  simp only [Sab, l a ha, l b hb, m a ha, m b hb]

lemma emb_Sab {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) : MeasurableEmbedding (Sab a b) := by
  have ha' : IsUnit a⁻¹.det := Matrix.isUnit_nonsing_inv_det _ ha
  have hb' : IsUnit b⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hb
  refine (mEquiv (Sab a b) (Sab a⁻¹ b⁻¹) (meas_Sab a b) (meas_Sab _ _) (Sab_inv ha hb) ?_).measurableEmbedding
  intro p
  have := Sab_inv ha' hb' p
  rwa [Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.nonsing_inv_nonsing_inv _ hb] at this

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

lemma mp_Sab (D : RealPlaceData k r Wp Wq) (hCI : ConjInv D) {a b : Mat k r} (ha : a ∈ UWset k r D.z)
    (hb : b ∈ UWset k r D.z') : MeasurePreserving (Sab a b) D.μSS D.μSS := by
  have := sfin D.haarW; have := sfin D.haarN; have := sfin D.haarW'
  have m1 : MeasurePreserving (lmulM a) D.μW D.μW := ⟨(cont_lmul a).measurable, D.haarW.left a ha⟩
  have m2 : MeasurePreserving (conjM a) D.μN D.μN := ⟨(cont_sand a a⁻¹).measurable, hCI a (Or.inl ha)⟩
  have m3 : MeasurePreserving (lmulM b) D.μW' D.μW' := ⟨(cont_lmul b).measurable, D.haarW'.left b hb⟩
  have m4 : MeasurePreserving (conjM b) D.μN D.μN := ⟨(cont_sand b b⁻¹).measurable, hCI b (Or.inr hb)⟩
  exact (m1.prod m2).prod (m3.prod m4)

lemma ae_in (D : RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have := sfin D.haarW; have := sfin D.haarN; have := sfin D.haarW'
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW.conc)
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarN.conc)
  have hW' : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' :=
    ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW'.conc)
  have A1 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hW)
  have A2 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  have A3 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.1 ∈ UWset k r D.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hW')
  have A4 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [A1, A2, A3, A4] with p h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩

section lie

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def piLIE (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (V →L[ℂ] V)) (hrep : IsCRepOn (UWset k r z) π)
    (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) (a : Mat k r) (ha : a ∈ UWset k r z) : V ≃ₗᵢ[ℂ] V where
  toLinearEquiv := LinearEquiv.ofLinear (π a).toLinearMap (π a⁻¹).toLinearMap
    (LinearMap.ext fun v => by
      change ((π a).comp (π a⁻¹)) v = v
      rw [← hrep.2 a ha _ (uw_inv ha), Matrix.mul_nonsing_inv _ (isUnit_of_uh ha.1), hrep.1]
      rfl)
    (LinearMap.ext fun v => by
      change ((π a⁻¹).comp (π a)) v = v
      rw [← hrep.2 _ (uw_inv ha) a ha, Matrix.nonsing_inv_mul _ (isUnit_of_uh ha.1), hrep.1]
      rfl)
  norm_map' := hu a ha

end lie

def ph (D : RealPlaceData k r Wp Wq) (p : SS k r) : ℂ :=
  psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2))

lemma JF_eq (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    JF D F g = ∫ p, ph D p • rho D p F g ∂D.μSS := rfl

lemma ph_Sab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    (p : SS k r) : ph D (Sab a b p) = ph D p := by
  show psi k r D.z cStd (a * Matrix.of p.1.2 * a⁻¹) * star (psi k r D.z' cStd (b * Matrix.of p.2.2 * b⁻¹)) = _
  rw [psi_conj _ ha, psi_conj _ hb]
  rfl

lemma sgs_Sab {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (p : SS k r) (g : Mat k r) :
    sgs (Sab a b p) g = sgs p (a⁻¹ * g * b) := by
  show (a * Matrix.of p.1.1)⁻¹ * (a * Matrix.of p.1.2 * a⁻¹)⁻¹ * g * (b * Matrix.of p.2.2 * b⁻¹) *
      (b * Matrix.of p.2.1) = (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (a⁻¹ * g * b) * Matrix.of p.2.2 *
      Matrix.of p.2.1
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul_cancel_left _ _ ha, Matrix.nonsing_inv_mul_cancel_left _ _ hb]

lemma rho_Sab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    {p : SS k r} (hp : D.inSS p) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    rho D (Sab a b p) F g = (D.π a).comp ((rho D p F (a⁻¹ * g * b)).comp (D.π' b⁻¹)) := by
  show (D.π (a * Matrix.of p.1.1)).comp ((F (sgs (Sab a b p) g)).comp (D.π' (b * Matrix.of p.2.1)⁻¹)) = _
  rw [sgs_Sab (isUnit_of_uh ha.1) (isUnit_of_uh hb.1), D.π_rep.2 a ha _ hp.1, Matrix.mul_inv_rev,
    D.π'_rep.2 _ (uw_inv hp.2.2.1) _ (uw_inv hb)]
  simp only [rho, ContinuousLinearMap.comp_assoc]

def Lab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z') :
    (Wq →L[ℂ] Wp) ≃L[ℂ] (Wq →L[ℂ] Wp) :=
  ContinuousLinearEquiv.arrowCongr (piLIE D.z' D.π' D.π'_rep D.π'_unitary b hb).toContinuousLinearEquiv
    (piLIE D.z D.π D.π_rep D.π_unitary a ha).toContinuousLinearEquiv

lemma Lab_apply (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    (X : Wq →L[ℂ] Wp) : Lab D ha hb X = (D.π a).comp (X.comp (D.π' b⁻¹)) :=
  ContinuousLinearMap.ext fun _ => rfl

lemma norm_Lab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    (X : Wq →L[ℂ] Wp) : ‖Lab D ha hb X‖ = ‖X‖ := by
  have e : Lab D ha hb X = ((piLIE D.z D.π D.π_rep D.π_unitary a ha : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp
      (X.comp ((piLIE D.z' D.π' D.π'_rep D.π'_unitary b hb).symm : Wq →L[ℂ] Wq)) :=
    ContinuousLinearMap.ext fun _ => rfl
  rw [e, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

lemma J_equiv (D : RealPlaceData k r Wp Wq) (hCI : ConjInv D) {a b : Mat k r} (ha : a ∈ UWset k r D.z)
    (hb : b ∈ UWset k r D.z') (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    JF D F g = Lab D ha hb (JF D F (a⁻¹ * g * b)) := by
  rw [JF_eq, JF_eq, ← (mp_Sab D hCI ha hb).integral_comp (emb_Sab (isUnit_of_uh ha.1) (isUnit_of_uh hb.1)),
    ← ContinuousLinearEquiv.integral_comp_comm]
  refine integral_congr_ae ?_
  filter_upwards [ae_in D] with p hp
  rw [ph_Sab D ha hb, rho_Sab D ha hb hp, map_smul, Lab_apply]

lemma E_equiv (D : RealPlaceData k r Wp Wq) (hCI : ConjInv D) {a b : Mat k r} (ha : a ∈ UWset k r D.z)
    (hb : b ∈ UWset k r D.z') (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    ∫⁻ p, ‖rho D p F g‖ₑ ∂D.μSS = ∫⁻ p, ‖rho D p F (a⁻¹ * g * b)‖ₑ ∂D.μSS := by
  rw [← (mp_Sab D hCI ha hb).lintegral_comp_emb (emb_Sab (isUnit_of_uh ha.1) (isUnit_of_uh hb.1))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_in D] with p hp
  have h := norm_Lab D ha hb (rho D p F (a⁻¹ * g * b))
  rw [Lab_apply] at h
  rw [rho_Sab D ha hb hp, enorm_eq_nnnorm, enorm_eq_nnnorm,
    show ‖(D.π a).comp ((rho D p F (a⁻¹ * g * b)).comp (D.π' b⁻¹))‖₊ = ‖rho D p F (a⁻¹ * g * b)‖₊ from NNReal.eq h]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymB
