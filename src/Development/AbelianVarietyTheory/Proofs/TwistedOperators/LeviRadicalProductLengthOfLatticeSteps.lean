module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviRadicalProductLengthOfLatticeSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviRadicalProductLengthOfLatticeSteps
open GlobalTheory.InertZeta

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem exists_eq_exp_of_ne {x : WithZero (Multiplicative ℤ)} (h : x ≠ 0) : ∃ m : ℤ, x = WithZero.exp m :=
  ⟨x.log, (WithZero.exp_log h).symm⟩

theorem exp_mul_le_exp_iff {x : WithZero (Multiplicative ℤ)} {s k : ℤ} :
    WithZero.exp s * x ≤ WithZero.exp k ↔ x ≤ WithZero.exp (k - s) := by
  by_cases h : x = 0
  · subst h; simp
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h
    rw [← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega

theorem exp_succ_le_of_not_le {x : WithZero (Multiplicative ℤ)} {k : ℤ} (h : ¬ x ≤ WithZero.exp k) :
    WithZero.exp (k + 1) ≤ x := by
  by_cases h0 : x = 0
  · subst h0; exact absurd zero_le h
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h0
    rw [WithZero.exp_le_exp] at h ⊢
    omega

theorem exists_le_exp_add (x : WithZero (Multiplicative ℤ)) (k₀ : ℤ) : ∃ e : ℕ, x ≤ WithZero.exp (k₀ + e) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h0
    exact ⟨(m - k₀).toNat, WithZero.exp_le_exp.2 (by omega)⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_pow_unif {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, hϖ, ← WithZero.exp_nsmul]; congr 1; simp

theorem v_zpow_unif {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; congr 1; simp

theorem pow_mul_mem_intL_iff {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) (x : L) :
    ϖ ^ k * x ∈ intL L ↔ Valued.v x ≤ WithZero.exp (k : ℤ) := by
  show Valued.v (ϖ ^ k * x) ≤ 1 ↔ _
  rw [map_mul, v_pow_unif hϖ, ← WithZero.exp_zero, exp_mul_le_exp_iff]
  simp

section Entries

variable {σ : L →+* L} {N : ℕ}


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem leviElt_mul_rad_entries {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m u : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m)
    (hu : u ∈ radQ σ N) :
    mat (m * u) 0 0 = ϖ ^ a ∧ (∀ j, mat (m * u) 0 (mid j) = ϖ ^ a * rowOf u j) ∧
    mat (m * u) 0 (Fin.last (N + 1)) = ϖ ^ a * cornerOf u ∧
    (∀ i, mat (m * u) (mid i) 0 = 0) ∧ (∀ i j, mat (m * u) (mid i) (mid j) = mat g₀ i j) ∧
    (∀ i, mat (m * u) (mid i) (Fin.last (N + 1)) = (mat g₀ *ᵥ colOf u) i) ∧
    mat (m * u) (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, mat (m * u) (Fin.last (N + 1)) (mid j) = 0) ∧
    mat (m * u) (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) := by
  obtain ⟨hmz, h00, hll, hmm⟩ := hm
  have hmz' : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hmz
  have hu' : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  have m0m : ∀ j, mat m 0 (mid j) = 0 := fun j => hmz' _ _ (by simp)
  have m0l : mat m 0 (Fin.last (N + 1)) = 0 := hmz' _ _ (by simp)
  have mm0 : ∀ i, mat m (mid i) 0 = 0 := fun i => hmz' _ _ (by simp)
  have mml : ∀ i, mat m (mid i) (Fin.last (N + 1)) = 0 := fun i => hmz' _ _ (by simp)
  have ml0 : mat m (Fin.last (N + 1)) 0 = 0 := hmz' _ _ (by simp)
  have mlm : ∀ j, mat m (Fin.last (N + 1)) (mid j) = 0 := fun j => hmz' _ _ (by simp)
  have u00 : mat u 0 0 = 1 := by rw [hu' _ _ le_rfl, Matrix.one_apply_eq]
  have um0 : ∀ i, mat u (mid i) 0 = 0 := fun i => by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne (mid_ne_zero i)]
  have ul0 : mat u (Fin.last (N + 1)) 0 = 0 := by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne last_ne_zero]
  have hu_mm : ∀ i j, mat u (mid i) (mid j) = if i = j then 1 else 0 := fun i j => by
    rw [hu' _ _ (by simp), Matrix.one_apply]; simp [mid_injective.eq_iff]
  have ulm : ∀ j, mat u (Fin.last (N + 1)) (mid j) = 0 := fun j => by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne (fun h => mid_ne_last j h.symm)]
  have ull : mat u (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by rw [hu' _ _ le_rfl, Matrix.one_apply_eq]
  simp only [mat_mul, Matrix.mul_apply, sum_idx]
  refine ⟨?_, fun j => ?_, ?_, fun i => ?_, fun i j => ?_, fun i => ?_, ?_, fun j => ?_, ?_⟩ <;>
    simp [m0m, m0l, mm0, mml, ml0, mlm, u00, um0, ul0, hu_mm, ulm, ull, h00, hll, hmm, rowOf, colOf, cornerOf,
      Matrix.mulVec, dotProduct]

end Entries

theorem pointwise_of_steps (hA : AddVec) (hD : Dual) (hS : SpanEq) (hH : Heis) : Pointwise := by
  intro L _ _ ϖ σ q N hU a g₀ m hm U V C l hf hl u hu
  classical
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨e00, e0m, e0l, em0, emm, eml, el0, elm, ell⟩ := leviElt_mul_rad_entries hm hu
  have hrb : ∀ j, rowOf u j = -σ (colOf u j.rev) := ((hH L ϖ σ q N hU).1 u hu).1

  let Q : ℕ → Prop := fun e => ∀ j, Valued.v ((rowOf u ᵥ* C) j) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)
  have hQD : ∀ e, Q e ↔
      (∀ i, Valued.v (((C * V * mat g₀) *ᵥ colOf u) i) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)) ∧
      ∀ i, Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ) := fun e => by
    have := hD L ϖ σ q N hU g₀ U V C hf (rowOf u) (colOf u) (ϖ ^ (a.toNat + e)) hrb
    simp only [pow_mul_mem_intL_iff hϖ] at this
    exact this
  have hQex : ∃ e, Q e := by
    choose f hf' using fun j => exists_le_exp_add (Valued.v ((rowOf u ᵥ* C) j)) (a.toNat : ℤ)
    obtain ⟨M, hM⟩ := Finite.exists_le f
    exact ⟨M, fun j => (hf' j).trans (WithZero.exp_le_exp.2 (by have := hM j; push_cast; omega))⟩
  let e := Nat.find hQex
  have hQe : Q e := Nat.find_spec hQex
  have hQmono : ∀ e', Q e' ↔ e ≤ e' := fun e' =>
    ⟨fun h => Nat.find_min' hQex h, fun h j => (hQe j).trans (WithZero.exp_le_exp.2 (by push_cast; omega))⟩
  have hnQ : 0 < e → ¬ Q (e - 1) := fun he h => by have := (hQmono _).1 h; omega
  have hsucc : 0 < e → ((a.toNat + (e - 1) : ℕ) : ℤ) + 1 = ((a.toNat + e : ℕ) : ℤ) := fun he => by omega
  have hQsharp : 0 < e → ∃ j, Valued.v ((rowOf u ᵥ* C) j) = WithZero.exp ((a.toNat + e : ℕ) : ℤ) := fun he => by
    obtain ⟨j, hj⟩ := not_forall.1 (hnQ he)
    refine ⟨j, le_antisymm (hQe j) ?_⟩
    have := exp_succ_le_of_not_le hj
    rwa [hsucc he] at this

  let y : L := ϖ ^ (-((a.toNat + e : ℕ) : ℤ))
  have hy : Valued.v y = WithZero.exp ((a.toNat + e : ℕ) : ℤ) := by rw [v_zpow_unif hϖ, neg_neg]
  obtain ⟨h2, h3⟩ := (hQD e).1 hQe
  have h4 : Valued.v y = WithZero.exp (a.toNat : ℤ) ∨
      (∃ i, Valued.v y = Valued.v (((C * V * mat g₀) *ᵥ colOf u) i)) ∨
      ∃ i, Valued.v y = Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) := by
    rcases Nat.eq_zero_or_pos e with he | he
    · left; rw [hy, he]; rfl
    · right
      have hn := hnQ he
      rw [hQD] at hn
      rcases not_and_or.1 hn with hn | hn
      · obtain ⟨i, hi⟩ := not_forall.1 hn
        have := exp_succ_le_of_not_le hi
        rw [hsucc he] at this
        exact Or.inl ⟨i, by rw [hy]; exact le_antisymm this (h2 i)⟩
      · obtain ⟨i, hi⟩ := not_forall.1 hn
        have := exp_succ_le_of_not_le hi
        rw [hsucc he] at this
        exact Or.inr ⟨i, by rw [hy]; exact le_antisymm this (h3 i)⟩
  obtain ⟨P, ρ, hPdet, hρ0, hρm, hρl, hlat⟩ :=
    hS L ϖ N a (mat (m * u)) (mat g₀) U V C (rowOf u) (colOf u) (cornerOf u) y hϖ hf e00 e0m e0l em0 emm eml el0 elm
      ell (by rw [hy, WithZero.exp_le_exp]; push_cast; omega) (fun i => by rw [hy]; exact h2 i)
      (fun i => by rw [hy]; exact h3 i) h4
  obtain ⟨c', hc'⟩ : ∃ c', c' = cornerOf u - rowOf u ⬝ᵥ ((C * V * mat g₀) *ᵥ colOf u) := ⟨_, rfl⟩
  rw [← hc'] at hρl
  have hPdet' : Valued.v P.det = WithZero.exp ((a.natAbs + l + e : ℕ) : ℤ) := by
    rw [hPdet, hl, hy, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, ← WithZero.exp_add]
    congr 1; simp only [Nat.cast_add]; omega
  have hvm : ∀ j (k : ℤ), Valued.v (ρ (mid j)) ≤ WithZero.exp k ↔
      Valued.v ((rowOf u ᵥ* C) j) ≤ WithZero.exp (k + a.toNat) := fun j k => by
    rw [hρm, map_mul, v_pow_unif hϖ, exp_mul_le_exp_iff, sub_neg_eq_add]
  have hvl : Valued.v (ρ (Fin.last (N + 1))) = WithZero.exp (-((2 * a.toNat + e : ℕ) : ℤ)) * Valued.v c' := by
    rw [hρl, map_div₀, map_mul, v_pow_unif hϖ, hy, div_eq_mul_inv, ← WithZero.exp_neg, mul_comm, ← mul_assoc,
      ← WithZero.exp_add]
    congr 2; push_cast; ring
  have hvl' : ∀ k : ℤ, Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp k ↔
      Valued.v c' ≤ WithZero.exp (k + ((2 * a.toNat + e : ℕ) : ℤ)) := fun k => by
    rw [hvl, exp_mul_le_exp_iff, sub_neg_eq_add]

  let R : ℕ → Prop := fun e₂ => e ≤ e₂ ∧ Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp (e₂ : ℤ)
  have hRex : ∃ e₂, R e₂ := by
    obtain ⟨k, hk⟩ := exists_le_exp_add (Valued.v (ρ (Fin.last (N + 1)))) (e : ℤ)
    exact ⟨e + k, by omega, by rwa [Nat.cast_add]⟩
  let e₂ := Nat.find hRex
  have hRe₂ : R e₂ := Nat.find_spec hRex
  have hbound : ∀ i, Valued.v (ρ i) ≤ WithZero.exp (e₂ : ℤ) := fun i => by
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
    · rw [hρ0, map_zero]; exact zero_le
    · rw [hvm]
      exact (hQe j).trans (WithZero.exp_le_exp.2 (by have := hRe₂.1; push_cast; omega))
    · exact hRe₂.2
  have hsharp : e₂ = 0 ∨ ∃ i, Valued.v (ρ i) = WithZero.exp (e₂ : ℤ) := by
    by_cases h : e₂ = e
    · rcases Nat.eq_zero_or_pos e with he | he
      · left; omega
      · right
        obtain ⟨j, hj⟩ := hQsharp he
        refine ⟨mid j, ?_⟩
        rw [hρm, map_mul, v_pow_unif hϖ, hj, ← WithZero.exp_add, h]
        congr 1; push_cast; ring
    · right
      have hlt : e < e₂ := lt_of_le_of_ne hRe₂.1 (Ne.symm h)
      have hn : ¬ R (e₂ - 1) := Nat.find_min hRex (by omega)
      have hn' : ¬ Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp ((e₂ - 1 : ℕ) : ℤ) := fun h' =>
        hn ⟨by omega, h'⟩
      refine ⟨Fin.last (N + 1), le_antisymm hRe₂.2 ?_⟩
      have := exp_succ_le_of_not_le hn'
      rwa [show ((e₂ - 1 : ℕ) : ℤ) + 1 = (e₂ : ℤ) by omega] at this
  have hLat := hA L (N + 2) P ((a.natAbs + l + e : ℕ) : ℤ) ρ e₂ hPdet' hbound hsharp
  rw [← hlat] at hLat
  have hlen : len (mat (m * u)) = a.natAbs + l + e + e₂ :=
    (hasLen_of_latLen (k := a.natAbs + l + e + e₂) (by convert hLat using 1; push_cast; ring)).len_eq
  rw [hlen]
  refine ⟨by omega, fun j => ?_⟩
  have hsm : Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) u ↔
      e ≤ j / 2 ∧ Valued.v c' ≤ WithZero.exp ((2 * a.toNat + j : ℕ) : ℤ) := by
    unfold Small
    rw [← hc']
    simp only [pow_mul_mem_intL_iff hϖ]
    exact and_congr (hQmono (j / 2)) Iff.rfl
  rw [hsm]
  constructor
  · intro h
    have h1 := hRe₂.1
    refine ⟨by omega, ?_⟩
    refine ((hvl' _).1 hRe₂.2).trans (WithZero.exp_le_exp.2 ?_)
    push_cast; omega
  · rintro ⟨h1, h2⟩
    have hR : R (j - e) := ⟨by omega, (hvl' _).2 (h2.trans_eq (by congr 1; push_cast; omega))⟩
    have := Nat.find_min' hRex hR
    omega

end GlobalTheory.InertZeta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviRadicalProductLengthOfLatticeStepsStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviRadicalProductLength_of_lattice_steps : AddVec → Dual → SpanEq → Heis → Pointwise := by
  first | exact @GlobalTheory.InertZeta.pointwise_of_steps | exact GlobalTheory.InertZeta.pointwise_of_steps | (intros; apply GlobalTheory.InertZeta.pointwise_of_steps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenberg
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenberg
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section HeisCalc

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem rowOf_one : rowOf (1 : GU σ (N + 2)) = 0 := funext fun j =>
  Matrix.one_apply_ne (mid_ne_zero j).symm

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem colOf_one : colOf (1 : GU σ (N + 2)) = 0 := funext fun i =>
  Matrix.one_apply_ne (mid_ne_last i)

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cornerOf_one : cornerOf (1 : GU σ (N + 2)) = 0 :=
  Matrix.one_apply_ne (last_ne_zero (N := N)).symm

variable
  (h1 : ∀ u ∈ radQ σ N, (∀ j, rowOf u j = -σ (colOf u j.rev)) ∧ cornerOf u + σ (cornerOf u) = rowOf u ⬝ᵥ colOf u ∧
      (u ∈ KU σ (N + 2) ↔ (∀ j, rowOf u j ∈ intL L) ∧ cornerOf u ∈ intL L))
  (h2 : ∀ u ∈ radQ σ N, ∀ u' ∈ radQ σ N, rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u')
include h1

theorem colOf_eq_of_rowOf_eq {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N)
    (h : rowOf u = rowOf u') : colOf u = colOf u' := funext fun i => by
  have a := (h1 u hu).1 i.rev
  have b := (h1 u' hu').1 i.rev
  rw [Fin.rev_rev, h] at a
  rw [Fin.rev_rev] at b
  exact σ.injective (neg_injective (a.symm.trans b))

theorem colOf_eq_zero {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) (h : rowOf u = 0) : colOf u = 0 := by
  rw [colOf_eq_of_rowOf_eq h1 hu (one_mem _) (h.trans rowOf_one.symm), colOf_one]

include h2

theorem rowOf_inv {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) :
    rowOf u⁻¹ = -rowOf u ∧ cornerOf u⁻¹ = -cornerOf u + rowOf u ⬝ᵥ colOf u := by
  obtain ⟨r, -, c⟩ := h2 u⁻¹ (inv_mem hu) u hu
  rw [inv_mul_cancel, rowOf_one] at r
  rw [inv_mul_cancel, cornerOf_one] at c
  have r' : rowOf u⁻¹ = -rowOf u := eq_neg_of_add_eq_zero_left r.symm
  refine ⟨r', ?_⟩
  rw [r', neg_dotProduct] at c
  linear_combination -c

theorem inv_mul_of_rowOf_eq {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N)
    (h : rowOf u = rowOf u') : rowOf (u⁻¹ * u') = 0 ∧ cornerOf (u⁻¹ * u') = cornerOf u' - cornerOf u := by
  obtain ⟨ri, ci⟩ := rowOf_inv h1 h2 hu
  obtain ⟨r, -, c⟩ := h2 u⁻¹ (inv_mem hu) u' hu'
  have hc := colOf_eq_of_rowOf_eq h1 hu hu' h
  refine ⟨by rw [r, ri, h, neg_add_cancel], ?_⟩
  rw [c, ci, ri, ← hc, neg_dotProduct]
  ring

theorem rowOf_inv_mul {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    rowOf (u⁻¹ * u') = -rowOf u + rowOf u' := by
  rw [(h2 u⁻¹ (inv_mem hu) u' hu').1, (rowOf_inv h1 h2 hu).1]

theorem mul_of_rowOf_eq_zero {u z : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hz : z ∈ radQ σ N) (h : rowOf z = 0) :
    rowOf (u * z) = rowOf u ∧ colOf (u * z) = colOf u ∧ cornerOf (u * z) = cornerOf u + cornerOf z := by
  obtain ⟨r, b, c⟩ := h2 u hu z hz
  have hb := colOf_eq_zero h1 hz h
  refine ⟨by rw [r, h, add_zero], by rw [b, hb, add_zero], by rw [c, hb, dotProduct_zero, add_zero]⟩

end HeisCalc

end GlobalTheory.InertZeta

namespace GlobalTheory.InertZeta

theorem count_of_heis : Heis → LatIndex → TraceIndex → Count := by
  intro hH hL hT L _ _ ϖ σ q N hU C D l e f hC hdet hex hinv
  obtain ⟨h1, h2, h3⟩ := hH L ϖ σ q N hU
  have hσσ := hU.1
  have hσv := hU.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := hU.2.2.2.1
  have hϖ1 : ϖ ∈ intL L := by show Valued.v ϖ ≤ 1; rw [hϖ]; exact oneLePart_eq_one.mp rfl
  have hσint : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx

  set A : Matrix (Fin N) (Fin N) L := ϖ ^ e • C with hA
  have hAint : IsInt A := fun i j => by
    rw [hA, Matrix.smul_apply, smul_eq_mul]; exact mul_mem (pow_mem hϖ1 _) (hC i j)
  have hAdet : Valued.v A.det = WithZero.exp (-((l + N * e : ℕ) : ℤ)) := by
    rw [hA, Matrix.det_smul, map_mul, map_pow, map_pow, hϖ, hdet, Fintype.card_fin, ← WithZero.exp_nsmul,
      ← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1; push_cast; ring
  have iL := hL L ϖ σ q N hU A (l + N * e) hAint hAdet
  have iT := hT L ϖ σ q f hU
  set Λ := preLat A
  set I := intV L N
  set T := traceZero σ (ϖ ^ f)
  set T₀ := traceZero σ 1
  have memΛ : ∀ r : Fin N → L, r ∈ Λ ↔ ∀ j, ϖ ^ e * (r ᵥ* C) j ∈ intL L := fun r => by
    rw [mem_preLat, hA, Matrix.vecMul_smul]; rfl
  rw [pow_add, ← iL, ← iT]

  have ex0 : ∀ r : Λ, ∃ u : radQ σ N, rowOf (u : GU σ (N + 2)) = r ∧ Small ϖ e f C D (u : GU σ (N + 2)) := fun r => by
    obtain ⟨u, hu, h, hs⟩ := hex r ((memΛ r).1 r.2)
    exact ⟨⟨u, hu⟩, h, hs⟩
  choose u₀ hu₀r hu₀s using ex0
  have exz : ∀ t : T, ∃ z : radQ σ N, rowOf (z : GU σ (N + 2)) = 0 ∧ cornerOf (z : GU σ (N + 2)) = t := fun t => by
    have ht := (mem_traceZero.1 t.2).2
    obtain ⟨z, hz, h, hc⟩ := h3 0 t (by
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero]; linear_combination ht)
    exact ⟨⟨z, hz⟩, h, hc⟩
  choose z hzr hzc using exz
  have smallOut : ∀ w : radQ σ N, Small ϖ e f C D (w : GU σ (N + 2)) →
      Small ϖ e f C D (((QuotientGroup.mk w : RadQuot σ N).out : radQ σ N) : GU σ (N + 2)) := fun w hw => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul ((KU σ (N + 2)).subgroupOf (radQ σ N)) w
    rw [hk]
    exact hinv w.1 w.2 k.1.1 k.1.2 (Subgroup.mem_subgroupOf.1 k.2) hw
  have smallW : ∀ (r : Λ) (t : T), Small ϖ e f C D ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) := fun r t => by
    obtain ⟨hr, hb, hc⟩ := mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)
    have hs := hu₀s r
    show Small ϖ e f C D ((u₀ r : GU σ (N + 2)) * (z t : GU σ (N + 2)))
    refine ⟨fun j => ?_, ?_⟩
    · rw [hr]; exact hs.1 j
    · rw [hr, hb, hc, hzc]
      convert add_mem hs.2 (mem_traceZero.1 t.2).1 using 1
      ring
  have rowW : ∀ (r : Λ) (t : T), rowOf ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) = r := fun r t =>
    ((mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)).1).trans (hu₀r r)
  have cornerW : ∀ (r : Λ) (t : T), cornerOf ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) =
      cornerOf (u₀ r : GU σ (N + 2)) + t := fun r t => by
    rw [← hzc t]; exact (mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)).2.2
  let Φ : (Λ ⧸ I.addSubgroupOf Λ) × (T ⧸ T₀.addSubgroupOf T) →
      {x : RadQuot σ N // Small ϖ e f C D (x.out : radQ σ N).1} := fun p =>
    ⟨QuotientGroup.mk (u₀ p.1.out * z p.2.out), smallOut _ (smallW _ _)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have hk := QuotientGroup.eq.1 (congrArg Subtype.val h)
      rw [Subgroup.mem_subgroupOf] at hk
      have hK := (h1 _ ((u₀ a.out * z b.out)⁻¹ * (u₀ a'.out * z b'.out)).2).2.2.1 hk
      have ha : a = a' := by
        rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' a', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf, mem_intV]
        intro j
        have := hK.1 j
        rwa [Subgroup.coe_mul, Subgroup.coe_inv, rowOf_inv_mul h1 h2 (u₀ a.out * z b.out).2 (u₀ a'.out * z b'.out).2,
          rowW, rowW] at this
      subst ha
      have hb : b = b' := by
        rw [← QuotientAddGroup.out_eq' b, ← QuotientAddGroup.out_eq' b', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf, mem_traceZero]
        have hd := inv_mul_of_rowOf_eq h1 h2 (u₀ a.out * z b.out).2 (u₀ a.out * z b'.out).2
          ((rowW _ _).trans (rowW _ _).symm)
        have hc := hK.2
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hd.2, cornerW, cornerW] at hc
        have t1 := (mem_traceZero.1 b.out.2).2
        have t2 := (mem_traceZero.1 b'.out.2).2
        refine ⟨?_, ?_⟩
        · convert hc using 1; push_cast; ring
        · push_cast; rw [map_add (f := _), map_neg]; linear_combination t2 - t1
      rw [hb]
    · rintro ⟨x, hx⟩

      have hrΛ : rowOf ((x.out : radQ σ N) : GU σ (N + 2)) ∈ Λ := (memΛ _).2 hx.1
      have hρ : (-(⟨_, hrΛ⟩ : Λ) + (QuotientAddGroup.mk (⟨_, hrΛ⟩ : Λ) : Λ ⧸ I.addSubgroupOf Λ).out) ∈
          I.addSubgroupOf Λ := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
      rw [AddSubgroup.mem_addSubgroupOf, mem_intV] at hρ
      set a : Λ ⧸ I.addSubgroupOf Λ := QuotientAddGroup.mk (⟨_, hrΛ⟩ : Λ) with ha
      set u : radQ σ N := x.out with hu
      set ρ : Fin N → L := -rowOf (u : GU σ (N + 2)) + (a.out : Fin N → L) with hρdef
      have hρ' : ∀ i, ρ i ∈ intL L := hρ
      obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
      set s : L := -∑ j, ρ j * σ (ρ j.rev) with hsdef
      have hs : σ s = s := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hsdef, map_neg, map_sum, map_mul, hσσ]
        congr 1
        exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp [mul_comm])
      have hsint : s ∈ intL L := neg_mem (Subring.sum_mem _ fun j _ => mul_mem (hρ' j) (hσint _ (hρ' _)))
      obtain ⟨k, hk, hkr, hkc⟩ := h3 ρ (τ * s) (by rw [map_mul, hs]; linear_combination s * hτ1)
      have hkK : k ∈ KU σ (N + 2) := (h1 k hk).2.2.2 ⟨fun j => hkr ▸ hρ' j, hkc ▸ mul_mem hτ hsint⟩
      set uk : radQ σ N := u * ⟨k, hk⟩ with hukdef
      have hukS : Small ϖ e f C D (uk : GU σ (N + 2)) := hinv u.1 u.2 k hk hkK hx
      have hukr : rowOf (uk : GU σ (N + 2)) = a.out := by
        rw [hukdef, Subgroup.coe_mul, (h2 _ u.2 _ hk).1, hkr, hρdef, add_neg_cancel_left]
      have hv := inv_mul_of_rowOf_eq h1 h2 (u₀ a.out).2 uk.2 ((hu₀r _).trans hukr.symm)
      set v : radQ σ N := (u₀ a.out)⁻¹ * uk with hvdef
      have hvr : rowOf (v : GU σ (N + 2)) = 0 := hv.1
      have hvc : cornerOf (v : GU σ (N + 2)) = cornerOf (uk : GU σ (N + 2)) - cornerOf (u₀ a.out : GU σ (N + 2)) := hv.2
      have htT : cornerOf (v : GU σ (N + 2)) ∈ T := by
        rw [mem_traceZero]
        refine ⟨?_, ?_⟩
        · have hcol := colOf_eq_of_rowOf_eq h1 (u₀ a.out).2 uk.2 ((hu₀r _).trans hukr.symm)
          have := sub_mem hukS.2 (hu₀s a.out).2
          rw [hukr, ← hcol, hu₀r] at this
          rw [hvc]
          convert this using 1
          ring
        · have := (h1 _ v.2).2.1
          rw [hvr, zero_dotProduct] at this
          linear_combination this
      set bq : T ⧸ T₀.addSubgroupOf T := QuotientAddGroup.mk (⟨_, htT⟩ : T) with hbq
      have hδ : (-(⟨_, htT⟩ : T) + bq.out) ∈ T₀.addSubgroupOf T := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceZero] at hδ
      refine ⟨(a, bq), Subtype.ext ?_⟩
      show (QuotientGroup.mk (u₀ a.out * z bq.out) : RadQuot σ N) = x
      have e1 : (QuotientGroup.mk u : RadQuot σ N) = QuotientGroup.mk uk :=
        QuotientGroup.eq.2 (by rw [hukdef, inv_mul_cancel_left]; exact Subgroup.mem_subgroupOf.2 hkK)
      rw [← QuotientGroup.out_eq' x, ← hu, e1, QuotientGroup.eq,
        show (u₀ a.out * z bq.out)⁻¹ * uk = (z bq.out)⁻¹ * v by rw [hvdef, _root_.mul_inv_rev, mul_assoc],
        Subgroup.mem_subgroupOf]
      have hzv := inv_mul_of_rowOf_eq h1 h2 (z bq.out).2 v.2 ((hzr _).trans hvr.symm)
      refine (h1 _ ((z bq.out)⁻¹ * v).2).2.2.2 ⟨fun j => ?_, ?_⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, hzv.1]; exact zero_mem _
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, hzv.2, hzc]
        have := neg_mem hδ.1
        convert this using 1
        push_cast
        ring
  rw [show I.relIndex Λ * T₀.relIndex T = Nat.card ((Λ ⧸ I.addSubgroupOf Λ) × (T ⧸ T₀.addSubgroupOf T)) from
    (Nat.card_prod _ _).symm]
  exact (Nat.card_eq_of_bijective Φ hΦ).symm

end GlobalTheory.InertZeta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenbergStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallRadicalCosetCount_of_heisenberg : Heis → LatIndex → TraceIndex → Count := by
  first | exact @GlobalTheory.InertZeta.count_of_heis | exact GlobalTheory.InertZeta.count_of_heis | (intros; apply GlobalTheory.InertZeta.count_of_heis <;> assumption)
end
end
