module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.FlagMatLower

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.PtEntryNeZeroImp
noncomputable section

namespace PI.AmpRootCommon

open Formalism.MainNotions.S

def pv : List (ℂ × ℕ) → ℕ → ℕ
  | [], i => i
  | (_, s) :: bs, i => if i < s then s - 1 - i else s + pv bs (i - s)

theorem ptEntry_ne_zero_imp : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), ptEntry bs i j ≠ 0 → j = pv bs i := by
  intro bs
  induction bs with
  | nil => intro i j h; simp [ptEntry] at h
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro i j h
    unfold ptEntry at h
    unfold pv
    by_cases h1 : i < s ∧ j < s
    · rw [ite_eq_left h1] at h
      by_cases h2 : i + j + 1 = s
      · rw [ite_eq_left h1.1]; omega
      · rw [ite_eq_right h2] at h; exact absurd rfl h
    · rw [ite_eq_right h1] at h
      by_cases h3 : s ≤ i ∧ s ≤ j
      · rw [ite_eq_left h3] at h
        have hj := ih (i - s) (j - s) h
        rw [ite_eq_right (by omega)]; omega
      · rw [ite_eq_right h3] at h; exact absurd rfl h

theorem pv_spec : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i < (bs.map Prod.snd).sum →
    pv bs i < (bs.map Prod.snd).sum ∧ pv bs (pv bs i) = i ∧ ptEntry bs i (pv bs i) ≠ 0 := by
  intro bs
  induction bs with
  | nil => intro _ i hi; simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro hb i hi
    have ht : t ≠ 0 := (hb (t, s) (by simp)).1
    have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (by simp [h])
    simp only [List.map_cons, List.sum_cons] at hi ⊢
    by_cases h1 : i < s
    · have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, h1]
      have e2 : pv ((t, s) :: bs) (s - 1 - i) = i := by
        simp only [pv]; rw [ite_eq_left (by omega)]; omega
      refine ⟨by omega, by rw [e1, e2], ?_⟩
      rw [e1]; unfold ptEntry
      rw [ite_eq_left ⟨h1, by omega⟩, ite_eq_left (by omega)]; exact ht
    · obtain ⟨ih1, ih2, ih3⟩ := ih hb' (i - s) (by omega)
      have e1 : pv ((t, s) :: bs) i = s + pv bs (i - s) := by simp [pv, h1]
      have e2 : pv ((t, s) :: bs) (s + pv bs (i - s)) = i := by
        simp only [pv]; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, ih2]; omega
      refine ⟨by omega, by rw [e1, e2], ?_⟩
      rw [e1]; unfold ptEntry
      rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]; exact ih3

theorem pv_adj : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i + 1 < (bs.map Prod.snd).sum →
    (pv bs (i + 1) + 1 = pv bs i ∧ ptEntry bs (pv bs (i + 1)) (i + 1) = ptEntry bs (pv bs i) i) ∨
      pv bs i < pv bs (i + 1) := by
  intro bs
  induction bs with
  | nil => intro _ i hi; simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro hb i hi
    have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (by simp [h])
    simp only [List.map_cons, List.sum_cons] at hi
    by_cases h1 : i + 1 < s
    · left
      have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, show i < s by omega]
      have e2 : pv ((t, s) :: bs) (i + 1) = s - 1 - (i + 1) := by simp [pv, h1]
      rw [e1, e2]
      refine ⟨by omega, ?_⟩
      unfold ptEntry
      rw [ite_eq_left ⟨by omega, h1⟩, ite_eq_left (by omega),
        ite_eq_left ⟨by omega, by omega⟩, ite_eq_left (by omega)]
    · by_cases h2 : i + 1 = s
      · right
        have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, show i < s by omega]
        have e2 : pv ((t, s) :: bs) (i + 1) = s + pv bs (i + 1 - s) := by simp [pv, h1]
        rw [e1, e2]; omega
      · have e1 : pv ((t, s) :: bs) i = s + pv bs (i - s) := by simp [pv, show ¬ i < s by omega]
        have e2 : pv ((t, s) :: bs) (i + 1) = s + pv bs (i - s + 1) := by
          simp only [pv]; rw [ite_eq_right h1, show i + 1 - s = i - s + 1 by omega]
        rw [e1, e2]
        rcases ih hb' (i - s) (by omega) with ⟨h3, h4⟩ | h3
        · left
          refine ⟨by omega, ?_⟩
          have hA : ¬ (s + pv bs (i - s + 1) < s ∧ i + 1 < s) := by omega
          have hB : s ≤ s + pv bs (i - s + 1) ∧ s ≤ i + 1 := by omega
          have hC : ¬ (s + pv bs (i - s) < s ∧ i < s) := by omega
          have hD : s ≤ s + pv bs (i - s) ∧ s ≤ i := by omega
          unfold ptEntry
          rw [ite_eq_right hA, ite_eq_left hB, ite_eq_right hC, ite_eq_left hD,
            Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, show i + 1 - s = i - s + 1 by omega]
          exact h4
        · right; omega

end PI.AmpRootCommon
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.SuperdiagPairingAdjacent
open Matrix

noncomputable section

namespace PI.AmpRootCommon

variable {n : ℕ}

theorem det_unitri {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) :
    u.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hu]; simp [hud]

theorem isUnit_unitri {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) :
    IsUnit u.det := by
  rw [det_unitri hu hud]; exact isUnit_one

theorem inv_upper {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) :
    u⁻¹.BlockTriangular id := by
  have : Invertible u := Matrix.invertibleOfIsUnitDet u (isUnit_unitri hu hud)
  exact Matrix.blockTriangular_inv_of_blockTriangular hu

theorem inv_superdiag {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (m1 m : Fin n) (hm : m1.val + 1 = m.val) : u⁻¹ m1 m = - u m1 m := by
  have hdet := isUnit_unitri hu hud
  have hw := inv_upper hu hud
  have hne : m1 ≠ m := fun e => by rw [e] at hm; omega
  have h1 : (u⁻¹ * u) m1 m = 0 := by
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply, if_neg hne]
  have h2 : (u⁻¹ * u) m1 m1 = 1 := by
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply, if_pos rfl]
  rw [Matrix.mul_apply, Finset.sum_eq_single m1] at h2
  · rw [Matrix.mul_apply, Finset.sum_eq_add m1 m hne] at h1
    · rw [hud] at h2 h1
      rw [mul_one] at h2
      rw [h2, one_mul] at h1
      linear_combination h1
    · intro c _ hc
      by_cases hlt : c.val < m1.val
      · rw [hw (show id c < id m1 from hlt), zero_mul]
      · have : m.val < c.val := by
          have h3 : c.val ≠ m1.val := fun e => hc.1 (Fin.ext e)
          have h4 : c.val ≠ m.val := fun e => hc.2 (Fin.ext e)
          omega
        rw [hu (show id m < id c from this), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    by_cases hlt : b.val < m1.val
    · rw [hw (show id b < id m1 from hlt), zero_mul]
    · have : m1.val < b.val := by
        have h3 : b.val ≠ m1.val := fun e => hb (Fin.ext e)
        omega
      rw [hu (show id m1 < id b from this), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

section Rel

variable {Z u u' : Matrix (Fin n) (Fin n) ℂ} {σ : Fin n → Fin n} {ζ : Fin n → ℂ}

theorem Z_row (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (i b : Fin n) (hb : b ≠ σ i) : Z i b = 0 := by
  rw [hZ, if_neg hb]

theorem Z_col (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (a j : Fin n)
    (ha : a ≠ σ j) : Z a j = 0 := by
  rw [hZ, if_neg]; intro e; apply ha; rw [e, hσ]

theorem Z_at (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (i : Fin n) : Z i (σ i) = ζ i := by
  rw [hZ, if_pos rfl]

theorem Z_at' (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (j : Fin n) :
    Z (σ j) j = ζ (σ j) := by
  rw [hZ, if_pos (hσ j).symm]

theorem relA (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) (hrel : uᴴ * Z * u' = Z) (i j : Fin n) :
    ζ i * u' (σ i) j = star (u⁻¹ (σ j) i) * ζ (σ j) := by
  have hdet := isUnit_unitri hu hud
  have hZu : Z * u' = (u⁻¹)ᴴ * Z := by
    calc Z * u' = ((u⁻¹)ᴴ * uᴴ) * Z * u' := by
          rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = (u⁻¹)ᴴ * (uᴴ * Z * u') := by simp only [Matrix.mul_assoc]
      _ = (u⁻¹)ᴴ * Z := by rw [hrel]
  have h := congrFun (congrFun hZu i) j
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ i), Finset.sum_eq_single (σ j)] at h
  · rw [Z_at hZ, Z_at' hσ hZ, Matrix.conjTranspose_apply] at h
    exact h
  · intro a _ ha; rw [Z_col hσ hZ a j ha, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; rw [Z_row hZ i b hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem relB (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z) (i j : Fin n) :
    star (u (σ j) i) * ζ (σ j) = ζ i * u'⁻¹ (σ i) j := by
  have hdet := isUnit_unitri hu' hud'
  have hZu : uᴴ * Z = Z * u'⁻¹ := by
    calc uᴴ * Z = uᴴ * Z * (u' * u'⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (uᴴ * Z * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Z * u'⁻¹ := by rw [hrel]
  have h := congrFun (congrFun hZu i) j
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ j), Finset.sum_eq_single (σ i)] at h
  · rw [Z_at hZ, Z_at' hσ hZ, Matrix.conjTranspose_apply] at h
    exact h
  · intro b _ hb; rw [Z_row hZ i b hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha; rw [Z_col hσ hZ a j ha, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem super_same (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hζ : ∀ i, ζ i ≠ 0) (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) (hrel : uᴴ * Z * u' = Z)
    (i i1 : Fin n) (h1 : (σ i1).val + 1 = (σ i).val) (h2 : ζ (σ i1) = - ζ (σ i)) :
    u' i i1 = star (u (σ i1) (σ i)) := by
  have h := relA hσ hZ hu hud hrel (σ i) i1
  rw [hσ, inv_superdiag hu hud (σ i1) (σ i) h1, h2, star_neg] at h
  apply mul_left_cancel₀ (hζ (σ i))
  linear_combination h

theorem super_diff (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hζ : ∀ i, ζ i ≠ 0) (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z)
    (i i1 : Fin n) (hlt : (σ i).val < (σ i1).val) : u' i i1 = 0 ∧ u i i1 = 0 := by
  constructor
  · have h := relA hσ hZ hu hud hrel (σ i) i1
    rw [hσ, inv_upper hu hud (show id (σ i) < id (σ i1) from hlt), star_zero, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (hζ _)
  · have h := relB hσ hZ hu' hud' hrel i1 (σ i)
    rw [hσ, inv_upper hu' hud' (show id (σ i) < id (σ i1) from hlt), mul_zero] at h
    have := (mul_eq_zero.mp h).resolve_right (hζ _)
    exact star_eq_zero.mp this

end Rel

section Sum

variable {m : ℕ}

def tau (σ : Fin (m + 1) → Fin (m + 1)) (i : Fin m) : Fin m :=
  if h : (σ i.succ).val + 1 = (σ i.castSucc).val then ⟨(σ i.succ).val, by have := (σ i.castSucc).isLt; omega⟩
  else i

theorem tau_val {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (tau σ i).val = (σ i.succ).val := by
  simp [tau, h]

theorem tau_neg {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : ¬ (σ i.succ).val + 1 = (σ i.castSucc).val) :
    tau σ i = i := by
  simp [tau, h]

theorem tau_cs {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (tau σ i).castSucc = σ i.succ := by
  apply Fin.ext; rw [Fin.val_castSucc, tau_val h]

theorem tau_succ {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (tau σ i).succ = σ i.castSucc := by
  apply Fin.ext; rw [Fin.val_succ, tau_val h, h]

theorem superdiagPairing_adjacent {σ : Fin (m + 1) → Fin (m + 1)} (hσ : ∀ i, σ (σ i) = i) {i : Fin m}
    (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (σ (tau σ i).succ).val + 1 = (σ (tau σ i).castSucc).val := by
  rw [tau_succ h, tau_cs h, hσ, hσ, Fin.val_castSucc, Fin.val_succ]

theorem tau_invol {σ : Fin (m + 1) → Fin (m + 1)} (hσ : ∀ i, σ (σ i) = i) : Function.Involutive (tau σ) := by
  intro i
  by_cases h : (σ i.succ).val + 1 = (σ i.castSucc).val
  · apply Fin.ext
    rw [tau_val (superdiagPairing_adjacent hσ h), tau_succ h, hσ, Fin.val_castSucc]
  · rw [tau_neg h, tau_neg h]

theorem sum_super {Z u u' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {σ : Fin (m + 1) → Fin (m + 1)}
    {ζ : Fin (m + 1) → ℂ} (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hζ : ∀ i, ζ i ≠ 0)
    (hadj : ∀ i i1 : Fin (m + 1), i1.val = i.val + 1 →
      ((σ i1).val + 1 = (σ i).val ∧ ζ (σ i1) = - ζ (σ i)) ∨ (σ i).val < (σ i1).val)
    (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z) :
    ∑ i : Fin m, u' i.castSucc i.succ = star (∑ i : Fin m, u i.castSucc i.succ) := by
  rw [star_sum]
  have hterm : ∀ i : Fin m, u' i.castSucc i.succ = star (u (tau σ i).castSucc (tau σ i).succ) := by
    intro i
    rcases hadj i.castSucc i.succ (by simp) with ⟨h1, h2⟩ | hlt
    · rw [tau_cs h1, tau_succ h1]
      exact super_same hσ hZ hζ hu hud hrel _ _ h1 h2
    · have hn : ¬ (σ i.succ).val + 1 = (σ i.castSucc).val := by omega
      rw [tau_neg hn]
      obtain ⟨e1, e2⟩ := super_diff hσ hZ hζ hu hud hu' hud' hrel _ _ hlt
      rw [e1, e2, star_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  exact Equiv.sum_comp (Function.Involutive.toPerm (tau σ) (tau_invol hσ))
    (fun i => star (u i.castSucc i.succ))

end Sum

end PI.AmpRootCommon
end
end

open Matrix

noncomputable section

namespace PI.AmpRootCommon

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem pt_spec (p : Point ℂ (r + 1)) (i : Fin (r + 1)) :
    pv p.1 i.val < r + 1 ∧ pv p.1 (pv p.1 i.val) = i.val ∧ ptEntry p.1 i.val (pv p.1 i.val) ≠ 0 := by
  let rec pv_spec : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i < (bs.map Prod.snd).sum →
      pv bs i < (bs.map Prod.snd).sum ∧ pv bs (pv bs i) = i ∧ ptEntry bs i (pv bs i) ≠ 0
    | [], _, i, hi => by simp at hi
    | (t, s) :: bs, hb, i, hi => by
      have ht : t ≠ 0 := (hb (t, s) (by simp)).1
      have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (by simp [h])
      simp only [List.map_cons, List.sum_cons] at hi ⊢
      by_cases h1 : i < s
      · have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, h1]
        have e2 : pv ((t, s) :: bs) (s - 1 - i) = i := by
          simp only [pv]; rw [if_pos (by omega)]; omega
        refine ⟨by omega, by rw [e1, e2], ?_⟩
        rw [e1]; unfold ptEntry
        rw [if_pos ⟨h1, by omega⟩, if_pos (by omega)]; exact ht
      · obtain ⟨ih1, ih2, ih3⟩ := pv_spec bs hb' (i - s) (by omega)
        have e1 : pv ((t, s) :: bs) i = s + pv bs (i - s) := by simp [pv, h1]
        have e2 : pv ((t, s) :: bs) (s + pv bs (i - s)) = i := by
          simp only [pv]; rw [if_neg (by omega), Nat.add_sub_cancel_left, ih2]; omega
        refine ⟨by omega, by rw [e1, e2], ?_⟩
        rw [e1]; unfold ptEntry
        rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]; exact ih3
  have h := pv_spec p.1 p.2.1 i.val (by rw [p.2.2]; exact i.isLt)
  rw [p.2.2] at h
  exact h

def ptσ (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : Fin (r + 1) := ⟨pv p.1 i.val, (pt_spec p i).1⟩

def ptζ (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ℂ :=
  (-1 : ℂ) ^ (r - (ptσ p i).val) * ptMat p i (ptσ p i)

theorem ptσ_invol (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ptσ p (ptσ p i) = i := Fin.ext (pt_spec p i).2.1

theorem ptζ_ne (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ptζ p i ≠ 0 := by
  unfold ptζ
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pt_spec p i).2.2

theorem neg_one_pow_mul_self (m : ℕ) : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
  rw [← mul_pow]
  norm_num

theorem zhat_pt {z z' : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : Point ℂ (r + 1)} (hP : ZhatO k r z z' g = ptMat p) (i j : Fin (r + 1)) :
    Zhat k r z z' g i j = if j = ptσ p i then ptζ p i else 0 := by
  let rec ptEntry_ne_zero_imp : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), ptEntry bs i j ≠ 0 → j = pv bs i
    | [], i, j, h => by simp [ptEntry] at h
    | (t, s) :: bs, i, j, h => by
      unfold ptEntry at h
      unfold pv
      by_cases h1 : i < s ∧ j < s
      · rw [if_pos h1] at h
        by_cases h2 : i + j + 1 = s
        · rw [if_pos h1.1]; omega
        · rw [if_neg h2] at h; exact absurd rfl h
      · rw [if_neg h1] at h
        by_cases h3 : s ≤ i ∧ s ≤ j
        · rw [if_pos h3] at h
          have := ptEntry_ne_zero_imp bs (i - s) (j - s) h
          rw [if_neg (by omega)]; omega
        · rw [if_neg h3] at h; exact absurd rfl h
  have hZ : Zhat k r z z' g i j = (-1 : ℂ) ^ (r - j.val) * ptMat p i j := by
    have h := congrFun (congrFun hP i) j
    simp only [ZhatO] at h
    rw [← h, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  rw [hZ]
  split_ifs with hj
  · subst hj
    rfl
  · have : ptEntry p.1 i.val j.val = 0 := by
      by_contra hne
      exact hj (Fin.ext (ptEntry_ne_zero_imp p.1 i.val j.val hne))
    show (-1 : ℂ) ^ (r - j.val) * ptEntry p.1 i.val j.val = 0
    rw [this, mul_zero]

theorem pt_adj (p : Point ℂ (r + 1)) (i i1 : Fin (r + 1)) (hi1 : i1.val = i.val + 1) :
    ((ptσ p i1).val + 1 = (ptσ p i).val ∧ ptζ p (ptσ p i1) = - ptζ p (ptσ p i)) ∨
      (ptσ p i).val < (ptσ p i1).val := by
  let rec pv_adj : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i + 1 < (bs.map Prod.snd).sum →
      (pv bs (i + 1) + 1 = pv bs i ∧ ptEntry bs (pv bs (i + 1)) (i + 1) = ptEntry bs (pv bs i) i) ∨
        pv bs i < pv bs (i + 1)
    | [], _, i, hi => by simp at hi
    | (t, s) :: bs, hb, i, hi => by
      have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (by simp [h])
      simp only [List.map_cons, List.sum_cons] at hi
      by_cases h1 : i + 1 < s
      · left
        have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, show i < s by omega]
        have e2 : pv ((t, s) :: bs) (i + 1) = s - 1 - (i + 1) := by simp [pv, h1]
        rw [e1, e2]
        refine ⟨by omega, ?_⟩
        unfold ptEntry
        rw [if_pos ⟨by omega, h1⟩, if_pos (by omega), if_pos ⟨by omega, by omega⟩, if_pos (by omega)]
      · by_cases h2 : i + 1 = s
        · right
          have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, show i < s by omega]
          have e2 : pv ((t, s) :: bs) (i + 1) = s + pv bs (i + 1 - s) := by simp [pv, h1]
          rw [e1, e2]; omega
        · have e1 : pv ((t, s) :: bs) i = s + pv bs (i - s) := by simp [pv, show ¬ i < s by omega]
          have e2 : pv ((t, s) :: bs) (i + 1) = s + pv bs (i - s + 1) := by
            simp only [pv]; rw [if_neg h1, show i + 1 - s = i - s + 1 by omega]
          rw [e1, e2]
          rcases pv_adj bs hb' (i - s) (by omega) with ⟨h3, h4⟩ | h3
          · left
            refine ⟨by omega, ?_⟩
            have hA : ¬ (s + pv bs (i - s + 1) < s ∧ i + 1 < s) := by omega
            have hB : s ≤ s + pv bs (i - s + 1) ∧ s ≤ i + 1 := by omega
            have hC : ¬ (s + pv bs (i - s) < s ∧ i < s) := by omega
            have hD : s ≤ s + pv bs (i - s) ∧ s ≤ i := by omega
            unfold ptEntry
            rw [if_neg hA, if_pos hB, if_neg hC, if_pos hD, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
              show i + 1 - s = i - s + 1 by omega]
            exact h4
          · right; omega
  have hs := p.2.2
  have hi1lt := i1.isLt
  rcases pv_adj p.1 p.2.1 i.val (by rw [hs]; omega) with ⟨h1, h2⟩ | h1
  · left
    have hv : pv p.1 i1.val = pv p.1 (i.val + 1) := by rw [hi1]
    refine ⟨by show pv p.1 i1.val + 1 = pv p.1 i.val; rw [hv]; exact h1, ?_⟩
    unfold ptζ
    rw [ptσ_invol p i1, ptσ_invol p i]
    show (-1 : ℂ) ^ (r - i1.val) * ptEntry p.1 (pv p.1 i1.val) i1.val =
      -((-1 : ℂ) ^ (r - i.val) * ptEntry p.1 (pv p.1 i.val) i.val)
    rw [hv, hi1, h2]
    have hr : r - i.val = (r - (i.val + 1)) + 1 := by omega
    rw [hr, pow_succ]
    ring
  · right
    show pv p.1 i.val < pv p.1 i1.val
    rw [hi1]
    exact h1

theorem flag_rel_Rset {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (hx : x ∈ Formalism.MainNotions.S.Rset k r g) :
    (flagMat k r z (g * x * g⁻¹))ᴴ * Zhat k r z z' g * flagMat k r z' x = Zhat k r z z' g := by
  have hgi : g⁻¹ * g = 1 := uh_inv_mul hg
  have hxe : g⁻¹ * (g * x * g⁻¹) * g = x := by
    calc g⁻¹ * (g * x * g⁻¹) * g = (g⁻¹ * g) * x * (g⁻¹ * g) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hgi, Matrix.one_mul, Matrix.mul_one]
  have ha : g * x * g⁻¹ ∈ RStab k r g := ⟨hx.2, by rw [hxe]; exact hx.1⟩
  have h := flag_rel hz hz' hg ha
  rw [hxe] at h
  exact h

section AtPt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
  {p : Point ℂ (r + 1)}

private theorem isUnit_det_of_unitriangular {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u.BlockTriangular id)
    (hd : ∀ i, u i i = 1) : IsUnit u.det := by
  rw [Matrix.det_of_upperTriangular hu, Finset.prod_eq_one fun i _ => hd i]
  exact isUnit_one

theorem flag_entry (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (i j : Fin (r + 1)) :
    ptζ p i * flagMat k r z' (g⁻¹ * a * g) (ptσ p i) j =
      star ((flagMat k r z a)⁻¹ (ptσ p j) i) * ptζ p (ptσ p j) := by
  have hU := isUnit_det_of_unitriangular (flagMat k r z a) (flagMat_upper ha.1) (flagMat_diag ha.1)
  have hrel := flag_rel hz hz' hg ha
  have hkey : Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g) =
      ((flagMat k r z a)⁻¹)ᴴ * Zhat k r z z' g := by
    calc Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g)
        = ((flagMat k r z a)⁻¹)ᴴ *
            ((flagMat k r z a)ᴴ * Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g)) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
            Matrix.mul_nonsing_inv _ hU, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = ((flagMat k r z a)⁻¹)ᴴ * Zhat k r z z' g := by rw [hrel]
  have hσ : ∀ l, (j = ptσ p l) ↔ (l = ptσ p j) := by
    intro l
    constructor
    · rintro rfl
      exact (ptσ_invol p l).symm
    · rintro rfl
      exact (ptσ_invol p j).symm
  have h := congrFun (congrFun hkey i) j
  simp only [Matrix.mul_apply, zhat_pt hP, hσ, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h
  exact h

private theorem blockTriangular_inv_of_unitriangular {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u.BlockTriangular id)
    (hd : ∀ i, u i i = 1) : u⁻¹.BlockTriangular id := by
  have hU := isUnit_det_of_unitriangular u hu hd
  letI : Invertible u := ⟨u⁻¹, Matrix.nonsing_inv_mul u hU, Matrix.mul_nonsing_inv u hU⟩
  exact Matrix.blockTriangular_inv_of_blockTriangular hu

private theorem star_flagMat_mul_ptZeta_eq (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (m n : Fin (r + 1)) :
    star (flagMat k r z a (ptσ p n) m) * ptζ p (ptσ p n) =
      ptζ p m * (flagMat k r z' (g⁻¹ * a * g))⁻¹ (ptσ p m) n := by
  have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
  have hU := isUnit_det_of_unitriangular (flagMat k r z' (g⁻¹ * a * g)) (flagMat_upper hx) (flagMat_diag hx)
  have hrel := flag_rel hz hz' hg ha
  have hkey : (flagMat k r z a)ᴴ * Zhat k r z z' g =
      Zhat k r z z' g * (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by
    calc (flagMat k r z a)ᴴ * Zhat k r z z' g
        = (flagMat k r z a)ᴴ * Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g) *
            (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by
          rw [Matrix.mul_assoc _ (flagMat k r z' (g⁻¹ * a * g)), Matrix.mul_nonsing_inv _ hU,
            Matrix.mul_one]
      _ = Zhat k r z z' g * (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by rw [hrel]
  have hσ : ∀ l, (n = ptσ p l) ↔ (l = ptσ p n) := by
    intro l
    constructor
    · rintro rfl
      exact (ptσ_invol p l).symm
    · rintro rfl
      exact (ptσ_invol p n).symm
  have h := congrFun (congrFun hkey m) n
  simp only [Matrix.mul_apply, zhat_pt hP, hσ, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h
  exact h

theorem flag_offblock (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (i j : Fin (r + 1))
    (hlt : (ptσ p i).val < (ptσ p j).val) :
    flagMat k r z' (g⁻¹ * a * g) i j = 0 ∧ flagMat k r z a i j = 0 := by
  have hlt' : ptσ p i < ptσ p j := hlt
  refine ⟨?_, ?_⟩
  · have h := flag_entry hz hz' hg hP ha (ptσ p i) j
    rw [ptσ_invol] at h
    have hv := blockTriangular_inv_of_unitriangular (flagMat k r z a) (flagMat_upper ha.1) (flagMat_diag ha.1)
    have h0 : (flagMat k r z a)⁻¹ (ptσ p j) (ptσ p i) = 0 := hv hlt'
    rw [h0, star_zero, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (ptζ_ne p _)
  · have h := star_flagMat_mul_ptZeta_eq hz hz' hg hP ha j (ptσ p i)
    rw [ptσ_invol] at h
    have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
    have hv := blockTriangular_inv_of_unitriangular (flagMat k r z' (g⁻¹ * a * g)) (flagMat_upper hx) (flagMat_diag hx)
    have h0 : (flagMat k r z' (g⁻¹ * a * g))⁻¹ (ptσ p j) (ptσ p i) = 0 := hv hlt'
    rw [h0, mul_zero] at h
    exact star_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (ptζ_ne p i))

end AtPt

end PI.AmpRootCommon
