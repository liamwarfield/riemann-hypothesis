module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InvSqrtTwoMulSelf
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.MatExtBvec
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

def sg (k r i : ℕ) : ℕ := if i < r ∨ r + k < i then 2 * r + k - i else i

theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = sg k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  unfold Hpk sg
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    rcases h1 with h1 | h1
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_pos ⟨h1, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_neg (by omega), if_pos ⟨by omega, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h1]
    push Not at h1
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases h2 : i = j
    · subst h2; rw [if_pos ⟨h1.1, h1.2, rfl⟩, if_pos rfl]
    · rw [if_neg (fun h => h2 h.2.2), if_neg (fun h => h2 (Fin.ext h.symm))]

theorem hpk_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) : Hpk k r j i = Hpk k r i j := by
  rw [hpk_apply, hpk_apply]; unfold sg
  split_ifs <;> first | rfl | omega

theorem hpk_conjT (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hpk_symm, hpk_apply]
  split_ifs <;> simp

theorem sg_lt {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i < 2 * r + k + 1 := by
  unfold sg; split_ifs <;> omega

theorem sg_sg {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r (sg k r i) = i := by
  unfold sg; split_ifs <;> omega

theorem sg_rk {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i = r + k ↔ i = r + k := by
  unfold sg; split_ifs <;> omega

theorem hpk_apply' (k r i : ℕ) (hi : i < 2 * r + k + 1) (j : Fin (2 * r + k + 1)) :
    Hpk k r ⟨i, hi⟩ j = if j.val = sg k r i then (if i = r + k then -1 else 1) else 0 :=
  hpk_apply k r ⟨i, hi⟩ j

theorem hpk_mul (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨sg k r i.val, sg_lt i.2⟩ : Fin _)]
  · rw [hpk_apply k r i ⟨sg k r i.val, sg_lt i.2⟩, hpk_apply' k r _ (sg_lt i.2) j, sg_sg i.2, Matrix.one_apply,
      if_pos (show ((⟨sg k r i.val, sg_lt i.2⟩ : Fin (2 * r + k + 1)).val = sg k r i.val) from rfl)]
    have hs := sg_rk (k := k) (r := r) i.2
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
      by_cases h : i.val = r + k
      · rw [if_pos h, if_pos (hs.2 h)]; norm_num
      · rw [if_neg h, if_neg (fun h' => h (hs.1 h'))]; norm_num
    · rw [if_neg hij, if_neg (fun h : j.val = i.val => hij (Fin.ext h.symm)), mul_zero]
  · intro b _ hb; rw [hpk_apply k r i b, if_neg (fun h => hb (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_mid {n N : ℕ} (h : N = n + 2) (f : Fin N → ℂ) (h0 : ∀ q : Fin N, q.val = 0 → f q = 0)
    (h1 : ∀ q : Fin N, q.val = n + 1 → f q = 0) : ∑ q, f q = ∑ q : Fin n, f ⟨q.val + 1, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, h0 0 rfl, h1 (Fin.last n).succ (by simp)]
  simp only [zero_add, add_zero]; rfl

theorem mv_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (q p : Fin n) : (M *ᵥ bvec q) p = M p q := by
  unfold bvec; simp [mulVec, dotProduct, Pi.single_apply]

theorem mat_ext_bvec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : ∀ q, A *ᵥ bvec q = B *ᵥ bvec q) : A = B := by
  ext i j; have := congrFun (h j) i; rwa [mv_bvec, mv_bvec] at this

section Lev
variable {k r' : ℕ}

def sh (q : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := ⟨q.val + 1, by have := q.2; omega⟩

theorem sh_val (q : Fin (2 * r' + k + 1)) : (sh q).val = q.val + 1 := rfl

theorem exists_sh (p : Fin (2 * (1 + r') + k + 1)) (hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) :
    ∃ q : Fin (2 * r' + k + 1), p = sh q :=
  ⟨⟨p.val - 1, by omega⟩, Fin.ext (by simp [sh]; omega)⟩

theorem sum_sh (f : Fin (2 * (1 + r') + k + 1) → ℂ) (h0 : ∀ q : Fin _, q.val = 0 → f q = 0)
    (h1 : ∀ q : Fin _, q.val = 2 * (1 + r') + k → f q = 0) : ∑ q, f q = ∑ q : Fin (2 * r' + k + 1), f (sh q) :=
  sum_mid (n := 2 * r' + k + 1) (by omega) f h0 (fun q hq => h1 q (by omega))

theorem lv_in (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) : liftVec k 1 r' v (sh q) = v q := by
  unfold liftVec; rw [dite_eq_left (show 1 ≤ (sh q).val ∧ (sh q).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := q.2; simp [sh]; omega⟩)]
  congr 1

theorem lv_out (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : liftVec k 1 r' v p = 0 := by
  unfold liftVec; rw [dite_eq_right (by omega)]

theorem io_in (g : Mat k r') (p q : Fin (2 * r' + k + 1)) : ιLev k 1 r' g (sh p) (sh q) = g p q := by
  unfold ιLev
  rw [dite_eq_left (show 1 ≤ (sh p).val ∧ (sh p).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := p.2; simp [sh]; omega⟩),
    dite_eq_left (show 1 ≤ (sh q).val ∧ (sh q).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := q.2; simp [sh]; omega⟩)]
  congr 1

theorem io_out (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · rw [dite_eq_left hp, dite_eq_right (by omega), if_neg (fun h => by subst h; omega)]
  · rw [dite_eq_right hp]

theorem io_out' (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  unfold ιLev; rw [dite_eq_right (by omega)]

theorem io_lv (g : Mat k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' v = liftVec k 1 r' (g *ᵥ v) := by
  funext p
  simp only [mulVec, dotProduct]
  rw [sum_sh _ (fun q hq => by rw [lv_out v q (by omega), mul_zero]) (fun q hq => by rw [lv_out v q (by omega), mul_zero])]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · obtain ⟨p', rfl⟩ := exists_sh p hp
    rw [lv_in]; simp only [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun q _ => by rw [io_in, lv_in]
  · rw [lv_out _ p (by omega)]
    exact Finset.sum_eq_zero fun q _ => by
      rw [io_out' g p _ (by omega), if_neg (fun h => by rw [h, sh_val] at hp; omega), zero_mul]

theorem io_bvec_out (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) :
    ιLev k 1 r' g *ᵥ bvec q = bvec q := by
  funext p; rw [mv_bvec, io_out g p q hq]; unfold bvec; simp only [Pi.single_apply]

theorem bvec_lv (q : Fin (2 * r' + k + 1)) : (bvec (sh q) : Fin (2 * (1 + r') + k + 1) → ℂ) = liftVec k 1 r' (bvec q) := by
  funext p
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · obtain ⟨p', rfl⟩ := exists_sh p hp
    rw [lv_in]; unfold bvec; simp only [Pi.single_apply, Fin.ext_iff, sh_val]; simp
  · rw [lv_out _ p (by omega)]; unfold bvec; rw [Pi.single_apply, if_neg (fun h => by rw [h, sh_val] at hp; omega)]

theorem io_bvec_sh (g : Mat k r') (q : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g *ᵥ bvec (sh q) = liftVec k 1 r' (g *ᵥ bvec q) := by
  rw [bvec_lv, io_lv]

theorem io_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  apply mat_ext_bvec; intro q
  rw [← Matrix.mulVec_mulVec]
  by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · obtain ⟨q', rfl⟩ := exists_sh q hq
    rw [io_bvec_sh, io_bvec_sh, io_lv, Matrix.mulVec_mulVec]
  · rw [io_bvec_out _ _ (by omega), io_bvec_out _ _ (by omega), io_bvec_out _ _ (by omega)]

theorem io_one : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext_bvec; intro q
  rw [Matrix.one_mulVec]
  by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · obtain ⟨q', rfl⟩ := exists_sh q hq
    rw [io_bvec_sh, Matrix.one_mulVec, bvec_lv]
  · rw [io_bvec_out _ _ (by omega)]

theorem io_conjT (g : Mat k r') : ιLev k 1 r' gᴴ = (ιLev k 1 r' g)ᴴ := by
  ext p q
  rw [conjTranspose_apply]; unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 <;>
    by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · rw [dite_eq_left hp, dite_eq_left hq, dite_eq_left hq, dite_eq_left hp, conjTranspose_apply]
  · rw [dite_eq_left hp, dite_eq_right hq, dite_eq_right hq, if_neg (fun h => by subst h; exact hq hp), star_zero]
  · rw [dite_eq_right hp, dite_eq_left hq, dite_eq_right hp, if_neg (fun h => by subst h; exact hp hq), star_zero]
  · rw [dite_eq_right hp, dite_eq_right hq]; by_cases h : p = q
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]

end Lev

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

section herm
variable {n : ℕ}

theorem dot_bvec (i : Fin n) (x : Fin n → ℂ) : star (bvec i) ⬝ᵥ x = x i := by
  unfold dotProduct
  rw [Finset.sum_eq_single i]
  · simp [bvec]
  · intro b _ hb; simp [bvec, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bvec_self (i : Fin n) : bvec i i = 1 := by simp [bvec]

theorem bvec_ne (i j : Fin n) (h : i.val ≠ j.val) : bvec i j = 0 := by
  unfold bvec; rw [Pi.single_apply, if_neg (fun e => h (congrArg Fin.val e).symm)]

theorem herm_bb (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : herm H (bvec i) (bvec j) = H j i := by
  unfold herm; rw [dot_bvec, mv_bvec]

theorem herm_add_l (H : Matrix (Fin n) (Fin n) ℂ) (v v' w : Fin n → ℂ) :
    herm H (v + v') w = herm H v w + herm H v' w := by
  unfold herm; rw [mulVec_add, dotProduct_add]

theorem herm_smul_l (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v w : Fin n → ℂ) : herm H (c • v) w = c * herm H v w := by
  unfold herm; rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_add_r (H : Matrix (Fin n) (Fin n) ℂ) (v w w' : Fin n → ℂ) :
    herm H v (w + w') = herm H v w + herm H v w' := by
  unfold herm; rw [star_add, add_dotProduct]

theorem herm_smul_r (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v w : Fin n → ℂ) :
    herm H v (c • w) = star c * herm H v w := by
  unfold herm; rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_sum_l (H : Matrix (Fin n) (Fin n) ℂ) {ι : Type} (s : Finset ι) (f : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ i ∈ s, f i) w = ∑ i ∈ s, herm H (f i) w := by
  unfold herm; rw [Matrix.mulVec_sum, dotProduct_sum]

theorem herm_zero_l (H : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) : herm H 0 w = 0 := by
  unfold herm; rw [mulVec_zero, dotProduct_zero]

theorem herm_mul (H g : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm (gᴴ * H * g) v w := by
  unfold herm; rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem herm_UH (H g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  rw [herm_mul, show gᴴ * H * g = H from hg]

end herm

theorem herm_hpk_r (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v (Hpk k r *ᵥ w) = star w ⬝ᵥ v := by
  unfold herm; rw [star_mulVec, ← dotProduct_mulVec, hpk_conjT, mulVec_mulVec, hpk_mul, one_mulVec]

theorem sq2_mul_sq2_eq_half : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  try push_cast
  rw [← mul_inv, h2]; norm_num

theorem star_inv_sqrt_two : star ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  try push_cast
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal]

section phi
variable (k n : ℕ)

theorem hpk_ww (j j' : Fin (k + 1)) :
    Hpk k n (wI k n j) (wI k n j') = if j = j' then (if j.val = k then -1 else 1) else 0 := by
  rw [hpk_apply]
  have hj := j.2
  have e1 : (wI k n j).val = n + j.val := rfl
  have e2 : (wI k n j').val = n + j'.val := rfl
  have hs : sg k n (n + j.val) = n + j.val := by unfold sg; rw [if_neg (by omega)]
  rw [e1, e2, hs]
  by_cases h : j = j'
  · subst h; rw [if_pos rfl, if_pos rfl]
    by_cases h' : j.val = k
    · rw [if_pos (by omega : n + j.val = n + k), if_pos h']
    · rw [if_neg (by omega : ¬ n + j.val = n + k), if_neg h']
  · rw [if_neg h, if_neg (fun e => h (Fin.ext (by omega)))]

theorem phi_iso (hk : 1 ≤ k) (a b : Fin (n + 1)) : herm (Hpk k n) (phiV k n a) (phiV k n b) = 0 := by
  unfold phiV
  split_ifs with ha hb hb
  · rw [herm_bb, hpk_apply]; simp only [esI, Fin.val_mk]; unfold sg; split_ifs <;> first | omega | rfl
  · unfold epsV
    rw [herm_smul_r, herm_add_r, herm_bb, herm_bb, hpk_apply, hpk_apply]
    simp only [esI, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]; unfold sg; split_ifs <;> first | omega | simp
  · unfold epsV
    rw [herm_smul_l, herm_add_l, herm_bb, herm_bb, hpk_apply, hpk_apply]
    simp only [esI, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]; unfold sg; split_ifs <;> first | omega | simp
  · unfold epsV
    have h0l : (0 : Fin (k + 1)) ≠ Fin.last k := fun h => by have := congrArg Fin.val h; simp at this; omega
    rw [herm_smul_l, herm_smul_r, herm_add_l, herm_add_r, herm_add_r, herm_bb, herm_bb, herm_bb, herm_bb]
    have hk0 : (0 : ℕ) ≠ k := by omega
    simp [hpk_ww, h0l, h0l.symm, hk0]

theorem eps_dot (hk : 1 ≤ k) : star (epsV k n) ⬝ᵥ epsV k n = 1 := by
  unfold epsV
  have hne : (wI k n 0).val ≠ (wI k n (Fin.last k)).val := by simp only [wI, Fin.val_zero, Fin.val_last]; omega
  rw [star_smul, star_inv_sqrt_two, smul_dotProduct, dotProduct_smul, star_add, add_dotProduct, dot_bvec, dot_bvec]
  simp only [Pi.add_apply, bvec_self, bvec_ne _ _ hne, bvec_ne _ _ (Ne.symm hne), smul_eq_mul]
  linear_combination 2 * sq2_mul_sq2_eq_half

theorem phi_dot (hk : 1 ≤ k) (a b : Fin (n + 1)) :
    star (phiV k n b) ⬝ᵥ phiV k n a = if a = b then 1 else 0 := by
  have hv : a = b ↔ a.val = b.val := Fin.ext_iff
  unfold phiV
  split_ifs with ha hb hab hb hab hb hab hb hab
  · subst hab; rw [dot_bvec, bvec_self]
  · rw [dot_bvec, bvec_ne]; simp only [esI, Fin.val_mk]; omega
  · omega
  · unfold epsV
    rw [dot_bvec, Pi.smul_apply, Pi.add_apply, bvec_ne, bvec_ne, add_zero, smul_zero]
    · simp only [esI, wI, Fin.val_mk]; simp; omega
    · simp only [esI, wI, Fin.val_mk]; simp; omega
  · omega
  · unfold epsV
    rw [star_smul, smul_dotProduct, star_add, add_dotProduct, dot_bvec, dot_bvec, bvec_ne, bvec_ne, add_zero, smul_zero]
    · simp only [esI, wI, Fin.val_mk]; simp; omega
    · simp only [esI, wI, Fin.val_mk]; simp; omega
  · exact eps_dot k n hk
  · omega

theorem phi_pair (hk : 1 ≤ k) (a b : Fin (n + 1)) :
    herm (Hpk k n) (phiV k n a) (phiV' k n b) = if a = b then 1 else 0 := by
  unfold phiV'; rw [herm_hpk_r, phi_dot k n hk]

theorem mphi_li (hk : 1 ≤ k) (m : Mat k n) (hm : m ∈ UH (Hpk k n)) :
    LinearIndependent ℂ (fun a => m *ᵥ phiV k n a) := by
  rw [Fintype.linearIndependent_iff]; intro g hg b
  have h : herm (Hpk k n) (∑ a, g a • (m *ᵥ phiV k n a)) (m *ᵥ phiV' k n b) =
      herm (Hpk k n) 0 (m *ᵥ phiV' k n b) := by rw [hg]
  rw [herm_zero_l, herm_sum_l] at h
  simp only [herm_smul_l, herm_UH _ _ hm, phi_pair k n hk, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

theorem iw_apply (hIW : IW) (hk : 1 ≤ k) (m : Mat k n) (hm : m ∈ UH (Hpk k n)) :
    ∃ κ : Mat k n, κ ∈ GV k n ∧ κᴴ * κ = 1 ∧ ∃ τ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, m *ᵥ phiV k n a = ∑ b, τ b a • (κ *ᵥ phiV k n b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k n l (fun a => m *ᵥ phiV k n a) := by
  obtain ⟨κ0, hκ0, τ, hτ, hrep, hprod⟩ := hIW k n (fun a => m *ᵥ phiV k n a) hk (mphi_li k n hk m hm)
    (fun a b => by
      show herm (Hpk k n) (m *ᵥ phiV k n a) (m *ᵥ phiV k n b) = 0
      rw [herm_UH _ _ hm, phi_iso k n hk])
  have hG : κ0ᴴ * Hpk k n * κ0 = Hpk k n := hκ0.1
  have hU : κ0ᴴ * κ0 = 1 := hκ0.2
  refine ⟨κ0 * Hpk k n, ?_, ?_, τ, hτ, fun a => ?_, hprod⟩
  · show (κ0 * Hpk k n)ᴴ * Hpk k n * (κ0 * Hpk k n) = Hpk k n
    rw [conjTranspose_mul, hpk_conjT]
    calc Hpk k n * κ0ᴴ * Hpk k n * (κ0 * Hpk k n) = Hpk k n * (κ0ᴴ * Hpk k n * κ0) * Hpk k n := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k n := by rw [hG, hpk_mul, Matrix.one_mul]
  · rw [conjTranspose_mul, hpk_conjT]
    calc Hpk k n * κ0ᴴ * (κ0 * Hpk k n) = Hpk k n * (κ0ᴴ * κ0) * Hpk k n := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.mul_one, hpk_mul]
  · rw [show m *ᵥ phiV k n a = ∑ b, τ b a • (κ0 *ᵥ phiV' k n b) from hrep a]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold phiV'; rw [Matrix.mulVec_mulVec]

end phi

section gram

theorem sum_castLE {M : Type} [AddCommMonoid M] {n l : ℕ} (h : l + 1 ≤ n) (f : Fin n → M)
    (hf : ∀ b : Fin n, l < b.val → f b = 0) : ∑ b, f b = ∑ b : Fin (l + 1), f (Fin.castLE h b) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE h)))]
  · rw [Finset.sum_image (fun a _ b _ e => Fin.castLE_injective h e)]
  · intro b _ hb; apply hf; by_contra hc; push Not at hc
    exact hb (Finset.mem_image.2 ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩)

theorem prod_Iic {M : Type} [CommMonoid M] {n : ℕ} (l : Fin (n + 1)) (f : Fin (n + 1) → M) :
    ∏ j ∈ Finset.Iic l, f j = ∏ j : Fin (l.val + 1), f (Fin.castLE (by omega) j) := by
  apply Finset.prod_nbij' (fun a => (⟨min a.val l.val, by omega⟩ : Fin (l.val + 1))) (Fin.castLE (by omega))
  · intro a _; exact Finset.mem_univ _
  · intro a _; rw [Finset.mem_Iic, Fin.le_def]; simp; omega
  · intro a ha; rw [Finset.mem_Iic, Fin.le_def] at ha; ext; simp; omega
  · intro a _; ext; simp; omega
  · intro a ha; rw [Finset.mem_Iic, Fin.le_def] at ha; congr 1; ext; simp; omega

theorem gram_mat' {N L : ℕ} (X : Fin L → Fin N → ℂ) (Xm : Matrix (Fin N) (Fin L) ℂ) (hX : ∀ p a, Xm p a = X a p) :
    (Matrix.of fun a b => star (X a) ⬝ᵥ X b) = Xmᴴ * Xm := by
  ext a b; simp [Matrix.mul_apply, dotProduct, conjTranspose_apply, hX]

theorem det_gram_tri {N L : ℕ} (Z : Fin L → Fin N → ℂ) (T : Matrix (Fin L) (Fin L) ℂ) (hT : T.BlockTriangular id) :
    (Matrix.of fun a b => star (∑ j, T j a • Z j) ⬝ᵥ ∑ j, T j b • Z j).det =
      (star (∏ j, T j j) * ∏ j, T j j) * (Matrix.of fun a b => star (Z a) ⬝ᵥ Z b).det := by
  rw [gram_mat' (fun a => ∑ j, T j a • Z j) ((Matrix.of fun p a => Z a p) * T) (fun p a => by
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _),
    gram_mat' Z (Matrix.of fun p a => Z a p) (fun p a => rfl), conjTranspose_mul]
  rw [show Tᴴ * (Matrix.of fun p a => Z a p)ᴴ * ((Matrix.of fun p a => Z a p) * T) =
      Tᴴ * ((Matrix.of fun p a => Z a p)ᴴ * (Matrix.of fun p a => Z a p)) * T by simp only [Matrix.mul_assoc]]
  rw [det_mul, det_mul, det_conjTranspose, det_of_upperTriangular hT]; ring

theorem ga_tri (k r : ℕ) (Z : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (l : Fin (r + 1)) :
    Ga k r l (fun a => ∑ b, τ b a • Z b) = (∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2) * Ga k r l Z := by
  have h : l.val + 1 ≤ r + 1 := by omega
  have hs : ∀ a : Fin (l.val + 1), (∑ b, τ b (Fin.castLE h a) • Z b) =
      ∑ j : Fin (l.val + 1), τ (Fin.castLE h j) (Fin.castLE h a) • Z (Fin.castLE h j) := by
    intro a; apply sum_castLE h; intro b hb
    rw [hτ (show id (Fin.castLE h a) < id b by simp only [id, Fin.lt_def, Fin.val_castLE]; omega), zero_smul]
  have hT : (τ.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
    intro i j hij; simp only [submatrix_apply]; apply hτ
    simp only [id, Fin.lt_def, Fin.val_castLE] at hij ⊢; exact hij
  unfold Ga
  simp only [hs]
  have key := det_gram_tri (fun j => Z (Fin.castLE h j)) (τ.submatrix (Fin.castLE h) (Fin.castLE h)) hT
  simp only [submatrix_apply] at key
  rw [key, prod_Iic l, show star (∏ j, τ (Fin.castLE h j) (Fin.castLE h j)) * ∏ j, τ (Fin.castLE h j) (Fin.castLE h j) =
      ((Complex.normSq (∏ j, τ (Fin.castLE h j) (Fin.castLE h j)) : ℝ) : ℂ) from (Complex.normSq_eq_conj_mul_self).symm,
    Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, norm_prod, ← Finset.prod_pow]

theorem ga_unit (k r : ℕ) (U : Mat k r) (hU : Uᴴ * U = 1) (l : Fin (r + 1)) (Z : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => U *ᵥ Z a) = Ga k r l Z := by
  unfold Ga; simp only [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hU, one_mulVec]

end gram

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem Iic_zero (n : ℕ) : Finset.Iic (0 : Fin (n + 1)) = {0} := by
  ext a
  simp [Fin.le_zero_iff]

section Lv
variable {k r' : ℕ}

def su (a : Fin (r' + 1)) : Fin (1 + r' + 1) := ⟨a.val + 1, by omega⟩

theorem su_val (a : Fin (r' + 1)) : (su a).val = a.val + 1 := rfl

theorem exists_su (a : Fin (1 + r' + 1)) (ha : a.val ≠ 0) : ∃ b : Fin (r' + 1), a = su b := by
  refine ⟨⟨a.val - 1, by have := a.2; omega⟩, Fin.ext ?_⟩
  show a.val = (a.val - 1) + 1
  omega

theorem prod_su {M : Type} [CommMonoid M] (f : Fin (1 + r' + 1) → M) :
    ∏ l, f l = f 0 * ∏ a : Fin (r' + 1), f (su a) := by
  rw [Fin.prod_univ_succ]
  congr 1
  exact (Fintype.prod_equiv (finCongr (by omega : r' + 1 = 1 + r')) (fun a => f (su a))
    (fun b => f b.succ) fun a => congrArg f (Fin.ext (by simp [su]))).symm

theorem sum_su {M : Type} [AddCommMonoid M] (f : Fin (1 + r' + 1) → M) :
    ∑ l, f l = f 0 + ∑ a : Fin (r' + 1), f (su a) := by
  rw [Fin.sum_univ_succ]
  congr 1
  exact (Fintype.sum_equiv (finCongr (by omega : r' + 1 = 1 + r')) (fun a => f (su a))
    (fun b => f b.succ) fun a => congrArg f (Fin.ext (by simp [su]))).symm

theorem lv_add (v w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' (v + w) = liftVec k 1 r' v + liftVec k 1 r' w := by
  ext p
  simp only [liftVec, Pi.add_apply]
  split_ifs <;> simp

theorem lv_smul (c : ℂ) (v : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' (c • v) = c • liftVec k 1 r' v := by
  ext p
  simp only [liftVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem lv_sum {ι : Type} (s : Finset ι) (f : ι → Fin (2 * r' + k + 1) → ℂ) :
    liftVec k 1 r' (∑ i ∈ s, f i) = ∑ i ∈ s, liftVec k 1 r' (f i) := by
  have e : liftVec k 1 r' (∑ i ∈ s, f i) =
      (AddMonoidHom.mk' (liftVec k 1 r') fun v w => lv_add v w) (∑ i ∈ s, f i) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  rfl

theorem phi_lift (a : Fin (r' + 1)) : liftVec k 1 r' (phiV k r' a) = phiV k (1 + r') (su a) := by
  unfold phiV
  by_cases h : a.val < r'
  · have h' : (su a).val < 1 + r' := by rw [su_val]; omega
    rw [dite_eq_left h, dite_eq_left h', ← bvec_lv]
    congr 1
    ext
    simp only [sh, esI, su_val, Fin.val_mk]
    omega
  · have h' : ¬ (su a).val < 1 + r' := by rw [su_val]; omega
    rw [dite_eq_right h, dite_eq_right h']
    unfold epsV
    have e0 : sh (wI k r' 0) = wI k (1 + r') 0 := by
      ext
      simp only [sh, wI, Fin.val_mk]
      omega
    have e1 : sh (wI k r' (Fin.last k)) = wI k (1 + r') (Fin.last k) := by
      ext
      simp only [sh, wI, Fin.val_mk]
      omega
    rw [lv_smul, lv_add, ← bvec_lv, ← bvec_lv, e0, e1]

theorem besselPhi_eq_reindexConj_rootCoords : phiV k (1 + r') 0 = bvec ⟨2 * (1 + r') + k, by omega⟩ := by
  unfold phiV
  rw [dite_eq_left (by simp only [Fin.val_zero]; omega)]
  congr 1

theorem levelEmbedding_fixes_firstVector (g : Mat k r') : ιLev k 1 r' g *ᵥ phiV k (1 + r') 0 = phiV k (1 + r') 0 := by
  rw [besselPhi_eq_reindexConj_rootCoords]
  exact io_bvec_out g _ (Or.inr rfl)

theorem io_phi_su (g : Mat k r') (a : Fin (r' + 1)) :
    ιLev k 1 r' g *ᵥ phiV k (1 + r') (su a) = liftVec k 1 r' (g *ᵥ phiV k r' a) := by
  rw [← phi_lift, io_lv]

def tt (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ) : Matrix (Fin (1 + r' + 1)) (Fin (1 + r' + 1)) ℂ := fun i j =>
  if i.val = 0 then (if j.val = 0 then 1 else 0)
  else if hj : j.val = 0 then 0 else τ ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩

variable (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ)

theorem tt_su (a b : Fin (r' + 1)) : tt τ (su b) (su a) = τ b a := by
  unfold tt
  rw [if_neg (by simp [su]), dite_eq_right (by simp [su])]
  congr 1 <;> ext <;> simp [su]

theorem tt_00 : tt τ 0 0 = 1 := by
  simp [tt]

theorem triangularCoeff_firstColumn_zero (b : Fin (1 + r' + 1)) (hb : b.val ≠ 0) : tt τ b 0 = 0 := by
  simp [tt, hb]

theorem tt_0su (a : Fin (r' + 1)) : tt τ 0 (su a) = 0 := by
  simp [tt, su]

theorem tt_tri (hτ : τ.BlockTriangular id) : (tt τ).BlockTriangular id := by
  intro i j hij
  simp only [id] at hij
  rw [Fin.lt_iff_val_lt_val] at hij
  unfold tt
  by_cases hi : i.val = 0
  · omega
  · rw [if_neg hi]
    by_cases hj : j.val = 0
    · rw [dite_eq_left hj]
    · rw [dite_eq_right hj]
      apply hτ
      simp only [id, Fin.mk_lt_mk]
      omega

theorem tt_rep (m κ : Mat k r') (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b))
    (a : Fin (1 + r' + 1)) :
    ιLev k 1 r' m *ᵥ phiV k (1 + r') a = ∑ b, tt τ b a • (ιLev k 1 r' κ *ᵥ phiV k (1 + r') b) := by
  by_cases ha : a.val = 0
  · have ha0 : a = 0 := Fin.ext ha
    subst ha0
    rw [levelEmbedding_fixes_firstVector, sum_su, tt_00, levelEmbedding_fixes_firstVector, one_smul]
    rw [Finset.sum_eq_zero fun b _ => by rw [triangularCoeff_firstColumn_zero τ (su b) (by simp [su]), zero_smul], add_zero]
  · obtain ⟨a', rfl⟩ := exists_su a ha
    rw [io_phi_su, hrep a', lv_sum, sum_su, tt_0su, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [tt_su, io_phi_su, lv_smul]

def suE : Fin (r' + 1) ↪ Fin (1 + r' + 1) :=
  ⟨su, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp only [su_val] at this; omega)⟩

theorem Iic_su (a : Fin (r' + 1)) : Finset.Iic (su a) = insert 0 ((Finset.Iic a).map suE) := by
  ext l
  simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_map]
  constructor
  · intro hl
    by_cases h0 : l.val = 0
    · exact Or.inl (Fin.ext h0)
    · obtain ⟨b, rfl⟩ := exists_su l h0
      refine Or.inr ⟨b, ?_, rfl⟩
      rw [Fin.le_iff_val_le_val] at hl ⊢
      rw [su_val, su_val] at hl
      omega
  · rintro (rfl | ⟨b, hb, rfl⟩)
    · exact Fin.zero_le _
    · show su b ≤ su a
      rw [Fin.le_iff_val_le_val] at hb ⊢
      rw [su_val, su_val]
      omega

theorem tt_prod0 : ∏ j ∈ Finset.Iic (0 : Fin (1 + r' + 1)), ‖tt τ j j‖ ^ 2 = 1 := by
  rw [Iic_zero, Finset.prod_singleton, tt_00]
  simp

theorem tt_prodS (a : Fin (r' + 1)) :
    ∏ j ∈ Finset.Iic (su a), ‖tt τ j j‖ ^ 2 = ∏ j ∈ Finset.Iic a, ‖τ j j‖ ^ 2 := by
  rw [Iic_su, Finset.prod_insert, Finset.prod_map, tt_00]
  · rw [norm_one, one_pow, one_mul]
    refine Finset.prod_congr rfl fun x _ => ?_
    show ‖tt τ (su x) (su x)‖ ^ 2 = _
    rw [tt_su]
  · simp only [Finset.mem_map, not_exists, not_and]
    intro b _ h
    have h' := congrArg Fin.val h
    change (su b).val = (0 : Fin (1 + r' + 1)).val at h'
    rw [su_val] at h'
    simp at h'

theorem ga_lev (x : Mat k (1 + r')) (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b)) (l : Fin (1 + r' + 1)) :
    Ga k (1 + r') l (fun a => (x * ιLev k 1 r' m) *ᵥ phiV k (1 + r') a) =
      (∏ j ∈ Finset.Iic l, ‖tt τ j j‖ ^ 2) * Ga k (1 + r') l (fun a => (x * ιLev k 1 r' κ) *ᵥ phiV k (1 + r') a) := by
  have e : (fun a => (x * ιLev k 1 r' m) *ᵥ phiV k (1 + r') a) =
      fun a => ∑ b, tt τ b a • ((x * ιLev k 1 r' κ) *ᵥ phiV k (1 + r') b) := by
    funext a
    rw [← Matrix.mulVec_mulVec, tt_rep τ m κ hrep a, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rw [e, ga_tri k (1 + r') _ (tt τ) (tt_tri τ hτ) l]

theorem levelDeterminant_of_triangular_change (x : Mat k (1 + r')) (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b)) :
    Del k (1 + r') 0 (x * ιLev k 1 r' m) = Del k (1 + r') 0 (x * ιLev k 1 r' κ) := by
  unfold Del
  rw [ga_lev τ x m κ hτ hrep 0, tt_prod0, one_mul]

theorem del_levS (x : Mat k (1 + r')) (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b))
    (hprod : ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r' l (fun a => m *ᵥ phiV k r' a)) (a : Fin (r' + 1)) :
    Del k (1 + r') (su a) (x * ιLev k 1 r' m) = Del k r' a m * Del k (1 + r') (su a) (x * ιLev k 1 r' κ) := by
  unfold Del
  rw [ga_lev τ x m κ hτ hrep (su a), tt_prodS, hprod a]
  have h0 : 0 ≤ Ga k r' a (fun b => m *ᵥ phiV k r' b) := by
    rw [← hprod a]
    exact Finset.prod_nonneg fun j _ => by positivity
  exact Real.sqrt_mul h0 _

theorem del_conj (hHC : HeisConjLev) (κ : Mat k r') (hκG : κ ∈ GV k r') (hκU : κᴴ * κ = 1) (X : HPar k r')
    (l : Fin (1 + r' + 1)) :
    Del k (1 + r') l (heis0 k r' X * ιLev k 1 r' κ) = Del k (1 + r') l (heis0 k r' (κᴴ *ᵥ X.1, X.2)) := by
  have hκU' : κ * κᴴ = 1 := by
    rw [← Matrix.inv_eq_left_inv hκU]
    exact Matrix.mul_nonsing_inv κ (Matrix.isUnit_det_of_left_inverse hκU)
  have hG' : κᴴ ∈ GV k r' := by
    have hκ : κᴴ * Hpk k r' * κ = Hpk k r' := hκG
    show κᴴᴴ * Hpk k r' * κᴴ = Hpk k r'
    rw [Matrix.conjTranspose_conjTranspose]
    calc κ * Hpk k r' * κᴴ = κ * (κᴴ * Hpk k r' * κ) * κᴴ := by rw [hκ]
      _ = (κ * κᴴ) * Hpk k r' * (κ * κᴴ) := by simp only [mul_assoc]
      _ = Hpk k r' := by rw [hκU', one_mul, mul_one]
  have hinv : (ιLev k 1 r' κᴴ)⁻¹ = ιLev k 1 r' κ :=
    Matrix.inv_eq_right_inv (by rw [← io_mul, hκU, io_one])
  have hconj := hHC k r' κᴴ hG' X
  rw [hinv] at hconj
  rw [← hconj]
  have hU : (ιLev k 1 r' κᴴ)ᴴ * ιLev k 1 r' κᴴ = 1 := by
    rw [← io_conjT, Matrix.conjTranspose_conjTranspose, ← io_mul, hκU', io_one]
  unfold Del
  rw [mul_assoc]
  have e : (fun a => (ιLev k 1 r' κᴴ * (heis0 k r' X * ιLev k 1 r' κ)) *ᵥ phiV k (1 + r') a) =
      fun a => ιLev k 1 r' κᴴ *ᵥ ((heis0 k r' X * ιLev k 1 r' κ) *ᵥ phiV k (1 + r') a) := by
    funext a
    rw [Matrix.mulVec_mulVec]
  rw [e, ga_unit k (1 + r') _ hU l]

theorem rep0 (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b)) :
    m *ᵥ phiV k r' 0 = τ 0 0 • (κ *ᵥ phiV k r' 0) := by
  rw [hrep 0, Finset.sum_eq_single 0]
  · intro b _ hb
    rw [hτ (show id (0 : Fin (r' + 1)) < id b from lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hb)),
      zero_smul]
  · intro h
    exact absurd (Finset.mem_univ 0) h

theorem lev_data (hIW : IW) (hHC : HeisConjLev) (hk : 1 ≤ k) (m : Mat k r') (hm : m ∈ UH (Hpk k r')) :
    ∃ κ : Mat k r', κ ∈ GV k r' ∧ κᴴ * κ = 1 ∧ ∃ t : ℂ, m *ᵥ phiV k r' 0 = t • (κ *ᵥ phiV k r' 0) ∧
      ‖t‖ = Del k r' 0 m ∧ ∀ X : HPar k r',
        Del k (1 + r') 0 (heis0 k r' X * ιLev k 1 r' m) = Del k (1 + r') 0 (heis0 k r' (κᴴ *ᵥ X.1, X.2)) ∧
        ∀ a : Fin (r' + 1), Del k (1 + r') (su a) (heis0 k r' X * ιLev k 1 r' m) =
          Del k r' a m * Del k (1 + r') (su a) (heis0 k r' (κᴴ *ᵥ X.1, X.2)) := by
  obtain ⟨κ, hκG, hκU, τ, hτ, hrep, hprod⟩ := iw_apply (k := k) (n := r') hIW hk m hm
  refine ⟨κ, hκG, hκU, τ 0 0, rep0 τ m κ hτ hrep, ?_, fun X => ⟨?_, fun a => ?_⟩⟩
  · unfold Del
    rw [← hprod 0, Iic_zero, Finset.prod_singleton, Real.sqrt_sq (norm_nonneg _)]
  · rw [levelDeterminant_of_triangular_change τ _ m κ hτ hrep, del_conj hHC κ hκG hκU X 0]
  · rw [del_levS τ _ m κ hτ hrep hprod a, del_conj hHC κ hκG hκU X (su a)]

end Lv

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
