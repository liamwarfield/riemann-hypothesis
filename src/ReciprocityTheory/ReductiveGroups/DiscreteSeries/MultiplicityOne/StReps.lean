module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsB
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsA
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

theorem sg_val_in {i : Fin (2 * r + k + 1)} (h : r ≤ i.val ∧ i.val ≤ r + k) : sg k r i = i := by
  simp [sg, h]

theorem sg_val_out {i : Fin (2 * r + k + 1)} (h : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) :
    (sg k r i).val = 2 * r + k - i.val := by
  simp [sg, h]

theorem sg_sg (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k
  · rw [sg_val_in h, sg_val_in h]
  · have h1 := sg_val_out h
    have h2 : ¬ (r ≤ (sg k r i).val ∧ (sg k r i).val ≤ r + k) := by
      have := i.isLt; omega
    apply Fin.ext; rw [sg_val_out h2, h1]; have := i.isLt; omega

theorem eq_sg_iff {i j : Fin (2 * r + k + 1)} : i = sg k r j ↔ j = sg k r i := by
  constructor
  · rintro rfl; rw [sg_sg]
  · rintro rfl; rw [sg_sg]

def mono {n : ℕ} (s : Fin n → Fin n) (a : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun l j => if l = s j then a j else 0

theorem mul_mono {n : ℕ} (s : Fin n → Fin n) (a : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (M * mono s a) i j = M i (s j) * a j := by
  rw [Matrix.mul_apply]
  simp only [mono, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem conjT_mono_mul {n : ℕ} (s : Fin n → Fin n) (a : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ((mono s a)ᴴ * M) i j = star (a i) * M (s i) j := by
  rw [Matrix.mul_apply]
  simp only [mono, of_apply, conjTranspose_apply, apply_ite, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def bt (k r : ℕ) (c : Fin r → ℂ) (j : Fin (2 * r + k + 1)) : ℂ :=
  if hj : j.val < r then c ⟨j.val, hj⟩
  else if hj2 : j.val ≤ r + k then 1
  else (star (c ⟨2 * r + k - j.val, by have := j.isLt; omega⟩))⁻¹

theorem bigCell_one_mono (c : Fin r → ℂ) :
    bigCell k r c 1 = mono (sg k r) (bt k r c) := by
  funext i j
  unfold bigCell bt mono; rw [of_apply]
  by_cases hj : j.val < r
  · have hs := sg_val_out (k := k) (r := r) (i := j) (by omega)
    simp only [dif_pos hj]
    congr 1
    apply propext; constructor
    · rintro rfl; apply Fin.ext; rw [hs]; simp [esI]
    · rintro rfl; apply Fin.ext; rw [hs]; simp [esI]
  · simp only [dif_neg hj]
    by_cases hj2 : j.val ≤ r + k
    · have hs := sg_val_in (k := k) (r := r) (i := j) ⟨by omega, hj2⟩
      simp only [dif_pos hj2, hs]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dif_pos hi, Matrix.one_apply]
        congr 1
        apply propext; constructor
        · intro h; apply Fin.ext; have := congrArg Fin.val h; simp at this; omega
        · rintro rfl; rfl
      · rw [dif_neg hi, if_neg]
        rintro rfl; exact hi ⟨by omega, hj2⟩
    · have hs := sg_val_out (k := k) (r := r) (i := j) (by omega)
      simp only [dif_neg hj2]
      congr 1
      apply propext; constructor
      · intro h; apply Fin.ext; rw [hs]; omega
      · rintro rfl; rw [hs]

def et (k r : ℕ) (j : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ j.val ∧ j.val ≤ r + k then (if j.val = r + k then -1 else 1) else 1

theorem Hpk_mono : Hpk k r = mono (sg k r) (et k r) := by
  funext i j
  unfold Hpk et mono; rw [of_apply]; beta_reduce
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · have hs := sg_val_in (k := k) (r := r) (i := j) hj
    rw [hs, if_pos hj]
    by_cases hij : i = j
    · subst hij
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hj.1, hj.2, rfl⟩, if_pos rfl]
    · rw [if_neg (by intro h; apply hij; apply Fin.ext; omega), if_neg (by intro h; apply hij; apply Fin.ext; omega),
        if_neg (by intro h; exact hij h.2.2), if_neg hij]
  · have hs := sg_val_out (k := k) (r := r) (i := j) hj
    rw [if_neg hj]
    by_cases hij : i = sg k r j
    · have hv : i.val = 2 * r + k - j.val := by rw [hij, hs]
      rw [if_pos hij]
      by_cases hir : i.val < r
      · rw [if_pos ⟨hir, by have := j.isLt; omega⟩]
      · rw [if_neg (by omega), if_pos ⟨by omega, by have := j.isLt; omega⟩]
    · have hv : i.val ≠ 2 * r + k - j.val := by intro h; apply hij; apply Fin.ext; rw [hs, h]
      rw [if_neg hij, if_neg (by omega), if_neg (by omega), if_neg (by intro h; apply hj; omega)]

theorem bt_sg_lt (c : Fin r → ℂ) {j : Fin (2 * r + k + 1)} (hj : j.val < r) :
    bt k r c (sg k r j) = (star (c ⟨j.val, hj⟩))⁻¹ := by
  have hs := sg_val_out (k := k) (r := r) (i := j) (by omega)
  unfold bt
  rw [dif_neg (by omega), dif_neg (by omega)]
  congr 3; apply Fin.ext; simp only [hs]; have := j.isLt; omega

theorem bt_sg_gt (c : Fin r → ℂ) {j : Fin (2 * r + k + 1)} (hj : r + k < j.val) :
    bt k r c (sg k r j) = c ⟨2 * r + k - j.val, by have := j.isLt; omega⟩ := by
  have hs := sg_val_out (k := k) (r := r) (i := j) (by omega)
  unfold bt
  rw [dif_pos (by omega)]
  congr 1; apply Fin.ext; simp only [hs]

theorem bt_gt (c : Fin r → ℂ) {j : Fin (2 * r + k + 1)} (hj : r + k < j.val) :
    bt k r c j = (star (c ⟨2 * r + k - j.val, by have := j.isLt; omega⟩))⁻¹ := by
  unfold bt; rw [dif_neg (by omega), dif_neg (by omega)]

theorem bt_lt (c : Fin r → ℂ) {j : Fin (2 * r + k + 1)} (hj : j.val < r) :
    bt k r c j = c ⟨j.val, hj⟩ := by
  unfold bt; rw [dif_pos hj]

theorem bt_in (c : Fin r → ℂ) {j : Fin (2 * r + k + 1)} (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    bt k r c j = 1 := by
  unfold bt; rw [dif_neg (by omega), dif_pos hj.2]

theorem et_out {j : Fin (2 * r + k + 1)} (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) : et k r j = 1 := by
  unfold et; rw [if_neg hj]

theorem sg_out {j : Fin (2 * r + k + 1)} (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) :
    ¬ (r ≤ (sg k r j).val ∧ (sg k r j).val ≤ r + k) := by
  rw [sg_val_out hj]; have := j.isLt; omega

theorem bigCell_one_unitary (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    (bigCell k r c 1)ᴴ * Hpk k r * bigCell k r c 1 = Hpk k r := by
  rw [bigCell_one_mono]
  ext i j
  rw [mul_mono, conjT_mono_mul, Hpk_mono]
  simp only [mono, of_apply]
  by_cases hij : i = sg k r j
  · subst hij
    rw [sg_sg, if_pos rfl, if_pos rfl]
    by_cases hj : j.val < r
    · rw [bt_sg_lt c hj, bt_lt c hj, et_out (sg_out (by omega)), et_out (by omega)]
      rw [star_inv₀, star_star, mul_one]; exact inv_mul_cancel₀ (hc _)
    · by_cases hj2 : j.val ≤ r + k
      · rw [sg_val_in ⟨by omega, hj2⟩, bt_in c ⟨by omega, hj2⟩]; simp
      · rw [bt_sg_gt c (by omega), bt_gt c (by omega), et_out (sg_out (by omega)), et_out (by omega), mul_one]
        exact mul_inv_cancel₀ (by rw [Ne, star_eq_zero]; exact hc _)
  · rw [if_neg hij, if_neg, mul_zero, zero_mul]
    intro h; apply hij; simpa only [sg_sg] using congrArg (sg k r) h

theorem bigCell_star_mul (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    bigCell k r (star c) 1 * bigCell k r c 1 = 1 := by
  rw [bigCell_one_mono, bigCell_one_mono]
  ext i j
  rw [mul_mono]
  simp only [mono, of_apply, sg_sg, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl]
    by_cases hj : i.val < r
    · rw [bt_sg_lt _ hj, bt_lt c hj]; simp only [Pi.star_apply, star_star]; exact inv_mul_cancel₀ (hc _)
    · by_cases hj2 : i.val ≤ r + k
      · rw [sg_val_in ⟨by omega, hj2⟩, bt_in _ ⟨by omega, hj2⟩, bt_in _ ⟨by omega, hj2⟩, mul_one]
      · rw [bt_sg_gt _ (by omega), bt_gt c (by omega)]; simp only [Pi.star_apply]
        exact mul_inv_cancel₀ (by rw [Ne, star_eq_zero]; exact hc _)
  · rw [if_neg hij, if_neg hij, zero_mul]

theorem bigCell_map_conj (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (bigCell k r c μ).map (starRingEnd ℂ) = bigCell k r (star c) (μ.map (starRingEnd ℂ)) := by
  ext i j
  simp only [map_apply, bigCell, Pi.star_apply]
  split_ifs <;> simp

def wbE (k r : ℕ) (v : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val ≤ r + k then v ⟨i.val - r, by omega⟩ else 0

theorem wI_val' (j : Fin (k + 1)) : (wI k r j).val = r + j.val := rfl

theorem wI_in (j : Fin (k + 1)) : r ≤ (wI k r j).val ∧ (wI k r j).val ≤ r + k := by
  rw [wI_val']; have := j.isLt; omega

theorem wI_sub (j : Fin (k + 1)) : (⟨(wI k r j).val - r, by rw [wI_val']; omega⟩ : Fin (k + 1)) = j := by
  apply Fin.ext; simp [wI_val']

theorem wbE_wI (v : Fin (k + 1) → ℂ) (j : Fin (k + 1)) : wbE k r v (wI k r j) = v j := by
  unfold wbE; rw [dif_pos (wI_in j)]; congr 1; exact wI_sub j

theorem sum_wb {f : Fin (2 * r + k + 1) → ℂ} (hf : ∀ i : Fin (2 * r + k + 1), ¬ (r ≤ i.val ∧ i.val ≤ r + k) → f i = 0) :
    ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by
  have hinj : Function.Injective (wI k r) := by
    intro a b h; apply Fin.ext; have := congrArg Fin.val h; rw [wI_val', wI_val'] at this; omega
  rw [show (∑ j : Fin (k + 1), f (wI k r j)) = ∑ i ∈ Finset.univ.map ⟨wI k r, hinj⟩, f i from (Finset.sum_map Finset.univ ⟨wI k r, hinj⟩ f).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hf
  intro h
  apply hi
  refine Finset.mem_map.2 ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _, ?_⟩
  apply Fin.ext; simp only [Function.Embedding.coeFn_mk, wI_val']; omega

theorem embWb_in (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : r ≤ i.val ∧ i.val ≤ r + k) (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    embWb k r X i j = X ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ := by
  unfold embWb; rw [dif_pos ⟨hi, hj⟩]

theorem embWb_out_left (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) : embWb k r X i j = if i = j then 1 else 0 := by
  unfold embWb; rw [dif_neg (fun h => hi h.1)]
  by_cases h : i = j
  · rw [if_pos ⟨h, hi⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

theorem embWb_out_right (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (2 * r + k + 1)}
    (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) : embWb k r X i j = if i = j then 1 else 0 := by
  unfold embWb; rw [dif_neg (fun h => hj h.2)]
  by_cases h : i = j
  · subst h; rw [if_pos ⟨rfl, hj⟩, if_pos rfl]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

theorem embWb_mulVec (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (k + 1) → ℂ) :
    embWb k r X *ᵥ wbE k r v = wbE k r (X *ᵥ v) := by
  funext i
  simp only [mulVec, dotProduct]
  rw [sum_wb (f := fun l => embWb k r X i l * wbE k r v l) (by intro l hl; simp [wbE, hl])]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · simp only [wbE_wI, embWb_in X hi (wI_in _), wI_sub]
    unfold wbE; rw [dif_pos hi]; rfl
  · simp only [embWb_out_left X hi]
    unfold wbE; rw [dif_neg hi]
    apply Finset.sum_eq_zero; intro j _
    rw [if_neg (fun h : i = wI k r j => hi (h ▸ wI_in j)), zero_mul]

theorem embWb_mul (X Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r (X * Y) = embWb k r X * embWb k r Y := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [sum_wb (f := fun l => embWb k r X i l * embWb k r Y l j)
        (by intro l hl; show embWb k r X i l * embWb k r Y l j = 0; rw [embWb_out_right X hl, if_neg (fun h : i = l => hl (h ▸ hi)), zero_mul])]
      simp only [embWb_in _ hi hj, embWb_in _ hi (wI_in _), embWb_in _ (wI_in _) hj, wI_sub, Matrix.mul_apply]
    · simp only [embWb_out_right _ hj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [embWb_out_left _ hi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem embWb_one : embWb k r (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [embWb_in _ hi hj, Matrix.one_apply]
      congr 1; apply propext; constructor
      · intro h; apply Fin.ext; have := congrArg Fin.val h; simp at this; omega
      · rintro rfl; rfl
    · rw [embWb_out_right _ hj]
  · rw [embWb_out_left _ hi]

theorem Hpk_mulVec_wbE (u : Fin (k + 1) → ℂ) : Hpk k r *ᵥ wbE k r u = wbE k r (Hb k *ᵥ u) := by
  funext i
  rw [Hpk_mono]
  simp only [mulVec, dotProduct, mono, of_apply, ite_mul, zero_mul]
  simp only [eq_sg_iff (i := i), Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · rw [sg_val_in hi]
    unfold wbE et Hb; rw [dif_pos hi, dif_pos hi, if_pos hi, mulVec_diagonal]
    congr 1; congr 1; apply propext; constructor
    · intro h; apply Fin.ext; simp; omega
    · intro h; have := congrArg Fin.val h; simp at this; omega
  · have h2 := sg_out (k := k) (r := r) hi
    unfold wbE; rw [dif_neg h2, dif_neg hi, mul_zero]

theorem herm_wbE (u v : Fin (k + 1) → ℂ) : herm (Hpk k r) (wbE k r u) (wbE k r v) = herm (Hb k) u v := by
  unfold herm
  rw [Hpk_mulVec_wbE]
  simp only [dotProduct, Pi.star_apply]
  rw [sum_wb (f := fun l => star (wbE k r v l) * wbE k r (Hb k *ᵥ u) l) (by intro l hl; simp [wbE, hl])]
  simp only [wbE_wI]

end ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA
end
end

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k : ℕ}

theorem zero_ne_last (hk : 1 ≤ k) : (0 : Fin (k + 1)) ≠ Fin.last k := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at h2
  omega

def sgd (d : ℂ) : ℂ := ((Real.sqrt (Complex.normSq d - 1) : ℝ) : ℂ)

theorem sgd_sq (d : ℂ) (hd : 1 < ‖d‖) : sgd d * sgd d = d * conj d - 1 := by
  have hx : 0 ≤ Complex.normSq d - 1 := by
    have h1 : 1 < Complex.normSq d := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg d]
    linarith
  unfold sgd
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx, Complex.mul_conj, Complex.ofReal_sub, Complex.ofReal_one]

theorem star_sgd (d : ℂ) : star (sgd d) = sgd d := by
  unfold sgd
  exact Complex.conj_ofReal _

section entries
variable (hk : 1 ≤ k) (d : ℂ)
include hk

theorem character_first_entry : mud k d 0 0 = -conj d := by
  unfold mud
  simp
theorem character_last_entry : mud k d (Fin.last k) 0 = -sgd d := by
  have h0 := zero_ne_last hk
  unfold mud sgd
  rw [if_neg (fun h => h0 h.1.symm), if_pos ⟨rfl, rfl⟩]
theorem mud0L : mud k d 0 (Fin.last k) = sgd d := by
  have h0 := zero_ne_last hk
  unfold mud sgd
  rw [if_neg (fun h => h0 h.2.symm), if_neg (fun h => h0 h.1), if_pos ⟨rfl, rfl⟩]
theorem mudLL : mud k d (Fin.last k) (Fin.last k) = d := by
  have h0 := zero_ne_last hk
  unfold mud
  rw [if_neg (fun h => h0 h.1.symm), if_neg (fun h => h0 h.2.symm), if_neg (fun h => h0 h.1.symm),
    if_pos ⟨rfl, rfl⟩]

theorem mud_col {l j : Fin (k + 1)} (hj0 : j ≠ 0) (hjL : j ≠ Fin.last k) :
    mud k d l j = if l = j then 1 else 0 := by
  unfold mud
  rw [if_neg (fun h => hj0 h.2), if_neg (fun h => hj0 h.2), if_neg (fun h => hjL h.2),
    if_neg (fun h => hjL h.2)]

theorem mud_row {l j : Fin (k + 1)} (hl0 : l ≠ 0) (hlL : l ≠ Fin.last k) :
    mud k d l j = if l = j then 1 else 0 := by
  unfold mud
  rw [if_neg (fun h => hl0 h.1), if_neg (fun h => hlL h.1), if_neg (fun h => hl0 h.1),
    if_neg (fun h => hlL h.1)]

theorem sum_two {f : Fin (k + 1) → ℂ} (hf : ∀ l, l ≠ 0 → l ≠ Fin.last k → f l = 0) :
    ∑ l, f l = f 0 + f (Fin.last k) := Finset.sum_eq_add 0 (Fin.last k) (zero_ne_last hk) (fun c _ hc => hf c hc.1 hc.2)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)

theorem mul_mud_col (P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (k + 1)} (hj0 : j ≠ 0)
    (hjL : j ≠ Fin.last k) : (P * mud k d) i j = P i j := by
  rw [Matrix.mul_apply]
  simp [mud_col hk d hj0 hjL]

theorem mul_mud_blk (P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) (hj : j = 0 ∨ j = Fin.last k) :
    (P * mud k d) i j = P i 0 * mud k d 0 j + P i (Fin.last k) * mud k d (Fin.last k) j := by
  rw [Matrix.mul_apply]
  apply sum_two hk
  intro l hl0 hlL
  rw [mud_row hk d hl0 hlL, if_neg, mul_zero]
  rintro rfl
  rcases hj with h | h
  · exact hl0 h
  · exact hlL h

end entries

theorem Hb_apply (i j : Fin (k + 1)) : Hb k i j = if i = j then (if i = Fin.last k then -1 else 1) else 0 := by
  unfold Hb
  rw [Matrix.diagonal_apply]

theorem mud_unitary (hk : 1 ≤ k) (d : ℂ) (hd : 1 < ‖d‖) : (mud k d)ᴴ * Hb k * mud k d = Hb k := by
  have hs := sgd_sq d hd
  have hss := star_sgd d
  have h0L := zero_ne_last hk
  ext i j
  have hP : ∀ a b : Fin (k + 1), ((mud k d)ᴴ * Hb k) a b = star (mud k d b a) * (if b = Fin.last k then -1 else 1) := by
    intro a b; unfold Hb; rw [mul_diagonal, conjTranspose_apply]
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [mul_mud_blk hk d _ _ _ (Or.inl rfl), hP, hP, Hb_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, character_last_entry hk, if_true, if_neg h0L, if_neg h0L.symm, star_neg, hss, Complex.star_def, Complex.conj_conj]
      linear_combination -hs
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [mud0L hk, mudLL hk, character_first_entry hk, character_last_entry hk, if_true, if_neg h0L, if_neg h0L.symm, hss,
        Complex.star_def]
      ring
    · simp only [mud_col hk d hi0 hiL, if_neg (Ne.symm hi0), if_neg (Ne.symm hiL), if_neg hi0]
      simp
  rcases eq_or_ne j (Fin.last k) with rfl | hjL
  · rw [mul_mud_blk hk d _ _ _ (Or.inr rfl), hP, hP, Hb_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, character_last_entry hk, mud0L hk, mudLL hk, if_true, if_neg h0L, if_neg h0L.symm, star_neg, hss, Complex.star_def,
        Complex.conj_conj]
      ring
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [mud0L hk, mudLL hk, if_true, if_neg h0L, if_neg h0L.symm, hss, Complex.star_def]
      linear_combination hs
    · simp only [mud_col hk d hi0 hiL, if_neg (Ne.symm hi0), if_neg (Ne.symm hiL), if_neg hiL]
      simp
  · rw [mul_mud_col hk d _ hj0 hjL, hP, mud_row hk d hj0 hjL, Hb_apply]
    by_cases hij : i = j
    · subst hij; simp [hjL]
    · rw [if_neg (Ne.symm hij), if_neg hij]; simp

theorem mud_conj_mul (hk : 1 ≤ k) (d : ℂ) (hd : 1 < ‖d‖) : (mud k d).map (starRingEnd ℂ) * mud k d = 1 := by
  have hs := sgd_sq d hd
  have hss := star_sgd d
  have h0L := zero_ne_last hk
  have hc : ∀ a b : Fin (k + 1), ((mud k d).map (starRingEnd ℂ)) a b = conj (mud k d a b) := fun a b => rfl
  have hsc : conj (sgd d) = sgd d := hss
  ext i j
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [mul_mud_blk hk d _ _ _ (Or.inl rfl), hc, hc, Matrix.one_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, mud0L hk, character_last_entry hk, if_true, map_neg, hsc, Complex.conj_conj]
      linear_combination -hs
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [character_last_entry hk, mudLL hk, character_first_entry hk, if_neg h0L.symm, map_neg, hsc]
      ring
    · simp only [mud_row hk d hi0 hiL, if_neg hi0, if_neg hiL]
      simp
  rcases eq_or_ne j (Fin.last k) with rfl | hjL
  · rw [mul_mud_blk hk d _ _ _ (Or.inr rfl), hc, hc, Matrix.one_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, mud0L hk, mudLL hk, if_neg h0L, if_neg h0L.symm, map_neg, hsc, Complex.conj_conj]
      ring
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [character_last_entry hk, mudLL hk, mud0L hk, if_true, map_neg, hsc]
      linear_combination -hs
    · simp only [mud_row hk d hi0 hiL, if_neg hi0, if_neg hiL]
      simp
  · rw [mul_mud_col hk d _ hj0 hjL, hc, mud_col hk d hj0 hjL, Matrix.one_apply]
    split_ifs <;> simp

theorem herm_mulVec {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    herm H (A *ᵥ u) (A *ᵥ v) = herm (Aᴴ * H * A) u v := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem herm_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b : ℂ) (u v : Fin n → ℂ) :
    herm H (a • u) (b • v) = a * conj b * herm H u v := by
  unfold herm
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
  ring

theorem herm_mud_last (hk : 1 ≤ k) (d : ℂ) :
    herm (Hb k) (mud k d *ᵥ Pi.single (Fin.last k) 1) (Pi.single (Fin.last k) 1) = -d := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_eq_single (Fin.last k)]
  · simp [Pi.single_apply, Hb_apply, mudLL hk d]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wbE_smul {r : ℕ} (a : ℂ) (v : Fin (k + 1) → ℂ) : wbE k r (a • v) = a • wbE k r v := by
  funext i
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k <;> simp [wbE, h]

theorem bvec_wI {r : ℕ} (j : Fin (k + 1)) : bvec (wI k r j) = wbE k r (Pi.single j 1) := by
  funext i
  simp only [bvec, wI, wbE, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

end ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA
end
end

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 RepsA

theorem stReps (h : UnitaryGroupStructuralFacts) : StReps := by
  obtain ⟨hB2, -, hRC, hBCF, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClG, -, hClW, -⟩ := hB2
  intro k r Wp _ _ _ D X hD _ γ hγ c d hc hd
  have hk := D.k_pos
  obtain ⟨hγu, hγz⟩ := hγ
  have hT : 0 < Tz k r D.z := D.T_pos

  have hdet : IsUnit γ.det := by
    have h1 := congrArg Matrix.det hγu
    rw [det_mul, det_mul, det_conjTranspose] at h1
    have hHb : (Hb k).det = -1 := by
      unfold Hb; rw [det_diagonal, Finset.prod_ite_eq' Finset.univ (Fin.last k) (fun _ => (-1 : ℂ))]
      simp
    rw [hHb] at h1
    rw [isUnit_iff_ne_zero]; intro h0; rw [h0] at h1; simp at h1
  have hγi : γ⁻¹ * γ = 1 := nonsing_inv_mul γ hdet
  have hγi' : γ * γ⁻¹ = 1 := mul_nonsing_inv γ hdet
  have hHbi : (γ⁻¹)ᴴ * Hb k * γ⁻¹ = Hb k := by
    calc (γ⁻¹)ᴴ * Hb k * γ⁻¹ = (γ⁻¹)ᴴ * (γᴴ * Hb k * γ) * γ⁻¹ := by rw [hγu]
      _ = (γ * γ⁻¹)ᴴ * Hb k * (γ * γ⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hb k := by rw [hγi']; simp
  set μ := mud k d with hμ
  set M := γ * μ * γ⁻¹ with hM
  have hμu : μᴴ * Hb k * μ = Hb k := mud_unitary hk d hd

  have h1 : Mᴴ * Hb k * M = Hb k := by
    rw [show Mᴴ * Hb k * M = (γ⁻¹)ᴴ * (μᴴ * (γᴴ * Hb k * γ) * μ) * γ⁻¹ by
      simp only [hM, conjTranspose_mul, Matrix.mul_assoc]]
    rw [hγu, hμu, hHbi]

  set s : ℝ := Real.sqrt (Tz k r D.z) with hs
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 hT).ne'
  have hzE : D.z = wbE k r ((s : ℂ) • (γ *ᵥ Pi.single (Fin.last k) 1)) := by
    rw [wbE_smul, ← embWb_mulVec, ← bvec_wI, hγz, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0,
      Complex.ofReal_one, one_smul]
  have hMγ : M * γ = γ * μ := by rw [hM, Matrix.mul_assoc, hγi, Matrix.mul_one]
  have h2 : herm (Hpk k r) (embWb k r M *ᵥ D.z) D.z = -((Tz k r D.z : ℝ) : ℂ) * d := by
    conv_lhs => rw [hzE]
    rw [embWb_mulVec, herm_wbE, mulVec_smul, mulVec_mulVec, hMγ, ← mulVec_mulVec, herm_smul, herm_mulVec, hγu,
      herm_mud_last hk d, Complex.conj_ofReal, ← Complex.ofReal_mul, hs, Real.mul_self_sqrt hT.le]
    ring

  have hB1 : bigCell k r c 1 ∈ GV k r := bigCell_one_unitary c hc
  have hEM : embWb k r M ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨M, h1, rfl⟩
  have hg0 : g0 k r γ c d = bigCell k r c 1 * embWb k r M := (hBCF k r c M).1
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rw [hg0]; exact (hClG k r).mul_mem _ hB1 _ hEM.1
  · set Γ := embWb k r γ with hΓdef
    set Γi := embWb k r γ⁻¹ with hΓidef
    have hΓΓi : Γ * Γi = 1 := by rw [hΓdef, hΓidef, ← embWb_mul, hγi', embWb_one]
    have hΓiΓ : Γi * Γ = 1 := by rw [hΓdef, hΓidef, ← embWb_mul, hγi, embWb_one]
    have hΓinv : Γ⁻¹ = Γi := inv_eq_right_inv hΓΓi
    have hΓW : Γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγu, rfl⟩
    have hΓiW : Γi ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ⁻¹, hHbi, rfl⟩
    have hconjM : ∀ N, embWb k r (γ * N * γ⁻¹) = Γ * embWb k r N * Γi := by
      intro N; rw [embWb_mul, embWb_mul]
    have e1 : Γi * g0 k r γ c d * Γ = bigCell k r c μ := by
      rw [hg0, hM, hconjM, (hBCF k r c μ).1]
      rw [show Γi * (bigCell k r c 1 * (Γ * embWb k r μ * Γi)) * Γ =
          (Γi * bigCell k r c 1) * Γ * embWb k r μ * (Γi * Γ) by simp only [Matrix.mul_assoc]]
      rw [(hUWb k r).2.2 c Γi hΓiW, Matrix.mul_assoc (bigCell k r c 1) Γi Γ, hΓiΓ, Matrix.mul_one, Matrix.mul_one]
    have e2 : gbar k r γ (g0 k r γ c d) =
        bigCell k r (star c) 1 * embWb k r (γ * μ.map (starRingEnd ℂ) * γ⁻¹) := by
      unfold gbar
      rw [hΓinv, e1, bigCell_map_conj, (hBCF k r (star c) _).1, hconjM, ← Matrix.mul_assoc Γ,
        (hUWb k r).2.2 (star c) Γ hΓW]
      simp only [Matrix.mul_assoc]
    have hB1' : bigCell k r (star c) 1 * bigCell k r c 1 = 1 := bigCell_star_mul c hc
    have hμc : μ.map (starRingEnd ℂ) * μ = 1 := mud_conj_mul hk d hd
    have hE : embWb k r (γ * μ.map (starRingEnd ℂ) * γ⁻¹) * embWb k r M = 1 := by
      rw [← embWb_mul, hM, show γ * μ.map (starRingEnd ℂ) * γ⁻¹ * (γ * μ * γ⁻¹) =
          γ * (μ.map (starRingEnd ℂ) * μ) * γ⁻¹ by
            simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc γ⁻¹ γ, hγi, Matrix.one_mul],
        hμc, Matrix.mul_one, hγi', embWb_one]
    have hg0' : g0 k r γ c d = embWb k r M * bigCell k r c 1 := (hBCF k r c M).2
    unfold th
    rw [e2, Matrix.mul_inv_rev, inv_eq_right_inv hE, inv_eq_right_inv hB1', hg0']
  · have hz' : D.z' = D.z := hD.z_eq
    have hcond : Tz k r D.z * Tz k r D.z' <
        Complex.normSq (herm (Hpk k r) (embWb k r M *ᵥ D.z') D.z) := by
      rw [hz', h2, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal]
      have h1d : 1 < Complex.normSq d := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg d]
      have hTT : 0 < Tz k r D.z * Tz k r D.z := mul_pos hT hT
      nlinarith
    obtain ⟨h, hh, h', hh', hm⟩ :=
      hRC k r D.z D.z' D.μsec hk D.z_mem D.z'_mem D.T_pos D.T'_pos D.sec (embWb k r M) hEM hcond
    rw [hz', h2] at hm
    rw [hz'] at hh'
    have hu := (hClW k r D.z).unit h hh
    have hu' := (hClW k r D.z).unit h' hh'
    refine ⟨h⁻¹, (hClW k r D.z).inv_mem h hh, h'⁻¹, (hClW k r D.z).inv_mem h' hh', ?_⟩
    rw [nonsing_inv_nonsing_inv h hu]
    show bigCell k r c (D.μsec (-((Tz k r D.z : ℝ) : ℂ) * d)) = h * g0 k r γ c d * h'⁻¹
    have hE : embWb k r (D.μsec (-((Tz k r D.z : ℝ) : ℂ) * d)) = h * embWb k r M * h'⁻¹ := by
      rw [hm]; simp only [← Matrix.mul_assoc]
      rw [mul_nonsing_inv h hu, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv h' hu', Matrix.mul_one]
    have hcm := (hUWb k r).2.2 c h ((hUWb k r).2.1 D.z hh)
    rw [(hBCF k r c _).1, hE, hg0]
    simp only [← Matrix.mul_assoc]
    rw [← hcm]

end ReciprocityTheory.ChartRestriction.DS.Mult1
