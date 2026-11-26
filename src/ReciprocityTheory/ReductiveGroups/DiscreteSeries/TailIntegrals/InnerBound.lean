module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LevelDeterminantOfTriangularChange

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.MpUnitary
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermExpand
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianFormLiftVecFirstVector
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem ell_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    ell k r z g = ∑ a : Fin r, (g *ᵥ fvec k r z ⟨a.val + 1, by omega⟩) (eI k r a) := by
  unfold ell
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a.val + 1 < r
  · rw [dif_pos h]
    first
      | simp [fvec, h, bvec, Matrix.mulVec_single_one]
      | simp [fvec, h, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  · rw [dif_neg h]
    simp [fvec, h]

section Lv2
variable {k r' : ℕ}

theorem hpk_sh (p q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') (sh p) (sh q) = Hpk k r' p q := by
  simp only [Hpk, sh, Fin.ext_iff, Fin.val_mk]
  have e1 : (p.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔
      (p.val < r' ∧ p.val + q.val = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e2 : (q.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔
      (q.val < r' ∧ p.val + q.val = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e3 : (1 + r' ≤ p.val + 1 ∧ p.val + 1 ≤ 1 + r' + k ∧ p.val + 1 = q.val + 1) ↔
      (r' ≤ p.val ∧ p.val ≤ r' + k ∧ p.val = q.val) := by
    constructor <;> intro h <;> omega
  have e4 : (p.val + 1 = 1 + r' + k) ↔ (p.val = r' + k) := by
    constructor <;> intro h <;> omega
  simp only [e1, e2, e3, e4]

theorem hpk_out (p : Fin (2 * (1 + r') + k + 1)) (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k)
    (q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') p (sh q) = 0 := by
  have := p.isLt
  have := q.isLt
  simp only [Hpk, sh, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

private lemma sum_eq_sum_sh_of_zero_at_edges (F : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hF : ∀ p : Fin (2 * (1 + r') + k + 1), (p.val = 0 ∨ p.val = 2 * (1 + r') + k) → F p = 0) :
    ∑ p, F p = ∑ q : Fin (2 * r' + k + 1), F (sh q) := by
  have hinj : Function.Injective (fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1))) := by
    intro a b h
    simp only [sh, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  rw [show ∑ q : Fin (2 * r' + k + 1), F (sh q) =
      ∑ p ∈ Finset.univ.map ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩, F p
      from (Finset.sum_map Finset.univ
        ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩ F).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hF
  by_contra hc
  apply hp
  have := p.isLt
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  refine ⟨⟨p.val - 1, by omega⟩, ?_⟩
  ext
  simp only [sh, Fin.val_mk]
  omega

private lemma liftVec_apply_sh (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (sh q) = v q := by
  have h1 : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [liftVec]
  rw [dif_pos h1]
  exact congrArg v (Fin.ext (by simp [sh]))

theorem hpk_lv (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' v = liftVec k 1 r' (Hpk k r' *ᵥ v) := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro j hj
    have h0 : ¬(1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]
    by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
    · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
      simp only [hpk_out p hp, zero_mul, Finset.sum_const_zero, liftVec, dif_neg h0]
    · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
        ext
        simp only [sh, Fin.val_mk]
        omega
      rw [hp']
      simp only [hpk_sh, liftVec_apply_sh, Matrix.mulVec, dotProduct]

theorem herm_lv (v w : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' v) (liftVec k 1 r' w) = herm (Hpk k r') v w := by
  unfold herm
  rw [hpk_lv]
  simp only [dotProduct, Pi.star_apply]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro p hp
    have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]

theorem hermitianForm_liftVec_firstVector (v : Fin (2 * r' + k + 1) → ℂ) : herm (Hpk k (1 + r')) (liftVec k 1 r' v) (e0 k r') = 0 := by
  unfold herm
  rw [hpk_lv]
  simp [e0, bvec, dotProduct, Pi.single_apply, liftVec, eI, a0]
  apply Finset.sum_eq_zero
  intro x _
  split_ifs with h1 h2 <;> first | rfl | (rw [h2] at h1; simp at h1)

theorem firstVector_apply_first (h : 0 < 1 + r') : e0 k r' (eI k (1 + r') ⟨0, h⟩) = 1 := by
  simp [e0, bvec, a0, eI]

theorem firstVector_apply_succ (b : ℕ) (h : b + 1 < 1 + r') : e0 k r' (eI k (1 + r') ⟨b + 1, h⟩) = 0 := by
  simp [e0, bvec, a0, eI, Pi.single_apply]

theorem eI_succ (b : ℕ) (h : b + 1 < 1 + r') : eI k (1 + r') ⟨b + 1, h⟩ = sh (eI k r' ⟨b, by omega⟩) := by
  ext
  simp [eI, sh]

private lemma lev_apply_sh_sh (m : Mat k r') (p q : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' m (sh p) (sh q) = m p q := by
  have hp : 1 ≤ (sh p : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh p : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := p.isLt
    simp only [sh, Fin.val_mk]
    omega
  have hq : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [ιLev]
  rw [dif_pos hp, dif_pos hq]
  exact congrArg₂ m (Fin.ext (by simp [sh])) (Fin.ext (by simp [sh]))

private lemma lev_mulVec_liftVec_eq_liftVec_mulVec (m : Mat k r') (w : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' m *ᵥ liftVec k 1 r' w = liftVec k 1 r' (m *ᵥ w) := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro j hj
    have h0 : ¬(1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]
    by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
    · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
      have hz : ∀ q : Fin (2 * r' + k + 1), ιLev k 1 r' m p (sh q) = 0 := by
        intro q
        have hne : p ≠ sh q := by
          intro he
          rw [he] at hp
          have := q.isLt
          simp only [sh, Fin.val_mk] at hp
          omega
        simp only [ιLev, dif_neg h0, if_neg hne]
      simp only [hz, zero_mul, Finset.sum_const_zero, liftVec, dif_neg h0]
    · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
        ext
        simp only [sh, Fin.val_mk]
        omega
      rw [hp']
      simp only [lev_apply_sh_sh, liftVec_apply_sh, Matrix.mulVec, dotProduct]

theorem hcol (hHA : HeisAct) (m : Mat k r') (X : HPar k r') (w : Fin (2 * r' + k + 1) → ℂ) :
    (heis0 k r' X * ιLev k 1 r' m) *ᵥ liftVec k 1 r' w =
      liftVec k 1 r' (m *ᵥ w) - herm (Hpk k r') (m *ᵥ w) X.1 • e0 k r' := by
  unfold HeisAct at hHA
  rw [← Matrix.mulVec_mulVec, lev_mulVec_liftVec_eq_liftVec_mulVec]
  unfold heis0
  rw [hHA, herm_lv, hermitianForm_liftVec_firstVector, zero_smul, add_zero]

theorem sum_fin_one_add_eq_add_sum {M : Type} [AddCommMonoid M] (F : Fin (1 + r') → M) :
    ∑ a, F a = F ⟨0, by omega⟩ + ∑ a' : Fin r', F ⟨a'.val + 1, by omega⟩ := by
  rw [← Fintype.sum_equiv (finCongr (Nat.add_comm r' 1))
    (fun a : Fin (r' + 1) => F (finCongr (Nat.add_comm r' 1) a)) F (fun _ => rfl), Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg F (Fin.ext (by simp))
  · exact Finset.sum_congr rfl fun a _ => congrArg F (Fin.ext (by simp))

private lemma liftVec_bvec_eq_bvec_sh (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' (bvec i) = bvec (sh i) := by
  funext p
  by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
  · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    have hne : p ≠ sh i := by
      intro he
      rw [he] at hp
      have := i.isLt
      simp only [sh, Fin.val_mk] at hp
      omega
    simp only [liftVec, dif_neg h0, bvec, Pi.single_apply, if_neg hne]
  · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
      ext
      simp only [sh, Fin.val_mk]
      omega
    rw [hp', liftVec_apply_sh]
    simp [bvec, Pi.single_apply, sh, Fin.ext_iff]

theorem fvec_lift (z1 : Fin (2 * r' + k + 1) → ℂ) (a : Fin (1 + r')) :
    fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩ = liftVec k 1 r' (fvec k r' z1 ⟨a.val, by omega⟩) := by
  by_cases ha : a.val < r'
  · have h1 : a.val + 1 < 1 + r' := by omega
    simp only [fvec, Fin.val_mk, dif_pos h1, dif_pos ha]
    rw [eI_succ a.val h1]
    exact (liftVec_bvec_eq_bvec_sh _).symm
  · have h1 : ¬ a.val + 1 < 1 + r' := by omega
    simp only [fvec, Fin.val_mk, dif_neg h1, dif_neg ha]

private lemma liftVec_apply_eI_zero_eq_zero (v : Fin (2 * r' + k + 1) → ℂ) (h : 0 < 1 + r') :
    liftVec k 1 r' v (eI k (1 + r') ⟨0, h⟩) = 0 := by
  simp [liftVec, eI]

theorem ell_lev (hHA : HeisAct) (z1 : Fin (2 * r' + k + 1) → ℂ) (m : Mat k r') (X : HPar k r') :
    ell k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
      -herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) X.1 + ell k r' z1 m := by
  have key : ∀ a : Fin (1 + r'),
      ((heis0 k r' X * ιLev k 1 r' m) *ᵥ fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩)
        (eI k (1 + r') a) =
      liftVec k 1 r' (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) (eI k (1 + r') a) -
        herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) X.1 * e0 k r' (eI k (1 + r') a) := by
    intro a
    rw [fvec_lift, hcol hHA]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ell_col, ell_col, sum_fin_one_add_eq_add_sum]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun a' _ => ?_)
  · beta_reduce
    rw [key, firstVector_apply_first, liftVec_apply_eI_zero_eq_zero, mul_one, zero_sub]
  · beta_reduce
    rw [key, firstVector_apply_succ, mul_zero, sub_zero, eI_succ, liftVec_apply_sh]

theorem lam_lev (hHA : HeisAct) (z1 : Fin (2 * r' + k + 1) → ℂ) (m : Mat k r') (X : HPar k r') :
    lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
      -2 * (herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) X.1).im + lam k r' z1 m := by
  simp only [lam, cStd]
  rw [ell_lev hHA]
  simp only [mul_add, mul_neg, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_im]
  norm_num

theorem z_lift (z : Fin (2 * (1 + r') + k + 1) → ℂ) (hz : inWb k (1 + r') z) :
    z = liftVec k 1 r' (fun q => z (sh q)) := by
  unfold inWb at hz
  funext p
  by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
  · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    rw [hz p (by omega)]
    simp only [liftVec, dif_neg h0]
  · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
      ext
      simp only [sh, Fin.val_mk]
      omega
    rw [hp', liftVec_apply_sh]

theorem shifted_mem_weightSpace (z : Fin (2 * (1 + r') + k + 1) → ℂ) (hz : inWb k (1 + r') z) : inWb k r' (fun q => z (sh q)) := by
  unfold inWb at hz ⊢
  intro i hi
  have := i.isLt
  exact hz (sh i) (by simp only [sh, Fin.val_mk]; omega)

theorem tz_lift (z1 : Fin (2 * r' + k + 1) → ℂ) : Tz k (1 + r') (liftVec k 1 r' z1) = Tz k r' z1 := by
  unfold Tz
  rw [herm_lv]

end Lv2

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

theorem herm_conj {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (v w : Fin n → ℂ) :
    star (herm H v w) = herm H w v := by
  have h : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this
  unfold herm
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h]; ring

theorem dot_bvec_r {n : ℕ} (i : Fin n) (x : Fin n → ℂ) : x ⬝ᵥ bvec i = x i := by
  simp [bvec]

section ex
variable (k n : ℕ)

def wp (i : Fin (k - 1)) : Fin (2 * n + k + 1) := wI k n ⟨i.val + 1, by omega⟩

def wv (i : Fin (k - 1)) : Fin (2 * n + k + 1) → ℂ := bvec (wp k n i)

theorem wp_val (i : Fin (k - 1)) : (wp k n i).val = n + (i.val + 1) := rfl

private theorem Hpk_apply_wp_eq_ite (i : Fin (k - 1)) (j : Fin (2 * n + k + 1)) :
    Hpk k n (wp k n i) j = if wp k n i = j then 1 else 0 := by
  have hi := i.isLt
  have hv := wp_val k n i
  have hj := j.isLt
  have hij : wp k n i = j ↔ (wp k n i).val = j.val := Fin.ext_iff
  unfold Hpk
  by_cases h : (wp k n i).val = j.val
  · rw [if_pos (hij.2 h), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, hij.2 h⟩,
      if_neg (by omega)]
  · rw [if_neg (fun he => h (hij.1 he)), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem hpk_mv_w (i : Fin (k - 1)) (y : Fin (2 * n + k + 1) → ℂ) : (Hpk k n *ᵥ y) (wp k n i) = y (wp k n i) := by
  simp only [mulVec, dotProduct, Hpk_apply_wp_eq_ite, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem hpk_bvec_w (i : Fin (k - 1)) : Hpk k n *ᵥ wv k n i = wv k n i := by
  funext p
  have hc : Hpk k n p (wp k n i) = star (Hpk k n (wp k n i) p) := by
    have := congrFun (congrFun (hpk_conjT k n) p) (wp k n i)
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  simp only [wv, bvec, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hc, Hpk_apply_wp_eq_ite]
  by_cases h : wp k n i = p
  · subst h; simp
  · rw [if_neg h, if_neg (fun he => h he.symm), star_zero]

theorem phi_w (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV k n a (wp k n i) = 0 := by
  have hi := i.isLt
  have hv := wp_val k n i
  have ha := a.isLt
  unfold phiV
  split_ifs with h
  · simp only [bvec]
    rw [Pi.single_apply, if_neg]
    intro he
    have := congrArg Fin.val he
    simp only [esI] at this
    omega
  · simp only [epsV, bvec, Pi.smul_apply, Pi.add_apply, Pi.single_apply]
    rw [if_neg, if_neg]
    · simp
    · intro he
      have := congrArg Fin.val he
      simp [wI, Fin.val_last] at this <;> omega
    · intro he
      have := congrArg Fin.val he
      simp [wI] at this <;> omega

theorem phi'_w (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV' k n a (wp k n i) = 0 := by
  show (Hpk k n *ᵥ phiV k n a) (wp k n i) = 0
  rw [hpk_mv_w, phi_w]

theorem herm_w_l (v : Fin (2 * n + k + 1) → ℂ) (i : Fin (k - 1)) : herm (Hpk k n) (wv k n i) v = star (v (wp k n i)) := by
  unfold herm
  rw [hpk_bvec_w]
  simp only [wv]
  rw [dot_bvec_r]
  rfl

theorem herm_w_r (v : Fin (2 * n + k + 1) → ℂ) (i : Fin (k - 1)) : herm (Hpk k n) v (wv k n i) = v (wp k n i) := by
  unfold herm
  have hs : star (wv k n i) = Pi.single (wp k n i) (1 : ℂ) := by
    ext j
    by_cases h : j = wp k n i <;> simp [wv, bvec, h]
  rw [hs, single_dotProduct, one_mul, hpk_mv_w]

def Phv : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → Fin (2 * n + k + 1) → ℂ :=
  Sum.elim (phiV' k n) (Sum.elim (phiV k n) (wv k n))

def Psv : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → Fin (2 * n + k + 1) → ℂ :=
  Sum.elim (phiV k n) (Sum.elim (phiV' k n) (wv k n))

private theorem herm_Hpk_mulVec_Hpk_mulVec (x y : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) (Hpk k n *ᵥ x) (Hpk k n *ᵥ y) = herm (Hpk k n) x y := by
  unfold herm
  rw [mulVec_mulVec, hpk_mul, one_mulVec, Matrix.star_mulVec, hpk_conjT, dotProduct_mulVec]

theorem pair_all (hk : 1 ≤ k) (c d : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1))) :
    herm (Hpk k n) (Phv k n d) (Psv k n c) = if c = d then 1 else 0 := by
  have hφ' : ∀ a, phiV' k n a = Hpk k n *ᵥ phiV k n a := fun _ => rfl
  rcases c with b | b | i <;> rcases d with a | a | j <;>
    simp only [Phv, Psv, Sum.elim_inl, Sum.elim_inr]
  · rw [← herm_conj (Hpk k n) (hpk_conjT k n) (phiV k n b) (phiV' k n a), phi_pair k n hk]
    by_cases h : b = a
    · subst h; simp
    · simp [h]
  · rw [phi_iso k n hk]; simp
  · rw [herm_w_l, phi_w]; simp
  · rw [hφ', hφ', herm_Hpk_mulVec_Hpk_mulVec, phi_iso k n hk]; simp
  · rw [phi_pair k n hk]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [herm_w_l, phi'_w]; simp
  · rw [herm_w_r, phi'_w]; simp
  · rw [herm_w_r, phi_w]; simp
  · rw [herm_w_l]
    simp only [wv, bvec, Pi.single_apply]
    by_cases h : i = j
    · subst h; simp
    · have hne : wp k n j ≠ wp k n i := by
        intro he
        apply h
        ext
        have := congrArg Fin.val he
        rw [wp_val, wp_val] at this
        omega
      simp [hne, h]

private theorem herm_sum_smul_left_tail_integrals {ι : Type*} [Fintype ι] (g : ι → ℂ) (v : ι → Fin (2 * n + k + 1) → ℂ)
    (w : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) (∑ c, g c • v c) w = ∑ c, g c * herm (Hpk k n) (v c) w := by
  unfold herm
  simp only [dotProduct, mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem expand (hk : 1 ≤ k) (y : Fin (2 * n + k + 1) → ℂ) :
    y = ∑ c, herm (Hpk k n) y (Psv k n c) • Phv k n c := by
  have hcoef : ∀ (g : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → ℂ) c,
      herm (Hpk k n) (∑ d, g d • Phv k n d) (Psv k n c) = g c := by
    intro g c
    rw [herm_sum_smul_left_tail_integrals]
    simp [pair_all k n hk]
  have hli : LinearIndependent ℂ (Phv k n) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg c
    have := hcoef g c
    rw [hg] at this
    simpa [herm] using this.symm
  have hcard : Fintype.card (Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1))) =
      Module.finrank ℂ (Fin (2 * n + k + 1) → ℂ) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Module.finrank_fin_fun]
    omega
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ c, b c = Phv k n c := fun c => by simp [b]
  have hy := b.sum_repr y
  simp only [hb] at hy
  conv_lhs => rw [← hy]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := hcoef (fun d => b.repr y d) c
  rw [hy] at this
  rw [this]

theorem herm_expand (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) y w = ∑ j, (herm (Hpk k n) y (phiV k n j) * herm (Hpk k n) (phiV' k n j) w +
      herm (Hpk k n) y (phiV' k n j) * herm (Hpk k n) (phiV k n j) w) +
      ∑ i, y (wp k n i) * herm (Hpk k n) (wv k n i) w := by
  conv_lhs => rw [expand k n hk y]
  rw [herm_sum_smul_left_tail_integrals, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Psv, Phv, Sum.elim_inl, Sum.elim_inr, herm_w_r]
  rw [Finset.sum_add_distrib]
  exact (add_assoc _ _ _).symm

theorem herm_linF (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k n) y w = linF (fun j => herm (Hpk k n) (phiV' k n (Fin.cast (by omega) j)) w)
      (fun j => herm (Hpk k n) (phiV k n (Fin.cast (by omega) j)) w) (fun i => herm (Hpk k n) (wv k n i) w)
      (hcoord k n (y, s)) := by
  rw [herm_expand k n hk y w]
  simp only [linF, hcoord]
  congr 1
  exact ((finCongr (by omega : 1 + n = n + 1)).sum_comp (fun j =>
    herm (Hpk k n) y (phiV k n j) * herm (Hpk k n) (phiV' k n j) w +
      herm (Hpk k n) y (phiV' k n j) * herm (Hpk k n) (phiV k n j) w)).symm

end ex

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

section cont
variable {p m : ℕ}

theorem cont_ite {β : Type} [TopologicalSpace β] [Zero β] (c : Prop) [Decidable c] {f : Xp p m → β}
    (hf : Continuous f) : Continuous (fun x => if c then f x else 0) := by
  by_cases h : c
  · simp only [h, if_true]; exact hf
  · simp only [h, if_false]; exact continuous_const

theorem cont_Lsq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => Lsq x l) := by
  unfold Lsq
  exact continuous_const.fun_add (continuous_finsetSum _ fun j _ =>
    cont_ite _ (((continuous_apply j).comp continuous_fst).norm.pow 2))

theorem cont_rhoSq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by
  unfold rhoSq
  refine ((cont_Lsq _).add (continuous_finsetSum _ fun i _ => ?_)).add (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm.pow 2)

theorem cont_bco (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  unfold bco
  refine ((Complex.continuous_ofReal.comp ((continuous_finsetSum _ fun i _ => ?_).fun_neg.div_const 2)).add
    ((Complex.continuous_ofReal.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
      continuous_const)).sub (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_apply j).comp continuous_fst).star)

theorem cont_de (l : Fin (p + 1)) : Continuous (fun x : Xp p m => de x l) := by
  unfold de
  exact Real.continuous_sqrt.comp (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

theorem cont_linF (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (fun x : Xp p m => linF η η' ζ x) := by
  unfold linF
  refine (continuous_finsetSum _ fun j _ => ?_).add (continuous_finsetSum _ fun i _ => ?_)
  · exact (((continuous_apply j).comp continuous_fst).mul continuous_const).add
      (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul continuous_const)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul continuous_const

def GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) (x : Xp p m) : ℝ≥0∞ :=
  (∏ l, ENNReal.ofReal (de x l ^ (-s l))) * ENNReal.ofReal ((1 + |2 * (linF η η' ζ x).im + c₀|) ^ (-δ))

theorem meas_GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) :
    Measurable (GI s δ η η' ζ c₀) := by
  unfold GI
  refine (Finset.measurable_prod _ fun l _ => ?_).mul ?_
  · exact ENNReal.measurable_ofReal.comp ((cont_de l).measurable.pow_const _)
  · exact ENNReal.measurable_ofReal.comp ((continuous_const.add ((continuous_const.mul
      (Complex.continuous_im.comp (cont_linF η η' ζ))).add continuous_const).abs).measurable.pow_const _)

end cont

theorem mp_unitary {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun y : Fin N → ℂ => U *ᵥ y) volume volume := by
  set f : (Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) := (Matrix.toLin' U).restrictScalars ℝ with hf
  have hfU : (fun y : Fin N → ℂ => U *ᵥ y) = ⇑f := by funext y; simp [hf, Matrix.toLin'_apply]
  have hn : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]; exact_mod_cast hn
  rw [hfU]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

theorem mp_hpar {k n : ℕ} (U : Mat k n) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun X : HPar k n => (U *ᵥ X.1, X.2)) volume volume :=
  (mp_unitary U hU).prod (MeasurePreserving.id volume)

theorem os_q (hOS : OS) (q p m : ℕ) (hq : q = p + 1) (δ γ : ℝ) (e : Fin (q + 1) → ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hγ : 0 < γ) (hγ8 : γ ≤ δ / 8) (he : ∀ l, 0 < e l) (hsum : e 0 + 2 * ∑ i : Fin q, e i.succ < γ / 2) :
    ∃ C : ℝ, ∀ (η η' : Fin q → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI (fun l => s0N q m l - e l) δ η η' ζ c₀ x ≤
        ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
  subst hq
  obtain ⟨C, hC⟩ := hOS p m δ γ e hδ hδ2 hγ hγ8 he hsum
  refine ⟨C, fun η η' ζ c₀ h0 => ?_⟩
  have e0 : (⟨0, by omega⟩ : Fin (p + 1)) = 0 := Fin.ext (by simp)
  rw [e0] at h0 ⊢
  exact hC η η' ζ c₀ h0

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

theorem cz0 {k : ℕ} (hk : 1 ≤ k) (z : Fin (2 * 0 + k + 1) → ℂ) (hT : 0 < Tz k 0 z) :
    herm (Hpk k 0) (epsV k 0) z ≠ 0 := by
  intro h
  have sgl : ∀ p : Fin (2 * 0 + k + 1), sg k 0 p.val = p.val := fun p => by
    have := p.2; unfold sg; rw [if_neg (by omega)]
  have hmv : ∀ (v : Fin (2 * 0 + k + 1) → ℂ) (p : Fin (2 * 0 + k + 1)),
      (Hpk k 0 *ᵥ v) p = (if p.val = 0 + k then -1 else 1) * v p := by
    intro v p; simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single p]
    · rw [hpk_apply, sgl, if_pos rfl]
    · intro q _ hq; rw [hpk_apply, sgl, if_neg (fun e => hq (Fin.ext e)), zero_mul]
    · intro hp; exact absurd (Finset.mem_univ _) hp
  have hw0 : (wI k 0 0).val = 0 := by simp [wI]
  have hwk : (wI k 0 (Fin.last k)).val = k := by simp [wI]
  have e1 : Hpk k 0 *ᵥ bvec (wI k 0 0) = bvec (wI k 0 0) := by
    funext p; rw [hmv]; split_ifs with hp
    · rw [bvec_ne _ _ (by omega), mul_zero]
    · rw [one_mul]
  have e2 : Hpk k 0 *ᵥ bvec (wI k 0 (Fin.last k)) = -bvec (wI k 0 (Fin.last k)) := by
    funext p; rw [hmv, Pi.neg_apply]; split_ifs with hp
    · rw [neg_one_mul]
    · rw [bvec_ne _ _ (by omega), mul_zero, neg_zero]
  have hh : herm (Hpk k 0) (epsV k 0) z =
      ((Real.sqrt 2)⁻¹ : ℂ) * (star (z (wI k 0 0)) - star (z (wI k 0 (Fin.last k)))) := by
    unfold epsV herm
    rw [mulVec_smul, mulVec_add, e1, e2, dotProduct_smul, dotProduct_add, dotProduct_neg, dot_bvec_r, dot_bvec_r,
      Pi.star_apply, Pi.star_apply, smul_eq_mul, sub_eq_add_neg]
  have hc : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by
    have : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by rw [sq2_mul_sq2_eq_half]; norm_num
    exact left_ne_zero_of_mul this
  rw [hh] at h
  have hzz : z (wI k 0 0) = z (wI k 0 (Fin.last k)) :=
    star_injective (sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hc))
  have hre : (herm (Hpk k 0) z z).re = ∑ p, (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
    unfold herm
    simp only [dotProduct, hmv, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.star_apply]
    split_ifs <;> simp [Complex.mul_re, Complex.normSq_apply]
  have hne : wI k 0 0 ≠ wI k 0 (Fin.last k) := fun e => by have := congrArg Fin.val e; omega
  have key : 0 ≤ ∑ p, (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (wI k 0 (Fin.last k))),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ (wI k 0 0)⟩)]
    rw [if_pos (show (wI k 0 (Fin.last k)).val = 0 + k by omega), if_neg (show ¬ (wI k 0 0).val = 0 + k by omega),
      hzz]
    have hrest : 0 ≤ ∑ p ∈ (Finset.univ.erase (wI k 0 (Fin.last k))).erase (wI k 0 0),
        (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
      refine Finset.sum_nonneg fun p hp => ?_
      have hpk : p ≠ wI k 0 (Fin.last k) := (Finset.mem_erase.1 (Finset.mem_erase.1 hp).2).1
      rw [if_neg (show ¬ (p.val = 0 + k) from fun e => hpk (Fin.ext (by omega)))]
      exact mul_nonneg zero_le_one (Complex.normSq_nonneg _)
    linarith
  unfold Tz at hT
  rw [hre] at hT
  linarith

theorem cz_ne {k n : ℕ} (hk : 1 ≤ k) (z1 : Fin (2 * n + k + 1) → ℂ) (hT : 0 < Tz k n z1) :
    herm (Hpk k n) (phiV k n ⟨0, by omega⟩) (fvec k n z1 ⟨0, by omega⟩) ≠ 0 := by
  by_cases hn : 0 < n
  · unfold phiV fvec
    rw [dite_eq_left hn, dite_eq_left hn, herm_bb, hpk_apply]
    rw [if_pos (show (esI k n ⟨0, hn⟩).val = sg k n (eI k n ⟨0, hn⟩).val by
        show 2 * n + k - 0 = sg k n 0; unfold sg; rw [if_pos (Or.inl hn)]),
      if_neg (show ¬ (eI k n ⟨0, hn⟩).val = n + k by show ¬ 0 = n + k; omega)]
    norm_num
  · have hn0 : n = 0 := by omega
    subst hn0
    unfold phiV fvec
    rw [dite_eq_right (lt_irrefl 0), dite_eq_right (lt_irrefl 0)]
    exact cz0 hk z1 hT

def etaF (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (1 + n) → ℂ :=
  fun j => herm (Hpk k n) (phiV' k n (Fin.cast (by omega) j)) w

def eta'F (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (1 + n) → ℂ :=
  fun j => herm (Hpk k n) (phiV k n (Fin.cast (by omega) j)) w

def zetaF (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (k - 1) → ℂ := fun i => herm (Hpk k n) (wv k n i) w

theorem herm_linF' {k n : ℕ} (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k n) y w = linF (etaF k n w) (eta'F k n w) (zetaF k n w) (hcoord k n (y, s)) :=
  herm_linF k n hk y w s

section inner
variable {k r' : ℕ}

theorem inner_bound (hIW : IW) (hF : FormulaF) (hHC : HeisConjLev) (hHA : HeisAct) (hk : 1 ≤ k)
    (s : Fin (1 + r' + 1) → ℝ) (δ γ C : ℝ) (z1 : Fin (2 * r' + k + 1) → ℂ)
    (hC : ∀ (η η' : Fin (1 + r') → ℂ) (ζ : Fin (k - 1) → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI s δ η η' ζ c₀ x ≤ ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)))
    (hcz : herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) ≠ 0)
    (m : Mat k r') (hm : m ∈ UH (Hpk k r')) :
    ∫⁻ X : HPar k r', ENNReal.ofReal (xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m)) *
        ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m)|) ^ (-δ)) ≤
      ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
        (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m) *
          ENNReal.ofReal ((1 + |lam k r' z1 m|) ^ (-(δ / 4)))) := by
  obtain ⟨κ, hκG, hκU, t, ht, htn, hD⟩ := lev_data hIW hHC hk m hm
  have hκU' : κ * κᴴ = 1 := mul_eq_one_comm.1 hκU
  have h00 : (0 : Fin (r' + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp)
  have ht' : m *ᵥ phiV k r' ⟨0, by omega⟩ = t • (κ *ᵥ phiV k r' ⟨0, by omega⟩) := by rw [← h00]; exact ht
  obtain ⟨w, hw⟩ : ∃ w, w = κᴴ *ᵥ (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∏ a : Fin (r' + 1), Del k r' a m ^ (-s (su a)) := ⟨_, rfl⟩
  have hDel : ∀ (n : ℕ) (l : Fin (n + 1)) (x : Mat k n), 0 ≤ Del k n l x := fun n l x => Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by rw [hA]; exact Finset.prod_nonneg fun a _ => Real.rpow_nonneg (hDel _ _ _) _
  have hpt : ∀ X : HPar k r',
      ENNReal.ofReal (xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m)) *
        ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m)|) ^ (-δ)) =
      ENNReal.ofReal A * GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
        (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := by
    intro X
    obtain ⟨hD0, hDS⟩ := hD X
    have hde : ∀ (x : Xp (1 + r') (k - 1)) (l : Fin (1 + r' + 1)), 0 ≤ de x l := fun x l => Real.sqrt_nonneg _
    have hmr : ∀ a : Fin (r' + 1), (Del k r' a m * de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) (su a)) ^ (-s (su a)) =
        Del k r' a m ^ (-s (su a)) * de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) (su a) ^ (-s (su a)) :=
      fun a => Real.mul_rpow (hDel _ _ _) (hde _ _)
    have hxi : xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m) =
        A * ∏ l, de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) l ^ (-s l) := by
      unfold xiR
      rw [prod_su, prod_su (fun l => de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) l ^ (-s l)), hD0]
      simp only [hDS, (hF k r' hk).1, hmr, Finset.prod_mul_distrib]
      rw [hA]; ring
    have hX : X.1 = κ *ᵥ (κᴴ *ᵥ X.1) := by rw [mulVec_mulVec, hκU', one_mulVec]
    have hmf : m *ᵥ fvec k r' z1 ⟨0, by omega⟩ = κ *ᵥ w := by rw [hw, mulVec_mulVec, hκU', one_mulVec]
    have hh : herm (Hpk k r') (κ *ᵥ w) X.1 = star (herm (Hpk k r') (κᴴ *ᵥ X.1) w) := by
      conv_lhs => rw [hX]
      rw [herm_UH _ _ hκG]
      exact (herm_conj _ (hpk_conjT k r') _ _).symm
    have hlam : lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
        2 * (linF (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (hcoord k r' (κᴴ *ᵥ X.1, X.2))).im + lam k r' z1 m := by
      rw [lam_lev hHA, hmf, hh, herm_linF' hk _ w X.2, Complex.star_def, Complex.conj_im]
      ring
    rw [hxi, hlam, ENNReal.ofReal_mul hA0, ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hde _ l) _)]
    unfold GI; rw [mul_assoc]
  have key : t * eta'F k r' w ⟨0, by omega⟩ = herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) := by
    show t * herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) w = _
    rw [hw, ← herm_UH _ _ hκG (phiV k r' ⟨0, by omega⟩) (κᴴ *ᵥ (m *ᵥ fvec k r' z1 ⟨0, by omega⟩)),
      mulVec_mulVec (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) κ κᴴ, hκU', one_mulVec, ← herm_smul_l, ← ht', herm_UH _ _ hm]
  have ht0 : t ≠ 0 := fun h => hcz (by rw [← key, h, zero_mul])
  have hη0 : eta'F k r' w ⟨0, by omega⟩ ≠ 0 := fun h => hcz (by rw [← key, h, mul_zero])
  have hκH : (κᴴ)ᴴ * κᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact hκU'
  have hg : Measurable (fun x => GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m) (hcoord k r' x)) :=
    (meas_GI _ _ _ _ _ _).comp (hF k r' hk).2.measurable
  have hD0pos : 0 < Del k r' 0 m := by rw [← htn]; exact norm_pos_iff.2 ht0
  have hcz0 : 0 < ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ := norm_pos_iff.2 hcz
  have hnorm : ‖eta'F k r' w ⟨0, by omega⟩‖ =
      ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ / Del k r' 0 m := by
    have : eta'F k r' w ⟨0, by omega⟩ = herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) / t := by
      rw [eq_div_iff ht0, mul_comm]; exact key
    rw [this, norm_div, htn]
  have hQ : xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m = A * Del k r' 0 m ^ γ := by
    unfold xiR; rw [hA, Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [if_true, Fin.succ_ne_zero, if_false, sub_zero]
    rw [show -(s (su 0) - γ) = -s (su 0) + γ by ring, Real.rpow_add hD0pos]; ring
  have hQ0 : 0 ≤ xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m :=
    Finset.prod_nonneg fun a _ => Real.rpow_nonneg (hDel _ _ _) _
  have hR0 : 0 ≤ (1 + |lam k r' z1 m|) ^ (-(δ / 4)) := Real.rpow_nonneg (by positivity) _
  calc _ = ∫⁻ X : HPar k r', ENNReal.ofReal A * GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := lintegral_congr hpt
    _ = ENNReal.ofReal A * ∫⁻ X : HPar k r', GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal A * ∫⁻ X : HPar k r', GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' X) := by rw [(mp_hpar κᴴ hκH).lintegral_comp hg]
    _ = ENNReal.ofReal A * ∫⁻ x, GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m) x := by
          rw [(hF k r' hk).2.lintegral_comp (meas_GI _ _ _ _ _ _)]
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C * ‖eta'F k r' w ⟨0, by omega⟩‖ ^ (-γ) * (1 + |lam k r' z1 m|) ^ (-δ / 4)) := by
          gcongr; exact hC _ _ _ _ hη0
    _ = ENNReal.ofReal (A * (C * ‖eta'F k r' w ⟨0, by omega⟩‖ ^ (-γ) * (1 + |lam k r' z1 m|) ^ (-δ / 4))) :=
          (ENNReal.ofReal_mul hA0).symm
    _ = ENNReal.ofReal ((C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m * (1 + |lam k r' z1 m|) ^ (-(δ / 4)))) := by
          congr 1
          rw [hnorm, Real.div_rpow hcz0.le hD0pos.le, Real.rpow_neg hD0pos.le, div_inv_eq_mul, hQ, neg_div]; ring
    _ = _ := by rw [ENNReal.ofReal_mul' (mul_nonneg hQ0 hR0), ENNReal.ofReal_mul hQ0]

end inner

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
