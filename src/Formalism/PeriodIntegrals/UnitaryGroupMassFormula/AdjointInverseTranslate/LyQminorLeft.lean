module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAaVector
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.SubsetUpperHessenberg
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.HkConjTranspose
open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

def hkSig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩

def hkEps (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = hkSig k r i then hkEps k r i else 0 := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [Hpk, hkSig, hkEps, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hk_sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkSig k r (hkSig k r i) = i := by
  apply Fin.ext
  simp only [hkSig]
  split_ifs <;> omega

theorem hk_eps_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkEps k r (hkSig k r i) = hkEps k r i := by
  simp only [hkEps, hkSig]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hk_eps_mul_self (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkEps k r i * hkEps k r i = 1 := by
  unfold hkEps
  split_ifs <;> norm_num

theorem hk_star_eps (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (hkEps k r i) = hkEps k r i := by
  unfold hkEps
  split_ifs <;> simp

theorem hk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [hk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hk_sig_sig, hk_eps_sig]
  by_cases h : j = i
  · subst h; simp [hk_eps_mul_self]
  · simp [h, one_apply_ne' h]

theorem hk_conjTranspose (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hk_apply, hk_apply]
  by_cases h : j = hkSig k r i
  · subst h
    simp [hk_sig_sig, hk_eps_sig, hk_star_eps]
  · have h' : i ≠ hkSig k r j := fun e => h (by rw [e, hk_sig_sig])
    simp [h, h']

theorem hpk_involution : HpkInvol := fun k r => ⟨hk_conjTranspose k r, hk_mul_self k r⟩

end AAInvW
end
end

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem lf_sig_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (hkSig k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := rfl

theorem lf_eI_val (k r : ℕ) (a : Fin r) : (eI k r a).val = a.val := rfl

theorem lf_esI_val (k r : ℕ) (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

theorem lf_sig_eI (k r : ℕ) (a : Fin r) : hkSig k r (eI k r a) = esI k r a := by
  apply Fin.ext
  rw [lf_sig_val, lf_esI_val, lf_eI_val]
  have h := a.isLt
  rw [if_neg (by omega)]

theorem lf_eps_eI (k r : ℕ) (a : Fin r) : hkEps k r (eI k r a) = 1 := by
  have h := a.isLt
  unfold hkEps
  rw [if_neg (by rw [lf_eI_val]; omega)]

theorem lf_H_eI (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) q = if q = esI k r a then 1 else 0 := by
  rw [hk_apply, lf_sig_eI, lf_eps_eI]

theorem lf_Hmul (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (t p : Fin (2 * r + k + 1)) : (Hpk k r * g) t p = hkEps k r t * g (hkSig k r t) p := by
  rw [Matrix.mul_apply]
  simp [hk_apply, ite_mul]

theorem lf_unit_entry (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : inUH (Hpk k r) g) (b p : Fin (2 * r + k + 1)) :
    ∑ t, star (g t b) * (hkEps k r t * g (hkSig k r t) p) = Hpk k r b p := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrFun (congrFun h b) p
  rw [Matrix.mul_assoc, Matrix.mul_apply] at h2
  rw [← h2]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [lf_Hmul, Matrix.conjTranspose_apply]

theorem lf_col_of_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {j : Fin n} {v : Fin n → ℂ}
    (h : M *ᵥ bvec j = v) (t : Fin n) : M t j = v t := by
  rw [← h]
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem lf_bvec_apply {n : ℕ} (j t : Fin n) : bvec j t = if t = j then 1 else 0 := by
  unfold bvec
  exact Pi.single_apply j 1 t

theorem lf_inUH_mul {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) :
    inUH H (a * b) := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

private theorem hpk_sq_lemma (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext t p
  rw [lf_Hmul, hk_apply, hk_sig_sig, hk_eps_sig, Matrix.one_apply]
  by_cases htp : p = t
  · subst htp
    rw [if_pos rfl, if_pos rfl]
    unfold hkEps
    split_ifs <;> norm_num
  · rw [if_neg htp, if_neg (Ne.symm htp), mul_zero]

theorem lf_det_ne_zero (k r : ℕ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : inUH (Hpk k r) g) : g.det ≠ 0 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hdH : (Hpk k r).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (hpk_sq_lemma k r)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  intro h0
  have h1 := congrArg Matrix.det hg'
  rw [Matrix.det_mul, h0, mul_zero] at h1
  exact hdH h1.symm

theorem lf_UW_row (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    h (esI k r a) p = if p = esI k r a then 1 else 0 := by
  obtain ⟨hU, hv, -⟩ := hh
  have hcol : ∀ t, h t (eI k r a) = if t = eI k r a then 1 else 0 := fun t => by
    rw [lf_col_of_mulVec (hv a).1 t, lf_bvec_apply]
  have h2 := lf_unit_entry k r h (show inUH (Hpk k r) h from hU) (eI k r a) p
  rw [lf_H_eI] at h2
  rw [← h2, Finset.sum_eq_single (eI k r a)]
  · rw [hcol, if_pos rfl, star_one, one_mul, lf_eps_eI, one_mul, lf_sig_eI]
  · intro t _ ht
    rw [hcol, if_neg ht, star_zero, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem lf_UW_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (a : Fin r) (t : Fin (2 * r + k + 1)) :
    h t (eI k r a) = if t = eI k r a then 1 else 0 := by
  exact (lf_col_of_mulVec (hh.2.1 a).1 t).trans (lf_bvec_apply _ _)

theorem lf_sig_small (k r : ℕ) (t : Fin (2 * r + k + 1)) (ht : t.val < r) :
    hkSig k r t = esI k r ⟨t.val, ht⟩ := by
  apply Fin.ext
  rw [lf_sig_val, lf_esI_val]
  rw [if_neg (by omega)]

theorem lf_N_rowStar (k r : ℕ) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : m ∈ Formalism.QuantumDeterminants.Nset k r) : ∀ (b : ℕ) (hb : b < r) (p : Fin (2 * r + k + 1)), p.val ≤ 2 * r + k - b →
      m (esI k r ⟨b, hb⟩) p = if p = esI k r ⟨b, hb⟩ then 1 else 0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro hb p hp
  have hU : inUH (Hpk k r) m := hm.1
  have hcol := hm.2.1 ⟨b, hb⟩
  have h2 := lf_unit_entry k r m hU (eI k r ⟨b, hb⟩) p
  rw [lf_H_eI] at h2
  rw [← h2, Finset.sum_eq_single (eI k r ⟨b, hb⟩)]
  · rw [hcol (eI k r ⟨b, hb⟩) (lf_eI_val k r ⟨b, hb⟩).ge, if_pos rfl, star_one, one_mul, lf_eps_eI,
      one_mul, lf_sig_eI]
  · intro t _ ht
    by_cases htb : b ≤ t.val
    · rw [hcol t htb, if_neg ht, star_zero, zero_mul]
    · push_neg at htb
      have htr : t.val < r := by omega
      rw [lf_sig_small k r t htr, ih t.val htb htr p (by omega), if_neg, mul_zero, mul_zero]
      intro hpe
      have h3 : p.val = 2 * r + k - t.val := by rw [hpe, lf_esI_val]
      omega
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem lf_S_rowStar (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hs : s ∈ Sset k r z) (a : Fin r) (j : Fin (2 * r + k + 1)) (hj : j.val ≤ 2 * r + k - a.val) :
    s (esI k r a) j = if j = esI k r a then 1 else 0 := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r a)]
  · rw [lf_UW_row k r z hh a, if_pos rfl, one_mul]
    exact lf_N_rowStar k r hm a.val a.isLt j hj
  · intro t _ ht
    rw [lf_UW_row k r z hh a, if_neg ht, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem subset_row_star : SsetRowStar := by
  unfold SsetRowStar
  intro k r z s hs a j hj
  have ha := a.isLt
  have hjl := j.isLt
  apply lf_S_rowStar k r z s hs a j
  by_contra hlt
  push_neg at hlt
  have hb : 2 * r + k - j.val < a.val := by omega
  apply hj ⟨2 * r + k - j.val, by omega⟩ hb
  apply Fin.ext
  rw [lf_esI_val]
  show j.val = 2 * r + k - (2 * r + k - j.val)
  omega

theorem subset_upper_hessenberg : SsetUH := by
  unfold SsetUH
  intro k r z s hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact lf_inUH_mul hh.1 hm.1

theorem lf_S_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hs : s ∈ Sset k r z) (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    s i (eI k r a) = if i = eI k r a then 1 else 0 := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
  · rw [hm.2.1 a (eI k r a) (lf_eI_val k r a).ge, if_pos rfl, mul_one, lf_UW_col k r z hh a i]
  · intro t _ ht
    by_cases hat : a.val ≤ t.val
    · rw [hm.2.1 a t hat, if_neg ht, mul_zero]
    · push_neg at hat
      have htr : t.val < r := by have := a.isLt; omega
      have ht' : t = eI k r ⟨t.val, htr⟩ := Fin.ext (lf_eI_val k r ⟨t.val, htr⟩).symm
      rw [ht', lf_UW_col k r z hh ⟨t.val, htr⟩ i, if_neg, zero_mul]
      intro hie
      have h3 := congrArg Fin.val hie
      rw [lf_eI_val] at h3
      simp only at h3
      omega
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem lf_triInv (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hM : M⁻¹ * M = 1)
    (hU : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → M i (eI k r a) = if i = eI k r a then 1 else 0) :
    ∀ (a : ℕ) (ha : a < r) (i : Fin (2 * r + k + 1)), a ≤ i.val →
      M⁻¹ i (eI k r ⟨a, ha⟩) = if i = eI k r ⟨a, ha⟩ then 1 else 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro ha i hi
  have h1 := congrFun (congrFun hM i) (eI k r ⟨a, ha⟩)
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  rw [Finset.sum_eq_single (eI k r ⟨a, ha⟩)] at h1
  · rw [hU ⟨a, ha⟩ (eI k r ⟨a, ha⟩) (lf_eI_val k r ⟨a, ha⟩).ge, if_pos rfl, mul_one] at h1
    exact h1
  · intro t _ ht
    by_cases hat : a ≤ t.val
    · rw [hU ⟨a, ha⟩ t hat, if_neg ht, mul_zero]
    · push_neg at hat
      have htr : t.val < r := by omega
      have ht' : t = eI k r ⟨t.val, htr⟩ := Fin.ext (lf_eI_val k r ⟨t.val, htr⟩).symm
      rw [ht', ih t.val hat htr i (by omega), if_neg, zero_mul]
      intro hie
      have h3 := congrArg Fin.val hie
      rw [lf_eI_val] at h3
      simp only at h3
      omega
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem lf_S_invCol (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hs : s ∈ Sset k r z) (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    s⁻¹ i (eI k r a) = if i = eI k r a then 1 else 0 := by
  have hUH : inUH (Hpk k r) s := subset_upper_hessenberg k r z s hs
  have hdet : IsUnit s.det := isUnit_iff_ne_zero.mpr (lf_det_ne_zero k r hUH)
  exact lf_triInv k r s (Matrix.nonsing_inv_mul s hdet) (fun b i' hb => lf_S_col k r z s hs b i' hb)
    a.val a.isLt i hi

theorem subset_inverse_column : SsetInvCol := by
  unfold SsetInvCol
  intro k r z s hs a i hi
  apply lf_S_invCol k r z s hs a i
  by_contra hlt
  push_neg at hlt
  have ha := a.isLt
  exact hi ⟨i.val, by omega⟩ hlt (Fin.ext (lf_eI_val k r ⟨i.val, by omega⟩).symm)

end AAInvW
end
end

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem lx_det_tri {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) (hT : ∀ a b : Fin m, a < b → T a b = 0)
    (hd : ∀ a, T a a = 1) : (T * N).det = N.det := by
  rw [Matrix.det_mul, Matrix.det_of_lowerTriangular T (by
      intro i j hij
      exact hT i j (OrderDual.toDual_lt_toDual.mp hij)), Finset.prod_eq_one (fun a _ => hd a), one_mul]

theorem lx_mulVec_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

theorem lx_mulVec_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) : (M *ᵥ bvec j) i = M i j := by
  exact (lf_col_of_mulVec rfl i).symm

theorem lx_herm_eI (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  unfold herm
  rw [dotProduct, Finset.sum_eq_single (eI k r a)]
  · rw [Pi.star_apply, lf_bvec_apply, if_pos rfl, star_one, one_mul, lx_mulVec_apply,
      Finset.sum_eq_single (esI k r a)]
    · rw [lf_H_eI, if_pos rfl, one_mul]
    · intro q _ hq
      rw [lf_H_eI, if_neg hq, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · intro t _ ht
    rw [Pi.star_apply, lf_bvec_apply, if_neg ht, star_zero, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem lx_sum_red {n m : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) (F : Fin n → ℂ)
    (hF : ∀ j, j ∉ Set.range e → F j = 0) : ∑ j, F j = ∑ b, F (e b) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (by intro x _ y _ h; exact he h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  apply hF
  rintro ⟨b, rfl⟩
  exact hj (Finset.mem_image_of_mem e (Finset.mem_univ b))

theorem lx_esI_ne (k r : ℕ) (b c : Fin r) (h : b.val ≠ c.val) : esI k r b ≠ esI k r c := by
  intro he
  have h2 := congrArg Fin.val he
  rw [lf_esI_val, lf_esI_val] at h2
  have := b.isLt
  have := c.isLt
  omega

theorem lx_eI_ne (k r : ℕ) (b c : Fin r) (h : b.val ≠ c.val) : eI k r b ≠ eI k r c := by
  intro he
  have h2 := congrArg Fin.val he
  rw [lf_eI_val, lf_eI_val] at h2
  exact h h2

theorem coef_left_aa : CoefLeftAA := by
  intro k r z m hm s g c hs
  have hrow := subset_row_star k r z s hs
  have inj : Function.Injective (fun b : Fin m => esI k r (Fin.castLE hm b)) := by
    intro b b' h
    have := b.isLt; have := b'.isLt
    have := congrArg Fin.val h
    simp only [lf_esI_val, Fin.val_castLE] at this
    exact Fin.ext (by omega)
  have key : ∀ (a l : Fin m), herm (Hpk k r) ((s * g) *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a))) =
      ∑ b : Fin m, s (esI k r (Fin.castLE hm a)) (esI k r (Fin.castLE hm b)) *
        herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm b))) := by
    intro a l
    simp only [lx_herm_eI]
    rw [← mulVec_mulVec, lx_mulVec_apply]
    refine lx_sum_red (fun b : Fin m => esI k r (Fin.castLE hm b)) inj _ ?_
    intro j hj
    have h0 : s (esI k r (Fin.castLE hm a)) j = 0 := by
      have hc : ∀ b : Fin r, b.val < (Fin.castLE hm a).val → j ≠ esI k r b := by
        intro b hb he
        apply hj
        refine ⟨⟨b.val, by simp only [Fin.val_castLE] at hb; omega⟩, ?_⟩
        rw [he]; rfl
      rw [hrow _ j hc, if_neg]
      intro he; exact hj ⟨a, he.symm⟩
    rw [h0, zero_mul]
  have hM : (Matrix.of fun a l : Fin m => herm (Hpk k r) ((s * g) *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))) =
      (Matrix.of fun a b : Fin m => s (esI k r (Fin.castLE hm a)) (esI k r (Fin.castLE hm b))) *
      (Matrix.of fun a l : Fin m => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))) := by
    ext a l
    simp only [of_apply, Matrix.mul_apply, key]
  rw [hM]
  apply lx_det_tri
  · intro a b hab
    simp only [of_apply]
    have hab' : a.val < b.val := hab
    rw [hrow _ _ ?_, if_neg]
    · exact lx_esI_ne k r _ _ (by simp only [Fin.val_castLE]; omega)
    · intro c hc
      exact lx_esI_ne k r _ _ (by simp only [Fin.val_castLE] at hc ⊢; omega)
  · intro a
    simp only [of_apply]
    rw [hrow _ _ ?_, if_pos rfl]
    intro c hc
    exact lx_esI_ne k r _ _ (by omega)

theorem coef_left_aa_vector : CoefLeftAAv := by
  unfold CoefLeftAAv
  intro k r z m hm s g B hs _
  have key : (Matrix.of fun a l : Fin m => ((s * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)) =
      (Matrix.of fun a b : Fin m => s⁻¹ (eI k r (Fin.castLE hm b)) (eI k r (Fin.castLE hm a))) *
      (Matrix.of fun a l : Fin m => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)) := by
    ext a l
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, lx_mulVec_apply]
    simp only [lx_mulVec_bvec]
    refine (lx_sum_red (fun b : Fin m => eI k r (Fin.castLE hm b)) ?_
      (fun j => g⁻¹ (B l) j * s⁻¹ j (eI k r (Fin.castLE hm a))) ?_).trans ?_
    · intro b b' h
      apply Fin.ext
      have h2 := congrArg Fin.val h
      simp only [lf_eI_val, Fin.coe_castLE] at h2
      exact h2
    · intro j hj
      show g⁻¹ (B l) j * s⁻¹ j (eI k r (Fin.castLE hm a)) = 0
      by_cases hle : (Fin.castLE hm a).val ≤ j.val
      · rw [lf_S_invCol k r z s hs (Fin.castLE hm a) j hle, if_neg, mul_zero]
        intro he
        exact hj ⟨a, he.symm⟩
      · exfalso
        apply hj
        push_neg at hle
        simp only [Fin.coe_castLE] at hle
        have := a.isLt
        refine ⟨⟨j.val, by omega⟩, ?_⟩
        apply Fin.ext
        simp only [lf_eI_val, Fin.coe_castLE, Fin.val_mk]
    · exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [key]
  apply lx_det_tri
  · intro a b hab
    have hab' : a.val < b.val := hab
    have hle : (Fin.castLE hm a).val ≤ (eI k r (Fin.castLE hm b)).val := by
      simp only [lf_eI_val, Fin.coe_castLE]
      omega
    rw [Matrix.of_apply, lf_S_invCol k r z s hs (Fin.castLE hm a) _ hle,
      if_neg (lx_eI_ne k r _ _ (by simp only [Fin.coe_castLE]; omega))]
  · intro a
    rw [Matrix.of_apply, lf_S_invCol k r z s hs (Fin.castLE hm a) _ (lf_eI_val k r _).ge, if_pos rfl]

end AAInvW
end
end

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem ly_Eab_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) (s : Matrix (Fin n) (Fin n) ℂ) :
    EabH H a b (fun x => F (s * x)) = fun x => EabH H a b F (s * x) := by
  funext x
  simp only [EabH, RdV, Matrix.mul_assoc]

theorem ly_Top_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E)
    (s : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.QuantumDeterminants.Top (EabH H) v a b (fun x => F (s * x)) = fun x => Formalism.QuantumDeterminants.Top (EabH H) v a b F (s * x) := by
  funext x
  simp only [Formalism.QuantumDeterminants.Top, EabH, RdV, Matrix.mul_assoc]

theorem ly_foldr_comm {X E : Type*} (L : (X → E) → (X → E)) (l : List ((X → E) → (X → E)))
    (hl : ∀ T ∈ l, ∀ f, T (L f) = L (T f)) (f : X → E) :
    l.foldr (fun T h => T h) (L f) = L (l.foldr (fun T h => T h) f) := by
  induction l with
  | nil => rfl
  | cons T l ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hl T' (by simp [hT'])), hl T (by simp)]

theorem ly_qminor_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (F : Matrix (Fin n) (Fin n) ℂ → E)
    (s x : Matrix (Fin n) (Fin n) ℂ) :
    qminorOp (EabH H) a b u (fun y => F (s * y)) x = qminorOp (EabH H) a b u F (s * x) := by
  unfold qminorOp
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Pi.smul_apply, Pi.smul_apply]
  congr 1
  rw [ly_foldr_comm (fun f y => f (s * y)) _ ?_ F]
  intro T hT f
  simp only [List.mem_ofFn, Set.mem_range] at hT
  obtain ⟨i, rfl⟩ := hT
  exact ly_Top_left H _ _ _ f s

theorem left_aa : LeftAA := by
  unfold LeftAA
  intro E _ _ k r z m hm u ell F s g hs hg
  constructor
  · simp only [AAop]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [ly_qminor_left, coef_left_aa k r z m hm s g c hs]
  · simp only [AAvop]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    rw [ly_qminor_left, coef_left_aa_vector k r z m hm s g B hs hg]

end AAInvW
