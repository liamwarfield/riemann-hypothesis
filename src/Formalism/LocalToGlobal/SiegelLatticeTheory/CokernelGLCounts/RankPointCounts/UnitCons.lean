module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NegOnePowMulSelf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdPowMulQd
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLatSk
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfEx
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfStG
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LtOfBlkOfLt
noncomputable section

namespace Formalism.L2.SG.Pf.BlockPermutation

open Formalism.MainNotions.S Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj

variable {K : Type*} [Field K]

theorem pval_pperm : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    pval bs (pperm bs i) = pval bs i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · simp only [pperm, pval, hi, if_true]
      rw [if_pos (by omega)]
    · simp only [pperm, pval, hi, if_false]
      rw [if_neg (by omega), show s + pperm bs (i - s) - s = pperm bs (i - s) by omega]
      exact pval_pperm bs (i - s) (by omega)

theorem blkOf_pperm : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    blkOf bs (pperm bs i) = blkOf bs i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · simp only [pperm, blkOf, hi, if_true]
      rw [if_pos (by omega)]
    · simp only [pperm, blkOf, hi, if_false]
      rw [if_neg (by omega), show s + pperm bs (i - s) - s = pperm bs (i - s) by omega]
      rw [blkOf_pperm bs (i - s) (by omega)]

theorem pperm_lt_iff : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → (i < j ↔ pperm bs j < pperm bs i)
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pperm, h1, h2, if_true]; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_left_inj] at hb
      simp only [pperm, h1, h2, if_false]
      have := pperm_lt_iff bs (i - s) (j - s) (by omega) (by omega) hb
      omega

theorem lt_of_blkOf_lt : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i < blkOf bs j → i < j ∧ pperm bs i < pperm bs j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [blkOf, h1, h2, if_true] at hb; omega
    · simp only [pperm, h1, h2, if_true, if_false]; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_lt_add_iff_right] at hb
      simp only [pperm, h1, h2, if_false]
      have := lt_of_blkOf_lt bs (i - s) (j - s) (by omega) (by omega) hb
      omega

theorem pperm_add : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → pperm bs i + i = pperm bs j + j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pperm, h1, h2, if_true]; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_left_inj] at hb
      simp only [pperm, h1, h2, if_false]
      have := pperm_add bs (i - s) (j - s) (by omega) (by omega) hb
      omega

theorem blkOf_mono : ∀ (bs : List (K × ℕ)) (i j : ℕ), i ≤ j → blkOf bs i ≤ blkOf bs j
  | [], i, j, _ => by simp [blkOf]
  | (t, s) :: bs, i, j, hij => by
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp [blkOf, h1, h2]
    · simp [blkOf, h1, h2]
    · omega
    · simp only [blkOf, h1, h2, if_false, add_le_add_iff_right]
      exact blkOf_mono bs (i - s) (j - s) (by omega)

theorem pval_eq_of_blk : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → pval bs i = pval bs j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pval, h1, h2, if_true]
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_left_inj] at hb
      simp only [pval, h1, h2, if_false]
      exact pval_eq_of_blk bs (i - s) (j - s) (by omega) (by omega) hb

section Pt

variable {N : ℕ} (p : Point K N)

theorem pval_pinv (a : Fin N) : pval p.1 (pinv p a).val = pval p.1 a.val :=
  pval_pperm p.1 a.val (by rw [p.2.2]; exact a.isLt)

theorem blkOf_pinv (a : Fin N) : blkOf p.1 (pinv p a).val = blkOf p.1 a.val :=
  blkOf_pperm p.1 a.val (by rw [p.2.2]; exact a.isLt)

theorem pinv_lt_iff (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) : a < b ↔ pinv p b < pinv p a :=
  pperm_lt_iff p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem lt_of_blk_lt (a b : Fin N) (hb : blkOf p.1 a.val < blkOf p.1 b.val) : a < b ∧ pinv p a < pinv p b :=
  lt_of_blkOf_lt p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem pinv_add (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) :
    (pinv p a).val + a.val = (pinv p b).val + b.val :=
  pperm_add p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem pval_eq_blk (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) : pval p.1 a.val = pval p.1 b.val :=
  pval_eq_of_blk p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

end Pt

end Formalism.L2.SG.Pf.BlockPermutation
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.BlockPermutation

open Formalism.MainNotions.S Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj Matrix

variable {K : Type*} [Field K] {N : ℕ} (p : Point K N)

abbrev cv (a : Fin N) : K := pval p.1 a.val

theorem cv_ne (a : Fin N) : cv p a ≠ 0 :=
  pval_ne p.1 (fun b hb => (p.2.1 b hb).1) a.val (by rw [p.2.2]; exact a.isLt)

theorem cv_pinv (a : Fin N) : cv p (pinv p a) = cv p a := pval_pinv p a

theorem pinv_inj {a b : Fin N} (h : pinv p a = pinv p b) : a = b := by
  have := congrArg (pinv p) h
  rwa [pinv_pinv, pinv_pinv] at this

theorem ptMat_mul_mono : ptMat p * mono (pinv p) (fun a => (cv p a)⁻¹) = 1 := by
  rw [ptMat_eq_mono]
  funext a b
  rw [mul_mono_apply _ (pinv_pinv p)]
  by_cases h : a = b
  · subst h
    simp only [mono, if_true, Matrix.one_apply_eq]
    rw [cv_pinv]; exact mul_inv_cancel₀ (cv_ne p a)
  · have hne : pinv p b ≠ pinv p a := fun e => h (pinv_inj p e).symm
    simp only [mono, hne, if_false, zero_mul, Matrix.one_apply_ne h]

theorem ptMat_inv : (ptMat p)⁻¹ = mono (pinv p) (fun a => (cv p a)⁻¹) :=
  Matrix.inv_eq_right_inv (ptMat_mul_mono p)

theorem conj_apply (M : Matrix (Fin N) (Fin N) K) (a b : Fin N) :
    ((ptMat p)⁻¹ * M * ptMat p) a b = (cv p a)⁻¹ * M (pinv p a) (pinv p b) * cv p b := by
  rw [ptMat_inv]
  conv_lhs => rw [ptMat_eq_mono]
  rw [mul_mono_apply _ (pinv_pinv p), mono_mul_apply]
  simp only [cv, pval_pinv]

theorem conj'_apply (M : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    (ptMat p * M * (ptMat p)⁻¹) i j = cv p i * M (pinv p i) (pinv p j) * (cv p j)⁻¹ := by
  rw [ptMat_inv]
  conv_lhs => rw [ptMat_eq_mono]
  rw [mul_mono_apply _ (pinv_pinv p), mono_mul_apply]
  simp only [cv, pval_pinv]

theorem ptMat_isUnit : IsUnit (ptMat p).det := Matrix.isUnit_det_of_right_inverse (ptMat_mul_mono p)

def IsBlockDiagonalMatrix (X : Matrix (Fin N) (Fin N) K) : Prop := ∀ a b : Fin N, blkOf p.1 a.val ≠ blkOf p.1 b.val → X a b = 0

theorem blk_lt_of_lt {a b : Fin N} (hab : a < b) (hne : blkOf p.1 a.val ≠ blkOf p.1 b.val) :
    blkOf p.1 a.val < blkOf p.1 b.val :=
  lt_of_le_of_ne (blkOf_mono p.1 a.val b.val (le_of_lt hab)) hne

theorem X_of_st {β b : Matrix (Fin N) (Fin N) K} (hβ : IsLoUni β) (hb : IsUpUni b) (hW : β * ptMat p * b = ptMat p) :
    (ptMat p)⁻¹ * β * ptMat p = b⁻¹ ∧ UpU ((ptMat p)⁻¹ * β * ptMat p) ∧ IsBlockDiagonalMatrix p ((ptMat p)⁻¹ * β * ptMat p) := by
  have hu := ptMat_isUnit p
  have h1 : (ptMat p)⁻¹ * β * ptMat p * b = 1 := by
    rw [show (ptMat p)⁻¹ * β * ptMat p * b = (ptMat p)⁻¹ * (β * ptMat p * b) by simp only [Matrix.mul_assoc], hW,
      Matrix.nonsing_inv_mul _ hu]
  have hX : (ptMat p)⁻¹ * β * ptMat p = b⁻¹ := (Matrix.inv_eq_left_inv h1).symm
  refine ⟨hX, ?_, ?_⟩
  · rw [hX]; exact upU_inv hb
  · intro a c hne
    rw [conj_apply]
    rcases lt_or_gt_of_ne (show a ≠ c from fun e => hne (by rw [e])) with h | h
    · have hb' := (lt_of_blk_lt p a c (blk_lt_of_lt p h hne)).2
      rw [(hβ _ _).1 hb', mul_zero, zero_mul]
    · have hup : UpU ((ptMat p)⁻¹ * β * ptMat p) := by rw [hX]; exact upU_inv hb
      have := (hup a c).1 h
      rwa [conj_apply] at this

theorem st_of_X {X : Matrix (Fin N) (Fin N) K} (hX : UpU X) (hB : IsBlockDiagonalMatrix p X) :
    IsLoUni (ptMat p * X * (ptMat p)⁻¹) ∧ IsUpUni X⁻¹ ∧
      ptMat p * X * (ptMat p)⁻¹ * ptMat p * X⁻¹ = ptMat p ∧ (ptMat p * X * (ptMat p)⁻¹).det = 1 := by
  have hu := ptMat_isUnit p
  have hXd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  refine ⟨fun i j => ⟨fun hij => ?_, fun hij => ?_⟩, upU_inv hX, ?_, ?_⟩
  · rw [conj'_apply]
    by_cases hs : blkOf p.1 i.val = blkOf p.1 j.val
    · have := (pinv_lt_iff p i j hs).1 hij
      rw [(hX _ _).1 this, mul_zero, zero_mul]
    · have h2 := (lt_of_blk_lt p i j (blk_lt_of_lt p hij hs)).2
      have hs' : blkOf p.1 (pinv p i).val ≠ blkOf p.1 (pinv p j).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact hs
      rw [hB _ _ hs', mul_zero, zero_mul]
  · subst hij
    rw [conj'_apply, (hX _ _).2 rfl, mul_one, mul_inv_cancel₀ (cv_ne p i)]
  · rw [Matrix.mul_assoc (ptMat p * X), Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hXd, Matrix.mul_one]
  · rw [Matrix.det_mul, Matrix.det_mul, upU_det hX, mul_one, ← Matrix.det_mul, Matrix.mul_nonsing_inv _ hu,
      Matrix.det_one]

end Formalism.L2.SG.Pf.BlockPermutation
end
end

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def CondX (w : Point D.host.E (D.R.rS + 1)) (X : MatR D) : Prop :=
  ∀ a c : Fin (D.R.rS + 1), a < c → blkOf w.1 a.val = blkOf w.1 c.val →
    X (pinv w c) (pinv w a) ∈ ddPow D (c.val - a.val) ∧ bt D X⁻¹ a c ∈ ddPow D (c.val - a.val) ∧
      X (pinv w c) (pinv w a) - D.conjF (bt D X⁻¹ a c) ∈ qdPow D (c.val - a.val)

theorem entryShape_iff (w : Point D.host.E (D.R.rS + 1)) {β b : MatR D} (hβ : IsLoUni β) (hb : IsUpUni b)
    (hW : β * ptMat w * b = ptMat w) :
    EntryShape D β b ↔ CondX w ((ptMat w)⁻¹ * β * ptMat w) := by
  obtain ⟨hXb, hX, hXB⟩ := X_of_st w hβ hb hW
  set X := (ptMat w)⁻¹ * β * ptMat w with hXdef
  have hbX : b = X⁻¹ := by
    rw [hXb, Matrix.nonsing_inv_nonsing_inv _ (by rw [upU_det hb]; exact isUnit_one)]

  have hβX : β = ptMat w * X * (ptMat w)⁻¹ := by
    have hu := ptMat_isUnit w
    rw [hXdef, show ptMat w * ((ptMat w)⁻¹ * β * ptMat w) * (ptMat w)⁻¹ =
      (ptMat w * (ptMat w)⁻¹) * β * (ptMat w * (ptMat w)⁻¹) by simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
  have hβij : ∀ i j, β i j = cv w i * X (pinv w i) (pinv w j) * (cv w j)⁻¹ := by
    intro i j; rw [hβX, conj'_apply]

  have hXiB : IsBlockDiagonalMatrix w X⁻¹ := by
    have hβi : IsLoUni β⁻¹ := by
      have := loU_inv (show LoU β from hβ); exact this
    have hW' : β⁻¹ * ptMat w * X = ptMat w := by
      have hu := ptMat_isUnit w
      have hβd : IsUnit β.det := by rw [loU_det (show LoU β from hβ)]; exact isUnit_one
      rw [hXdef, show β⁻¹ * ptMat w * ((ptMat w)⁻¹ * β * ptMat w) = β⁻¹ * (ptMat w * (ptMat w)⁻¹) * β * ptMat w by
        simp only [Matrix.mul_assoc], Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hβd,
        Matrix.one_mul]
    obtain ⟨h1, -, h3⟩ := X_of_st w hβi hX hW'
    have hXi : (ptMat w)⁻¹ * β⁻¹ * ptMat w = X⁻¹ := h1
    rw [← hXi]; exact h3
  rw [hbX]
  constructor
  · intro h a c hac hs
    obtain ⟨h1, h2, h3⟩ := h c a hac
    have hcv : cv w c = cv w a := (pval_eq_blk w a c hs).symm
    have key : ∀ x : D.host.E, cv w a * (x * (cv w a)⁻¹) = x := fun x => by
      rw [mul_comm x, ← mul_assoc, mul_inv_cancel₀ (cv_ne w a), one_mul]
    rw [hβij, hcv, mul_assoc, key] at h1 h3
    exact ⟨h1, h2, h3⟩
  · intro h i j hji
    by_cases hs : blkOf w.1 j.val = blkOf w.1 i.val
    · obtain ⟨h1, h2, h3⟩ := h j i hji hs
      have hcv : cv w i = cv w j := (pval_eq_blk w j i hs).symm
      have key : ∀ x : D.host.E, cv w j * (x * (cv w j)⁻¹) = x := fun x => by
        rw [mul_comm x, ← mul_assoc, mul_inv_cancel₀ (cv_ne w j), one_mul]
      rw [hβij, hcv, mul_assoc, key]
      exact ⟨h1, h2, h3⟩
    · have hs' : blkOf w.1 (pinv w i).val ≠ blkOf w.1 (pinv w j).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
      have hb0 : X⁻¹ j i = 0 := hXiB j i hs
      have hbt : bt D X⁻¹ j i = 0 := by simp [bt, hb0]
      rw [hβij, hXB _ _ hs', mul_zero, zero_mul, hbt, map_zero, sub_zero]
      exact ⟨FractionalIdeal.zero_mem _, FractionalIdeal.zero_mem _, FractionalIdeal.zero_mem _⟩

theorem mem_stabInt_iff_X (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word)
    (w : Point D.host.E (D.R.rS + 1)) (β : GLR D) (hβ : IsLoUni (β : MatR D)) {b : MatR D} (hb : IsUpUni b)
    (hW : (β : MatR D) * ptMat w * b = ptMat w) :
    β ∈ stabInt D u u' δ M w ↔ CondX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) := by
  rw [stabIntShape D δ M hA u u' w β]
  constructor
  · rintro ⟨-, b', hb', hW', hE⟩
    exact (entryShape_iff w hβ hb' hW').1 hE
  · intro h
    exact ⟨hβ, b, hb, hW, (entryShape_iff w hβ hb hW).2 h⟩

end Formalism.L2.SG.Pf.StabIntSh
end
end

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

def hgt (q : FreeE w) : ℕ := q.1.2.val - q.1.1.val

theorem qbar_prop (q : FreeE w) :
    pinv w q.1.2 < pinv w q.1.1 ∧ blkOf w.1 (pinv w q.1.2).val = blkOf w.1 (pinv w q.1.1).val :=
  ⟨(pinv_lt_iff w q.1.1 q.1.2 q.2.2).1 q.2.1, by rw [blkOf_pinv, blkOf_pinv]; exact q.2.2.symm⟩

def qbar (q : FreeE w) : FreeE w := ⟨(pinv w q.1.2, pinv w q.1.1), qbar_prop w q⟩

def selfP (q : FreeE w) : Prop := qbar w q = q

def upperM (q : FreeE w) : Prop := (qbar w q).1.1 < q.1.1

def hpr (q : FreeE w) : ℕ := 2 * hgt w q + if upperM w q then 1 else 0

def sgq (q : FreeE w) : D.host.E := (-1) ^ (D.R.rS - q.1.1.val) * (-1) ^ (D.R.rS - q.1.2.val)

def Xmat (y : FreeE w → D.host.E) : MatR D := fun a c =>
  if a = c then 1 else if h : a < c ∧ blkOf w.1 a.val = blkOf w.1 c.val then y ⟨(a, c), h⟩ else 0

def trunc (y : FreeE w → D.host.E) (n : ℕ) : FreeE w → D.host.E := fun q => if hgt w q < n then y q else 0

def cf (y : FreeE w → D.host.E) (q : FreeE w) : D.host.E := ((Xmat w (trunc w y (hgt w q)))⁻¹) q.1.1 q.1.2


variable (D) in
def mOdd : ℕ := (gS D + 1) / 2

def τA (q : FreeE w) (y : FreeE w → D.host.E) : D.host.E :=
  if selfP w q then (mOdd D : D.host.E) * cf w y q
  else if upperM w q then sgq w (qbar w q) * D.conjF (-(y (qbar w q)) + cf w y (qbar w q))
  else 0


variable (D) in
def sLat (h : ℕ) (s : D.host.E) (_hs : D.conjF s = s) : AddSubgroup D.host.E where
  carrier := {z | z ∈ ddPow D h ∧ z + s * D.conjF z ∈ qdPow D h}
  zero_mem' := by
    refine ⟨FractionalIdeal.zero_mem _, ?_⟩
    simp only [map_zero, mul_zero, add_zero]; exact FractionalIdeal.zero_mem _
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨(ddPow D h : Submodule (𝓞 D.host.E) D.host.E).add_mem ha1 hb1, ?_⟩
    rw [map_add (f := _), show a + b + s * (D.conjF a + D.conjF b) = (a + s * D.conjF a) + (b + s * D.conjF b) by ring]
    exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).add_mem ha2 hb2
  neg_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨(ddPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem ha1, ?_⟩
    rw [map_neg, show -a + s * -D.conjF a = -(a + s * D.conjF a) by ring]
    exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem ha2

theorem sgq_conj (q : FreeE w) : D.conjF (sgq w q) = sgq w q := by
  simp [sgq, map_pow, map_neg, map_one]

def Iq (q : FreeE w) : FI D := if selfP w q ∨ ¬ upperM w q then ddPow D (hgt w q) else qdPow D (hgt w q)

def Λq (q : FreeE w) : AddSubgroup D.host.E :=
  if selfP w q then sLat D (hgt w q) (sgq w q) (sgq_conj w q)
  else ((Iq w q : FI D) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup


variable (D) in
def TwistC : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → Odd (gS D) → ∀ (w : Point D.host.E (D.R.rS + 1)) (y : FreeE w → D.host.E),
      CondX w (Xmat w y) ↔ ∀ q, y q - τA w q y ∈ Λq w q



end Formalism.L2.SG.Pf.StabIntLat
end
end

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ddS_ne : ddS D ≠ 0 := by
  intro h
  apply shapeNZ.1 1
  unfold ddPow; rw [h]; simp

theorem ddPow_mul (i j : ℕ) : ddPow D i * ddPow D j = ddPow D (i + j) := by
  unfold ddPow
  rw [← zpow_add₀ ddS_ne]
  congr 1; push_cast; ring

theorem mem_ddPow_mul {i j : ℕ} {x y : D.host.E} (hx : x ∈ ddPow D i) (hy : y ∈ ddPow D j) :
    x * y ∈ ddPow D (i + j) := by
  rw [← ddPow_mul]; exact FractionalIdeal.mul_mem_mul hx hy

theorem mem_qdPow_mul {i j : ℕ} {x y : D.host.E} (hx : x ∈ qdPow D i) (hy : y ∈ ddPow D j) :
    x * y ∈ qdPow D (i + j) := by
  have := FractionalIdeal.mul_mem_mul hx hy
  unfold qdPow at this ⊢
  rwa [mul_assoc, ddPow_mul] at this

theorem mem_ddPow_mul_qd {i j : ℕ} {x y : D.host.E} (hx : x ∈ ddPow D i) (hy : y ∈ qdPow D j) :
    x * y ∈ qdPow D (i + j) := by
  rw [mul_comm, add_comm]; exact mem_qdPow_mul hy hx

theorem one_mem_ddPow0 : (1 : D.host.E) ∈ ddPow D 0 := by
  unfold ddPow; simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
  exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩

theorem qd_le_dd (h : ℕ) {x : D.host.E} (hx : x ∈ qdPow D h) : x ∈ ddPow D h := by
  rw [qdPow_mem_iff] at hx
  have h2 : ((gS D : ℕ) : D.host.E) ∈ ddPow D 0 := by
    unfold ddPow; simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨(gS D : ℕ), map_natCast _ _⟩
  have := mem_ddPow_mul h2 hx
  rwa [zero_add, mul_div_cancel₀ _ gS_ne] at this

def GrD (M : MatR D) : Prop := ∀ a c : Fin (D.R.rS + 1), a ≤ c → M a c ∈ ddPow D (c.val - a.val)

theorem grD_inv {X : MatR D} (hX : UpU X) (hG : GrD X) : GrD X⁻¹ := by
  have hXi := upU_inv hX
  have hd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  have key : ∀ n : ℕ, ∀ a c : Fin (D.R.rS + 1), a ≤ c → c.val - a.val = n → X⁻¹ a c ∈ ddPow D n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a c hac hn
      rcases eq_or_lt_of_le hac with h | h
      · subst h; rw [(hXi a a).2 rfl]; simp only [Nat.sub_self] at hn; subst hn; exact one_mem_ddPow0
      ·
        have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv X hd) a) c
        rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt h), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
          (hX a a).2 rfl, one_mul] at h1
        have h2 : X⁻¹ a c = -∑ i ∈ Finset.univ.erase a, X a i * X⁻¹ i c := by
          rw [eq_neg_iff_add_eq_zero]; exact h1
        rw [h2]
        refine (ddPow D n : Submodule (𝓞 D.host.E) D.host.E).neg_mem (Submodule.sum_mem _ fun i hi => ?_)
        have hia : i ≠ a := Finset.ne_of_mem_erase hi
        by_cases hai : a < i
        · by_cases hic : i ≤ c
          · have hlt : c.val - i.val < n := by have : a.val < i.val := hai; omega
            have e : n = (i.val - a.val) + (c.val - i.val) := by have : a.val < i.val := hai; omega
            rw [e]
            exact mem_ddPow_mul (hG a i (le_of_lt hai)) (ih _ hlt i c hic rfl)
          · rw [(hXi i c).1 (lt_of_not_ge hic), mul_zero]; exact FractionalIdeal.zero_mem _
        · rw [(hX a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]; exact FractionalIdeal.zero_mem _
  intro a c hac
  exact key _ a c hac rfl

theorem inv_diff {X X' : MatR D} (hX : UpU X) (hX' : UpU X') {a c : Fin (D.R.rS + 1)} (hac : a < c)
    (hag : ∀ i j : Fin (D.R.rS + 1), i < j → j.val - i.val < c.val - a.val → X i j = X' i j) :
    X⁻¹ a c - X'⁻¹ a c = X' a c - X a c := by
  have hd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  have hd' : IsUnit X'.det := by rw [upU_det hX']; exact isUnit_one
  have hXi := upU_inv hX
  have hXi' := upU_inv hX'
  have hm : X⁻¹ - X'⁻¹ = X⁻¹ * (X' - X) * X'⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd', Matrix.mul_one]
  have e := congrFun (congrFun hm a) c
  rw [Matrix.sub_apply] at e
  rw [e, Matrix.mul_apply, Finset.sum_eq_single c]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hXi a a).2 rfl, (hXi' c c).2 rfl, one_mul, mul_one, Matrix.sub_apply]
    · intro i _ hia
      by_cases hai : a < i
      · rw [Matrix.sub_apply]
        by_cases hic : i < c
        · rw [hag i c hic (by have : a.val < i.val := hai; have : i.val < c.val := hic; omega), sub_self, mul_zero]
        · rcases eq_or_lt_of_le (not_lt.1 hic) with h | h
          · rw [h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]
          · rw [(hX' i c).1 h, (hX i c).1 h, sub_self, mul_zero]
      · rw [(hXi a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]
    · simp
  · intro j _ hjc
    by_cases hjc' : j < c
    · rw [Matrix.mul_apply]
      refine mul_eq_zero_of_left (Finset.sum_eq_zero fun i _ => ?_) _
      by_cases hai : a ≤ i
      · rw [Matrix.sub_apply]
        by_cases hij : i < j
        · rw [hag i j hij (by have : a.val ≤ i.val := hai; have : j.val < c.val := hjc'; omega), sub_self, mul_zero]
        · rcases eq_or_lt_of_le (not_lt.1 hij) with h | h
          · rw [h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]
          · rw [(hX' i j).1 h, (hX i j).1 h, sub_self, mul_zero]
      · rw [(hXi a i).1 (lt_of_not_ge hai), zero_mul]
    · rw [(hXi' j c).1 (lt_of_le_of_ne (not_lt.1 hjc') (Ne.symm hjc)), mul_zero]
  · simp

variable (w : Point D.host.E (D.R.rS + 1))

theorem Xmat_upU (y : FreeE w → D.host.E) : UpU (Xmat w y) := by
  intro a c
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [Xmat, ne_of_gt h, if_false]
    rw [dite_eq_right (fun h' => absurd h'.1 (not_lt.2 (le_of_lt h)))]
  · simp [Xmat, h]

theorem Xmat_blk (y : FreeE w → D.host.E) : IsBlockDiagonalMatrix w (Xmat w y) := by
  intro a c hne
  have hac : a ≠ c := fun e => hne (by rw [e])
  simp only [Xmat, hac, if_false]
  rw [dite_eq_right (fun h' => hne h'.2)]

theorem Xmat_q (y : FreeE w → D.host.E) (q : FreeE w) : Xmat w y q.1.1 q.1.2 = y q := by
  have hne : q.1.1 ≠ q.1.2 := ne_of_lt q.2.1
  simp only [Xmat, hne, if_false]
  rw [dite_eq_left q.2]
  rfl

theorem Xmat_grD (y : FreeE w → D.host.E) (hy : ∀ q, y q ∈ ddPow D (hgt w q)) : GrD (Xmat w y) := by
  intro a c hac
  rcases eq_or_lt_of_le hac with h | h
  · subst h; simp only [Xmat, if_true, Nat.sub_self]; exact one_mem_ddPow0
  · by_cases hb : blkOf w.1 a.val = blkOf w.1 c.val
    · have := Xmat_q w y ⟨(a, c), h, hb⟩
      simp only at this; rw [this]; exact hy ⟨(a, c), h, hb⟩
    · rw [Xmat_blk w y a c hb]; exact FractionalIdeal.zero_mem _

end Formalism.L2.SG.Pf.StabIntLat
end
end

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Conj

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (hA : ∀ q, Agree δ M q)

include hA in
theorem dd_conj {h : ℕ} (hk : h ≤ D.R.rS) {x : D.host.E} (hx : x ∈ ddPow D h) : D.conjF x ∈ ddPow D h := by
  rw [← locGlob _ (shapeNZ.1 h)] at hx ⊢
  exact fun p => locMem_conj δ M hA p hk (hx p)

include hA in
theorem qd_conj {h : ℕ} (hk : h ≤ D.R.rS) {x : D.host.E} (hx : x ∈ qdPow D h) : D.conjF x ∈ qdPow D h := by
  rw [qdPow_mem_iff] at hx ⊢
  have := dd_conj δ M hA hk hx
  rwa [map_div₀, map_natCast] at this

end Conj

theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : D.host.E) ^ k) * (-1) ^ k = 1 := by
  rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩

variable (w : Point D.host.E (D.R.rS + 1))

def sgm (a c : Fin (D.R.rS + 1)) : D.host.E := (-1) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val)

omit w in
theorem sgm_mul (a d c : Fin (D.R.rS + 1)) : sgm a d * sgm d c = sgm a c := by
  unfold sgm
  have := neg_one_pow_mul_self (D := D) (D.R.rS - d.val)
  linear_combination ((-1 : D.host.E) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val)) * this

omit w in
theorem sgm_self (a : Fin (D.R.rS + 1)) : sgm a a = (1 : D.host.E) := neg_one_pow_mul_self _

omit w in
theorem sgm_conj (a c : Fin (D.R.rS + 1)) : D.conjF (sgm a c) = sgm a c := by
  simp [sgm, map_pow, map_neg, map_one]

omit w in
theorem sgm_cases (a c : Fin (D.R.rS + 1)) : sgm a c = (1 : D.host.E) ∨ sgm a c = -1 := by
  unfold sgm
  rw [← pow_add]
  exact neg_one_pow_eq_or _ _

theorem sgm_pinv (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    sgm a c * sgm (pinv w c) (pinv w a) = (1 : D.host.E) := by
  unfold sgm
  have h1 := pinv_add w a c hs
  have ha := a.isLt; have hc := c.isLt; have ha' := (pinv w a).isLt; have hc' := (pinv w c).isLt
  rw [show ((-1 : D.host.E)) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val) *
      ((-1) ^ (D.R.rS - (pinv w c).val) * (-1) ^ (D.R.rS - (pinv w a).val)) =
      (-1) ^ ((D.R.rS - a.val) + (D.R.rS - c.val) + (D.R.rS - (pinv w c).val) + (D.R.rS - (pinv w a).val)) by ring]
  exact Even.neg_one_pow ⟨2 * D.R.rS - (pinv w a).val - a.val, by omega⟩

def Psi (Mt : MatR D) : MatR D := fun a c => sgm a c * D.conjF (Mt (pinv w c) (pinv w a))

def piPerm : Equiv.Perm (Fin (D.R.rS + 1)) := ⟨pinv w, pinv w, pinv_pinv w, pinv_pinv w⟩

theorem Psi_sub (A B : MatR D) : Psi w (A - B) = Psi w A - Psi w B := by
  funext a c; simp [Psi, map_sub, mul_sub]

theorem Psi_mul (A B : MatR D) : Psi w (A * B) = Psi w B * Psi w A := by
  funext a c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Psi, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (piPerm w) _ _ (fun e => ?_)
  simp only [piPerm, Equiv.coe_fn_mk, pinv_pinv]
  rw [← sgm_mul a (pinv w e) c]; ring

theorem Psi_one : Psi w (1 : MatR D) = 1 := by
  funext a c
  simp only [Psi, Matrix.one_apply]
  by_cases h : a = c
  · subst h; simp [sgm_self]
  · have : pinv w c ≠ pinv w a := fun e => h (pinv_inj w e).symm
    simp [this, h]

theorem Psi_inv {A : MatR D} (hA : IsUnit A.det) : Psi w A⁻¹ = (Psi w A)⁻¹ := by
  have : Psi w A⁻¹ * Psi w A = 1 := by rw [← Psi_mul, Matrix.mul_nonsing_inv _ hA, Psi_one]
  exact (Matrix.inv_eq_left_inv this).symm

theorem Psi_Psi {A : MatR D} (hB : IsBlockDiagonalMatrix w A) : Psi w (Psi w A) = A := by
  funext a c
  simp only [Psi, pinv_pinv, map_mul, Formalism.MainNotions.BridgeLemma.conjF_inv, sgm_conj]
  by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
  · rw [← mul_assoc, sgm_pinv w a c hs, one_mul]
  · rw [hB a c hs, mul_zero, mul_zero]

theorem Psi_blk {A : MatR D} (hB : IsBlockDiagonalMatrix w A) : IsBlockDiagonalMatrix w (Psi w A) := by
  intro a c hne
  have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
    rw [blkOf_pinv, blkOf_pinv]; exact fun e => hne e.symm
  simp only [Psi, hB _ _ this, map_zero, mul_zero]

theorem Psi_upU {A : MatR D} (hU : UpU A) (hB : IsBlockDiagonalMatrix w A) : UpU (Psi w A) := by
  intro a c
  refine ⟨fun hca => ?_, fun hac => ?_⟩
  · simp only [Psi]
    by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
    · have := (pinv_lt_iff w c a hs.symm).1 hca
      rw [(hU _ _).1 this, map_zero, mul_zero]
    · have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
      rw [hB _ _ this, map_zero, mul_zero]
  · subst hac; simp [Psi, sgm_self, (hU _ _).2 rfl]

theorem Psi_grD (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ q, Agree δ M q) {A : MatR D} (hB : IsBlockDiagonalMatrix w A) (hG : GrD A) : GrD (Psi w A) := by
  intro a c hac
  simp only [Psi]
  by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
  · have hle : pinv w c ≤ pinv w a := by
      rcases eq_or_lt_of_le hac with h | h
      · rw [h]
      · exact le_of_lt ((pinv_lt_iff w a c hs).1 h)
    have hh : (pinv w a).val - (pinv w c).val = c.val - a.val := by
      have := pinv_add w a c hs; omega
    have h1 := hG _ _ hle
    rw [hh] at h1
    have h2 := dd_conj δ M hA (by have := c.isLt; omega) h1
    rcases sgm_cases a c with e | e
    · rw [e, one_mul]; exact h2
    · rw [e, neg_one_mul]; exact (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem h2
  · have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
      rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
    rw [hB _ _ this, map_zero, mul_zero]; exact FractionalIdeal.zero_mem _

theorem blk_inv {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) : IsBlockDiagonalMatrix w X⁻¹ := by
  obtain ⟨hlo, hXi, hW, -⟩ := st_of_X w hU hB
  set β := ptMat w * X * (ptMat w)⁻¹
  have hu := ptMat_isUnit w
  have hβd : IsUnit β.det := by rw [loU_det (show LoU β from hlo)]; exact isUnit_one
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hW' : β⁻¹ * ptMat w * X = ptMat w := by
    have : ptMat w * X⁻¹ = β⁻¹ * ptMat w := by
      calc ptMat w * X⁻¹ = β⁻¹ * (β * ptMat w * X⁻¹) := by
            rw [Matrix.mul_assoc β]; exact (Matrix.nonsing_inv_mul_cancel_left β _ hβd).symm
        _ = β⁻¹ * ptMat w := by rw [hW]
    rw [← this, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hXd, Matrix.mul_one]
  obtain ⟨h1, -, h3⟩ := X_of_st w (loU_inv (show LoU β from hlo)) hU hW'
  rw [h1] at h3
  exact h3

end Formalism.L2.SG.Pf.StabIntLat
end
end

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

theorem E_strict {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) (i j : Fin (D.R.rS + 1)) (hji : j ≤ i) :
    (X - Psi w X⁻¹) i j = 0 := by
  have hP := Psi_upU w (upU_inv hU) (blk_inv w hU hB)
  rw [Matrix.sub_apply]
  rcases eq_or_lt_of_le hji with h | h
  · subst h; rw [(hU _ _).2 rfl, (hP _ _).2 rfl, sub_self]
  · rw [(hU _ _).1 h, (hP _ _).1 h, sub_self]

theorem unitCons (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ q, Agree δ M q) {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) (hG : GrD X)
    {a c : Fin (D.R.rS + 1)} (hac : a < c)
    (hlow : ∀ i j : Fin (D.R.rS + 1), i < j → j.val - i.val < c.val - a.val →
      (X - Psi w X⁻¹) i j ∈ qdPow D (j.val - i.val)) :
    Psi w (X - Psi w X⁻¹) a c - (X - Psi w X⁻¹) a c ∈ qdPow D (c.val - a.val) := by
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hXi := upU_inv hU
  have hBi := blk_inv w hU hB
  have hGi := grD_inv hU hG
  have hY := Psi_upU w hU hB
  have hGY := Psi_grD w δ M hA hB hG
  have hPi : Psi w X⁻¹ = (Psi w X)⁻¹ := Psi_inv w hXd
  have hYd : IsUnit (Psi w X).det := by rw [upU_det hY]; exact isUnit_one
  have hES := E_strict w hU hB
  have hPE : Psi w (X - Psi w X⁻¹) = Psi w X * (X - Psi w X⁻¹) * X⁻¹ := by
    rw [Psi_sub, Psi_Psi w hBi, hPi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hXd,
      Matrix.mul_nonsing_inv _ hYd, Matrix.one_mul]
  have decomp : Psi w X * (X - Psi w X⁻¹) * X⁻¹ - (X - Psi w X⁻¹) =
      (Psi w X - 1) * (X - Psi w X⁻¹) * X⁻¹ + (X - Psi w X⁻¹) * (X⁻¹ - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
  rw [hPE, ← Matrix.sub_apply, decomp, Matrix.add_apply]
  have hac' : a.val < c.val := hac
  refine (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem ?_ ?_
  · rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h1 : a < i
    · have h1' : a.val < i.val := h1
      by_cases h2 : i < j
      · have h2' : i.val < j.val := h2
        by_cases h3 : j ≤ c
        · have h3' : j.val ≤ c.val := h3
          rw [show (Psi w X - 1) a i = Psi w X a i by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h1), sub_zero]]
          have m1 := hGY a i (le_of_lt h1)
          have m2 := hlow i j h2 (by omega)
          have m3 := hGi j c h3
          have := mem_qdPow_mul (mem_ddPow_mul_qd m1 m2) m3
          rwa [show i.val - a.val + (j.val - i.val) + (c.val - j.val) = c.val - a.val by omega] at this
        · rw [(hXi j c).1 (lt_of_not_ge h3), mul_zero]; exact FractionalIdeal.zero_mem _
      · rw [hES i j (not_lt.1 h2), mul_zero, zero_mul]; exact FractionalIdeal.zero_mem _
    · have h0 : (Psi w X - 1) a i = 0 := by
        rw [Matrix.sub_apply]
        rcases eq_or_lt_of_le (not_lt.1 h1) with h | h
        · rw [h, (hY _ _).2 rfl, Matrix.one_apply_eq, sub_self]
        · rw [(hY _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
      rw [h0, zero_mul, zero_mul]; exact FractionalIdeal.zero_mem _
  · rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases h1 : a < j
    · have h1' : a.val < j.val := h1
      by_cases h2 : j < c
      · have h2' : j.val < c.val := h2
        rw [show (X⁻¹ - 1) j c = X⁻¹ j c by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h2), sub_zero]]
        have := mem_qdPow_mul (hlow a j h1 (by omega)) (hGi j c (le_of_lt h2))
        rwa [show j.val - a.val + (c.val - j.val) = c.val - a.val by omega] at this
      · have h0 : (X⁻¹ - 1) j c = 0 := by
          rw [Matrix.sub_apply]
          rcases eq_or_lt_of_le (not_lt.1 h2) with h | h
          · rw [h, (hXi _ _).2 rfl, Matrix.one_apply_eq, sub_self]
          · rw [(hXi _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
        rw [h0, mul_zero]; exact FractionalIdeal.zero_mem _
    · rw [hES a j (not_lt.1 h1), zero_mul]; exact FractionalIdeal.zero_mem _

end Formalism.L2.SG.Pf.StabIntLat
