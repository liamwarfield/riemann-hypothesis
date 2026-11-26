module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittAlg
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

section Form

variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

theorem hform_eq_dot (x y : Fin n → S) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_sub_left (x y z : Fin n → S) :
    hform s J (x - y) z = hform s J x z - hform s J y z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, ← sub_dotProduct]
  congr 1
  ext i
  simp

theorem hform_sub_right (x y z : Fin n → S) :
    hform s J x (y - z) = hform s J x y - hform s J x z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, mulVec_sub, dotProduct_sub]

theorem hform_add_left (x y z : Fin n → S) :
    hform s J (x + y) z = hform s J x z + hform s J y z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, ← add_dotProduct]
  congr 1
  ext i
  simp

theorem hform_add_right (x y z : Fin n → S) :
    hform s J x (y + z) = hform s J x y + hform s J x z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, mulVec_add, dotProduct_add]

theorem hform_smul_left (a : S) (x y : Fin n → S) :
    hform s J (a • x) y = s a * hform s J x y := by
  rw [hform_eq_dot, hform_eq_dot, ← smul_eq_mul, ← smul_dotProduct]
  congr 1
  ext i
  simp

theorem hform_smul_right (a : S) (x y : Fin n → S) :
    hform s J x (a • y) = a * hform s J x y := by
  rw [hform_eq_dot, hform_eq_dot, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hform_zero_left (y : Fin n → S) : hform s J 0 y = 0 := by simp [hform]

theorem hform_zero_right (x : Fin n → S) : hform s J x 0 = 0 := by simp [hform]

theorem hform_sum_right {ι : Type} (t : Finset ι) (c : ι → S) (v : ι → Fin n → S) (z : Fin n → S) :
    hform s J z (∑ i ∈ t, c i • v i) = ∑ i ∈ t, c i * hform s J z (v i) := by
  induction t using Finset.cons_induction with
  | empty => simp [hform_zero_right]
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, hform_add_right, hform_smul_right, ih]

theorem hform_sum_left {ι : Type} (t : Finset ι) (c : ι → S) (v : ι → Fin n → S) (z : Fin n → S) :
    hform s J (∑ i ∈ t, c i • v i) z = ∑ i ∈ t, s (c i) * hform s J (v i) z := by
  induction t using Finset.cons_induction with
  | empty => simp [hform_zero_left]
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, hform_add_left, hform_smul_left, ih]

theorem hform_conj (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (x y : Fin n → S) :
    s (hform s J x y) = hform s J y x := by
  have hJ' : ∀ i j, s (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [cT] using this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hs, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_single (i j : Fin n) :
    hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite]

theorem hform_entry (T : Matrix (Fin n) (Fin n) S) (i j : Fin n) :
    (cT s T * J * T) i j = hform s J (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1) := by
  rw [mulVec_single_one, mulVec_single_one]
  simp only [hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem unitary_of (T : Matrix (Fin n) (Fin n) S) (h : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w) :
    cT s T * J * T = J := by
  ext i j
  rw [hform_entry, h, hform_single]

def rT (u : Fin n → S) (ci lam : S) : Matrix (Fin n) (Fin n) S :=
  s lam • (1 - ci • vecMulVec u (vecMul (fun i => s (u i)) J))

theorem rT_mulVec (u : Fin n → S) (ci lam : S) (z : Fin n → S) :
    rT s J u ci lam *ᵥ z = s lam • (z - (ci * hform s J u z) • u) := by
  rw [rT, smul_mulVec, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
    ← hform_eq_dot, op_smul_eq_smul, smul_smul]

theorem rT_preserves (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (u : Fin n → S) (c ci lam : S)
    (hlam : lam * s lam = 1) (huu : hform s J u u = c + s c) (e2 : ci * c = 1) (z w : Fin n → S) :
    hform s J (rT s J u ci lam *ᵥ z) (rT s J u ci lam *ᵥ w) = hform s J z w := by
  have e3 : s ci * s c = 1 := by rw [← map_mul, e2, map_one]
  have hconj := hform_conj s J hs hJ
  rw [rT_mulVec, rT_mulVec]
  simp only [hform_smul_left, hform_smul_right, hform_sub_left, hform_sub_right, map_mul, hs, hconj]
  rw [huu]
  linear_combination
    (hform s J z w - ci * hform s J u w * hform s J z u
      - s ci * hform s J z u * (hform s J u w - ci * hform s J u w * (c + s c))) * hlam
    + hform s J z u * hform s J u w * (s ci * e2 + ci * e3)

def pM {a : ℕ} (t : Finset (Fin a)) (y : Fin a → Fin n → S) (β' : Fin a → S) : Matrix (Fin n) (Fin n) S :=
  ∑ i ∈ t, β' i • vecMulVec (y i) (vecMul (fun k => s (y i k)) J)

theorem pM_mulVec {a : ℕ} (t : Finset (Fin a)) (y : Fin a → Fin n → S) (β' : Fin a → S) (z : Fin n → S) :
    pM s J t y β' *ᵥ z = ∑ i ∈ t, (β' i * hform s J (y i) z) • y i := by
  unfold pM
  induction t using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, add_mulVec, ih, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
      ← hform_eq_dot, op_smul_eq_smul, smul_smul]

end Form

section Int

variable {S : Type} [CommRing S] (O : Subring S)

theorem mulVec_mem {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (hM : ∀ i j, M i j ∈ O) (z : Fin n → S)
    (hz : ∀ k, z k ∈ O) (k : Fin n) : (M *ᵥ z) k ∈ O := by
  simp only [mulVec, dotProduct]
  exact O.sum_mem fun j _ => O.mul_mem (hM k j) (hz j)

theorem mul_mem' {n : ℕ} (M N : Matrix (Fin n) (Fin n) S) (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O)
    (i j : Fin n) : (M * N) i j ∈ O := by
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hM i k) (hN k j)

theorem one_mem' {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) S) i j ∈ O := by
  rw [Matrix.one_apply]
  split_ifs
  exacts [O.one_mem, O.zero_mem]

variable (s : S →+* S) (hsO : ∀ z ∈ O, s z ∈ O)
include hsO

theorem hform_mem {n : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (x y : Fin n → S)
    (hx : ∀ k, x k ∈ O) (hy : ∀ k, y k ∈ O) : hform s J x y ∈ O :=
  O.sum_mem fun i _ => O.sum_mem fun j _ => O.mul_mem (O.mul_mem (hsO _ (hx i)) (hJ i j)) (hy j)

theorem cT_mem {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (hM : ∀ i j, M i j ∈ O) (i j : Fin n) :
    cT s M i j ∈ O := by
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact hsO _ (hM j i)

theorem vmv_mem {n : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (u : Fin n → S)
    (hu : ∀ k, u k ∈ O) (i j : Fin n) : vecMulVec u (vecMul (fun k => s (u k)) J) i j ∈ O := by
  simp only [vecMulVec_apply, vecMul, dotProduct]
  exact O.mul_mem (hu i) (O.sum_mem fun k _ => O.mul_mem (hsO _ (hu k)) (hJ k j))

theorem rT_mem {n : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (u : Fin n → S)
    (hu : ∀ k, u k ∈ O) (ci lam : S) (hci : ci ∈ O) (hlam : lam ∈ O) (i j : Fin n) : rT s J u ci lam i j ∈ O := by
  simp only [rT, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  exact O.mul_mem (hsO _ hlam) (O.sub_mem (one_mem' O i j) (O.mul_mem hci (vmv_mem O s hsO J hJ u hu i j)))

theorem pM_mem {n a : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (t : Finset (Fin a))
    (y : Fin a → Fin n → S) (hy : ∀ i k, y i k ∈ O) (β' : Fin a → S) (hβ' : ∀ i, β' i ∈ O) (i j : Fin n) :
    pM s J t y β' i j ∈ O := by
  simp only [pM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact O.sum_mem fun k _ => O.mul_mem (hβ' k) (vmv_mem O s hsO J hJ (y k) (hy k) i j)

end Int

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlgWitt
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

private theorem s_inv_eq_of_s_eq_of_mul_eq_one {S : Type} [CommRing S] (s : S →+* S) (b b' : S) (hb : s b = b)
    (h : b * b' = 1) : s b' = b' := by
  have h1 : s b * s b' = 1 := by rw [← map_mul, h, map_one]
  rw [hb] at h1
  calc s b' = (b' * b) * s b' := by rw [mul_comm b' b, h, one_mul]
    _ = b' * (b * s b') := by ring
    _ = b' := by rw [h1, mul_one]

private theorem hform_transvection_preserves {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ z, s (s z) = z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : IsHerm s J) (v : Fin n → S) (b b' lam : S)
    (hvv : hform s J v v = b) (hbb : b * b' = 1) (hb' : s b' = b') (hlam : lam * s lam = 1)
    (z w : Fin n → S) :
    hform s J (z + ((s lam - 1) * (b' * hform s J v z)) • v)
      (w + ((s lam - 1) * (b' * hform s J v w)) • v) = hform s J z w := by
  have hzv : hform s J z v = s (hform s J v z) := (hform_conj s J hs hJ v z).symm
  simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
  rw [hzv, hvv]
  simp only [map_mul, map_sub, map_one, hs, hb']
  linear_combination (b' * hform s J v w * s (hform s J v z)) * hlam +
    (b' * hform s J v w * s (hform s J v z) * (lam - 1) * (s lam - 1)) * hbb

theorem algWitt : Formalism.L2.SG.Pf.NcS.IntWittPf.AlgWitt := by
  unfold Formalism.L2.SG.Pf.NcS.IntWittPf.AlgWitt
  intro S _ s O hs hsO n J J' hJ hJJ' hJO hJ'O a β β' hβO hβ'O hββ' hH x y hxO hyO hxx hyy

  have key : ∀ k : ℕ, k ≤ a → ∃ M : Matrix (Fin n) (Fin n) S,
      (∀ z w, hform s J (M *ᵥ z) (M *ᵥ w) = hform s J z w) ∧ (∀ i j, M i j ∈ O) ∧
      ∀ i : Fin a, i.val < k → M *ᵥ y i = x i := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨1, fun z w => by rw [Matrix.one_mulVec, Matrix.one_mulVec],
        fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.one_mem' O i j, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨M, hMp, hMO, hMy⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨i0, hi0⟩ : ∃ i0 : Fin a, i0.val = k := ⟨⟨k, hk⟩, rfl⟩
      obtain ⟨yy, hyy_def⟩ : ∃ yy : Fin n → S, yy = M *ᵥ y i0 := ⟨_, rfl⟩
      have hyyO : ∀ l, yy l ∈ O := fun l => by
        rw [hyy_def]; exact mulVec_mem O M hMO (y i0) (hyO i0) l
      have htO : hform s J (x i0) yy ∈ O := hform_mem O s hsO J hJO (x i0) yy (hxO i0) hyyO
      obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := hH i0 (hform s J (x i0) yy) htO
      have hxx0 : hform s J (x i0) (x i0) = β i0 := by rw [hxx, if_pos rfl]
      have hyy0 : hform s J yy yy = β i0 := by rw [hyy_def, hMp, hyy, if_pos rfl]
      have hβr : s (β i0) = β i0 := by
        have h := hform_conj s J hs hJ (x i0) (x i0)
        rwa [hxx0] at h
      have hβ'r : s (β' i0) = β' i0 := s_inv_eq_of_s_eq_of_mul_eq_one s (β i0) (β' i0) hβr (hββ' i0)

      obtain ⟨u, hu_def⟩ : ∃ u : Fin n → S, u = yy - lam • x i0 := ⟨_, rfl⟩
      have huO : ∀ l, u l ∈ O := fun l => by
        rw [hu_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact O.sub_mem (hyyO l) (O.mul_mem hlamO (hxO i0 l))
      have huy : hform s J u yy = β i0 - s lam * hform s J (x i0) yy := by
        rw [hu_def, hform_sub_left, hform_smul_left, hyy0]
      have huu : hform s J u u =
          (β i0 - s lam * hform s J (x i0) yy) + s (β i0 - s lam * hform s J (x i0) yy) := by
        rw [hu_def]
        simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right]
        rw [hyy0, hxx0, ← hform_conj s J hs hJ (x i0) yy]
        simp only [map_sub, map_mul, hs, hβr]
        linear_combination (β i0) * hlam
      have hcc : c' * (β i0 - s lam * hform s J (x i0) yy) = 1 := by rw [mul_comm]; exact hc'
      obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) S, T = rT s J u c' 1 := ⟨_, rfl⟩
      have hT_mul : ∀ z, T *ᵥ z = z - (c' * hform s J u z) • u := fun z => by
        rw [hT, rT_mulVec, map_one, one_smul]
      have hT_pres : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w := fun z w => by
        rw [hT]
        exact rT_preserves s J hs hJ u _ c' 1 (by rw [map_one, one_mul]) huu hcc z w
      have hT_O : ∀ i j, T i j ∈ O := fun i j => by
        rw [hT]; exact rT_mem O s hsO J hJO u huO c' 1 hc'O O.one_mem i j
      have hT_yy : T *ᵥ yy = lam • x i0 := by
        rw [hT_mul, huy, hcc, one_smul, hu_def, sub_sub_cancel]

      obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin n) S,
          D = 1 + (s lam - 1) • pM s J {i0} x β' := ⟨_, rfl⟩
      have hD_mul : ∀ z, D *ᵥ z = z + ((s lam - 1) * (β' i0 * hform s J (x i0) z)) • x i0 :=
        fun z => by
          rw [hD, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, pM_mulVec,
            Finset.sum_singleton, smul_smul]
      have hD_pres : ∀ z w, hform s J (D *ᵥ z) (D *ᵥ w) = hform s J z w := fun z w => by
        rw [hD_mul, hD_mul]
        exact hform_transvection_preserves s hs J hJ (x i0) (β i0) (β' i0) lam hxx0 (hββ' i0) hβ'r hlam z w
      have hD_O : ∀ i j, D i j ∈ O := fun i j => by
        rw [hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        exact O.add_mem (Formalism.L2.SG.Pf.NcS.IntWittAlg.one_mem' O i j)
          (O.mul_mem (O.sub_mem (hsO lam hlamO) O.one_mem)
            (pM_mem O s hsO J hJO {i0} x hxO β' hβ'O i j))
      have hD_x : D *ᵥ (lam • x i0) = x i0 := by
        rw [hD_mul, hform_smul_right, hxx0]
        funext l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (x i0 l) * hlam + (x i0 l * (lam * s lam - lam)) * hββ' i0

      have hfix : ∀ i : Fin a, i.val < k → D *ᵥ (T *ᵥ x i) = x i := by
        intro i hi
        have hne : i0 ≠ i := fun h => by subst h; omega
        have h0 : hform s J u (x i) = 0 := by
          rw [hu_def, hform_sub_left, hform_smul_left, hxx i0 i, if_neg hne, ← hMy i hi, hyy_def,
            hMp, hyy i0 i, if_neg hne]
          ring
        rw [hT_mul, h0, mul_zero, zero_smul, sub_zero, hD_mul, hxx i0 i, if_neg hne, mul_zero,
          mul_zero, zero_smul, add_zero]
      refine ⟨D * T * M, fun z w => ?_, fun i j => ?_, fun i hi => ?_⟩
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hD_pres, hT_pres, hMp]
      · exact Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O (D * T) M
          (fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O D T hD_O hT_O i j) hMO i j
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · rw [hMy i hlt]; exact hfix i hlt
        · have hi' : i = i0 := Fin.ext (by omega)
          rw [hi', ← hyy_def, hT_yy, hD_x]
  obtain ⟨M, hMp, hMO, hMy⟩ := key a le_rfl
  have hU : cT s M * J * M = J := unitary_of s J M hMp
  have hNM : (J' * cT s M * J) * M = 1 := by
    calc (J' * cT s M * J) * M = J' * (cT s M * J * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hJJ']
  have hMN : M * (J' * cT s M * J) = 1 := mul_eq_one_comm.mp hNM
  refine ⟨⟨M, J' * cT s M * J, hMN, hNM⟩, ?_, fun i j => hMO i j, fun i j => ?_, fun i => hMy i i.isLt⟩
  · show cT s M * J * M = J
    exact hU
  · show (J' * cT s M * J) i j ∈ O
    exact Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O (J' * cT s M) J
      (fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O J' (cT s M) hJ'O
        (fun i j => cT_mem O s hsO M hMO i j) i j) hJO i j

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittGS
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

section GS

variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (J : Matrix (Fin n) (Fin n) K)

theorem exists_aniso (hσ : ∀ z, σ (σ z) = z) (hJ : IsHerm σ J) (h2 : (2 : K) ≠ 0) (u w : Fin n → K)
    (huw : hform σ J u w ≠ 0) : ∃ r t : K, hform σ J (r • u + t • w) (r • u + t • w) ≠ 0 := by
  by_contra H
  push Not at H
  have hexp : ∀ r t : K, hform σ J (r • u + t • w) (r • u + t • w) =
      σ r * r * hform σ J u u + σ r * t * hform σ J u w + σ t * r * hform σ J w u +
        σ t * t * hform σ J w w := by
    intro r t
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
    ring
  set q := hform σ J u w with hq
  set t : K := 2⁻¹ / q with htdef
  have h1 := H 1 0
  have h2' := H 0 1
  have h3 := H 1 t
  rw [hexp, map_one, map_zero] at h1 h2'
  rw [hexp, map_one] at h3
  have ht : t * q = 2⁻¹ := div_mul_cancel₀ _ huw
  have hst : σ t * hform σ J w u = 2⁻¹ := by
    rw [← hform_conj σ J hσ hJ u w, ← hq, ← map_mul, ht, map_inv₀, map_ofNat]
  have hinv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  exact one_ne_zero (by linear_combination h3 - h1 - (σ t * t) * h2' - ht - hst - hinv : (1 : K) = 0)

end GS

theorem hermDiag : Formalism.L2.SG.Pf.NcS.IntWittPf.HermDiag := by
  intro K _ σ hσ h2 n J hJ a X0 hT
  classical
  have hconj := hform_conj σ J hσ hJ
  let W : Submodule K (Fin n → K) := Submodule.span K (Set.range X0)
  let comb : (Fin a → K) → (Fin n → K) := fun c => ∑ l, c l • X0 l
  have hN : ∀ c : Fin a → K, (∀ j, hform σ J (X0 j) (comb c) = 0) → c = 0 := by
    intro c hc
    refine Matrix.eq_zero_of_mulVec_eq_zero hT ?_
    funext j
    have e : hform σ J (X0 j) (∑ l, c l • X0 l) = 0 := hc j
    rw [hform_sum_right] at e
    simp only [mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hcW : ∀ c, comb c ∈ W := fun c => W.sum_mem fun l _ => W.smul_mem _ (Submodule.subset_span ⟨l, rfl⟩)
  have main : ∀ k ≤ a, ∃ Z : Fin k → Fin n → K, (∀ i, Z i ∈ W) ∧
      (∀ i j, i ≠ j → hform σ J (Z i) (Z j) = 0) ∧ ∀ i, hform σ J (Z i) (Z i) ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨Z, hZW, hZo, hZd⟩ := ih (by omega)
      let f : (Fin a → K) →ₗ[K] (Fin k → K) :=
        { toFun := fun c i => hform σ J (Z i) (comb c)
          map_add' := by
            intro c d
            funext i
            simp only [comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, hform_add_right]
          map_smul' := by
            intro r c
            funext i
            simp only [comb, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← smul_smul, ← Finset.smul_sum,
              hform_smul_right] }
      have hlt : Module.finrank K (Fin k → K) < Module.finrank K (Fin a → K) := by
        simp only [Module.finrank_fin_fun]
        omega
      obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
      have hcZ : ∀ i, hform σ J (Z i) (comb c) = 0 := fun i => congrFun (LinearMap.mem_ker.1 hc) i
      obtain ⟨j, hj⟩ : ∃ j, hform σ J (X0 j) (comb c) ≠ 0 := by
        by_contra H
        push Not at H
        exact hc0 (hN c H)
      let w := X0 j - ∑ i, (hform σ J (Z i) (X0 j) / hform σ J (Z i) (Z i)) • Z i
      have hwZ : ∀ m, hform σ J (Z m) w = 0 := by
        intro m
        simp only [w, hform_sub_right, hform_sum_right]
        rw [Finset.sum_eq_single m]
        · rw [div_mul_cancel₀ _ (hZd m), sub_self]
        · intro i _ him
          rw [hZo m i (Ne.symm him), mul_zero]
        · simp
      have hwc : hform σ J w (comb c) ≠ 0 := by
        simp only [w, hform_sub_left, hform_sum_left]
        rw [Finset.sum_eq_zero, sub_zero]
        · exact hj
        · intro i _
          rw [hcZ i, mul_zero]
      have hwW : w ∈ W := W.sub_mem (Submodule.subset_span ⟨j, rfl⟩) (W.sum_mem fun i _ => W.smul_mem _ (hZW i))
      obtain ⟨r, t, hz⟩ := exists_aniso σ J hσ hJ h2 w (comb c) hwc
      set z := r • w + t • comb c with hzdef
      have hzZ : ∀ m, hform σ J (Z m) z = 0 := by
        intro m
        rw [hzdef, hform_add_right, hform_smul_right, hform_smul_right, hwZ, hcZ, mul_zero, mul_zero, add_zero]
      refine ⟨Fin.snoc Z z, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact W.add_mem (W.smul_mem _ hwW) (W.smul_mem _ (hcW c))
        · rw [Fin.snoc_castSucc]
          exact hZW i
      · intro i j
        refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h; exact absurd rfl h
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc, ← hconj, hzZ, map_zero]
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact hzZ i
        · intro hij
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hZo i j (fun e => hij (by rw [e]))
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact hz
        · rw [Fin.snoc_castSucc]
          exact hZd i
  obtain ⟨Z, hZW, hZo, hZd⟩ := main a le_rfl
  have hex : ∀ i, ∃ c : Fin a → K, ∑ l, c l • X0 l = Z i :=
    fun i => (Submodule.mem_span_range_iff_exists_fun K).1 (hZW i)
  choose C hC using hex
  let P : Matrix (Fin a) (Fin a) K := Matrix.of C
  have hPX : ∀ i, ∑ l, P i l • X0 l = Z i := fun i => hC i
  have hdet : P.det ≠ 0 := by
    intro hd
    obtain ⟨c, hc0, hcP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    apply hc0
    funext j
    have e : ∑ i, c i • Z i = 0 := by
      have hl : ∀ l, ∑ i, c i * P i l = 0 := fun l => by
        have := congrFun hcP l
        simpa [vecMul, dotProduct] using this
      simp_rw [← hPX, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hl, zero_smul, Finset.sum_const_zero]
    have h := congrArg (hform σ J (Z j)) e
    rw [hform_sum_right, hform_zero_right, Finset.sum_eq_single j] at h
    · exact (mul_eq_zero.1 h).resolve_right (hZd j)
    · intro i _ hij
      rw [hZo j i (Ne.symm hij), mul_zero]
    · simp
  refine ⟨P, P⁻¹, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.2 hdet), ?_, ?_⟩
  · intro i j hij
    rw [hPX, hPX]
    exact hZo i j hij
  · intro i
    rw [hPX]
    exact hZd i

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LamAE
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittLam
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
open scoped TensorProduct

theorem norm_id {S : Type} [CommRing S] (B p q a b D Θ : S) (h : Θ ^ 2 = D) :
    (B - (p - q * Θ) * (a + b * Θ)) * (B - (p + q * Θ) * (a - b * Θ)) =
      (B - p * a + q * b * D) ^ 2 - D * (q * a - p * b) ^ 2 := by
  linear_combination (q * b * (2 * (B - p * a) + q * b * (Θ ^ 2 + D)) - (p * b - q * a) ^ 2) * h

theorem norm_one {S : Type} [CommRing S] (p q D Θ : S) (h : Θ ^ 2 = D) :
    (p + q * Θ) * (p - q * Θ) = p ^ 2 - D * q ^ 2 := by
  linear_combination (-q ^ 2) * h

theorem core_loc {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] (ι : R →+* S) (s : S →+* S)
    (O : Subring S) (hιO : ∀ r, ι r ∈ O) (Θ : S) (hΘO : Θ ∈ O) (D Bt P Q a b : R)
    (hΘ : Θ ^ 2 = ι D) (hsΘ : s Θ = -Θ) (hsι : ∀ r, s (ι r) = ι r) (hPQ : P ^ 2 - D * Q ^ 2 = 1)
    (Bi K i4 : R) (hB : Bt * Bi = 1) (hK : Q * D * K = 1) (h4 : (4 : R) * i4 = 1) :
    ∃ lam ∈ O, lam * s lam = 1 ∧ ∃ c' ∈ O, (ι Bt - s lam * (ι a + ι b * Θ)) * c' = 1 := by
  let pp : Fin 4 → R := ![1, -1, P, -P]
  let qq : Fin 4 → R := ![0, 0, Q, -Q]
  let f : Fin 4 → R := fun i => (Bt - pp i * a + qq i * b * D) ^ 2 - D * (qq i * a - pp i * b) ^ 2
  have ef0 : f 0 = (Bt - a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring
  have ef1 : f 1 = (Bt + a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring
  have ef2 : f 2 = (Bt - P * a + Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring
  have ef3 : f 3 = (Bt + P * a - Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring
  have hspanTop : Ideal.span (Set.range f) = ⊤ := by
    have mem : ∀ i, f i ∈ Ideal.span (Set.range f) := fun i => Ideal.subset_span ⟨i, rfl⟩
    have ha : a ∈ Ideal.span (Set.range f) := by
      have : a = i4 * Bi * (f 1 - f 0) := by
        rw [ef1, ef0]; linear_combination (-a) * h4 + (-4 * i4 * a) * hB
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (mem 1) (mem 0))
    have hm : P * a - Q * D * b ∈ Ideal.span (Set.range f) := by
      have : P * a - Q * D * b = i4 * Bi * (f 3 - f 2) := by
        rw [ef3, ef2]
        linear_combination (-(P * a - Q * D * b)) * h4 + (-4 * i4 * (P * a - Q * D * b)) * hB
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (mem 3) (mem 2))
    have hb : b ∈ Ideal.span (Set.range f) := by
      have : b = K * (P * a - (P * a - Q * D * b)) := by linear_combination (-b) * hK
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (Ideal.mul_mem_left _ _ ha) hm)
    have hN : a ^ 2 - D * b ^ 2 ∈ Ideal.span (Set.range f) := by
      have : a ^ 2 - D * b ^ 2 = a * a - (D * b) * b := by ring
      rw [this]; exact sub_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
    have hB2 : Bt ^ 2 ∈ Ideal.span (Set.range f) := by
      have : Bt ^ 2 = f 0 + (2 * Bt) * a - (a ^ 2 - D * b ^ 2) := by rw [ef0]; ring
      rw [this]; exact sub_mem (add_mem (mem 0) (Ideal.mul_mem_left _ _ ha)) hN
    rw [Ideal.eq_top_iff_one]
    have : (1 : R) = Bi ^ 2 * Bt ^ 2 := by linear_combination (-(Bt * Bi + 1)) * hB
    rw [this]; exact Ideal.mul_mem_left _ _ hB2
  have hnorm : ∀ i, pp i ^ 2 - D * qq i ^ 2 = 1 := by
    intro i; fin_cases i <;> simp [pp, qq] <;> linear_combination hPQ
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (f i) := by
    by_contra H
    push Not at H
    have hle : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).2 (H i)
    rw [hspanTop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 hle)
  set L : S := ι (pp i) + ι (qq i) * Θ with hL
  set M : S := ι (pp i) - ι (qq i) * Θ with hM
  have hsL : s L = M := by rw [hL, hM, map_add (f := _), map_mul, hsι, hsι, hsΘ]; ring
  have hsM : s M = L := by rw [hL, hM, map_sub, map_mul, hsι, hsι, hsΘ]; ring
  have hLM : L * M = 1 := by
    rw [hL, hM, norm_one _ _ _ _ hΘ, ← map_pow, ← map_pow, ← map_mul, ← map_sub, hnorm i, map_one]
  set c : S := ι Bt - M * (ι a + ι b * Θ) with hc
  set sc : S := ι Bt - L * (ι a - ι b * Θ) with hsc
  have hcc : c * sc = ι (f i) := by
    rw [hc, hsc, hL, hM]
    simp only [f, map_sub, map_add (f := _), map_mul, map_pow]
    exact norm_id _ _ _ _ _ _ _ hΘ
  obtain ⟨u, hu⟩ := hi
  have hLO : L ∈ O := O.add_mem (hιO _) (O.mul_mem (hιO _) hΘO)
  have hMO : M ∈ O := O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)
  refine ⟨L, hLO, by rw [hsL]; exact hLM, sc * ι ((u⁻¹ : Rˣ) : R), ?_, ?_⟩
  · exact O.mul_mem (O.sub_mem (hιO _) (O.mul_mem hLO (O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)))) (hιO _)
  · rw [hsL, ← hc, ← mul_assoc, hcc, ← hu, ← map_mul, Units.mul_inv, map_one]

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Formalism.L2.SG.Pf.NcS.KfOrbPf
open scoped TensorProduct

theorem lamAE : LamAE := by
  intro F E _ _ _ _ _ σ hCM δ hδ hδ0
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabS.sigma_invol σ hCM.2.2.2
  obtain ⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by
    by_contra H
    push Not at H
    let w : InfinitePlace E := Classical.arbitrary _
    have hreal : ComplexEmbedding.IsReal w.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext z
      rw [ComplexEmbedding.conjugate_coe_eq, ← Complex.star_def, ← hCM.2.2.2, H z]
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (hCM.2.1.isComplex w)) (InfinitePlace.isReal_iff.2 hreal)
  set θ : E := x - σ x with hθdef
  have hσθ : σ θ = -θ := by rw [hθdef, map_sub, hσ]; ring
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hind : ∀ p q : F, algebraMap F E p + algebraMap F E q * θ = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h' := congrArg σ h
    rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσθ, map_zero] at h'
    have hq : (2 : E) * (algebraMap F E q * θ) = 0 := by linear_combination h - h'
    have hq0 : q = 0 := by
      rcases mul_eq_zero.1 ((mul_eq_zero.1 hq).resolve_left two_ne_zero) with h1 | h1
      · exact (algebraMap F E).injective (by rw [h1, map_zero])
      · exact absurd h1 hθ0
    subst hq0
    rw [map_zero, zero_mul, add_zero] at h
    exact ⟨(algebraMap F E).injective (by rw [h, map_zero]), rfl⟩
  let v2 : Fin 2 → E := ![1, θ]
  have hli : LinearIndependent F v2 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    have e : algebraMap F E (g 0) + algebraMap F E (g 1) * θ = 0 := by
      rw [← hg]; simp [v2, Algebra.smul_def]
    obtain ⟨h0, h1⟩ := hind _ _ e
    intro i
    fin_cases i
    · exact h0
    · exact h1
  let b2 : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hCM.2.2.1])
  have hb2 : ∀ i, b2 i = v2 i := fun i => by
    simp only [b2, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hdec : ∀ e : E, e = algebraMap F E (b2.repr e 0) + algebraMap F E (b2.repr e 1) * θ := by
    intro e
    conv_lhs => rw [← b2.sum_repr e]
    rw [Fin.sum_univ_two, hb2, hb2]
    simp [v2, Algebra.smul_def]

  have hfixF : ∀ e : E, σ e = e → e = algebraMap F E (b2.repr e 0) := by
    intro e he
    have h1 := hdec e
    have h2 := congrArg σ h1
    rw [he, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσθ] at h2
    have h3 : algebraMap F E 0 + algebraMap F E (2 * b2.repr e 1) * θ = 0 := by
      rw [map_zero, map_mul, map_ofNat]; linear_combination h2 - h1
    have hq := (hind _ _ h3).2
    have hq' : b2.repr e 1 = 0 := (mul_eq_zero.1 hq).resolve_left two_ne_zero
    rw [hq', map_zero (algebraMap F E), zero_mul, add_zero] at h1
    exact h1
  have hθ2σ : σ (θ ^ 2) = θ ^ 2 := by rw [map_pow, hσθ, neg_sq]
  set d := b2.repr (θ ^ 2) 0 with hd_def
  have hd : θ ^ 2 = algebraMap F E d := hfixF _ hθ2σ
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd
    exact hθ0 ((pow_eq_zero_iff two_ne_zero).1 hd)
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, map_one] at hd
    have h1 : (θ - 1) * (θ + 1) = 0 := by linear_combination hd
    rcases mul_eq_zero.1 h1 with h | h
    · have e : θ = 1 := sub_eq_zero.1 h
      rw [e, map_one] at hσθ
      exact two_ne_zero (by linear_combination hσθ : (2 : E) = 0)
    · have e : θ = -1 := eq_neg_of_add_eq_zero_left h
      rw [e, map_neg, map_one] at hσθ
      exact two_ne_zero (by linear_combination -hσθ : (2 : E) = 0)
  set β0 := b2.repr δ 0 with hβ0_def
  have hδF : δ = algebraMap F E β0 := hfixF δ hδ
  have hβ0 : β0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hδF
    exact hδ0 hδF
  have h1d : (1 - d) ≠ 0 := sub_ne_zero.2 (Ne.symm hd1)
  set Pc : F := (1 + d) / (1 - d) with hPc
  set Qc : F := 2 / (1 - d) with hQc_def
  have hQc : Qc ≠ 0 := div_ne_zero two_ne_zero h1d
  have hpq : Pc ^ 2 - d * Qc ^ 2 = 1 := by
    rw [hPc, hQc_def]
    field_simp
    ring
  filter_upwards [ev_int (F := F) d, ev_int (F := F) β0, ev_int (F := F) β0⁻¹, ev_int (F := F) Pc,
    ev_int (F := F) Qc, ev_int (F := F) (Qc * d)⁻¹, ev_int (F := F) (4 : F)⁻¹, ev_oev (F := F) θ, ev_crd_oev b2]
    with v hdv hβv hβiv hPv hQv hKv h4v hθv hcrd
  intro t ht
  let ι : v.adicCompletionIntegers F →+* Fv F v ⊗[F] E :=
    (algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype
  have hιF : ∀ (y : F) (hy : algebraMap F (Fv F v) y ∈ v.adicCompletionIntegers F),
      ι ⟨_, hy⟩ = algebraMap F (Fv F v ⊗[F] E) y := by
    intro y hy
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) y) = _
    rw [← IsScalarTower.algebraMap_apply]
  have hιO : ∀ r, ι r ∈ oevRing (E := E) v := by
    intro r
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) ∈ OEv (E := E) v
    rw [Algebra.algebraMap_eq_smul_one]
    exact oev_smul' v r.2 (oev_one v)
  have hsι : ∀ r, sigR (Fv F v) σ (ι r) = ι r := by
    intro r
    show sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) = _
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hincl : ∀ y : F, inclR (F := F) (Fv F v) (algebraMap F E y) = algebraMap F (Fv F v ⊗[F] E) y :=
    fun y => (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).commutes y
  have hΘ : (inclR (F := F) (Fv F v) θ) ^ 2 = ι ⟨_, hdv⟩ := by
    rw [hιF, ← map_pow, hd, hincl]
  have hsΘ : sigR (Fv F v) σ (inclR (F := F) (Fv F v) θ) = -inclR (F := F) (Fv F v) θ := by
    simp [sigR, inclR, hσθ, TensorProduct.tmul_neg]
  have hcrd' := hcrd t ht
  have htd : t = ι ⟨_, hcrd' 0⟩ + ι ⟨_, hcrd' 1⟩ * inclR (F := F) (Fv F v) θ := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr t]
    rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb2, hb2]
    show _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 0) +
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 1) * inclR (F := F) (Fv F v) θ
    simp only [PI.VolStabS.PositiveNearLattice.crd, Algebra.smul_def, v2, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [inclR]
  have hPQ : (⟨_, hPv⟩ : v.adicCompletionIntegers F) ^ 2 - ⟨_, hdv⟩ * ⟨_, hQv⟩ ^ 2 = 1 := by
    apply Subtype.ext
    show (algebraMap F (Fv F v) Pc) ^ 2 - algebraMap F (Fv F v) d * (algebraMap F (Fv F v) Qc) ^ 2 = 1
    rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, hpq, map_one]
  have hB : (⟨_, hβv⟩ : v.adicCompletionIntegers F) * ⟨_, hβiv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) β0 * algebraMap F (Fv F v) β0⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hβ0, map_one]
  have hK : (⟨_, hQv⟩ : v.adicCompletionIntegers F) * ⟨_, hdv⟩ * ⟨_, hKv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) Qc * algebraMap F (Fv F v) d * algebraMap F (Fv F v) (Qc * d)⁻¹ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (mul_ne_zero hQc hd0), map_one]
  have h4 : (4 : v.adicCompletionIntegers F) * ⟨_, h4v⟩ = 1 := by
    apply Subtype.ext
    show ((4 : v.adicCompletionIntegers F) : Fv F v) * algebraMap F (Fv F v) (4 : F)⁻¹ = 1
    have e4 : ((4 : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) 4 := by
      rw [map_ofNat]; rfl
    rw [e4, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
  obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := core_loc ι (sigR (Fv F v) σ) (oevRing (E := E) v) hιO
    (inclR (F := F) (Fv F v) θ) hθv ⟨_, hdv⟩ ⟨_, hβv⟩ ⟨_, hPv⟩ ⟨_, hQv⟩ ⟨_, hcrd' 0⟩ ⟨_, hcrd' 1⟩
    hΘ hsΘ hsι hPQ ⟨_, hβiv⟩ ⟨_, hKv⟩ ⟨_, h4v⟩ hB hK h4
  refine ⟨lam, hlamO, hlam, c', hc'O, ?_⟩
  have hδι : inclR (F := F) (Fv F v) δ = ι ⟨_, hβv⟩ := by rw [hιF, hδF, hincl]
  rw [hδι]
  conv_lhs => rw [htd]
  exact hc'

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Matrix Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittAlg
open scoped TensorProduct

section Main

theorem sigR_inclR' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hform_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (sigR R σ) (JR R J) (fun i => inclR R (x i)) (fun i => inclR R (y i)) =
      inclR R (Formalism.UG.hform (σ : E →+* E) J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, JR, Matrix.map_apply, sigR_inclR']
  rfl

theorem intWittAE_of (hA : AlgWitt) (hD : HermDiag) (hL : LamAE) : LocSBPf.IntWittAE := by
  intro F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hT hLat d b
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLL, rfl⟩ := hLat
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabS.sigma_invol σ hCM.2.2.2
  have hJh : Formalism.UG.IsHerm (σ : E →+* E) J := by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact hJ.1 i j
  obtain ⟨P, Q, hQP, hPo, hPd⟩ := hD E (σ : E →+* E) hσ two_ne_zero n J hJh a X0 hT
  set Z0 : Fin a → Fin n → E := fun i => ∑ l, P i l • X0 l with hZ0
  have hZ0e : ∀ i, Z0 i = ∑ l, P i l • X0 l := fun i => rfl
  have hX0e : ∀ c, X0 c = ∑ l, Q c l • Z0 l := fun c => by
    funext k
    simp only [hZ0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ l, Q c l * (P l m * X0 m k) = (if c = m then 1 else 0) * X0 m k := by
      intro m
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      rw [← Matrix.mul_apply, hQP, Matrix.one_apply]
    simp_rw [hm]
    simp
  let δ : Fin a → E := fun i => Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 i)
  have hδσ : ∀ i, σ (δ i) = δ i := fun i => hform_conj (σ : E →+* E) J hσ hJh _ _
  have hJi : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.2 hJ.2)
  filter_upwards [ev_latLoc_std L hLL,
    eventually_all.2 fun k => ev_oev (F := F) (b k),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J i j),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J⁻¹ i j),
    eventually_all.2 fun i => ev_oev (F := F) (δ i),
    eventually_all.2 fun i => ev_oev (F := F) (δ i)⁻¹,
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (P i j),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (Z0 i j),
    eventually_all.2 fun i => hL F E σ hCM (δ i) (hδσ i) (hPd i)]
    with v hstd hbv hJv hJiv hδv hδiv hPv hZv hlam
  intro X hX hgram
  let O := oevRing (E := E) v
  have hXO : ∀ c k, X c k ∈ O := by
    intro c k
    show X c k ∈ OEv (E := E) v
    rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr (X c k)]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    exact oev_smul' v (hX c k l) (hbv l)
  let s := sigR (Fv F v) σ
  have hs : ∀ z, s (s z) = z := PI.VolStabS.sigR_invol (Fv F v) σ hσ
  have hsO : ∀ z ∈ O, s z ∈ O := by
    intro z hz
    exact oev_sigR v σ hz
  let Jv := JR (F := F) (Fv F v) J
  let Jv' := JR (F := F) (Fv F v) J⁻¹
  have hJJ : Jv' * Jv = 1 := by
    show J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1
    rw [← Matrix.map_mul, hJi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJvh : Formalism.UG.IsHerm s Jv := by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Jv, JR, s, sigR_inclR']
    rw [hJ.1 i j]
  let y : Fin a → Fin n → Fv F v ⊗[F] E := fun i k => inclR (F := F) (Fv F v) (Z0 i k)
  let x : Fin a → Fin n → Fv F v ⊗[F] E := fun i => ∑ l, inclR (F := F) (Fv F v) (P i l) • X l
  have hxO : ∀ i k, x i k ∈ O := by
    intro i k
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact O.sum_mem fun l _ => O.mul_mem (hPv i l) (hXO l k)
  have hyy : ∀ i j, Formalism.UG.hform s Jv (y i) (y j) = if i = j then inclR (F := F) (Fv F v) (δ i) else 0 := by
    intro i j
    rw [show Formalism.UG.hform s Jv (y i) (y j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) from
      hform_inclR _ σ J _ _]
    split_ifs with h
    · subst h; rfl
    · rw [hPo i j h, map_zero]
  have hXX : ∀ l m, Formalism.UG.hform s Jv (X l) (X m) =
      inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by
    intro l m
    exact congrFun (congrFun hgram l) m
  have hxx : ∀ i j, Formalism.UG.hform s Jv (x i) (x j) = if i = j then inclR (F := F) (Fv F v) (δ i) else 0 := by
    intro i j
    have e1 : Formalism.UG.hform s Jv (x i) (x j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) := by
      calc Formalism.UG.hform s Jv (x i) (x j)
          = ∑ l, inclR (F := F) (Fv F v) (σ (P i l)) * ∑ m, inclR (F := F) (Fv F v) (P j m) *
              inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by
            simp only [x]
            rw [hform_sum_left]
            simp_rw [hform_sum_right, hXX, s, sigR_inclR']
        _ = _ := by
            rw [hZ0e i, hZ0e j, hform_sum_left]
            simp_rw [hform_sum_right]
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [map_sum, map_mul]
            rfl
    rw [e1]
    split_ifs with h
    · subst h; rfl
    · rw [hPo i j h, map_zero]
  obtain ⟨g, hg, hgO, hgiO, hgy⟩ := hA (Fv F v ⊗[F] E) s O hs hsO n Jv Jv' hJvh hJJ hJv hJiv a
    (fun i => inclR (F := F) (Fv F v) (δ i)) (fun i => inclR (F := F) (Fv F v) (δ i)⁻¹) hδv hδiv
    (fun i => by rw [← map_mul, mul_inv_cancel₀ (hPd i), map_one])
    hlam x y hxO hZv hxx hyy
  refine ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), ?_, ?_⟩
  · show ∀ w, w ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
      (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w ∈ latLoc (E := E) v (L : Set (Fin n → E))
    rw [hstd]
    intro w
    constructor
    · intro hw
      exact mem_std_of_oev v _ fun i => mulVec_mem O _ hgO w (fun k => mem_oev_of_std v w hw k) i
    · intro hw
      have e : w = ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w) := by
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      rw [e]
      exact mem_std_of_oev v _ fun i => mulVec_mem O _ hgiO _ (fun k => mem_oev_of_std v _ hw k) i
  · funext c
    show (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ ratTup (F := F) (Fv F v) X0 c = X c
    have e1 : ratTup (F := F) (Fv F v) X0 c = ∑ l, inclR (F := F) (Fv F v) (Q c l) • y l := by
      funext k
      simp only [ratTup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, y]
      rw [hX0e c]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Finset.sum_apply, map_sum, map_mul]
    rw [e1, mulVec_sum]
    simp_rw [mulVec_smul, hgy]
    funext k
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ l, inclR (F := F) (Fv F v) (Q c l) * (inclR (F := F) (Fv F v) (P l m) * X m k) =
        (if c = m then 1 else 0) * X m k := by
      intro m
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [← mul_assoc, ← Finset.sum_mul, ← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, hQP, Matrix.one_apply]
      split_ifs <;> simp
    simp_rw [hm]
    simp

end Main

theorem integral_witt_almost_everywhere : Formalism.L2.SG.Pf.NcS.LocSBPf.IntWittAE :=
  intWittAE_of IntWittAlg.algWitt IntWittAlg.hermDiag lamAE

end Formalism.L2.SG.Pf.NcS.IntWittPf
