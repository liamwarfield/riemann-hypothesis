module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.AnisoPeelAlt

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.DensExactInertOf
open Finset

noncomputable section

namespace DensInertW

theorem Fr_zero_zero (q d : ℕ) : Fr q d 0 0 = 1 := by
  rw [Fr]

theorem Fr_succ (q d r c : ℕ) : Fr q d (r + 1) c = valN q d * Fr q (d - 1) r c := by
  rw [Fr]

theorem Fr_zero_succ (q d c : ℕ) :
    Fr q d 0 (c + 1) = (valZ q d - 1) * (q : ℤ) ^ (2 * c) * Fr q (d - 2) 0 c := by
  rw [Fr]

theorem top_cnt_fin_zero {L : Type} [Field L] {n : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L)
    (W : Submodule L (Fin n → L)) (B : Matrix (Fin 0) (Fin 0) L) : cntT q M W B = 1 := by
  unfold cntT
  have h : {X : Fin 0 → Fin n → L | (∀ i, X i ∈ W) ∧ LinearIndependent L X ∧
      ∀ i j, hf q M (X i) (X j) = B i j} = Set.univ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  rw [h, Set.ncard_univ]
  simp

theorem top_diag_count (hA : AnisoPeel) (hI : IsoPeel) (K L : Type) [Field K] [Fintype K]
    [Field L] [Fintype L] [Algebra K L] (h2 : Module.finrank K L = 2) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) L) (hM : IsHerm (Fintype.card K) M) :
    ∀ (m : ℕ) (w : Fin m → L) (r : ℕ), r ≤ m → (∀ i, w i ≠ 0 ↔ i.val < r) →
      (∀ i, w i ^ Fintype.card K = w i) →
      ∀ W : Submodule L (Fin n → L), NonDeg (Fintype.card K) M W →
        (cntT (Fintype.card K) M W (Matrix.diagonal w) : ℤ) =
          Fr (Fintype.card K) (Module.finrank L W) r (m - r) := by
  intro m
  induction m with
  | zero =>
    intro w r hr _ _ W _
    obtain rfl : r = 0 := by omega
    rw [top_cnt_fin_zero, Fr_zero_zero]
    rfl
  | succ c ih =>
    intro w r hr hw hwq W hW
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      have hw0 : w = 0 := by
        funext i
        by_contra h
        have := (hw i).mp h
        omega
      have hdiag : Matrix.diagonal w = (0 : Matrix (Fin (c + 1)) (Fin (c + 1)) L) := by
        rw [hw0]; exact Matrix.diagonal_zero
      rw [hdiag]
      have hk := hI K L h2 n M W hM hW c (Fr (Fintype.card K) (Module.finrank L W - 2) 0 c)
        (fun W' hW' hrk => by
          have h1 := ih (fun _ => 0) 0 (Nat.zero_le _) (fun i => by simp)
            (fun i => by simp [zero_pow Fintype.card_ne_zero]) W' hW'
          rw [Matrix.diagonal_zero] at h1
          rw [h1, show Module.finrank L W' = Module.finrank L W - 2 by omega, Nat.sub_zero])
      rw [hk, Nat.sub_zero, Fr_zero_succ]
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      have hw0 : w 0 ≠ 0 := (hw 0).mpr (by simp)
      have hcons : Matrix.diagonal w =
          Matrix.diagonal (Fin.cons (w 0) (Fin.tail w) : Fin (c + 1) → L) := by
        rw [Fin.cons_self_tail]
      rw [hcons]
      have hk := hA K L h2 n M W hM hW c (w 0) (Fin.tail w)
        (Fr (Fintype.card K) (Module.finrank L W - 1) r' (c - r')) (hwq 0) hw0
        (fun W' hW' hrk => by
          have h1 := ih (Fin.tail w) r' (by omega)
            (fun i => by simp only [Fin.tail]; rw [hw i.succ]; simp [Fin.val_succ])
            (fun i => hwq i.succ) W' hW'
          rw [h1, show Module.finrank L W' = Module.finrank L W - 1 by omega])
      rw [hk, show c + 1 - (r' + 1) = c - r' by omega, Fr_succ]

theorem top_nondeg_top {L : Type} [Field L] {n : ℕ} (q : ℕ) (hq : 0 < q)
    (M : Matrix (Fin n) (Fin n) L) (hdet : IsUnit M.det) : NonDeg q M ⊤ := by
  intro w _ hw
  have h0 : Matrix.vecMul w M = 0 := by
    funext l0
    have h := hw (Pi.single l0 1) Submodule.mem_top
    simp only [hf, Pi.single_apply, ite_pow, one_pow, zero_pow hq.ne', mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    simpa [Matrix.vecMul, dotProduct] using h
  calc w = Matrix.vecMul w (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul w M) M⁻¹ := by rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [h0, Matrix.zero_vecMul]

theorem top_rank (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (m : ℕ) (B P : Matrix (Fin m) (Fin m) L) (hP : IsUnit P.det) :
    (P * B * (P.map (fun y => y ^ Fintype.card K)).transpose).rank = B.rank := by
  have hF : P.map (fun y => y ^ Fintype.card K) =
      P.map ((FiniteField.frobeniusAlgHom K L : L →ₐ[K] L) : L →+* L) := by
    ext i j
    simp [FiniteField.frobeniusAlgHom_apply]
  have hu : IsUnit (P.map (fun y => y ^ Fintype.card K)).transpose.det := by
    rw [Matrix.det_transpose, hF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hP.map _
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP]

theorem densExactInert_of (hD : Diag) (hC : Congr) (hA : AnisoPeel) (hI : IsoPeel)
    (hR : Arith) : Formalism.L2.SG.DensExact.DensExactInert := by
  classical
  intro K L _ _ _ _ _ h2 n m Ph Gm hPh hPhH hGm
  obtain ⟨P, hP, w, r, hrm, hdiag, hw, hwq⟩ := hD K L h2 m Gm hGm
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hcnt : Formalism.L2.SG.DensExact.countInert K L n m Ph Gm = cntT (Fintype.card K) Ph ⊤ Gm := by
    unfold Formalism.L2.SG.DensExact.countInert cntT
    congr 1
    ext X
    simp [hf]
  have hcong := hC K L h2 n Ph ⊤ m Gm P hP
  rw [hdiag] at hcong
  have hrank : Gm.rank = r := by
    rw [← top_rank K L m Gm P hP, hdiag, Matrix.rank_diagonal,
      Fintype.card_congr (Equiv.subtypeEquivRight hw)]
    have e : {i : Fin m // i.val < r} ≃ Fin r :=
      { toFun := fun i => ⟨i.1.val, i.2⟩
        invFun := fun j => ⟨⟨j.val, by omega⟩, j.2⟩
        left_inv := fun i => rfl
        right_inv := fun j => rfl }
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hcount := top_diag_count hA hI K L h2 n Ph hPhH m w r hrm hw hwq ⊤
    (top_nondeg_top _ (by omega) Ph hPh)
  rw [finrank_top, Module.finrank_fin_fun] at hcount
  rw [hcnt, ← hcong, hrank, ← hR (Fintype.card K) n m r hq hrm, ← hcount]
  norm_cast

end DensInertW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.FinrankInfKerAddOne
open Finset Module

namespace DensInertW.Sub

variable {L : Type} [Field L]

theorem q_ne_zero_of_inv {q : ℕ} (hinv : ∀ a : L, (a ^ q) ^ q = a) : q ≠ 0 := by
  intro hq
  subst hq
  have h := hinv 0
  simp at h

def sig (q : ℕ) (hq : q ≠ 0) (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) : L →+* L where
  toFun a := a ^ q
  map_one' := one_pow q
  map_mul' a b := mul_pow a b q
  map_zero' := zero_pow hq
  map_add' := hadd

theorem sig_apply (q : ℕ) (hq : q ≠ 0) (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (a : L) :
    sig q hq hadd a = a ^ q := rfl

section
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}

theorem hf_add_left (x x' y : Fin n → L) : hf q M (x + x') y = hf q M x y + hf q M x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left (c : L) (x y : Fin n → L) : hf q M (c • x) y = c * hf q M x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hf_zero_left (y : Fin n → L) : hf q M 0 y = 0 := by
  simp [hf]

theorem hf_sub_left (x x' y : Fin n → L) : hf q M (x - x') y = hf q M x y - hf q M x' y := by
  simp only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

def hfL (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (y : Fin n → L) : (Fin n → L) →ₗ[L] L where
  toFun x := hf q M x y
  map_add' x x' := hf_add_left x x' y
  map_smul' c x := by simp only [hf_smul_left, smul_eq_mul, RingHom.id_apply]

theorem hfL_apply (y x : Fin n → L) : hfL q M y x = hf q M x y := rfl

theorem hf_add_right (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (x y y' : Fin n → L) :
    hf q M x (y + y') = hf q M x y + hf q M x y' := by
  simp only [hf, Pi.add_apply, hadd, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (x : Fin n → L) (c : L) (y : Fin n → L) :
    hf q M x (c • y) = c ^ q * hf q M x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, mul_pow]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hf_sub_right (hq : q ≠ 0) (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (x y y' : Fin n → L) : hf q M x (y - y') = hf q M x y - hf q M x y' := by
  have hs : ∀ a b : L, (a - b) ^ q = a ^ q - b ^ q := fun a b => by
    have h := hadd (a - b) b
    rw [sub_add_cancel] at h
    rw [h]
    ring
  simp only [hf, Pi.sub_apply, hs, mul_sub, Finset.sum_sub_distrib]

theorem hf_symm (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hM : ∀ k l, M l k = M k l ^ q) (x y : Fin n → L) : hf q M y x = (hf q M x y) ^ q := by
  have hq := q_ne_zero_of_inv hinv
  have e : (hf q M x y) ^ q = sig q hq hadd (hf q M x y) := rfl
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, map_pow, sig_apply, hinv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hM]
  ring

end

section geom
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}

theorem hf_eq_zero_of_diag (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (hinv : ∀ a : L, (a ^ q) ^ q = a) (hM : ∀ k l, M l k = M k l ^ q)
    (htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ q ≠ 0)
    (W : Submodule L (Fin n → L)) (h0 : ∀ v ∈ W, hf q M v v = 0) :
    ∀ x ∈ W, ∀ y ∈ W, hf q M x y = 0 := by
  intro x hx y hy
  have key : ∀ c : L, c * hf q M x y + (c * hf q M x y) ^ q = 0 := by
    intro c
    have h1 := h0 (c • x + y) (W.add_mem (W.smul_mem c hx) hy)
    rw [hf_add_left, hf_add_right hadd, hf_add_right hadd, h0 _ (W.smul_mem c hx), h0 y hy,
      hf_symm hadd hinv hM (c • x) y, hf_smul_left] at h1
    linear_combination h1
  by_contra hz
  obtain ⟨c, hc⟩ := htr _ hz
  exact hc (key c)

theorem finrank_inf_ker_add_one (W : Submodule L (Fin n → L)) (f : (Fin n → L) →ₗ[L] L)
    (u : Fin n → L) (hu : u ∈ W) (hfu : f u ≠ 0) :
    finrank L ↥(W ⊓ LinearMap.ker f) + 1 = finrank L ↥W := by
  have hsurj : LinearMap.range f = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun a => ⟨(a / f u) • u, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu]
  have hr : finrank L (LinearMap.range f) = 1 := by
    rw [hsurj, finrank_top, Module.finrank_self]
  have hk := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, Module.finrank_fin_fun] at hk
  have hsup : W ⊔ LinearMap.ker f = ⊤ := by
    refine eq_top_iff.mpr fun v _ => Submodule.mem_sup.mpr
      ⟨(f v / f u) • u, W.smul_mem _ hu, v - (f v / f u) • u, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu, sub_self]
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  rw [hsup, finrank_top, Module.finrank_fin_fun] at h
  omega

theorem finrank_perp_aniso (W : Submodule L (Fin n → L)) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) :
    finrank L ↥(W ⊓ LinearMap.ker (hfL q M e)) + 1 = finrank L ↥W :=
  finrank_inf_ker_add_one W _ e he hee

theorem sub_mem_perp (W : Submodule L (Fin n → L)) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) (w : Fin n → L) (hw : w ∈ W) :
    w - (hf q M w e / hf q M e e) • e ∈ W ⊓ LinearMap.ker (hfL q M e) := by
  refine Submodule.mem_inf.2 ⟨W.sub_mem hw (W.smul_mem _ he), ?_⟩
  rw [LinearMap.mem_ker, hfL_apply, hf_sub_left, hf_smul_left, div_mul_cancel₀ _ hee, sub_self]

theorem nondeg_perp_aniso (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (W : Submodule L (Fin n → L)) (hW : NonDeg q M W) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) : NonDeg q M (W ⊓ LinearMap.ker (hfL q M e)) := by
  intro w hw hperp
  have hw' := Submodule.mem_inf.1 hw
  have hwe : hf q M w e = 0 := LinearMap.mem_ker.1 hw'.2
  apply hW w hw'.1
  intro v hv
  have h1 := hperp _ (sub_mem_perp W e he hee v hv)
  have hsplit : v = (v - (hf q M v e / hf q M e e) • e) + (hf q M v e / hf q M e e) • e :=
    (sub_add_cancel _ _).symm
  rw [hsplit, hf_add_right hadd, h1, hf_smul_right, hwe]
  ring

end geom

end DensInertW.Sub
end
