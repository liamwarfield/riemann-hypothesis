module

public import ReciprocityTheory.DualLattices.FischerSelfNeZero

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.SumLatInvMulVec
section -- merged from ReciprocityTheory.DualLattices.ExistsUnitMinor
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem freePts_integral {n h : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (F : Lat v (Fin n × Fin h)) (hF : F.B = freeMat a h) {w : Fin n × Fin h → C} (hw : w ∈ F.pts)
    (y : Fin n × Fin h) : v (w y) ≤ 1 := by
  obtain ⟨c, hc, rfl⟩ := hw
  rw [hF]
  simp only [Matrix.mulVec, dotProduct]
  refine v.map_sum_le fun x _ => ?_
  rw [map_mul]
  refine mul_le_one₀ ?_ (zero_le) (hc x)
  simp only [freeMat, Matrix.of_apply]
  split_ifs
  · rw [map_pow]
    exact pow_le_one₀ (zero_le) (ha _)
  · simp

def fder {n : ℕ} (a : Fin n → C) (τ : Fin n) : C := ∏ τ' ∈ Finset.univ.erase τ, (a τ - a τ')

theorem prod_fder {n : ℕ} (a : Fin n → C) : ∏ τ, fder a τ = discr a := rfl

private lemma valuation_coeff_prod_X_sub_C_le_one {n : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (s : Finset (Fin n)) (k : ℕ) :
    v ((∏ τ' ∈ s, (Polynomial.X - Polynomial.C (a τ'))).coeff k) ≤ 1 := by
  have h : (∏ τ' ∈ s, (Polynomial.X - Polynomial.C (a τ'))) =
      (∏ τ' ∈ s, (Polynomial.X - Polynomial.C (⟨a τ', ha τ'⟩ : v.integer))).map v.integer.subtype := by
    simp [Polynomial.map_prod]
  rw [h, Polynomial.coeff_map]
  exact (Valuation.mem_integer_iff _ _).1 (Subtype.prop _)

theorem conductor_mem {n h : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (F : Lat v (Fin n × Fin h)) (hF : F.B = freeMat a h) (τ : Fin n) (u : Fin h → C)
    (hu : ∀ l, v (u l) ≤ 1) :
    (fun y : Fin n × Fin h => if y.1 = τ then fder a τ * u y.2 else 0) ∈ F.pts := by
  classical
  have hdeg : (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).natDegree < n := by
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_lt (Fin.pos τ) one_pos
  have heval : ∀ τ', (∏ τ'' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ''))).eval (a τ') =
      if τ' = τ then fder a τ else 0 := by
    intro τ'
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    split_ifs with h
    · subst h
      rfl
    · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (sub_self _)
  refine ⟨fun x => (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).coeff x.1 * u x.2,
    fun x => ?_, ?_⟩
  · rw [map_mul]
    exact mul_le_one₀ (valuation_coeff_prod_X_sub_C_le_one ha _ _) (zero_le) (hu _)
  · rw [hF]
    funext y
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, freeMat, Matrix.of_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hsum : ∑ k : Fin n, a y.1 ^ (k : ℕ) *
        ((∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).coeff k * u y.2) =
        (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).eval (a y.1) * u y.2 := by
      rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_mul,
        ← Fin.sum_univ_eq_sum_range (fun i => _ * a y.1 ^ i * u y.2)]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum, heval]
    split_ifs <;> simp

end ReciprocityTheory.PGsh.Up
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

def phiMap {n s h : ℕ} (A : Fin n → Matrix (Fin s) (Fin h) C) (w : Fin n × Fin h → C) :
    Fin n × Fin s → C := fun y => ∑ l, A y.1 y.2 l * w (y.1, l)

lemma sumLat_inv_mulVec {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (w : Fin n × Fin s → C)
    (τ : Fin n) (i : Fin s) :
    ((sumLat Mτ).B⁻¹ *ᵥ w) (τ, i) = ((Mτ τ).B⁻¹ *ᵥ fun j => w (τ, j)) i := by
  classical
  unfold sumLat
  simp only
  have hinv : (reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (blockDiagonal fun τ ↦ (Mτ τ).B))⁻¹ =
      reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
        (blockDiagonal fun τ ↦ (Mτ τ).B⁻¹) := by
    refine Matrix.inv_eq_left_inv ?_
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
    have h1 : (fun τ ↦ (Mτ τ).B⁻¹ * (Mτ τ).B) = 1 :=
      funext fun τ ↦ Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (Mτ τ).det_ne)
    rw [h1, Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]
  rw [hinv]
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma v_mulVec_le {m k : Type} [Fintype k] (P : Matrix m k C) (x : k → C)
    (hP : ∀ i j, v (P i j) ≤ 1) (hx : ∀ j, v (x j) ≤ 1) (i : m) : v ((P *ᵥ x) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine v.map_sum_le fun j _ ↦ ?_
  rw [map_mul]
  exact mul_le_one₀ (hP i j) (zero_le) (hx j)

theorem polyVec_mem {n h : ℕ} {a : Fin n → C} (F : Lat v (Fin n × Fin h))
    (hF : F.B = freeMat a h) (p : Polynomial C) (hp : ∀ k, v (p.coeff k) ≤ 1)
    (hdeg : p.natDegree < n) (u : Fin h → C) (hu : ∀ l, v (u l) ≤ 1) :
    (fun y : Fin n × Fin h => p.eval (a y.1) * u y.2) ∈ F.pts := by
  classical
  refine ⟨fun y ↦ p.coeff (y.1 : ℕ) * u y.2, ?_, ?_⟩
  · intro j
    rw [map_mul]
    exact mul_le_one₀ (hp _) (zero_le) (hu _)
  · funext y
    rw [hF]
    simp only [Matrix.mulVec, dotProduct, freeMat, Matrix.of_apply, Fintype.sum_prod_type,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ ↦ by ring

end ReciprocityTheory.PGsh.Up
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

private theorem mulVec_single_one_apply {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι C)
    (i k : ι) : (M *ᵥ Pi.single k 1) i = M i k := by
  rw [Matrix.mulVec_single_one]
  rfl

private theorem valuation_inv_mulVec_le_one_of_mem_pts {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι) {x : ι → C}
    (hx : x ∈ L.pts) (i : ι) : v ((L.B⁻¹ *ᵥ x) i) ≤ 1 := by
  obtain ⟨c, hc, rfl⟩ := hx
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ L.isUnit_det, Matrix.one_mulVec]
  exact hc i

private theorem valuation_mul_apply_le_one {ι κ μ : Type} [Fintype κ] (X : Matrix ι κ C) (Z : Matrix κ μ C)
    (hX : ∀ i j, v (X i j) ≤ 1) (hZ : ∀ i j, v (Z i j) ≤ 1) (i : ι) (k : μ) :
    v ((X * Z) i k) ≤ 1 :=
  v_mulVec_le X (fun j => Z j k) hX (fun j => hZ j k) i

private theorem blockDiag_mul_blockDiag {n p q r : ℕ} (X : Fin n → Matrix (Fin p) (Fin q) C)
    (Z : Fin n → Matrix (Fin q) (Fin r) C) :
    (Matrix.of fun (y : Fin n × Fin p) (x : Fin n × Fin q) =>
        if y.1 = x.1 then X y.1 y.2 x.2 else 0) *
      (Matrix.of fun (y : Fin n × Fin q) (x : Fin n × Fin r) =>
        if y.1 = x.1 then Z y.1 y.2 x.2 else 0) =
    Matrix.of fun (y : Fin n × Fin p) (x : Fin n × Fin r) =>
      if y.1 = x.1 then (X y.1 * Z y.1) y.2 x.2 else 0 := by
  ext y x
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_eq_single y.1]
  · by_cases h : y.1 = x.1
    · simp [h, Matrix.mul_apply]
    · simp [h]
  · intro τ hτ
    simp [Ne.symm hτ]

private theorem blockDiag_mul_diagonal_eq_diagonal_mul {n p q : ℕ} (X : Fin n → Matrix (Fin p) (Fin q) C) (g : Fin n → C) :
    (Matrix.of fun (y : Fin n × Fin p) (x : Fin n × Fin q) =>
        if y.1 = x.1 then X y.1 y.2 x.2 else 0) *
        Matrix.diagonal (fun x : Fin n × Fin q => g x.1) =
      Matrix.diagonal (fun y : Fin n × Fin p => g y.1) *
        Matrix.of fun (y : Fin n × Fin p) (x : Fin n × Fin q) =>
          if y.1 = x.1 then X y.1 y.2 x.2 else 0 := by
  ext y x
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.of_apply]
  by_cases h : y.1 = x.1
  · rw [if_pos h, h]
    ring
  · rw [if_neg h]
    ring

private theorem prod_fder_fst_eq_discr_pow {n m : ℕ} (a : Fin n → C) :
    ∏ x : Fin n × Fin m, fder a x.1 = discr a ^ m := by
  rw [Fintype.prod_prod_type, ← prod_fder a, ← Finset.prod_pow]
  simp

theorem colength_sq_mul_le {n : ℕ} (a : Fin n → C) (hinj : Function.Injective a) (ha : ∀ τ, v (a τ) ≤ 1)
    (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
    (M' S : Lat v (Fin n × Fin s)) (Mτ : Fin n → Lat v (Fin s)) (hF : F.B = freeMat a h)
    (hM' : M'.pts = phiMap A '' F.pts)
    (hMτ : ∀ τ, (Mτ τ).pts = projPts M'.pts τ) (hS : S.pts = sumPts Mτ) :
    colen M' S ^ 2 * v (discr a) ^ h ≤ v (discr a) ^ (2 * s) := by
  have hf : ∀ τ, fder a τ ≠ 0 := by
    intro τ
    unfold fder
    exact Finset.prod_ne_zero_iff.mpr fun τ' hτ' =>
      sub_ne_zero.mpr fun e => Finset.ne_of_mem_erase hτ' (hinj e).symm
  have hd0 : discr a ≠ 0 := by
    rw [← prod_fder a]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => hf τ
  have hd : v (discr a) ≠ 0 := (map_ne_zero v).mpr hd0
  have hYex : ∀ (τ : Fin n) (j : Fin s), ∃ w ∈ F.pts,
      (fun i => phiMap A w (τ, i)) = (Mτ τ).B *ᵥ Pi.single j 1 := by
    intro τ j
    have hm : (Mτ τ).B *ᵥ Pi.single j 1 ∈ (Mτ τ).pts := ⟨_, isIntegralVec_single j, rfl⟩
    rw [hMτ τ] at hm
    obtain ⟨m, hm', hmj⟩ := hm
    rw [hM'] at hm'
    obtain ⟨w, hw, rfl⟩ := hm'
    exact ⟨w, hw, hmj⟩
  choose wY hwYF hwY using hYex
  have hWex : ∀ k : Fin n × Fin s, ∃ w ∈ F.pts, phiMap A w = M'.B *ᵥ Pi.single k 1 := by
    intro k
    have hm : M'.B *ᵥ Pi.single k 1 ∈ M'.pts := ⟨_, isIntegralVec_single k, rfl⟩
    rw [hM'] at hm
    obtain ⟨w, hw, e⟩ := hm
    exact ⟨w, hw, e⟩
  choose wW hwWF hwW using hWex
  have hGint : ∀ τ i l, v (((Mτ τ).B⁻¹ * A τ) i l) ≤ 1 := by
    intro τ i l
    obtain ⟨w, hwd⟩ : ∃ w : Fin n × Fin h → C,
        w = fun y => (1 : Polynomial C).eval (a y.1) * (Pi.single l (1 : C) : Fin h → C) y.2 :=
        ⟨_, rfl⟩
    have hw : w ∈ F.pts := by
      rw [hwd]
      exact polyVec_mem F hF 1 (fun k => by rw [Polynomial.coeff_one]; split_ifs <;> simp)
        (by rw [Polynomial.natDegree_one]; exact τ.pos) (Pi.single l 1)
        (fun l' => by rw [Pi.single_apply]; split_ifs <;> simp)
    have hm : (fun i => phiMap A w (τ, i)) ∈ (Mτ τ).pts := by
      rw [hMτ τ]
      exact ⟨phiMap A w, by rw [hM']; exact ⟨w, hw, rfl⟩, rfl⟩
    have key := valuation_inv_mulVec_le_one_of_mem_pts (Mτ τ) hm i
    have hp : (fun i => phiMap A w (τ, i)) = fun i => A τ i l := by
      funext i'
      rw [hwd]
      simp [phiMap, Pi.single_apply]
    rw [hp] at key
    exact key
  obtain ⟨Gτ, hGτ⟩ : ∃ Gτ : Fin n → Matrix (Fin s) (Fin h) C,
      Gτ = fun τ => (Mτ τ).B⁻¹ * A τ := ⟨_, rfl⟩
  obtain ⟨Yτ, hYτ⟩ : ∃ Yτ : Fin n → Matrix (Fin h) (Fin s) C,
      Yτ = fun τ => Matrix.of fun l j => wY τ j (τ, l) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin n × Fin s) (Fin n × Fin h) C,
      G = Matrix.of fun y x => if y.1 = x.1 then Gτ y.1 y.2 x.2 else 0 := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : Matrix (Fin n × Fin h) (Fin n × Fin s) C,
      Y = Matrix.of fun y x => if y.1 = x.1 then Yτ y.1 y.2 x.2 else 0 := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Matrix (Fin n × Fin s) (Fin n × Fin h) C,
      Φ = Matrix.of fun y x => if y.1 = x.1 then A y.1 y.2 x.2 else 0 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Matrix (Fin n × Fin h) (Fin n × Fin s) C,
      W = Matrix.of fun x k => wW k x := ⟨_, rfl⟩
  obtain ⟨Dh, hDh⟩ : ∃ D : Matrix (Fin n × Fin h) (Fin n × Fin h) C,
      D = Matrix.diagonal fun x => fder a x.1 := ⟨_, rfl⟩
  obtain ⟨Ds, hDs⟩ : ∃ D : Matrix (Fin n × Fin s) (Fin n × Fin s) C,
      D = Matrix.diagonal fun y => fder a y.1 := ⟨_, rfl⟩
  obtain ⟨Eh, hEh⟩ : ∃ E : Matrix (Fin n × Fin h) (Fin n × Fin h) C,
      E = Matrix.diagonal fun x => (fder a x.1)⁻¹ * (1 - fder a x.1) := ⟨_, rfl⟩
  obtain ⟨Es, hEs⟩ : ∃ E : Matrix (Fin n × Fin s) (Fin n × Fin s) C,
      E = Matrix.diagonal fun y => (fder a y.1)⁻¹ * (1 - fder a y.1) := ⟨_, rfl⟩
  have hAY : ∀ τ, A τ * (Matrix.of fun (l : Fin h) (j : Fin s) => wY τ j (τ, l)) = (Mτ τ).B := by
    intro τ
    ext i j
    have e := congrFun (hwY τ j) i
    rw [mulVec_single_one_apply] at e
    rw [← e, Matrix.mul_apply]
    simp only [Matrix.of_apply, phiMap]
  have hGYτ : ∀ τ, Gτ τ * Yτ τ = 1 := by
    intro τ
    rw [hGτ, hYτ]
    show (Mτ τ).B⁻¹ * A τ * (Matrix.of fun (l : Fin h) (j : Fin s) => wY τ j (τ, l)) = 1
    rw [Matrix.mul_assoc, hAY τ, Matrix.nonsing_inv_mul _ (Mτ τ).isUnit_det]
  have hGint' : ∀ y x, v (G y x) ≤ 1 := by
    intro y x
    rw [hG]
    simp only [Matrix.of_apply]
    split_ifs
    · rw [hGτ]
      exact hGint y.1 y.2 x.2
    · simp
  have hYint : ∀ x y, v (Y x y) ≤ 1 := by
    intro x y
    rw [hYd]
    simp only [Matrix.of_apply]
    split_ifs
    · rw [hYτ]
      exact freePts_integral ha F hF (hwYF x.1 y.2) (x.1, x.2)
    · simp
  have hGYbig : G * Y = 1 := by
    rw [hG, hYd, blockDiag_mul_blockDiag Gτ Yτ]
    simp only [hGYτ]
    ext ⟨τ, i⟩ ⟨τ', j⟩
    by_cases hτ : τ = τ'
    · subst hτ
      simp [Matrix.one_apply]
    · simp [hτ, Matrix.one_apply]
  have hΦW : Φ * W = M'.B := by
    ext y k
    have e := congrFun (hwW k) y
    rw [mulVec_single_one_apply] at e
    rw [← e, hΦ, hW, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_eq_single y.1]
    · simp [phiMap]
    · intro τ hτ
      simp [Ne.symm hτ]
  have hSG : (sumLat Mτ).B⁻¹ * Φ = G := by
    ext ⟨τ, i⟩ x
    have e := sumLat_inv_mulVec Mτ (fun z => Φ z x) τ i
    refine e.trans ?_
    rw [hΦ, hG, hGτ]
    simp only [Matrix.of_apply]
    by_cases hτ : τ = x.1
    · have hv : (fun j : Fin s => if τ = x.1 then A τ j x.2 else 0) = fun j => A τ j x.2 := by
        funext j
        rw [if_pos hτ]
      rw [hv, if_pos hτ]
      rfl
    · have hv : (fun j : Fin s => if τ = x.1 then A τ j x.2 else 0) = 0 := by
        funext j
        rw [if_neg hτ]
        rfl
      rw [hv, if_neg hτ, Matrix.mulVec_zero]
      rfl
  have hSS : S.pts = (sumLat Mτ).pts := by rw [hS, sumLat_pts]
  have hcol : colen M' S = v (G * W).det := by
    rw [colen_congr (rfl : M'.pts = M'.pts) hSS, colen_eq_v_det, ← hΦW, ← Matrix.mul_assoc, hSG]
  have hGDcomm : G * Dh = Ds * G := by
    rw [hG, hDh, hDs]
    exact blockDiag_mul_diagonal_eq_diagonal_mul Gτ (fder a)
  have hGEcomm : G * Eh = Es * G := by
    rw [hG, hEh, hEs]
    exact blockDiag_mul_diagonal_eq_diagonal_mul Gτ (fun τ => (fder a τ)⁻¹ * (1 - fder a τ))
  have hGD0 : G * (Dh * (1 - Y * G)) = 0 := by
    rw [← Matrix.mul_assoc, hGDcomm, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc G Y G, hGYbig, Matrix.one_mul, sub_self, Matrix.mul_zero]
  have hfac : (W * G + (1 - Y * G)) * (Y * G + Dh * (1 - Y * G)) = W * G + Dh * (1 - Y * G) := by
    have p1 : W * G * (Y * G) = W * G := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc G Y G, hGYbig, Matrix.one_mul]
    have p2 : W * G * (Dh * (1 - Y * G)) = 0 := by
      rw [Matrix.mul_assoc, hGD0, Matrix.mul_zero]
    have p3 : (1 - Y * G) * (Y * G) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc G Y G, hGYbig,
        Matrix.one_mul, sub_self]
    have p4 : (1 - Y * G) * (Dh * (1 - Y * G)) = Dh * (1 - Y * G) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc Y G, hGD0, Matrix.mul_zero, sub_zero]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, p1, p2, p3, p4, add_zero, zero_add]
  have hdetA1 : (W * G + (1 - Y * G)).det = (G * W).det := by
    have e : W * G + (1 - Y * G) = 1 + (W - Y) * G := by
      rw [Matrix.sub_mul]
      abel
    rw [e, Matrix.det_one_add_mul_comm, Matrix.mul_sub, hGYbig]
    congr 1
    abel
  have hDE : Dh * Eh = 1 - Dh := by
    rw [hDh, hEh, Matrix.diagonal_mul_diagonal]
    ext x x'
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs
    · rw [← mul_assoc, mul_inv_cancel₀ (hf _), one_mul]
    · simp
  have h1Es : (1 : Matrix (Fin n × Fin s) (Fin n × Fin s) C) + Es =
      Matrix.diagonal fun y => (fder a y.1)⁻¹ := by
    rw [hEs]
    ext y y'
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs
    · rw [mul_sub, mul_one, inv_mul_cancel₀ (hf _)]
      ring
    · simp
  have hA2eq : Y * G + Dh * (1 - Y * G) = Dh * (1 + Eh * Y * G) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hDE, Matrix.mul_sub,
      Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc Dh Y G]
    abel
  have hdetA2 : (Y * G + Dh * (1 - Y * G)).det = discr a ^ h * (discr a ^ s)⁻¹ := by
    rw [hA2eq, Matrix.det_mul, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc G Eh Y, hGEcomm,
      Matrix.mul_assoc Es G Y, hGYbig, Matrix.mul_one, h1Es, Matrix.det_diagonal, hDh,
      Matrix.det_diagonal, prod_fder_fst_eq_discr_pow, Finset.prod_inv_distrib, prod_fder_fst_eq_discr_pow]
  have hFW : ∀ i k, v ((F.B⁻¹ * W) i k) ≤ 1 := by
    intro i k
    rw [hW]
    exact valuation_inv_mulVec_le_one_of_mem_pts F (hwWF k) i
  have hFD : ∀ i x, v ((F.B⁻¹ * Dh) i x) ≤ 1 := by
    intro i x
    have hc := conductor_mem ha F hF x.1 (Pi.single x.2 1) (fun l => by
      rw [Pi.single_apply]
      split_ifs <;> simp)
    have key := valuation_inv_mulVec_le_one_of_mem_pts F hc i
    have hcv : (fun y : Fin n × Fin h => if y.1 = x.1 then fder a x.1 * (Pi.single x.2 (1 : C) : Fin h → C) y.2 else 0)
        = fder a x.1 • (Pi.single x (1 : C) : Fin n × Fin h → C) := by
      funext y
      rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.single_apply]
      by_cases h1 : y.1 = x.1
      · by_cases h2 : y.2 = x.2
        · have hyx : y = x := Prod.ext h1 h2
          simp [hyx]
        · have hyx : y ≠ x := fun e => h2 (by rw [e])
          simp [h1, h2, hyx]
      · have hyx : y ≠ x := fun e => h1 (by rw [e])
        simp [h1, hyx]
    rw [hcv, Matrix.mulVec_smul, Pi.smul_apply, mulVec_single_one_apply, smul_eq_mul] at key
    rw [hDh, Matrix.mul_diagonal, mul_comm]
    exact key
  have hQint : ∀ y x, v (((1 : Matrix (Fin n × Fin h) (Fin n × Fin h) C) - Y * G) y x) ≤ 1 := by
    intro y x
    rw [Matrix.sub_apply]
    refine le_trans (Valuation.map_sub v _ _) (max_le ?_ (valuation_mul_apply_le_one _ _ hYint hGint' y x))
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hUint : IsIntegralMat v (F.B⁻¹ * (W * G + Dh * (1 - Y * G))) := by
    intro i x
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.add_apply]
    refine le_trans (Valuation.map_add v _ _) (max_le ?_ ?_)
    · exact valuation_mul_apply_le_one _ _ hFW hGint' i x
    · exact valuation_mul_apply_le_one _ _ hFD hQint i x
  have hU : v (W * G + Dh * (1 - Y * G)).det ≤ v F.B.det := by
    have e : W * G + Dh * (1 - Y * G) = F.B * (F.B⁻¹ * (W * G + Dh * (1 - Y * G))) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ F.isUnit_det, Matrix.one_mul]
    rw [e, Matrix.det_mul, map_mul]
    calc v F.B.det * v (F.B⁻¹ * (W * G + Dh * (1 - Y * G))).det ≤ v F.B.det * 1 :=
          mul_le_mul' le_rfl (IsIntegralMat.det_le_one hUint)
      _ = v F.B.det := mul_one _
  have hvF : v F.B.det ^ 2 = v (discr a) ^ h := by
    rw [hF]
    exact v_det_freeMat_sq a h
  have hdetT : (W * G + Dh * (1 - Y * G)).det = (G * W).det * (discr a ^ h * (discr a ^ s)⁻¹) := by
    rw [← hfac, Matrix.det_mul, hdetA1, hdetA2]
  have h1 : v (G * W).det * (v (discr a) ^ h * (v (discr a) ^ s)⁻¹) ≤ v F.B.det := by
    have hU' := hU
    rwa [hdetT, map_mul, map_mul, map_inv₀, map_pow, map_pow] at hU'
  have h2 : v (G * W).det * v (discr a) ^ h ≤ v F.B.det * v (discr a) ^ s := by
    have h3 := mul_le_mul' h1 (le_refl (v (discr a) ^ s))
    rwa [mul_assoc, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd), mul_one] at h3
  rw [hcol]
  have hpos : 0 < v (discr a) ^ h := pow_pos (pos_iff_ne_zero.mpr hd) h
  refine le_of_mul_le_mul_right ?_ hpos
  calc v (G * W).det ^ 2 * v (discr a) ^ h * v (discr a) ^ h
        = (v (G * W).det * v (discr a) ^ h) * (v (G * W).det * v (discr a) ^ h) := by ring
    _ ≤ (v F.B.det * v (discr a) ^ s) * (v F.B.det * v (discr a) ^ s) := mul_le_mul' h2 h2
    _ = v F.B.det ^ 2 * v (discr a) ^ (2 * s) := by ring
    _ = v (discr a) ^ (2 * s) * v (discr a) ^ h := by rw [hvF, mul_comm]

end ReciprocityTheory.PGsh.Up
