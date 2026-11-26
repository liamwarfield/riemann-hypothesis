module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.PositiveShells.ContinuousColElVal
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Shell

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blkAt_val {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) :
    (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j =
      fromBlocks (g : Matrix (Fin n) (Fin n) k) 0 0 (1 : Matrix (Fin (N - n)) (Fin (N - n)) k)
        (finSumFinEquiv.symm (Fin.cast (Nat.add_sub_cancel' h).symm i))
        (finSumFinEquiv.symm (Fin.cast (Nat.add_sub_cancel' h).symm j)) := by
  rfl

theorem cast_eq_castAdd {n N : ℕ} (h : n ≤ N) (i : Fin N) (hi : (i : ℕ) < n) :
    Fin.cast (Nat.add_sub_cancel' h).symm i = Fin.castAdd (N - n) (⟨i, hi⟩ : Fin n) := Fin.ext rfl

theorem cast_eq_natAdd {n N : ℕ} (h : n ≤ N) (i : Fin N) (hi : n ≤ (i : ℕ)) :
    Fin.cast (Nat.add_sub_cancel' h).symm i = Fin.natAdd n (⟨i - n, by omega⟩ : Fin (N - n)) := by
  ext; simp; omega

theorem blkAt_val_lt {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) (hi : (i : ℕ) < n) (hj : (j : ℕ) < n) :
    (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j = (g : Matrix (Fin n) (Fin n) k) ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [blkAt_val, cast_eq_castAdd h i hi, cast_eq_castAdd h j hj, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁]

theorem blkAt_val_left {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) (hi : n ≤ (i : ℕ)) :
    (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [blkAt_val, cast_eq_natAdd h i hi, finSumFinEquiv_symm_apply_natAdd]
  by_cases hj : (j : ℕ) < n
  · rw [cast_eq_castAdd h j hj, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₂₁,
      one_apply_ne (fun e => by rw [e] at hi; omega)]
    rfl
  · rw [cast_eq_natAdd h j (by omega), finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂]
    simp only [Matrix.one_apply, Fin.ext_iff]
    congr 1
    apply propext; omega

theorem blkAt_val_right {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) (hj : n ≤ (j : ℕ)) :
    (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  by_cases hi : n ≤ (i : ℕ)
  · exact blkAt_val_left h g i j hi
  rw [blkAt_val, cast_eq_castAdd h i (by omega), finSumFinEquiv_symm_apply_castAdd,
    cast_eq_natAdd h j hj, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂,
    one_apply_ne (fun e => by rw [e] at hi; omega)]
  rfl

theorem unip_val (n : ℕ) (x : Fin n → k) (i j : Fin (n + 1)) :
    ((unip k n (Multiplicative.ofAdd x) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j + if hij : (j : ℕ) = n ∧ (i : ℕ) < n then x ⟨i, hij.2⟩ else 0 := by
  show (1 + colMat k n x) i j = _
  rw [Matrix.add_apply]
  congr 1
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last => simp [colMat]
    | cast i => simp [colMat]
  · have : ¬ ((j : ℕ) = n) := fun e => hj (Fin.ext (by simp [e]))
    simp [colMat, hj, this]

theorem colEl_val {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (i j : Fin N) :
    (colEl k m N h x : Matrix (Fin N) (Fin N) k) i j =
      (1 : Matrix (Fin N) (Fin N) k) i j + if hij : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m then x ⟨i, by omega⟩ else 0 := by
  show (blkAt k (m + 2) N h (unip k (m + 1) (Multiplicative.ofAdd x)) : Matrix (Fin N) (Fin N) k) i j = _
  by_cases hi : (i : ℕ) < m + 2
  · by_cases hj : (j : ℕ) < m + 2
    · rw [blkAt_val_lt h _ i j hi hj, unip_val]
      congr 1
      · simp [Matrix.one_apply, Fin.ext_iff]
      · by_cases c : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m
        · rw [dif_pos ⟨c.1, by simp only [Fin.val_mk]; omega⟩, dif_pos c]
        · rw [dif_neg (by simp only [Fin.val_mk]; omega), dif_neg c]
    · rw [blkAt_val_right h _ i j (by omega), dif_neg (by omega), add_zero]
  · rw [blkAt_val_left h _ i j (by omega), dif_neg (by omega), add_zero]

theorem colEl_add {m N : ℕ} (h : m + 2 ≤ N) (x y : Fin (m + 1) → k) :
    colEl k m N h (x + y) = colEl k m N h x * colEl k m N h y := by
  simp only [colEl, ofAdd_add, map_mul]

theorem colEl_zero {m N : ℕ} (h : m + 2 ≤ N) : colEl k m N h 0 = 1 := by
  simp only [colEl, ofAdd_zero, map_one]

theorem colEl_mul_neg {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    colEl k m N h x * colEl k m N h (-x) = 1 := by
  rw [← colEl_add, add_neg_cancel, colEl_zero]

theorem colEl_inv {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    (colEl k m N h x)⁻¹ = colEl k m N h (-x) :=
  (eq_inv_of_mul_eq_one_right (colEl_mul_neg h x)).symm

theorem continuous_colEl_val {m N : ℕ} (h : m + 2 ≤ N) :
    Continuous fun x => (colEl k m N h x : Matrix (Fin N) (Fin N) k) := by
  refine continuous_matrix fun i j => ?_
  simp only [colEl_val]
  by_cases c : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m
  · simp only [dif_pos c]
    exact continuous_const.add (continuous_apply _)
  · simp only [dif_neg c]
    exact continuous_const

theorem continuous_colEl {m N : ℕ} (h : m + 2 ≤ N) : Continuous (colEl k m N h) := by
  refine Units.continuous_iff.2 ⟨continuous_colEl_val h, ?_⟩
  simp only [colEl_inv]
  exact (continuous_colEl_val h).comp continuous_neg

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_colFix_iff {N n : ℕ} (g : GL (Fin N) k) :
    g ∈ colFix k N n ↔ ∀ r i : Fin N, (i : ℕ) < n →
      (g : Matrix (Fin N) (Fin N) k) r i = (1 : Matrix (Fin N) (Fin N) k) r i := by
  have e : ∀ i : Fin N, (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) =
      fun r => (g : Matrix (Fin N) (Fin N) k) r i := by
    intro i; funext r; simp [mulVec, dotProduct, Pi.single_apply]
  have e1 : ∀ i : Fin N, (Pi.single i (1 : k) : Fin N → k) = fun r => (1 : Matrix (Fin N) (Fin N) k) r i := by
    intro i; funext r; simp [Pi.single_apply, Matrix.one_apply]
  constructor
  · intro hg r i hi
    have hg' : ∀ i : Fin N, (i : ℕ) < n →
        (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = Pi.single i 1 := hg
    exact congrFun ((e i).symm.trans ((hg' i hi).trans (e1 i))) r
  · intro hg i hi
    show (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = Pi.single i 1
    rw [e i, e1 i]; funext r; exact hg r i hi

theorem colEl_mem_unipB {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : colEl k m N h x ∈ unipB k (Fin N) := by
  rw [mem_unipB]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := Fin.lt_def.1 hij
    rw [colEl_val, one_apply_ne (fun e => by rw [e] at this; omega), dif_neg (by omega), add_zero]
  · rw [colEl_val, one_apply_eq, dif_neg (by omega), add_zero]

theorem colEl_mem_derUnip {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : colEl k m N h x ∈ derUnip k N (m + 1) :=
  Subgroup.mem_inf.2 ⟨colEl_mem_unipB h x, (mem_colFix_iff _).2 fun r i hi => by
    rw [colEl_val, dif_neg (by omega), add_zero]⟩

theorem derChar_colEl (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    derChar k ψ N (m + 1) ⟨colEl k m N h x, colEl_mem_derUnip h x⟩ = 1 := by
  show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ),
    (colEl k m N h x : GL (Fin N) k).val p.1 p.2)) = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  rw [colEl_val, one_apply_ne (fun e => by rw [e] at h1; omega), dif_neg (by omega), add_zero]

theorem scalAt_val {n N : ℕ} (hn : n ≤ N) (z : kˣ) :
    (scalAt k n N hn z : Matrix (Fin N) (Fin N) k) = diagonal fun i : Fin N => if (i : ℕ) < n then (z : k) else 1 := by
  ext i j
  unfold scalAt
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n
    · rw [blkAt_val_lt hn _ i j hi hj]
      simp [Matrix.algebraMap_matrix_apply, diagonal_apply, hi, Fin.ext_iff]
    · rw [blkAt_val_right hn _ i j (by omega)]
      rw [one_apply_ne (fun e => by rw [e] at hi; omega), diagonal_apply_ne _ (fun e => by rw [e] at hi; omega)]
  · rw [blkAt_val_left hn _ i j (by omega)]
    by_cases e : i = j
    · subst e; simp [hi]
    · rw [one_apply_ne e, diagonal_apply_ne _ e]

theorem scalAt_mul_colEl {m N : ℕ} (h : m + 2 ≤ N) (z : kˣ) (x : Fin (m + 1) → k) :
    scalAt k (m + 1) N (by omega) z * colEl k m N h x = colEl k m N h ((z : k) • x) * scalAt k (m + 1) N (by omega) z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  rw [scalAt_val, diagonal_mul, mul_diagonal, colEl_val, colEl_val]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases c : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m
  · rw [dif_pos c, dif_pos c, one_apply_ne (fun e => by rw [e] at c; omega), if_pos (by omega), if_neg (by omega)]
    ring
  · rw [dif_neg c, dif_neg c]
    by_cases e : i = j
    · subst e; simp
    · simp [one_apply_ne e]

theorem unip_mem_Mir (n : ℕ) (x : Fin n → k) : unip k n (Multiplicative.ofAdd x) ∈ Mir k n :=
  MirU_le_Mir k n ⟨_, rfl⟩

theorem det_unip (n : ℕ) (x : Fin n → k) : Matrix.GeneralLinearGroup.det (unip k n (Multiplicative.ofAdd x)) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [unip_val, one_apply_eq, dif_neg (by omega), add_zero]
  · intro i j hij
    have := Fin.lt_def.1 hij
    rw [unip_val, one_apply_ne (fun e => by rw [e] at this; simp at this), dif_neg (by simp at this; omega), add_zero]

theorem nabs_one' : nabs k 1 = 1 := by simp [nabs]

theorem nabs_pow' (z : kˣ) (n : ℕ) : nabs k (z ^ n) = nabs k z ^ n := by simp [nabs, map_pow]

theorem B_colEl {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : MirEq π (m + 1) h s B)
    (x : Fin (m + 1) → k) (v w : V) : B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w := by
  have := hB _ (unip_mem_Mir (m + 1) x) v w
  rw [det_unip, nabs_one', Real.one_rpow, Complex.ofReal_one, one_mul] at this
  exact this

theorem scalAt_mem_Mir (m : ℕ) (z : kˣ) : scalAt k (m + 1) (m + 1 + 1) (by omega) z ∈ Mir k (m + 1) := by
  show vecMul (eLast k (m + 1)) _ = _
  rw [vecMul_eLast, scalAt_val]
  funext j
  by_cases hj : j = Fin.last (m + 1)
  · subst hj; simp [eLast]
  · rw [diagonal_apply_ne _ (Ne.symm hj)]
    simp [eLast, Pi.single_apply, hj]

theorem blkAt_scalAt {m N : ℕ} (h : m + 2 ≤ N) (z : kˣ) :
    blkAt k (m + 1 + 1) N h (scalAt k (m + 1) (m + 1 + 1) (by omega) z) = scalAt k (m + 1) N (by omega) z := by
  apply Units.ext
  ext i j
  rw [scalAt_val]
  by_cases hi : (i : ℕ) < m + 2
  · by_cases hj : (j : ℕ) < m + 2
    · rw [blkAt_val_lt h _ i j hi hj, scalAt_val]
      by_cases e : i = j
      · subst e; simp
      · rw [diagonal_apply_ne _ e, diagonal_apply_ne _ (fun e' => e (Fin.ext (by simpa using congrArg Fin.val e')))]
    · rw [blkAt_val_right h _ i j (by omega)]
      by_cases e : i = j
      · subst e; simp; omega
      · rw [one_apply_ne e, diagonal_apply_ne _ e]
  · rw [blkAt_val_left h _ i j (by omega)]
    by_cases e : i = j
    · subst e; simp; omega
    · rw [one_apply_ne e, diagonal_apply_ne _ e]

theorem det_scalAt (m : ℕ) (z : kˣ) :
    Matrix.GeneralLinearGroup.det (scalAt k (m + 1) (m + 1 + 1) (by omega) z) = z ^ (m + 1) := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalAt_val, det_diagonal, Fin.prod_univ_castSucc]
  simp
  rw [Finset.prod_congr rfl (fun x _ => if_pos (Nat.lt_succ_iff.1 x.isLt))]
  simp

theorem B_scalAt {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : MirEq π (m + 1) h s B)
    (z : kˣ) (v w : V) :
    B (π (scalAt k (m + 1) N (by omega) z) v) (π (scalAt k (m + 1) N (by omega) z) w) =
      ((nabs k z ^ (((m : ℝ) + 1) * s) : ℝ) : ℂ) * B v w := by
  have := hB _ (scalAt_mem_Mir m z) v w
  rw [blkAt_scalAt h z, det_scalAt, nabs_pow', ← Real.rpow_natCast_mul (show 0 ≤ nabs k z from NNReal.coe_nonneg _)] at this
  rw [this]
  push_cast
  ring_nf

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem row_one_mul {N : ℕ} (A M : Matrix (Fin N) (Fin N) k) (i j : Fin N)
    (hA : ∀ l, A i l = (1 : Matrix (Fin N) (Fin N) k) i l) : (A * M) i j = M i j := by
  rw [Matrix.mul_apply]
  simp_rw [hA]
  rw [← Matrix.mul_apply, Matrix.one_mul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem col_mul_one {N : ℕ} (A M : Matrix (Fin N) (Fin N) k) (i j : Fin N)
    (hA : ∀ l, A l j = (1 : Matrix (Fin N) (Fin N) k) l j) : (M * A) i j = M i j := by
  rw [Matrix.mul_apply]
  simp_rw [hA]
  rw [← Matrix.mul_apply, Matrix.mul_one]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem colFix_mulVec {N n : ℕ} {g : GL (Fin N) k} (hg : g ∈ colFix k N n) (y : Fin N → k)
    (hy : ∀ r : Fin N, n ≤ (r : ℕ) → y r = 0) : (g : Matrix (Fin N) (Fin N) k).mulVec y = y := by
  have hg' := (mem_colFix_iff g).1 hg
  conv_rhs => rw [← one_mulVec y]
  funext r
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : (l : ℕ) < n
  · rw [hg' r l hl]
  · rw [hy l (by omega), mul_zero, mul_zero]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mulVec_single_apply {N : ℕ} (M : Matrix (Fin N) (Fin N) k) (i r : Fin N) :
    M.mulVec (Pi.single i 1) r = M r i := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem colEl_mul_apply {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (M : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    ((colEl k m N h x : Matrix (Fin N) (Fin N) k) * M) i j =
      M i j + if hi : (i : ℕ) ≤ m then x ⟨i, by omega⟩ * M ⟨m + 1, by omega⟩ j else 0 := by
  rw [Matrix.mul_apply]
  simp_rw [colEl_val, add_mul, Finset.sum_add_distrib]
  have e1 : ∑ l, (1 : Matrix (Fin N) (Fin N) k) i l * M l j = M i j := by rw [← Matrix.mul_apply, Matrix.one_mul]
  rw [e1]
  congr 1
  by_cases hi : (i : ℕ) ≤ m
  · rw [dif_pos hi, Finset.sum_eq_single ⟨m + 1, by omega⟩]
    · rw [dif_pos ⟨rfl, hi⟩]
    · intro l _ hl
      rw [dif_neg (fun c => hl (Fin.ext c.1)), zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [dif_neg hi]
    exact Finset.sum_eq_zero fun l _ => by rw [dif_neg (fun c => hi c.2), zero_mul]

theorem conj_colEl (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (u : derUnip k N (m + 2)) :
    ∃ hu : colEl k m N h x * (u : GL (Fin N) k) * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2),
      lvlChar k ψ N (m + 2) ⟨_, hu⟩ = lvlChar k ψ N (m + 2) u := by
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 u.2
  have hrow : ∀ M : Matrix (Fin N) (Fin N) k, ∀ i j : Fin N, m + 1 ≤ (i : ℕ) →
      ((colEl k m N h x : Matrix (Fin N) (Fin N) k) * M) i j = M i j := by
    intro M i j hi
    exact row_one_mul _ _ _ _ fun l => by rw [colEl_val, dif_neg (by omega), add_zero]
  have hcol : ∀ M : Matrix (Fin N) (Fin N) k, ∀ i j : Fin N, m + 2 ≤ (j : ℕ) →
      (M * (((colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) i j = M i j := by
    intro M i j hj
    exact col_mul_one _ _ _ _ fun l => by rw [colEl_inv, colEl_val, dif_neg (by omega), add_zero]
  have hmem : colEl k m N h x * (u : GL (Fin N) k) * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (colEl_mem_unipB h x) hu1)
      (Subgroup.inv_mem _ (colEl_mem_unipB h x)), ?_⟩
    show ∀ i : Fin N, (i : ℕ) < m + 2 → _
    intro i hi
    have hy : ∀ r : Fin N, m + 2 ≤ (r : ℕ) →
        (((colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) r = 0 := by
      intro r hr
      rw [mulVec_single_apply, colEl_inv, colEl_val, one_apply_ne (fun e => by rw [e] at hr; omega),
        dif_neg (by omega), add_zero]
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, colFix_mulVec hu2 _ hy, mulVec_mulVec,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  refine ⟨hmem, ?_⟩
  show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 2 - 1 ≤ (p.1 : ℕ),
      (colEl k m N h x * (u : GL (Fin N) k) * (colEl k m N h x)⁻¹ : GL (Fin N) k).val p.1 p.2)) =
    Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 2 - 1 ≤ (p.1 : ℕ),
      (u : GL (Fin N) k).val p.1 p.2))
  congr 2
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  rw [Units.val_mul, Units.val_mul, hcol _ _ _ (by omega), hrow _ _ _ (by omega)]

theorem colEl_twKer (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (x : Fin (m + 1) → k) {v : V}
    (hv : v ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))) :
    π (colEl k m N h x) v ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := by
  have key : twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) ≤
      (twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))).comap (π (colEl k m N h x)) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, y, rfl⟩
    obtain ⟨hm, hχ⟩ := conj_colEl ψ h x u
    refine Submodule.subset_span ⟨⟨_, hm⟩, π (colEl k m N h x) y, ?_⟩
    rw [hχ, map_sub, map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  exact key hv

theorem derKer_le (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    DerKer k ψ π m ≤ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) ⊔
      Submodule.span ℂ {w | ∃ (x : Fin (m + 1) → k) (v : V), w = π (colEl k m N h x) v - v} := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 u.2
  obtain ⟨hl, hd⟩ := (mem_unipB k).1 hu1
  have hf := (mem_colFix_iff _).1 hu2
  set U : GL (Fin N) k := (u : GL (Fin N) k) with hU
  let j1 : Fin N := ⟨m + 1, by omega⟩
  let a : Fin (m + 1) → k := fun r => (U : Matrix (Fin N) (Fin N) k) ⟨r, by omega⟩ j1
  set u' : GL (Fin N) k := colEl k m N h (-a) * U with hu'
  have hmem : u' ∈ derUnip k N (m + 2) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (colEl_mem_unipB h (-a)) hu1, (mem_colFix_iff _).2 fun r i hi => ?_⟩
    rw [hu', Units.val_mul, colEl_mul_apply]
    by_cases hi' : (i : ℕ) < m + 1
    · rw [hf r i hi', hf j1 i hi', one_apply_ne (show j1 ≠ i from fun e => by rw [← e] at hi'; simp [j1] at hi')]
      simp
    · have hi1 : i = j1 := Fin.ext (by simp [j1]; omega)
      subst hi1
      by_cases hr : (r : ℕ) ≤ m
      · rw [dif_pos hr, hd, mul_one, one_apply_ne (fun e => by rw [e] at hr; simp [j1] at hr)]
        simp [a]
      · rw [dif_neg hr, add_zero]
        by_cases e : r = j1
        · rw [e, hd, one_apply_eq]
        · rw [one_apply_ne e]
          exact hl r j1 (Fin.lt_def.2 (by have := Fin.val_ne_of_ne e; simp [j1] at this ⊢; omega))
  have hχ : derChar k ψ N (m + 1) u = lvlChar k ψ N (m + 2) ⟨u', hmem⟩ := by
    show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ), U.val p.1 p.2)) =
      Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ), u'.val p.1 p.2))
    congr 2
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    rw [hu', Units.val_mul, colEl_mul_apply, dif_neg (by omega), add_zero]
  have hUu : U = colEl k m N h a * u' := by
    rw [hu', ← mul_assoc, colEl_mul_neg, one_mul]
  have h1 : π u' v - ((lvlChar k ψ N (m + 2) ⟨u', hmem⟩ : ℂˣ) : ℂ) • v ∈
      twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := Submodule.subset_span ⟨⟨u', hmem⟩, v, rfl⟩
  have h2 := colEl_twKer ψ h π a h1
  have h3 : π (colEl k m N h a) v - v ∈
      Submodule.span ℂ {w | ∃ (x : Fin (m + 1) → k) (v : V), w = π (colEl k m N h x) v - v} :=
    Submodule.subset_span ⟨a, v, rfl⟩
  have e : π U v - ((derChar k ψ N (m + 1) u : ℂˣ) : ℂ) • v =
      π (colEl k m N h a) (π u' v - ((lvlChar k ψ N (m + 2) ⟨u', hmem⟩ : ℂˣ) : ℂ) • v) +
        ((lvlChar k ψ N (m + 2) ⟨u', hmem⟩ : ℂˣ) : ℂ) • (π (colEl k m N h a) v - v) := by
    rw [hχ]
    conv_lhs => rw [hUu, map_mul, Module.End.mul_apply]
    rw [map_sub, map_smul, smul_sub]
    abel
  rw [e]
  exact Submodule.add_mem_sup h2 (Submodule.smul_mem _ _ h3)

theorem sub_colEl_mem (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (x : Fin (m + 1) → k) (v : V) :
    v - π (colEl k m N h x) v ∈ DerKer k ψ π m := by
  have hm : π (colEl k m N h x) v - ((derChar k ψ N (m + 1) ⟨colEl k m N h x, colEl_mem_derUnip h x⟩ : ℂˣ) : ℂ) • v ∈
      DerKer k ψ π m := Submodule.subset_span ⟨⟨_, colEl_mem_derUnip h x⟩, v, rfl⟩
  rw [derChar_colEl, Units.val_one, one_smul] at hm
  rw [← neg_sub]
  exact neg_mem hm

end PositivityTheory.RgUd.Form.U.Shell
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

set_option linter.unusedSectionVars false

namespace PositivityTheory.RgUd.Form.U.Shell

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Avg

variable {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)

def IsTr (A H : AddSubgroup (Fin (m + 1) → k)) (T : Finset (Fin (m + 1) → k)) : Prop :=
  H ≤ A ∧ IsOpen (H : Set (Fin (m + 1) → k)) ∧ (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H

def FixH (H : AddSubgroup (Fin (m + 1) → k)) (v : V) : Prop := ∀ a ∈ H, π (colEl k m N h a) v = v

def avgL (T : Finset (Fin (m + 1) → k)) : V →ₗ[ℂ] V := ((T.card : ℂ)⁻¹) • ∑ t ∈ T, π (colEl k m N h t)

theorem avgL_apply (T : Finset (Fin (m + 1) → k)) (v : V) :
    avgL h π T v = ((T.card : ℂ)⁻¹) • ∑ t ∈ T, π (colEl k m N h t) v := by
  rw [avgL, LinearMap.smul_apply, LinearMap.sum_apply]

theorem pi_colEl_add (x y : Fin (m + 1) → k) (v : V) :
    π (colEl k m N h (x + y)) v = π (colEl k m N h x) (π (colEl k m N h y) v) := by
  rw [colEl_add, map_mul, Module.End.mul_apply]

def stab (v : V) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {a | π (colEl k m N h a) v = v}
  zero_mem' := by
    show π (colEl k m N h 0) v = v
    rw [colEl_zero, map_one, Module.End.one_apply]
  add_mem' := by
    intro a b ha hb
    show π (colEl k m N h (a + b)) v = v
    rw [pi_colEl_add, hb, ha]
  neg_mem' := by
    intro a ha
    show π (colEl k m N h (-a)) v = v
    conv_lhs => rw [← (show π (colEl k m N h a) v = v from ha)]
    rw [← pi_colEl_add, neg_add_cancel, colEl_zero, map_one, Module.End.one_apply]

theorem isOpen_stab (hπ : IsSmooth π) (v : V) : IsOpen (stab h π v : Set (Fin (m + 1) → k)) :=
  (hπ v).preimage (continuous_colEl h)

variable {h π}

theorem IsTr.card_ne {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) :
    (T.card : ℂ) ≠ 0 := by
  obtain ⟨t, ⟨ht, -⟩, -⟩ := hT.2.2.2 0 A.zero_mem
  exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem ht)

private theorem sum_transversal_add_eq_sum_of_periodic {G M : Type*} [AddCommGroup G] [AddCommMonoid M] (A H : AddSubgroup G)
    (T : Finset G) (hTA : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) (f : G → M)
    (hf : ∀ x y, y ∈ H → f (x + y) = f x) (a : G) (ha : a ∈ A) :
    ∑ t ∈ T, f (t + a) = ∑ t ∈ T, f t := by
  classical
  have key : ∀ x ∈ A, ∃ t, t ∈ T ∧ x - t ∈ H := fun x hx => (hu x hx).exists
  choose! r hrT hrH using key
  have hfr : ∀ x ∈ A, f x = f (r x) := by
    intro x hx
    have := hf (r x) (x - r x) (hrH x hx)
    rw [add_sub_cancel] at this
    exact this
  have huniq : ∀ x ∈ A, ∀ t ∈ T, x - t ∈ H → r x = t := by
    intro x hx t ht hxt
    exact (hu x hx).unique ⟨hrT x hx, hrH x hx⟩ ⟨ht, hxt⟩
  refine Finset.sum_nbij' (fun t => r (t + a)) (fun t => r (t - a)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact hrT _ (A.add_mem (hTA t ht) ha)
  · intro t ht
    exact hrT _ (A.sub_mem (hTA t ht) ha)
  · intro t ht
    have hx : t + a ∈ A := A.add_mem (hTA t ht) ha
    apply huniq _ (A.sub_mem (hTA _ (hrT _ hx)) ha) t ht
    have := H.neg_mem (hrH _ hx)
    convert this using 1
    abel
  · intro t ht
    have hx : t - a ∈ A := A.sub_mem (hTA t ht) ha
    apply huniq _ (A.add_mem (hTA _ (hrT _ hx)) ha) t ht
    have := H.neg_mem (hrH _ hx)
    convert this using 1
    abel
  · intro t ht
    exact hfr _ (A.add_mem (hTA t ht) ha)

theorem sum_translate {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {v : V}
    (hv : FixH h π H v) {a : Fin (m + 1) → k} (ha : a ∈ A) :
    ∑ t ∈ T, π (colEl k m N h (t + a)) v = ∑ t ∈ T, π (colEl k m N h t) v := by
  apply sum_transversal_add_eq_sum_of_periodic A H T hT.2.2.1 hT.2.2.2 (fun x => π (colEl k m N h x) v) _ a ha
  intro x y hy
  beta_reduce
  rw [pi_colEl_add, hv y hy]

theorem avgL_colEl {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {v : V}
    (hv : FixH h π H v) {a : Fin (m + 1) → k} (ha : a ∈ A) : avgL h π T (π (colEl k m N h a) v) = avgL h π T v := by
  rw [avgL_apply, avgL_apply]
  congr 1
  rw [← sum_translate hT hv ha]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pi_colEl_add]

theorem colEl_avgL {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {v : V}
    (hv : FixH h π H v) {a : Fin (m + 1) → k} (ha : a ∈ A) : π (colEl k m N h a) (avgL h π T v) = avgL h π T v := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avgL_apply, map_smul, map_sum]
  congr 1
  rw [← sum_translate hT hv ha]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [add_comm, pi_colEl_add]

theorem avgL_of_inv {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {y : V}
    (hy : ∀ a ∈ A, π (colEl k m N h a) y = y) : avgL h π T y = y := by
  rw [avgL_apply, Finset.sum_congr rfl fun t ht => hy t (hT.2.2.1 t ht), Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hT.card_ne, one_smul]

theorem avgL_eq {A H H' : AddSubgroup (Fin (m + 1) → k)} {T T' : Finset (Fin (m + 1) → k)} {v : V} (hT : IsTr A H T)
    (hv : FixH h π H v) (hT' : IsTr A H' T') (hv' : FixH h π H' v) : avgL h π T v = avgL h π T' v := by
  have h1 : avgL h π T (avgL h π T' v) = avgL h π T' v :=
    avgL_of_inv hT fun a ha => colEl_avgL hT' hv' ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h1, avgL_apply h π T' v, map_smul, map_sum,
    Finset.sum_congr rfl fun t ht => avgL_colEl hT hv (hT'.2.2.1 t ht), Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hT'.card_ne, one_smul]

theorem avg_eq {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {v : V}
    (hv : FixH h π H v) : avg (1 : AddChar k Circle) h π 0 A v = avgL h π T v := by
  have hd : ∃ p, AvgData (1 : AddChar k Circle) h π 0 A v p :=
    ⟨(H, T), hT.1, hT.2.1, hv, fun a _ => by simp, hT.2.2.1, hT.2.2.2⟩
  rw [avg, dite_eq_left hd]
  obtain ⟨p1, p2, p3, -, p5, p6⟩ := hd.choose_spec
  have e := avgL_eq (h := h) (π := π) (v := v) ⟨p1, p2, p5, p6⟩ p3 hT hv
  rw [← e, avgL_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  simp

theorem avgL_sub_mem (ψ : AddChar k Circle) {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)}
    (hT : IsTr A H T) (v : V) : v - avgL h π T v ∈ DerKer k ψ π m := by
  have hc := hT.card_ne
  have e : v - avgL h π T v = ((T.card : ℂ)⁻¹) • ∑ t ∈ T, (v - π (colEl k m N h t) v) := by
    rw [avgL_apply, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => sub_colEl_mem ψ h π t v)

theorem IsTr.neg [DecidableEq (Fin (m + 1) → k)] {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) :
    IsTr A H (T.image Neg.neg) := by
  refine ⟨hT.1, hT.2.1, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact A.neg_mem (hT.2.2.1 s hs)
  · intro a ha
    obtain ⟨s, ⟨hs, hsH⟩, huniq⟩ := hT.2.2.2 (-a) (A.neg_mem ha)
    refine ⟨-s, ⟨Finset.mem_image_of_mem _ hs, ?_⟩, ?_⟩
    · have := H.neg_mem hsH
      convert this using 1
      abel
    · rintro t ⟨ht, htH⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht
      have hH' : -a - s' ∈ H := by
        have := H.neg_mem htH
        convert this using 1
        abel
      rw [huniq s' ⟨hs', hH'⟩]

theorem B_avgL {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : MirEq π (m + 1) h s B) {A H : AddSubgroup (Fin (m + 1) → k)}
    {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {v w : V} (hw : FixH h π H w) :
    B (avgL h π T v) w = B v (avgL h π T w) := by
  classical
  have hTn := hT.neg
  have hcard : (T.image Neg.neg).card = T.card := Finset.card_image_of_injective _ neg_injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← avgL_eq hTn hw hT hw, avgL_apply, avgL_apply, Finset.sum_image (fun x _ y _ hxy => neg_injective hxy),
    hcard, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_sum, map_sum,
    LinearMap.sum_apply]
  simp only [map_inv₀, map_natCast, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have ew : w = π (colEl k m N h t) (π (colEl k m N h (-t)) w) := by
    rw [← pi_colEl_add, add_neg_cancel, colEl_zero, map_one, Module.End.one_apply]
  conv_lhs => rw [ew]
  rw [B_colEl h hB]

private theorem exists_tr_lemma {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (A H : AddSubgroup G) (hA : IsCompact (A : Set G)) (hH : IsOpen (H : Set G)) :
    ∃ T : Finset G, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  classical
  obtain ⟨S, hS⟩ := hA.elim_finite_subcover (fun a : A => (fun x => x - (a : G)) ⁻¹' (H : Set G))
    (fun a => hH.preimage (continuous_id.sub continuous_const))
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simp [H.zero_mem]⟩)
  set S' : Finset G := S.image (fun a : A => (a : G)) with hS'
  have hS'A : ∀ s ∈ S', s ∈ A := by
    intro s hs
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hs
    exact a.2
  have hcov : ∀ x ∈ A, ∃ s ∈ S', x - s ∈ H := by
    intro x hx
    have := hS hx
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
    obtain ⟨a, ha, hxa⟩ := this
    exact ⟨a, Finset.mem_image_of_mem _ ha, hxa⟩
  let r : G → G := fun x => Classical.epsilon fun s => s ∈ S' ∧ x - s ∈ H
  have hr : ∀ x ∈ A, r x ∈ S' ∧ x - r x ∈ H := fun x hx => by
    obtain ⟨s, hs, hxs⟩ := hcov x hx
    exact Classical.epsilon_spec (p := fun s => s ∈ S' ∧ x - s ∈ H) ⟨s, hs, hxs⟩
  have hreq : ∀ x y, x - y ∈ H → r x = r y := by
    intro x y hxy
    show Classical.epsilon _ = Classical.epsilon _
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := H.sub_mem h2 hxy
      convert this using 1
      abel
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := H.add_mem hxy h2
      convert this using 1
      abel
  refine ⟨S'.image r, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact hS'A _ (hr s (hS'A s hs)).1
  · intro a ha
    obtain ⟨s, hs, has⟩ := hcov a ha
    refine ⟨r a, ⟨?_, (hr a ha).2⟩, ?_⟩
    · rw [hreq a s has]
      exact Finset.mem_image_of_mem _ hs
    · rintro t ⟨ht, hat⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht
      have h1 := (hr s' (hS'A s' hs')).2
      apply hreq
      have := H.sub_mem h1 hat
      convert this using 1
      abel

theorem exists_tr {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) {H₀ : AddSubgroup (Fin (m + 1) → k)}
    (hH₀ : IsOpen (H₀ : Set (Fin (m + 1) → k))) : ∃ H T, IsTr A H T ∧ H ≤ H₀ := by
  have hHo : IsOpen ((H₀ ⊓ A : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) := by
    rw [AddSubgroup.coe_inf]
    exact hH₀.inter hA.2
  obtain ⟨T, hTA, hu⟩ := exists_tr_lemma A (H₀ ⊓ A) hA.1 hHo
  exact ⟨H₀ ⊓ A, T, ⟨inf_le_right, hHo, hTA, hu⟩, inf_le_left⟩

def scl (z : kˣ) (A : AddSubgroup (Fin (m + 1) → k)) : AddSubgroup (Fin (m + 1) → k) :=
  A.map (DistribMulAction.toAddEquiv (Fin (m + 1) → k) z).toAddMonoidHom

theorem mem_scl (z : kˣ) (A : AddSubgroup (Fin (m + 1) → k)) (x : Fin (m + 1) → k) :
    x ∈ scl z A ↔ (z⁻¹ : kˣ) • x ∈ A :=
  AddSubgroup.mem_map_equiv

theorem IsTr.smul [DecidableEq (Fin (m + 1) → k)] {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)}
    (hT : IsTr A H T) (z : kˣ) : IsTr (scl z A) (scl z H) (T.image fun t => z • t) := by
  have hc : Continuous fun x : Fin (m + 1) → k => (z⁻¹ : kˣ) • x := by
    simp only [Units.smul_def]
    exact continuous_const_smul _
  refine ⟨fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [mem_scl] at hx ⊢
    exact hT.1 hx
  · have e : (scl z H : Set (Fin (m + 1) → k)) =
        (fun x => (z⁻¹ : kˣ) • x) ⁻¹' (H : Set (Fin (m + 1) → k)) := by
      ext x
      exact mem_scl z H x
    rw [e]
    exact hT.2.1.preimage hc
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    rw [mem_scl, inv_smul_smul]
    exact hT.2.2.1 s hs
  · intro a ha
    rw [mem_scl] at ha
    obtain ⟨s, ⟨hs, hsH⟩, huniq⟩ := hT.2.2.2 _ ha
    refine ⟨z • s, ⟨Finset.mem_image_of_mem _ hs, ?_⟩, ?_⟩
    · rw [mem_scl, smul_sub, inv_smul_smul]
      exact hsH
    · rintro t ⟨ht, htH⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht
      rw [mem_scl, smul_sub, inv_smul_smul] at htH
      rw [huniq s' ⟨hs', htH⟩]

end Avg

section Ball

def ball (m : ℕ) (u : kˣ) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ valuation k (u : k)}
  add_mem' := fun {a b} ha hb i => by
    show valuation k (a i + b i) ≤ _
    exact ((valuation k).map_add _ _).trans (max_le (ha i) (hb i))
  zero_mem' := fun i => by simp
  neg_mem' := fun {a} ha i => by
    show valuation k (-(a i)) ≤ _
    rw [Valuation.map_neg]
    exact ha i

theorem coe_ball (m : ℕ) (u : kˣ) : (ball m u : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => cball u := by
  ext x
  exact ⟨fun hx i _ => hx i, fun hx i => hx i (Set.mem_univ i)⟩

theorem isLat_ball (m : ℕ) (u : kˣ) : IsLat (ball m u) := by
  refine ⟨?_, ?_⟩ <;> rw [coe_ball]
  · exact isCompact_univ_pi fun _ => isCompact_cball u
  · exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball u

theorem ball_mono (m : ℕ) {u u' : kˣ} (hu : valuation k (u : k) ≤ valuation k (u' : k)) : ball m u ≤ ball m u' :=
  fun _ hx i => (hx i).trans hu

theorem scl_ball (m : ℕ) (z u : kˣ) : scl z (ball m u) = ball m (z * u) := by
  ext x
  rw [mem_scl]
  have hz : 0 < valuation k (z : k) := by simp [zero_lt_iff]
  refine forall_congr' fun i => ?_
  show valuation k (((z⁻¹ : kˣ) • x) i) ≤ valuation k (u : k) ↔ valuation k (x i) ≤ valuation k ((z * u : kˣ) : k)
  rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    inv_mul_le_iff₀ hz]

theorem ball_pow_mono (m : ℕ) (z : kˣ) (hz : valuation k (z : k) < 1) (u₀ : kˣ) {t t' : ℕ} (htt' : t ≤ t') :
    ball m (z⁻¹ ^ t * u₀) ≤ ball m (z⁻¹ ^ t' * u₀) := by
  apply ball_mono
  have hz0 : valuation k (z : k) ≠ 0 := (Valuation.ne_zero_iff _).mpr z.ne_zero
  have h1 : 1 ≤ (valuation k (z : k))⁻¹ := by
    calc 1 = valuation k (z : k) * (valuation k (z : k))⁻¹ := (mul_inv_cancel₀ hz0).symm
      _ ≤ 1 * (valuation k (z : k))⁻¹ := mul_le_mul_of_nonneg_right hz.le zero_le'
      _ = (valuation k (z : k))⁻¹ := one_mul _
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 htt') zero_le'

theorem exists_mem_ball (m : ℕ) (z : kˣ) (hz : valuation k (z : k) < 1) (u₀ : kˣ) (x : Fin (m + 1) → k) :
    ∃ t : ℕ, x ∈ ball m (z⁻¹ ^ t * u₀) := by
  have hz0 : valuation k (z : k) ≠ 0 := (Valuation.ne_zero_iff _).mpr z.ne_zero
  have hu0 : 0 < valuation k (u₀ : k) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr u₀.ne_zero)
  have h1 : 1 < (valuation k (z : k))⁻¹ := (one_lt_inv₀ (zero_lt_iff.mpr hz0)).mpr hz
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  have hi : ∀ i, ∃ t : ℕ, valuation k (x i) ≤ (valuation k (z : k))⁻¹ ^ t * valuation k (u₀ : k) := by
    intro i
    obtain ⟨t, ht⟩ := MulArchimedean.arch (valuation k (x i) * (valuation k (u₀ : k))⁻¹) h1
    exact ⟨t, (mul_inv_le_iff₀ hu0).mp ht⟩
  choose t ht using hi
  refine ⟨Finset.univ.sup t, fun i => ?_⟩
  show valuation k (x i) ≤ valuation k ((z⁻¹ ^ Finset.univ.sup t * u₀ : kˣ) : k)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
  exact (ht i).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ h1.le (Finset.le_sup (Finset.mem_univ i))) zero_le')

theorem tendsto_ball (m : ℕ) (z : kˣ) (hz : valuation k (z : k) < 1) (u₀ : kˣ) :
    Filter.Tendsto (fun t : ℕ => (⟨ball m (z⁻¹ ^ t * u₀), isLat_ball m _⟩ : {A : AddSubgroup (Fin (m + 1) → k) // IsLat A}))
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  rintro ⟨A, hA⟩
  obtain ⟨T0, hT0⟩ := hA.1.elim_directed_cover
    (fun t : ℕ => (ball m (z⁻¹ ^ t * u₀) : Set (Fin (m + 1) → k)))
    (fun t => (isLat_ball m _).2)
    (fun x _ => Set.mem_iUnion.mpr (exists_mem_ball m z hz u₀ x))
    (Monotone.directed_le fun t t' htt' x hx => ball_pow_mono m z hz u₀ htt' hx)
  rw [Filter.eventually_atTop]
  exact ⟨T0, fun t ht x hx => ball_pow_mono m z hz u₀ ht (hT0 hx)⟩

end Ball

section Scal

variable {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem FixH.smul {H : AddSubgroup (Fin (m + 1) → k)} {v : V} (hv : FixH h π H v) (z : kˣ) :
    FixH h π (scl z H) (π (scalAt k (m + 1) N (by omega) z) v) := by
  intro a ha
  rw [mem_scl] at ha
  have e : colEl k m N h a * scalAt k (m + 1) N (by omega) z =
      scalAt k (m + 1) N (by omega) z * colEl k m N h ((z⁻¹ : kˣ) • a) := by
    rw [scalAt_mul_colEl, Units.smul_def, smul_smul, Units.mul_inv, one_smul]
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hv _ ha]

theorem avgL_smul [DecidableEq (Fin (m + 1) → k)] (T : Finset (Fin (m + 1) → k)) (z : kˣ) (v : V) :
    avgL h π (T.image fun t => z • t) (π (scalAt k (m + 1) N (by omega) z) v) =
      π (scalAt k (m + 1) N (by omega) z) (avgL h π T v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avgL_apply, avgL_apply, Finset.card_image_of_injective _ (MulAction.injective z),
    Finset.sum_image (fun x _ y _ hxy => MulAction.injective z hxy), map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : π (colEl k m N h ((z : k) • t)) * π (scalAt k (m + 1) N (by omega) z) =
      π (scalAt k (m + 1) N (by omega) z) * π (colEl k m N h t) := by
    rw [← map_mul, ← map_mul, scalAt_mul_colEl]
  beta_reduce
  rw [Units.smul_def]
  exact LinearMap.congr_fun e v

end Scal

end PositivityTheory.RgUd.Form.U.Shell
