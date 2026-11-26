module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CarrierRow

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CellBlock
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CellBase
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.CellW

open NumberField Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E]

def Intg {m n : Type*} (d : 𝓞 E) (M : Matrix m n E) : Prop :=
  ∃ M' : Matrix m n (𝓞 E), M'.map (algebraMap (𝓞 E) E) = (algebraMap (𝓞 E) E d) • M

theorem intg_mul {l m n : Type*} [Fintype m] {d d' : 𝓞 E} {M : Matrix l m E} {N : Matrix m n E}
    (hM : Intg d M) (hN : Intg d' N) : Intg (d * d') (M * N) := by
  obtain ⟨M', hM'⟩ := hM
  obtain ⟨N', hN'⟩ := hN
  refine ⟨M' * N', ?_⟩
  rw [Matrix.map_mul, hM', hN', Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_mul, mul_comm]

theorem intg_sub {m n : Type*} {d : 𝓞 E} {M N : Matrix m n E} (hM : Intg d M) (hN : Intg d N) :
    Intg d (M - N) := by
  obtain ⟨M', hM'⟩ := hM
  obtain ⟨N', hN'⟩ := hN
  refine ⟨M' - N', ?_⟩
  ext i j
  have h1 := congrFun (congrFun hM' i) j
  have h2 := congrFun (congrFun hN' i) j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub] at h1 h2 ⊢
  rw [h1, h2]; ring

theorem intg_dvd {m n : Type*} {a D : 𝓞 E} {M : Matrix m n E} (hM : Intg a M) (h : a ∣ D) : Intg D M := by
  obtain ⟨M', hM'⟩ := hM
  obtain ⟨k, rfl⟩ := h
  refine ⟨k • M', ?_⟩
  ext i j
  have := congrFun (congrFun hM' i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at this ⊢
  rw [this]; ring

theorem intg_one {n : Type*} [DecidableEq n] (d : 𝓞 E) : Intg d (1 : Matrix n n E) := by
  refine ⟨d • (1 : Matrix n n (𝓞 E)), ?_⟩
  ext i j
  by_cases h : i = j <;> simp [h]

theorem intg_zero {m n : Type*} (d : 𝓞 E) : Intg d (0 : Matrix m n E) :=
  ⟨0, by ext i j; simp⟩

theorem intg_submatrix {m n m' n' : Type*} {d : 𝓞 E} {M : Matrix m n E} (hM : Intg d M) (f : m' → m)
    (g : n' → n) : Intg d (M.submatrix f g) := by
  obtain ⟨M', hM'⟩ := hM
  refine ⟨M'.submatrix f g, ?_⟩
  ext i j
  have h1 := congrFun (congrFun hM' (f i)) (g j)
  simpa using h1

theorem intg_fromBlocks {l m n o : Type*} {d : 𝓞 E} {A : Matrix l n E} {B : Matrix l o E}
    {C : Matrix m n E} {D : Matrix m o E} (hA : Intg d A) (hB : Intg d B) (hC : Intg d C) (hD : Intg d D) :
    Intg d (Matrix.fromBlocks A B C D) := by
  obtain ⟨A', hA'⟩ := hA
  obtain ⟨B', hB'⟩ := hB
  obtain ⟨C', hC'⟩ := hC
  obtain ⟨D', hD'⟩ := hD
  refine ⟨Matrix.fromBlocks A' B' C' D', ?_⟩
  rw [Matrix.fromBlocks_map, hA', hB', hC', hD', Matrix.fromBlocks_smul]

theorem intg_adj {k : ℕ} {d : 𝓞 E} {M : Matrix (Fin k) (Fin k) E} (hM : Intg d M) :
    Intg (d ^ (k - 1)) M.adjugate := by
  obtain ⟨M', hM'⟩ := hM
  refine ⟨M'.adjugate, ?_⟩
  have h1 := RingHom.map_adjugate (algebraMap (𝓞 E) E) M'
  simp only [RingHom.mapMatrix_apply] at h1
  rw [h1, hM', Matrix.adjugate_smul, Fintype.card_fin, map_pow]

theorem intg_of_entries {m n : Type*} {Z : Matrix m n E} (h : ∀ i j, ∃ o : 𝓞 E, (o : E) = Z i j) :
    Intg 1 Z := by
  refine ⟨fun i j => Classical.choose (h i j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, map_one, one_smul]
  exact Classical.choose_spec (h i j)

theorem exists_den (x : E) :
    ∃ m : 𝓞 E, m ≠ 0 ∧ ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = algebraMap (𝓞 E) E m * x := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  refine ⟨s, nonZeroDivisors.ne_zero s.2, a, ?_⟩
  simp only at h
  rw [← h, mul_comm]

theorem alg_ne_zero {d : 𝓞 E} (hd : d ≠ 0) : algebraMap (𝓞 E) E d ≠ 0 := by
  intro h
  exact hd ((injective_iff_map_eq_zero (algebraMap (𝓞 E) E)).mp (IsFractionRing.injective (𝓞 E) E) d h)

section Uni

variable {K : Type*} [Field K] {k : ℕ}

theorem lo_bt {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A.BlockTriangular OrderDual.toDual :=
  fun i j h => (hA i j).1 (by simpa using h)

theorem lo_diag_mul {A B : Matrix (Fin k) (Fin k) K} (hA : A.BlockTriangular OrderDual.toDual)
    (hB : B.BlockTriangular OrderDual.toDual) (i : Fin k) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hB (by simpa using h), mul_zero]
    · rw [hA (by simpa using h), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem lo_mul {A B : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) (hB : IsLoUni B) : IsLoUni (A * B) := by
  have ht := (lo_bt hA).mul (lo_bt hB)
  intro i j
  refine ⟨fun h => ht (by simpa using h), fun h => ?_⟩
  subst h
  rw [lo_diag_mul (lo_bt hA) (lo_bt hB), (hA i i).2 rfl, (hB i i).2 rfl, one_mul]

theorem lo_det {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular A (lo_bt hA)]
  exact Finset.prod_eq_one fun i _ => (hA i i).2 rfl

theorem lo_mul_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A * A.adjugate = 1 := by
  rw [Matrix.mul_adjugate, lo_det hA, one_smul]

theorem lo_adj_mul {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A.adjugate * A = 1 := by
  rw [Matrix.adjugate_mul, lo_det hA, one_smul]

theorem lo_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : IsLoUni A.adjugate := by
  letI : Invertible A.det := invertibleOfNonzero (by rw [lo_det hA]; exact one_ne_zero)
  letI : Invertible A := Matrix.invertibleOfDetInvertible A
  have hinv : A⁻¹ = A.adjugate := by rw [Matrix.inv_def, lo_det hA, Ring.inverse_one, one_smul]
  have ht : A.adjugate.BlockTriangular OrderDual.toDual := by
    rw [← hinv]; exact Matrix.blockTriangular_inv_of_blockTriangular (lo_bt hA)
  intro i j
  refine ⟨fun h => ht (by simpa using h), fun h => ?_⟩
  subst h
  have h1 := congrFun (congrFun (lo_mul_adj hA) i) i
  rw [lo_diag_mul (lo_bt hA) ht, (hA i i).2 rfl, one_mul, Matrix.one_apply_eq] at h1
  exact h1

theorem up_iff_lo_transpose {U : Matrix (Fin k) (Fin k) K} : IsUpUni U ↔ IsLoUni U.transpose := by
  constructor
  · intro h i j
    exact ⟨fun hij => (h j i).1 hij, fun hij => (h j i).2 hij.symm⟩
  · intro h i j
    exact ⟨fun hij => (h j i).1 hij, fun hij => (h j i).2 hij.symm⟩

theorem up_mul {A B : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) (hB : IsUpUni B) : IsUpUni (A * B) := by
  rw [up_iff_lo_transpose] at *
  rw [Matrix.transpose_mul]; exact lo_mul hB hA

theorem up_det {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : A.det = 1 := by
  rw [← Matrix.det_transpose]; exact lo_det (up_iff_lo_transpose.mp hA)

theorem up_mul_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : A * A.adjugate = 1 := by
  rw [Matrix.mul_adjugate, up_det hA, one_smul]

theorem up_adj_mul {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : A.adjugate * A = 1 := by
  rw [Matrix.adjugate_mul, up_det hA, one_smul]

theorem up_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : IsUpUni A.adjugate := by
  rw [up_iff_lo_transpose] at *
  rw [Matrix.adjugate_transpose]; exact lo_adj hA

end Uni

theorem quotFinite (c : 𝓞 E) (hc : c ≠ 0) : Finite (𝓞 E ⧸ Ideal.span {c}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hc)

theorem fin_of_cong {α ι : Type*} [Finite ι] (X : Set α) (f : α → ι → E)
    (hf : ∀ x ∈ X, ∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = f x i) (c : 𝓞 E) (hc : c ≠ 0)
    (R : α → α → Prop)
    (hR : ∀ x ∈ X, ∀ y ∈ X,
      (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E o = f y i - f x i) → R x y) :
    ∃ Zs : Set α, Zs.Finite ∧ ∀ x ∈ X, ∃ y ∈ Zs, R x y := by
  have := quotFinite c hc
  let g : α → ι → (𝓞 E ⧸ Ideal.span {c}) := fun x i =>
    if h : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = f x i then Ideal.Quotient.mk _ (Classical.choose h) else 0
  haveI : Finite {ρ : ι → (𝓞 E ⧸ Ideal.span {c}) // ∃ x ∈ X, g x = ρ} := Subtype.finite
  refine ⟨Set.range (fun ρ : {ρ : ι → (𝓞 E ⧸ Ideal.span {c}) // ∃ x ∈ X, g x = ρ} => Classical.choose ρ.2),
    Set.finite_range _, ?_⟩
  intro x hx
  have hex : ∃ x' ∈ X, g x' = g x := ⟨x, hx, rfl⟩
  refine ⟨Classical.choose hex, ⟨⟨g x, hex⟩, rfl⟩, ?_⟩
  obtain ⟨hy, hgy⟩ := Classical.choose_spec hex
  apply hR x hx _ hy
  intro i
  have h1 := hf x hx i
  have h2 := hf _ hy i
  have hg := congrFun hgy i
  simp only [g, dif_pos h1, dif_pos h2] at hg
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hg
  obtain ⟨o, ho⟩ := hg
  refine ⟨o, ?_⟩
  rw [← map_mul, ← ho, map_sub, Classical.choose_spec h1, Classical.choose_spec h2]

end PI.TermsAtPtFiniteW.CellW
end
end

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.CellW

open NumberField Formalism.MainNotions.S Matrix

variable {E : Type} [Field E] [NumberField E]

def revJ (K : Type*) [Zero K] [One K] (s : ℕ) : Matrix (Fin s) (Fin s) K :=
  fun i j => if j = Fin.rev i then 1 else 0

section Rev

variable {K : Type*} [Field K] {s : ℕ}

theorem revJ_mul_apply (M : Matrix (Fin s) (Fin s) K) (i j : Fin s) : (revJ K s * M) i j = M (Fin.rev i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [revJ]
  · intro k _ hk; simp [revJ, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_revJ_apply (M : Matrix (Fin s) (Fin s) K) (i j : Fin s) : (M * revJ K s) i j = M i (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [revJ]
  · intro k _ hk
    have : j ≠ Fin.rev k := by
      intro h; apply hk; rw [h, Fin.rev_rev]
    simp [revJ, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem revJ_revJ : revJ K s * revJ K s = 1 := by
  ext i j
  rw [revJ_mul_apply]
  simp only [revJ, Fin.rev_rev, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem revJ_conj_up {L : Matrix (Fin s) (Fin s) K} (hL : IsLoUni L) : IsUpUni (revJ K s * L * revJ K s) := by
  intro i j
  rw [mul_revJ_apply, revJ_mul_apply]
  refine ⟨fun h => (hL _ _).1 (Fin.rev_lt_rev.mpr h), fun h => (hL _ _).2 (by rw [h])⟩

end Rev

theorem intg_revJ (x : E) (m o : 𝓞 E) (h : algebraMap (𝓞 E) E o = algebraMap (𝓞 E) E m * x) (s : ℕ) :
    Intg m (x • revJ E s) := by
  refine ⟨o • revJ (𝓞 E) s, ?_⟩
  ext i j
  by_cases hij : j = Fin.rev i <;> simp [revJ, hij, h]

section Blocks

variable {K : Type*} {s n : ℕ}

theorem blocks_eq (M : Matrix (Fin (s + n)) (Fin (s + n)) K) :
    M.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (M.submatrix (Fin.castAdd n) (Fin.castAdd n)) (M.submatrix (Fin.castAdd n) (Fin.natAdd s))
        (M.submatrix (Fin.natAdd s) (Fin.castAdd n)) (M.submatrix (Fin.natAdd s) (Fin.natAdd s)) := by
  ext (i | i) (j | j) <;> simp

variable [CommRing K]

theorem lo_11 {L : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsLoUni L) :
    IsLoUni (L.submatrix (Fin.castAdd n) (Fin.castAdd n)) := by
  intro i j
  refine ⟨fun hij => (h _ _).1 ?_, fun hij => (h _ _).2 (by rw [hij])⟩
  rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_castAdd]; exact hij

theorem lo_22 {L : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsLoUni L) :
    IsLoUni (L.submatrix (Fin.natAdd s) (Fin.natAdd s)) := by
  intro i j
  refine ⟨fun hij => (h _ _).1 ?_, fun hij => (h _ _).2 (by rw [hij])⟩
  rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_natAdd]; omega

theorem lo_12 {L : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsLoUni L) :
    L.submatrix (Fin.castAdd n) (Fin.natAdd s) = 0 := by
  ext i j
  refine (h _ _).1 ?_
  rw [Fin.lt_def]; simp only [Fin.val_castAdd, Fin.val_natAdd]; have := i.isLt; omega

theorem up_11 {U : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsUpUni U) :
    IsUpUni (U.submatrix (Fin.castAdd n) (Fin.castAdd n)) := by
  intro i j
  refine ⟨fun hij => (h _ _).1 ?_, fun hij => (h _ _).2 (by rw [hij])⟩
  rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_castAdd]; exact hij

theorem up_22 {U : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsUpUni U) :
    IsUpUni (U.submatrix (Fin.natAdd s) (Fin.natAdd s)) := by
  intro i j
  refine ⟨fun hij => (h _ _).1 ?_, fun hij => (h _ _).2 (by rw [hij])⟩
  rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_natAdd]; omega

theorem up_21 {U : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsUpUni U) :
    U.submatrix (Fin.natAdd s) (Fin.castAdd n) = 0 := by
  ext i j
  refine (h _ _).1 ?_
  rw [Fin.lt_def]; simp only [Fin.val_castAdd, Fin.val_natAdd]; have := j.isLt; omega

theorem cast_lt_cast {i j : Fin s} : Fin.castAdd n i < Fin.castAdd n j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def]; simp only [Fin.val_castAdd]

theorem nat_lt_nat {i j : Fin n} : Fin.natAdd s i < Fin.natAdd s j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def]; simp only [Fin.val_natAdd]; omega

theorem cast_ne_nat (i : Fin s) (j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd s j := by
  intro h; have h1 := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
  have := i.isLt; omega

theorem not_nat_lt_cast (i : Fin n) (j : Fin s) : ¬ Fin.natAdd s i < Fin.castAdd n j := by
  rw [Fin.lt_def]; simp only [Fin.val_castAdd, Fin.val_natAdd]; have := j.isLt; omega

theorem lo_of_blocks {A : Matrix (Fin s) (Fin s) K} {C : Matrix (Fin n) (Fin s) K}
    {D : Matrix (Fin n) (Fin n) K} (hA : IsLoUni A) (hD : IsLoUni D) :
    IsLoUni ((fromBlocks A 0 C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) := by
  intro i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁, cast_lt_cast,
        Fin.castAdd_inj]
      exact hA i j
    | right j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        fromBlocks_apply₁₂, Matrix.zero_apply]
      exact ⟨by simp, fun h => absurd h (cast_ne_nat i j)⟩
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        fromBlocks_apply₂₁]
      exact ⟨fun h => absurd h (not_nat_lt_cast i j), fun h => absurd h.symm (cast_ne_nat j i)⟩
    | right j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂, nat_lt_nat,
        Fin.natAdd_inj]
      exact hD i j

theorem up_of_blocks {A : Matrix (Fin s) (Fin s) K} {B : Matrix (Fin s) (Fin n) K}
    {D : Matrix (Fin n) (Fin n) K} (hA : IsUpUni A) (hD : IsUpUni D) :
    IsUpUni ((fromBlocks A B 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) := by
  intro i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁, cast_lt_cast,
        Fin.castAdd_inj]
      exact hA i j
    | right j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        fromBlocks_apply₁₂]
      exact ⟨fun h => absurd h (not_nat_lt_cast j i), fun h => absurd h (cast_ne_nat i j)⟩
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        fromBlocks_apply₂₁, Matrix.zero_apply]
      exact ⟨by simp, fun h => absurd h.symm (cast_ne_nat j i)⟩
    | right j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂, nat_lt_nat,
        Fin.natAdd_inj]
      exact hD i j

end Blocks

theorem lo_one {K : Type*} [Field K] {k : ℕ} : IsLoUni (1 : Matrix (Fin k) (Fin k) K) := by
  intro i j
  exact ⟨fun h => one_apply_ne (ne_of_lt h), fun h => by rw [h, one_apply_eq]⟩

def BDm {N : ℕ} (W : Matrix (Fin N) (Fin N) E) : Prop :=
  ∀ d : 𝓞 E, d ≠ 0 → ∃ D : 𝓞 E, D ≠ 0 ∧ ∀ Z : Matrix (Fin N) (Fin N) E, Intg d Z →
    (∃ L0 U0, IsLoUni L0 ∧ IsUpUni U0 ∧ Z = L0 * W * U0) →
    ∃ L1 U1, IsLoUni L1 ∧ IsUpUni U1 ∧ Z = L1 * W * U1 ∧ Intg D L1 ∧ Intg D U1

theorem submatrix_equiv_prod {K : Type*} [CommRing K] {m n : Type*} [Fintype m] [Fintype n]
    (e : m ≃ n) (A B C : Matrix n n K) :
    (A * B * C).submatrix e e = A.submatrix e e * B.submatrix e e * C.submatrix e e := by
  rw [submatrix_mul_equiv, submatrix_mul_equiv]

theorem bd_step {s n : ℕ} (t : E) (ht : t ≠ 0) (W' : Matrix (Fin n) (Fin n) E)
    (W : Matrix (Fin (s + n)) (Fin (s + n)) E)
    (hW : W.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (t • revJ E s) 0 0 W')
    (ih : BDm W') : BDm W := by
  intro d hd
  obtain ⟨mt, hmt, ot, hot⟩ := exists_den t⁻¹
  have hD1 : mt * d ≠ 0 := mul_ne_zero hmt hd
  have hδ : (mt * d) ^ (s - 1) * mt ≠ 0 := mul_ne_zero (pow_ne_zero _ hD1) hmt
  have hd' : d * ((mt * d) ^ (s - 1) * mt) * d ≠ 0 := mul_ne_zero (mul_ne_zero hd hδ) hd
  obtain ⟨D', hD', hih⟩ := ih _ hd'
  refine ⟨d * ((mt * d) ^ (s - 1) * mt) * (mt * d) * D', mul_ne_zero (mul_ne_zero (mul_ne_zero hd hδ) hD1) hD', ?_⟩
  rintro Z hZ ⟨L0, U0, hL0, hU0, hZe⟩

  set P := Z.submatrix (Fin.castAdd n) (Fin.castAdd n) with hPdef
  set Q := Z.submatrix (Fin.castAdd n) (Fin.natAdd s) with hQdef
  set R := Z.submatrix (Fin.natAdd s) (Fin.castAdd n) with hRdef
  set S := Z.submatrix (Fin.natAdd s) (Fin.natAdd s) with hSdef
  set liftZP_unit := L0.submatrix (Fin.castAdd n) (Fin.castAdd n)
  set lintegral_supP_lt_top₂ := L0.submatrix (Fin.natAdd s) (Fin.castAdd n)
  set lix_inf_of_locP_le := L0.submatrix (Fin.natAdd s) (Fin.natAdd s)
  set U11 := U0.submatrix (Fin.castAdd n) (Fin.castAdd n)
  set U12 := U0.submatrix (Fin.castAdd n) (Fin.natAdd s)
  set U22 := U0.submatrix (Fin.natAdd s) (Fin.natAdd s)
  set W1 := t • revJ E s with hW1
  set W1i := t⁻¹ • revJ E s with hW1i
  have hW1W1i : W1 * W1i = 1 := by
    rw [hW1, hW1i, smul_mul_smul_comm, mul_inv_cancel₀ ht, one_smul, revJ_revJ]
  have hW1iW1 : W1i * W1 = 1 := by
    rw [hW1, hW1i, smul_mul_smul_comm, inv_mul_cancel₀ ht, one_smul, revJ_revJ]
  have key : Z.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (liftZP_unit * W1 * U11) (liftZP_unit * W1 * U12) (lintegral_supP_lt_top₂ * W1 * U11) (lintegral_supP_lt_top₂ * W1 * U12 + lix_inf_of_locP_le * W' * U22) := by
    rw [hZe, submatrix_equiv_prod, hW, blocks_eq L0, blocks_eq U0, lo_12 hL0, up_21 hU0,
      fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc]
    rfl
  rw [blocks_eq Z, fromBlocks_inj] at key
  obtain ⟨hP0, hQ0, hR0, hS0⟩ := key
  have hP : P = liftZP_unit * W1 * U11 := hP0
  have hQ : Q = liftZP_unit * W1 * U12 := hQ0
  have hR : R = lintegral_supP_lt_top₂ * W1 * U11 := hR0
  have hS : S = lintegral_supP_lt_top₂ * W1 * U12 + lix_inf_of_locP_le * W' * U22 := hS0

  set U1 := W1i * P with hU1def
  have hU1 : IsUpUni U1 := by
    have : U1 = (revJ E s * liftZP_unit * revJ E s) * U11 := by
      rw [hU1def, hP, hW1i, hW1]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht, one_smul,
        Matrix.mul_assoc]
    rw [this]
    exact up_mul (revJ_conj_up (lo_11 hL0)) (up_11 hU0)
  have hWU1 : W1 * U1 = P := by rw [hU1def, ← Matrix.mul_assoc, hW1W1i, Matrix.one_mul]
  set Pinv := U1.adjugate * W1i with hPinvdef
  have hPinvP : Pinv * P = 1 := by
    rw [hPinvdef, ← hWU1, Matrix.mul_assoc, ← Matrix.mul_assoc W1i, hW1iW1, Matrix.one_mul, up_adj_mul hU1]
  have hPPinv : P * Pinv = 1 := mul_eq_one_comm.mp hPinvP
  have hX : (W1 * U11 * Pinv) * liftZP_unit = 1 := by
    apply mul_eq_one_comm.mp
    rw [show liftZP_unit * (W1 * U11 * Pinv) = P * Pinv by rw [hP]; simp only [Matrix.mul_assoc], hPPinv]
  have hRPQ : R * Pinv * Q = lintegral_supP_lt_top₂ * W1 * U12 := by
    rw [hR, hQ]
    calc lintegral_supP_lt_top₂ * W1 * U11 * Pinv * (liftZP_unit * W1 * U12) = lintegral_supP_lt_top₂ * ((W1 * U11 * Pinv) * liftZP_unit) * W1 * U12 := by
          simp only [Matrix.mul_assoc]
      _ = lintegral_supP_lt_top₂ * W1 * U12 := by rw [hX, Matrix.mul_one]
  have hS' : S - R * Pinv * Q = lix_inf_of_locP_le * W' * U22 := by rw [hRPQ, hS]; abel

  have hPi : Intg d P := intg_submatrix hZ _ _
  have hQi : Intg d Q := intg_submatrix hZ _ _
  have hRi : Intg d R := intg_submatrix hZ _ _
  have hSi : Intg d S := intg_submatrix hZ _ _
  have hW1ii : Intg mt W1i := intg_revJ _ _ _ hot s
  have hU1i : Intg (mt * d) U1 := intg_mul hW1ii hPi
  have hPinvi : Intg ((mt * d) ^ (s - 1) * mt) Pinv := by
    exact intg_mul (intg_adj hU1i) hW1ii
  have hRPi : Intg (d * ((mt * d) ^ (s - 1) * mt)) (R * Pinv) := intg_mul hRi hPinvi
  have hS'i : Intg (d * ((mt * d) ^ (s - 1) * mt) * d) (S - R * Pinv * Q) :=
    intg_sub (intg_dvd hSi ⟨(mt * d) ^ (s - 1) * mt * d, by ring⟩) (intg_mul hRPi hQi)
  obtain ⟨L2, U2, hL2, hU2, hS2, hL2i, hU2i⟩ :=
    hih _ hS'i ⟨lix_inf_of_locP_le, U22, lo_22 hL0, up_22 hU0, hS'⟩

  refine ⟨(fromBlocks 1 0 (R * Pinv) L2).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    (fromBlocks U1 (W1i * Q) 0 U2).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    lo_of_blocks (lo_one (K := E)) hL2, up_of_blocks hU1 hU2, ?_, ?_, ?_⟩
  · have hZZ : Z = (Z.submatrix finSumFinEquiv finSumFinEquiv).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      simp
    have hWW : W = (W.submatrix finSumFinEquiv finSumFinEquiv).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      simp
    rw [hWW, ← submatrix_equiv_prod, hW, fromBlocks_multiply, fromBlocks_multiply, hZZ, blocks_eq Z]
    congr 1
    have hc : ∀ {m : ℕ} (X : Matrix (Fin s) (Fin m) E), W1 * (W1i * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hW1W1i, Matrix.one_mul]
    have h22 := sub_eq_iff_eq_add'.mp hS2
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_assoc, hU1def,
      hc] at h22 ⊢
    rw [fromBlocks_inj]
    refine ⟨rfl, rfl, ?_, h22⟩
    rw [hPinvP, Matrix.mul_one]
  · refine intg_submatrix (intg_fromBlocks (intg_one _) (intg_zero _) (intg_dvd hRPi ?_) (intg_dvd hL2i ?_)) _ _
    · exact ⟨(mt * d) * D', by ring⟩
    · exact ⟨d * ((mt * d) ^ (s - 1) * mt) * (mt * d), by ring⟩
  · refine intg_submatrix (intg_fromBlocks (intg_dvd hU1i ?_) (intg_dvd (intg_mul hW1ii hQi) ?_) (intg_zero _)
      (intg_dvd hU2i ?_)) _ _
    · exact ⟨d * ((mt * d) ^ (s - 1) * mt) * D', by ring⟩
    · exact ⟨d * ((mt * d) ^ (s - 1) * mt) * D', by ring⟩
    · exact ⟨d * ((mt * d) ^ (s - 1) * mt) * (mt * d), by ring⟩

end PI.TermsAtPtFiniteW.CellW
end
end

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.CellW

open NumberField Formalism.MainNotions.S Matrix

variable {E : Type} [Field E] [NumberField E]

def pm (L : List (E × ℕ)) : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E :=
  fun a b => ptEntry L a.val b.val

theorem pm_cons (t : E) (s : ℕ) (bs : List (E × ℕ)) :
    (pm ((t, s) :: bs) : Matrix (Fin (s + (bs.map Prod.snd).sum)) (Fin (s + (bs.map Prod.snd).sum)) E).submatrix
      finSumFinEquiv finSumFinEquiv = fromBlocks (t • revJ E s) 0 0 (pm bs) := by
  ext (i | i) (j | j)
  · show ptEntry ((t, s) :: bs) (i : ℕ) (j : ℕ) = t * (if j = Fin.rev i then (1 : E) else 0)
    simp only [ptEntry]
    rw [if_pos ⟨i.isLt, j.isLt⟩]
    have hiff : ((i : ℕ) + (j : ℕ) + 1 = s) ↔ j = Fin.rev i := by
      rw [Fin.ext_iff, Fin.val_rev]; omega
    by_cases h : j = Fin.rev i
    · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
  · show ptEntry ((t, s) :: bs) (i : ℕ) (s + (j : ℕ)) = 0
    have := i.isLt
    simp only [ptEntry]
    rw [if_neg (by omega), if_neg (by omega)]
  · show ptEntry ((t, s) :: bs) (s + (i : ℕ)) (j : ℕ) = 0
    have := j.isLt
    simp only [ptEntry]
    rw [if_neg (by omega), if_neg (by omega)]
  · show ptEntry ((t, s) :: bs) (s + (i : ℕ)) (s + (j : ℕ)) = ptEntry bs (i : ℕ) (j : ℕ)
    simp only [ptEntry]
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]

theorem bd_all : ∀ L : List (E × ℕ), (∀ b ∈ L, b.1 ≠ 0 ∧ 1 ≤ b.2) → BDm (pm L) := by
  intro L
  induction L with
  | nil =>
    intro _ d _
    refine ⟨1, one_ne_zero, ?_⟩
    rintro Z _ ⟨L0, U0, hL0, hU0, hZ⟩
    exact ⟨L0, U0, hL0, hU0, hZ, ⟨0, by ext i; exact absurd i.isLt (by simp)⟩,
      ⟨0, by ext i; exact absurd i.isLt (by simp)⟩⟩
  | cons b bs ih =>
    rcases b with ⟨t, s⟩
    intro h
    have ht : t ≠ 0 := (h (t, s) List.mem_cons_self).1
    exact bd_step t ht (pm bs) (pm ((t, s) :: bs)) (pm_cons t s bs)
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem map_smul' {m n : Type*} (c : 𝓞 E) (X : Matrix m n (𝓞 E)) :
    (c • X).map (algebraMap (𝓞 E) E) = algebraMap (𝓞 E) E c • X.map (algebraMap (𝓞 E) E) := by
  ext i j; simp

theorem alg_inj {x y : 𝓞 E} (h : algebraMap (𝓞 E) E x = algebraMap (𝓞 E) E y) : x = y :=
  IsFractionRing.injective (𝓞 E) E h

theorem lob_of {N : ℕ} {b : 𝓞 E} {A : Matrix (Fin N) (Fin N) E} (hA : IsLoUni A)
    (Y : Matrix (Fin N) (Fin N) (𝓞 E)) (h : A - 1 = algebraMap (𝓞 E) E b • Y.map (algebraMap (𝓞 E) E)) :
    ∃ A' : Matrix (Fin N) (Fin N) (𝓞 E), LoB b A' ∧ A'.map (fun x => (x : E)) = A := by
  have hmap : (1 + b • Y).map (fun x => (x : E)) = A := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    show algebraMap (𝓞 E) E ((1 + b • Y) i j) = A i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq] at this ⊢
      rw [map_one]; linear_combination -this
    · rw [Matrix.one_apply_ne hij] at this ⊢
      rw [map_zero, zero_add, ← this, sub_zero]
  refine ⟨1 + b • Y, ?_, hmap⟩
  intro i j
  have hij := congrFun (congrFun hmap i) j
  simp only [Matrix.map_apply] at hij
  refine ⟨fun h' => alg_inj (by rw [map_zero]; exact hij.trans ((hA i j).1 h')), fun h' => ?_, fun h' => ?_⟩
  · exact alg_inj (by rw [map_one]; exact hij.trans ((hA i j).2 h'))
  · refine ⟨Y i j, ?_⟩
    simp [Matrix.one_apply_ne (ne_of_gt h')]

theorem upb_of {N : ℕ} {b : 𝓞 E} {A : Matrix (Fin N) (Fin N) E} (hA : IsUpUni A)
    (Y : Matrix (Fin N) (Fin N) (𝓞 E)) (h : A - 1 = algebraMap (𝓞 E) E b • Y.map (algebraMap (𝓞 E) E)) :
    ∃ A' : Matrix (Fin N) (Fin N) (𝓞 E), UpB b A' ∧ A'.map (fun x => (x : E)) = A := by
  have hmap : (1 + b • Y).map (fun x => (x : E)) = A := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    show algebraMap (𝓞 E) E ((1 + b • Y) i j) = A i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq] at this ⊢
      rw [map_one]; linear_combination -this
    · rw [Matrix.one_apply_ne hij] at this ⊢
      rw [map_zero, zero_add, ← this, sub_zero]
  refine ⟨1 + b • Y, ?_, hmap⟩
  intro i j
  have hij := congrFun (congrFun hmap i) j
  simp only [Matrix.map_apply] at hij
  refine ⟨fun h' => alg_inj (by rw [map_zero]; exact hij.trans ((hA i j).1 h')), fun h' => ?_, fun h' => ?_⟩
  · exact alg_inj (by rw [map_one]; exact hij.trans ((hA i j).2 h'))
  · refine ⟨Y i j, ?_⟩
    simp [Matrix.one_apply_ne (ne_of_lt h')]

theorem close_rel {N : ℕ} {D b : 𝓞 E} (W : Matrix (Fin N) (Fin N) E)
    {Lx Ux Ly Uy : Matrix (Fin N) (Fin N) E} (hLx : IsLoUni Lx) (hUx : IsUpUni Ux) (hLy : IsLoUni Ly)
    (hUy : IsUpUni Uy) (hLxi : Intg D Lx) (hUxi : Intg D Ux)
    (ML MU : Matrix (Fin N) (Fin N) (𝓞 E))
    (hL : Ly - Lx = algebraMap (𝓞 E) E (D ^ N * b) • ML.map (algebraMap (𝓞 E) E))
    (hU : Uy - Ux = algebraMap (𝓞 E) E (D ^ N * b) • MU.map (algebraMap (𝓞 E) E)) :
    ∃ A B : Matrix (Fin N) (Fin N) (𝓞 E), LoB b A ∧ UpB b B ∧
      A.map (fun x => (x : E)) * (Lx * W * Ux) * B.map (fun x => (x : E)) = Ly * W * Uy := by
  have hpow : D ^ N = D ^ (N - (N - 1)) * D ^ (N - 1) := by rw [← pow_add]; congr 1; omega
  obtain ⟨AL, hAL⟩ := intg_adj hLxi
  obtain ⟨AU, hAU⟩ := intg_adj hUxi
  have hA1 : Ly * Lx.adjugate - 1 =
      algebraMap (𝓞 E) E b • ((D ^ (N - (N - 1)) • (ML * AL)).map (algebraMap (𝓞 E) E)) := by
    rw [← lo_mul_adj hLx, ← Matrix.sub_mul, hL, map_smul', Matrix.map_mul, hAL, hpow]
    simp only [map_mul, map_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ring_nf
  have hB1 : Ux.adjugate * Uy - 1 =
      algebraMap (𝓞 E) E b • ((D ^ (N - (N - 1)) • (AU * MU)).map (algebraMap (𝓞 E) E)) := by
    rw [← up_adj_mul hUx, ← Matrix.mul_sub, hU, map_smul', Matrix.map_mul, hAU, hpow]
    simp only [map_mul, map_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ring_nf
  obtain ⟨A, hA, hAm⟩ := lob_of (lo_mul hLy (lo_adj hLx)) _ hA1
  obtain ⟨B, hB, hBm⟩ := upb_of (up_mul (up_adj hUx) hUy) _ hB1
  refine ⟨A, B, hA, hB, ?_⟩
  rw [hAm, hBm]
  calc Ly * Lx.adjugate * (Lx * W * Ux) * (Ux.adjugate * Uy)
      = Ly * (Lx.adjugate * Lx) * W * (Ux * Ux.adjugate) * Uy := by simp only [Matrix.mul_assoc]
    _ = Ly * W * Uy := by rw [lo_adj_mul hLx, up_mul_adj hUx, Matrix.mul_one, Matrix.mul_one]

end PI.TermsAtPtFiniteW.CellW

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.MainNotions.S CellW

theorem cellReduce_holds : CellReduce := by
  intro E _ _ N p b hb
  obtain ⟨L, hL, hsum⟩ := p
  subst hsum
  obtain ⟨D, hD, hbd⟩ := bd_all L hL 1 one_ne_zero
  let X : Set (Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E) :=
    {x | IsLoUni x.2.1 ∧ IsUpUni x.2.2 ∧ x.1 = x.2.1 * pm L * x.2.2 ∧ Intg D x.2.1 ∧ Intg D x.2.2}
  let f : (Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E ×
      Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) E) →
      Bool × Fin (L.map Prod.snd).sum × Fin (L.map Prod.snd).sum → E := fun x k =>
    if k.1 then algebraMap (𝓞 E) E D * x.2.2 k.2.1 k.2.2 else algebraMap (𝓞 E) E D * x.2.1 k.2.1 k.2.2
  have hf : ∀ x ∈ X, ∀ k, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = f x k := by
    rintro x ⟨-, -, -, ⟨L', hL'⟩, ⟨U', hU'⟩⟩ ⟨c, i, j⟩
    cases c
    · exact ⟨L' i j, by simpa [f] using congrFun (congrFun hL' i) j⟩
    · exact ⟨U' i j, by simpa [f] using congrFun (congrFun hU' i) j⟩
  have hc : D ^ (L.map Prod.snd).sum * D * b ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hD) hD) hb
  obtain ⟨Zs, hfin, hZs⟩ := fin_of_cong X f hf _ hc
    (fun x y => ∃ A B : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) (𝓞 E), LoB b A ∧ UpB b B ∧
      A.map (fun x => (x : E)) * x.1 * B.map (fun x => (x : E)) = y.1) (by
    rintro x ⟨hLx, hUx, hx, hLxi, hUxi⟩ y ⟨hLy, hUy, hy, -, -⟩ hxy
    have hDE := alg_ne_zero hD
    have hM : ∀ c : Bool, ∃ M : Matrix (Fin (L.map Prod.snd).sum) (Fin (L.map Prod.snd).sum) (𝓞 E),
        ∀ i j, algebraMap (𝓞 E) E D * algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) *
          algebraMap (𝓞 E) E (M i j) = f y (c, i, j) - f x (c, i, j) := by
      intro c
      refine ⟨fun i j => Classical.choose (hxy (c, i, j)), fun i j => ?_⟩
      rw [← Classical.choose_spec (hxy (c, i, j))]
      simp only [map_mul, map_pow]; ring
    obtain ⟨ML, hML⟩ := hM false
    obtain ⟨MU, hMU⟩ := hM true
    have hL : y.2.1 - x.2.1 = algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) • ML.map (algebraMap (𝓞 E) E) := by
      ext i j
      have := hML i j
      simp only [f, Bool.false_eq_true, if_false] at this
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      apply mul_left_cancel₀ hDE
      rw [mul_sub, ← this]; ring
    have hU : y.2.2 - x.2.2 = algebraMap (𝓞 E) E (D ^ (L.map Prod.snd).sum * b) • MU.map (algebraMap (𝓞 E) E) := by
      ext i j
      have := hMU i j
      simp only [f, if_true] at this
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      apply mul_left_cancel₀ hDE
      rw [mul_sub, ← this]; ring
    obtain ⟨A, B, hA, hB, hAB⟩ := close_rel (pm L) hLx hUx hLy hUy hLxi hUxi ML MU hL hU
    exact ⟨A, B, hA, hB, by rw [hx, hy]; exact hAB⟩)
  refine ⟨Prod.fst '' Zs, hfin.image _, ?_⟩
  intro Z hZ hcell
  obtain ⟨L1, U1, hL1, hU1, hZe, hL1i, hU1i⟩ := hbd Z (intg_of_entries hZ) hcell
  obtain ⟨y, hy, A, B, hA, hB, hAB⟩ := hZs (Z, L1, U1) ⟨hL1, hU1, hZe, hL1i, hU1i⟩
  exact ⟨A, B, hA, hB, ⟨y, hy, hAB.symm⟩⟩

end PI.TermsAtPtFiniteW
