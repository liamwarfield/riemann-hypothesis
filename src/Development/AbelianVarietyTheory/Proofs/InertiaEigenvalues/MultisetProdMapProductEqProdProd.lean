module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
noncomputable section

namespace GlobalTheory.JSW

def padTo {m n : ℕ} (_h : m ≤ n) (l : Fin m → ℕ) : Fin n → ℕ :=
  fun i => if hi : (i : ℕ) < m then l ⟨i, hi⟩ else 0


open Classical in
def antiParts (m d : ℕ) : Finset (Fin m → ℕ) :=
  (Finset.Nat.antidiagonalTuple m d).filter Antitone

def jtDet {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (l : Fin m → ℕ) : A :=
  Matrix.det (Matrix.of fun i j : Fin m =>
    if ((l i : ℤ) - i + j) < 0 then 0 else h (((l i : ℤ) - i + j).toNat))

def staircase (m : ℕ) : Fin m → ℕ := fun i => m - 1 - i

def alternant (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) : MvPolynomial (Fin m) A :=
  Matrix.det (Matrix.of fun i j : Fin m => (MvPolynomial.X j : MvPolynomial (Fin m) A) ^ μ i)

theorem schur_eq_jtDet (n : ℕ) (l : Fin n → ℕ) :
    schur n l = jtDet n (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := rfl

theorem mem_antiParts {m d : ℕ} {l : Fin m → ℕ} : l ∈ antiParts m d ↔ ∑ i, l i = d ∧ Antitone l := by
  classical
  simp [antiParts, Finset.Nat.mem_antidiagonalTuple]

theorem padTo_self {m : ℕ} (l : Fin m → ℕ) : padTo le_rfl l = l := by
  funext i; simp [padTo, i.2]

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacobiTrudiAlternantExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddLeOfStrictAnti
namespace GlobalTheory.StrictAntiAddLe

theorem add_le_of_strictAnti : ∀ {m : ℕ} {s : Fin m → ℕ}, StrictAnti s →
    ∀ (k : ℕ) (i j : Fin m), (↑j : ℕ) = (↑i : ℕ) + k → s j + k ≤ s i := by
  intro m s hs k
  induction k with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    have hj := j.isLt
    have hlt : (i : ℕ) + k < m := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hlt⟩ rfl
    have h2 : s j < s ⟨(i : ℕ) + k, hlt⟩ := by
      apply hs
      rw [Fin.lt_def]
      show (i : ℕ) + k < (j : ℕ)
      omega
    omega

end GlobalTheory.StrictAntiAddLe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacobiTrudiAlternantExpansion
noncomputable section

open MvPolynomial Finset Equiv

namespace GlobalTheory.JSW

def antisymHExt {A : Type*} [CommRing A] (h : ℕ → A) (z : ℤ) : A :=
  if z < 0 then 0 else h z.toNat

def antisymMat {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (ν : Fin m → ℕ) :
    Matrix (Fin m) (Fin m) A :=
  Matrix.of fun i j => antisymHExt h ((ν j : ℤ) - staircase m i)

theorem alternant_eq_sum_perm {A : Type*} [CommRing A] (m : ℕ) (μ : Fin m → ℕ) :
    alternant A m μ = ∑ σ : Perm (Fin m),
      ((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) * ∏ i, X i ^ μ (σ i) := by
  rw [alternant, Matrix.det_apply']
  simp [Matrix.of_apply]

theorem antisym_shift_sum {A : Type*} [CommRing A] (m d : ℕ) (h : ℕ → A) (μ : Fin m → ℕ) :
    (∏ i, (X i : MvPolynomial (Fin m) A) ^ μ i) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, μ i),
        (∏ j, C (antisymHExt h ((ν j : ℤ) - μ j))) * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
  classical
  set F : (Fin m → ℕ) → MvPolynomial (Fin m) A :=
    fun ν => (∏ j, C (antisymHExt h ((ν j : ℤ) - μ j))) * ∏ j, X j ^ ν j with hF
  have key : ∀ k : Fin m → ℕ, (∏ i, (X i : MvPolynomial (Fin m) A) ^ μ i) *
      ∏ j, C (h (k j)) * X j ^ (k j) = F (k + μ) := by
    intro k
    simp only [hF]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have e : (((k + μ) j : ℕ) : ℤ) - μ j = k j := by simp
    rw [e, antisymHExt, if_neg (not_lt.2 (Int.natCast_nonneg _)), Int.toNat_natCast, Pi.add_apply, pow_add]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => key k]
  rw [← Finset.sum_image (g := fun k => k + μ) (by intro a _ b _ hab; exact add_right_cancel hab)]
  apply Finset.sum_subset
  · intro ν hν
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hν
    rw [Finset.Nat.mem_antidiagonalTuple] at hk ⊢
    simp [Finset.sum_add_distrib, hk]
  · intro ν hν hnot
    by_cases hle : ∀ j, μ j ≤ ν j
    · exfalso
      apply hnot
      refine Finset.mem_image.2 ⟨ν - μ, ?_, ?_⟩
      · rw [Finset.Nat.mem_antidiagonalTuple] at hν ⊢
        have : ∑ i, (ν - μ) i + ∑ i, μ i = ∑ i, ν i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
        omega
      · funext j
        simp [Nat.sub_add_cancel (hle j)]
    · push_neg at hle
      obtain ⟨j, hj⟩ := hle
      simp only [hF]
      rw [Finset.prod_eq_zero (Finset.mem_univ j), zero_mul]
      rw [antisymHExt, if_pos (by omega), map_zero]

theorem antisym_lhs_eq {A : Type*} [CommRing A] (m d : ℕ) (h : ℕ → A) :
    alternant A m (staircase m) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i),
        C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
  rw [alternant_eq_sum_perm, Finset.sum_mul]
  have hσ : ∀ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) *
      (∏ i, X i ^ staircase m (σ i)) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i),
        (((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) *
          ∏ j, C (antisymHExt h ((ν j : ℤ) - staircase m (σ j)))) * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
    intro σ
    rw [mul_assoc, antisym_shift_sum m d h (fun i => staircase m (σ i)),
      Equiv.sum_comp σ (staircase m), Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_mul, Matrix.det_apply', map_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_prod]
  rfl

theorem antisymMat_comp_perm {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (μ : Fin m → ℕ)
    (τ : Perm (Fin m)) :
    (antisymMat m h (fun i => μ (τ i))).det = (Perm.sign τ : ℤ) * (antisymMat m h μ).det := by
  rw [← Matrix.det_permute']
  rfl

theorem antisymMat_staircase {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (l : Fin m → ℕ) :
    (antisymMat m h (fun i => l i + staircase m i)).det = jtDet m h l := by
  rw [jtDet, ← Matrix.det_transpose]
  congr 1
  ext i j
  have hi := i.2
  have hj := j.2
  have e : (((l i + staircase m i : ℕ)) : ℤ) - (staircase m j : ℕ) = (l i : ℤ) - i + j := by
    simp only [staircase]
    omega
  simp only [antisymMat, Matrix.of_apply, Matrix.transpose_apply, antisymHExt]
  rw [e]

theorem antisym_strictAnti {m : ℕ} {l : Fin m → ℕ} (hl : Antitone l) :
    StrictAnti (fun i => l i + staircase m i) := by
  intro i j hij
  have h1 := hl hij.le
  have h2 : (i : ℕ) < j := hij
  have := j.2
  simp only [staircase]
  omega

theorem antisym_gap {m : ℕ} {s : Fin m → ℕ} (hs : StrictAnti s) :
    ∀ (k : ℕ) (i j : Fin m), (j : ℕ) = i + k → s j + k ≤ s i := by
  first
  | exact @_root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti
  | exact _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti
  | (apply _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> assumption)
  | (intros; apply _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti ..)


open Classical in
theorem antisym_sum_sort {M : Type*} [AddCommMonoid M] (m d : ℕ) (g : (Fin m → ℕ) → M) :
    ∑ l ∈ antiParts m d, ∑ τ : Perm (Fin m), g (fun i => l (τ i) + staircase m (τ i)) =
      ∑ ν ∈ (Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i)).filter Function.Injective, g ν := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => fun i => p.1 (p.2 i) + staircase m (p.2 i)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hl, -⟩ := Finset.mem_product.1 hp
    rw [mem_antiParts] at hl
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    refine ⟨?_, ?_⟩
    · rw [Equiv.sum_comp p.2 (fun i => p.1 i + staircase m i), Finset.sum_add_distrib, hl.1]
    · exact (antisym_strictAnti hl.2).injective.comp p.2.injective
  · intro p hp q hq hpq
    obtain ⟨hl, -⟩ := Finset.mem_product.1 hp
    obtain ⟨hl', -⟩ := Finset.mem_product.1 hq
    rw [mem_antiParts] at hl hl'
    set ν : Fin m → ℕ := fun i => p.1 (p.2 i) + staircase m (p.2 i) with hν
    have hν' : ν = fun i => q.1 (q.2 i) + staircase m (q.2 i) := hpq
    have a1 : Antitone (ν ∘ p.2.symm) := by
      have : ν ∘ p.2.symm = fun i => p.1 i + staircase m i := by funext i; simp [hν]
      rw [this]; exact (antisym_strictAnti hl.2).antitone
    have a2 : Antitone (ν ∘ q.2.symm) := by
      have : ν ∘ q.2.symm = fun i => q.1 i + staircase m i := by funext i; simp [hν']
      rw [this]; exact (antisym_strictAnti hl'.2).antitone
    have u := Tuple.unique_antitone a1 a2
    have hinj : Function.Injective ν := (antisym_strictAnti hl.2).injective.comp p.2.injective
    have hperm : p.2.symm = q.2.symm := Equiv.ext fun i => hinj (congrFun u i)
    have h2 : p.2 = q.2 := by simpa using congrArg Equiv.symm hperm
    have h1 : p.1 = q.1 := by
      funext i
      have := congrFun hν' (p.2.symm i)
      simp only [hν, h2, Equiv.apply_symm_apply] at this
      omega
    exact Prod.ext h1 h2
  · intro ν hν
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hν
    obtain ⟨hsum, hinj⟩ := hν
    set σ := Tuple.sort (fun i => OrderDual.toDual (ν i)) with hσ
    have hanti : Antitone (ν ∘ σ) := by
      have := Tuple.monotone_sort (fun i => OrderDual.toDual (ν i))
      exact monotone_toDual_comp_iff.1 this
    have hs : StrictAnti (ν ∘ σ) := hanti.strictAnti_of_injective (hinj.comp σ.injective)
    have hδ : ∀ i, staircase m i ≤ ν (σ i) := by
      intro i
      have hm : m - 1 < m := by have := i.2; omega
      have := antisym_gap hs (m - 1 - i) i ⟨m - 1, hm⟩ (by simp; have := i.2; omega)
      simp only [staircase, Function.comp] at this ⊢
      omega
    refine ⟨(fun i => ν (σ i) - staircase m i, σ.symm), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
      rw [mem_antiParts]
      refine ⟨?_, ?_⟩
      · show ∑ i, (ν (σ i) - staircase m i) = d
        have e : ∑ i, (ν (σ i) - staircase m i) + ∑ i, staircase m i = ∑ i, ν (σ i) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hδ i)
        rw [Equiv.sum_comp σ ν] at e
        omega
      · intro i j hij
        have g := antisym_gap hs (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega)
        have h1 := hδ i
        have h2 := hδ j
        simp only [staircase, Function.comp] at g h1 h2 ⊢
        have := j.2
        have : (i : ℕ) ≤ j := hij
        omega
    · funext i
      have := hδ (σ.symm i)
      simp only [Equiv.apply_symm_apply] at this ⊢
      omega
  · intro p _
    rfl

theorem alternant_staircase_mul_antidiagonal {A : Type} [CommRing A] (m d : ℕ) (h : ℕ → A) :
    alternant A m (staircase m) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, MvPolynomial.C (h (k j)) * MvPolynomial.X j ^ (k j) =
      ∑ l ∈ antiParts m d,
        MvPolynomial.C (jtDet m h l) * alternant A m (fun i => l i + staircase m i) := by
  classical
  rw [antisym_lhs_eq]
  have hr : ∀ l : Fin m → ℕ, C (jtDet m h l) * alternant A m (fun i => l i + staircase m i) =
      ∑ τ : Perm (Fin m), (fun ν : Fin m → ℕ =>
        C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j)
        (fun i => l (τ i) + staircase m (τ i)) := by
    intro l
    rw [alternant_eq_sum_perm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e := antisymMat_comp_perm m h (fun i => l i + staircase m i) τ
    simp only at e ⊢
    rw [e, antisymMat_staircase, map_mul, map_intCast]
    ring
  rw [Finset.sum_congr rfl fun l _ => hr l, antisym_sum_sort m d
    (fun ν : Fin m → ℕ => C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j)]
  symm
  apply Finset.sum_filter_of_ne
  intro ν _ hne
  by_contra hni
  apply hne
  obtain ⟨a, b, hab, hne'⟩ : ∃ a b, ν a = ν b ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    exact ⟨a, b, hab, hne⟩
  rw [Matrix.det_zero_of_column_eq hne' (fun k => by simp [antisymMat, hab]), map_zero, zero_mul]

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacobiTrudiAlternantExpansionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_trudi_alternant_expansion : ∀ {A : Type} [CommRing A] (m d : ℕ) (h : ℕ → A),
    GlobalTheory.JSW.alternant A m (GlobalTheory.JSW.staircase m) *
                 ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, MvPolynomial.C (h (k j)) * MvPolynomial.X j ^ (k j) =
      ∑ l ∈ GlobalTheory.JSW.antiParts m d,
        MvPolynomial.C (GlobalTheory.JSW.jtDet m h l) * GlobalTheory.JSW.alternant A m (fun i => l i + GlobalTheory.JSW.staircase m i) := by
  exact @GlobalTheory.JSW.alternant_staircase_mul_antidiagonal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurPolynomialPadZerosEqJacobiTrudiDeterminant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurPolynomialPadZerosEqJacobiTrudiDeterminant
noncomputable section

namespace GlobalTheory.JSW

theorem jacobi_trudi_det_pad_zeros {A : Type*} [CommRing A] (h : ℕ → A) (h0 : h 0 = 1) {m n : ℕ} (hmn : m ≤ n)
    (l : Fin m → ℕ) : jtDet n h (padTo hmn l) = jtDet m h l := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  unfold jtDet
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  set M := (Matrix.of fun i j : Fin (m + k) =>
    if ((padTo hmn l i : ℤ) - i + j) < 0 then 0 else h (((padTo hmn l i : ℤ) - i + j).toNat)).submatrix
      finSumFinEquiv finSumFinEquiv with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hM, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply, padTo]
    have hj := j.2
    simp
    omega
  have h22 : M.toBlocks₂₂.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_eq_one
      intro i _
      simp [hM, Matrix.toBlocks₂₂, padTo, h0]
    · intro i j hij
      simp only [hM, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_right, padTo]
      have : (j : ℕ) < i := hij
      simp
      omega
  have h11 : M.toBlocks₁₁ = Matrix.of fun i j : Fin m =>
      if ((l i : ℤ) - i + j) < 0 then 0 else h (((l i : ℤ) - i + j).toNat) := by
    ext i j
    simp [hM, Matrix.toBlocks₁₁, padTo]
  rw [← Matrix.fromBlocks_toBlocks M, h21, Matrix.det_fromBlocks_zero₂₁, h22, h11, mul_one]

theorem schur_padTo_eq_jtDet {m n : ℕ} (hmn : m ≤ n) (l : Fin m → ℕ) :
    schur n (padTo hmn l) = jtDet m (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := by
  rw [schur_eq_jtDet]
  exact jacobi_trudi_det_pad_zeros _ (MvPolynomial.hsymm_zero _ _) hmn l

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurPolynomialPadZerosEqJacobiTrudiDeterminantStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurPolynomial_padZeros_eq_jacobiTrudiDeterminant : ∀ {m n : ℕ} (hmn : m ≤ n) (l : Fin m → ℕ),
    GlobalTheory.JSW.schur n (GlobalTheory.JSW.padTo hmn l) = GlobalTheory.JSW.jtDet m (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := by
  first | exact @GlobalTheory.JSW.schur_padTo_eq_jtDet | exact GlobalTheory.JSW.schur_padTo_eq_jtDet | (intros; apply GlobalTheory.JSW.schur_padTo_eq_jtDet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegree
noncomputable section

open MvPolynomial

namespace GlobalTheory.JSW.CauchyGlue

theorem map_jtDet {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (h : ℕ → A)
    (l : Fin m → ℕ) : f (jtDet m h l) = jtDet m (fun k => f (h k)) l := by
  rw [jtDet, jtDet, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem map_alternant {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (μ : Fin m → ℕ) :
    MvPolynomial.map f (alternant A m μ) = alternant B m μ := by
  rw [alternant, alternant, RingHom.map_det]
  congr 1
  ext i j
  simp

theorem alternant_eq_det (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) :
    alternant A m μ = Matrix.det (Matrix.of fun i j : Fin m => (X i : MvPolynomial (Fin m) A) ^ μ j) := by
  rw [alternant, ← Matrix.det_transpose]
  rfl

theorem alternant_staircase_ne_zero (m : ℕ) : alternant ℂ m (staircase m) ≠ 0 := by
  have e : (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℂ) ^ staircase m i) =
      (Matrix.transpose (Matrix.vandermonde (fun j : Fin m => (X j : MvPolynomial (Fin m) ℂ)))).submatrix Fin.revPerm id := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Fin.revPerm_apply, id, staircase, Fin.val_rev]
    congr 1
    omega
  rw [alternant, e, Matrix.det_permute, Matrix.det_transpose]
  refine mul_ne_zero ?_ ?_
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with h | h <;> simp [h]
  · exact (Matrix.det_vandermonde_ne_zero_iff).2 (MvPolynomial.X_injective)

theorem bialt_int (m : ℕ) (l : Fin m → ℕ) (hl : Antitone l) :
    schur m l * alternant ℤ m (staircase m) = alternant ℤ m (fun i => l i + staircase m i) := by
  simp only [alternant_eq_det, staircase]
  rw [schur_mul_det_eq_det m l hl]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply]
  congr 1
  have := j.2
  omega

theorem cauchy_formal : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  intro m n hmn α β d
  set hC : ℕ → ℂ := fun k => eval₂ (Int.castRingHom ℂ) α (hsymm (Fin n) ℤ k) with hhC
  have hA := GlobalTheory.T.jacobi_trudi_alternant_expansion (A := ℂ) m d hC
  have hpad : ∀ l : Fin m → ℕ, schurAt (padTo hmn l) α = jtDet m hC l := by
    intro l
    rw [schurAt, GlobalTheory.T.schurPolynomial_padZeros_eq_jacobiTrudiDeterminant hmn l, ← MvPolynomial.coe_eval₂Hom, map_jtDet]
    rfl
  have hbi : ∀ l ∈ antiParts m d, alternant ℂ m (fun i => l i + staircase m i) =
      MvPolynomial.map (Int.castRingHom ℂ) (schur m l) * alternant ℂ m (staircase m) := by
    intro l hl
    have := congrArg (MvPolynomial.map (Int.castRingHom ℂ)) (bialt_int m l (mem_antiParts.1 hl).2)
    rw [map_mul, map_alternant, map_alternant] at this
    exact this.symm
  have hR : ∑ l ∈ antiParts m d, C (jtDet m hC l) * alternant ℂ m (fun i => l i + staircase m i) =
      alternant ℂ m (staircase m) *
        ∑ l ∈ antiParts m d, C (jtDet m hC l) * MvPolynomial.map (Int.castRingHom ℂ) (schur m l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hbi l hl]
    ring
  rw [hR] at hA
  have hP := mul_left_cancel₀ (alternant_staircase_ne_zero m) hA
  have hE := congrArg (MvPolynomial.eval β) hP
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_prod, map_mul, eval_C, eval_X, map_pow, MvPolynomial.eval_map] at hE
  refine (Finset.sum_congr rfl fun l _ => ?_).trans hE.symm
  rw [hpad]
  rfl

end GlobalTheory.JSW.CauchyGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegreeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchy_identity_schur_formal_degree : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  exact @GlobalTheory.JSW.CauchyGlue.cauchy_formal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerInversePowerSeriesEvalOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerInversePowerSeriesEvalOne
noncomputable section

namespace GlobalTheory.JSW

open PowerSeries

theorem hasSum_coeff_mk_mul_polynomial (c : ℕ → ℂ) (hc : Summable fun d => ‖c d‖)
    (p : Polynomial ℂ) :
    HasSum (fun d => coeff d (mk c * (p : PowerSeries ℂ))) ((∑' d, c d) * p.eval 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa [Polynomial.coe_add, mul_add, Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    have hf : (fun d => coeff d (mk c * ((Polynomial.monomial n a : Polynomial ℂ) : PowerSeries ℂ)))
        = fun d => if n ≤ d then c (d - n) * a else 0 := by
      funext d
      rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow, ← mul_assoc,
        PowerSeries.coeff_mul_X_pow']
      split_ifs <;> simp [PowerSeries.coeff_mul_C]
    rw [hf, Polynomial.eval_monomial, one_pow, mul_one]
    refine (hasSum_nat_add_iff' n).mp ?_
    have h0 : ∑ i ∈ Finset.range n, (if n ≤ i then c (i - n) * a else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp [not_le.mpr hi]
    rw [h0, sub_zero]
    simpa using (Summable.of_norm hc).hasSum.mul_right a

theorem eulerInverse_eval_one {ι : Type} [Fintype ι] (c : ℕ → ℂ) (hc : Summable fun d => ‖c d‖)
    (Q : ι → ℂ)
    (h : PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1) :
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  set P : Polynomial ℂ := ∏ p, (1 - Polynomial.C (Q p) * Polynomial.X) with hPdef
  have hP : (P : PowerSeries ℂ) = ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) := by
    have := map_prod (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)
      (fun p => 1 - Polynomial.C (Q p) * Polynomial.X) Finset.univ
    rw [hPdef]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply] at this
    rw [this]
    simp
  have h1 := hasSum_coeff_mk_mul_polynomial c hc P
  rw [hP, h] at h1
  have h2 : HasSum (fun d => coeff d (1 : PowerSeries ℂ)) 1 := by
    simpa [PowerSeries.coeff_one] using hasSum_ite_eq 0 (1 : ℂ)
  have h3 := h1.unique h2
  have hev : P.eval 1 = ∏ p, (1 - Q p) := by simp [hPdef, Polynomial.eval_prod]
  rw [hev] at h3
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  · rw [← eq_inv_of_mul_eq_one_left h3]
    exact (Summable.of_norm hc).hasSum

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerInversePowerSeriesEvalOneStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerInverse_powerSeries_eval_one : ∀ {ι : Type} [Fintype ι] (c : ℕ → ℂ), (Summable fun d => ‖c d‖) → ∀ (Q : ι → ℂ),
    PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1 →
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  exact @GlobalTheory.JSW.eulerInverse_eval_one
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRegroupAntitonePartitionsByDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRegroupAntitonePartitionsByDegree
noncomputable section

namespace GlobalTheory.JSW

theorem tsum_fibre_entrySum_eq {m : ℕ} {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (F : (Fin m → ℕ) → E) (d : ℕ) :
    ∑' b : (fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}, F b.1.1 =
      ∑ l ∈ antiParts m d, F l := by
  rw [← Finset.tsum_subtype (antiParts m d) F]
  let e : ((fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}) ≃
      {x // x ∈ antiParts m d} :=
    { toFun := fun b => ⟨b.1.1, mem_antiParts.2 ⟨b.2, b.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (mem_antiParts.1 x.2).2⟩, (mem_antiParts.1 x.2).1⟩
      left_inv := fun b => rfl
      right_inv := fun x => rfl }
  exact e.tsum_eq (fun x => F x.1)

theorem regroup_antiParts {m : ℕ} (G : (Fin m → ℕ) → ℂ)
    (hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) :
    Summable (fun d => ‖∑ l ∈ antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s := by
  set σ : {l : Fin m → ℕ // Antitone l} → ℕ := fun l => ∑ i, l.1 i with hσ
  have h1 := hG.hasSum.tsum_fiberwise σ
  have h1' : Summable (fun d => ∑ l ∈ antiParts m d, ‖G l‖) := by
    refine h1.summable.congr fun d => ?_
    exact tsum_fibre_entrySum_eq (fun l => ‖G l‖) d
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => norm_sum_le _ _) h1', ?_⟩
  intro s hs
  have hg : Summable fun l : {l : Fin m → ℕ // Antitone l} => G l.1 := hG.of_norm
  have h2 := hg.hasSum.tsum_fiberwise σ
  have h2' : HasSum (fun d => ∑ l ∈ antiParts m d, G l) (∑' l : {l : Fin m → ℕ // Antitone l}, G l.1) :=
    h2.congr_fun fun d => (tsum_fibre_entrySum_eq G d).symm
  rw [hs.unique h2']
  exact hg.hasSum

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRegroupAntitonePartitionsByDegreeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_regroup_antitonePartitions_by_degree : ∀ {m : ℕ} (G : (Fin m → ℕ) → ℂ),
    (Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) →
    Summable (fun d => ‖∑ l ∈ GlobalTheory.JSW.antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ GlobalTheory.JSW.antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s := by
  first | exact @GlobalTheory.JSW.regroup_antiParts | exact GlobalTheory.JSW.regroup_antiParts | (intros; apply GlobalTheory.JSW.regroup_antiParts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MkSumProdHsymmMulProdOneSub
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MkSumProdHsymmMulProdOneSub
noncomputable section

open Finset PowerSeries

namespace GlobalTheory.JSW

theorem sum_finsuppAntidiag_univ_fin {M : Type*} [AddCommMonoid M] {m : ℕ} (d : ℕ)
    (F : (Fin m → ℕ) → M) :
    ∑ l ∈ finsuppAntidiag (univ : Finset (Fin m)) d, F l =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d, F k := by
  refine Finset.sum_equiv Finsupp.equivFunOnFinite ?_ ?_
  · intro l
    simp [mem_finsuppAntidiag, Finset.Nat.mem_antidiagonalTuple]
  · intro l _
    rfl

theorem coeff_prod_mk_fin {m : ℕ} (f : Fin m → ℕ → ℂ) (d : ℕ) :
    coeff d (∏ j, PowerSeries.mk (f j)) =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, f j (k j) := by
  rw [coeff_prod, sum_finsuppAntidiag_univ_fin d (fun k => ∏ j, coeff (k j) (PowerSeries.mk (f j)))]
  simp only [coeff_mk]

theorem prod_map_X_eq_monomial_toFinsupp {n : ℕ} (s : Multiset (Fin n)) :
    (s.map (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add (f := _),
      Multiset.toFinsupp_singleton, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

theorem sum_toFinsupp_fin {n : ℕ} (s : Multiset (Fin n)) :
    ∑ i, Multiset.toFinsupp s i = Multiset.card s := by
  simp [Multiset.toFinsupp_apply, Multiset.sum_count_eq_card]

theorem hsymm_fin_eq_sum_monomial {n : ℕ} (k : ℕ) :
    MvPolynomial.hsymm (Fin n) ℤ k =
      ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) k, MvPolynomial.monomial l 1 := by
  rw [MvPolynomial.hsymm]
  refine Finset.sum_bij (fun s _ => Multiset.toFinsupp s.1) ?_ ?_ ?_ ?_
  · intro s _
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    rw [sum_toFinsupp_fin, s.2]
  · intro a _ b _ h
    exact Sym.coe_injective (Multiset.toFinsupp.injective h)
  · intro l hl
    rw [mem_finsuppAntidiag] at hl
    refine ⟨⟨Finsupp.toMultiset l, ?_⟩, mem_univ _, ?_⟩
    · rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact hl.1
    · simp
  · intro s _
    exact prod_map_X_eq_monomial_toFinsupp s.1

theorem eval₂_hsymm_fin {n : ℕ} (α : Fin n → ℂ) (k : ℕ) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ k) =
      ∑ l ∈ Finset.Nat.antidiagonalTuple n k, ∏ i, α i ^ l i := by
  rw [hsymm_fin_eq_sum_monomial, MvPolynomial.eval₂_sum,
    ← sum_finsuppAntidiag_univ_fin k (fun l => ∏ i, α i ^ l i)]
  refine sum_congr rfl fun l _ => ?_
  rw [MvPolynomial.eval₂_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem one_sub_C_mul_X_mul_mk_pow (a : ℂ) :
    (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ k) = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
  cases k with
  | zero => simp
  | succ k => simp [pow_succ, mul_comm]

theorem mk_hsymm_mul_prod_one_sub {n : ℕ} (α : Fin n → ℂ) (u : ℂ) :
    PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * u ^ k) *
      ∏ i, (1 - PowerSeries.C (α i * u) * PowerSeries.X) = 1 := by
  have h : PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * u ^ k) =
      ∏ i, PowerSeries.mk (fun k => (α i * u) ^ k) := by
    ext k
    rw [coeff_prod_mk_fin, coeff_mk, eval₂_hsymm_fin, sum_mul]
    refine sum_congr rfl fun l hl => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hl
    simp_rw [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hl]
  rw [h, ← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [mul_comm]; exact one_sub_C_mul_X_mul_mk_pow _

theorem mk_sum_prod_hsymm_mul_prod_one_sub : ∀ {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ),
    PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) *
      ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) = 1 := by
  intro m n α β T
  have h1 : PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) =
      ∏ j, PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * (β j * T) ^ k) := by
    ext d
    rw [coeff_mk, coeff_prod_mk_fin, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hk
    simp_rw [mul_pow, ← mul_assoc, prod_mul_distrib, prod_pow_eq_pow_sum, hk]
    ring
  have h2 : ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) =
      ∏ j, ∏ i, (1 - PowerSeries.C (α i * (β j * T)) * PowerSeries.X) := by
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp_rw [mul_assoc]
  rw [h1, h2, ← prod_mul_distrib]
  exact prod_eq_one fun j _ => mk_hsymm_mul_prod_one_sub α (β j * T)

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MkSumProdHsymmMulProdOneSubStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mk_sum_hsymm_mul_prod_one_sub_eq_one : ∀ {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ),
    PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) *
      ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) = 1 := by
  exact @GlobalTheory.JSW.mk_sum_prod_hsymm_mul_prod_one_sub
end
end

noncomputable section

namespace GlobalTheory.JSW

open Finset

theorem cauchy_local {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) α * schurAt l.1 β‖ * ‖T‖ ^ (∑ i, l.1 i)) :
    (∀ i j, 1 - α i * β j * T ≠ 0) ∧
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} =>
      schurAt (padTo hmn l.1) α * schurAt l.1 β * T ^ (∑ i, l.1 i))
      (∏ i, ∏ j, (1 - α i * β j * T)⁻¹) := by
  set G : (Fin m → ℕ) → ℂ := fun l => schurAt (padTo hmn l) α * schurAt l β * T ^ (∑ i, l i) with hGdef
  have hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖ := by
    refine hs.congr fun l => ?_
    simp [G, norm_pow]
  obtain ⟨hsum, htrans⟩ := GlobalTheory.T.hasSum_regroup_antitonePartitions_by_degree G hG
  have hc : (fun d => ∑ l ∈ antiParts m d, G l) = fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
      ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
    funext d
    rw [← GlobalTheory.T.cauchy_identity_schur_formal_degree hmn α β d, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [G]; rw [(mem_antiParts.1 hl).1]; ring
  have h5 := GlobalTheory.T.mk_sum_hsymm_mul_prod_one_sub_eq_one α β T
  rw [← hc] at h5
  obtain ⟨hne, hhas⟩ := GlobalTheory.T.eulerInverse_powerSeries_eval_one _ hsum (fun p : Fin n × Fin m => α p.1 * β p.2 * T) h5
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Fintype.prod_prod_type] at hne
    exact Finset.prod_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 hne i (mem_univ _)) j (mem_univ _)
  · have := htrans _ hhas
    rw [← Finset.prod_inv_distrib, Fintype.prod_prod_type] at this
    exact this

theorem multiset_prod_map_product_eq_prod_prod {X Y : Type} (A : Multiset X) (B : Multiset Y) (f : X × Y → ℂ) :
    ((A ×ˢ B).map f).prod = (A.map fun a => (B.map fun b => f (a, b)).prod).prod := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih => simp [Multiset.cons_product, ih]

theorem locL_univ (q : ℕ) {m n : ℕ} (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (s : ℂ) :
    locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s =
      ∏ i, ∏ j, (1 - (α i : ℂ) * β j * (q : ℂ) ^ (-s))⁻¹ := by
  rw [locL, multiset_prod_map_product_eq_prod_prod, Multiset.map_map]
  simp only [Multiset.map_map, Function.comp_def]
  rfl

theorem cauchy_locL {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (q : ℕ) (s : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β j : ℂ))‖ *
        ‖(q : ℂ) ^ (-s)‖ ^ (∑ i, l.1 i)) :
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} => schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) *
      schurAt l.1 (fun j => (β j : ℂ)) * ((q : ℂ) ^ (-s)) ^ (∑ i, l.1 i))
      (locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s) := by
  rw [locL_univ]; exact (cauchy_local hmn _ _ _ hs).2

end GlobalTheory.JSW
