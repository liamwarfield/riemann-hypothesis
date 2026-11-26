module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ModelIdentificationOfExplicitMap

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.StatementY
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering

open MvPolynomial Formalism.GradedWeylDivisibility

def covY (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial _ K))

def FirstColumnPolynomialsSpan : Prop :=
  ∀ (K : Type) [Field K] (m P : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), 1 ≤ m →
    (F ∈ dualWeyl K (m + 1) (m + 1) (fun t => if t = 0 then P else 0) ↔
      ∃ f : MvPolynomial (Fin (m + 1)) K, f.IsHomogeneous P ∧ rename (fun i => (i, (0 : Fin (m + 1)))) f = F)

def SignedMinorPolynomialsSpan : Prop :=
  ∀ (K : Type) [Field K] (m Q : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), 1 ≤ m →
    (F ∈ dualWeyl K (m + 1) (m + 1) (fun t => if t = Fin.last m then 0 else Q) ↔
      ∃ f : MvPolynomial (Fin (m + 1)) K, f.IsHomogeneous Q ∧ aeval (covY K m) f = F)

def SignedMinorsAlgIndependent : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → AlgebraicIndependent K (covY K m)

def SignedMinorsCofactorTransform : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)), IsUnit g.det →
    rowAct K g (covY K m i) = C g.det * ∑ j, C (g⁻¹ j i) * covY K m j

def CovL5adj : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)),
    rowAct K g (covY K m i) = ∑ j, C (g.adjugate j i) * covY K m j

end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.CovWeyl
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering

open MvPolynomial Formalism.GradedWeylDivisibility

section general

variable {K : Type} [Field K] {r n : ℕ}

private lemma cw_pow_mem {ν : Fin n → ℕ} {y : MvPolynomial (Fin r × Fin n) K}
    (hy : y ∈ dualWeyl K r n ν) (k : ℕ) : y ^ k ∈ dualWeyl K r n (k • ν) := by
  induction k with
  | zero => simpa using (dualWeylMul K r n 0 0 0 0).2
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact (dualWeylMul K r n _ _ _ _).1 ih hy

private lemma cw_prod_mem {ι : Type} (s : Finset ι) (μ : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) K) (h : ∀ i ∈ s, g i ∈ dualWeyl K r n (μ i)) :
    ∏ i ∈ s, g i ∈ dualWeyl K r n (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (dualWeylMul K r n 0 0 0 0).2
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (dualWeylMul K r n _ _ _ _).1 (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma cw_aeval_mem {σ : Type} {ν : Fin n → ℕ} (y : σ → MvPolynomial (Fin r × Fin n) K)
    (hy : ∀ i, y i ∈ dualWeyl K r n ν) (Q : ℕ) (f : MvPolynomial σ K) (hf : f.IsHomogeneous Q) :
    aeval y f ∈ dualWeyl K r n (Q • ν) := by
  rw [aeval_def, eval₂_eq]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : ∑ i ∈ d.support, d i = Q := by
    have := hf (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have := cw_prod_mem d.support (fun i => d i • ν) (fun i => y i ^ d i)
    (fun i _ => cw_pow_mem (hy i) _)
  rwa [← Finset.sum_smul, hdeg] at this

private lemma cw_prod_aeval {σ ι : Type} (y : σ → MvPolynomial (Fin r × Fin n) K) (s : Finset ι)
    (g : ι → MvPolynomial (Fin r × Fin n) K) (e : ι → ℕ)
    (h : ∀ k, ∃ f : MvPolynomial σ K, f.IsHomogeneous (e k) ∧ aeval y f = g k) :
    ∃ f : MvPolynomial σ K, f.IsHomogeneous (∑ k ∈ s, e k) ∧ aeval y f = ∏ k ∈ s, g k := by
  choose f hf1 hf2 using h
  exact ⟨∏ k ∈ s, f k, IsHomogeneous.prod _ _ _ (fun k _ => hf1 k), by
    rw [map_prod]; exact Finset.prod_congr rfl fun k _ => hf2 k⟩

private lemma cw_span_le {σ : Type} (y : σ → MvPolynomial (Fin r × Fin n) K) (Q : ℕ) (ν : Fin n → ℕ)
    (h : ∀ (k : ℕ) (sz : Fin k → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
      shapeDeg sz = ν → ∃ f : MvPolynomial σ K, f.IsHomogeneous Q ∧ aeval y f = bideterminant K sz hsz I)
    (F : MvPolynomial (Fin r × Fin n) K) (hF : F ∈ dualWeyl K r n ν) :
    ∃ f : MvPolynomial σ K, f.IsHomogeneous Q ∧ aeval y f = F := by
  rw [standardMonomialSpanDomain K r n ν] at hF
  have key := (Submodule.span_le
    (p := Submodule.map (aeval y).toLinearMap (homogeneousSubmodule σ K Q))).mpr (by
      rintro _ ⟨k, sz, hsz, I, hs, rfl⟩
      obtain ⟨f, hf, hfe⟩ := h k sz hsz I hs
      exact ⟨f, hf, hfe⟩) hF
  obtain ⟨f, hf, hfe⟩ := key
  exact ⟨f, hf, hfe⟩

private lemma cw_single_mem (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin r) :
    initMinor K J hs ∈ dualWeyl K r n (fun t => if t.val < s then 1 else 0) := by
  have := bidetMem K r n 1 (fun _ => s) (fun _ => hs) (fun _ => J)
  have h1 : bideterminant K (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => J) = initMinor K J hs := by
    simp [bideterminant]
  have h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = fun t => if t.val < s then 1 else 0 := by
    funext t
    by_cases ht : t.val < s <;> simp [shapeDeg, ht]
  rwa [h1, h2] at this

private lemma cw_minor0 (s : ℕ) (hs : s ≤ n) (h : s = 0) (J : Fin s → Fin r) :
    initMinor K J hs = 1 := by
  subst h
  simp [initMinor]

private lemma cw_le_of_shape {k : ℕ} (sz : Fin k → ℕ) (t : Fin n) (h : shapeDeg sz t = 0) (j : Fin k) :
    sz j ≤ t.val := by
  by_contra hk
  have hm : j ∈ Finset.univ.filter (fun k => t.val < sz k) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  simp only [shapeDeg, Finset.card_eq_zero] at h
  rw [h] at hm
  simp at hm

end general

private lemma cw_card {n k : ℕ} (sz : Fin k → ℕ) :
    ∑ j, (if 0 < sz j then 1 else 0) = shapeDeg sz (0 : Fin (n + 1)) := by
  simp only [shapeDeg, Fin.val_zero, Finset.sum_boole, Nat.cast_id]
  congr

private lemma cw_minor1 {K : Type} [Field K] {r n : ℕ} (s : ℕ) (hs : s ≤ n + 1) (h : 0 < s) (h1 : s ≤ 1)
    (J : Fin s → Fin r) : initMinor K J hs = X (J ⟨0, h⟩, 0) := by
  obtain rfl : s = 1 := by omega
  simp [initMinor]

theorem first_column_polynomials_characterize : FirstColumnPolynomialsSpan := by
  intro K _ m P F hm
  have hren : ∀ f : MvPolynomial (Fin (m + 1)) K, rename (fun i => (i, (0 : Fin (m + 1)))) f =
      aeval (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) f :=
    fun f => DFunLike.congr_fun (algHom_ext fun i => by simp) f
  simp only [hren]
  constructor
  · refine cw_span_le _ P _ ?_ F
    intro k sz hsz I hs
    have h0 : shapeDeg sz (0 : Fin (m + 1)) = P := by rw [hs]; simp
    have h1 : shapeDeg sz (⟨1, by omega⟩ : Fin (m + 1)) = 0 := by rw [hs]; simp [Fin.ext_iff]
    have hle : ∀ j, sz j ≤ 1 := cw_le_of_shape sz _ h1
    have := cw_prod_aeval
      (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) Finset.univ
      (fun j => initMinor K (I j) (hsz j)) (fun j => if 0 < sz j then 1 else 0) ?_
    · rw [cw_card, h0] at this
      exact this
    · intro j
      by_cases hj : 0 < sz j
      · refine ⟨X (I j ⟨0, hj⟩), by simpa [hj] using isHomogeneous_X K (I j ⟨0, hj⟩), ?_⟩
        rw [aeval_X, cw_minor1 _ _ hj (hle j)]
      · exact ⟨1, by simpa [hj] using isHomogeneous_one (Fin (m + 1)) K,
          by rw [map_one, cw_minor0 _ _ (by omega)]⟩
  · rintro ⟨f, hf, rfl⟩
    have := cw_aeval_mem
      (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))
      (ν := fun t => if t.val < 1 then 1 else 0) ?_ P f hf
    · convert this using 2
      funext t
      by_cases ht : t = 0
      · simp [ht]
      · simp [ht]
    · intro i
      have := cw_single_mem (K := K) (r := m + 1) (n := m + 1) 1 (by omega) (fun _ => i)
      rwa [cw_minor1 _ _ (by omega) le_rfl] at this

private lemma cw_key {K : Type} [Field K] (m : ℕ) (J : Fin m → Fin (m + 1)) :
    ∃ (i : Fin (m + 1)) (ε : K), initMinor K J (Nat.le_succ m) = C ε * covY K m i := by
  by_cases hJ : Function.Injective J
  · have hns : ¬ Function.Surjective J := by
      intro hsur
      have := Fintype.card_le_of_surjective J hsur
      simp at this
    simp only [Function.Surjective, not_forall, not_exists] at hns
    obtain ⟨i, hi⟩ := hns
    have hex : ∀ a, ∃ z, i.succAbove z = J a := fun a => Fin.exists_succAbove_eq (hi a)
    choose σ hσ using hex
    have hinj : Function.Injective σ := by
      intro a b hab
      apply hJ
      rw [← hσ a, ← hσ b, hab]
    let e : Equiv.Perm (Fin m) := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
    set N : Matrix (Fin m) (Fin m) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
      fun a b => X (i.succAbove a, b.castSucc) with hN
    have hM : initMinor K J (Nat.le_succ m) = (N.submatrix e id).det := by
      unfold initMinor
      refine congrArg Matrix.det (Matrix.ext fun a b => ?_)
      change X (J a, Fin.castLE _ b) = X (i.succAbove (σ a), b.castSucc)
      rw [hσ a]
      rfl
    refine ⟨i, ((Equiv.Perm.sign e : ℤ) : K) * (-1) ^ (i : ℕ), ?_⟩
    rw [hM, Matrix.det_permute]
    have h1 : ((-1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ^ (i : ℕ)) * (-1) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]; simp
    have h2 : covY K m i = (-1) ^ (i : ℕ) * N.det := rfl
    rw [h2]
    simp only [map_mul, map_pow, map_neg, map_one, map_intCast]
    linear_combination (-(((Equiv.Perm.sign e : ℤ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) * N.det) * h1
  · simp only [Function.Injective, not_forall] at hJ
    obtain ⟨a, b, hab, hne⟩ := hJ
    refine ⟨0, 0, ?_⟩
    rw [map_zero, zero_mul]
    unfold initMinor
    refine Matrix.det_zero_of_row_eq hne ?_
    funext q
    simp [hab]

private lemma cw_key' {K : Type} [Field K] (m s : ℕ) (hs : s ≤ m + 1) (h : s = m) (J : Fin s → Fin (m + 1)) :
    ∃ (i : Fin (m + 1)) (ε : K), initMinor K J hs = C ε * covY K m i := by
  subst h
  exact cw_key s J

private lemma cw_covY_mem {K : Type} [Field K] (m : ℕ) (i : Fin (m + 1)) :
    covY K m i ∈ dualWeyl K (m + 1) (m + 1) (fun t => if t.val < m then 1 else 0) := by
  have := cw_single_mem (K := K) (r := m + 1) (n := m + 1) m (Nat.le_succ m) i.succAbove
  have h2 : covY K m i = ((-1 : K) ^ (i : ℕ)) • initMinor K i.succAbove (Nat.le_succ m) := by
    rw [smul_eq_C_mul]
    simp only [map_pow, map_neg, map_one]
    rfl
  rw [h2]
  exact Submodule.smul_mem _ _ this

theorem signed_minor_polynomials_characterize : SignedMinorPolynomialsSpan := by
  intro K _ m Q F hm
  constructor
  · refine cw_span_le _ Q _ ?_ F
    intro k sz hsz I hs
    have h0 : shapeDeg sz (0 : Fin (m + 1)) = Q := by
      rw [hs]
      have : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [this]
    have h1 : shapeDeg sz (⟨m - 1, by omega⟩ : Fin (m + 1)) = Q := by
      rw [hs]
      have : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [this]
    have h2 : shapeDeg sz (Fin.last m) = 0 := by rw [hs]; simp
    have hle : ∀ j, sz j ≤ m := cw_le_of_shape sz _ h2
    have hsub : Finset.univ.filter (fun j => m - 1 < sz j) ⊆ Finset.univ.filter (fun j => 0 < sz j) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      have a0 : (Finset.univ.filter (fun j => 0 < sz j)).card = Q := h0
      have a1 : (Finset.univ.filter (fun j => m - 1 < sz j)).card = Q := h1
      rw [a0, a1])
    have hm' : ∀ j, 0 < sz j → sz j = m := by
      intro j hj
      have : j ∈ Finset.univ.filter (fun j => m - 1 < sz j) := by
        rw [heq]; simpa using hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      have := hle j
      omega
    have := cw_prod_aeval (covY K m) Finset.univ
      (fun j => initMinor K (I j) (hsz j)) (fun j => if 0 < sz j then 1 else 0) ?_
    · rw [cw_card, h0] at this
      exact this
    · intro j
      by_cases hj : 0 < sz j
      · obtain ⟨i, ε, hi⟩ := cw_key' (K := K) m (sz j) (hsz j) (hm' j hj) (I j)
        refine ⟨C ε * X i, by simpa [hj] using (isHomogeneous_X K i).C_mul ε, ?_⟩
        rw [map_mul, aeval_X, aeval_C, hi]
        rfl
      · exact ⟨1, by simpa [hj] using isHomogeneous_one (Fin (m + 1)) K,
          by rw [map_one, cw_minor0 _ _ (by omega)]⟩
  · rintro ⟨f, hf, rfl⟩
    have := cw_aeval_mem (covY K m) (cw_covY_mem m) Q f hf
    convert this using 2
    funext t
    by_cases ht : t = Fin.last m
    · simp [ht]
    · have : t.val < m := by
        have h1 := t.isLt
        have h2 : t.val ≠ m := fun h => ht (Fin.ext (by simpa using h))
        omega
      simp [ht, this]

end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.CovDet
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering

open MvPolynomial Formalism.GradedWeylDivisibility

private theorem cvd_adj {B : Type*} [CommRing B] {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
    (i : Fin (m + 1)) :
    M.adjugate 0 i = (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => M (i.succAbove a) b.succ) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, add_zero, Fin.succAbove_zero]
  rfl

private def cvdM (K : Type) [Field K] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
  fun a b => Fin.cases 0 (fun b' : Fin m => X (a, b'.castSucc)) b

private theorem cvd_covY (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) :
    covY K m i = (cvdM K m).adjugate 0 i := by
  rw [cvd_adj]
  simp only [covY]
  congr 2

theorem signed_minors_cofactor_adjugate : CovL5adj := by
  intro K _ m g i
  have hM : (rowAct K (n := m + 1) g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →+* _).mapMatrix (cvdM K m)
      = g.map C * cvdM K m := by
    ext a b
    refine Fin.cases ?_ (fun b' => ?_) b
    · simp [cvdM, Matrix.mul_apply]
    · simp [cvdM, Matrix.mul_apply, rowAct]
  rw [cvd_covY]
  calc rowAct K g ((cvdM K m).adjugate 0 i)
      = ((rowAct K (n := m + 1) g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →+* _).mapMatrix
          (cvdM K m).adjugate) 0 i := rfl
    _ = (g.map C * cvdM K m).adjugate 0 i := by rw [RingHom.map_adjugate, hM]
    _ = (((cvdM K m).adjugate * (g.map C).adjugate :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) 0 i) := by
        rw [Matrix.adjugate_mul_distrib]
    _ = ∑ j, C (g.adjugate j i) * covY K m j := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← cvd_covY, mul_comm]
      congr 1
      rw [show g.map C = (C : K →+* MvPolynomial (Fin (m + 1) × Fin (m + 1)) K).mapMatrix g from rfl,
        ← RingHom.map_adjugate]
      rfl

theorem signed_minors_cofactor_transform : SignedMinorsCofactorTransform := by
  intro K _ m g i hg
  rw [signed_minors_cofactor_adjugate K m g i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← C_mul, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
    Ring.mul_inverse_cancel _ hg, one_mul]

private def cvdN {F : Type*} [Field F] {k : ℕ} (z : Fin (k + 2) → F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F :=
  fun i j => if i = 0 then z j else if i = j then (if i = 1 then (z 0)⁻¹ else 1) else 0

private theorem cvdN_det {F : Type*} [Field F] {k : ℕ} (z : Fin (k + 2) → F) (h0 : z 0 ≠ 0) :
    (cvdN z).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [cvdN, Fin.succ_ne_zero, Fin.succ_succ_ne_one, h0]
  · intro i j hij
    have h1 : i ≠ 0 := by
      rintro rfl
      exact absurd hij (Fin.not_lt_zero _)
    have h2 : i ≠ j := ne_of_gt hij
    simp [cvdN, h1, h2]

theorem signed_minors_alg_independent : SignedMinorsAlgIndependent := by
  intro K _ m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let L := FractionRing (MvPolynomial (Fin (k + 1 + 1)) K)
  let ι : MvPolynomial (Fin (k + 1 + 1)) K →ₐ[K] L := IsScalarTower.toAlgHom K _ L
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  let z : Fin (k + 1 + 1) → L := fun i => ι (X i)
  have hz : AlgebraicIndependent K z := (MvPolynomial.algebraicIndependent_X _ _ :
    AlgebraicIndependent K (X : Fin (k + 1 + 1) → MvPolynomial (Fin (k + 1 + 1)) K)).map' hι
  have hz0 : z 0 ≠ 0 := (map_ne_zero_iff ι hι).mpr (MvPolynomial.X_ne_zero (R := K) (0 : Fin (k + 1 + 1)))
  let N := cvdN z
  have hN : N.det = 1 := cvdN_det z hz0
  let Q := N⁻¹
  have hQ : Q.adjugate = N := by
    have h1 : N * Q = 1 := Matrix.mul_nonsing_inv N (by rw [hN]; exact isUnit_one)
    have h2 : Q * Q.adjugate = 1 := by
      rw [Matrix.mul_adjugate, Matrix.det_nonsing_inv, hN, Ring.inverse_one, one_smul]
    calc Q.adjugate = (N * Q) * Q.adjugate := by rw [h1, one_mul]
      _ = N := by rw [mul_assoc, h2, mul_one]
  let f : MvPolynomial (Fin (k + 1 + 1) × Fin (k + 1 + 1)) K →ₐ[K] L :=
    aeval fun v => Fin.lastCases 0 (fun b : Fin (k + 1) => Q v.1 b.succ) v.2
  apply AlgebraicIndependent.of_comp f
  convert hz using 1
  funext i
  show f (covY K (k + 1) i) = z i
  have hzi : Q.adjugate 0 i = z i := by
    rw [hQ]
    simp [N, cvdN]
  rw [← hzi, cvd_adj]
  simp only [covY, map_mul, map_pow, map_neg, map_one]
  congr 1
  refine (AlgHom.map_det f (Matrix.of fun a b : Fin (k + 1) =>
    (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (k + 1 + 1) × Fin (k + 1 + 1)) K))).trans ?_
  congr 1
  ext a b
  simp [f]

end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
end
end

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

theorem covY_eq (K : Type) [Field K] (m : ℕ) : ShapeCovering.covY K m = covY K m := rfl

def ExplicitMapInjective : Prop := ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → Function.Injective (PsiXY K m)

def ExplicitMapOntoTwoLetters : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → ∀ (P Q : ℕ) x,
    x ∈ twoSp K m P Q ↔ ∃ f ∈ PolAB K (m + 1) P Q, PsiXY K m f = x

def TwoLetterLatticeGaussInverse : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 1 ≤ m → ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf), IsUnit g.det →
    ∀ g' : GL (Fin (m + 1)) R.Kf, (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) = g⁻¹ →
      ∀ (P Q : ℕ), ∀ f ∈ PolAB R.Kf (m + 1) P Q,
        PsiXY R.Kf m f ∈ twoLat R.O m P Q (colSpan R.O g) ↔ f ∈ latOf g' (GaussLat R.Ov.toSubring)

end Formalism.MainNotions.flipOneThree.Pf

end
