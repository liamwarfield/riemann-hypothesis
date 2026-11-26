module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqMulDiagonal
open IsDedekindDomain NumberField

namespace GlobalTheory.SmithBetween

open Matrix

theorem _root_.GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n R) (hM : M.det ≠ 0) :
    ∃ P Q : Matrix n n R, IsUnit P.det ∧ IsUnit Q.det ∧ ∃ c : n → R,
      M * Q = P * Matrix.diagonal c := by
  have hinj : Function.Injective M.mulVecLin := Matrix.mulVec_injective_of_det_ne_zero hM
  obtain ⟨m, snf⟩ := Submodule.smithNormalForm (Pi.basisFun R n) (LinearMap.range M.mulVecLin)
  have hm : m = Fintype.card n := by
    have h1 := Module.finrank_eq_card_basis snf.bN
    rw [LinearMap.finrank_range_of_inj hinj] at h1
    simpa using h1.symm
  have hf : Function.Bijective snf.f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨snf.f.injective, by simp [hm]⟩
  let g : Fin m ≃ n := Equiv.ofBijective snf.f hf
  let eN := LinearEquiv.ofInjective M.mulVecLin hinj
  let bQ : Module.Basis n R (n → R) := (snf.bN.map eN.symm).reindex g
  letI := (Pi.basisFun R n).invertibleToMatrix snf.bM
  letI := (Pi.basisFun R n).invertibleToMatrix bQ
  refine ⟨(Pi.basisFun R n).toMatrix snf.bM, (Pi.basisFun R n).toMatrix bQ, ?_, ?_,
    fun j => snf.a (g.symm j), ?_⟩
  · exact isUnit_det_of_invertible _
  · exact isUnit_det_of_invertible _
  · ext i j
    have key : M *ᵥ bQ j = snf.a (g.symm j) • snf.bM j := by
      have h2 := snf.snf (g.symm j)
      have h3 : snf.f (g.symm j) = j := g.apply_symm_apply j
      rw [h3] at h2
      rw [← h2]
      simp only [bQ, Module.Basis.reindex_apply, Module.Basis.map_apply]
      have h4 : ((eN (eN.symm (snf.bN (g.symm j)))) : n → R) =
          M.mulVecLin (eN.symm (snf.bN (g.symm j))) := rfl
      rw [LinearEquiv.apply_symm_apply] at h4
      rw [← Matrix.mulVecLin_apply, ← h4]
    have := congrFun key i
    simp only [Matrix.mul_diagonal, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [Matrix.mul_apply]
    simp [Matrix.mulVec, dotProduct] at this
    simpa [mul_comm, Module.Basis.toMatrix_apply] using this

theorem _root_.GlobalTheory.SmithBetween.smith_between (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (M M' : Matrix (Fin n) (Fin n) R)
    (hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R)) (hdet : Associated M.det (ϖ ^ k)) :
    ∃ P Q : Matrix (Fin n) (Fin n) R, IsUnit P.det ∧ IsUnit Q.det ∧
      M * Q = P * Matrix.diagonal (fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ) := by
  classical
  have hM0 : M.det ≠ 0 := by
    rw [hdet.ne_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
  obtain ⟨P, Q, hP, hQ, c, hMQ⟩ := _root_.GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal M hM0
  have hdvd : ∀ j, c j ∣ ϖ := by
    intro j
    have hD : Matrix.diagonal c = P⁻¹ * M * Q := by
      rw [Matrix.mul_assoc, hMQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
    have hX : Matrix.diagonal c * (Q⁻¹ * M' * P) = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
      rw [hD]
      calc P⁻¹ * M * Q * (Q⁻¹ * M' * P) = P⁻¹ * (M * (Q * Q⁻¹) * M') * P := by
            simp only [Matrix.mul_assoc]
        _ = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
            rw [Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, hMM, Matrix.mul_smul, Matrix.mul_one,
              Matrix.smul_mul, Matrix.nonsing_inv_mul _ hP]
    have := congrFun (congrFun hX j) j
    simp only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at this
    exact ⟨_, this.symm⟩
  let d : Fin n → R := fun j => if IsUnit (c j) then 1 else ϖ
  have hu : ∀ j, ∃ u : Rˣ, c j = d j * u := by
    intro j
    by_cases h : IsUnit (c j)
    · exact ⟨h.unit, by simp [d, h]⟩
    · obtain ⟨b, hb⟩ := hdvd j
      rcases hϖ.isUnit_or_isUnit hb with h' | h'
      · exact absurd h' h
      · refine ⟨h'.unit⁻¹, ?_⟩
        simp only [d, h, if_false, hb]
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
  choose u hu using hu

  set s := (Finset.univ.filter fun j => ¬IsUnit (c j)).card with hs
  have hprod : ∏ j, d j = ϖ ^ s := by
    simp only [d]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have hsk : s = k := by
    have h1 : M.det * Q.det = P.det * ∏ j, c j := by
      rw [← Matrix.det_mul, hMQ, Matrix.det_mul, Matrix.det_diagonal]
    have h2 : ∏ j, c j = ϖ ^ s * ∏ j, (u j : R) := by
      rw [← hprod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => hu j
    have h3 : Associated (ϖ ^ s) M.det := by
      have hA : Associated (M.det * Q.det) M.det := (associated_mul_isUnit_left_iff hQ).2 (Associated.refl _)
      have hv : IsUnit (P.det * ∏ j, (u j : R)) :=
        hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)
      have hB : Associated (ϖ ^ s) (P.det * ∏ j, c j) := by
        rw [h2, mul_left_comm]
        exact associated_mul_unit_right _ _ hv
      rw [← h1] at hB
      exact hB.trans hA
    have h4 : Associated (ϖ ^ s) (ϖ ^ k) := h3.trans hdet
    exact le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.dvd)
      ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.symm.dvd)
  let P' := P * Matrix.diagonal fun j => (u j : R)
  have hP' : IsUnit P'.det := by
    simp only [P', Matrix.det_mul, Matrix.det_diagonal]
    exact hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)
  have hMQ' : M * Q = P' * Matrix.diagonal d := by
    rw [hMQ, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext j
    rw [hu j, mul_comm]

  have hcard1 : Fintype.card {j // ¬IsUnit (c j)} = Fintype.card {i : Fin n // ¬i.1 < n - k} := by
    rw [Fintype.card_subtype, ← hs, hsk, Fintype.card_subtype_compl, Fintype.card_subtype,
      Fin.card_filter_val_lt, Fintype.card_fin]
    omega
  have hcard0 : Fintype.card {j // IsUnit (c j)} = Fintype.card {i : Fin n // i.1 < n - k} := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun j => IsUnit (c j))
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt]
    rw [← hs, hsk, Finset.card_univ, Fintype.card_fin] at h
    omega
  let τ : Equiv.Perm (Fin n) :=
    Equiv.subtypeCongr (Fintype.equivOfCardEq hcard0) (Fintype.equivOfCardEq hcard1)
  have hτ : ∀ j, (τ j).1 < n - k ↔ IsUnit (c j) := by
    intro j
    by_cases h : IsUnit (c j)
    · have e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inl ⟨j, h⟩ :=
        Equiv.sumCompl_symm_apply_of_pos (p := fun x => IsUnit (c x)) (a := j) h
      simp only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inl,
        Equiv.sumCompl_apply_inl, h, iff_true]
      exact (Fintype.equivOfCardEq hcard0 ⟨j, h⟩).2
    · have e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inr ⟨j, h⟩ :=
        Equiv.sumCompl_symm_apply_of_neg (p := fun x => IsUnit (c x)) (a := j) h
      simp only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inr,
        Equiv.sumCompl_apply_inr, h, iff_false]
      exact (Fintype.equivOfCardEq hcard1 ⟨j, h⟩).2
  have hsign : ∀ A : Matrix (Fin n) (Fin n) R, IsUnit A.det → IsUnit (A.submatrix id τ.symm).det := by
    intro A hA
    rw [Matrix.det_permute']
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ.symm) with h | h <;> simp [h, hA]
  refine ⟨P'.submatrix id τ.symm, Q.submatrix id τ.symm, hsign P' hP', hsign Q hQ, ?_⟩
  have h1 : M * Q.submatrix id τ.symm = (M * Q).submatrix id τ.symm := by
    ext i j; simp [Matrix.mul_apply]
  rw [h1, hMQ', ← Matrix.submatrix_mul_equiv P' (Matrix.diagonal d) id τ.symm τ.symm,
    Matrix.submatrix_diagonal_equiv]
  congr 2
  funext i
  have := hτ (τ.symm i)
  rw [Equiv.apply_symm_apply] at this
  simp only [Function.comp_apply, d]
  by_cases hi : i.1 < n - k
  · simp [hi, this.1 hi]
  · simp [hi, mt this.2 hi]

end GlobalTheory.SmithBetween
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialClearDenominatorsEval
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialClearDenominatorsEval
namespace GlobalTheory

open MvPolynomial Finset

theorem clearDenominators {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K)
    (P D : ι → MvPolynomial τ K) :
    ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) →
      MvPolynomial.eval y M ≠ 0 ∧
      MvPolynomial.eval y G = MvPolynomial.eval y M *
        MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by
  classical
  set N := F.totalDegree
  refine ⟨∑ m ∈ F.support, C (F.coeff m) * ∏ i ∈ F.vars, (P i) ^ (m i) * (D i) ^ (N - m i),
    ∏ i ∈ F.vars, (D i) ^ N, fun y hy => ⟨?_, ?_⟩⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [map_pow]; exact pow_ne_zero _ (hy i)
  · have hle : ∀ m ∈ F.support, ∀ i, m i ≤ N := fun m hm i =>
      (monomial_le_degreeOf i hm).trans (degreeOf_le_totalDegree F i)
    have hsub : ∀ m ∈ F.support, m.support ⊆ F.vars := fun m hm i hi =>
      (MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨m, hm, hi⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.eval_eq (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F,
      map_prod, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul, eval_C, map_prod]
    rw [Finset.prod_subset (hsub m hm) (fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero])]
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow]
    have hd := hy i
    have hk := hle m hm i
    rw [div_pow, ← pow_sub_mul_pow (MvPolynomial.eval y (D i)) hk]
    field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialClearDenominatorsEvalStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomial_clear_denominators_eval : ∀ {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K) (P D : ι → MvPolynomial τ K), ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) → MvPolynomial.eval y M ≠ 0 ∧ MvPolynomial.eval y G = MvPolynomial.eval y M * MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by
  first | exact @GlobalTheory.clearDenominators | exact GlobalTheory.clearDenominators | (intros; apply GlobalTheory.clearDenominators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm
noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel

variable (n : ℕ)

abbrev Ext : Type := ExteriorAlgebra ℂ (Fin n → ℂ)

abbrev Big : Type := Ext n ⊗[ℂ] Ext n

def vec (a : Fin n) : Ext n := ExteriorAlgebra.ι ℂ (Pi.single a 1 : Fin n → ℂ)

def gen (x : Fin n × Fin n) : Big n := vec n x.1 ⊗ₜ vec n x.2

theorem vec_mul_vec_comm (a b : Fin n) : vec n a * vec n b = -(vec n b * vec n a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem gen_comm : ∀ u ∈ Set.range (gen n), ∀ v ∈ Set.range (gen n), u * v = v * u := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  simp only [gen, Algebra.TensorProduct.tmul_mul_tmul, vec_mul_vec_comm n x.1, vec_mul_vec_comm n x.2,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]

abbrev EvenPart : Subalgebra ℂ (Big n) := Algebra.adjoin ℂ (Set.range (gen n))

open scoped IsMulCommutative in
instance : CommRing (EvenPart n) :=
  have := Algebra.isMulCommutative_adjoin ℂ (s := Set.range (gen n))
    (fun u hu v hv _ => gen_comm n u hu v hv)
  inferInstance

def toEven : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] EvenPart n :=
  aeval fun x => ⟨gen n x, Algebra.subset_adjoin ⟨x, rfl⟩⟩

open Classical in
def topForm (i : ℕ) : (Fin n → ℂ) [⋀^Fin i]→ₗ[ℂ] ℂ :=
  if h : i = n then (Pi.basisFun ℂ (Fin n)).det.domDomCongr (finCongr h.symm) else 0

def topExt : Ext n →ₗ[ℂ] ℂ := ExteriorAlgebra.liftAlternating (topForm n)

def topBig : Big n →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₂ (topExt n) ∘ₗ topExt n)

theorem topBig_tmul (x y : Ext n) : topBig n (x ⊗ₜ y) = topExt n x * topExt n y := rfl

variable {n} {p q : ℕ}

def blockPoly (e : Fin p × Fin q → Fin n) : Matrix (Fin p) (Fin p) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ b, X (e (i, b), e (j, b))

def blockPolyBar (e : Fin p × Fin q → Fin n) : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun b b' => ∑ i, X (e (i, b), e (i, b'))

end GlobalTheory.GrassModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefQuadMargin
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefQuadMargin
namespace GlobalTheory

private lemma quad_smul {ι : Type} [Fintype ι] (M : ι → ι → ℝ) (a : ℝ) (c : ι → ℝ) :
    ∑ i, ∑ j, (a • c) i * (a • c) j * M i j = a ^ 2 * ∑ i, ∑ j, c i * c j * M i j := by
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

private lemma quad_err {ι : Type} [Fintype ι] (E : ι → ι → ℝ) (η : ℝ) (_hη : 0 ≤ η)
    (hE : ∀ i j, |E i j| ≤ η) (c : ι → ℝ) :
    |∑ i, ∑ j, c i * c j * E i j| ≤ (Fintype.card ι : ℝ) ^ 2 * (‖c‖ ^ 2 * η) := by
  have hc : ∀ i, |c i| ≤ ‖c‖ := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm c i
  calc |∑ i, ∑ j, c i * c j * E i j|
      ≤ ∑ i, ∑ j, |c i * c j * E i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, ‖c‖ ^ 2 * η := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul, sq]
        have h1 := hc i; have h2 := hc j; have h3 := hE i j
        have := abs_nonneg (c i); have := abs_nonneg (c j); have := abs_nonneg (E i j)
        have := norm_nonneg c
        calc |c i| * |c j| * |E i j| ≤ ‖c‖ * ‖c‖ * |E i j| := by gcongr
          _ ≤ ‖c‖ * ‖c‖ * η := by gcongr
    _ = (Fintype.card ι : ℝ) ^ 2 * (‖c‖ ^ 2 * η) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem posDef_quad_margin {ι : Type} [Fintype ι] (M : ι → ι → ℝ)
    (hM : ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) :
    ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) →
      ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun E _ c hc => absurd (Subsingleton.elim c 0) hc⟩
  set q : (ι → ℝ) → ℝ := fun c => ∑ i, ∑ j, c i * c j * M i j with hq
  have hcont : Continuous q := by
    simp only [hq]; fun_prop
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    (NormedSpace.sphere_nonempty).mpr zero_le_one
  obtain ⟨c₀, hc₀, hmin⟩ :=
    (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hcont.continuousOn
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl; simp at hc₀
  set μ := q c₀ with hμ
  have hμpos : 0 < μ := hM c₀ hc₀ne
  have hlow : ∀ c : ι → ℝ, c ≠ 0 → μ * ‖c‖ ^ 2 ≤ q c := by
    intro c hc
    have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hmem : ‖c‖⁻¹ • c ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
    have h1 : μ ≤ q (‖c‖⁻¹ • c) := hmin hmem
    have h2 : q (‖c‖⁻¹ • c) = (‖c‖⁻¹) ^ 2 * q c := quad_smul M _ c
    rw [h2] at h1
    have h3 : (‖c‖⁻¹) ^ 2 * ‖c‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow]
    calc μ * ‖c‖ ^ 2 ≤ ((‖c‖⁻¹) ^ 2 * q c) * ‖c‖ ^ 2 := by gcongr
      _ = q c := by rw [mul_comm ((‖c‖⁻¹) ^ 2), mul_assoc, h3, mul_one]
  set K : ℝ := (Fintype.card ι : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  refine ⟨μ / (2 * K + 1), div_pos hμpos (by linarith), ?_⟩
  intro E hE c hc
  have hη0 : 0 ≤ μ / (2 * K + 1) := (div_pos hμpos (by linarith)).le
  have herr := quad_err E _ hη0 hE c
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hsplit : ∑ i, ∑ j, c i * c j * (M i j + E i j)
      = q c + ∑ i, ∑ j, c i * c j * E i j := by
    simp only [hq, mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  have hKη : K * (μ / (2 * K + 1)) < μ := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  have hs2 : 0 < ‖c‖ ^ 2 := by positivity
  have := hlow c hc
  have hlow' := (abs_le.mp herr).1
  rw [← hK] at hlow'
  nlinarith [mul_lt_mul_of_pos_right hKη hs2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefQuadMarginStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_margin_quadForm_pos_of_perturbation : ∀ {ι : Type} [Fintype ι] (M : ι → ι → ℝ), (∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) → ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) → ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := by
  first | exact @GlobalTheory.posDef_quad_margin | exact GlobalTheory.posDef_quad_margin | (intros; apply GlobalTheory.posDef_quad_margin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearDescentToBaseChangeOfForm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearDescentToBaseChangeOfForm
open scoped TensorProduct

namespace GlobalTheory

theorem exists_semilinear_descent_to_baseChange :
  ∀ {LL : Type} [Field LL] [Algebra ℚ LL] (L0 : IntermediateField ℚ LL) {Ks : Type} [Field Ks] [Algebra Ks LL]
    (kKs : Ks →+* L0), (∀ x, ((kKs x : L0) : LL) = algebraMap Ks LL x) →
    ∀ {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL) {n : ℕ} (bs : Fin n → WL), (∀ i, bs i ∈ WK) →
    Submodule.span Ks (Set.range bs) = WK → LinearIndependent LL bs → Submodule.span LL (Set.range bs) = ⊤ →
    ∀ {KT : Type} [Field KT] [Algebra Ks KT] (rd : L0 →+* KT), (∀ s, algebraMap Ks KT s = rd (kKs s)) →
    ∃ Φ : WL →+ KT ⊗[Ks] WK, (∀ (c : L0) (x : WL), Φ ((c : LL) • x) = rd c • Φ x) ∧
      (∀ (f : WL →ₗ[LL] WL) (fr : WK →ₗ[Ks] WK), (∀ w : WK, (fr w : WL) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange KT fr (Φ x)) ∧
      ∀ w : WK, Φ (w : WL) = (1 : KT) ⊗ₜ[Ks] w := by
  intro LL _ _ L0 Ks _ _ kKs hk WL _ _ _ _ WK n bs hb hKs hLi hLs KT _ _ rd hrd
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L0 LL)
    (LinearMap.ker_eq_bot.mpr (algebraMap L0 LL).injective)
  have hπ1 : π 1 = 1 := by
    have := LinearMap.congr_fun hπ 1
    simpa using this
  have hπx : ∀ (c : L0) (y : LL), π ((c : LL) * y) = c * π y := by
    intro c y
    have : ((c : LL) * y) = c • y := (Algebra.smul_def c y).symm
    rw [this, map_smul, smul_eq_mul]
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin n) LL WL, ∀ k, B k = bs k :=
    ⟨Module.Basis.mk hLi (by rw [hLs]), fun k => Module.Basis.mk_apply _ _ k⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : WL →+ KT ⊗[Ks] WK,
      ∀ x, Φ x = ∑ k, rd (π (B.repr x k)) • ((1 : KT) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK)) :=
    ⟨{ toFun := fun x => ∑ k, rd (π (B.repr x k)) • ((1 : KT) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK))
       map_zero' := by simp
       map_add' := by intro x y; simp [map_add (f := _), add_smul, Finset.sum_add_distrib] },
     fun _ => rfl⟩
  have key : ∀ (l : LL) (w : WK), Φ (l • (w : WL)) = rd (π l) • ((1 : KT) ⊗ₜ[Ks] w) := by
    intro l w
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun Ks).mp
      (show (w : WL) ∈ Submodule.span Ks (Set.range bs) by rw [hKs]; exact w.2)
    have hw : w = ∑ k, s k • (⟨bs k, hb k⟩ : WK) := by
      apply Subtype.ext; simp [hs]
    have hrep : ∀ k, B.repr (l • (w : WL)) k = l * algebraMap Ks LL (s k) := by
      have : l • (w : WL) = ∑ k, (l * algebraMap Ks LL (s k)) • B k := by
        rw [← hs, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hB, mul_smul, algebraMap_smul]
      intro k
      rw [this, B.repr_sum_self]
    rw [hΦ]
    conv_rhs => rw [hw, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrep, ← hk, mul_comm, hπx, map_mul, ← hrd, TensorProduct.tmul_smul, ← algebraMap_smul KT (s k),
      smul_smul, mul_comm]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro c x
    rw [hΦ, hΦ x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hπx, map_mul, mul_smul]
  · intro f fr hf x
    conv_lhs => rw [← B.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, hΦ x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hB, ← hf ⟨bs k, hb k⟩, key, map_smul, LinearMap.baseChange_tmul]
  · intro w
    have := key 1 w
    rw [one_smul, hπ1, map_one, one_smul] at this
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearDescentToBaseChangeOfFormStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_descent_to_baseChange_of_form : ∀ {LL : Type} [Field LL] [Algebra ℚ LL] (L0 : IntermediateField ℚ LL) {Ks : Type} [Field Ks] [Algebra Ks LL]
    (kKs : Ks →+* L0), (∀ x, ((kKs x : L0) : LL) = algebraMap Ks LL x) →
    ∀ {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL) {n : ℕ} (bs : Fin n → WL), (∀ i, bs i ∈ WK) →
    Submodule.span Ks (Set.range bs) = WK → LinearIndependent LL bs → Submodule.span LL (Set.range bs) = ⊤ →
    ∀ {KT : Type} [Field KT] [Algebra Ks KT] (rd : L0 →+* KT), (∀ s, algebraMap Ks KT s = rd (kKs s)) →
    ∃ Φ : WL →+ KT ⊗[Ks] WK, (∀ (c : L0) (x : WL), Φ ((c : LL) • x) = rd c • Φ x) ∧
      (∀ (f : WL →ₗ[LL] WL) (fr : WK →ₗ[Ks] WK), (∀ w : WK, (fr w : WL) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange KT fr (Φ x)) ∧
      ∀ w : WK, Φ (w : WL) = (1 : KT) ⊗ₜ[Ks] w := by
  first | exact @GlobalTheory.exists_semilinear_descent_to_baseChange | exact GlobalTheory.exists_semilinear_descent_to_baseChange | (intros; apply GlobalTheory.exists_semilinear_descent_to_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixBasisLatticeUpToDenominatorNotMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixBasisLatticeUpToDenominatorNotMem
set_option autoImplicit false
noncomputable section

open NumberField IsDedekindDomain Matrix Module
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.LatticeLocBasis

theorem exists_basis_up_to_fintype {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A]
    [Algebra A E] [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : Type} [Fintype n] (L : Submodule O (n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (n → E)) = ⊤) :
    ∃ (s : S) (b : n → n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (n → E) := Submodule.span A (L : Set (n → E)) with hM
  have : Submodule.IsFullLattice E M :=
    { toIsLattice := Submodule.IsLattice.of_fg E <| by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = Fintype.card n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq E M).trans (Module.finrank_fintype_fun_eq_card E))
  have := Submodule.IsLattice.free E M
  have := Submodule.IsLattice.finite E M
  let c : Basis n A M := (Module.finBasisOfFinrankEq A M hrk).reindex (Fintype.equivFin n).symm
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis n A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : n → E) = (t i : O) • (c i : n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : n → n → E := fun i => (c' i : n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsFullLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsFullLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

theorem exists_matrix_up_to_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by
  intro K _ _ n _ _ L 𝔭 hfg hsp
  have hp := 𝔭.isPrime
  have hS : 𝔭.asIdeal.primeCompl ≤ (𝓞 K)⁰ := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra K 𝔭.asIdeal.primeCompl hS
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) 𝔭.ne_bot A
  obtain ⟨⟨s, hs⟩, b, hli, hb, hw⟩ := exists_basis_up_to_fintype (A := A) 𝔭.asIdeal.primeCompl L hfg hsp
  let g : Matrix n n K := Matrix.of fun i j => b j i
  have hcol : g.col = b := by funext j i; rfl
  have hunit : IsUnit g := Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  refine ⟨g, hdet, s, hs, ?_, ?_⟩
  · intro x hx i
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw x hx)
    have hg : g *ᵥ (fun i => algebraMap (𝓞 K) K (a i)) = (s : K) • x := by
      have : (s : K) • x = s • x := algebraMap_smul K s x
      rw [this]
      change _ = ((⟨s, hs⟩ : 𝔭.asIdeal.primeCompl) : 𝓞 K) • x
      rw [← ha]
      funext i
      simp only [Matrix.mulVec, dotProduct, g, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have h2 : (s : K) • (g⁻¹ *ᵥ x) = fun i => algebraMap (𝓞 K) K (a i) := by
      rw [← Matrix.mulVec_smul, ← hg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    exact ⟨a i, (congrFun h2 i).symm⟩
  · intro j
    have : (s : K) • (fun i => g i j) = s • b j := algebraMap_smul K s (b j)
    rw [this]
    exact L.smul_mem _ (hb j)

end GlobalTheory.LatticeLocBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixBasisLatticeUpToDenominatorNotMemStatement
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_basis_lattice_up_to_denominator_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by
  first | exact @GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem | exact GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem | (intros; apply GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfValued
open IsDedekindDomain NumberField
namespace GlobalTheory
namespace DegreeOneUniformiser

private theorem adicCompletionIntegers_integers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers F) :=
  ⟨Subtype.val_injective, fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2,
    fun x hx => ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mpr hx⟩, rfl⟩⟩

theorem _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F)
    (h : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) : Irreducible π := by
  have hI := adicCompletionIntegers_integers v
  have hunit : ∀ x : v.adicCompletionIntegers F, IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
    fun x => hI.isUnit_iff_valuation_eq_one
  have hle : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) ≤ 1 :=
    fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := (hunit π).mp hu
    rw [h] at this
    exact absurd this (by decide)
  · have hv : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
        WithZero.exp (-1 : ℤ) := by
      rw [← h, hab, Subring.coe_mul, map_mul]
    have ha0 : Valued.v (a : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hv; exact WithZero.exp_ne_zero hv.symm
    have hb0 : Valued.v (b : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hv; exact WithZero.exp_ne_zero hv.symm
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (a : v.adicCompletion F) = WithZero.exp m :=
      ⟨_, (WithZero.exp_log ha0).symm⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (b : v.adicCompletion F) = WithZero.exp n :=
      ⟨_, (WithZero.exp_log hb0).symm⟩
    have ha := hle a
    have hb := hle b
    rw [hm, hn, ← WithZero.exp_add, WithZero.exp_inj] at hv
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha
    rw [hn, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb
    rw [hunit, hunit, hm, hn, ← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
    omega

theorem _root_.GlobalTheory.DegreeOneUniformiser.exists_irreducible_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (ψ : E →+* v.adicCompletion F), (∀ a : F, ψ (algebraMap F E a) = algebraMap F (v.adicCompletion F) a) → (∀ x : 𝓞 E, ψ (x : E) ∈ v.adicCompletionIntegers F) → (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ψ ((x : E)⁻¹) ∉ v.adicCompletionIntegers F)) → ∀ ϖ : 𝓞 E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ π : v.adicCompletionIntegers F, Irreducible π ∧ (π : v.adicCompletion F) = ψ (ϖ : E) := by
  intro F E _ _ _ _ _ v P ψ hψ hint hP ϖ hϖP hϖP2
  have hle : ∀ x : 𝓞 E, Valued.v (ψ (x : E)) ≤ 1 := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hint x)
  have hne : ∀ x : 𝓞 E, x ≠ 0 → Valued.v (ψ (x : E)) ≠ 0 := by
    intro x hx
    rw [Valuation.ne_zero_iff, map_ne_zero_iff _ ψ.injective]
    exact_mod_cast hx
  have hone : ∀ x : 𝓞 E, x ∉ P.asIdeal → Valued.v (ψ (x : E)) = 1 := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => hx (h ▸ P.asIdeal.zero_mem)
    have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp
      (not_not.mp (mt (hP x hx0).mpr hx))
    rw [map_inv₀, map_inv₀] at h1
    exact le_antisymm (hle x) ((inv_le_one₀ (zero_lt_iff.mpr (hne x hx0))).mp h1)
  have hϖ0 : ϖ ≠ 0 := fun h => hϖP2 (h ▸ Ideal.zero_mem _)
  have hlt : Valued.v (ψ (ϖ : E)) < 1 := by
    have h1 := (hP ϖ hϖ0).mp hϖP
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le, map_inv₀, map_inv₀] at h1
    exact (one_lt_inv₀ (zero_lt_iff.mpr (hne ϖ hϖ0))).mp h1
  obtain ⟨u, hu⟩ := v.intValuation_exists_uniformizer
  let f : 𝓞 E := ⟨algebraMap F E (u : F), (RingOfIntegers.isIntegral_coe u).algebraMap⟩
  have hf : Valued.v (ψ (f : E)) = WithZero.exp (-1 : ℤ) := by
    show Valued.v (ψ (algebraMap F E (u : F))) = _
    rw [hψ, ← hu, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (u : F)
  have hf0 : f ≠ 0 := fun h => by
    rw [h] at hf
    simp only [ZeroMemClass.coe_zero, map_zero] at hf
    exact WithZero.exp_ne_zero hf.symm
  have hfP : f ∈ P.asIdeal := by
    rw [hP f hf0, HeightOneSpectrum.mem_adicCompletionIntegers, not_le, map_inv₀, map_inv₀, hf,
      ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem _).mpr hϖP : Ideal.span {ϖ} ≤ P.asIdeal)
  have hJP : ¬ J ≤ P.asIdeal := fun hJP => hϖP2 (by
    have hmem : ϖ ∈ Ideal.span {ϖ} := Ideal.mem_span_singleton_self ϖ
    rw [hJ] at hmem
    rw [pow_two]
    exact Ideal.mul_mono_right hJP hmem)
  obtain ⟨t, htJ, htP⟩ := Set.not_subset.mp hJP
  have hft : f * t ∈ Ideal.span {ϖ} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hfP htJ
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hft
  have hval := congrArg (fun x : 𝓞 E => Valued.v (ψ (x : E))) hs
  simp only [MulMemClass.coe_mul, map_mul] at hval
  rw [hone t htP, mul_one, hf] at hval
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v (ψ (ϖ : E)) := by
    rw [← hval]
    calc Valued.v (ψ (s : E)) * Valued.v (ψ (ϖ : E)) ≤ 1 * Valued.v (ψ (ϖ : E)) :=
          mul_le_mul' (hle s) le_rfl
      _ = Valued.v (ψ (ϖ : E)) := one_mul _
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (ψ (ϖ : E)) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log (hne ϖ hϖ0)).symm⟩
  rw [hm, WithZero.exp_le_exp] at hge
  rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  have hm1 : m = -1 := by omega
  refine ⟨⟨ψ (ϖ : E), hint ϖ⟩, _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued v _ ?_, rfl⟩
  rw [← hm1]
  exact hm

end DegreeOneUniformiser
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDomainOfIsIntegrallyClosedOfIsReduced
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDomainOfIsIntegrallyClosedOfIsReduced
open IsLocalRing

namespace GlobalTheory

theorem eq_zero_of_mem_minimalPrimes {R : Type} [CommRing R] [IsReduced R] {y : R}
    (hy : ∀ P ∈ minimalPrimes R, y ∈ P) : y = 0 := by
  have : y ∈ nilradical R := by
    rw [nilradical_eq_sInf, Submodule.mem_sInf]
    intro J hJ
    haveI : Ideal.IsPrime J := hJ
    obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := J) bot_le
    exact hpJ (hy p hp)
  rw [nilradical_eq_zero] at this
  simpa using this

theorem isDomain_of_isIntegrallyClosed_of_isReduced :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R],
      IsIntegrallyClosed R → IsDomain R := by
  intro R _ _ _ _ hic
  classical
  suffices hbot : (⊥ : Ideal R).IsPrime by
    haveI : NoZeroDivisors R := ⟨fun {x y} h => by
      have : x * y ∈ (⊥ : Ideal R) := by simp [h]
      simpa using hbot.mem_or_mem this⟩
    exact NoZeroDivisors.to_isDomain R
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  obtain ⟨P, hP⟩ : ∃ P, P ∈ minimalPrimes R := by
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R))
      (J := IsLocalRing.maximalIdeal R) bot_le
    exact ⟨p, hp⟩
  have hPprime : P.IsPrime := hP.1.1
  have minle : ∀ {A B : Ideal R}, A ∈ minimalPrimes R → B ∈ minimalPrimes R → A ≤ B → A = B :=
    fun {A B} hA hB hAB => le_antisymm hAB (hB.2 hA.1 hAB)
  set T : Finset (Ideal R) := hfin.toFinset with hT
  have memT : ∀ Q, Q ∈ T ↔ Q ∈ minimalPrimes R := fun Q => by simp [T]
  set Q : Ideal R := (T.erase P).inf id with hQ
  have hQle : ∀ P' ∈ T.erase P, Q ≤ P' := fun P' h => Finset.inf_le (f := id) h
  by_cases hone : T.erase P = ∅
  ·
    have hPbot : P = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y = 0 := eq_zero_of_mem_minimalPrimes (fun P' hP' => by
        by_cases h : P' = P
        · exact h ▸ hy
        · have : P' ∈ T.erase P := Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩
          simp [hone] at this)
      simp [this]
    exact hPbot ▸ hPprime
  exfalso
  obtain ⟨P₂, hP₂⟩ := Finset.nonempty_iff_ne_empty.2 hone

  have hnot : ¬ ((P ⊔ Q : Ideal R) : Set R) ⊆ ⋃ i ∈ (↑T : Set (Ideal R)), (i : Set R) := by
    intro hsub
    obtain ⟨P', hP'T, hle⟩ := (Ideal.subset_union_prime (f := id) P P
      (fun i hi _ _ => ((memT i).1 hi).1.1)).1 hsub
    have hle' : P ⊔ Q ≤ P' := hle
    have h1 : P = P' := minle hP ((memT P').1 hP'T) (le_sup_left.trans hle')
    have hQP : Q ≤ P := by
      have h2 : Q ≤ P' := le_sup_right.trans hle'
      rw [← h1] at h2
      exact h2
    obtain ⟨P'', hP''e, hP''le⟩ := (Ideal.IsPrime.inf_le' (s := T.erase P) (f := id) hPprime).1 hQP
    have : P'' = P := minle ((memT P'').1 (Finset.mem_of_mem_erase hP''e)) hP hP''le
    exact Finset.ne_of_mem_erase hP''e this
  obtain ⟨s, hsPQ, hsout⟩ := Set.not_subset.1 hnot
  have hsnot : ∀ P' ∈ minimalPrimes R, s ∉ P' := fun P' hP' hs =>
    hsout (Set.mem_biUnion (x := P') (by simpa [memT] using hP') hs)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hsPQ
  have hsnzd : ∀ y : R, y * s = 0 → y = 0 := fun y hy =>
    eq_zero_of_mem_minimalPrimes (fun P' hP' => by
      have : y * s ∈ P' := by simp [hy]
      exact (hP'.1.1.mem_or_mem this).resolve_right (hsnot P' hP'))
  have hab0 : a * b = 0 := eq_zero_of_mem_minimalPrimes (fun P' hP' => by
    by_cases h : P' = P
    · exact h ▸ P.mul_mem_right b ha
    · exact P'.mul_mem_left a (hQle P' (Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩) hb))
  have hs : s ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_right.2 hsnzd
  let K := FractionRing R
  set e : K := IsLocalization.mk' K a ⟨s, hs⟩ with he_def
  have hspec : e * algebraMap R K s = algebraMap R K a := IsLocalization.mk'_spec K a ⟨s, hs⟩
  have ht : IsUnit (algebraMap R K s) := IsLocalization.map_units K (⟨s, hs⟩ : nonZeroDivisors R)
  have has : a * s = a * a := by rw [← hab, mul_add, hab0, add_zero]
  have hee : e * e = e := by
    refine (ht.mul ht).mul_left_inj.1 ?_
    calc e * e * (algebraMap R K s * algebraMap R K s)
        = (e * algebraMap R K s) * (e * algebraMap R K s) := by ring
      _ = algebraMap R K (a * a) := by rw [hspec, map_mul]
      _ = algebraMap R K (a * s) := by rw [has]
      _ = (e * algebraMap R K s) * algebraMap R K s := by rw [hspec, map_mul]
      _ = e * (algebraMap R K s * algebraMap R K s) := by ring
  have hint : IsIntegral R e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
    · simp [Polynomial.eval₂_sub, sq, hee]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hinj := IsFractionRing.injective R K
  have hrr : r * r = r := hinj (by rw [map_mul, hr, hee])
  have hrs : r * s = a := hinj (by rw [map_mul, hr, hspec])
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with hu | hu
  · have hr1 : r = 1 := hu.mul_left_cancel (by rw [hrr, mul_one])
    rw [hr1, one_mul] at hrs

    exact hsnot P hP (hrs ▸ ha)
  · have hr0 : r = 0 := by
      have : (1 - r) * r = 0 := by rw [sub_mul, one_mul, hrr, sub_self]
      exact (hu.mul_right_eq_zero).1 this
    rw [hr0, zero_mul] at hrs

    have hsb : s = b := by rw [← hab, ← hrs, zero_add]
    exact hsnot P₂ ((memT P₂).1 (Finset.mem_of_mem_erase hP₂)) (hsb ▸ hQle P₂ hP₂ hb)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDomainOfIsIntegrallyClosedOfIsReducedStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R], IsIntegrallyClosed R → IsDomain R := by
  first | exact @GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced | exact GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced | (intros; apply GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced <;> assumption)
end
end
