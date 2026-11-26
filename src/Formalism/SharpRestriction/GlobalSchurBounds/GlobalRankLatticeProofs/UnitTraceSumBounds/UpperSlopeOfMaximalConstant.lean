module

public import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaOperatorBasis
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HookBound

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StdSlopeLow
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaGram
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.StdSlopeLowOf
noncomputable section

namespace PI.SlopeSteps

open MvPolynomial Formalism.GradedWeylDivisibility

theorem hwNormPos {N : ℕ} (ν : Fin N → ℕ) : 0 < fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) :=
  (fockQPos _ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)).2 (hwNe ℚ N N le_rfl ν)

theorem natPowPos (N k : ℕ) (hk : N = 0 → k = 0) : (0 : ℚ) < (N : ℚ) ^ k := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · rw [hk h0, pow_zero]; exact one_pos
  · exact pow_pos (by exact_mod_cast h0) k

theorem sumNuZero {N : ℕ} (ν : Fin N → ℕ) : N = 0 → ∑ s, ν s = 0 := by
  rintro rfl
  simp

theorem stdSlopeLow_of (hT2 : NablaGramLow) (hT3 : GramDual) (hT4 : NablaBasis) : PI.StdSlopeLow := by
  intro N ν μ hν ⟨r, e, hr, hμ⟩
  obtain ⟨r', ⟨e'⟩⟩ := hT4 N ν
  obtain ⟨hrr, hdet⟩ := hT3 N ν r r' e e' hν
  subst hrr
  have hlow := hT2 N ν r e' hν
  have hpos := hwNormPos ν
  have hNpow := natPowPos N (∑ s, ν s) (sumNuZero ν)
  have hPpos : (0 : ℚ) < ((∏ s, (ν s).factorial : ℕ) : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _)
  set h := fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) with hh
  set A : ℚ := ((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * h) with hAdef
  have hA : 0 < A := div_pos hPpos (mul_pos hNpow hpos)
  set D := (gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det with hDdef
  set D' := (gramOf ν fun i => (e' i : MvPolynomial (Fin N × Fin N) ℤ)).det with hD'def
  have hD'pos : 0 < D' := lt_of_lt_of_le (pow_pos hA r) hlow
  have hDeq : D = D'⁻¹ := eq_inv_of_mul_eq_one_left hdet
  have hDle : D ≤ (A ^ r)⁻¹ := by rw [hDeq]; exact inv_anti₀ (pow_pos hA r) hlow
  have hDpos : 0 < D := by rw [hDeq]; exact inv_pos.mpr hD'pos
  have hstd : (PI.stdGram ν e).det = D := rfl
  rw [hμ, hstd]
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hDler : (D : ℝ) ≤ ((A : ℝ) ^ r)⁻¹ := by exact_mod_cast hDle
  have hlog : Real.log (D : ℝ) ≤ -((r : ℝ) * Real.log (A : ℝ)) := by
    calc Real.log (D : ℝ) ≤ Real.log (((A : ℝ) ^ r)⁻¹) := Real.log_le_log hDr hDler
      _ = -((r : ℝ) * Real.log (A : ℝ)) := by rw [Real.log_inv, Real.log_pow]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogA : Real.log (A : ℝ) = -((∑ l, (ν l : ℝ)) * Real.log N + Real.log (cNu ν)) := by
    have hP : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
      Finset.prod_pos fun l _ => by exact_mod_cast Nat.factorial_pos _
    have hNr : (0 : ℝ) < (N : ℝ) ^ (∑ s, ν s) := by exact_mod_cast hNpow
    have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hpos
    have hAeq : (A : ℝ) = (∏ l, ((ν l).factorial : ℝ)) / ((N : ℝ) ^ (∑ s, ν s) * (h : ℝ)) := by
      rw [hAdef]; push_cast; ring
    have hc : cNu ν = (h : ℝ) / ∏ l, ((ν l).factorial : ℝ) := rfl
    rw [hAeq, hc, Real.log_div hP.ne' (mul_pos hNr hhr).ne', Real.log_mul hNr.ne' hhr.ne',
      Real.log_div hhr.ne' hP.ne', Real.log_pow]
    push_cast
    ring
  rw [← hlogA, le_div_iff₀ hrpos]
  nlinarith

end PI.SlopeSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.MonomialFactorizationLower
namespace PI.SlopeSteps

open Finset

theorem multinomial_le_pow {N : ℕ} (f : Fin N → ℕ) : Nat.multinomial univ f ≤ N ^ (∑ a, f a) := by
  have h := Finset.sum_pow_eq_sum_piAntidiag (R := ℕ) (univ : Finset (Fin N)) (fun _ => (1 : ℕ)) (∑ a, f a)
  simp only [one_pow, prod_const_one, mul_one, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  rw [h]
  exact Finset.single_le_sum (f := fun k => Nat.multinomial univ k) (fun _ _ => Nat.zero_le _)
    (mem_piAntidiag.mpr ⟨rfl, fun i _ => mem_univ i⟩)

theorem col_fact_le {N : ℕ} (f : Fin N → ℕ) :
    (∑ a, f a).factorial ≤ N ^ (∑ a, f a) * ∏ a, (f a).factorial := by
  rw [← Nat.multinomial_spec univ f, mul_comm]
  exact Nat.mul_le_mul_right _ (multinomial_le_pow f)

theorem monomial_factorization_lower : MonoFactLow := by
  intro N ν m hm
  classical
  have h1 : ∏ k ∈ m.support, (m k).factorial = ∏ s : Fin N, ∏ a : Fin N, (m (a, s)).factorial := by
    rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
      rw [Finsupp.mem_support_iff, not_not] at hk
      rw [hk, Nat.factorial_zero])]
    rw [Fintype.prod_prod_type, Finset.prod_comm]
  rw [h1, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun s _ => ?_
  have := col_fact_le (fun a => m (a, s))
  rwa [hm s] at this

end PI.SlopeSteps
end

noncomputable section

namespace PI.SlopeSteps

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV Matrix

theorem det_mul_rect' {R : Type*} [CommRing R] {k : ℕ} {n : Type*} [Fintype n]
    (A : Matrix (Fin k) n R) (B : Matrix n (Fin k) R) :
    (A * B).det = ∑ f : Fin k → n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [det_apply, Matrix.mul_apply, Fintype.prod_sum, Finset.smul_sum, submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul, Finset.prod_mul_distrib]
  ring

theorem sum_comp_perm' {M : Type*} [AddCommMonoid M] {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (F : (Fin k → n) → M) (τ : Equiv.Perm (Fin k)) : ∑ f : Fin k → n, F (fun i => f (τ i)) = ∑ f, F f :=
  Equiv.sum_comp (Equiv.arrowCongr τ.symm (Equiv.refl n)) F

theorem factorial_mul_det_gram_cauchy_binet {R : Type*} [CommRing R] (k : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (q : n → R) (V : Matrix n (Fin k) R) :
    (k.factorial : R) * (Vᵀ * diagonal q * V).det =
      ∑ f : Fin k → n, (∏ i, q (f i)) * ((V.submatrix f id).det * (Vᵀ.submatrix id f).det) := by
  have hexp : (Vᵀ * diagonal q * V).det = ∑ f : Fin k → n, (∏ i, q (f i)) *
      ((∏ i, V (f i) i) * (Vᵀ.submatrix id f).det) := by
    rw [Matrix.mul_assoc, det_mul_rect']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [diagonal_mul, Finset.prod_mul_distrib, mul_assoc]
  have hk : (k.factorial : R) = ∑ _τ : Equiv.Perm (Fin k), (1 : R) := by
    simp [Fintype.card_perm]
  have step : ∀ τ : Equiv.Perm (Fin k),
      (1 : R) * ∑ f : Fin k → n, (∏ i, q (f i)) * ((∏ i, V (f i) i) * (Vᵀ.submatrix id f).det)
        = ∑ f : Fin k → n, (∏ i, q (f i)) *
            ((∏ i, V (f (τ i)) i) * ((Vᵀ.submatrix id f).submatrix id τ).det) := by
    intro τ
    rw [one_mul, ← sum_comp_perm' _ τ]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Equiv.prod_comp τ (fun i => q (f i))]
    rfl
  rw [hexp, hk, Finset.sum_mul, Finset.sum_congr rfl fun τ _ => step τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [det_apply (V.submatrix f id), Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [det_permute']
  simp only [submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
  ring

theorem factorial_mul_det_sq {R : Type*} [CommRing R] (k : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (q : n → R) (V : Matrix n (Fin k) R) :
    (k.factorial : R) * (Vᵀ * diagonal q * V).det =
      ∑ f : Fin k → n, (∏ i, q (f i)) * ((V.submatrix f id).det * (V.submatrix f id).det) := by
  rw [factorial_mul_det_gram_cauchy_binet]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← transpose_submatrix, det_transpose]

theorem fockQ_eq_sum {σ : Type} (P Q : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    fockQ P Q = ∑ m ∈ S, P.coeff m * Q.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm]
  ring

theorem nabla_gram_lower_bound : NablaGramLow := by
  intro N ν r e hν
  classical
  have hpos := hwNormPos ν
  set h := fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) with hh
  have hNpow := natPowPos N (∑ s, ν s) (sumNuZero ν)
  set A : ℚ := ((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * h) with hA
  have hA0 : 0 ≤ A := div_nonneg (Nat.cast_nonneg _) (mul_pos hNpow hpos).le
  set S : Finset (Fin N × Fin N →₀ ℕ) :=
    Finset.univ.biUnion fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ).support with hS
  set Vz : Matrix S (Fin r) ℤ := Matrix.of fun m i => (e i : MvPolynomial (Fin N × Fin N) ℤ).coeff m.1 with hVz
  set V : Matrix S (Fin r) ℚ := Vz.map (Int.castRingHom ℚ) with hV
  set q : S → ℚ := fun m => ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) / h with hq

  have hG : gramOf ν (fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)) = Vᵀ * diagonal q * V := by
    ext i j
    have hsub : (map (Int.castRingHom ℚ) (e i : MvPolynomial (Fin N × Fin N) ℤ)).support ⊆ S :=
      (MvPolynomial.support_map_subset _ _).trans (by
        rw [hS]
        exact Finset.subset_biUnion_of_mem (fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ).support)
          (Finset.mem_univ i))
    simp only [gramOf, Matrix.of_apply]
    rw [fockQ_eq_sum _ _ S hsub, Finset.sum_div, ← Finset.sum_coe_sort S]
    rw [Matrix.mul_apply]
    simp only [mul_diagonal, transpose_apply, hV, hVz, map_apply, of_apply, hq, coeff_map, eq_intCast]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hh]
    ring

  have hqA : ∀ m : S, A ≤ q m := by
    intro m
    obtain ⟨i, -, hm⟩ := Finset.mem_biUnion.mp m.2
    have hcol := colSums ℤ N N ν _ (e i).2 m.1 hm
    have hT1 := monomial_factorization_lower N ν m.1 hcol
    have hT1q : ((∏ s, (ν s).factorial : ℕ) : ℚ) ≤
        (N : ℚ) ^ (∑ s, ν s) * ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) := by
      exact_mod_cast hT1
    rw [hA, hq]
    rw [div_le_div_iff₀ (mul_pos hNpow hpos) hpos]
    calc ((∏ s, (ν s).factorial : ℕ) : ℚ) * h
        ≤ (N : ℚ) ^ (∑ s, ν s) * ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) * h :=
          mul_le_mul_of_nonneg_right hT1q hpos.le
      _ = ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) * ((N : ℚ) ^ (∑ s, ν s) * h) := by ring

  have hid1 := factorial_mul_det_sq r (fun _ => (1 : ℚ)) V
  rw [diagonal_one, Matrix.mul_one] at hid1
  simp only [Finset.prod_const_one, one_mul] at hid1
  have hfac : (0 : ℚ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hVVnn : 0 ≤ (Vᵀ * V).det := by
    have h0 : 0 ≤ (r.factorial : ℚ) * (Vᵀ * V).det := by
      rw [hid1]; exact Finset.sum_nonneg fun f _ => mul_self_nonneg _
    exact nonneg_of_mul_nonneg_right (by linarith) hfac
  have hind := linIndep_Q e
  have hVVne : (Vᵀ * V).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have h1 : dotProduct (V *ᵥ v) (V *ᵥ v) = 0 := by
      have h1' := congrArg (fun x => dotProduct v x) hv
      simp only [dotProduct_zero] at h1'
      rwa [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at h1'
    have h2 : V *ᵥ v = 0 := by
      funext m
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => mul_self_nonneg ((V *ᵥ v) m))).mp h1 m
        (Finset.mem_univ _)
      exact mul_self_eq_zero.mp h3
    have h3 : ∑ i, v i • intQ N N (e i : MvPolynomial (Fin N × Fin N) ℤ) = 0 := by
      ext m
      rw [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      simp only [MvPolynomial.coeff_smul, smul_eq_mul, we_intQ_apply, MvPolynomial.coeff_map, eq_intCast]
      by_cases hm : m ∈ S
      · have h4 := congrFun h2 ⟨m, hm⟩
        simp only [mulVec, dotProduct, hV, hVz, map_apply, of_apply, Pi.zero_apply, eq_intCast] at h4
        rw [← h4]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      · refine Finset.sum_eq_zero fun i _ => ?_
        have h5 : (e i : MvPolynomial (Fin N × Fin N) ℤ).coeff m = 0 := by
          by_contra hc
          exact hm (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, MvPolynomial.mem_support_iff.mpr hc⟩)
        rw [h5, Int.cast_zero, mul_zero]
    exact hv0 (funext (Fintype.linearIndependent_iff.mp hind v h3))
  have hVVint : (Vᵀ * V).det = (((Vzᵀ * Vz).det : ℤ) : ℚ) := by
    have h6 := RingHom.map_det (Int.castRingHom ℚ) (Vzᵀ * Vz)
    rw [eq_intCast] at h6
    rw [h6, RingHom.mapMatrix_apply, Matrix.map_mul, transpose_map]
  have hVV1 : 1 ≤ (Vᵀ * V).det := by
    rw [hVVint] at hVVnn hVVne ⊢
    have hz : 0 < (Vzᵀ * Vz).det := by
      have := lt_of_le_of_ne hVVnn (Ne.symm hVVne)
      exact_mod_cast this
    exact_mod_cast hz

  have hid := factorial_mul_det_sq r q V
  have hprod : ∀ f : Fin r → S, A ^ r ≤ ∏ i, q (f i) := by
    intro f
    calc A ^ r = ∏ _i : Fin r, A := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i, q (f i) := Finset.prod_le_prod₀ (fun _ _ => hA0) (fun i _ => hqA (f i))
  have hmain : A ^ r * ((r.factorial : ℚ) * (Vᵀ * V).det) ≤
      (r.factorial : ℚ) * (Vᵀ * diagonal q * V).det := by
    rw [hid1, hid, Finset.mul_sum]
    exact Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hprod f) (mul_self_nonneg _)
  rw [hG]
  have hAr : 0 ≤ A ^ r := pow_nonneg hA0 r
  nlinarith [mul_le_mul_of_nonneg_left hVV1 (mul_nonneg hAr hfac.le)]

end PI.SlopeSteps
end
end

theorem standard_slope_lower : PI.StdSlopeLow :=
  PI.SlopeSteps.stdSlopeLow_of PI.SlopeSteps.nabla_gram_lower_bound PI.SlopeSteps.gram_matrix_duality
    PI.SlopeSteps.nabla_operator_basis
end

namespace Formalism.MainNotions.flipTwoThree

theorem hookBound_holds : HookBound := hook_length_bound

end Formalism.MainNotions.flipTwoThree
