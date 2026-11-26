module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolyConjSelfReciprocalCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolyConjSelfReciprocalCoeff
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjSelfRecip

theorem ell_coeff_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    P.coeff 0 ≠ 0 ∧ ∀ k ≤ n, P.coeff 0 * IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) := by
  intro E _ _ _ n P hP
  have hdeg : P.natDegree = n := hP.2.1
  obtain ⟨h0, hid⟩ := ell_conj_selfRecip E n P hP
  refine ⟨h0, fun k hk => ?_⟩
  have hc := congrArg (fun Q : E[X] => Q.coeff k) hid
  simp only [coeff_C_mul, coeff_reverse] at hc
  have hnd : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n := by
    rw [natDegree_map_eq_of_injective (IsCMField.complexConj E).toRingEquiv.toRingHom.injective, hdeg]
  rw [hnd, revAt_le hk, coeff_map] at hc
  have hc2 := congrArg (IsCMField.complexConj E) hc
  simpa [map_mul] using hc2

end GlobalTheory.ConjSelfRecip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolyConjSelfReciprocalCoeffStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_poly_conj_selfReciprocal_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → P.coeff 0 ≠ 0 ∧ ∀ k ≤ n, P.coeff 0 * IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) := by
  first | exact @GlobalTheory.ConjSelfRecip.ell_coeff_conj | exact GlobalTheory.ConjSelfRecip.ell_coeff_conj | (intros; apply GlobalTheory.ConjSelfRecip.ell_coeff_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationEqOrConjOfUnderMaximalRealSubfieldEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationEqOrConjOfUnderMaximalRealSubfieldEq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.BCT

theorem valuation_eq_or_eq_conj_of_under_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∀ y : E, w.valuation E y = u.valuation E y) ∨ (∀ y : E, w.valuation E y = u.valuation E (IsCMField.complexConj E y)) := by
  intro E _ _ _ w u h
  set σ : E ≃+* E := (IsCMField.complexConj E).toRingEquiv with hσ
  set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ with he
  have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = IsCMField.complexConj E (x : E) := fun x => rfl
  have hmem : ∀ x ∈ w.asIdeal, x ∈ u.asIdeal ∨ e x ∈ u.asIdeal := by
    intro x hx
    have hfix : IsCMField.complexConj E (((x * e x : 𝓞 E)) : E) = ((x * e x : 𝓞 E) : E) := by
      have h1 : ((x * e x : 𝓞 E) : E) = (x : E) * IsCMField.complexConj E (x : E) := by
        rw [← hc]; rfl
      rw [h1, map_mul, IsCMField.complexConj_apply_apply, mul_comm]
    have hF : ((x * e x : 𝓞 E) : E) ∈ maximalRealSubfield E :=
      (IsCMField.complexConj_eq_self_iff E _).1 hfix
    have hint : IsIntegral ℤ (⟨_, hF⟩ : maximalRealSubfield E) := by
      have := (x * e x).isIntegral_coe
      exact (isIntegral_algebraMap_iff ).1 this
    have hz : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) ⟨_, hint⟩ = x * e x :=
      RingOfIntegers.ext rfl
    have h1 : (⟨_, hint⟩ : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ w.asIdeal
      rw [hz]
      exact Ideal.mul_mem_right _ _ hx
    rw [← h] at h1
    change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ u.asIdeal at h1
    rw [hz] at h1
    exact u.isPrime.mem_or_mem h1
  have hsub : (w.asIdeal : Set (𝓞 E)) ⊆ (u.asIdeal : Set (𝓞 E)) ∪
      (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal := fun x hx => hmem x hx
  rcases Ideal.subset_union.1 hsub with h2 | h2
  · left
    have : w = u := HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h2)
    subst this
    intro y; rfl
  · right
    intro y
    exact GlobalTheory.QNorm.valuation_of_eq_comap σ u w
      (w.isMaximal.eq_of_le (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).isPrime.ne_top h2) y

end GlobalTheory.BCT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationEqOrConjOfUnderMaximalRealSubfieldEqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_eq_or_conj_of_under_maximalRealSubfield_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∀ y : E, w.valuation E y = u.valuation E y) ∨ (∀ y : E, w.valuation E y = u.valuation E (IsCMField.complexConj E y)) := by
  first | exact @GlobalTheory.BCT.valuation_eq_or_eq_conj_of_under_eq | exact GlobalTheory.BCT.valuation_eq_or_eq_conj_of_under_eq | (intros; apply GlobalTheory.BCT.valuation_eq_or_eq_conj_of_under_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffsValuedBoundedOnCompactGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffsValuedBoundedOnCompactGL
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CharpolyBound

theorem continuous_coeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  refine (MvPolynomial.continuous_eval _).comp ?_
  exact continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1)

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_vle (w : Pl E) (m : ℤ) : IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound {X : Type} [TopologicalSpace X] (w : Pl E) {f : X → w.adicCompletion E} (hf : Continuous f)
    {C : Set X} (hC : IsCompact C) : ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ C, Valued.v (f x) ≤ B := by
  have hcov : C ⊆ ⋃ m : ℤ, f ⁻¹' {y | Valued.v y ≤ WithZero.exp m} := by
    intro x _
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
    rcases eq_or_ne (Valued.v (f x)) 0 with h | h
    · exact ⟨0, by rw [h]; exact zero_le'⟩
    · exact ⟨WithZero.log (Valued.v (f x)), (WithZero.exp_log h).ge⟩
  have hmono : Monotone fun m : ℤ => f ⁻¹' {y | Valued.v y ≤ WithZero.exp m} := by
    intro a b hab x hx
    exact le_trans hx (WithZero.exp_le_exp.2 hab)
  obtain ⟨m, hm⟩ := hC.elim_directed_cover _ (fun m => (isOpen_vle w m).preimage hf) hcov hmono.directed_le
  exact ⟨WithZero.exp m, fun x hx => hm hx⟩

end GlobalTheory.CharpolyBound

open GlobalTheory.CharpolyBound in
theorem GlobalTheory.CharpolyBound.bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (C : Set (GLw n w)), IsCompact C → ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ B) ∧ Valued.v ((g.val.charpoly.coeff 0)⁻¹) ≤ B := by
  intro E _ _ _ n w C hC
  have hval : Continuous fun g : GLw n w => g.val := Units.continuous_val
  have hinv : Continuous fun g : GLw n w => ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    Units.continuous_coe_inv
  have hk : ∀ k : ℕ, ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, Valued.v (g.val.charpoly.coeff k) ≤ B :=
    fun k => exists_bound w ((continuous_coeff n k).comp hval) hC
  choose Bk hBk using hk
  obtain ⟨Bi, hBi⟩ := exists_bound w (hinv.matrix_det) hC
  refine ⟨(Finset.range (n + 1)).sup Bk ⊔ Bi, fun g hg => ⟨fun k => ?_, ?_⟩⟩
  · by_cases hkn : k ≤ n
    · exact le_sup_of_le_left ((hBk k g hg).trans (Finset.le_sup (f := Bk) (Finset.mem_range.2 (by omega))))
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; omega), map_zero]
      exact zero_le'
  · have h0 : g.val.charpoly.coeff 0 = (-1) ^ n * g.val.det := by
      rw [det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    have hdet : g.val.det * ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det = 1 := by
      rw [← det_mul, Units.mul_inv, det_one]
    have hc : (g.val.charpoly.coeff 0)⁻¹ =
        (-1) ^ n * ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det := by
      rw [h0, mul_inv, inv_eq_of_mul_eq_one_right hdet, ← inv_pow, inv_neg_one]
    rw [hc, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    exact le_sup_of_le_right (hBi g hg)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffsValuedBoundedOnCompactGLStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_coeffs_valued_bounded_on_compact_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (C : Set (GLw n w)), IsCompact C → ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ B) ∧ Valued.v ((g.val.charpoly.coeff 0)⁻¹) ≤ B := by
  first | exact @GlobalTheory.CharpolyBound.bound | exact GlobalTheory.CharpolyBound.bound | (intros; apply GlobalTheory.CharpolyBound.bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyIntegralUnitConstCoeffOfMemMaxCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyIntegralUnitConstCoeffOfMemMaxCompact
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CharpolyInt

theorem charpoly_coeff_det_int {E : Type} [Field E] [NumberField E] {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E) :
    (∀ k, A.charpoly.coeff k ∈ w.adicCompletionIntegers E) ∧ A.det ∈ w.adicCompletionIntegers E := by
  let M : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hMA : M.map (w.adicCompletionIntegers E).subtype = A := by ext i j; rfl
  refine ⟨fun k => ?_, ?_⟩
  · rw [← hMA, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (M.charpoly.coeff k).2
  · have hdet : A.det = ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) := by
      rw [← hMA]; exact (RingHom.map_det (w.adicCompletionIntegers E).subtype M).symm
    rw [hdet]; exact M.det.2

theorem entries_int_of_mem_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) :
    (∀ i j, g.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (g⁻¹).1 i j ∈ w.adicCompletionIntegers E := by
  simp only [GlobalTheory.LFun.KGL] at hg
  unfold GLint at hg
  obtain ⟨h, rfl⟩ := hg
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (bc (Ov E w).subtype h).1 i j = ((h.1 i j : Ov E w) : w.adicCompletion E) := rfl
    rw [this]; exact (h.1 i j).2
  · have : ((bc (Ov E w).subtype h)⁻¹).1 i j = (((h⁻¹).1 i j : Ov E w) : w.adicCompletion E) := by
      rw [← map_inv]; rfl
    rw [this]; exact ((h⁻¹).1 i j).2

theorem kint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w),
    g ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (g.val.charpoly.coeff 0) = 1 := by
  intro E _ _ _ n w g hg
  obtain ⟨h1, h2⟩ := entries_int_of_mem_KGL w n g hg
  obtain ⟨hc, hd⟩ := charpoly_coeff_det_int w g.val h1
  obtain ⟨-, hd'⟩ := charpoly_coeff_det_int w (g⁻¹).val h2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd hd'
  refine ⟨fun k => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc k), ?_⟩
  have hprod : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hv : Valued.v g.val.det * Valued.v (g⁻¹).val.det = 1 := by rw [← map_mul, hprod, map_one]
  have hdet : Valued.v g.val.det = 1 := by
    refine le_antisymm hd ?_
    calc (1 : _) = Valued.v g.val.det * Valued.v (g⁻¹).val.det := hv.symm
      _ ≤ Valued.v g.val.det * 1 := mul_le_mul' le_rfl hd'
      _ = Valued.v g.val.det := mul_one _
  have h0 : g.val.charpoly.coeff 0 = (-1) ^ Fintype.card (Fin n) * g.val.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h0, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, hdet]

end GlobalTheory.CharpolyInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyIntegralUnitConstCoeffOfMemMaxCompactStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_integral_unit_constCoeff_of_mem_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w), g ∈ GlobalTheory.LFun.KGL w (n := n) → (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (g.val.charpoly.coeff 0) = 1 := by
  first | exact @GlobalTheory.CharpolyInt.kint | exact GlobalTheory.CharpolyInt.kint | (intros; apply GlobalTheory.CharpolyInt.kint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedEmbeddingsAndValuations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedEmbeddingsAndValuations
open NumberField IsDedekindDomain Filter

namespace GlobalTheory.BddFinite

theorem exists_le_exp_nat (B : WithZero (Multiplicative ℤ)) : ∃ n : ℕ, B ≤ WithZero.exp (n : ℤ) := by
  induction B using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe m =>
    refine ⟨(Multiplicative.toAdd m).toNat, ?_⟩
    rw [WithZero.exp, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]
    simp only [toAdd_ofAdd]
    exact Int.self_le_toNat _

theorem exists_clearing {K : Type} [Field K] [NumberField K] (A : Set K)
    (w : HeightOneSpectrum (𝓞 K)) (B : WithZero (Multiplicative ℤ))
    (hB : ∀ x ∈ A, w.valuation K x ≤ B) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ x ∈ A, w.valuation K ((a : K) * x) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_le_exp_nat B
  have hne : w.asIdeal ^ n ≠ ⊥ := pow_ne_zero n w.ne_bot
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨r, hr0, fun x hx => ?_⟩
  have h1 : w.intValuation r ≤ WithZero.exp (-(n : ℤ)) := (w.intValuation_le_pow_iff_mem r n).2 hr
  rw [map_mul]
  have h2 : w.valuation K (r : K) = w.intValuation r := w.valuation_of_algebraMap r
  rw [h2]
  calc w.intValuation r * w.valuation K x ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) :=
        mul_le_mul' h1 ((hB x hx).trans hn)
    _ = 1 := by rw [← WithZero.exp_add]; simp

theorem finite_of_bdd : ∀ (K : Type) [Field K] [NumberField K] (A : Set K) (R : ℝ), (∀ x ∈ A, ∀ τ : K →+* ℂ, ‖τ x‖ ≤ R) → (∀ w : HeightOneSpectrum (𝓞 K), ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ A, w.valuation K x ≤ B) → (∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ x ∈ A, w.valuation K x ≤ 1) → A.Finite := by
  classical
  intro K _ _ A R hR hB hcof
  choose B hB using hB
  choose a ha0 ha using fun w => exists_clearing A w (B w) (hB w)
  have hF : {w : HeightOneSpectrum (𝓞 K) | ¬ ∀ x ∈ A, w.valuation K x ≤ 1}.Finite :=
    Filter.eventually_cofinite.mp hcof
  set F := hF.toFinset with hFdef
  set d : 𝓞 K := ∏ w ∈ F, a w with hd
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w _ => ha0 w)
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0

  have hval : ∀ x ∈ A, ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((d : K) * x) ≤ 1 := by
    intro x hx v
    by_cases hv : v ∈ F
    · have hsplit : (d : K) = ((∏ w ∈ F.erase v, a w : 𝓞 K) : K) * (a v : K) := by
        rw [hd, ← Finset.prod_erase_mul F a hv]; push_cast; ring
      rw [hsplit, mul_assoc, map_mul]
      exact mul_le_one' (v.valuation_le_one _) (ha v x hx)
    · have hv' : ∀ y ∈ A, v.valuation K y ≤ 1 := by
        have : v ∉ {w : HeightOneSpectrum (𝓞 K) | ¬ ∀ x ∈ A, w.valuation K x ≤ 1} := by
          simpa [F] using hv
        simpa using this
      rw [map_mul]
      exact mul_le_one' (v.valuation_le_one _) (hv' x hx)
  set M : ℝ := ∑ τ : K →+* ℂ, ‖τ (d : K)‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun τ _ => norm_nonneg _)
  have hfin := NumberField.Embeddings.finite_of_norm_le K ℂ (M * R)
  refine (hfin.image (fun y => (d : K)⁻¹ * y)).subset ?_
  intro x hx
  refine ⟨(d : K) * x, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ (hval x hx)
    rw [← hy]
    exact (NumberField.RingOfIntegers.isIntegral_coe y)
  · intro τ
    rw [map_mul, norm_mul]
    have h1 : ‖τ (d : K)‖ ≤ M :=
      Finset.single_le_sum (f := fun τ : K →+* ℂ => ‖τ (d : K)‖) (fun τ _ => norm_nonneg _) (Finset.mem_univ τ)
    exact mul_le_mul h1 (hR x hx τ) (norm_nonneg _) hM0
  · simp only
    rw [← mul_assoc, inv_mul_cancel₀ hdK, one_mul]

end GlobalTheory.BddFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedEmbeddingsAndValuationsStatement
open NumberField IsDedekindDomain Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_bounded_embeddings_and_valuations : ∀ (K : Type) [Field K] [NumberField K] (A : Set K) (R : ℝ), (∀ x ∈ A, ∀ τ : K →+* ℂ, ‖τ x‖ ≤ R) → (∀ w : HeightOneSpectrum (𝓞 K), ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ A, w.valuation K x ≤ B) → (∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ x ∈ A, w.valuation K x ≤ 1) → A.Finite := by
  first | exact @GlobalTheory.BddFinite.finite_of_bdd | exact GlobalTheory.BddFinite.finite_of_bdd | (intros; apply GlobalTheory.BddFinite.finite_of_bdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEllipticCharpolyCompactSection
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinChar

theorem norm_coeff_le_of_mem_ell (E : Type) [Field E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (τ : E →+* ℂ) (k : ℕ) :
    ‖τ (P.coeff k)‖ ≤ (2 : ℝ) ^ n := by
  obtain ⟨hm, hd, -, hr⟩ := hP
  have h := Polynomial.coeff_le_of_roots_le (f := τ) (B := 1) k hm (IsAlgClosed.splits _) (fun z hz => (hr τ z hz).le)
  rw [Polynomial.coeff_map, one_pow, one_mul, hd] at h
  exact h.trans (by exact_mod_cast Nat.choose_le_two_pow n k)

theorem finite_ell_charpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w (n := n)) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P}.Finite := by
  intro E _ _ _ n S hS C hC hK
  set T := {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P} with hT
  choose σ hσ using fun w => (hS w).exists
  choose B hB using fun w => GlobalTheory.T.charpoly_coeffs_valued_bounded_on_compact_GL E n w (C w) (hC w)
  have loc : ∀ P ∈ T, ∀ u ∈ S, (∀ k, u.valuation E (P.coeff k) ≤ B u) ∧ u.valuation E (P.coeff 0)⁻¹ ≤ B u ∧
      (C u ⊆ GlobalTheory.LFun.KGL u (n := n) → (∀ k, u.valuation E (P.coeff k) ≤ 1) ∧ u.valuation E (P.coeff 0) = 1) := by
    intro P hP u hu
    obtain ⟨g, hg, hgP⟩ := hP.2 u hu
    have e : ∀ k, u.valuation E (P.coeff k) = Valued.v (g.val.charpoly.coeff k) := fun k => by
      rw [hgP, Polynomial.coeff_map]; exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).symm
    refine ⟨fun k => (e k).trans_le ((hB u g hg).1 k), ?_, fun hsub => ?_⟩
    · rw [map_inv₀, e, ← map_inv₀]; exact (hB u g hg).2
    · have := GlobalTheory.T.charpoly_integral_unit_constCoeff_of_mem_maxCompact E n u g (hsub hg)
      exact ⟨fun k => (e k).trans_le (this.1 k), (e 0).trans this.2⟩
  have glob : ∀ P ∈ T, ∀ w : Pl E, ∀ k, w.valuation E (P.coeff k) ≤ max (B (σ w)) (B (σ w) * B (σ w)) ∧
      (C (σ w) ⊆ GlobalTheory.LFun.KGL (σ w) (n := n) → w.valuation E (P.coeff k) ≤ 1) := by
    intro P hP w k
    have hu := loc P hP (σ w) (hσ w).1
    obtain ⟨h0, hc⟩ := GlobalTheory.T.elliptic_poly_conj_selfReciprocal_coeff E n P hP.1
    rcases GlobalTheory.T.valuation_eq_or_conj_of_under_maximalRealSubfield_eq E w (σ w) (hσ w).2 with h | h
    · rw [h]
      exact ⟨(hu.1 k).trans (le_max_left _ _), fun hs => (hu.2.2 hs).1 k⟩
    · rw [h]
      by_cases hk : k ≤ n
      · have e : IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) * (P.coeff 0)⁻¹ := by
          rw [← hc k hk]; field_simp
        rw [e, map_mul]
        refine ⟨(mul_le_mul' (hu.1 _) hu.2.1).trans (le_max_right _ _), fun hs => ?_⟩
        rw [map_inv₀, (hu.2.2 hs).2, inv_one, mul_one]; exact (hu.2.2 hs).1 _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega), map_zero, map_zero]
        exact ⟨zero_le', fun _ => zero_le'⟩
  set A := {x : E | ∃ P ∈ T, ∃ k, P.coeff k = x} with hA
  have hAfin : A.Finite := by
    refine GlobalTheory.T.finite_of_bounded_embeddings_and_valuations E A ((2 : ℝ) ^ n) ?_ ?_ ?_
    · rintro _ ⟨P, hP, k, rfl⟩ τ; exact norm_coeff_le_of_mem_ell E n P hP.1 τ k
    · intro w; exact ⟨_, by rintro _ ⟨P, hP, k, rfl⟩; exact (glob P hP w k).1⟩
    · have hbad : {u : Pl E | ¬ C u ⊆ GlobalTheory.LFun.KGL u (n := n)}.Finite := Filter.eventually_cofinite.1 hK
      have : {w : Pl E | ¬ ∀ x ∈ A, w.valuation E x ≤ 1} ⊆ ⋃ u ∈ {u : Pl E | ¬ C u ⊆ GlobalTheory.LFun.KGL u (n := n)},
          {w : Pl E | w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))} := by
        intro w hw
        simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hw ⊢
        refine ⟨σ w, fun hs => hw ?_, (hσ w).2.symm⟩
        rintro _ ⟨P, hP, k, rfl⟩; exact (glob P hP w k).2 hs
      refine Filter.eventually_cofinite.2 (Set.Finite.subset (hbad.biUnion fun u _ => ?_) this)
      exact ((IsDedekindDomain.primesOver_finite (u.under (𝓞 (maximalRealSubfield E))).asIdeal (𝓞 E)).preimage
        (fun a _ b _ h => HeightOneSpectrum.ext h)).subset fun w hw => ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  refine Set.Finite.of_finite_image (f := fun P : E[X] => fun k : Fin (n + 1) => P.coeff k) ?_ ?_
  · refine (Set.Finite.pi (t := fun _ : Fin (n + 1) => A) fun _ => hAfin).subset ?_
    rintro _ ⟨P, hP, rfl⟩ k _
    exact ⟨P, hP, k, rfl⟩
  · intro P hP Q hQ h
    ext k
    by_cases hk : k ≤ n
    · exact congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ.1.2.1]; omega)]

end GlobalTheory.FinChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEllipticCharpolyCompactSectionStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_ellipticCharpoly_compact_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w (n := n)) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P}.Finite := by
  first | exact @GlobalTheory.FinChar.finite_ell_charpoly | exact GlobalTheory.FinChar.finite_ell_charpoly | (intros; apply GlobalTheory.FinChar.finite_ell_charpoly <;> assumption)
end
