module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumSingularAndInvertible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDoma
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumMulDualEqCardPowSq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumMulDualEqCardPowSq
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem sum_addChar_trace_mul_eq {k : Type} [Field k] [Fintype k] [DecidableEq k] {R : Type}
    [CommRing R] [IsDomain R] (ψ : AddChar k R) (hψ : ψ.IsPrimitive) {r : ℕ}
    (m : Matrix (Fin r) (Fin r) k) :
    ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * m)) =
      if m = 0 then (Fintype.card k : R) ^ (r ^ 2) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, sum_const, card_univ,
      nsmul_eq_mul, mul_one]
    rw [show Fintype.card (Matrix (Fin r) (Fin r) k) = Fintype.card (Fin r → Fin r → k) from rfl]
    simp [Fintype.card_fun, ← pow_mul, sq]
  · obtain ⟨i, j, hij⟩ : ∃ i j, m i j ≠ 0 := by
      by_contra h; push_neg at h; exact hm (Matrix.ext h)
    have h1 := hψ hij
    obtain ⟨c, hc⟩ : ∃ c, ψ (m i j * c) ≠ 1 := by
      by_contra h; push_neg at h; apply h1; ext c; simp [AddChar.mulShift_apply, h]
    set a₀ : Matrix (Fin r) (Fin r) k := Matrix.single j i c
    have ha₀ : trace (a₀ * m) = m i j * c := by
      simp [a₀, Matrix.trace_single_mul, mul_comm]
    set S := ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * m))
    have hS : S = ψ (trace (a₀ * m)) * S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight a₀) _ _ (fun a => ?_)
      simp only [Equiv.subRight_apply, ← AddChar.map_add_eq_mul, Matrix.sub_mul, trace_sub]
      congr 1; ring
    rw [ha₀] at hS
    have : (1 - ψ (m i j * c)) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hc
    · exact h

end GlobalTheory

namespace GlobalTheory

theorem matrixGaussSum_mul_dual_eq_card_pow : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) * (∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ⁻¹ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) = (Fintype.card k : R) ^ (r ^ 2) := by
  intro k _ _ _ R _ _ ψ ξ r hψ hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k R ψ ξ r hψ hξ
  let S : Matrix (Fin r) (Fin r) k → R := fun a => ∑ x : GL (Fin r) k,
    (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (trace (a * (x : Matrix (Fin r) (Fin r) k)))

  have key1 : ∑ a, S a * ψ (-trace a) = (Fintype.card k : R) ^ (r ^ 2) := by
    simp only [S, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hx : ∀ x : GL (Fin r) k, ∑ a : Matrix (Fin r) (Fin r) k,
        (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (trace (a * (x : Matrix (Fin r) (Fin r) k))) * ψ (-trace a)
        = (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
          ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * ((x : Matrix (Fin r) (Fin r) k) - 1))) := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_assoc, ← AddChar.map_add_eq_mul, Matrix.mul_sub, Matrix.mul_one, trace_sub, sub_eq_add_neg]
    simp_rw [hx, sum_addChar_trace_mul_eq ψ hψ]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro x _ hx1
      rw [if_neg, mul_zero]
      intro h
      apply hx1
      ext1
      simpa using sub_eq_zero.mp h
    · simp

  have key2 : ∑ a, S a * ψ (-trace a) =
      ∑ g : GL (Fin r) k, S (g : Matrix (Fin r) (Fin r) k) * ψ (-trace (g : Matrix (Fin r) (Fin r) k)) := by
    symm
    refine Fintype.sum_of_injective (fun g : GL (Fin r) k => (g : Matrix (Fin r) (Fin r) k)) (fun g h e => Units.ext e) _ _ ?_ (fun g => rfl)
    intro a ha
    have hdet : a.det = 0 := by
      by_contra h
      exact ha ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a h, rfl⟩
    simp only [S]
    rw [hsing a hdet, zero_mul]
  rw [← key1, key2]
  simp only [S]
  simp_rw [hinv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [MonoidHom.inv_apply, AddChar.inv_apply]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumMulDualEqCardPowSqStatement
open Matrix Finset
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixGaussSum_mul_dual_eq_card_pow_sq : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) * (∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ⁻¹ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) = (Fintype.card k : R) ^ (r ^ 2) := by
  first | exact @GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow | exact GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow | (intros; apply GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGalois
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem norm_val_monoidHom_units_eq_one {G : Type} [Group G] [Finite G] (ξ : G →* ℂˣ) (g : G) :
    ‖((ξ g : ℂˣ) : ℂ)‖ = 1 := by
  have h : (ξ g) ^ (Nat.card G) = 1 := by rw [← map_pow, pow_card_eq_one']; exact map_one ξ
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card G) ?_ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem isIntegral_int_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    IsIntegral ℤ z :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [h]⟩

theorem isIntegral_val_monoidHom_units {G : Type} [Group G] [Finite G] (ξ : G →* ℂˣ) (g : G) :
    IsIntegral ℤ ((ξ g : ℂˣ) : ℂ) := by
  refine isIntegral_int_of_pow_eq_one (n := Nat.card G) Nat.card_pos ?_
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

theorem isIntegral_addChar_apply {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (x : k) :
    IsIntegral ℤ (ψ x) := by
  refine isIntegral_int_of_pow_eq_one (n := Fintype.card k) Fintype.card_pos ?_
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]

theorem complexMatrixGaussSum_norm_integral_galois :
    ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∀ S : ℂ, S = (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k))) → ‖S‖ ^ 2 = (Fintype.card k : ℝ) ^ (r ^ 2) ∧ IsIntegral ℤ S ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ (r ^ 2) * S⁻¹) ∧ ∀ (τ : ℂ ≃+* ℂ) (ξ' : kˣ →* ℂˣ), (∀ x, ((ξ' x : ℂˣ) : ℂ) = τ ((ξ x : ℂˣ) : ℂ)) → ∃ a : kˣ, (∀ x, τ (ψ x) = ψ ((a : k) * x)) ∧ τ S = ((ξ' a : ℂˣ) : ℂ) ^ r * ∑ x : GL (Fin r) k, (((ξ' (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) := by
  intro k _ _ _ ψ ξ r hψ hξ S hS
  have hN := GlobalTheory.T.matrixGaussSum_mul_dual_eq_card_pow_sq k ℂ ψ ξ r hψ hξ
  simp only [Matrix.one_mul] at hN
  rw [← hS] at hN
  set D := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hD
  have hconj : D = starRingEnd ℂ S := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, AddChar.inv_apply, AddChar.map_neg_eq_conj, MonoidHom.inv_apply, inv_inv,
      Units.val_inv_eq_inv_val, map_inv₀,
      ← Complex.inv_eq_conj (norm_val_monoidHom_units_eq_one ξ _), inv_inv]
  have hDint : IsIntegral ℤ D := by
    refine IsIntegral.sum _ fun x _ => IsIntegral.mul ?_ (isIntegral_addChar_apply _ _)
    exact isIntegral_val_monoidHom_units _ _
  have hSint : IsIntegral ℤ S := by
    rw [hS]
    refine IsIntegral.sum _ fun x _ => IsIntegral.mul ?_ (isIntegral_addChar_apply _ _)
    rw [← map_inv]
    exact isIntegral_val_monoidHom_units _ _
  have hq0 : (Fintype.card k : ℂ) ^ (r ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hS0 : S ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hN
    exact hq0 hN.symm
  refine ⟨?_, hSint, ?_, ?_⟩
  · rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hN
    exact_mod_cast hN
  · rw [← hN, mul_comm S D, mul_assoc, mul_inv_cancel₀ hS0, mul_one]
    exact hDint
  · intro τ ξ' hξ'

    let φ : AddChar k ℂ := (τ : ℂ →+* ℂ).toMonoidHom.compAddChar ψ
    have hbij : Function.Bijective (fun b : k => ψ.mulShift b) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨AddChar.to_mulShift_inj_of_isPrimitive hψ, AddChar.card_eq.symm⟩
    obtain ⟨b, hb⟩ := hbij.2 φ
    have hbφ : ∀ x, τ (ψ x) = ψ (b * x) := fun x => by
      have := DFunLike.congr_fun hb x
      simpa [φ, AddChar.mulShift_apply] using this.symm
    have hb0 : b ≠ 0 := by
      rintro rfl
      have h1 : ψ.mulShift 1 ≠ 1 := hψ one_ne_zero
      apply h1
      ext x
      have := hbφ x
      rw [zero_mul, AddChar.map_zero_eq_one, ← map_one τ] at this
      rw [AddChar.mulShift_apply, one_mul, AddChar.one_apply]
      exact τ.injective this
    have hξ'1 : ξ' ≠ 1 := by
      intro h1
      apply hξ
      ext x
      have := hξ' x
      rw [h1, MonoidHom.one_apply, Units.val_one, ← map_one τ] at this
      exact (τ.injective this).symm
    refine ⟨Units.mk0 b hb0, fun x => hbφ x, ?_⟩
    let g : GL (Fin r) k :=
      Units.map (Matrix.scalar (Fin r) : k →+* Matrix (Fin r) (Fin r) k).toMonoidHom (Units.mk0 b hb0)
    have hg : (g : Matrix (Fin r) (Fin r) k) = Matrix.scalar (Fin r) b := rfl
    have hdet : Matrix.GeneralLinearGroup.det g = (Units.mk0 b hb0) ^ r := by
      ext
      simp [hg, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]
    have key := (GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ ξ' r hψ hξ'1).2 g
    rw [hdet, map_pow, Units.val_pow_eq_pow_val] at key
    simp only [Matrix.one_mul] at key
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← key, hS, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, hbφ, Units.val_inv_eq_inv_val, map_inv₀, ← hξ', ← Units.val_inv_eq_inv_val, hg,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGaloisStatement
open Matrix Finset
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∀ S : ℂ, S = (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k))) → ‖S‖ ^ 2 = (Fintype.card k : ℝ) ^ (r ^ 2) ∧ IsIntegral ℤ S ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ (r ^ 2) * S⁻¹) ∧ ∀ (τ : ℂ ≃+* ℂ) (ξ' : kˣ →* ℂˣ), (∀ x, ((ξ' x : ℂˣ) : ℂ) = τ ((ξ x : ℂˣ) : ℂ)) → ∃ a : kˣ, (∀ x, τ (ψ x) = ψ ((a : k) * x)) ∧ τ S = ((ξ' a : ℂˣ) : ℂ) ^ r * ∑ x : GL (Fin r) k, (((ξ' (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) := by
  first | exact @GlobalTheory.complexMatrixGaussSum_norm_integral_galois | exact GlobalTheory.complexMatrixGaussSum_norm_integral_galois | (intros; apply GlobalTheory.complexMatrixGaussSum_norm_integral_galois <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramDetEqNormMulGramDetOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramDetEqNormMulGramDetOne
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.InvAlg

theorem gramDet_eq_norm_mul (K : UQ) (B : InvAlg K) (x : B.A) :
    B.gramDet x = Algebra.norm K.E x * B.gramDet 1 := by
  classical
  set b := Module.finBasis K.E B.A
  have hM : (Matrix.of fun i j => B.herm x (b i) (b j)) =
      (Algebra.leftMulMatrix b x).transpose * (Matrix.of fun i j => B.herm 1 (b i) (b j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, herm, one_mul,
      Algebra.leftMulMatrix_apply]
    have h := b.sum_repr (x * b i)
    conv_lhs => rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, LinearMap.toMatrix_apply]
    simp
  unfold gramDet
  rw [hM, Matrix.det_mul, Matrix.det_transpose, Algebra.norm_eq_matrix_det b]

end GlobalTheory.UnitLemma.InvAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramDetEqNormMulGramDetOneStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramDet_eq_norm_mul_gramDet_one : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.gramDet x = Algebra.norm K.E x * B.gramDet 1 := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul | exact GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul | (intros; apply GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardKerMulCardEq
namespace GlobalTheory.ZModDual

theorem card_quot_ker_le (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A] [Module (ZMod n) A]
    [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (A ⧸ LinearMap.ker b) ≤ Nat.card (B ⧸ LinearMap.ker b.flip) := by
  set K' := LinearMap.ker b.flip
  have : Finite (B ⧸ K') := Finite.of_surjective K'.mkQ K'.mkQ_surjective
  have : Finite (Module.Dual (ZMod n) B) :=
    Finite.of_injective (fun f : Module.Dual (ZMod n) B => (f : B → ZMod n)) DFunLike.coe_injective
  have hle : LinearMap.range b ≤ K'.dualAnnihilator := by
    rintro _ ⟨a, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    have := LinearMap.congr_fun (LinearMap.mem_ker.1 hy) a
    simpa using this
  calc Nat.card (A ⧸ LinearMap.ker b) = Nat.card (LinearMap.range b) :=
        Nat.card_congr (LinearMap.quotKerEquivRange b).toEquiv
    _ ≤ Nat.card K'.dualAnnihilator :=
        Nat.card_le_card_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ = Nat.card (Module.Dual (ZMod n) (B ⧸ K')) :=
        Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator K').toEquiv.symm
    _ = Nat.card (B ⧸ K') := card_dual_eq n (B ⧸ K')

theorem card_ker_mul_card_eq (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A]
    [Module (ZMod n) A] [Finite A] [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (LinearMap.ker b) * Nat.card B = Nat.card (LinearMap.ker b.flip) * Nat.card A := by
  have h1 := card_quot_ker_le n A B b
  have h2 := card_quot_ker_le n B A b.flip
  rw [LinearMap.flip_flip] at h2
  have heq : Nat.card (A ⧸ LinearMap.ker b) = Nat.card (B ⧸ LinearMap.ker b.flip) := le_antisymm h1 h2
  have eA := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker b)
  have eB := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker b.flip)
  rw [eA, eB, heq]
  ring

end GlobalTheory.ZModDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenMulLeftImageLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenMulLeftImageLattice
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem finite_quot_span_of_ne_zero (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have h1 : Ideal.span {c} = IsLocalRing.maximalIdeal O ^ n := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow, hu,
      Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [h1]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

theorem finite_between_mulLat (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L)
    (c : K.O) (hc : c ≠ 0) :
    {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by
  haveI := finite_quot_span_of_ne_zero K.O c hc
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1
  have hfg : (⊤ : Submodule K.O L).FG := Module.Finite.fg_top
  set S : Submodule K.O L := Ideal.span {c} • (⊤ : Submodule K.O L) with hS
  haveI : Finite (L ⧸ S) := Submodule.finite_quotient_smul _ hfg
  haveI : Finite (Submodule K.O (L ⧸ S)) :=
    Finite.of_injective (fun P : Submodule K.O (L ⧸ S) => (P : Set (L ⧸ S))) SetLike.coe_injective
  let f : Submodule K.O B.A → Submodule K.O (L ⧸ S) := fun M => (M.comap L.subtype).map S.mkQ
  have hSle : ∀ M : Submodule K.O B.A, mulLat K.O (algebraMap K.O B.A c) L ≤ M → S ≤ M.comap L.subtype := by
    intro M hM
    rw [hS, Submodule.smul_le]
    intro r hr x _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have hx : algebraMap K.O B.A c * (x : B.A) ∈ M := hM ⟨x, x.2, rfl⟩
    have : ((a * c) • x : L) = (a • (algebraMap K.O B.A c * (x : B.A)) : B.A) := by
      rw [Submodule.coe_smul, ← Algebra.smul_def, smul_smul]
    rw [Submodule.mem_comap, Submodule.subtype_apply, this]
    exact M.smul_mem a hx
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M₁ h₁ M₂ h₂ heq
  have e1 : M₁.comap L.subtype = M₂.comap L.subtype := by
    have := congrArg (Submodule.comap S.mkQ) heq
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.2 (hSle M₁ h₁.1), sup_eq_right.2 (hSle M₂ h₂.1)] at this
  have e2 := congrArg (Submodule.map L.subtype) e1
  rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 h₁.2,
    inf_eq_right.2 h₂.2] at e2

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenMulLeftImageLatticeStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 → {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by
  first | exact @GlobalTheory.UnitLemma.finite_between_mulLat | exact GlobalTheory.UnitLemma.finite_between_mulLat | (intros; apply GlobalTheory.UnitLemma.finite_between_mulLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMonoidAlgebraLiftEqOfCharpolyEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMonoidAlgebraLiftEqOfCharpolyEq
open scoped BigOperators

namespace GlobalTheory

open Polynomial in
private lemma det_generic_sum_eq_of_charpoly_eq {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly)
    (m : ℕ) (g : Fin m → G) :
    (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) k) • (ρ (g i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)).det =
      (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) k) • (σ (g i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)).det := by
  ext d
  let T : Subalgebra k (Bool → k) :=
    AlgHom.equalizer (Pi.evalAlgHom k (fun _ : Bool => k) true) (Pi.evalAlgHom k (fun _ : Bool => k) false)
  have key := _root_.GlobalTheory.coeff_det_generic_sum_mem_of_charpoly_coeff_mem T n
    (fun b => if b then ρ else σ) (by intro g j; simp [T, AlgHom.mem_equalizer, h]) m g d
  simpa [T, AlgHom.mem_equalizer] using key

open Polynomial in
private lemma charpoly_sum_smul_eq_of_charpoly_eq {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly)
    (m : ℕ) (c : Fin m → k) (g : Fin m → G) :
    (∑ i, c i • ρ (g i)).charpoly = (∑ i, c i • σ (g i)).charpoly := by
  have hd := det_generic_sum_eq_of_charpoly_eq n ρ σ h (m + 1) (Fin.cons 1 g)
  have key : ∀ τ : G →* Matrix (Fin n) (Fin n) k, (∑ i, c i • τ (g i)).charpoly =
      MvPolynomial.aeval (Fin.cons (X : k[X]) (fun i => -C (c i)) : Fin (m + 1) → k[X])
        (∑ i, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) k) •
          (τ ((Fin.cons 1 g : Fin (m + 1) → G) i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin (m + 1)) k)).det := by
    intro τ
    rw [AlgHom.map_det]
    unfold Matrix.charpoly
    congr 1
    ext i j
    simp [Fin.sum_univ_succ, Matrix.charmatrix_apply, Matrix.sum_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  rw [key ρ, key σ, hd]

open Polynomial in
theorem _root_.GlobalTheory.charpoly_lift_eq_of_charpoly_eq : ∀ {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ g, (ρ g).charpoly = (σ g).charpoly) →
    ∀ a : MonoidAlgebra k G,
      (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a).charpoly =
      (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G σ a).charpoly := by
  intro k G _ _ n ρ σ h a
  have hsum : ∀ τ : G →* Matrix (Fin n) (Fin n) k,
      MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G τ a =
        ∑ i, a.coeff (a.coeff.support.equivFin.symm i) • τ (a.coeff.support.equivFin.symm i) := by
    intro τ
    rw [MonoidAlgebra.lift_apply, Finsupp.sum, ← Finset.sum_coe_sort a.coeff.support]
    exact (Equiv.sum_comp a.coeff.support.equivFin.symm (fun x : a.coeff.support => a.coeff x • τ x)).symm
  rw [hsum ρ, hsum σ]
  exact charpoly_sum_smul_eq_of_charpoly_eq n ρ σ h _ _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMonoidAlgebraLiftEqOfCharpolyEqStatement
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_monoidAlgebraLift_eq_of_charpoly_eq : ∀ {k G : Type} [Field k] [Monoid G] (n : ℕ) (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ g, (ρ g).charpoly = (σ g).charpoly) → ∀ a : MonoidAlgebra k G, (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a).charpoly = (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G σ a).charpoly := by
  first | exact @GlobalTheory.charpoly_lift_eq_of_charpoly_eq | exact GlobalTheory.charpoly_lift_eq_of_charpoly_eq | (intros; apply GlobalTheory.charpoly_lift_eq_of_charpoly_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfAlgHomEqMul
open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr

theorem _root_.GlobalTheory.CycFr.eq_act_of_comm {l : ℕ} [Fact l.Prime] {O : Type}
    [CommRing O] [IsDomain O] [CharZero O]
    [Algebra ℤ_[l] O] (φ₀ g : O⟦X⟧ →ₐ[O] O⟦X⟧) (c : ℤ_[l]) (hφ : φ₀ X = (1 + X) ^ l - 1)
    (hc : ∀ a, φ₀ (g a) = g (φ₀ a)) (h0 : constantCoeff (g X) = 0)
    (h1 : coeff 1 (g X) = algebraMap ℤ_[l] O c) :
    g = _root_.GlobalTheory.CycFr.act O c := by
  set A := _root_.GlobalTheory.CycFr.act O c X with hAdef
  set G := g X with hGdef
  set P : O⟦X⟧ := ∑ i ∈ Finset.range l, (1 + X) ^ i with hPdef
  have hP : (1 + X : O⟦X⟧) ^ l - 1 = X * P := by
    rw [← geom_sum_mul, add_sub_cancel_left, mul_comm]
  have hPc : constantCoeff P = (l : O) := by simp [P]
  have hXφ : X ∣ φ₀ X := by rw [hφ, hP]; exact dvd_mul_right _ _
  have hφact : φ₀ = _root_.GlobalTheory.CycFr.act O (l : ℤ_[l]) := by
    apply _root_.GlobalTheory.CycFr.algHom_ext_X _ _ hXφ
    rw [hφ, _root_.GlobalTheory.CycFr.act_nat_X]
  have hA0 : constantCoeff A = 0 :=
    PowerSeries.X_dvd_iff.mp (_root_.GlobalTheory.CycFr.X_dvd_act_X c)
  have hG : φ₀ G = (1 + G) ^ l - 1 := by
    rw [hGdef, hc, hφ]; simp [map_sub, map_pow, map_add (f := _), map_one]
  have hA : φ₀ A = (1 + A) ^ l - 1 := by
    rw [hAdef, hφact, _root_.GlobalTheory.CycFr.act_comm, ← hφact, hφ]
    simp [map_sub, map_pow, map_add (f := _), map_one]
  have hstep : ∀ n, 2 ≤ n → ∀ E : O⟦X⟧, G - A = X ^ n * E → constantCoeff E = 0 := by
    intro n hn E hE
    set S : O⟦X⟧ := ∑ i ∈ Finset.range l, (1 + G) ^ i * (1 + A) ^ (l - 1 - i) with hSdef
    have hSc : constantCoeff S = (l : O) := by simp [S, hA0, h0]
    have hD : φ₀ (G - A) = (G - A) * S := by
      have hgs := geom_sum₂_mul (1 + G) (1 + A) l
      rw [add_sub_add_left_eq_sub] at hgs
      rw [map_sub, hG, hA, mul_comm, hgs]; ring
    rw [hE, map_mul, map_pow, hφ, hP, mul_pow, mul_assoc, mul_assoc] at hD
    have hcancel := mul_left_cancel₀ (pow_ne_zero n PowerSeries.X_ne_zero) hD
    have hcc := congrArg constantCoeff hcancel
    rw [map_mul, map_mul, map_pow, hPc, hSc,
      _root_.GlobalTheory.CycFr.constantCoeff_algHom φ₀ hXφ E] at hcc
    have hne : ((l : O) ^ n) ≠ (l : O) := by
      rw [← Nat.cast_pow, Ne, Nat.cast_inj]
      intro h
      have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
      have := Nat.pow_right_injective h2 (h.trans (pow_one l).symm)
      omega
    have : constantCoeff E * ((l : O) ^ n - l) = 0 := by linear_combination hcc
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have hdvd : ∀ n, X ^ (n + 2) ∣ G - A := by
    intro n
    induction n with
    | zero =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [hA0, h0]
      · rw [map_sub, h1, hAdef, _root_.GlobalTheory.CycFr.coeff_one_act_X, sub_self]
    | succ k ih =>
      obtain ⟨E, hE⟩ := ih
      have he := hstep (k + 2) (by omega) E hE
      obtain ⟨F, hF⟩ := PowerSeries.X_dvd_iff.mpr he
      exact ⟨F, by rw [hE, hF]; ring⟩
  have hGA : G = A := by
    rw [← sub_eq_zero]
    ext m
    have := PowerSeries.X_pow_dvd_iff.mp (hdvd m) m (by omega)
    simpa using this
  exact _root_.GlobalTheory.CycFr.algHom_ext_X _ _ (PowerSeries.X_dvd_iff.mpr h0) hGA

end GlobalTheory.CycFr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlg
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlg
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.HilbertNinety

theorem exists_unit_sigma (K : UQ) (B : InvAlg K) (u : B.A) (hu : u * B.σ u = 1) :
    ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  classical
  letI : Module ℚ B.A := Module.compHom B.A (algebraMap ℚ K.E)
  let b : B.A →+ B.A :=
    { toFun := fun a => a + B.σ a * B.σ u
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add (f := _)]; ring }
  have hb : ∀ a, b a = a + B.σ a * B.σ u := fun a => rfl
  have hbσ : ∀ a, B.σ (b a) = b a * u := by
    intro a
    rw [hb, map_add (f := _), map_mul, B.σ_σ, B.σ_σ]
    linear_combination (-(B.σ a)) * hu
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  set e : K.E := algebraMap K.O K.E x with he
  have hce : K.c e - e ≠ 0 := by
    intro h
    rw [sub_eq_zero, he, hxy] at h
    have := IsFractionRing.injective K.O K.E h
    exact hne (by rw [this, sub_self]; exact Ideal.zero_mem _)
  have key : ∀ z : B.A, algebraMap K.E B.A (K.c e - e) * z =
      algebraMap K.E B.A (K.c e) * b z - b (algebraMap K.E B.A e * z) := by
    intro z
    rw [hb, hb, map_mul, B.σ_alg, map_sub]
    ring
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  haveI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
  let S : MaximalSpectrum B.A → Submodule ℚ B.A := fun m =>
    { carrier := {a | b a ∈ m.asIdeal}
      add_mem' := fun {a c} ha hc => by
        change b (a + c) ∈ m.asIdeal
        rw [map_add (f := _)]; exact m.asIdeal.add_mem ha hc
      zero_mem' := by change b 0 ∈ m.asIdeal; rw [map_zero]; exact m.asIdeal.zero_mem
      smul_mem' := fun q a ha => by
        change b (q • a) ∈ m.asIdeal
        rw [map_rat_smul]
        change (algebraMap ℚ K.E q) • b a ∈ m.asIdeal
        rw [Algebra.smul_def]
        exact m.asIdeal.mul_mem_left _ ha }
  have hS : ⊤ ∉ Finset.univ.image S := by
    intro h
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 h
    have hall : ∀ a, b a ∈ m.asIdeal := fun a => by
      have : a ∈ S m := hm ▸ Submodule.mem_top
      exact this
    have h1 : algebraMap K.E B.A (K.c e - e) ∈ m.asIdeal := by
      have := key 1
      rw [mul_one] at this
      rw [this]
      exact m.asIdeal.sub_mem (m.asIdeal.mul_mem_left _ (hall 1)) (hall _)
    apply m.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : algebraMap K.E B.A (K.c e - e)⁻¹ * algebraMap K.E B.A (K.c e - e) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hce, map_one]
    rw [← h2]
    exact m.asIdeal.mul_mem_left _ h1
  have h3 := Subspace.biUnion_ne_univ_of_top_notMem hS
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).1 h3
  have hunit : IsUnit (b a) := by
    by_contra hn
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hn
    apply ha
    exact Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm
  exact ⟨hunit.unit, by rw [IsUnit.unit_spec]; exact hbσ a⟩

end GlobalTheory.UnitLemma.HilbertNinety
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlgStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_sigma_eq_mul_invAlg : ∀ (K : UQ) (B : InvAlg K) (u : B.A), u * B.σ u = 1 → ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  first | exact @GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma | exact GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma | (intros; apply GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactIntMatrix
open Matrix MeasureTheory Topology

noncomputable section

namespace GlobalTheory.JR.MeasExist

theorem isOpen_intMatrix (r : ℕ) (k : Type) [NontriviallyNormedField k] [IsUltrametricDist k] :
    IsOpen {A : Matrix (Fin r) (Fin r) k | ∀ i j, ‖A i j‖ ≤ 1} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  have h : IsOpen (Metric.closedBall (0 : k) 1) := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hc : Continuous fun A : Matrix (Fin r) (Fin r) k => A i j := by fun_prop
  convert h.preimage hc using 1
  ext A; simp

theorem isCompact_intMatrix (r : ℕ) (k : Type) [NontriviallyNormedField k] [LocallyCompactSpace k] :
    IsCompact {A : Matrix (Fin r) (Fin r) k | ∀ i j, ‖A i j‖ ≤ 1} := by
  haveI : ProperSpace k := ProperSpace.of_locallyCompactSpace k
  have h : IsCompact (Set.pi Set.univ fun _ : Fin r => Set.pi Set.univ fun _ : Fin r =>
      Metric.closedBall (0 : k) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {A : Matrix (Fin r) (Fin r) k | ∀ i j, ‖A i j‖ ≤ 1} = (Set.pi Set.univ fun _ : Fin r =>
      Set.pi Set.univ fun _ : Fin r => Metric.closedBall (0 : k) 1) := by
    ext A
    exact ⟨fun H i _ j _ => mem_closedBall_zero_iff.2 (H i j),
      fun H i j => mem_closedBall_zero_iff.1 (H i trivial j trivial)⟩
  rw [e]; exact h

theorem isOpen_glO (r : ℕ) (k : Type) [NontriviallyNormedField k] [IsUltrametricDist k] :
    IsOpen (glO r k) := by
  have h1 := (isOpen_intMatrix r k).preimage (Units.continuous_val (M := Matrix (Fin r) (Fin r) k))
  have h2 := (isOpen_intMatrix r k).preimage (Units.continuous_coe_inv (M := Matrix (Fin r) (Fin r) k))
  convert h1.inter h2 using 1
  ext g
  simp only [glO, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, forall_and]

theorem isCompact_glO (r : ℕ) (k : Type) [NontriviallyNormedField k] [LocallyCompactSpace k] :
    IsCompact (glO r k) := by
  have hK := isCompact_intMatrix r k
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin r) (Fin r) k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [glO, Set.mem_setOf_eq, Set.mem_preimage, forall_and, Units.embedProduct_apply, Set.mem_prod,
    (MulOpposite.op_injective).mem_set_image]

theorem one_mem_intMatrix (r : ℕ) (k : Type) [NormedField k] (i j : Fin r) :
    ‖(1 : Matrix (Fin r) (Fin r) k) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem isOpen_uO (r : ℕ) (k : Type) [NontriviallyNormedField k] [IsUltrametricDist k] [StarRing k] :
    IsOpen (uO r k) :=
  (isOpen_intMatrix r k).preimage continuous_subtype_val

theorem isCompact_uO (r : ℕ) (k : Type) [NontriviallyNormedField k] [LocallyCompactSpace k] [StarRing k]
    [ContinuousStar k] : IsCompact (uO r k) :=
  (isClosed_unitary (R := Matrix (Fin r) (Fin r) k)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_intMatrix r k)

@[to_additive exists_addHaar_eq_one  ]
theorem exists_haar_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] {K : Set G} (hc : IsCompact K) (ho : IsOpen K) (hne : K.Nonempty) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ μ K = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K, hc⟩, by rwa [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk, ho.interior_eq]⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

theorem nonempty_meas (r : ℕ) (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [h : Unram F E] : Nonempty (Meas r F E) := by
  haveI := h.ultraF
  haveI := h.ultraE
  haveI := h.lcF
  haveI := h.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun y => (h.norm_star y).le⟩
  borelize (GL (Fin r) F) (↥(Matrix.unitaryGroup (Fin r) E)) F E
  obtain ⟨μG, hG, vG⟩ := exists_haar_eq_one (isCompact_glO r F) (isOpen_glO r F)
    ⟨1, fun i j => ⟨one_mem_intMatrix r F i j, by simpa using one_mem_intMatrix r F i j⟩⟩
  obtain ⟨μU, hU, vU⟩ := exists_haar_eq_one (isCompact_uO r E) (isOpen_uO r E)
    ⟨1, fun i j => one_mem_intMatrix r E i j⟩
  obtain ⟨μF, hF, vF⟩ := exists_addHaar_eq_one (isCompact_closedBall (0 : F) 1)
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero) ⟨0, by simp⟩
  obtain ⟨μE, hE, vE⟩ := exists_addHaar_eq_one (isCompact_closedBall (0 : E) 1)
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero) ⟨0, by simp⟩
  exact ⟨Meas.mk μG μU μF μE hG hU hF hE vG vU vF vE⟩

end GlobalTheory.JR.MeasExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjTransposeVecMulVecSelf
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.UnitWitt

variable {E : Type} [Field E] [StarRing E] {r : ℕ}

theorem vecMulVec_mulVec_eq (w v z : Fin r → E) : vecMulVec w v *ᵥ z = (v ⬝ᵥ z) • w := by
  ext i
  simp [mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem conjTranspose_vecMulVec_self (w : Fin r → E) : (vecMulVec w (star w))ᴴ = vecMulVec w (star w) := by
  ext i j
  simp [vecMulVec, conjTranspose_apply, mul_comm]

theorem vecMulVec_self_mul (w : Fin r → E) :
    vecMulVec w (star w) * vecMulVec w (star w) = (star w ⬝ᵥ w) • vecMulVec w (star w) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem refl_mem (w : Fin r → E) (a : E) (ha : a ≠ 0) (hN : star w ⬝ᵥ w = a + star a) :
    (1 - a⁻¹ • vecMulVec w (star w)) ∈ unitaryGroup (Fin r) E := by
  rw [mem_unitaryGroup_iff']
  have hs : star (1 - a⁻¹ • vecMulVec w (star w)) = 1 - (star a)⁻¹ • vecMulVec w (star w) := by
    rw [star_sub, star_one, star_smul, star_inv₀]
    congr 2
    exact conjTranspose_vecMulVec_self w
  have ha' : star a ≠ 0 := by simpa using ha
  rw [hs]
  have key : (star a)⁻¹ + a⁻¹ - (star a)⁻¹ * a⁻¹ * (star w ⬝ᵥ w) = 0 := by
    rw [hN]; field_simp; ring
  calc (1 - (star a)⁻¹ • vecMulVec w (star w)) * (1 - a⁻¹ • vecMulVec w (star w))
      = 1 - ((star a)⁻¹ + a⁻¹ - (star a)⁻¹ * a⁻¹ * (star w ⬝ᵥ w)) • vecMulVec w (star w) := by
        rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, vecMulVec_self_mul,
          smul_smul, sub_smul, add_smul]
        abel
    _ = 1 := by rw [key, zero_smul, sub_zero]

theorem refl_mulVec (w u : Fin r → E) (a : E) (ha : star w ⬝ᵥ u = a) (ha0 : a ≠ 0) :
    (1 - a⁻¹ • vecMulVec w (star w)) *ᵥ u = u - w := by
  have h1 : (a⁻¹ • vecMulVec w (star w)) *ᵥ u = a⁻¹ • (vecMulVec w (star w) *ᵥ u) := by
    ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [sub_mulVec, one_mulVec, h1, vecMulVec_mulVec_eq, ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]

theorem star_dot (x y : Fin r → E) : star (star x ⬝ᵥ y) = star y ⬝ᵥ x := by
  simp [dotProduct, star_sum, mul_comm]

theorem exists_of_ne (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v) (ha : star (u - v) ⬝ᵥ u ≠ 0) :
    ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  have hN : star (u - v) ⬝ᵥ (u - v) = star (u - v) ⬝ᵥ u + star (star (u - v) ⬝ᵥ u) := by
    rw [star_dot]
    simp only [star_sub, sub_dotProduct, dotProduct_sub]
    rw [← hc]
    ring
  refine ⟨⟨_, refl_mem (u - v) _ ha hN⟩, ?_⟩
  show (1 - (star (u - v) ⬝ᵥ u)⁻¹ • vecMulVec (u - v) (star (u - v))) *ᵥ u = v
  rw [refl_mulVec (u - v) u _ rfl ha]
  abel

theorem exists_unitary_mulVec (h2 : (2 : E) ≠ 0) (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v)
    (h0 : star u ⬝ᵥ u ≠ 0) : ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  by_cases ha : star (u - v) ⬝ᵥ u = 0
  · have hvu : star v ⬝ᵥ u = star u ⬝ᵥ u := by
      rw [star_sub, sub_dotProduct, sub_eq_zero] at ha; exact ha.symm
    have hc' : star (-u) ⬝ᵥ (-u) = star v ⬝ᵥ v := by simpa using hc
    have ha' : star (-u - v) ⬝ᵥ (-u) ≠ 0 := by
      have : star (-u - v) ⬝ᵥ (-u) = 2 * (star u ⬝ᵥ u) := by
        simp only [star_sub, star_neg, sub_dotProduct, neg_dotProduct, dotProduct_neg, hvu]
        ring
      rw [this]; exact mul_ne_zero h2 h0
    obtain ⟨g, hg⟩ := exists_of_ne (-u) v hc' ha'
    refine ⟨⟨-g.1, ?_⟩, ?_⟩
    · rw [mem_unitaryGroup_iff', star_neg, neg_mul_neg]; exact mem_unitaryGroup_iff'.1 g.2
    · show (-g.1) *ᵥ u = v
      rw [← hg, neg_mulVec, mulVec_neg]
  · exact exists_of_ne u v hc ha

end GlobalTheory.UnitWitt

theorem GlobalTheory.unitary_transitive_of_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (u v : Fin r → E), star u ⬝ᵥ u = star v ⬝ᵥ v →
    star u ⬝ᵥ u ≠ 0 → ∃ g : Matrix.unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  intro F E _ _ _ _ hU r u v hc h0
  haveI : CharZero F := hU.charZero
  have h2 : (2 : E) ≠ 0 := by
    intro h
    apply (two_ne_zero : (2 : F) ≠ 0)
    apply (algebraMap F E).injective
    rw [map_ofNat, map_zero]; exact h
  exact GlobalTheory.UnitWitt.exists_unitary_mulVec h2 u v hc h0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicCompletionExtension
open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT

theorem factorPow_evalₐ_adic {B : Type} [CommRing B] (J : Ideal B) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion J B) :
    Ideal.Quotient.factorPow J h (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J B x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have hs := s.prop h
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hs
  rw [← neg_sub]
  exact (J ^ m).neg_mem hs

theorem exists_adicCompletion_extension {B : Type} [CommRing B] (l : ℕ)
    (f : B →+* AdicCompletion (Ideal.span {(l : B)}) B) :
    ∃ g : AdicCompletion (Ideal.span {(l : B)}) B →+* AdicCompletion (Ideal.span {(l : B)}) B,
      ∀ b, g (algebraMap B _ b) = f b := by
  have hJ : ∀ n, ∀ b ∈ Ideal.span {(l : B)} ^ n,
      AdicCompletion.evalₐ (Ideal.span {(l : B)}) n (f b) = 0 := by
    intro n b hb
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]
    have hl : ((l : B ⧸ Ideal.span {(l : B)} ^ n)) ^ n = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : B)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    rw [hl, zero_mul]
  let ψ : ∀ n, B ⧸ Ideal.span {(l : B)} ^ n →+* B ⧸ Ideal.span {(l : B)} ^ n := fun n =>
    Ideal.Quotient.lift (Ideal.span {(l : B)} ^ n)
      ((AdicCompletion.evalₐ (Ideal.span {(l : B)}) n : _ →+* _).comp f) (hJ n)
  have hψ : ∀ n b, ψ n (Ideal.Quotient.mk _ b) =
      AdicCompletion.evalₐ (Ideal.span {(l : B)}) n (f b) := fun n b => rfl
  let F : ∀ n, AdicCompletion (Ideal.span {(l : B)}) B →+* B ⧸ Ideal.span {(l : B)} ^ n :=
    fun n => (ψ n).comp (AdicCompletion.evalₐ (Ideal.span {(l : B)}) n : _ →+* _)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (Ideal.span {(l : B)}) hle).comp (F n) = F m := by
    intro m n hle
    ext x
    obtain ⟨b, hb⟩ :=
      Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {(l : B)}) n x)
    simp only [F, RingHom.comp_apply, RingHom.coe_coe]
    rw [← factorPow_evalₐ_adic _ hle x, ← hb, hψ, factorPow_evalₐ_adic, Ideal.Quotient.factor_mk, hψ]
  refine ⟨AdicCompletion.liftRingHom _ F hF, fun b => ?_⟩
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [AdicCompletion.evalₐ_liftRingHom]
  simp only [F, RingHom.comp_apply, RingHom.coe_coe]
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, hψ]
  rfl

theorem exists_EE_extension {l : ℕ} {O : Type} [CommRing O] (ψ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hu : IsUnit (algebraMap O⟦X⟧ (EE O l) (ψ X))) :
    ∃ ψE : EE O l →ₐ[O] EE O l,
      ∀ a, ψE (algebraMap O⟦X⟧ (EE O l) a) = algebraMap O⟦X⟧ (EE O l) (ψ a) := by
  have hu' : IsUnit (((algebraMap O⟦X⟧ (EE O l)).comp (ψ : O⟦X⟧ →+* O⟦X⟧)) X) := hu
  obtain ⟨g, hg⟩ := exists_adicCompletion_extension l
    (IsLocalization.Away.lift (X : O⟦X⟧) (S := Localization.Away (X : O⟦X⟧)) hu')
  have key : ∀ a, g (algebraMap O⟦X⟧ (EE O l) a) = algebraMap O⟦X⟧ (EE O l) (ψ a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (EE O l), hg,
      IsLocalization.Away.lift_eq]
    rfl
  refine ⟨{ g with commutes' := fun c => ?_ }, key⟩
  show g (algebraMap O (EE O l) c) = algebraMap O (EE O l) c
  rw [IsScalarTower.algebraMap_apply O O⟦X⟧ (EE O l), key, AlgHom.commutes]

end GlobalTheory.NB.LT
end
