module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupMulPUnitFibreEqLevelOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexScaledUniformiser
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexScaledUniformiser
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem local_index_scaled : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (M : Matrix (Fin n) (Fin n) F) (d : ℕ), M.det ≠ 0 →
    (∀ i j, v.1 (M⁻¹ i j) ≤ WithZero.exp (d : ℤ)) →
    ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = n * d - ord v M.det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (d : ℤ)) → φ p = 0 →
        ∀ i, v.1 (M.mulVec p i) ≤ 1 := by
  intro k F _ _ _ _ _ hFF v n M d hM hMinv
  obtain ⟨hmul, hzpow, -, -, -, ⟨π, hπ0, hπ⟩, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v

  have hvπ : v.1 π = WithZero.exp (-1) := by
    have hne : v.1 π ≠ 0 := by simpa using hπ0
    have : WithZero.log (v.1 π) = -1 := by
      unfold ord at hπ; omega
    rw [← this, WithZero.exp_log hne]
  set c : F := π ^ d with hcdef
  have hc0 : c ≠ 0 := pow_ne_zero _ hπ0
  have hvc : v.1 c = WithZero.exp (-(d : ℤ)) := by
    rw [hcdef, map_pow, hvπ]
    show WithZero.exp (-1) ^ d = _
    rw [← WithZero.exp_nsmul]; congr 1; simp
  set h : Matrix (Fin n) (Fin n) F := c⁻¹ • M with hhdef
  have hdet : h.det = (c⁻¹) ^ n * M.det := by rw [hhdef, Matrix.det_smul, Fintype.card_fin]
  have hdet0 : h.det ≠ 0 := by rw [hdet]; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc0)) hM
  have hinv : h⁻¹ = c • M⁻¹ := by
    rw [hhdef]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM)]
  have hinvb : ∀ i j, v.1 (h⁻¹ i j) ≤ 1 := by
    intro i j
    rw [hinv, Matrix.smul_apply, smul_eq_mul, map_mul, hvc]
    calc WithZero.exp (-(d : ℤ)) * v.1 (M⁻¹ i j) ≤ WithZero.exp (-(d : ℤ)) * WithZero.exp (d : ℤ) :=
          by gcongr; exact hMinv i j
      _ = 1 := by rw [← WithZero.exp_add]; simp
  obtain ⟨N, φ₀, hN, hφ₀⟩ := GlobalTheory.T.functionFieldPlace_local_index_colength k F hFF v n h hdet0 hinvb

  have hord : ord v h.det = -(n * d : ℤ) + ord v M.det := by
    have e : (c⁻¹) ^ n = π ^ (-(n * d : ℤ)) := by
      rw [hcdef, inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
    rw [hdet, hmul _ _ (pow_ne_zero _ (inv_ne_zero hc0)) hM, e, hzpow π hπ0, hπ, mul_one]
  let sc : (Fin n → F) →ₗ[k] (Fin n → F) :=
    { toFun := fun p => c • p
      map_add' := fun p q => smul_add c p q
      map_smul' := fun a p => by
        ext i
        show c * (a • p i) = a • (c * p i)
        rw [Algebra.smul_def, Algebra.smul_def]; ring }
  refine ⟨N, φ₀ ∘ₗ sc, by rw [hN, hord]; ring, ?_⟩
  intro p hp hφ i
  have hx : ∀ i, v.1 ((c • p) i) ≤ 1 := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hvc]
    calc WithZero.exp (-(d : ℤ)) * v.1 (p i) ≤ WithZero.exp (-(d : ℤ)) * WithZero.exp (d : ℤ) :=
          by gcongr; exact hp i
      _ = 1 := by rw [← WithZero.exp_add]; simp
  have := hφ₀ (c • p) hx hφ i
  have e2 : h.mulVec (c • p) = M.mulVec p := by
    rw [hhdef, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rwa [e2] at this

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexScaledUniformiserStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldPlace_localIndex_scaled_uniformiser : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (M : Matrix (Fin n) (Fin n) F) (d : ℕ), M.det ≠ 0 →
    (∀ i j, v.1 (M⁻¹ i j) ≤ WithZero.exp (d : ℤ)) →
    ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = n * d - ord v M.det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (d : ℤ)) → φ p = 0 →
        ∀ i, v.1 (M.mulVec p i) ≤ 1 := by
  first | exact @GlobalTheory.Nef.local_index_scaled | exact GlobalTheory.Nef.local_index_scaled | (intros; apply GlobalTheory.Nef.local_index_scaled <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannInequalityCofinalFunctionField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsManyBoundedByPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsManyBoundedByPow
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.PolesOfT

open Polynomial

variable {k F : Type} [Field k] [Field F] [Algebra k F]

abbrev Mx (t : F) (v : Place k F) : WithZero (Multiplicative ℤ) := max 1 (v.1 t)

theorem one_le_Mx (t : F) (v : Place k F) : 1 ≤ Mx t v := le_max_left _ _

theorem val_aeval_le (t : F) (p : k[X]) (v : Place k F) :
    v.1 (aeval t p) ≤ Mx t v ^ p.natDegree := by
  rw [aeval_eq_sum_range]
  refine v.1.map_sum_le fun i hi => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : v.1 (algebraMap k F (p.coeff i)) ≤ 1 := by
    by_cases h : p.coeff i = 0
    · simp [h]
    · exact (v.2.2 _ h).le
  calc v.1 (algebraMap k F (p.coeff i)) * v.1 t ^ i ≤ 1 * Mx t v ^ i :=
        mul_le_mul' hc (pow_le_pow_left₀ zero_le' (le_max_right _ _) i)
    _ = Mx t v ^ i := one_mul _
    _ ≤ Mx t v ^ p.natDegree := pow_le_pow_right₀ (one_le_Mx t v) hi'

theorem val_le_of_monic (t y : F) (P : F[X]) (hP : P.Monic) (hy : P.eval y = 0) (c : ℕ)
    (v : Place k F) (hc : ∀ i < P.natDegree, v.1 (P.coeff i) ≤ Mx t v ^ c) :
    v.1 y ≤ Mx t v ^ c := by
  by_contra hlt
  push_neg at hlt
  have hM : 1 ≤ Mx t v ^ c := one_le_pow₀ (one_le_Mx t v)
  have hy1 : 1 < v.1 y := lt_of_le_of_lt hM hlt
  have hy0 : v.1 y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy1)
  rw [hP.as_sum, eval_add, eval_pow, eval_X, Polynomial.eval_finsetSum] at hy
  have heq := eq_neg_of_add_eq_zero_left hy
  have hlt2 : v.1 (∑ i ∈ Finset.range P.natDegree, (C (P.coeff i) * X ^ i).eval y) <
      v.1 y ^ P.natDegree := by
    refine v.1.map_sum_lt (pow_ne_zero _ hy0) fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [eval_mul, eval_C, eval_pow, eval_X, map_mul, map_pow]
    calc v.1 (P.coeff i) * v.1 y ^ i ≤ Mx t v ^ c * v.1 y ^ i := mul_le_mul' (hc i hi') le_rfl
      _ < v.1 y * v.1 y ^ i := mul_lt_mul_of_pos_right hlt (pow_pos (lt_trans zero_lt_one hy1) _)
      _ = v.1 y ^ (i + 1) := (pow_succ' _ _).symm
      _ ≤ v.1 y ^ P.natDegree := pow_le_pow_right₀ hy1.le hi'
  have h3 : v.1 (y ^ P.natDegree) = v.1 (∑ i ∈ Finset.range P.natDegree, (C (P.coeff i) * X ^ i).eval y) := by
    rw [heq, Valuation.map_neg]
  rw [map_pow] at h3
  rw [← h3] at hlt2
  exact lt_irrefl _ hlt2

end GlobalTheory.Nef.PolesOfT

namespace GlobalTheory.Nef.PolesOfT

open Polynomial

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem exists_mul_bdd (t y : F) (hy : IsAlgebraic k⟮t⟯ y) :
    ∃ q : k[X], aeval t q ≠ 0 ∧ ∃ c : ℕ, ∀ v : Place k F, v.1 (aeval t q * y) ≤ Mx t v ^ c := by
  classical
  obtain ⟨p, hp0, hpy⟩ := hy
  set A : Subalgebra k F := (aeval t : k[X] →ₐ[k] F).range with hA
  set P : F[X] := p.map (algebraMap k⟮t⟯ F) with hPdef
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap k⟮t⟯ F).injective).mpr hp0
  have hPy : P.eval y = 0 := by rw [hPdef, eval_map, ← aeval_def]; exact hpy
  have hcoef : ∀ i, ∃ s : k[X], aeval t s ≠ 0 ∧ aeval t s * P.coeff i ∈ A := by
    intro i
    rw [hPdef, coeff_map]
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff k (p.coeff i : F)).mp (p.coeff i).2
    by_cases hs : aeval t s = 0
    · refine ⟨1, by simp, ?_⟩
      have : algebraMap k⟮t⟯ F (p.coeff i) = 0 := by
        change (p.coeff i : F) = 0
        rw [hrs, hs, div_zero]
      rw [this, mul_zero]; exact A.zero_mem
    · refine ⟨s, hs, ?_⟩
      change aeval t s * (p.coeff i : F) ∈ A
      rw [hrs, mul_div_cancel₀ _ hs]
      exact ⟨r, rfl⟩
  choose s hs0 hsA using hcoef
  set D : F := ∏ i ∈ Finset.range (P.natDegree + 1), aeval t (s i) with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hs0 i
  set Q : F[X] := C D * P with hQdef
  have hQA : ∀ i, Q.coeff i ∈ A := by
    intro i
    rw [hQdef, coeff_C_mul]
    by_cases hi : i ∈ Finset.range (P.natDegree + 1)
    · rw [hD, ← Finset.prod_erase_mul _ _ hi, mul_assoc]
      refine A.mul_mem (A.prod_mem fun j _ => ⟨s j, rfl⟩) (hsA i)
    · have : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by
        simp only [Finset.mem_range, not_lt] at hi; omega)
      rw [this, mul_zero]; exact A.zero_mem
  have hQ0 : Q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hD0) hP0
  have hQy : Q.eval y = 0 := by rw [hQdef, eval_mul, hPy, mul_zero]
  set R : F[X] := integralNormalization Q with hRdef
  have hRmon : R.Monic := monic_integralNormalization hQ0
  have hRy : R.eval (Q.leadingCoeff * y) = 0 :=
    integralNormalization_eval₂_eq_zero (RingHom.id F) hQy (fun x hx => hx)
  have hRA : ∀ i, R.coeff i ∈ A := by
    intro i
    rw [hRdef, integralNormalization_coeff]
    split_ifs
    · exact A.one_mem
    · exact A.mul_mem (hQA i) (A.pow_mem (hQA _) _)
  choose pr hpr using hRA
  obtain ⟨q, hq⟩ := hQA Q.natDegree
  have hq' : aeval t q = Q.leadingCoeff := hq
  refine ⟨q, by rw [hq']; exact leadingCoeff_ne_zero.mpr hQ0,
    (Finset.range R.natDegree).sup fun i => (pr i).natDegree, fun v => ?_⟩
  rw [hq']
  refine val_le_of_monic t _ R hRmon hRy _ v fun i hi => ?_
  have h1 : R.coeff i = aeval t (pr i) := (hpr i).symm
  rw [h1]
  exact (val_aeval_le t (pr i) v).trans
    (pow_le_pow_right₀ (one_le_Mx t v) (Finset.le_sup (f := fun i => (pr i).natDegree) (Finset.mem_range.mpr hi)))

end GlobalTheory.Nef.PolesOfT

namespace GlobalTheory.Nef

open Polynomial PolesOfT

theorem exists_many_bounded_by_pow : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ t : F, Transcendental k t → ∃ c : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ ((N : ℤ) - c) * Module.finrank k⟮t⟯ F ≤ n ∧ ∀ (i : Fin n) (v : Place k F), v.1 (f i) ≤ max 1 (v.1 t) ^ N := by
  intro k F _ _ _ _ _ _ t ht
  by_cases hfin : FiniteDimensional k⟮t⟯ F
  swap
  · refine ⟨0, fun N => ⟨0, Fin.elim0, linearIndependent_empty_type, ?_, fun i => i.elim0⟩⟩
    rw [Module.finrank_of_infinite_dimensional hfin]; simp
  set d := Module.finrank k⟮t⟯ F with hd
  let b := Module.finBasis k⟮t⟯ F
  have halg : ∀ j, IsAlgebraic k⟮t⟯ (b j) := fun j => Algebra.IsAlgebraic.isAlgebraic _
  choose q hq0 cj hcj using fun j => exists_mul_bdd t (b j) (halg j)
  refine ⟨Finset.univ.sup cj, fun N => ?_⟩
  set c := Finset.univ.sup cj with hc
  set L := N - c with hL
  let w : Fin d → k⟮t⟯ := fun j => aeval (IntermediateField.AdjoinSimple.gen k t) (q j)
  have hw : ∀ j, algebraMap k⟮t⟯ F (w j) = aeval t (q j) := fun j => by
    simp only [w]; rw [← aeval_algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen]
  have hw0 : ∀ j, w j ≠ 0 := fun j h => hq0 j (by rw [← hw j, h, map_zero])
  let y : Fin d → F := fun j => aeval t (q j) * b j
  have hyli : LinearIndependent k⟮t⟯ y := by
    have := b.linearIndependent.units_smul (fun j => Units.mk0 (w j) (hw0 j))
    convert this using 1
    funext j
    simp [y, Algebra.smul_def, hw]
  have hpowF : LinearIndependent k (fun n : ℕ => t ^ n) := by
    have h1 := (Polynomial.basisMonomials k).linearIndependent.map' (aeval t).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp ht))
    have heq : (fun n : ℕ => t ^ n) = (aeval t).toLinearMap ∘ Polynomial.basisMonomials k := by
      funext n
      simp [Polynomial.coe_basisMonomials]
    rw [heq]
    exact h1
  have hpow : LinearIndependent k (fun i : Fin L => (IntermediateField.AdjoinSimple.gen k t) ^ (i : ℕ)) := by
    have heq : (IsScalarTower.toAlgHom k k⟮t⟯ F).toLinearMap ∘
        (fun i : Fin L => (IntermediateField.AdjoinSimple.gen k t) ^ (i : ℕ)) =
        (fun n : ℕ => t ^ n) ∘ (fun i : Fin L => (i : ℕ)) := by
      funext i
      simp
    apply LinearIndependent.of_comp (IsScalarTower.toAlgHom k k⟮t⟯ F).toLinearMap
    rw [heq]
    exact hpowF.comp _ Fin.val_injective
  have hprod := linearIndependent_smul hpow hyli
  refine ⟨L * d, fun i => (fun p : Fin L × Fin d => (IntermediateField.AdjoinSimple.gen k t) ^ (p.1 : ℕ) • y p.2)
    (finProdFinEquiv.symm i), hprod.comp _ finProdFinEquiv.symm.injective, ?_, ?_⟩
  · push_cast
    have h1 : ((N : ℤ) - c) ≤ (L : ℤ) := by omega
    exact mul_le_mul_of_nonneg_right h1 (Int.natCast_nonneg _)
  · intro i v
    dsimp only
    generalize finProdFinEquiv.symm i = p
    obtain ⟨a, j⟩ := p
    have hsm : (IntermediateField.AdjoinSimple.gen k t) ^ (a : ℕ) • y j = t ^ (a : ℕ) * (aeval t (q j) * b j) := by
      rw [Algebra.smul_def, map_pow, IntermediateField.AdjoinSimple.algebraMap_gen]
    dsimp only
    rw [hsm, map_mul, map_pow]
    have ha : (a : ℕ) + c ≤ N := by have := a.2; omega
    calc v.1 t ^ (a : ℕ) * v.1 (aeval t (q j) * b j) ≤ Mx t v ^ (a : ℕ) * Mx t v ^ c :=
          mul_le_mul' (pow_le_pow_left₀ zero_le' (le_max_right _ _) _)
            ((hcj j v).trans (pow_le_pow_right₀ (one_le_Mx t v) (Finset.le_sup (Finset.mem_univ j))))
      _ = Mx t v ^ ((a : ℕ) + c) := (pow_add _ _ _).symm
      _ ≤ max 1 (v.1 t) ^ N := pow_le_pow_right₀ (one_le_Mx t v) ha

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsManyBoundedByPowStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearIndependent_bounded_by_pow_of_transcendental : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ t : F, Transcendental k t → ∃ c : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ ((N : ℤ) - c) * Module.finrank k⟮t⟯ F ≤ n ∧ ∀ (i : Fin n) (v : Place k F), v.1 (f i) ≤ max 1 (v.1 t) ^ N := by
  first | exact @GlobalTheory.Nef.exists_many_bounded_by_pow | exact GlobalTheory.Nef.exists_many_bounded_by_pow | (intros; apply GlobalTheory.Nef.exists_many_bounded_by_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannInequalityCofinalFunctionField
open scoped IntermediateField Polynomial RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

namespace RiemannCofinal

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem val_ne_zero (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≠ 0 :=
  (Valuation.ne_zero_iff _).2 hx

theorem ord_mul (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul (val_ne_zero v hx) (val_ne_zero v hy)]
  ring

theorem ord_inv (v : Place k F) (x : F) : ord v x⁻¹ = -ord v x := by
  unfold ord
  rw [map_inv₀, WithZero.log_inv]

theorem ord_pow (v : Place k F) (x : F) (n : ℕ) : ord v (x ^ n) = n * ord v x := by
  unfold ord
  rw [map_pow, WithZero.log_pow]
  simp

theorem ord_one (v : Place k F) : ord v 1 = 0 := by simp [ord]

theorem ord_le_ord (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (h : v.1 x ≤ v.1 y) :
    ord v y ≤ ord v x := by
  unfold ord
  have := (WithZero.log_le_log (val_ne_zero v hx) (val_ne_zero v hy)).2 h
  omega

theorem le_one_iff (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≤ 1 ↔ 0 ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (val_ne_zero v hx) one_ne_zero, WithZero.log_one]
  constructor <;> intro <;> omega

theorem lt_one_iff (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x < 1 ↔ 0 < ord v x := by
  unfold ord
  rw [← WithZero.log_lt_log (val_ne_zero v hx) one_ne_zero, WithZero.log_one]
  constructor <;> intro <;> omega

theorem ord_prod {ι : Type} (v : Place k F) (s : Finset ι) (x : ι → F) (hx : ∀ i ∈ s, x i ≠ 0) :
    ord v (∏ i ∈ s, x i) = ∑ i ∈ s, ord v (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ord_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul v (hx a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

theorem val_algebraMap_le (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [v.2.2 c hc]

end RiemannCofinal

end GlobalTheory.Nef

namespace GlobalTheory.Nef

open RiemannCofinal

theorem riemann_cofinal : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ D : Place k F →₀ ℤ, ∃ D' : Place k F →₀ ℤ, D ≤ D' ∧ ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ (D'.sum fun _ m => m) - γ ≤ n ∧ ∀ (i : Fin n) (v : Place k F), -D' v ≤ ord v (f i) := by
  intro k F _ _ _ _ _ hFF
  classical
  obtain ⟨t, ht, -⟩ := id hFF
  have ht0 : t ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
  have hti : Transcendental k t⁻¹ := fun h => ht (IsAlgebraic.inv_iff.1 h)
  have hadj : k⟮t⁻¹⟯ = k⟮t⟯ := le_antisymm
    (IntermediateField.adjoin_simple_le_iff.2 (inv_mem (IntermediateField.mem_adjoin_simple_self k t)))
    (IntermediateField.adjoin_simple_le_iff.2
      (by simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)))
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_linearIndependent_bounded_by_pow_of_transcendental k F hFF t ht
  obtain ⟨hPfin, hPdeg⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hFF t⁻¹ hti
  rw [hadj] at hPdeg
  refine ⟨c * Module.finrank k⟮t⟯ F, fun D => ?_⟩

  have hpole : ∀ w : Place k F, ¬ w.1 t ≤ 1 ↔ w.1 t⁻¹ < 1 := by
    intro w
    rw [lt_one_iff w (inv_ne_zero ht0), ord_inv, le_one_iff w ht0]
    constructor <;> intro <;> omega

  have hres : ∀ v : Place k F, v.1 t ≤ 1 → ∃ a : k, v.1 (t - algebraMap k F a) < 1 :=
    fun v => (GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground k F hFF v).2 t
  obtain ⟨r, hr⟩ : ∃ r : Place k F → k, ∀ v : Place k F, v.1 t ≤ 1 → v.1 (t - algebraMap k F (r v)) < 1 :=
    ⟨fun v => if h : v.1 t ≤ 1 then (hres v h).choose else 0, fun v h => by
      simp only [dif_pos h]; exact (hres v h).choose_spec⟩
  have hlin0 : ∀ a : k, t - algebraMap k F a ≠ 0 := fun a h =>
    ht (sub_eq_zero.1 h ▸ isAlgebraic_algebraMap a)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ∑ v ∈ D.support, (D v).natAbs := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : F, h = ∏ v ∈ D.support, (t - algebraMap k F (r v)) ^ (D v).natAbs :=
    ⟨_, rfl⟩
  have hh0 : h ≠ 0 := hh ▸ Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hlin0 _)
  have hordh : ∀ w : Place k F,
      ord w h = ∑ v ∈ D.support, ((D v).natAbs : ℤ) * ord w (t - algebraMap k F (r v)) := by
    intro w
    rw [hh, ord_prod w _ _ (fun v _ => pow_ne_zero _ (hlin0 _))]
    exact Finset.sum_congr rfl fun v _ => ord_pow w _ _
  obtain ⟨hhfin, hhsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF h hh0
  obtain ⟨n, f, hli, hn, hf⟩ := hc (2 * M)
  obtain ⟨P, hP⟩ : ∃ P : Place k F → ℤ,
      P = {v : Place k F | v.1 t⁻¹ < 1}.indicator fun v => ord v t⁻¹ := ⟨_, rfl⟩
  have hPpole : ∀ w : Place k F, ¬ w.1 t ≤ 1 → P w = -ord w t := by
    intro w hw
    rw [hP, Set.indicator_of_mem (show w ∈ {v : Place k F | v.1 t⁻¹ < 1} from (hpole w).1 hw),
      ord_inv]
  have hPint : ∀ w : Place k F, w.1 t ≤ 1 → P w = 0 := by
    intro w hw
    rw [hP, Set.indicator_of_notMem (show w ∉ {v : Place k F | v.1 t⁻¹ < 1} from
      fun h' => (hpole w).2 h' hw)]
  have hPsupp : Function.support P ⊆ {v : Place k F | v.1 t⁻¹ < 1} := by
    intro w hw
    by_contra hw'
    exact hw (hPint w (by by_contra h'; exact hw' ((hpole w).1 h')))
  have hhsupp : Function.support (fun v : Place k F => ord v h) ⊆ {v : Place k F | v.1 h ≠ 1} := by
    intro v hv hv1
    exact hv (show ord v h = 0 by simp [ord, hv1])
  obtain ⟨g, hg⟩ : ∃ g : Place k F → ℤ, g = fun v => ((2 * M : ℕ) : ℤ) * P v + ord v h := ⟨_, rfl⟩
  have hgfin : (Function.support g).Finite := by
    refine (hPfin.union hhfin).subset fun v hv => ?_
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
    apply hv
    have h1 : P v = 0 := by
      by_contra h'; exact hnot.1 (hPsupp h')
    have h2 : ord v h = 0 := by simp [ord, hnot.2]
    simp [hg, h1, h2]
  refine ⟨Finsupp.ofSupportFinite g hgfin, ?_, n, fun i => f i * h⁻¹, ?_, ?_, ?_⟩
  ·
    intro w
    show D w ≤ g w
    simp only [hg]
    have hDM : D w ≤ (M : ℤ) := by
      by_cases hw : w ∈ D.support
      · have h1 := Finset.single_le_sum (f := fun v => (D v).natAbs) (fun _ _ => Nat.zero_le _) hw
        have h2 : D w ≤ ((D w).natAbs : ℤ) := Int.le_natAbs
        rw [hM]
        have h3 : (((D w).natAbs : ℕ) : ℤ) ≤ ((∑ v ∈ D.support, (D v).natAbs : ℕ) : ℤ) :=
          Nat.cast_le.2 h1
        omega
      · rw [Finsupp.notMem_support_iff.1 hw]; positivity
    by_cases ht1 : w.1 t ≤ 1
    · have hnn : ∀ v, 0 ≤ ord w (t - algebraMap k F (r v)) := fun v =>
        (le_one_iff w (hlin0 _)).1
          ((Valuation.map_sub _ _ _).trans (max_le ht1 (val_algebraMap_le w _)))
      simp only [hPint w ht1, mul_zero, zero_add, hordh w]
      by_cases hw : w ∈ D.support
      · have hone : 0 < ord w (t - algebraMap k F (r w)) := (lt_one_iff w (hlin0 _)).1 (hr w ht1)
        have h2 : D w ≤ ((D w).natAbs : ℤ) := Int.le_natAbs
        have h3 := Finset.single_le_sum
          (f := fun v => ((D v).natAbs : ℤ) * ord w (t - algebraMap k F (r v)))
          (fun v _ => mul_nonneg (by positivity) (hnn v)) hw
        have h4 : ((D w).natAbs : ℤ) ≤ ((D w).natAbs : ℤ) * ord w (t - algebraMap k F (r w)) := by
          nlinarith
        omega
      · rw [Finsupp.notMem_support_iff.1 hw]
        exact Finset.sum_nonneg fun v _ => mul_nonneg (by positivity) (hnn v)
    · have hge : ∀ v, ord w t ≤ ord w (t - algebraMap k F (r v)) := fun v =>
        ord_le_ord w (hlin0 _) ht0 ((Valuation.map_sub _ _ _).trans
          (max_le le_rfl ((val_algebraMap_le w _).trans (le_of_lt (not_le.1 ht1)))))
      have hsum : (M : ℤ) * ord w t ≤ ord w h := by
        rw [hordh, hM]
        push_cast
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hge v) (by positivity)
      have hneg : ord w t < 0 := by
        have := (le_one_iff w ht0).not.1 ht1
        omega
      rw [hPpole w ht1]
      push_cast
      have hM0 : (0 : ℤ) ≤ M := by positivity
      nlinarith
  ·
    exact hli.map' (LinearMap.mulRight k h⁻¹)
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (inv_ne_zero hh0)))
  ·
    have hsub : Function.support g ⊆ ↑(Finsupp.ofSupportFinite g hgfin).support := by
      intro v hv
      exact Finsupp.mem_support_iff.2 hv
    have hdeg : ((Finsupp.ofSupportFinite g hgfin).sum fun _ m => m) =
        ((2 * M : ℕ) : ℤ) * Module.finrank k⟮t⟯ F := by
      have h1 : ((Finsupp.ofSupportFinite g hgfin).sum fun _ m => m) = ∑ᶠ v, g v := by
        rw [finsum_eq_sum_of_support_subset g hsub]
        rfl
      have hPsum : ∑ᶠ v, P v = Module.finrank k⟮t⟯ F := by
        rw [finsum_mem_def] at hPdeg
        rw [hP]; exact hPdeg
      rw [h1, hg]
      rw [finsum_add_distrib
        ((hPfin.subset hPsupp).subset fun v hv h0 => hv (by simp [h0]))
        (hhfin.subset hhsupp), ← mul_finsum, hhsum, hPsum, add_zero]
    rw [hdeg]
    push_cast
    calc ((2 * M : ℕ) : ℤ) * Module.finrank k⟮t⟯ F - c * Module.finrank k⟮t⟯ F
        = (((2 * M : ℕ) : ℤ) - c) * Module.finrank k⟮t⟯ F := by ring
      _ ≤ n := hn
  ·
    intro i w
    have hfi : f i ≠ 0 := hli.ne_zero i
    show -(g w) ≤ ord w (f i * h⁻¹)
    rw [ord_mul w hfi (inv_ne_zero hh0), ord_inv, hg]
    have key : -(((2 * M : ℕ) : ℤ) * P w) ≤ ord w (f i) := by
      by_cases ht1 : w.1 t ≤ 1
      · have h1 : w.1 (f i) ≤ 1 := by simpa [max_eq_left ht1] using hf i w
        rw [hPint w ht1]
        simpa using (le_one_iff w hfi).1 h1
      · have h1 : w.1 (f i) ≤ w.1 (t ^ (2 * M)) := by
          rw [map_pow]; simpa [max_eq_right (le_of_lt (not_le.1 ht1))] using hf i w
        have := ord_le_ord w hfi (pow_ne_zero _ ht0) h1
        rw [ord_pow] at this
        rw [hPpole w ht1]
        push_cast at this ⊢
        linarith
    simp only
    linarith

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannInequalityCofinalFunctionFieldStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_inequality_cofinal_functionField : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ D : Place k F →₀ ℤ, ∃ D' : Place k F →₀ ℤ, D ≤ D' ∧ ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ (D'.sum fun _ m => m) - γ ≤ n ∧ ∀ (i : Fin n) (v : Place k F), -D' v ≤ ord v (f i) := by
  first | exact @GlobalTheory.Nef.riemann_cofinal | exact GlobalTheory.Nef.riemann_cofinal | (intros; apply GlobalTheory.Nef.riemann_cofinal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroLinearCombinationMemCommonKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroLinearCombinationMemCommonKernel
open GlobalTheory.Nef

namespace GlobalTheory

theorem exists_ne_zero_comb_mem_ker :
    ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by
  intro k F ι _ _ _ n m f hf S N ψ hlt
  let T : (Fin n → Fin m → k) →ₗ[k] (Fin n → F) :=
    { toFun := fun c i => ∑ j, c i j • f j
      map_add' := by
        intro a b; funext i; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a; funext i; simp [Finset.smul_sum, smul_smul] }
  have hT : ∀ c, T c = fun i => ∑ j, c i j • f j := fun c => rfl
  let Ψ : (Fin n → Fin m → k) →ₗ[k] ((v : S) → Fin (N v) → k) :=
    LinearMap.pi fun v => (ψ v).comp T
  have hlt' : Module.finrank k ((v : S) → Fin (N v) → k) < Module.finrank k (Fin n → Fin m → k) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fin_fun]
    rw [Finset.sum_coe_sort S (fun v => N v), Module.finrank_pi_fintype]
    simpa [Module.finrank_fin_fun] using hlt
  have hk : LinearMap.ker Ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt'
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hk
  refine ⟨c, ?_, ?_⟩
  · intro h0
    apply hc0
    funext i j
    have hi : ∑ j, c i j • f j = 0 := congrFun h0 i
    exact Fintype.linearIndependent_iff.1 hf (c i) hi j
  · intro v hv
    have := congrFun (LinearMap.mem_ker.1 hc) ⟨v, hv⟩
    simpa [Ψ, hT] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroLinearCombinationMemCommonKernelStatement
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel : ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by
  first | exact @GlobalTheory.exists_ne_zero_comb_mem_ker | exact GlobalTheory.exists_ne_zero_comb_mem_ker | (intros; apply GlobalTheory.exists_ne_zero_comb_mem_ker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfLargeAdelicDegree
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem val_le_exp_of_ord (v : Place k F) (x : F) (d : ℤ) (hd : 0 ≤ d) (h : -d ≤ ord v x) :
    v.1 x ≤ WithZero.exp d := by
  by_cases hx : v.1 x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    unfold ord at h; omega

theorem val_algebraMap_le_one (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

theorem val_comb_le (v : Place k F) {m : ℕ} (f : Fin m → F) (c : Fin m → k)
    (B : WithZero (Multiplicative ℤ)) (h : ∀ j, v.1 (f j) ≤ B) : v.1 (∑ j, c j • f j) ≤ B := by
  apply v.1.map_sum_le
  intro j _
  rw [Algebra.smul_def, map_mul]
  calc v.1 (algebraMap k F (c j)) * v.1 (f j) ≤ 1 * B := mul_le_mul' (val_algebraMap_le_one v _) (h j)
    _ = B := one_mul B

theorem val_mulVec_le_one (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (hM : ∀ i j, v.1 (M i j) ≤ 1) (p : Fin n → F) (hp : ∀ i, v.1 (p i) ≤ 1) (i : Fin n) :
    v.1 (M.mulVec p i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  apply v.1.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (M i j) * v.1 (p j) ≤ 1 * 1 := mul_le_mul' (hM i j) (hp j)
    _ = 1 := one_mul 1

theorem exists_exp_bound (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    ∃ d : ℕ, ∀ i j, v.1 (M i j) ≤ WithZero.exp (d : ℤ) := by
  refine ⟨Finset.univ.sup fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat,
    fun i j => ?_⟩
  by_cases hx : v.1 (M i j) = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    have := Finset.le_sup (f := fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat)
      (Finset.mem_univ (i, j))
    simp only at this
    omega

theorem exists_section_of_large_deg : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → (n : ℤ) * γ < deg g → ∃ p : Fin n → F, p ≠ 0 ∧ ∀ (v : Place k F) (i : Fin n), v.1 ((g v).mulVec p i) ≤ 1 := by
  intro k F _ _ _ _ _ hFF
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.riemann_inequality_cofinal_functionField k F hFF
  refine ⟨γ, fun n g hg hdeg => ?_⟩
  classical
  set B := hg.2.toFinset with hBdef
  choose d0 hd0 using fun v => exists_exp_bound v (g v)⁻¹
  let D : Place k F →₀ ℤ := Finsupp.onFinset B (fun v => if v ∈ B then (d0 v : ℤ) else 0)
    (by intro v hv; by_contra h; exact hv (if_neg h))
  obtain ⟨D', hDD', m, f, hf, hm, hford⟩ := hγ D
  have hD0 : ∀ v, 0 ≤ D' v := fun v => le_trans
    (by simp only [D, Finsupp.onFinset_apply]; split_ifs <;> omega) (hDD' v)
  have hloc : ∀ v, ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)),
      (N : ℤ) = n * ((D' v).toNat : ℕ) - ord v (g v).det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ)) → φ p = 0 →
        ∀ i, v.1 ((g v).mulVec p i) ≤ 1 := by
    intro v
    refine GlobalTheory.T.functionFieldPlace_localIndex_scaled_uniformiser k F hFF v n (g v) _ (hg.1 v) ?_
    intro i j
    by_cases hv : v ∈ B
    · have hDv : D v = d0 v := by simp [D, Finsupp.onFinset_apply, hv]
      calc v.1 ((g v)⁻¹ i j) ≤ WithZero.exp (d0 v : ℤ) := hd0 v i j
        _ ≤ _ := by
          rw [WithZero.exp_le_exp]; have := hDD' v; rw [hDv] at this; omega
    · have hU : Unimod v (g v) := by simpa [B] using hv
      have hU' := ((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.2 n (g v) (g v) hU hU).2
      calc v.1 ((g v)⁻¹ i j) ≤ 1 := hU'.1 i j
        _ = WithZero.exp 0 := rfl
        _ ≤ _ := by rw [WithZero.exp_le_exp]; omega
  choose N φ hN hφ using hloc
  set S := B ∪ D'.support with hS
  have hsumD : D'.sum (fun _ m => m) = ∑ v ∈ S, D' v := by
    unfold Finsupp.sum
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hv; simpa using hv
  have hdegS : deg g = ∑ v ∈ S, ord v (g v).det := by
    unfold deg
    apply finsum_eq_sum_of_support_subset
    intro v hv
    rw [Finset.coe_union]; left
    simp only [B, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro hU; apply hv
    simp [ord, hU.2]
  have hNsum : ((∑ v ∈ S, N v : ℕ) : ℤ) < n * m := by
    push_cast
    rw [Finset.sum_congr rfl (fun v _ => hN v), Finset.sum_sub_distrib, ← Finset.mul_sum]
    have : ∀ v, (((D' v).toNat : ℕ) : ℤ) = D' v := fun v => Int.toNat_of_nonneg (hD0 v)
    simp_rw [this]
    rw [← hsumD, ← hdegS]
    have := mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg n)
    nlinarith
  obtain ⟨c, hp0, hpψ⟩ := GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel k F (Place k F) n m f hf S N φ (by exact_mod_cast hNsum)
  refine ⟨_, hp0, fun v i => ?_⟩
  have hpb : ∀ i, v.1 (∑ j, c i j • f j) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ) := fun i =>
    val_comb_le v f (c i) _ (fun j => val_le_exp_of_ord v _ _ (by omega)
      (by rw [Int.toNat_of_nonneg (hD0 v)]; exact hford j v))
  by_cases hv : v ∈ S
  · exact hφ v _ hpb (hpψ v hv) i
  · have hvB : v ∉ B := fun h => hv (Finset.mem_union_left _ h)
    have hD'v : D' v = 0 := by
      by_contra h; exact hv (Finset.mem_union_right _ (Finsupp.mem_support_iff.2 h))
    have hU : Unimod v (g v) := by simpa [B] using hvB
    apply val_mulVec_le_one v _ hU.1
    intro i; have := hpb i; rw [hD'v] at this; simpa using this

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfLargeAdelicDegreeStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_large_adelic_degree : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → (n : ℤ) * γ < deg g → ∃ p : Fin n → F, p ≠ 0 ∧ ∀ (v : Place k F) (i : Fin n), v.1 ((g v).mulVec p i) ≤ 1 := by
  first | exact @GlobalTheory.Nef.exists_section_of_large_deg | exact GlobalTheory.Nef.exists_section_of_large_deg | (intros; apply GlobalTheory.Nef.exists_section_of_large_deg <;> assumption)
end
