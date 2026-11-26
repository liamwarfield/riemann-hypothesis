module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralVandermondeMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagIntegralVandermondeMul.proof (h1 : FlagIntegralTopComponent.Statement)
    (h2 : FlagHomogeneousComponentMul.Statement) (h3 : FlagVandermondeHomogeneous.Statement) :
    FlagIntegralVandermondeMul.Statement := by
  intro f N R
  rw [h1 f N (blockVandermonde f N * R),
    h2 _ (blockVandermonde f N) R (topDegree f N) (topDegree f N) (h3 f N),
    if_pos le_rfl, Nat.sub_self, homogeneousComponent_zero, mul_comm,
    Flag.flagIntegral_C_mul, constantCoeff_eq]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityRowsPerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchRootOfUnityRowsPerm.proof : SchRootOfUnityRowsPerm.Statement := by
  intro k l π hk hl
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hζk : rootOfUnity k ^ k = 1 := by
    unfold rootOfUnity
    exact (Complex.isPrimitiveRoot_exp k hk0).pow_eq_one
  have hmod : ∀ j n : ℕ, rootOfUnity k ^ (j * n) = rootOfUnity k ^ (j * (n % k)) := by
    intro j n
    conv_lhs => rw [← Nat.mod_add_div n k]
    rw [mul_add, pow_add, mul_left_comm j k, pow_mul (rootOfUnity k) k, hζk, one_pow, mul_one]
  have hM : (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)) =
      (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).submatrix π id := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
    rw [hmod, hl i]
  rw [hM, Matrix.det_permute]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDividedDifferencePoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagDividedDifferencePoly.proof (h1 : FlagVandermondeDvd.Statement) :
    FlagDividedDifferencePoly.Statement := by
  intro f N H
  obtain ⟨R, hR⟩ := h1 f N _ (isBlockAlternating_antisymmetrize f N H)
  refine ⟨R, hR, fun w => ?_⟩
  have h := isBlockAlternating_antisymmetrize f N H w
  rw [hR, map_mul, Flag.blockPermute_blockVandermonde, smul_mul_assoc] at h
  have hs : blockSign f N w ≠ 0 := by
    intro h0
    have := Flag.blockSign_mul_self f N w
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ (Flag.blockVandermonde_ne_zero f N) (smul_right_injective _ hs h)

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralViaQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagIntegralViaQuotient.proof (h1 : FlagIntegralAntisymmetrize.Statement)
    (h2 : FlagIntegralVandermondeMul.Statement) : FlagIntegralViaQuotient.Statement := by
  intro f N H R hR
  have hA := h1 f N H
  rw [hR, h2 f N R] at hA
  have hne : (N.factorial : ℚ) ^ f ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  linear_combination -hA

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityRowsEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Complex

theorem rootOfUnity_pow_self (k : ℕ) (hk : k ≠ 0) : rootOfUnity k ^ k = 1 :=
  (Complex.isPrimitiveRoot_exp k hk).pow_eq_one

theorem rootOfUnity_pow_mod (k : ℕ) (hk : k ≠ 0) (a : ℕ) :
    rootOfUnity k ^ a = rootOfUnity k ^ (a % k) := by
  conv_lhs => rw [← Nat.mod_add_div a k, pow_add, pow_mul, rootOfUnity_pow_self k hk, one_pow,
    mul_one]

theorem SchRootOfUnityRowsEq.proof : SchRootOfUnityRowsEq.Statement := by
  intro k l i i' hne hmod
  have hk : k ≠ 0 := by
    rintro rfl
    exact i.elim0
  apply Matrix.det_zero_of_row_eq hne
  funext j
  simp only [Matrix.of_apply]
  rw [pow_mul', pow_mul', rootOfUnity_pow_mod k hk (l i), rootOfUnity_pow_mod k hk (l i'), hmod]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityBialternant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem aeval_vandermondeOf_X {m : ℕ} (v : Fin m → ℂ) :
    aeval v (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ))) = vandermondeOf v := by
  simp [vandermondeOf, map_prod, map_sub, aeval_X]

theorem SchRootOfUnityBialternant.proof (h1 : SchSchurEvalMatrix.Statement) :
    SchRootOfUnityBialternant.Statement := by
  intro k nu hk
  have hw : ∀ j : Fin k, rootOfUnityPoint k k j = rootOfUnity k ^ (j : ℕ) := fun j => by
    simp [rootOfUnityPoint, j.isLt]
  have key := congrArg (aeval (rootOfUnityPoint k k)) (Schur.det_pow_add_staircase_eq nu)
  rw [map_mul, h1 k k k nu hk le_rfl, AlgHom.map_det, aeval_vandermondeOf_X] at key
  have hv : rootOfUnityPoint k k = fun i : Fin k => rootOfUnity k ^ (i : ℕ) := funext hw
  rw [hv] at key
  rw [← key]
  congr 1
  ext i j
  simp [AlgHom.mapMatrix_apply, Matrix.map_apply, aeval_X, ← pow_mul]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAntisymDecomposition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem antisymmetrize_finset_sum (f N : ℕ) {ι : Type*} (s : Finset ι) (g : ι → RootRing f N) :
    antisymmetrize f N (∑ i ∈ s, g i) = ∑ i ∈ s, antisymmetrize f N (g i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [antisymmetrize, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

theorem FlagAntisymDecomposition.proof (h1 : FlagSymmetricMulAntisym.Statement)
    (h2 : FlagPowerSumSymmetric.Statement) : FlagAntisymDecomposition.Statement := by
  intro f N F G Q R hF hR
  rw [hF, Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_left_comm, h1 f N _ _ (h2 f N l σ), hR, mul_left_comm]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagStaircaseOrbit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

noncomputable section

theorem FlagStaircaseOrbit.bijective_of_injective {f N : ℕ} (γ : Fin f × Fin N →₀ ℕ) (τ : Fin f)
    (hlt : ∀ i, γ (τ, i) < N) (hinj : Function.Injective fun i : Fin N => γ (τ, i)) :
    Function.Bijective fun i : Fin N => (⟨γ (τ, i), hlt i⟩ : Fin N) := by
  refine Finite.injective_iff_bijective.mp ?_
  intro i j h
  exact hinj (congrArg Fin.val h)

theorem FlagStaircaseOrbit.proof : FlagStaircaseOrbit.Statement := by
  intro f N α β hα hβ iα iβ
  let A : Fin f → (Fin N ≃ Fin N) := fun τ =>
    Equiv.ofBijective _ (FlagStaircaseOrbit.bijective_of_injective α τ (hα τ) (iα τ))
  let B : Fin f → (Fin N ≃ Fin N) := fun τ =>
    Equiv.ofBijective _ (FlagStaircaseOrbit.bijective_of_injective β τ (hβ τ) (iβ τ))
  refine ⟨fun τ => (B τ).trans (A τ).symm, fun τ i => ?_⟩
  have h : A τ ((A τ).symm (B τ i)) = B τ i := Equiv.apply_symm_apply _ _
  have h' := congrArg Fin.val h
  exact h'

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralTopDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagIntegralTopDegree.proof (h1 : FlagAltTopDegree.Statement)
    (h2 : FlagAntisymHomogeneous.Statement) (h3 : FlagIntegralViaQuotient.Statement) :
    FlagIntegralTopDegree.Statement := by
  intro f N H hH
  obtain ⟨e, he⟩ := h1 f N (antisymmetrize f N H) (isBlockAlternating_antisymmetrize f N H)
    (h2 f N H _ hH)
  have hI := h3 f N H (C e) (by rw [he, mul_comm])
  rw [constantCoeff_C] at hI
  have hΔ : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (RootRing f N) (FractionRing (RootRing f N)))).mpr
      (Flag.blockVandermonde_ne_zero f N)
  have hdd : dividedDifference f N H = algebraMap ℚ (FractionRing (RootRing f N)) e := by
    rw [dividedDifference, he, map_mul, mul_div_assoc, div_self hΔ, mul_one,
      IsScalarTower.algebraMap_apply ℚ (RootRing f N) (FractionRing (RootRing f N)),
      MvPolynomial.algebraMap_eq]
  rw [hdd, ← map_mul, hI]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictSymmetric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem rename_comp_restrictToBlock (f N : ℕ) (τ : Fin f) (π : Equiv.Perm (Fin N)) :
    (rename π).comp (restrictToBlock f N τ) =
      (restrictToBlock f N τ).comp (blockPermute f N (Function.update 1 τ π)) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨σ, i⟩
  by_cases h : σ = τ
  · subst h
    simp [restrictToBlock, blockPermute]
  · simp [restrictToBlock, blockPermute, h]

theorem FlagRestrictSymmetric.proof : FlagRestrictSymmetric.Statement := by
  intro f N τ R hR π
  have key := congrArg (fun φ : RootRing f N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ R)
    (rename_comp_restrictToBlock f N τ π)
  simp only [AlgHom.comp_apply] at key
  rw [key, hR]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchPowerSumHomWeighted
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem psum_isHomogeneous_alt (N j : ℕ) : (psum (Fin N) ℚ j).IsHomogeneous j :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i j

theorem SchPowerSumHomWeighted.proof : SchPowerSumHomWeighted.Statement := by
  intro N d S hS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [S.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun e he => ?_
  have hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = d :=
    hS (mem_support_iff.mp he)
  rw [powerSumHom, aeval_monomial, Finsupp.prod, algebraMap_eq]
  have hprod : (∏ i ∈ e.support, psum (Fin N) ℚ ((i : ℕ) + 1) ^ e i).IsHomogeneous
      (∑ i ∈ e.support, ((i : ℕ) + 1) * e i) :=
    IsHomogeneous.prod _ _ _ fun i _ => (psum_isHomogeneous_alt N ((i : ℕ) + 1)).pow (e i)
  have hsum : ∑ i ∈ e.support, ((i : ℕ) + 1) * e i = d := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hsum] at hprod
  exact hprod.C_mul _

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAevalSignedRename
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchAevalSignedRename.proof : SchAevalSignedRename.Statement := by
  intro ι κ _ _ _ _ s g d P hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hd : (∑ i ∈ e.support, e i) = d := by
    have h := hP (mem_support_iff.mp he)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [rename_monomial, aeval_monomial, monomial_eq, Finsupp.prod_mapDomain_index
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [algebraMap_eq, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← C_pow]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum, hd]
  ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagQuotientHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem FlagQuotientHomogeneous.proof : FlagQuotientHomogeneous.Statement := by
  intro σ A R m k hA0 hA hAR
  have hzero : ∀ j, j ≠ k → homogeneousComponent j R = 0 := by
    intro j hj
    have h1 := HomogeneousComponentMul.proof σ ℚ A R m (m + j) hA
    rw [if_pos (Nat.le_add_right m j), Nat.add_sub_cancel_left] at h1
    have h2 : homogeneousComponent (m + j) (A * R) = 0 := by
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hAR),
        if_neg (by omega)]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hA0
  have hR : R = homogeneousComponent k R := by
    conv_lhs => rw [← sum_homogeneousComponent R]
    refine Finset.sum_eq_single k (fun j _ hj => hzero j hj) (fun hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    exact homogeneousComponent_eq_zero k R (by omega)
  rw [hR]
  exact homogeneousComponent_isHomogeneous k R

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDiffNotDvd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagDiffNotDvd.proof : FlagDiffNotDvd.Statement := by
  intro σ _ a b c d hab hcd h1 h2 hdvd
  let ψ : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
    aeval (fun i => X (if i = a then b else i))
  have hψ : ∀ i, ψ (X i) = X (if i = a then b else i) := fun i => by
    simp only [ψ, aeval_X]
  obtain ⟨q, hq⟩ := hdvd
  have h := congrArg ψ hq
  rw [map_mul, map_sub, map_sub, hψ, hψ, hψ, hψ, if_pos rfl, if_neg (Ne.symm hab), sub_self,
    zero_mul, sub_eq_zero] at h
  have hcd' := X_injective h
  by_cases hc : c = a <;> by_cases hd : d = a
  · exact hcd (hc.trans hd.symm)
  · rw [if_pos hc, if_neg hd] at hcd'
    exact h1 ⟨hc.symm, hcd'⟩
  · rw [if_neg hc, if_pos hd] at hcd'
    exact h2 ⟨hd.symm, hcd'.symm⟩
  · rw [if_neg hc, if_neg hd] at hcd'
    exact hcd hcd'

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchResidueCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchResidueCount.proof : SchResidueCount.Statement := by
  intro k l hlt hinj
  have hsplit : ∀ i, l i = l i % k + k * (if k ≤ l i then 1 else 0) := by
    intro i
    have hi := hlt i
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  have himg : (univ.image fun i => l i % k) = range k := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [mem_image, mem_univ, true_and] at hc
      obtain ⟨i, rfl⟩ := hc
      exact mem_range.2 (Nat.mod_lt _ i.pos)
    · rw [card_image_of_injective _ hinj, card_range, card_univ, Fintype.card_fin]
  have hres : ∑ i, l i % k = k * (k - 1) / 2 := by
    rw [← sum_range_id, ← himg, sum_image (fun i _ j _ h => hinj h)]
  calc ∑ i, l i = ∑ i, (l i % k + k * (if k ≤ l i then 1 else 0)) :=
        sum_congr rfl (fun i _ => hsplit i)
    _ = ∑ i, l i % k + k * (univ.filter fun i => k ≤ l i).card := by
        rw [sum_add_distrib, ← mul_sum, sum_boole, Nat.cast_id]
    _ = k * (k - 1) / 2 + k * (univ.filter fun i => k ≤ l i).card := by
        rw [hres]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatAlternantZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchConcatAlternantZero.proof : SchConcatAlternantZero.Statement := by
  intro r a lam hanti hnot
  have hex : ∃ i, lam i < a := by
    by_contra h
    exact hnot fun i => not_lt.mp fun hi => h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let k : Fin r := ⟨r - 1, by omega⟩
  have hkv : (k : ℕ) = r - 1 := rfl
  have hik : i ≤ k := by
    rw [Fin.le_def, hkv]; omega
  have hka : lam k < a := lt_of_le_of_lt (hanti hik) hi
  let j : Fin a := ⟨a - 1 - lam k, by omega⟩
  have hjv : (j : ℕ) = a - 1 - lam k := rfl
  have hexp : lam k + (r - 1 - (k : ℕ)) = a - 1 - (j : ℕ) := by
    rw [hkv, hjv]; omega
  unfold alternant
  apply Matrix.det_zero_of_column_eq (i := Sum.inl k) (j := Sum.inr j) Sum.inl_ne_inr
  intro p
  simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  rw [hexp]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchurPowerSumCoefficient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchurPowerSumCoefficient.proof (h1 : SchWeightedPreimage.Statement)
    (h2 : SchEvalPowerSumHom.Statement) (h3 : SchSchurHomogeneous.Statement)
    (h4 : SchSchurAtRootsOfUnity.Statement) : SchurPowerSumCoefficient.Statement := by
  intro N r k hk1 hkN nu hanti hsum
  have hhom := h3 (Fin N) r nu
  rw [hsum] at hhom
  obtain ⟨S, hS, hw⟩ := h1 N k (schur (Fin N) nu) (Schur.schur_isSymmetric (σ := Fin N) nu) hhom
  refine ⟨S, hS, ?_⟩
  have e1 := h2 N k hk1 hkN S hw
  rw [hS, h4 N r k nu hk1 hkN hanti hsum] at e1
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  apply Rat.cast_injective (α := ℂ)
  split_ifs with h
  · rw [if_pos h] at e1
    push_cast
    rw [eq_div_iff hk]
    linear_combination -e1
  · rw [if_neg h] at e1
    push_cast
    rcases mul_eq_zero.mp e1.symm with h0 | h0
    · exact absurd h0 hk
    · exact h0

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralAntisymmetrize
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem flagIntegral_sum_smul_blockPermute (f N : ℕ) (H : RootRing f N)
    (s : Finset (Fin f → Equiv.Perm (Fin N))) :
    flagIntegral f N (∑ w ∈ s, blockSign f N w • blockPermute f N w H) =
      ∑ w ∈ s, blockSign f N w * flagIntegral f N (blockPermute f N w H) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Flag.flagIntegral_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Flag.flagIntegral_add, ih, smul_eq_C_mul,
      Flag.flagIntegral_C_mul]

theorem FlagIntegralAntisymmetrize.proof (h1 : FlagIntegralPermute.Statement) :
    FlagIntegralAntisymmetrize.Statement := by
  intro f N H
  rw [antisymmetrize, flagIntegral_sum_smul_blockPermute]
  rw [Finset.sum_congr rfl fun w _ => by
    rw [h1 f N w H, ← mul_assoc, Flag.blockSign_mul_self, one_mul]]
  rw [Finset.sum_const, Finset.card_univ, Flag.card_blockPerm, nsmul_eq_mul]
  push_cast
  ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagCoeffBlockPermute
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

def blockPermuteEquiv (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    Fin f × Fin N ≃ Fin f × Fin N where
  toFun p := (p.1, w p.1 p.2)
  invFun p := (p.1, (w p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem FlagCoeffBlockPermute.proof : FlagCoeffBlockPermute.Statement := by
  intro f N w P α
  classical
  set E := blockPermuteEquiv f N w with hE
  set β : Fin f × Fin N →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2) with hβ
  have hmap : Finsupp.mapDomain E β = α := by
    ext q
    obtain ⟨p, rfl⟩ := E.surjective q
    rw [Finsupp.mapDomain_apply_of_injective E.injective]
    simp [hβ, hE, blockPermuteEquiv]
  have hren : blockPermute f N w P = rename E P := rfl
  rw [hren, ← hmap, coeff_rename_mapDomain E E.injective]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchWeightedPreimage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchWeightedPreimage.proof (h1 : SchPowerSumHomWeighted.Statement) :
    SchWeightedPreimage.Statement := by
  classical
  intro N k P hsym hhom
  obtain ⟨S₀, hS₀⟩ := Flag.exists_powerSumHom_eq hsym
  let w : Fin N → ℕ := fun i => (i : ℕ) + 1
  refine ⟨weightedHomogeneousComponent w k S₀, ?_,
    weightedHomogeneousComponent_isWeightedHomogeneous k S₀⟩
  have hfin := weightedHomogeneousComponent_finsupp (w := w) S₀
  have hsum := sum_weightedHomogeneousComponent w S₀
  rw [finsum_eq_sum _ hfin] at hsum
  have hterm : ∀ m : ℕ, homogeneousComponent k (powerSumHom N (weightedHomogeneousComponent w m S₀))
      = if k = m then powerSumHom N (weightedHomogeneousComponent w m S₀) else 0 :=
    fun m => homogeneousComponent_of_mem
      (h1 N m _ (weightedHomogeneousComponent_isWeightedHomogeneous m S₀))
  have key : homogeneousComponent k (powerSumHom N S₀) =
      powerSumHom N (weightedHomogeneousComponent w k S₀) := by
    conv_lhs => rw [← hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    simp only [hterm, Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · have hk0 : weightedHomogeneousComponent w k S₀ = 0 := by
        by_contra hne
        exact hk (Set.Finite.mem_toFinset (hs := hfin) |>.mpr hne)
      rw [hk0, map_zero]
  rw [← key, hS₀, homogeneousComponent_eq_self hhom]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurEvalMatrix
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchSchurEvalMatrix.aeval_completeSymmetric (h1 : SchCompleteAtRootsOfUnity.Statement)
    (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (d : ℤ) :
    aeval (rootOfUnityPoint N k) (completeSymmetric (Fin N) d) =
      if 0 ≤ d ∧ (k : ℤ) ∣ d then 1 else 0 := by
  unfold completeSymmetric
  by_cases h0 : 0 ≤ d
  · rw [if_pos h0, h1 N k d.toNat hk hkN]
    have hdiv : (k ∣ d.toNat) ↔ ((k : ℤ) ∣ d) := by
      rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg h0]
    by_cases hd : (k : ℤ) ∣ d
    · rw [if_pos (hdiv.mpr hd), if_pos ⟨h0, hd⟩]
    · rw [if_neg (fun h => hd (hdiv.mp h)), if_neg (fun h => hd h.2)]
  · rw [if_neg h0, map_zero, if_neg (fun h => h0 h.1)]

theorem SchSchurEvalMatrix.proof (h1 : SchCompleteAtRootsOfUnity.Statement) :
    SchSchurEvalMatrix.Statement := by
  intro N k r nu hk hkN
  unfold schur
  rw [AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    SchSchurEvalMatrix.aeval_completeSymmetric h1 N k hk hkN]
  rfl

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatAlternant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchConcatAlternant.alternant_comp_perm {N : ℕ} (w : Fin N → ℕ) (τ : Equiv.Perm (Fin N)) :
    alternant (w ∘ τ) = C ((Equiv.Perm.sign τ : ℤ) : ℚ) * alternant w := by
  unfold alternant
  have hM : (Matrix.of fun i i' : Fin N =>
      (X i : MvPolynomial (Fin N) ℚ) ^ (w ∘ τ) i') =
      (Matrix.of fun i i' : Fin N => (X i : MvPolynomial (Fin N) ℚ) ^ w i').submatrix id τ := rfl
  rw [hM, Matrix.det_permute', map_intCast]

theorem SchConcatAlternant.alternant_add_staircase {N : ℕ} (mu : Fin N → ℕ) :
    alternant (fun p : Fin N => mu p + (N - 1 - (p : ℕ))) =
      vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)) * schur (Fin N) mu := by
  rw [mul_comm, ← Schur.det_pow_add_staircase_eq, ← Matrix.det_transpose]
  rfl

theorem SchConcatAlternant.proof (h1 : SchAlternantRenamePlace.Statement)
    (h2 : SchConcatExponent.Statement) : SchConcatAlternant.Statement := by
  intro r a c
  obtain ⟨τ, hτ⟩ := h2 r a c
  refine ⟨((Equiv.Perm.sign τ : ℤ) : ℚ), ?_, fun lam hlam => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  · rw [h1, hτ lam hlam, SchConcatAlternant.alternant_comp_perm,
      SchConcatAlternant.alternant_add_staircase,
      Schur.schur_padPartition (Fin (r + a)) (fun i : Fin r => lam i - a) (r + a) (by omega), map_mul,
      rename_C]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagProdPrimesDvd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

theorem FlagProdPrimesDvd.proof : FlagProdPrimesDvd.Statement := by
  intro R _ _ ι s p x
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert t s ht ih =>
    intro hp hne hdvd
    have hs : (∏ i ∈ s, p i) ∣ x :=
      ih (fun i hi => hp i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hne i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
        (fun i hi => hdvd i (mem_insert_of_mem hi))
    obtain ⟨y, hy⟩ := hs
    have hpt : Prime (p t) := hp t (mem_insert_self t s)
    have hnd : ¬ p t ∣ ∏ i ∈ s, p i := by
      rw [Prime.dvd_finsetProd_iff hpt]
      rintro ⟨j, hj, hdj⟩
      refine hne t (mem_insert_self t s) j (mem_insert_of_mem hj) ?_ hdj
      rintro rfl
      exact ht hj
    have hty : p t ∣ y := by
      have h := hdvd t (mem_insert_self t s)
      rw [hy] at h
      exact (hpt.dvd_or_dvd h).resolve_left hnd
    rw [prod_insert ht, hy, mul_comm (p t)]
    exact mul_dvd_mul_left _ hty

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurRowsToK
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchSchurRowsToK.proof : SchSchurRowsToK.Statement := by
  intro σ _ _ r k nu hanti hsum
  by_cases hrk : r ≤ k
  · exact (Schur.schur_padPartition σ nu k hrk).symm
  · replace hrk : k < r := Nat.lt_of_not_le hrk
    have hzero : ∀ i : Fin r, k ≤ (i : ℕ) → nu i = 0 := by
      intro i hi
      by_contra hne
      have hpos : 1 ≤ nu i := Nat.one_le_iff_ne_zero.mpr hne
      have h1 : ∑ j ∈ Finset.Iic i, 1 ≤ ∑ j ∈ Finset.Iic i, nu j :=
        Finset.sum_le_sum fun j hj => le_trans hpos (hanti (Finset.mem_Iic.mp hj))
      have h2 : ∑ j ∈ Finset.Iic i, nu j ≤ ∑ j, nu j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Iic] at h1
      omega
    have heq : nu = Schur.padPartition r
        (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0) := by
      funext i
      simp only [Schur.padPartition]
      by_cases hik : (i : ℕ) < k
      · simp [hik, i.isLt]
      · simp only [hik, dite_false]
        exact hzero i (by omega)
    calc schur σ nu
        = schur σ (Schur.padPartition r
            (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)) :=
          congrArg (schur σ) heq
      _ = _ := Schur.schur_padPartition σ _ r hrk.le

end GroundTheory.Heights₂.Heights.RestTerms
end
