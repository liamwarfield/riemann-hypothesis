module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.SpecialiseGenericMatrixInverse

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.LaurentDegreesSubstitutionSubset
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section inv

variable {A : Type*} [CommRing A] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)

theorem laurentExpand_C (σ : Type*) (b : LaurentPolynomial A) :
    mul_Phi σ A (C b) = AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A) b := by
  simp [mul_Phi]

theorem laurentExpand_X (σ : Type*) (v : σ) :
    mul_Phi σ A (X v) = LaurentPolynomial.C (X v) := by
  simp [mul_Phi]

theorem mapRingHom_laurent_C {A' : Type*} [CommRing A'] (f : A →+* A') (a : A) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  ext k
  rw [AddMonoidAlgebra.coeff_mapRingHom, LaurentPolynomial.C_apply, LaurentPolynomial.C_apply]
  split_ifs <;> simp

private theorem mapRingHom_laurent_comp {A₁ B₁ D₁ : Type*} [CommRing A₁] [CommRing B₁] [CommRing D₁]
    (f : B₁ →+* D₁) (g : A₁ →+* B₁) (x : LaurentPolynomial A₁) :
    AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.mapRingHom ℤ g x) =
      AddMonoidAlgebra.mapRingHom ℤ (f.comp g) x := by
  ext k
  simp only [AddMonoidAlgebra.coeff_mapRingHom, RingHom.comp_apply]

theorem laurentExpand_substitution (M M' : Matrix (Fin n) (Fin n) A) (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_Phi (ι × Fin n) A (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) =
      AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M') (mul_Phi (ι × Fin n) A Q) := by
  have key : (mul_Phi (ι × Fin n) A).comp
      (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C)) =
      (AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M')).comp (mul_Phi (ι × Fin n) A) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      have hC : (matrixSubst LL S (RingHom.id A) M M').comp (C : A →+* MvPolynomial (ι × Fin n) A) = C :=
        RingHom.ext fun a => by simp only [RingHom.comp_apply, matrixSubst_C, RingHom.id_apply]
      simp only [RingHom.comp_apply, matrixSubst_C, RingHom.id_apply, laurentExpand_C, mapRingHom_laurent_comp, hC]
    · intro v
      simp only [RingHom.comp_apply, matrixSubst_X, laurentExpand_X, mapRingHom_laurent_C]
      split_ifs <;> simp [map_sum, laurentExpand_C, laurentExpand_X, mapRingHom_laurent_C, Matrix.map_apply]
  exact congrArg (fun f => f Q) key

theorem laurent_degrees_substitution_subset (M M' : Matrix (Fin n) (Fin n) A) (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_degs (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) ⊆
      mul_degs Q := by
  rw [mul_degs_eq (matrixSubst LL S (RingHom.id _) _ _ Q), laurentExpand_substitution]
  have key : (AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M')).comp (mul_Phi (ι × Fin n) A) =
      eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ ((matrixSubst LL S (RingHom.id A) M M').comp C))
        (fun v => LaurentPolynomial.C (matrixSubst LL S (RingHom.id A) M M' (X v))) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, laurentExpand_C, mapRingHom_laurent_comp, MvPolynomial.eval₂Hom_C]
    · intro v
      simp only [RingHom.comp_apply, laurentExpand_X, mapRingHom_laurent_C, MvPolynomial.eval₂Hom_X']
  have e := congrArg (fun f => f Q) key
  simp only [RingHom.comp_apply] at e
  rw [e]
  exact mul_Psi_support _ _ Q

theorem laurent_degrees_substitution_eq (M M' : Matrix (Fin n) (Fin n) A) (h : M * M' = 1)
    (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_degs (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) =
      mul_degs Q := by
  apply Finset.Subset.antisymm (laurent_degrees_substitution_subset LL S M M' Q)
  have h' : M' * M = 1 := by
    first
    | exact Matrix.mul_eq_one_comm.1 h
    | exact mul_eq_one_comm.1 h
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) h
    | exact Matrix.nonsing_inv_mul_cancel_of_mul_eq_one h
  have hQ : matrixSubst LL S (RingHom.id _) (M'.map LaurentPolynomial.C) (M.map LaurentPolynomial.C)
      (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) = Q := by
    rw [matrixSubst_comp, ← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _), matrixSubst_one,
      MvPolynomial.map_id]
  conv_lhs => rw [← hQ]
  exact laurent_degrees_substitution_subset LL S M' M _

end inv

private theorem genericMatrixBis_mul_genericMatrixInverse (R : Type) [Field R] (n : ℕ) : genericMatrixRootWeights R n * genericMatrixInverse R n = 1 := by
  have e : genericMatrixInverse R n = IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det •
      (genMat R n).adjugate.map (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) := by
    ext a b
    simp [genericMatrixInverse, Matrix.smul_apply]
  rw [e, genericMatrixRootWeights, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp [Matrix.smul_apply, Matrix.one_apply, hab]

private theorem map_C_genericMatrixBis_and_inverse_eq_gL_gLinv (R : Type) [Field R] (n : ℕ) :
    (genericMatrixRootWeights R n).map LaurentPolynomial.C = gL R n ∧ (genericMatrixInverse R n).map LaurentPolynomial.C = gLinv R n := by
  constructor <;> (ext a b; simp [genericMatrixRootWeights, genericMatrixInverse, gL, gLinv])

private theorem support_laurent_C_mul_T_of_ne_zero {B : Type*} [CommRing B] (h : B) (hh : h ≠ 0) (w : ℤ) :
    (LaurentPolynomial.C h * LaurentPolynomial.T w).coeff.support = {w} := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
  exact Finsupp.support_single_ne_zero _ hh

private theorem laurent_C_mul_T_eq_zero_iff {B : Type*} [CommRing B] (h : B) (w : ℤ) :
    LaurentPolynomial.C h * LaurentPolynomial.T w = 0 ↔ h = 0 := by
  constructor
  · intro e
    have := congrArg (fun p : LaurentPolynomial B => p.coeff w) e
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single] at this
    simpa using this
  · rintro rfl
    simp

theorem twist_exponents_are_weight_entries : TwistExponentsAreWeightEntries := by
  intro R _ ι _ LL n S j G
  classical
  let u : (GLLaurent R n)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  let D : Fin n → (GLLaurent R n)ˣ := fun a => if a = j then u else 1
  have hD : (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n)) =
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T 1 else 1) := by
    congr 1; funext a; by_cases h : a = j <;> simp [D, h, u]
  have hD' : (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n)) =
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T (-1) else 1) := by
    congr 1; funext a; by_cases h : a = j <;> simp [D, h, u]
  obtain ⟨hgL, hgLinv⟩ := map_C_genericMatrixBis_and_inverse_eq_gL_gLinv R n
  have hcoefL : (LaurentPolynomial.C).comp (coefficientMap R n) = coefL R n := rfl
  have hH : MvPolynomial.map LaurentPolynomial.C (genericTranslate LL S G) =
      matrixSubst LL S (coefL R n) (gLinv R n) (gL R n) G := by
    rw [genericTranslate, map_matrixSubst, hgL, hgLinv, hcoefL]
  have hT : twistSub LL S j G = matrixSubst LL S (RingHom.id _) (gL R n) (gLinv R n)
      (matrixSubst LL S (RingHom.id _) (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n))
        (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n))
        (MvPolynomial.map LaurentPolynomial.C (genericTranslate LL S G))) := by
    rw [hH, hD, hD', matrixSubst_comp, matrixSubst_comp, twistSub_eq_matrixSubst]
    simp only [twistMat, Matrix.mul_assoc]
  have hprod : ∀ w : Fin n → ℤ, (((∏ a, D a ^ w a) : (GLLaurent R n)ˣ) : GLLaurent R n) =
      LaurentPolynomial.T (w j) := by
    intro w
    rw [Finset.prod_eq_single j (fun a _ ha => by simp [D, ha]) (fun h => absurd (Finset.mem_univ j) h)]
    simp only [D, if_pos rfl]
    rcases w j with k | k
    · rw [Int.ofNat_eq_coe, zpow_natCast, Units.val_pow_eq_pow_val]
      simp only [u, LaurentPolynomial.T_pow, mul_one]
    · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      simp only [u, Units.inv_mk, LaurentPolynomial.T_pow]
      congr 1
      rw [Int.negSucc_eq]
      push_cast
      ring
  set H := genericTranslate LL S G with hHdef
  set P := matrixSubst LL S (RingHom.id _) (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n))
        (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n))
        (MvPolynomial.map LaurentPolynomial.C H) with hPdef
  have hcoef : ∀ m, P.coeff m = LaurentPolynomial.C (H.coeff m) * LaurentPolynomial.T (wtS LL S m j) := by
    intro m
    rw [hPdef]
    conv_lhs => rw [H.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, MvPolynomial.map_monomial,
      torus_acts_through_weight (GLLaurent R n) (GLLaurent R n) ι LL n S (RingHom.id _) D, RingHom.id_apply, hprod,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [MvPolynomial.notMem_support_iff.mp hm]
      simp
  have hsupp : P.support = H.support := by
    ext m
    rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, hcoef, Ne, laurent_C_mul_T_eq_zero_iff]
  show mul_degs (twistSub LL S j G) = _
  rw [hT, ← hgL, ← hgLinv, laurent_degrees_substitution_eq LL S (genericMatrixRootWeights R n) (genericMatrixInverse R n) (genericMatrixBis_mul_genericMatrixInverse R n)]
  rw [mul_degs, hsupp, ← Finset.biUnion_singleton]
  apply Finset.biUnion_congr rfl
  intro m hm
  rw [hcoef]
  exact support_laurent_C_mul_T_of_ne_zero _ (MvPolynomial.mem_support_iff.mp hm) _

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def binomialFunctions : AddSubgroup (ℤ → ℤ) := AddSubgroup.closure (Set.range fun k : ℕ => fun w : ℤ => Ring.choose w k)

theorem binomialFunctions_shift_mem (s : ℤ) (k : ℕ) : (fun w : ℤ => Ring.choose (w + s) k) ∈ binomialFunctions := by
  have h : (fun w : ℤ => Ring.choose (w + s) k) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, Ring.choose s ij.2 • (fun w : ℤ => Ring.choose w ij.1) := by
    funext w
    rw [Ring.add_choose_eq (h := Commute.all w s), Finset.sum_apply]
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp [mul_comm]
  rw [h]
  exact AddSubgroup.sum_mem _ fun ij _ =>
    AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self ij.1)) _

private theorem ring_choose_eq_zero_of_nonneg_of_lt (x : ℤ) (k : ℕ) (h0 : 0 ≤ x) (hk : x < k) : Ring.choose x k = 0 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
  simp

private theorem ring_choose_self_of_eq (x : ℤ) (k : ℕ) (h : x = k) : Ring.choose x k = 1 := by
  subst h
  rw [Ring.choose_natCast, Nat.choose_self]
  simp

private theorem ring_choose_neg_one (k : ℕ) : Ring.choose (-1 : ℤ) k = (-1) ^ k := by
  induction k with
  | zero => simp [Ring.choose_zero_right]
  | succ k ih =>
    have h := Ring.choose_succ_succ (-1 : ℤ) k
    rw [neg_add_cancel, Ring.choose_zero_succ, ih] at h
    rw [pow_succ]
    linarith

theorem binomialFunctions_window_indicator (w0 : ℤ) (B : ℕ) : ∃ f ∈ binomialFunctions, ∀ w : ℤ, -(B : ℤ) ≤ w → w ≤ B →
    f w = if w = w0 then 1 else 0 := by
  induction B with
  | zero =>
    refine ⟨(if (0 : ℤ) = w0 then 1 else 0) • (fun w : ℤ => Ring.choose w 0),
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self 0)) _, ?_⟩
    intro w h1 h2
    have hw : w = 0 := by omega
    subst hw
    simp [Ring.choose_zero_right]
  | succ B ih =>
    obtain ⟨f, hf, hfw⟩ := ih
    have hg1 : (fun w : ℤ => Ring.choose (w + B) (2 * B + 1)) ∈ binomialFunctions := binomialFunctions_shift_mem _ _
    have hg2 : (fun w : ℤ => Ring.choose (w + ((B : ℤ) + 1)) (2 * B + 2)) ∈ binomialFunctions := binomialFunctions_shift_mem _ _
    set g1 : ℤ → ℤ := fun w : ℤ => Ring.choose (w + B) (2 * B + 1) with hg1d
    set g2 : ℤ → ℤ := fun w : ℤ => Ring.choose (w + ((B : ℤ) + 1)) (2 * B + 2) with hg2d
    set c1 : ℤ := (if (B : ℤ) + 1 = w0 then 1 else 0) - f ((B : ℤ) + 1) with hc1
    set c2 : ℤ := (if -((B : ℤ) + 1) = w0 then 1 else 0) - f (-((B : ℤ) + 1)) with hc2
    refine ⟨f + c1 • g2 + c2 • (g2 - g1),
      add_mem (add_mem hf (AddSubgroup.zsmul_mem _ hg2 _)) (AddSubgroup.zsmul_mem _ (sub_mem hg2 hg1) _), ?_⟩
    intro w h1 h2
    push_cast at h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rcases (by omega : (-(B : ℤ) ≤ w ∧ w ≤ B) ∨ w = B + 1 ∨ w = -((B : ℤ) + 1)) with h | h | h
    · have e1 : g1 w = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      have e2 : g2 w = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      rw [e1, e2, hfw w h.1 h.2]
      ring
    · subst h
      have e1 : g1 ((B : ℤ) + 1) = 1 := ring_choose_self_of_eq _ _ (by push_cast; ring)
      have e2 : g2 ((B : ℤ) + 1) = 1 := ring_choose_self_of_eq _ _ (by push_cast; ring)
      rw [e1, e2, hc1]
      ring
    · subst h
      have e1 : g1 (-((B : ℤ) + 1)) = -1 := by
        simp only [hg1d]
        rw [show -((B : ℤ) + 1) + B = -1 by ring, ring_choose_neg_one, pow_succ, pow_mul]
        simp
      have e2 : g2 (-((B : ℤ) + 1)) = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      rw [e1, e2, hc2]
      ring

section graded

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)

def diagonalMultiplier (a : Fin n) (f : ℤ → ℤ) (x : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ x.support, monomial m (x.coeff m * ((f (wtS LL S m a) : ℤ) : R))


open Classical in
def monomialRestriction (q : (ι × Fin n →₀ ℕ) → Prop) (x : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ x.support.filter q, monomial m (x.coeff m)

theorem coeff_diagonalMultiplier (a : Fin n) (f : ℤ → ℤ) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (diagonalMultiplier LL S a f x) m = x.coeff m * ((f (wtS LL S m a) : ℤ) : R) := by
  classical
  simp only [diagonalMultiplier, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, zero_mul]

open Classical in
theorem coeff_monomialRestriction (q : (ι × Fin n →₀ ℕ) → Prop) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (monomialRestriction q x) m = if q m then x.coeff m else 0 := by
  simp only [monomialRestriction, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
  by_cases hq : q m <;> by_cases hm : x.coeff m = 0 <;> simp [hq, hm]

theorem diagonalMultiplier_mem (W : Submodule R (MvPolynomial (ι × Fin n) R))
    (hW : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) (a : Fin n) (f : ℤ → ℤ) (hf : f ∈ binomialFunctions) :
    ∀ x ∈ W, diagonalMultiplier LL S a f x ∈ W := by
  have hb : ∀ (k : ℕ) (x : MvPolynomial (ι × Fin n) R),
      binomPol R LL S a k x = diagonalMultiplier LL S a (fun w => Ring.choose w k) x := by
    intro k x
    conv_lhs => rw [x.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [binomialOperator_monomial]
    rfl
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    intro x hx
    rw [← hb]
    exact hW a k x hx
  | zero =>
    intro x _
    have e : diagonalMultiplier LL S a 0 x = 0 := by
      ext m
      simp [coeff_diagonalMultiplier]
    rw [e]
    exact W.zero_mem
  | add f g _ _ hf hg =>
    intro x hx
    have e : diagonalMultiplier LL S a (f + g) x = diagonalMultiplier LL S a f x + diagonalMultiplier LL S a g x := by
      ext m
      simp [coeff_diagonalMultiplier, mul_add]
    rw [e]
    exact W.add_mem (hf x hx) (hg x hx)
  | neg f _ hf =>
    intro x hx
    have e : diagonalMultiplier LL S a (-f) x = -diagonalMultiplier LL S a f x := by
      ext m
      simp [coeff_diagonalMultiplier]
    rw [e]
    exact W.neg_mem (hf x hx)

theorem weightEntry_restriction_mem (W : Submodule R (MvPolynomial (ι × Fin n) R))
    (hW : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) (a : Fin n) (w0 : ℤ) :
    ∀ x ∈ W, monomialRestriction (fun m => wtS LL S m a = w0) x ∈ W := by
  intro x hx
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ m ∈ x.support, -(B : ℤ) ≤ wtS LL S m a ∧ wtS LL S m a ≤ B := by
    refine ⟨∑ m ∈ x.support, (wtS LL S m a).natAbs, fun m hm => ?_⟩
    have h := Finset.single_le_sum (f := fun m => (wtS LL S m a).natAbs) (fun _ _ => Nat.zero_le _) hm
    have h2 : |wtS LL S m a| ≤ ((∑ m ∈ x.support, (wtS LL S m a).natAbs : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h
    exact ⟨by linarith [neg_abs_le (wtS LL S m a)], by linarith [le_abs_self (wtS LL S m a)]⟩
  obtain ⟨f, hf, hfw⟩ := binomialFunctions_window_indicator w0 B
  have e : monomialRestriction (fun m => wtS LL S m a = w0) x = diagonalMultiplier LL S a f x := by
    ext m
    rw [coeff_monomialRestriction, coeff_diagonalMultiplier]
    by_cases hm : m ∈ x.support
    · rw [hfw _ (hB m hm).1 (hB m hm).2]
      split_ifs <;> simp
    · rw [MvPolynomial.mem_support_iff, not_not] at hm
      simp [hm]
  rw [e]
  exact diagonalMultiplier_mem LL S W hW a f hf x hx

end graded

theorem binomial_stable_contains_components : BinomialStableContainsComponents := by
  intro R _ ι _ LL n S W hW x hx nu
  classical
  have key : ∀ s : Finset (Fin n), monomialRestriction (fun m => ∀ a ∈ s, wtS LL S m a = nu a) x ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : monomialRestriction (fun m => ∀ a ∈ (∅ : Finset (Fin n)), wtS LL S m a = nu a) x = x := by
        ext m
        rw [coeff_monomialRestriction]
        simp
      rw [e]
      exact hx
    | @insert a s _ ih =>
      have e : monomialRestriction (fun m => ∀ b ∈ insert a s, wtS LL S m b = nu b) x =
          monomialRestriction (fun m => wtS LL S m a = nu a) (monomialRestriction (fun m => ∀ b ∈ s, wtS LL S m b = nu b) x) := by
        ext m
        rw [coeff_monomialRestriction, coeff_monomialRestriction, coeff_monomialRestriction]
        by_cases h1 : wtS LL S m a = nu a <;> by_cases h2 : ∀ b ∈ s, wtS LL S m b = nu b <;>
          simp [h1, h2, Finset.forall_mem_insert]
      rw [e]
      exact weightEntry_restriction_mem LL S W hW a (nu a) _ ih
  have e : weightComponent LL S nu x = monomialRestriction (fun m => ∀ a ∈ Finset.univ, wtS LL S m a = nu a) x := by
    ext m
    rw [coeff_weightComponent, coeff_monomialRestriction]
    by_cases h : wtS LL S m = nu
    · have h' : ∀ a ∈ (Finset.univ : Finset (Fin n)), wtS LL S m a = nu a := fun a _ => by rw [h]
      rw [if_pos h, if_pos h']
    · have h' : ¬ ∀ a ∈ (Finset.univ : Finset (Fin n)), wtS LL S m a = nu a :=
        fun h'' => h (funext fun a => h'' a (Finset.mem_univ a))
      rw [if_neg h, if_neg h']
  rw [e]
  exact key _

end Formalism.MainNotions.G.GLWeightTheory
