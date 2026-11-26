module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperMulInc
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp

theorem exists_upper_mul_inc : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (h : GL (Fin n) ℚ_[g]), ∃ (p : GL (Fin n) ℚ_[g]) (k : GL (Fin n) ℤ_[g]), (∀ i j : Fin n, j < i → (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j = 0) ∧ h = p * inc g n k := by
  intro g hg n h
  have hdet : ((h⁻¹ : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero
  obtain ⟨k, U, hk, hU, -, hA⟩ := Formalism.L2.Pj.iwasawa (V := ℤ_[g]) _ hdet

  have hUdet : IsUnit U.det := by
    rw [hA, Matrix.det_mul] at hdet
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  let K : GL (Fin n) ℤ_[g] := ((Matrix.isUnit_iff_isUnit_det k).mpr hk).unit
  have hinc : ((inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) =
      k.map (algebraMap ℤ_[g] ℚ_[g]) := rfl
  refine ⟨h * inc g n K, K⁻¹, ?_, ?_⟩
  · intro i j hij
    have e1 : ((h * inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) = U⁻¹ := by
      rw [Units.val_mul, hinc]
      calc (h : Matrix (Fin n) (Fin n) ℚ_[g]) * k.map (algebraMap ℤ_[g] ℚ_[g])
          = (h : Matrix (Fin n) (Fin n) ℚ_[g]) * (k.map (algebraMap ℤ_[g] ℚ_[g]) * U) * U⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv U hUdet, Matrix.mul_one]
        _ = U⁻¹ := by rw [← hA, Units.mul_inv, Matrix.one_mul]
    rw [e1]
    haveI := Matrix.invertibleOfIsUnitDet U hUdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU hij
  · rw [map_inv, mul_inv_cancel_right]

end GlobalTheory.GLp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrincipalCongruenceFixedVectorsIff
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp.ParInd

section Blocks
variable {R : Type} [CommRing R] {a b : ℕ}

theorem entN_tl (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin a) :
    entN M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_br (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin b) :
    entN M (a + i) (a + j) = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_self {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) : entN M i j = M i j := by
  simp [entN]

theorem det_par (M : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0) :
    M.det = (Matrix.of fun i j : Fin a => entN M i j).det *
      (Matrix.of fun i j : Fin b => entN M (a + i) (a + j)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    apply h <;> simp
  rw [h0, Matrix.det_fromBlocks_zero₂₁]
  congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, entN_tl, entN_br]

theorem exists_blocks (p : GL (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix _ _ R) i j = 0) :
    ∃ (x : GL (Fin a) R) (y : GL (Fin b) R),
      (∀ i j : Fin a, (x : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) i j) ∧
      (∀ i j : Fin b, (y : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) (a + i) (a + j)) := by
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [det_par _ h] at hu
  have h1 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hu)
  have h2 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)
  exact ⟨h1.unit, h2.unit, fun i j => by simp, fun i j => by simp⟩

def dg (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  fun i j => if (i : ℕ) < a ∧ (j : ℕ) < a then entN x i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then entN y (i - a) (j - a) else 0

theorem dg_par (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin (a + b))
    (hj : (j : ℕ) < a) (hi : a ≤ (i : ℕ)) : dg x y i j = 0 := by
  unfold dg
  rw [if_neg (by omega), if_neg (by omega)]

theorem dg_tl (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin a) :
    entN (dg x y) i j = x i j := by
  rw [entN_tl]
  simp [dg, entN_self]

theorem dg_br (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin b) :
    entN (dg x y) (a + i) (a + j) = y i j := by
  rw [entN_br]
  simp [dg, entN_self]

theorem dg_det (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) :
    (dg x y).det = x.det * y.det := by
  rw [det_par _ (dg_par x y)]
  congr 2 <;> ext i j <;> simp [dg_tl, dg_br]

theorem dg_unit (x : GL (Fin a) R) (y : GL (Fin b) R) : IsUnit (dg x.val y.val) := by
  rw [Matrix.isUnit_iff_isUnit_det, dg_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit)

end Blocks

variable {g : ℕ} [Fact g.Prime] {a b : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem inc_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (inc g n k).val = k.val.map (algebraMap ℤ_[g] ℚ_[g]) := rfl

theorem red_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (red g n k).val = k.val.map (PadicInt.toZMod (p := g)) := rfl

theorem det_inc (n : ℕ) (k : GL (Fin n) ℤ_[g]) : Matrix.GeneralLinearGroup.det (inc g n k) =
    Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, inc_val, Units.coe_map]
  exact ((algebraMap ℤ_[g] ℚ_[g]).map_det k.val).symm

variable {π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V} {σ : Representation ℂ (GL (Fin a) ℚ_[g]) W}
  {ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ} {Λ : V →ₗ[ℂ] W} {χ : (ZMod g)ˣ →* ℂˣ}

theorem blk_val (x : Gn g a) (y : Gn g b) : (blk a b (a + b) x y).val = dg x.val y.val := by
  have hu := dg_unit x y
  change (toG (dg x.val y.val)).val = _
  rw [toG, dif_pos hu, IsUnit.unit_spec]

end GlobalTheory.GLp.ParInd
end

noncomputable section

namespace GlobalTheory.GLp.Supp

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders TensorProduct GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem alg_apply {G U : Type} [Group G] [Fintype G] [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U)
    (a : MonoidAlgebra ℂ G) (w : U) : ρ.asAlgebraHom a w = ∑ x, a.coeff x • ρ x w := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single x c =>
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp

theorem entN_par {a b : ℕ} (x : Gn g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (y : Gn g b) (i j : ℕ) :
    (i < a → j < a → entN (par finSumFinEquiv x B y).val i j = entN x.val i j) ∧
    (a ≤ i → j < a → entN (par finSumFinEquiv x B y).val i j = 0) ∧
    (entN (par finSumFinEquiv x B y).val (a + i) (a + j) = entN y.val i j) ∧
    (B = 0 → i < a → a ≤ j → entN (par finSumFinEquiv x B y).val i j = 0) := by
  refine ⟨fun hi hj => ?_, fun hi hj => ?_, ?_, fun hB hi hj => ?_⟩
  · have := par_apply finSumFinEquiv x B y (.inl ⟨i, hi⟩) (.inl ⟨j, hj⟩)
    rw [entN, entN, dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨hi, hj⟩]
    exact this
  · unfold entN
    split_ifs with h
    · have := par_apply finSumFinEquiv x B y (.inr ⟨i - a, by omega⟩) (.inl ⟨j, hj⟩)
      rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] at this
      rw [← this]
      exact congrArg₂ _ (Fin.ext (by simp; omega)) (Fin.ext (by simp))
    · rfl
  · unfold entN
    by_cases h : i < b ∧ j < b
    · rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left h]
      exact par_apply finSumFinEquiv x B y (.inr ⟨i, h.1⟩) (.inr ⟨j, h.2⟩)
    · rw [dite_eq_right (by omega), dite_eq_right h]
  · unfold entN
    split_ifs with h
    · have := par_apply finSumFinEquiv x B y (.inl ⟨i, hi⟩) (.inr ⟨j - a, by omega⟩)
      subst hB
      rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] at this
      rw [← this]
      exact congrArg₂ _ (Fin.ext (by simp)) (Fin.ext (by simp; omega))
    · rfl

theorem ext_entN {n : ℕ} {x y : Gn g n} (h : ∀ i j : ℕ, i < n → j < n → entN x.val i j = entN y.val i j) :
    x = y := by
  ext i j
  rw [← ParInd.entN_self x.val, ← ParInd.entN_self y.val, h _ _ i.2 j.2]

section Local

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def repK (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : Representation ℂ (Gn g n) (fixK1 π) where
  toFun x := (π (lift g n x)).restrict fun _ hv => padicIntGL_smul_mem_principalCongruenceFixed π hv _
  map_one' := LinearMap.ext fun v => Subtype.ext (lift_one_apply π v.2)
  map_mul' x y := LinearMap.ext fun v => Subtype.ext (lift_mul_apply π v.2 x y)

theorem repK_red (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (k : GL (Fin n) ℤ_[g]) (v : fixK1 π) :
    (repK π (red g n k) v : V) = π (inc g n k) v :=
  inc_eq_of_red_eq π v.2 (red_invFun _)

theorem repK_alg (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a : MonoidAlgebra ℂ (Gn g n)) (v : fixK1 π) :
    ((repK π).asAlgebraHom a v : V) = actK π a v := by
  rw [alg_apply, actK, LinearMap.sum_apply, Submodule.coe_sum]
  rfl

end Local

section Ind

variable {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def parZ (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) : GL (Fin (a + b)) ℤ_[g] where
  val := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val B 0 y.val)
  inv := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (x⁻¹).val
    (-((x⁻¹).val * B * (y⁻¹).val)) 0 (y⁻¹).val)
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [← Matrix.mul_assoc]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]

theorem parZ_apply (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g])
    (i j : Fin a ⊕ Fin b) : (parZ x B y).val (finSumFinEquiv i) (finSumFinEquiv j) =
      Matrix.fromBlocks x.val B 0 y.val i j := by
  simp [parZ]

theorem red_parZ (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) :
    red g _ (parZ x B y) =
      par finSumFinEquiv (red g a x) (B.map (PadicInt.toZMod (p := g))) (red g b y) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [par_apply, ParInd.red_val, Matrix.map_apply, parZ_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [ParInd.red_val]

theorem exists_dual_right (z : W ⊗[ℂ] W') (hz : z ≠ 0) : ∃ P : W ⊗[ℂ] W' →ₗ[ℂ] W, P z ≠ 0 ∧
    ∀ (A : W →ₗ[ℂ] W) (y : W ⊗[ℂ] W'), P (TensorProduct.map A LinearMap.id y) = A (P y) := by
  let β := Module.Basis.ofVectorSpace ℂ W'
  have h1 : TensorProduct.equivFinsuppOfBasisRight β z ≠ 0 := by simpa using hz
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h1
  refine ⟨Finsupp.lapply i ∘ₗ (TensorProduct.equivFinsuppOfBasisRight β).toLinearMap, hi, fun A y => ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem exists_dual_left (z : W ⊗[ℂ] W') (hz : z ≠ 0) : ∃ P : W ⊗[ℂ] W' →ₗ[ℂ] W', P z ≠ 0 ∧
    ∀ (A : W' →ₗ[ℂ] W') (y : W ⊗[ℂ] W'), P (TensorProduct.map LinearMap.id A y) = A (P y) := by
  obtain ⟨P, h1, h2⟩ := exists_dual_right (TensorProduct.comm ℂ W W' z) (by simpa using hz)
  refine ⟨P ∘ₗ (TensorProduct.comm ℂ W W').toLinearMap, h1, fun A y => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← h2]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

end Ind

end GlobalTheory.GLp.Supp
