module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness

@[expose] public section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
open scoped Matrix

noncomputable section

namespace DedupShared

theorem dedup_roots_stable_8 {k : Type} [Field k] {n : ℕ} (f : k →+* ℂ) (M P : GL (Fin n) k) (t : kˣ)
    (h : (M : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (M : Matrix (Fin n) (Fin n) k) =
      (t : k) • (P : Matrix (Fin n) (Fin n) k)) (B : Multiset ℂ)
    (hB : (M : Matrix (Fin n) (Fin n) k).charpoly.map f = (B.map fun b => X - C b).prod) :
    B.map (fun b => f t * b⁻¹) = B := by
  set N : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) k).map f with hN
  set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) k).map f with hQ
  have hdet : ∀ U : GL (Fin n) k, ((U : Matrix (Fin n) (Fin n) k).map f).det ≠ 0 := fun U => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero f).2 (Matrix.GeneralLinearGroup.det U).ne_zero
  have h' : Nᵀ * Q * N = f t • Q := by
    have := congrArg (fun Z : Matrix (Fin n) (Fin n) k => Z.map f) h
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [this]
    ext i j
    simp [hQ]
  rw [← Matrix.charpoly_map, ← hN] at hB
  have hc : B.card = n := by
    have := congrArg natDegree hB
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have ev : ∀ x : ℂ, (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N).det = (B.map fun b => x - b).prod := fun x => by
    have := congrArg (eval x) hB
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at this
    simpa [Matrix.smul_one_eq_diagonal] using this
  have e0 : N.det = B.prod := by
    have := ev 0
    simp only [zero_smul, zero_sub, Matrix.det_neg, Fintype.card_fin] at this
    rw [Multiset.prod_map_neg, hc] at this
    exact mul_left_cancel₀ (pow_ne_zero _ (by simp)) this
  have hb : ∀ b ∈ B, b ≠ 0 := fun b hb h0 => hdet M (e0.trans (Multiset.prod_eq_zero (h0 ▸ hb)))
  have key : ∀ x : ℂ, x ≠ 0 → ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod = (B.map fun b => x - b).prod := by
    intro x hx
    have e1 : Nᵀ * Q * (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N) =
        (-x) • (((f t / x) • (1 : Matrix (Fin n) (Fin n) ℂ) - N)ᵀ * Q) := by
      rw [mul_sub, h', Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, sub_mul, smul_sub,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one, one_mul, neg_mul, mul_div_cancel₀ _ hx, neg_smul, neg_smul]
      abel
    have e2 := congrArg Matrix.det e1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
      ev, ev, e0, Fintype.card_fin] at e2
    have e3 : B.prod * ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod =
        (-x) ^ n * (B.map fun b => f t / x - b).prod := by
      rw [← hc, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul, Multiset.map_map]
      conv_lhs => rw [← Multiset.map_id' B, Multiset.map_map, ← Multiset.prod_map_mul]
      refine congrArg _ (Multiset.map_congr rfl fun b h => ?_)
      have := hb b h
      simp only [Function.comp_apply]
      field_simp
      ring
    refine mul_left_cancel₀ (mul_ne_zero (e0 ▸ hdet M) (hdet P)) ?_
    rw [← hQ]
    linear_combination Q.det * e3 - e2
  have hp : ((B.map fun b => f t * b⁻¹).map fun b => X - C b).prod = (B.map fun b => X - C b).prod := by
    refine eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun x hx => ?_)
    have := key x hx
    simpa [eval_multiset_prod, Multiset.map_map] using this
  have := congrArg roots hp
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at this

end DedupShared
end
