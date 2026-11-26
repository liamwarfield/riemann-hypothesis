module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.DiscreteValuationQuotients

private lemma lenQuotSpan {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {x : O} (hx : x ≠ 0) :
    Module.length O (O ⧸ Ideal.span ({x} : Set O)) = IsDiscreteValuationRing.addVal O x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n, Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

private lemma addValUnit {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (u : Oˣ) : IsDiscreteValuationRing.addVal O (u : O) = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h := IsDiscreteValuationRing.addVal_def' u hϖ 0
  rwa [pow_zero, mul_one, Nat.cast_zero] at h

private lemma addValProd {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (g : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, g i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, IsDiscreteValuationRing.addVal_one]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]

theorem goal1 :
    ∀ {O : Type u_1} {M : Type u_2} [inst : CommRing O] [inst_1 : IsDomain O]
      [inst_2 : IsDiscreteValuationRing O] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module O M]
      [Module.Free O M] [Module.Finite O M] (φ : M →ₗ[O] M),
      Function.Injective ⇑φ →
        Module.length O (M ⧸ φ.range) = (IsDiscreteValuationRing.addVal O) (LinearMap.det φ) := by
  intro O M _ _ _ _ _ _ _ φ hφ
  classical
  let e0 : M ≃ₗ[O] LinearMap.range φ := LinearEquiv.ofInjective φ hφ
  have h : Module.finrank O (LinearMap.range φ) = Module.finrank O M := e0.finrank_eq.symm
  let b := Module.Free.chooseBasis O M
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[O] LinearMap.range φ := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[O] M := (LinearMap.range φ).subtype ∘ₗ (e' : M →ₗ[O] LinearMap.range φ)
  have hφf : φ = (LinearMap.range φ).subtype ∘ₗ (e0 : M →ₗ[O] LinearMap.range φ) :=
    LinearMap.ext fun x => rfl
  have hassoc : Associated (LinearMap.det φ) (LinearMap.det f) := by
    rw [hφf]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _) (b' i) : LinearMap.range φ) : M) = _
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hval : IsDiscreteValuationRing.addVal O (LinearMap.det φ) =
      IsDiscreteValuationRing.addVal O (∏ i, a i) := by
    obtain ⟨u, hu⟩ := hassoc
    rw [← hdet, ← hu, IsDiscreteValuationRing.addVal_mul, addValUnit, add_zero]
  rw [(Submodule.quotientEquivPiSpan (LinearMap.range φ) b h).length_eq,
    Module.length_pi_of_fintype, hval, addValProd]
  exact Finset.sum_congr rfl fun i _ => lenQuotSpan (Submodule.smithNormalFormCoeffs_ne_zero b h i)

end Bl.DiscreteValuationQuotients
