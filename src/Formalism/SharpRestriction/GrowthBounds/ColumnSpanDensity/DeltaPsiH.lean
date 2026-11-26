module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SingleWeightOfModelIdentification
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FunctorComparisonOfSingleWeight

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DeltaPsiH
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

def covY (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))

def PsiXY (K : Type) [Field K] (m : ℕ) : PolXY K (m + 1) →ₐ[K] MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) K :=
  aeval (Sum.elim (fun i : Fin (m + 1) => X (true, (i, (0 : Fin (m + 1)))))
    (fun i : Fin (m + 1) => rename (Prod.mk false) (covY K m i)))

def deltaB (K : Type) [Field K] (m : ℕ) :
    MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) K →ₐ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  rename Prod.snd

theorem sum_covY (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) :
    ∑ i : Fin (m + 1), (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) * covY K m i = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let N : Matrix (Fin (k + 2)) (Fin (k + 2)) (MvPolynomial (Fin (k + 2) × Fin (k + 2)) K) :=
    Matrix.of fun a c => Fin.cases (X (a, 0)) (fun b : Fin (k + 1) => X (a, b.castSucc)) c
  have h0 : N.det = 0 :=
    Matrix.det_zero_of_column_eq (i := 0) (j := (0 : Fin (k + 1)).succ) (Fin.succ_ne_zero 0).symm
      (fun a => rfl)
  rw [Matrix.det_succ_column_zero] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : N.submatrix i.succAbove Fin.succ =
      fun a b => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (k + 2) × Fin (k + 2)) K) := by
    ext a b
    simp [N]
  have hN0 : N i 0 = X (i, 0) := by simp [N]
  rw [hsub, hN0, covY]
  ring

theorem delta_Psi_h (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) : deltaB K m (PsiXY K m (hXY K (m + 1))) = 0 := by
  have hid : (Prod.snd ∘ Prod.mk false : Fin (m + 1) × Fin (m + 1) → Fin (m + 1) × Fin (m + 1)) = id := rfl
  have h1 : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inl i) * X (Sum.inr i))) =
      X (i, 0) * covY K m i := by
    intro i
    simp only [PsiXY, deltaB, map_mul, aeval_X, Sum.elim_inl, Sum.elim_inr, rename_X, rename_rename, hid,
      rename_id, AlgHom.id_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hXY, map_sum, map_sum, Finset.sum_congr rfl fun i _ => h1 i]
  exact sum_covY K m hm

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FunctorComparisonOfSingleWeightFacts
namespace Formalism.MainNotions.flipOneThree.Pf

private theorem exists_linearMap_prod_rename_eq {K : Type} [Field K] (I β γ : Type) [Fintype I] [DecidableEq I]
    (f : I → MvPolynomial β K →ₗ[K] MvPolynomial γ K) :
    ∃ Φ : MvPolynomial (I × β) K →ₗ[K] MvPolynomial (I × γ) K,
      ∀ P : I → MvPolynomial β K,
        Φ (∏ i, MvPolynomial.rename (fun v : β => (i, v)) (P i)) =
          ∏ i, MvPolynomial.rename (fun v : γ => (i, v)) (f i (P i)) := by
  classical
  let Φ : MvPolynomial (I × β) K →ₗ[K] MvPolynomial (I × γ) K :=
    (MvPolynomial.basisMonomials (I × β) K).constr K
      (fun m => ∏ i, MvPolynomial.rename (fun v : γ => (i, v))
        (f i (MvPolynomial.monomial (m.curry i) 1)))
  have hΦb : ∀ m, Φ (MvPolynomial.basisMonomials (I × β) K m) =
      ∏ i, MvPolynomial.rename (fun v : γ => (i, v))
        (f i (MvPolynomial.monomial (m.curry i) 1)) :=
    fun m => Module.Basis.constr_basis _ _ _ _
  have hcur : ∀ (g : I → β →₀ ℕ) (i : I),
      (∑ j, Finsupp.mapDomain (fun v : β => (j, v)) (g j)).curry i = g i := by
    intro g i
    ext b
    rw [Finsupp.curry_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
    · exact Finsupp.mapDomain_apply_of_injective (fun a c h => (Prod.ext_iff.1 h).2) _ _
    · intro j _ hj
      apply Finsupp.mapDomain_notin_range
      rintro ⟨c, hc⟩
      exact hj (congrArg Prod.fst hc)
    · intro h
      exact absurd (Finset.mem_univ i) h
  refine ⟨Φ, fun P => ?_⟩
  let L : (I → MvPolynomial β K) →ₘₗ[K] MvPolynomial (I × γ) K :=
    Φ.compMultilinearMap ((MultilinearMap.mkPiAlgebra K I (MvPolynomial (I × β) K)).compLinearMap
      (fun i => (MvPolynomial.rename (fun v : β => (i, v))).toLinearMap))
  let M : (I → MvPolynomial β K) →ₘₗ[K] MvPolynomial (I × γ) K :=
    (MultilinearMap.mkPiAlgebra K I (MvPolynomial (I × γ) K)).compLinearMap
      (fun i => (MvPolynomial.rename (fun v : γ => (i, v))).toLinearMap ∘ₗ f i)
  have hLM : L = M := by
    refine Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials β K) fun g => ?_
    simp only [L, M, LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, MvPolynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
      LinearMap.comp_apply, MvPolynomial.rename_monomial]
    rw [← MvPolynomial.monomial_sum_one]
    have hb : (MvPolynomial.monomial (∑ i, Finsupp.mapDomain (fun v : β => (i, v)) (g i)) (1 : K)) =
        MvPolynomial.basisMonomials (I × β) K (∑ i, Finsupp.mapDomain (fun v : β => (i, v)) (g i)) := by
      rw [MvPolynomial.coe_basisMonomials]
    rw [hb, hΦb]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hcur]
  have h := congrArg (fun F => F P) hLM
  simpa [L, M] using h

theorem existsIO' : ExistsIO := by
  intro K _ S α _ _ TT i
  classical
  let f : S → MvPolynomial α K →ₗ[K] MvPolynomial (Bool × α) K := fun s =>
    if h : s ∈ TT then i ⟨s, h⟩
    else (MvPolynomial.aeval (fun _ : α => (0 : MvPolynomial (Bool × α) K))).toLinearMap
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_prod_rename_eq (K := K) S α (Bool × α) f
  let ψ : MvPolynomial (S × (Bool × α)) K →ₐ[K] MvPolynomial ((TT × Bool) × α) K :=
    MvPolynomial.aeval (fun x : S × (Bool × α) =>
      if h : x.1 ∈ TT then (MvPolynomial.X ((⟨x.1, h⟩, x.2.1), x.2.2) : MvPolynomial ((TT × Bool) × α) K)
      else 0)
  refine ⟨ψ.toLinearMap ∘ₗ Φ, fun P hP => ?_⟩
  rw [LinearMap.comp_apply, hΦ, AlgHom.toLinearMap_apply, map_prod]
  have key : ∀ s : S, ψ (MvPolynomial.rename (fun v : Bool × α => (s, v)) (f s (P s))) =
      if h : s ∈ TT then
        MvPolynomial.rename (fun v : Bool × α => (((⟨s, h⟩ : TT), v.1), v.2)) (i ⟨s, h⟩ (P s))
      else 1 := by
    intro s
    by_cases h : s ∈ TT
    · rw [dif_pos h]
      have hf : f s = i ⟨s, h⟩ := by simp only [f, dif_pos h]
      rw [hf]
      have hc : ψ.comp (MvPolynomial.rename (fun v : Bool × α => (s, v))) =
          MvPolynomial.rename (fun v : Bool × α => (((⟨s, h⟩ : TT), v.1), v.2)) := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [ψ, h]
      exact congrArg (fun F : MvPolynomial (Bool × α) K →ₐ[K] MvPolynomial ((TT × Bool) × α) K =>
        F (i ⟨s, h⟩ (P s))) hc
    · rw [dif_neg h]
      have hf : f s = (MvPolynomial.aeval (fun _ : α => (0 : MvPolynomial (Bool × α) K))).toLinearMap := by
        simp only [f, dif_neg h]
      rw [hf, hP s h]
      simp
  rw [Finset.prod_congr rfl fun s _ => key s]
  rw [← Finset.prod_subset (Finset.subset_univ TT) (fun s _ hs => dif_neg hs)]
  rw [← Finset.prod_coe_sort TT]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [dif_pos s.2]

theorem existsPR' : ExistsPR := by
  intro K _ S α _ _ TT pr
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_prod_rename_eq (K := K) TT (Bool × α) α pr
  refine ⟨(MvPolynomial.rename (fun x : TT × α => ((x.1 : S), x.2))).toLinearMap ∘ₗ Φ ∘ₗ
    (MvPolynomial.rename (fun x : (TT × Bool) × α => (x.1.1, (x.1.2, x.2)))).toLinearMap, fun Y => ?_⟩
  have h1 : (MvPolynomial.rename (fun x : (TT × Bool) × α => (x.1.1, (x.1.2, x.2))))
      (∏ s : TT, MvPolynomial.rename (fun v : Bool × α => ((s, v.1), v.2)) (Y s)) =
      ∏ s : TT, MvPolynomial.rename (fun v : Bool × α => (s, v)) (Y s) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => (MvPolynomial.rename_rename _ _ _).trans rfl
  have h2 : ∀ s : TT, MvPolynomial.rename (fun x : TT × α => ((x.1 : S), x.2))
      (MvPolynomial.rename (fun v : α => (s, v)) (pr s (Y s))) =
      MvPolynomial.rename (fun v : α => ((s : S), v)) (pr s (Y s)) :=
    fun s => (MvPolynomial.rename_rename _ _ _).trans rfl
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [h1, hΦ, map_prod]
  exact Finset.prod_congr rfl fun s _ => h2 s

theorem regroupP : RegroupP := fun _ _ _ _ _ _ _ _ _ N y hy => KP.regroup N y hy

theorem functor_comparison_of_single_weight_facts (h : SingleWeightLatticeComparison) : LatticeFunctorComparison := functor_comparison_of_single_weight existsIO' existsPR' regroupP h

end Formalism.MainNotions.flipOneThree.Pf
end
