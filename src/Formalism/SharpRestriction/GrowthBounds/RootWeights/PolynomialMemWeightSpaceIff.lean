module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.GlOperatorPreservesMultidegree
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivationFinsetSumApply
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem derivation_finset_sum_apply {σ α : Type} (s : Finset α)
    (D : α → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (F : MvPolynomial σ K) :
    (∑ l ∈ s, D l) F = ∑ l ∈ s, D l F := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]


open Classical in
def glDerivation (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) :=
  ∑ l : ι, if l ∈ S then
      (if LL.vec l then (X (l, a) : MvPolynomial (ι × Fin n) K) • pderiv (l, b)
       else -((X (l, b) : MvPolynomial (ι × Fin n) K) • pderiv (l, a)))
    else 0

theorem gl_action_eq_derivation (LL : Letters ι) (S : Set ι) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K) :
    glAct K LL S a b F = glDerivation K LL S a b F := by
  unfold glAct glDerivation
  rw [LinearMap.sum_apply, derivation_finset_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

open Classical in
theorem gl_derivation_variable (LL : Letters ι) (S : Set ι) (a b : Fin n) (l : ι) (c : Fin n) :
    glDerivation K LL S a b (X (l, c)) =
      if l ∈ S then (if LL.vec l then (if c = b then X (l, a) else 0) else (if c = a then -X (l, b) else 0))
      else 0 := by
  unfold glDerivation
  rw [derivation_finset_sum_apply, Finset.sum_eq_single l]
  · split_ifs <;> simp_all [pderiv_X, Pi.single_apply]
  · intro l' _ hl'
    split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hl']
  · simp

theorem gl_derivation_lie_bracket (LL : Letters ι) (S : Set ι) (a b c d : Fin n) :
    ⁅glDerivation K LL S a b, glDerivation K LL S c d⁆ =
      (if b = c then glDerivation K LL S a d else 0) - (if d = a then glDerivation K LL S c b else 0) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨l, e⟩
  rw [Derivation.commutator_apply]
  by_cases hl : l ∈ S
  · by_cases hv : LL.vec l = true
    · simp only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d),
        map_zero, Derivation.coe_sub, Pi.sub_apply]
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = d <;> by_cases h4 : e = b <;>
        subst_vars <;> simp_all [gl_derivation_variable] <;> grind
    · simp only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d),
        map_zero, map_neg, Derivation.coe_sub, Pi.sub_apply]
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = c <;> by_cases h4 : e = a <;>
        subst_vars <;> simp_all [gl_derivation_variable]
  · by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [gl_derivation_variable, hl, h1, h2]

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem gl_operator_apply_derivation (LL : Letters ι) (S : Set ι) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K) :
    glOps K n LL S a b F = glDerivation K LL S a b F := gl_action_eq_derivation LL S a b F

theorem polynomial_gl_commutation (LL : Letters ι) (S : Set ι) (a b c d : Fin n) :
    glOps K n LL S a b * glOps K n LL S c d - glOps K n LL S c d * glOps K n LL S a b =
      (if b = c then glOps K n LL S a d else 0) - (if d = a then glOps K n LL S c b else 0) := by
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) => D F)
    (gl_derivation_lie_bracket (K := K) LL S a b c d)
  simp only [Derivation.commutator_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, gl_operator_apply_derivation]
  rw [h]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, gl_operator_apply_derivation]

theorem disjoint_letters_commute (LL : Letters ι) (S S' : Set ι) (hd : Disjoint S S') (a b c d : Fin n) :
    glOps K n LL S a b * glOps K n LL S' c d = glOps K n LL S' c d * glOps K n LL S a b := by
  classical
  have h0 : ⁅glDerivation K LL S a b, glDerivation K LL S' c d⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    rintro ⟨l, e⟩
    rw [Derivation.commutator_apply]
    by_cases hl : l ∈ S
    · have hl' : l ∉ S' := fun h => (Set.disjoint_left.1 hd) hl h
      simp only [gl_derivation_variable, hl, hl', if_true, if_false, map_zero]
      split_ifs <;> simp [gl_derivation_variable, hl']
    · simp only [gl_derivation_variable, hl, if_false, map_zero]
      split_ifs <;> simp [gl_derivation_variable, hl]
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) => D F) h0
  simp only [Derivation.commutator_apply] at h
  simp only [Module.End.mul_apply, gl_operator_apply_derivation]
  exact sub_eq_zero.1 h

theorem gl_operator_union_add (LL : Letters ι) (S S' : Set ι) (hs : S ⊆ S') (a b : Fin n) :
    glOps K n LL S' a b = glOps K n LL S a b + glOps K n LL (S' \ S) a b := by
  classical
  have h0 : glDerivation K LL S' a b = glDerivation K LL S a b + glDerivation K LL (S' \ S) a b := by
    apply MvPolynomial.derivation_ext
    rintro ⟨l, e⟩
    rw [Derivation.add_apply]
    by_cases hl : l ∈ S
    · have hl' : l ∈ S' := hs hl
      simp [gl_derivation_variable, hl, hl']
    · by_cases hl' : l ∈ S' <;> simp [gl_derivation_variable, hl, hl']
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.add_apply, gl_operator_apply_derivation, h0, Derivation.add_apply]

theorem variable_mul_pderiv_monomial {σ : Type} (v w : σ) (m : σ →₀ ℕ) (c : K) :
    (X v : MvPolynomial σ K) * pderiv w (monomial m c) =
      monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : K)) := by
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
    add_comm (Finsupp.single v 1)]

open Classical in
theorem gl_derivation_monomial (LL : Letters ι) (S : Set ι) (a b : Fin n) (m : ι × Fin n →₀ ℕ) (c : K) :
    glDerivation K LL S a b (monomial m c) =
      ∑ l : ι, if l ∈ S then
        (if LL.vec l then monomial (m - Finsupp.single (l, b) 1 + Finsupp.single (l, a) 1) (c * (m (l, b) : K))
         else -monomial (m - Finsupp.single (l, a) 1 + Finsupp.single (l, b) 1) (c * (m (l, a) : K)))
      else 0 := by
  simp only [glDerivation, derivation_finset_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp only [Derivation.smul_apply, smul_eq_mul, variable_mul_pderiv_monomial]
  · simp only [Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul, variable_mul_pderiv_monomial]
  · simp

theorem multidegree_polarization_move (m : ι × Fin n →₀ ℕ) (l : ι) (a b : Fin n) (h : m (l, b) ≠ 0) (i : ι) :
    multideg (m - Finsupp.single (l, b) 1 + Finsupp.single (l, a) 1) i = multideg m i := by
  classical
  unfold multideg
  have hle : ∀ c : Fin n, (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c) ≤ m (i, c) := by
    intro c
    rw [Finsupp.single_apply]
    split_ifs with hc
    · rw [← hc]; exact Nat.one_le_iff_ne_zero.mpr h
    · exact Nat.zero_le _
  have hs : ∑ c : Fin n, (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c) =
      ∑ c : Fin n, (Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c) := by
    by_cases hi : i = l
    · subst hi
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, Ne.symm hi]
  have key : ∀ c : Fin n, (m - Finsupp.single (l, b) 1 + Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c)
      + (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c)
      = m (i, c) + (Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c) := by
    intro c
    rw [Finsupp.add_apply, Finsupp.tsub_apply]
    have := hle c
    omega
  have hsum := Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => key c)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hs] at hsum
  omega

theorem gl_operator_preserves_multidegree (LL : Letters ι) (S : Set ι) (d : ι → ℕ) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K)
    (hF : F ∈ Pol K n d) : glOps K n LL S a b F ∈ Pol K n d := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gl_operator_apply_derivation, F.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hm' : ∀ i, multideg m i = d i := (MvPolynomial.mem_restrictSupport_iff K).1 hF (by simpa using hm)
  rw [gl_derivation_monomial]
  refine Submodule.sum_mem _ fun l _ => ?_
  split_ifs
  · rw [Pol, monomial_mem_restrictSupport]
    by_cases h0 : m (l, b) = 0
    · right; simp [h0]
    · left; intro i; rw [multidegree_polarization_move m l a b h0, hm']
  · refine Submodule.neg_mem _ ?_
    rw [Pol, monomial_mem_restrictSupport]
    by_cases h0 : m (l, a) = 0
    · right; simp [h0]
    · left; intro i; rw [multidegree_polarization_move m l b a h0, hm']
  · exact Submodule.zero_mem _

theorem homogeneous_multidegree_findim (d : ι → ℕ) : FiniteDimensional K (Pol K n d) := by
  classical
  have hfin : Set.Finite {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} := by
    refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : ι × Fin n => d v.1))).subset ?_
    intro m hm v
    have := hm v.1
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    rw [← this]
    exact Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
  have : Finite {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} := hfin
  exact Module.Finite.of_basis (basisRestrictSupport K {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i})

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem monomial_shift_cancel {σ : Type} (m : σ →₀ ℕ) (v : σ) (c : K) :
    (monomial (m - Finsupp.single v 1 + Finsupp.single v 1) (c * (m v : K)) : MvPolynomial σ K) =
      monomial m (c * (m v : K)) := by
  by_cases h : m v = 0
  · simp [h]
  · rw [tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]
    omega

theorem diagonal_derivation_monomial (LL : Letters ι) (S : Set ι) (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : K) :
    glDerivation K LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : K) * c) := by
  rw [gl_derivation_monomial]
  simp only [monomial_shift_cancel]
  unfold wtS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Int.cast_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [mul_comm]

theorem diagonal_derivation_coeff (LL : Letters ι) (S : Set ι) (a : Fin n) (F : MvPolynomial (ι × Fin n) K)
    (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (glDerivation K LL S a a F) m = ((wtS LL S m a : ℤ) : K) * AddMonoidAlgebra.coeff F m := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [diagonal_derivation_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add, mul_add]

theorem polynomial_mem_weightSpace_iff (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K) :
    F ∈ weightSp (glOps K n LL S) mu ↔ ∀ a, glDerivation K LL S a a F = ((mu a : ℤ) : K) • F := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_eq_zero, gl_operator_apply_derivation]
  rfl

theorem weight_vector_monomial_weight [CharZero K] (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K)
    (hF : F ∈ weightSp (glOps K n LL S) mu) (m : ι × Fin n →₀ ℕ) (hm : m ∈ F.support) : wtS LL S m = mu := by
  funext a
  have h := congrArg (AddMonoidAlgebra.coeff · m) ((polynomial_mem_weightSpace_iff LL S mu F).1 hF a)
  rw [diagonal_derivation_coeff, coeff_smul, smul_eq_mul] at h
  have hc : AddMonoidAlgebra.coeff F m ≠ 0 := mem_support_iff.1 hm
  have h2 := mul_right_cancel₀ hc h
  exact_mod_cast h2

theorem monomial_mem_weightSpace (LL : Letters ι) (S : Set ι) (m : ι × Fin n →₀ ℕ) (c : K) :
    monomial m c ∈ weightSp (glOps K n LL S) (wtS LL S m) := by
  rw [polynomial_mem_weightSpace_iff]
  intro a
  rw [diagonal_derivation_monomial, smul_monomial, smul_eq_mul]

theorem polynomial_isGLRep (LL : Letters ι) (S : Set ι) : IsGLRep (glOps K n LL S) := by
  classical
  refine ⟨polynomial_gl_commutation LL S, ?_, ?_⟩
  · intro x
    haveI : ∀ m : x.support, FiniteDimensional K (Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i)) :=
      fun m => homogeneous_multidegree_findim _
    refine ⟨⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i), inferInstance, ?_, ?_⟩
    · have key : ∑ m ∈ x.support, monomial m (AddMonoidAlgebra.coeff x m) ∈
          ⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i) := by
        apply Submodule.sum_mem
        intro m hm
        apply Submodule.mem_iSup_of_mem (⟨m, hm⟩ : x.support)
        rw [Pol, mem_restrictSupport_iff]
        intro m' hm'
        have h1 := support_monomial_subset (Finset.mem_coe.1 hm')
        rw [Finset.mem_singleton] at h1
        subst h1
        intro i
        rfl
      convert key using 1
      exact x.as_sum
    · intro a b y hy
      refine Submodule.iSup_induction _ (motive := fun y => glOps K n LL S a b y ∈
        ⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i)) hy ?_ ?_ ?_
      · intro m z hz
        exact Submodule.mem_iSup_of_mem m (gl_operator_preserves_multidegree LL S _ a b z hz)
      · simp
      · intro z w hz hw
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hz hw
  · rw [eq_top_iff]
    intro F _
    have key : ∑ m ∈ F.support, monomial m (AddMonoidAlgebra.coeff F m) ∈ ⨆ mu : Fin n → ℤ, weightSp (glOps K n LL S) mu := by
      apply Submodule.sum_mem
      intro m _
      exact Submodule.mem_iSup_of_mem (wtS LL S m) (monomial_mem_weightSpace LL S m _)
    convert key using 1
    exact F.as_sum

end Formalism.MainNotions.G.GLWeightTheory
