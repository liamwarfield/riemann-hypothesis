module

public import Formalism.PeriodIntegrals.LowCyc

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.MinusPartOfMem
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.FockInnerSelfReNonneg
noncomputable section

open MvPolynomial

namespace PI.FHS

variable {σ : Type*}

def wt (α : σ →₀ ℕ) : ℂ := α.prod (fun _ k => (k.factorial : ℂ))

lemma wt_eq_nat (α : σ →₀ ℕ) : wt α = ((α.prod fun _ k => k.factorial : ℕ) : ℂ) := by
  simp [wt, Finsupp.prod]

lemma wt_pos_nat (α : σ →₀ ℕ) : 0 < (α.prod fun _ k => k.factorial : ℕ) := by
  unfold Finsupp.prod
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _

lemma conj_wt (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := by
  rw [wt_eq_nat, map_natCast]

private theorem fockInner_eq_sum_support_left (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P Q = ∑ α ∈ P.support, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α := by
  unfold FockH1Action.fockInner
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.sum_eq_single α]
  · rw [if_pos rfl, wt]
  · intro β _ hβ
    rw [if_neg (Ne.symm hβ), mul_zero]
  · intro hα
    rw [MvPolynomial.mem_support_iff, not_not] at hα
    simp only [hα, mul_zero, zero_mul]

lemma fockInner_eq_sum (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : ∀ α, AddMonoidAlgebra.coeff P α ≠ 0 → AddMonoidAlgebra.coeff Q α ≠ 0 → α ∈ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α := by
  classical
  rw [fockInner_eq_sum_support_left]
  have h1 : ∑ α ∈ P.support, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α
      = ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α := by
    apply Finset.sum_subset (fun x hx => Finset.mem_union_left _ hx)
    intro α _ hα
    rw [MvPolynomial.mem_support_iff, not_not] at hα
    rw [hα, map_zero, zero_mul, zero_mul]
  have h2 : ∑ α ∈ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α
      = ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α := by
    apply Finset.sum_subset (fun x hx => Finset.mem_union_right _ hx)
    intro α _ hα
    by_cases hP : AddMonoidAlgebra.coeff P α = 0
    · rw [hP, map_zero, zero_mul, zero_mul]
    · by_cases hQ : AddMonoidAlgebra.coeff Q α = 0
      · rw [hQ, mul_zero, zero_mul]
      · exact absurd (hS α hP hQ) hα
  rw [h1, h2]

lemma fockInner_eq_sum_left (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α :=
  fockInner_eq_sum P Q S (fun _ hP _ => hS (MvPolynomial.mem_support_iff.mpr hP))

lemma fockInner_eq_sum_right (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : Q.support ⊆ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α :=
  fockInner_eq_sum P Q S (fun _ _ hQ => hS (MvPolynomial.mem_support_iff.mpr hQ))

lemma fockInner_add_left (P P' Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (P + P') Q = FockH1Action.fockInner P Q + FockH1Action.fockInner P' Q := by
  rw [fockInner_eq_sum_right (P + P') Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P' Q Q.support (Finset.Subset.refl _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [MvPolynomial.coeff_add, map_add (f := _)]
  ring

lemma fockInner_add_right (P Q Q' : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (Q + Q') = FockH1Action.fockInner P Q + FockH1Action.fockInner P Q' := by
  rw [fockInner_eq_sum_support_left, fockInner_eq_sum_support_left P Q, fockInner_eq_sum_support_left P Q',
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [MvPolynomial.coeff_add]
  ring

lemma fockInner_smul_left (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (c • P) Q = (starRingEnd ℂ) c * FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_right (c • P) Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  simp only [coeff_smul, smul_eq_mul, map_mul]
  ring

lemma fockInner_smul_right (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (c • Q) = c * FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_support_left, fockInner_eq_sum_support_left P Q, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  simp only [coeff_smul, smul_eq_mul]
  ring

lemma fockInner_neg_right (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (-Q) = - FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_support_left, fockInner_eq_sum_support_left P Q, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg]
  ring

lemma fockInner_neg_left (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (-P) Q = - FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_right (-P) Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg, map_neg]
  ring

lemma fockInner_zero_left (Q : MvPolynomial σ ℂ) : FockH1Action.fockInner 0 Q = 0 := by
  simp [fockInner_eq_sum_support_left]

lemma fockInner_zero_right (P : MvPolynomial σ ℂ) : FockH1Action.fockInner P 0 = 0 := by
  simp [fockInner_eq_sum_support_left]

lemma fockInner_conj (P Q : MvPolynomial σ ℂ) :
    (starRingEnd ℂ) (FockH1Action.fockInner Q P) = FockH1Action.fockInner P Q := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockInner_eq_sum_right Q P P.support (Finset.Subset.refl _),
    fockInner_eq_sum_support_left P Q, map_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [map_mul, map_mul, conj_wt, Complex.conj_conj]
  ring

private theorem conj_mul_self_eq_normSq (z : ℂ) : (starRingEnd ℂ) z * z = ((Complex.normSq z : ℝ) : ℂ) := by
  exact Complex.normSq_eq_conj_mul_self.symm

lemma fockInner_self (P : MvPolynomial σ ℂ) : FockH1Action.fockInner P P =
    ∑ α ∈ P.support, (((Complex.normSq (AddMonoidAlgebra.coeff P α)) *
      ((α.prod fun _ k => k.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [fockInner_eq_sum_support_left]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [conj_mul_self_eq_normSq, wt_eq_nat]
  rw [Complex.ofReal_mul, Complex.ofReal_natCast]

lemma fockInner_self_re_nonneg (P : MvPolynomial σ ℂ) : 0 ≤ (FockH1Action.fockInner P P).re := by
  rw [fockInner_self, Complex.re_sum]
  refine Finset.sum_nonneg (fun α _ => ?_)
  rw [Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

lemma fockInner_self_eq_zero {P : MvPolynomial σ ℂ} (h : FockH1Action.fockInner P P = 0) : P = 0 := by
  have hre : ∑ α ∈ P.support, Complex.normSq (AddMonoidAlgebra.coeff P α) *
      ((α.prod fun _ k => k.factorial : ℕ) : ℝ) = 0 := by
    have h' := congrArg Complex.re h
    rw [fockInner_self, Complex.re_sum] at h'
    simpa only [Complex.ofReal_re, Complex.zero_re] using h'
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun α _ => mul_nonneg (Complex.normSq_nonneg (AddMonoidAlgebra.coeff P α)) (Nat.cast_nonneg _))).mp hre
  by_contra hP
  obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hP)
  rcases mul_eq_zero.mp (hterm α hα) with h1 | h1
  · rw [Complex.normSq_eq_zero] at h1
    exact (MvPolynomial.mem_support_iff.mp hα) h1
  · exact absurd h1 (Nat.cast_ne_zero.mpr (wt_pos_nat α).ne')

lemma wt_add_single [Fintype σ] [DecidableEq σ] (β : σ →₀ ℕ) (l : σ) :
    wt (β + Finsupp.single l 1) = ((β l + 1 : ℕ) : ℂ) * wt β := by
  have hw : ∀ γ : σ →₀ ℕ, wt γ = ∏ i, ((γ i).factorial : ℂ) := fun γ =>
    Finsupp.prod_fintype γ _ (fun _ => by simp)
  have key1 : ∏ i, (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ) =
      (((β + Finsupp.single l 1 : σ →₀ ℕ) l).factorial : ℂ) *
        ∏ i ∈ Finset.univ.erase l, (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ) := by
    exact (Finset.mul_prod_erase Finset.univ
        (fun i => (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ)) (Finset.mem_univ l)).symm
  have key2 : ∏ i, ((β i).factorial : ℂ) =
      ((β l).factorial : ℂ) * ∏ i ∈ Finset.univ.erase l, ((β i).factorial : ℂ) := by
    exact (Finset.mul_prod_erase Finset.univ
        (fun i => ((β i).factorial : ℂ)) (Finset.mem_univ l)).symm
  rw [hw, hw, key1, key2]
  have hrest : ∏ i ∈ Finset.univ.erase l, (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ)
      = ∏ i ∈ Finset.univ.erase l, ((β i).factorial : ℂ) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hi)),
      add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

private theorem X_mul_monomial_eq_monomial_add_single (l : σ) (a : σ →₀ ℕ) (c : ℂ) :
    X l * monomial a c = monomial (a + Finsupp.single l 1) c := by
  rw [add_comm]
  rw [MvPolynomial.monomial_single_add, pow_one]

private theorem fockInner_monomial_monomial_self (a : σ →₀ ℕ) (c d : ℂ) :
    FockH1Action.fockInner (monomial a c) (monomial a d) = (starRingEnd ℂ) c * d * wt a := by
  classical
  rw [fockInner_eq_sum_left _ _ {a} support_monomial_subset, Finset.sum_singleton]
  simp [coeff_monomial]

private theorem fockInner_monomial_monomial_of_ne (a b : σ →₀ ℕ) (c d : ℂ) (h : b ≠ a) :
    FockH1Action.fockInner (monomial a c) (monomial b d) = 0 := by
  classical
  rw [fockInner_eq_sum_left _ _ {a} support_monomial_subset, Finset.sum_singleton]
  simp [coeff_monomial, h]

lemma fockInner_X_mul [Fintype σ] (l : σ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (X l * P) Q = FockH1Action.fockInner P (pderiv l Q) := by
  classical
  refine MvPolynomial.induction_on' P (fun a c => ?_) (fun P P' hP hP' => ?_)
  · refine MvPolynomial.induction_on' Q (fun b d => ?_) (fun Q Q' hQ hQ' => ?_)
    · rw [X_mul_monomial_eq_monomial_add_single, pderiv_monomial]
      by_cases h : b = a + Finsupp.single l 1
      · subst h
        rw [add_tsub_cancel_right, fockInner_monomial_monomial_self, fockInner_monomial_monomial_self,
          wt_add_single, Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast
        ring
      · rw [fockInner_monomial_monomial_of_ne _ _ _ _ h]
        by_cases hbl : b l = 0
        · rw [hbl, Nat.cast_zero, mul_zero, map_zero, fockInner_zero_right]
        · have hb : b - Finsupp.single l 1 + Finsupp.single l 1 = b := by
            ext i
            by_cases hi : i = l
            · subst hi
              simp
              omega
            · simp [Ne.symm hi]
          have hne : b - Finsupp.single l 1 ≠ a := fun he => h (hb.symm.trans (by rw [he]))
          rw [fockInner_monomial_monomial_of_ne _ _ _ _ hne]
    · rw [fockInner_add_right, map_add (f := _), fockInner_add_right, hQ, hQ']
  · rw [mul_add, fockInner_add_left, fockInner_add_left, hP, hP']

lemma fockInner_pderiv [Fintype σ] (l : σ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (pderiv l P) Q = FockH1Action.fockInner P (X l * Q) := by
  rw [← fockInner_conj (pderiv l P) Q, ← fockInner_X_mul l Q P, fockInner_conj]

lemma fockInner_hc_left {n : ℕ} (P Q : MvPolynomial σ ℂ) (hQ : Q ∈ FockH1Action.homog σ n) :
    FockH1Action.fockInner (homogeneousComponent n P) Q = FockH1Action.fockInner P Q := by
  have hQ' : Q.IsHomogeneous n := (mem_homogeneousSubmodule _ _).mp hQ
  rw [fockInner_eq_sum_right (homogeneousComponent n P) Q Q.support
      (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hdeg := hQ' (MvPolynomial.mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent]
  split_ifs with hc
  · rfl
  · exact absurd (by
      first
      | exact hdeg
      | (rw [Finsupp.degree_eq_weight_one]; exact hdeg)) hc

lemma fockInner_hc_right {n : ℕ} (P Q : MvPolynomial σ ℂ) (hP : P ∈ FockH1Action.homog σ n) :
    FockH1Action.fockInner P (homogeneousComponent n Q) = FockH1Action.fockInner P Q := by
  have hP' : P.IsHomogeneous n := (mem_homogeneousSubmodule _ _).mp hP
  rw [fockInner_eq_sum_support_left, fockInner_eq_sum_support_left P Q]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hdeg := hP' (MvPolynomial.mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent]
  split_ifs with hc
  · rfl
  · exact absurd (by
      first
      | exact hdeg
      | (rw [Finsupp.degree_eq_weight_one]; exact hdeg)) hc

end PI.FHS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.FockCore
noncomputable section

open MvPolynomial

namespace PI.FHS

variable {σ : Type*}

def FockV (σ : Type*) : Type _ := MvPolynomial σ ℂ

instance : AddCommGroup (FockV σ) := inferInstanceAs (AddCommGroup (MvPolynomial σ ℂ))

instance : Module ℂ (FockV σ) := inferInstanceAs (Module ℂ (MvPolynomial σ ℂ))

@[instance_reducible]
def fockCore : InnerProductSpace.Core ℂ (FockV σ) where
  inner P Q := FockH1Action.fockInner (σ := σ) P Q
  conj_inner_symm x y := fockInner_conj (σ := σ) x y
  re_inner_nonneg x := by simpa using fockInner_self_re_nonneg (σ := σ) x
  add_left x y z := fockInner_add_left (σ := σ) x y z
  smul_left x y r := fockInner_smul_left (σ := σ) r x y
  definite _ h := fockInner_self_eq_zero (σ := σ) h

private lemma finiteDimensional_homog' [Fintype σ] (n : ℕ) :
    FiniteDimensional ℂ (FockH1Action.homog σ n) := by
  classical
  first
  | exact inferInstance
  | (let c : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => n)
     have hS : (Set.Icc (0 : σ →₀ ℕ) c).Finite := Set.finite_Icc 0 c
     have hle : FockH1Action.homog σ n ≤ Submodule.span ℂ
         ((fun d => MvPolynomial.monomial d (1 : ℂ)) '' Set.Icc (0 : σ →₀ ℕ) c) := by
       intro p hp
       have hph : p.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n p).1 hp
       rw [p.as_sum]
       refine Submodule.sum_mem _ (fun d hd => ?_)
       have hmono : MvPolynomial.monomial d (AddMonoidAlgebra.coeff p d)
           = AddMonoidAlgebra.coeff p d • MvPolynomial.monomial d (1 : ℂ) := by
         first
         | simp [MvPolynomial.smul_monomial]
         | rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
       rw [hmono]
       refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, ⟨by first | exact zero_le | exact bot_le | simp, ?_⟩, rfl⟩)
       have hp0 : p ≠ 0 := by
         rintro rfl
         simp at hd
       have htd : p.totalDegree ≤ n := by
         first
         | exact hph.totalDegree_le
         | exact (hph.totalDegree hp0).le
       have hsum : (d.sum fun _ e => e) ≤ n := (MvPolynomial.le_totalDegree hd).trans htd
       intro i
       have h1 : d i ≤ d.sum (fun _ e => e) := by
         by_cases hi : i ∈ d.support
         · exact Finset.single_le_sum (f := fun j => d j) (fun j _ => Nat.zero_le _) hi
         · rw [Finsupp.mem_support_iff, not_not] at hi
           rw [hi]
           exact Nat.zero_le _
       simpa [c] using h1.trans hsum
     haveI : FiniteDimensional ℂ (Submodule.span ℂ
         ((fun d => MvPolynomial.monomial d (1 : ℂ)) '' Set.Icc (0 : σ →₀ ℕ) c)) :=
       FiniteDimensional.span_of_finite ℂ (hS.image _)
     exact Submodule.finiteDimensional_of_le hle)


set_option maxHeartbeats 800000 in
lemma exists_orth [Fintype σ] (K : Submodule ℂ (MvPolynomial σ ℂ)) (n : ℕ)
    (hK : K ≤ FockH1Action.homog σ n) (f : MvPolynomial σ ℂ) :
    ∃ y ∈ K, ∀ x ∈ K, FockH1Action.fockInner x (f - y) = 0 := by
  classical
  haveI : FiniteDimensional ℂ (FockH1Action.homog σ n) := finiteDimensional_homog' n
  have hfin : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le hK
  let K' : Submodule ℂ (FockV σ) := K
  haveI : FiniteDimensional ℂ K' := hfin
  letI : NormedAddCommGroup (FockV σ) := (fockCore (σ := σ)).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (FockV σ) := by
    first
    | exact InnerProductSpace.ofCore (fockCore (σ := σ)).toCore
    | exact InnerProductSpace.ofCore (fockCore (σ := σ)).toPreInnerProductSpaceCore
    | exact InnerProductSpace.ofCore (fockCore (σ := σ))
  haveI hproj : K'.HasOrthogonalProjection := inferInstance
  let g : FockV σ := f
  let P := K'.orthogonalProjection g
  have hP : ∀ x ∈ K', inner ℂ x (g - (P : FockV σ)) = 0 := by
    first
    | exact K'.orthogonalProjection_inner_eq_zero g
    | exact fun x hx => (K'.mem_orthogonal _).1 (K'.sub_orthogonalProjection_mem_orthogonal g) x hx
    | exact fun x hx => (K'.mem_orthogonal _).1 (K'.sub_starProjection_mem_orthogonal g) x hx
  have key : ∀ x y : FockV σ, inner ℂ x y = FockH1Action.fockInner (σ := σ) x y := fun _ _ => rfl
  let q : MvPolynomial σ ℂ := (P : FockV σ)
  have hsub : g - (P : FockV σ) = (show FockV σ from f - q) := rfl
  refine ⟨(P : FockV σ), P.2, fun x hx => ?_⟩
  have h1 := hP x hx
  rw [hsub] at h1
  have h2 : FockH1Action.fockInner (σ := σ) x (f - q) = 0 := (key x (f - q)).symm.trans h1
  exact h2

end PI.FHS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.ConjTransposeOneKronecker
noncomputable section

open MvPolynomial Matrix FockH1Action

namespace PI.FHS

section Sums

variable {σ : Type*}

lemma fockInner_sum_left {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, fockInner (f i) Q := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty, fockInner_zero_left]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, fockInner_add_left, ih]

lemma fockInner_sum_right {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (P : MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ t, f i) = ∑ i ∈ t, fockInner P (f i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty, fockInner_zero_right]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, fockInner_add_right, ih]

end Sums

variable {p q r s : ℕ}

lemma omE_apply_of_ne {l l' : Ln p q r s} (h : l ≠ l') (P : Pol p q r s) :
    omE l l' P = raiB l (lowB l' P) := by
  rw [FockH1Action.omE, if_neg h, add_zero]; rfl

private theorem raiB_apply_eq_X_mul_of_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = true)
    (P : FockH1Action.Pol p q r s) : FockH1Action.raiB m P = X m * P := by
  rw [FockH1Action.raiB, if_pos h]; rfl

private theorem raiB_apply_eq_neg_pderiv_of_not_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = false)
    (P : FockH1Action.Pol p q r s) : FockH1Action.raiB m P = -(pderiv m P) := by
  rw [FockH1Action.raiB, if_neg (by simp [h])]; rfl

private theorem lowB_apply_eq_pderiv_of_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = true)
    (P : FockH1Action.Pol p q r s) : FockH1Action.lowB m P = pderiv m P := by
  rw [FockH1Action.lowB, if_pos h]; rfl

private theorem lowB_apply_eq_X_mul_of_not_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = false)
    (P : FockH1Action.Pol p q r s) : FockH1Action.lowB m P = X m * P := by
  rw [FockH1Action.lowB, if_neg (by simp [h])]; rfl

lemma omE_adj {l l' : Ln p q r s} (h : linePos l ≠ linePos l') (P Q : Pol p q r s) :
    fockInner (omE l l' P) Q = - fockInner P (omE l' l Q) := by
  have hne : l ≠ l' := fun e => h (e ▸ rfl)
  rw [omE_apply_of_ne hne, omE_apply_of_ne (Ne.symm hne)]
  cases hl : FockH1Action.linePos l <;> cases hl' : FockH1Action.linePos l'
  · exact absurd (hl.trans hl'.symm) h
  · rw [lowB_apply_eq_pderiv_of_linePos hl', raiB_apply_eq_neg_pderiv_of_not_linePos hl, lowB_apply_eq_X_mul_of_not_linePos hl, raiB_apply_eq_X_mul_of_linePos hl',
      fockInner_neg_left, fockInner_pderiv, fockInner_pderiv]
  · rw [lowB_apply_eq_X_mul_of_not_linePos hl', raiB_apply_eq_X_mul_of_linePos hl, lowB_apply_eq_pderiv_of_linePos hl, raiB_apply_eq_neg_pderiv_of_not_linePos hl',
      fockInner_neg_right, neg_neg, fockInner_X_mul, fockInner_X_mul]
  · exact absurd (hl.trans hl'.symm) h

lemma omAct_apply (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    omAct p q r s M P = ∑ l, ∑ l', M l l' • omE l l' P := by
  simp [FockH1Action.omAct, LinearMap.sum_apply, LinearMap.smulRight_apply]

def Mixed (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Prop :=
  ∀ l l', M l l' ≠ 0 → linePos l ≠ linePos l'

lemma omAct_adj (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (hM : Mixed M) (P Q : Pol p q r s) :
    fockInner (omAct p q r s M P) Q = - fockInner P (omAct p q r s Mᴴ Q) := by
  rw [omAct_apply, omAct_apply]
  simp only [fockInner_sum_left, fockInner_sum_right, fockInner_smul_left,
    fockInner_smul_right, Matrix.conjTranspose_apply]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  by_cases hz : M l l' = 0
  · simp [hz]
  · rw [omE_adj (hM l l' hz), mul_neg]
    rfl

lemma sameBlock_symm {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> simp_all [FockH1Action.sameBlock]

lemma isPC_ct {Z : Mat p q} (h : IsPC Z) : IsPC Zᴴ := by
  intro a b hab
  simp [Matrix.conjTranspose_apply, h b a (sameBlock_symm hab)]

lemma fockAct1_eq (Z : Mat p q) :
    fockAct1 p q r s Z = omAct p q r s (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s)) :=
  rfl

lemma fockAct2_eq (Z : Mat r s) :
    fockAct2 p q r s Z = omAct p q r s (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z) :=
  rfl

lemma mixed1 {Z : Mat p q} (hZ : IsPC Z) :
    Mixed (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s)) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ hne
  simp only [Matrix.kroneckerMap_apply] at hne
  by_cases hcd : c = d
  · subst hcd
    have hs : ¬ FockH1Action.sameBlock a b := fun hab => hne (by rw [hZ a b hab, zero_mul])
    clear hne hZ
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [FockH1Action.sameBlock, FockH1Action.linePos]
  · exact absurd (by rw [Matrix.one_apply_ne hcd, mul_zero]) hne

lemma mixed2 {Z : Mat r s} (hZ : IsPC Z) :
    Mixed (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ hne
  simp only [Matrix.kroneckerMap_apply] at hne
  by_cases hab : a = b
  · subst hab
    have hs : ¬ FockH1Action.sameBlock c d := fun hcd => hne (by rw [hZ c d hcd, mul_zero])
    clear hne hZ
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      simp_all [FockH1Action.sameBlock, FockH1Action.linePos]
  · exact absurd (by rw [Matrix.one_apply_ne hab, zero_mul]) hne

lemma conjTranspose_kronecker_one (Z : Mat p q) :
    (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s))ᴴ =
      Matrix.kroneckerMap (fun a b => a * b) Zᴴ (1 : Mat r s) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  by_cases hcd : c = d
  · subst hcd; simp
  · rw [Matrix.one_apply_ne hcd, Matrix.one_apply_ne (Ne.symm hcd)]; simp

lemma conjTranspose_one_kronecker (Z : Mat r s) :
    (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z)ᴴ =
      Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Zᴴ := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab)]; simp

theorem fockAct1_adj {Z : Mat p q} (hZ : IsPC Z) (P Q : Pol p q r s) :
    fockInner (fockAct1 p q r s Z P) Q = - fockInner P (fockAct1 p q r s Zᴴ Q) := by
  rw [fockAct1_eq, fockAct1_eq,
    omAct_adj _ (mixed1 hZ), conjTranspose_kronecker_one]

theorem fockAct2_adj {Z : Mat r s} (hZ : IsPC Z) (P Q : Pol p q r s) :
    fockInner (fockAct2 p q r s Z P) Q = - fockInner P (fockAct2 p q r s Zᴴ Q) := by
  rw [fockAct2_eq, fockAct2_eq,
    omAct_adj _ (mixed2 hZ), conjTranspose_one_kronecker]

end PI.FHS
end
end

noncomputable section

open MvPolynomial Matrix FockH1Action

namespace PI.FHS

section Parts

variable {σ : Type*}

lemma plusPart_of_mem {A : Module.End ℂ (MvPolynomial σ ℂ)} {d : ℕ} {P : MvPolynomial σ ℂ}
    (hP : P ∈ homog σ d) : plusPart A P = homogeneousComponent (d + 2) (A P) := by
  unfold plusPart
  rw [finsum_eq_single _ d]
  · rw [homogeneousComponent_of_mem hP, if_pos rfl]
  · intro e he
    rw [homogeneousComponent_of_mem hP, if_neg he, map_zero, map_zero]

lemma minusPart_of_mem {A : Module.End ℂ (MvPolynomial σ ℂ)} {d : ℕ} {Q : MvPolynomial σ ℂ}
    (hQ : Q ∈ homog σ (d + 2)) : minusPart A Q = homogeneousComponent d (A Q) := by
  unfold minusPart
  rw [finsum_eq_single _ d]
  · rw [homogeneousComponent_of_mem hQ, if_pos rfl]
  · intro e he
    rw [homogeneousComponent_of_mem hQ, if_neg (by omega), map_zero, map_zero]

end Parts

variable {p q r s : ℕ}

lemma kill {a b : ℕ} (A : Mat a b →ₗ[ℂ] Module.End ℂ (Pol p q r s))
    (hA : ∀ Z : Mat a b, IsPC Z → ∀ P Q, fockInner (A Z P) Q = - fockInner P (A Zᴴ Q))
    {d : ℕ} {z : Pol p q r s} (hz : z ∈ homog (Ix p q × Ix r s) (d + 2))
    (horth : ∀ Z : Mat a b, IsPC Z → ∀ g ∈ homog (Ix p q × Ix r s) d,
      fockInner (plusPart (A Z) g) z = 0)
    (Z : Mat a b) (hZ : IsPC Z) : minusPart (A Z) z = 0 := by
  have hm : minusPart (A Z) z = homogeneousComponent d (A Z z) := minusPart_of_mem hz
  have hmem : minusPart (A Z) z ∈ homog (Ix p q × Ix r s) d := by
    rw [hm]
    exact homogeneousComponent_mem d _
  apply fockInner_self_eq_zero
  calc fockInner (minusPart (A Z) z) (minusPart (A Z) z)
      = fockInner (homogeneousComponent d (A Z z)) (minusPart (A Z) z) := by rw [← hm]
    _ = fockInner (A Z z) (minusPart (A Z) z) := fockInner_hc_left _ _ hmem
    _ = - fockInner z (A Zᴴ (minusPart (A Z) z)) := hA Z hZ _ _
    _ = - fockInner z (homogeneousComponent (d + 2) (A Zᴴ (minusPart (A Z) z))) := by
        rw [fockInner_hc_right _ _ hz]
    _ = - fockInner z (plusPart (A Zᴴ) (minusPart (A Z) z)) := by rw [plusPart_of_mem hmem]
    _ = 0 := by rw [← fockInner_conj, horth Zᴴ (isPC_ct hZ) _ hmem, map_zero, neg_zero]

theorem harmSplit : PI.FockDegreeTwoParts.HarmSplit := by
  intro p q r s u1 u2 _ d
  have hRle : Submodule.span ℂ (raised p q r s u1 u2 d) ≤ homog (Ix p q × Ix r s) (d + 2) := by
    rw [Submodule.span_le]
    rintro R ⟨Q, hQ, h | h⟩
    · obtain ⟨_, Z, _, rfl⟩ := h
      rw [SetLike.mem_coe, plusPart_of_mem hQ]
      exact homogeneousComponent_mem _ _
    · obtain ⟨_, Z, _, rfl⟩ := h
      rw [SetLike.mem_coe, plusPart_of_mem hQ]
      exact homogeneousComponent_mem _ _
  apply le_antisymm
  · intro f hf
    obtain ⟨y, hy, horth⟩ := exists_orth (Submodule.span ℂ (raised p q r s u1 u2 d)) (d + 2) hRle f
    have hfy : f - y ∈ homog (Ix p q × Ix r s) (d + 2) := Submodule.sub_mem _ hf (hRle hy)
    have hlow : f - y ∈ lowKer p q r s u1 u2 := by
      refine ⟨fun hu Z hZ => ?_, fun hu Z hZ => ?_⟩
      · refine kill (fockAct1 p q r s) (fun Z hZ P Q => fockAct1_adj hZ P Q) hfy (fun Z' hZ' g hg => ?_) Z hZ
        exact horth _ (Submodule.subset_span ⟨g, hg, Or.inl ⟨hu, Z', hZ', rfl⟩⟩)
      · refine kill (fockAct2 p q r s) (fun Z hZ P Q => fockAct2_adj hZ P Q) hfy (fun Z' hZ' g hg => ?_) Z hZ
        exact horth _ (Submodule.subset_span ⟨g, hg, Or.inr ⟨hu, Z', hZ', rfl⟩⟩)
    have hsplit : f = (f - y) + y := by abel
    rw [hsplit]
    exact Submodule.add_mem_sup ⟨hfy, Submodule.subset_span hlow⟩ hy
  · exact sup_le inf_le_left hRle

end PI.FHS
end
end

theorem harmonicSplitting_holds : PI.FockDegreeTwoParts.HarmSplit := PI.FHS.harmSplit
