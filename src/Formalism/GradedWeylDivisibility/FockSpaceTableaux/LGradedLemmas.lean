module

public import Formalism.GradedWeylDivisibility.StatementB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

@[expose] public section

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lgraded_wa {r n : ℕ} (a : Fin r) : Fin r × Fin n → ℕ := fun v => if v.1 = a then 1 else 0

theorem lgraded_rowGen_X {r n : ℕ} (a : Fin r) (v : Fin r × Fin n) :
    rowGen ℚ a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (lgraded_wa (n := n) a v) := by
  obtain ⟨b, j⟩ := v
  simp only [rowGen, aeval_X, lgraded_wa]
  by_cases h : b = a
  · subst h
    rw [if_pos rfl, if_pos rfl, pow_one]
    ring
  · simp [h]

theorem lgraded_rowGen_C {r n : ℕ} (a : Fin r) (c : ℚ) :
    rowGen ℚ a a (C c : MvPolynomial (Fin r × Fin n) ℚ) = Polynomial.C (C c) := by
  rw [rowGen, aeval_C, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem lgraded_rowGen_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℚ) :
    rowGen ℚ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  induction m using Finsupp.induction
  next => rw [monomial_zero', lgraded_rowGen_C]; simp
  next v k m _ _ ih =>
    have hw : Finsupp.weight (lgraded_wa a) (Finsupp.single v k) = k * lgraded_wa a v := by
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    rw [add_comm, monomial_add_single, map_mul, ih, map_pow, lgraded_rowGen_X, map_add (f := _), map_mul,
      map_pow, hw, mul_pow, ← pow_mul, pow_add, mul_comm (lgraded_wa a v) k]
    ring

theorem lgraded_euler_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℚ) :
    rowDiv ℚ a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) • monomial m c := by
  rw [rowDiv, lgraded_rowGen_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]

theorem lgraded_coeff_euler {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ)
    (m : Fin r × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (rowDiv ℚ a a 1 f) m = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) * AddMonoidAlgebra.coeff f m := by
  induction f using MvPolynomial.induction_on'
  next m' c' =>
    rw [lgraded_euler_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  next p q hp hq =>
    have hpq : rowDiv ℚ a a 1 (p + q) = rowDiv ℚ a a 1 p + rowDiv ℚ a a 1 q := by
      simp only [rowDiv, map_add (f := _), Polynomial.coeff_add]
    rw [hpq, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem lgraded_weight_rowW {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = Finsupp.weight (lgraded_wa a) m := by
  simp only [Finsupp.weight_apply, rowW, lgraded_wa]
  simp only [Finsupp.sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : v.1 = a
  · simp [h]
  · simp [h, Ne.symm h]

private lemma exists_mem_coeff_eq_prod_weight_sub_mul_coeff {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ))
    (hM : RowDivClosed M) (a : Fin r) (T : Finset ℕ) : ∀ g ∈ M, ∃ h ∈ M, ∀ m, AddMonoidAlgebra.coeff h m =
      (∏ s ∈ T, (((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) - (s : ℚ))) * AddMonoidAlgebra.coeff g m := by
  classical
  induction T using Finset.induction_on
  next => intro g hg; exact ⟨g, hg, fun m => by simp⟩
  next s T hs ih =>
    intro g hg
    obtain ⟨h, hh, hc⟩ := ih g hg
    refine ⟨rowDiv ℚ a a 1 h - (s : ℚ) • h, M.sub_mem (hM a a 1 h hh) (M.smul_mem _ hh), fun m => ?_⟩
    rw [coeff_sub, coeff_smul, lgraded_coeff_euler, hc, Finset.prod_insert hs, smul_eq_mul]
    ring

theorem lgraded_sep {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M)
    (a : Fin r) (V : Finset ℕ) :
    ∀ f ∈ M, (∀ m ∈ f.support, Finsupp.weight (lgraded_wa a) m ∈ V) →
      ∀ t, weightedHomogeneousComponent (lgraded_wa a) t f ∈ M := by
  intro f hf hV t
  classical
  obtain ⟨h, hh, hc⟩ := exists_mem_coeff_eq_prod_weight_sub_mul_coeff M hM a (V.erase t) f hf
  have key : weightedHomogeneousComponent (lgraded_wa a) t f =
      (∏ s ∈ V.erase t, ((t : ℚ) - (s : ℚ)))⁻¹ • h := by
    ext m
    rw [coeff_weightedHomogeneousComponent, coeff_smul, hc, smul_eq_mul]
    by_cases hm : m ∈ f.support
    · have hmV := hV m hm
      split_ifs with hw
      · rw [hw]
        have hne : (∏ s ∈ V.erase t, ((t : ℚ) - (s : ℚ))) ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro s hs
          have hst := (Finset.mem_erase.1 hs).1
          exact sub_ne_zero.2 (by exact_mod_cast hst.symm)
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      · have hmem : Finsupp.weight (lgraded_wa a) m ∈ V.erase t := Finset.mem_erase.2 ⟨hw, hmV⟩
        have h0 : ∏ s ∈ V.erase t,
            (((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) - (s : ℚ)) = 0 :=
          Finset.prod_eq_zero hmem (sub_self _)
        rw [h0]
        simp
    · rw [mem_support_iff, not_not] at hm
      simp [hm]
  rw [key]
  exact M.smul_mem _ hh

theorem lgraded_multi {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M)
    (μ : Fin r → ℕ) (A : Finset (Fin r)) :
    ∀ f ∈ M, ∃ h ∈ M, ∀ m, AddMonoidAlgebra.coeff h m =
      if (∀ a ∈ A, Finsupp.weight (lgraded_wa a) m = μ a) then AddMonoidAlgebra.coeff f m else 0 := by
  classical
  induction A using Finset.induction_on
  next => intro f hf; exact ⟨f, hf, fun m => by simp⟩
  next b A hb ih =>
    intro f hf
    obtain ⟨h, hh, hc⟩ := ih f hf
    refine ⟨weightedHomogeneousComponent (lgraded_wa b) (μ b) h,
      lgraded_sep M hM b (h.support.image (Finsupp.weight (lgraded_wa b))) h hh
        (fun m hm => Finset.mem_image_of_mem _ hm) (μ b), fun m => ?_⟩
    rw [coeff_weightedHomogeneousComponent, hc]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    by_cases h1 : Finsupp.weight (lgraded_wa b) m = μ b <;> simp [h1]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem rowdiv_mem_dualWeyl_iff (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

def CoeffHom {R : Type*} [CommRing R] {r n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R))
    (μ : Fin n → ℕ) : Prop :=
  ∀ k, IsWeightedHomogeneous (colW r n) (P.coeff k) μ

theorem CoeffHom.mul {R : Type*} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' : Fin n → ℕ}
    (hP : CoeffHom P μ) (hQ : CoeffHom Q μ') : CoeffHom (P * Q) (μ + μ') := by
  intro k
  rw [Polynomial.coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ fun x _ => (hP x.1).mul (hQ x.2)

theorem CoeffHom.one {R : Type*} [CommRing R] {r n : ℕ} :
    CoeffHom (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs
  · exact isWeightedHomogeneous_one R _
  · exact isWeightedHomogeneous_zero R _ _

theorem CoeffHom.pow {R : Type*} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ : Fin n → ℕ}
    (hP : CoeffHom P μ) (e : ℕ) : CoeffHom (P ^ e) (e • μ) := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact CoeffHom.one
  | succ e ih => rw [pow_succ, succ_nsmul]; exact ih.mul hP

theorem CoeffHom.prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → Fin n → ℕ)
    (h : ∀ i ∈ s, CoeffHom (P i) (μ i)) : CoeffHom (∏ i ∈ s, P i) (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CoeffHom.one (R := R) (r := r) (n := n))
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem CoeffHom.algebraMap {R : Type*} [CommRing R] {r n : ℕ} (c : R) :
    CoeffHom (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs
  · rw [MvPolynomial.algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  · exact isWeightedHomogeneous_zero R _ _

theorem CoeffHom.gen {R : Type*} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    CoeffHom (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (colW r n v) := by
  intro k
  have hX : IsWeightedHomogeneous (colW r n) (X v : MvPolynomial (Fin r × Fin n) R) (colW r n v) :=
    isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (colW r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (colW r n v) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs
    · exact hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs
      · exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

theorem CoeffHom.rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    CoeffHom (rowGen R a b (monomial d c)) (Finsupp.weight (colW r n) d) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine (CoeffHom.algebraMap c).mul ?_
  unfold Finsupp.prod Finsupp.sum
  exact CoeffHom.prod _ _ _ fun v _ => (CoeffHom.gen a b v).pow _

theorem rowDiv_homog (R : Type*) [CommRing R] {r n : ℕ} (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (colW r n) f ν) :
    IsWeightedHomogeneous (colW r n) (rowDiv R a b k f) ν := by
  unfold rowDiv
  conv => pattern f; rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := CoeffHom.rowGen_monomial R a b d (AddMonoidAlgebra.coeff f d) k
  rwa [hf (mem_support_iff.mp hd)] at this

def rowGenO (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R]
      Polynomial (MvPolynomial (Option (Fin r × Fin n)) R) :=
  aeval fun o => Option.elim o (Polynomial.C (X none)) fun v =>
    Polynomial.C (X (some v)) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (some (a, v.2))) else 0)

theorem rowGenO_comp_colAddGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (l j : Fin n) :
    (rowGenO R a b).comp (colAddGen R (r := r) l j) =
      (Polynomial.mapAlgHom (colAddGen R (r := r) l j)).comp (rowGen R a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]
  by_cases h2 : v.2 = j <;> by_cases h1 : v.1 = b <;>
    simp [h1, h2, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
      aeval_X] <;> ring

theorem rowGenO_comp_rename (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    (rowGenO R a b).comp (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
      (Polynomial.mapAlgHom (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n)))).comp
        (rowGen R a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, rename_X, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]
  by_cases h1 : v.1 = b <;>
    simp [h1, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]

theorem rowDiv_colAddGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : colAddGen R l j f = rename some f) :
    colAddGen R l j (rowDiv R a b k f) = rename some (rowDiv R a b k f) := by
  have hA := congrArg (fun φ => φ f) (rowGenO_comp_colAddGen R a b l j)
  have hB := congrArg (fun φ => φ f) (rowGenO_comp_rename R (n := n) a b)
  simp only [AlgHom.comp_apply, Polynomial.coe_mapAlgHom] at hA hB
  rw [hf, hB] at hA
  have hk := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P k) hA
  simp only [Polynomial.coeff_map] at hk
  unfold rowDiv
  exact hk.symm

theorem dualWeylModuleRowDividedPowerStable : RowDivStable := by
  intro R _ r n ν a b k f hf
  rw [rowdiv_mem_dualWeyl_iff] at hf ⊢
  exact ⟨rowDiv_homog R ν a b k f hf.1, fun l j hlj => rowDiv_colAddGen R a b k l j f (hf.2 l j hlj)⟩

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColSums
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lccomp_weight_colW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    (Finsupp.weight (colW r n) m) t = ∑ a : Fin r, m (a, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [colW, Pi.single_apply]

theorem columnSums_holds : ColSums := by
  intro R _ r n ν f hf m hm t
  have h1 := (Submodule.mem_inf.mp hf).1
  rw [mem_weightedHomogeneousSubmodule] at h1
  rw [← lccomp_weight_colW_apply, h1 (mem_support_iff.mp hm)]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem applyWord_hw_mem_dualWeyl
    (h1 : HWMem) (h2 : RowDivStable)
    (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∀ w : List (Fin r × Fin r × ℕ),
      applyWord R w (hw R hn ν) ∈ dualWeyl R r n ν := fun
  | [] => h1 R r n hn ν hν
  | x :: w => h2 R r n ν x.1 x.2.1 x.2.2 _
      (applyWord_hw_mem_dualWeyl h1 h2 R r n hn ν hν w)

theorem weylLeDual_of (h1 : HWMem) (h2 : RowDivStable) : WeylLeDual := by
  intro R _ r n hn ν hν
  show Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) =>
      applyWord R w (hw R hn ν)) ≤ dualWeyl R r n ν
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact applyWord_hw_mem_dualWeyl h1 h2 R r n hn ν hν w

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lsat_spec_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp (colAddGen R l j) =
      colAdd R l j c := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp

theorem lsat_spec_rename {R : Type*} [CommRing R] {r n : ℕ} (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp
      (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rename_X]

theorem lsat_eval_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n)
    (x : Option (Fin r × Fin n) → R) :
    (aeval x).comp (colAddGen R l j) = (aeval (x ∘ some)).comp (colAdd R l j (x none)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp

theorem dualWeylModuleMemIff : DualWeylPoint := by
  intro R _ _ _ r n ν f
  rw [lsat_mem_dualWeyl]
  refine and_congr_right fun _ => forall₂_congr fun l j => imp_congr_right fun _ => ?_
  constructor
  · intro h c
    let ψ : Option (Fin r × Fin n) → MvPolynomial (Fin r × Fin n) R :=
      fun o => Option.elim o (C c) X
    have h1 : aeval ψ (colAddGen R l j f) = aeval ψ (rename some f) := by rw [h]
    have e1 : aeval ψ (colAddGen R l j f) = colAdd R l j c f := by
      rw [← AlgHom.comp_apply, lsat_spec_colAddGen]
    have e2 : aeval ψ (rename some f) = f := by
      rw [← AlgHom.comp_apply, lsat_spec_rename, AlgHom.id_apply]
    rw [← e1, h1, e2]
  · intro h
    apply MvPolynomial.funext
    intro x
    have e := congrArg (fun φ => φ f) (lsat_eval_colAddGen (R := R) l j x)
    simp only [AlgHom.comp_apply, h] at e
    change aeval x (colAddGen R l j f) = aeval x (rename some f)
    rw [e, aeval_rename]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section general

variable {σ : Type*}

lemma lfockq_eq_sum (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  refine Finset.sum_subset h (fun m _ hm => ?_)
  have hz : f.coeff m = 0 := by
    by_contra hne
    exact hm (MvPolynomial.mem_support_iff.mpr hne)
  simp [hz]

lemma lfockq_symm (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := by
  classical
  rw [lfockq_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    lfockq_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun m _ => by ring)

lemma lfockq_self_pos (f : MvPolynomial σ ℚ) (hf : f ≠ 0) : 0 < fockQ f f := by
  unfold fockQ
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hf (MvPolynomial.support_eq_empty.mp he)
  refine Finset.sum_pos (fun m hm => ?_) hne
  have hc : f.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hw : (0 : ℚ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) :=
    Nat.cast_pos.mpr (Finset.prod_pos (fun k _ => Nat.factorial_pos _))
  exact mul_pos (mul_self_pos.mpr hc) hw

lemma lfockq_add_left (f f' g : MvPolynomial σ ℚ) :
    fockQ (f + f') g = fockQ f g + fockQ f' g := by
  classical
  rw [lfockq_eq_sum (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    lfockq_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    lfockq_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)

lemma lfockq_smul_left (c : ℚ) (f g : MvPolynomial σ ℚ) :
    fockQ (c • f) g = c * fockQ f g := by
  rw [lfockq_eq_sum (c • f) g f.support MvPolynomial.support_smul,
    lfockq_eq_sum f g f.support subset_rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)

end general

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetMinor
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def initW (n s : ℕ) : Fin n → ℕ := fun t => if t.val < s then 1 else 0

theorem sum_single_castLE {n s : ℕ} (hs : s ≤ n) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hs q) 1 : Fin n → ℕ)) = initW n s := by
  funext t
  rw [Finset.sum_apply]
  simp only [initW]
  by_cases h : t.val < s
  · rw [if_pos h, Finset.sum_eq_single ⟨t.val, h⟩]
    · have e : Fin.castLE hs ⟨t.val, h⟩ = t := Fin.ext rfl
      rw [e, Pi.single_eq_same]
    · intro q _ hq
      rw [Pi.single_apply, if_neg]
      intro htq
      apply hq
      subst htq
      exact Fin.ext rfl
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Pi.single_apply, if_neg]
    intro htq
    apply h
    subst htq
    exact q.isLt

theorem initMinor_isWeightedHomogeneous {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (colW r n) (initMinor R I hs) (initW n s) := by
  rw [← mem_weightedHomogeneousSubmodule]
  unfold initMinor
  rw [Matrix.det_apply]
  refine _root_.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule, ← sum_single_castLE hs]
  apply IsWeightedHomogeneous.prod
  intro q _
  exact isWeightedHomogeneous_X (R := R) (colW r n) (I (σ q), Fin.castLE hs q)

theorem algHom_det_of {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) {s : ℕ} (M : Fin s → Fin s → A) :
    φ (Matrix.of M).det = (Matrix.of fun p q => φ (M p q)).det := by
  rw [AlgHom.map_det]
  rfl

theorem colAddGen_X {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    colAddGen R l j (X v) =
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) := by
  simp only [colAddGen, aeval_X]

theorem initMinor_invariant {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) (l j : Fin n) (hlj : l < j) :
    colAddGen R l j (initMinor R I hs) = rename some (initMinor R I hs) := by
  unfold initMinor
  rw [algHom_det_of, algHom_det_of]
  simp only [colAddGen_X, rename_X]
  by_cases hj : j.val < s
  · have hl : l.val < s := Nat.lt_trans (show l.val < j.val from hlj) hj
    have hjl : (⟨j.val, hj⟩ : Fin s) ≠ ⟨l.val, hl⟩ := by
      intro h
      exact hlj.ne' (Fin.ext (Fin.mk.inj_iff.mp h))
    rw [← Matrix.det_updateCol_add_smul_self
      (Matrix.of fun p q : Fin s =>
        (X (some (I p, Fin.castLE hs q)) : MvPolynomial (Option (Fin r × Fin n)) R)) hjl (X none)]
    congr 1
    ext p q
    simp only [Matrix.updateCol_apply, Matrix.of_apply]
    by_cases hq : q = ⟨j.val, hj⟩
    · subst hq
      have e1 : Fin.castLE hs ⟨j.val, hj⟩ = j := Fin.ext rfl
      have e2 : Fin.castLE hs ⟨l.val, hl⟩ = l := Fin.ext rfl
      rw [e1, e2]
      simp
    · have hne : Fin.castLE hs q ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        exact hq (Fin.ext hv)
      rw [if_neg hne, if_neg hq]
  · congr 1
    ext p q
    simp only [Matrix.of_apply]
    have hne : Fin.castLE hs q ≠ j := by
      intro h
      apply hj
      rw [← h]
      exact q.isLt
    rw [if_neg hne]

theorem initMinor_mem {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs ∈ dualWeyl R r n (initW n s) := by
  unfold dualWeyl
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact initMinor_isWeightedHomogeneous I hs
  · simp only [Submodule.mem_iInf]
    intro l j hlj
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact initMinor_invariant I hs l j hlj

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lhwinHt (r n : ℕ) : Fin r × Fin n → ℤ := fun v => (v.1.val : ℤ)

def LhwinShift {R : Type*} [CommRing R] {r n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R))
    (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous (lhwinHt r n) (P.coeff k) (μ + k * δ)

theorem lhwinShift_mul {R : Type*} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : LhwinShift P μ δ) (hQ : LhwinShift Q μ' δ) : LhwinShift (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have e : μ + μ' + (k : ℤ) * δ = (μ + (x.1 : ℤ) * δ) + (μ' + (x.2 : ℤ) * δ) := by
    rw [← hx']; push_cast; ring
  rw [e]
  exact (hP x.1).mul (hQ x.2)

theorem lhwinShift_one {R : Type*} [CommRing R] {r n : ℕ} (δ : ℤ) :
    LhwinShift (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    simpa using isWeightedHomogeneous_one R (lhwinHt r n)
  · exact isWeightedHomogeneous_zero R _ _

theorem lhwinShift_pow {R : Type*} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : LhwinShift P μ δ) (e : ℕ) : LhwinShift (P ^ e) (e • μ) δ := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact lhwinShift_one δ
  | succ e ih => rw [pow_succ, succ_nsmul]; exact lhwinShift_mul ih hP

theorem lhwinShift_prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, LhwinShift (P i) (μ i) δ) : LhwinShift (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (lhwinShift_one (R := R) (r := r) (n := n) δ)
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact lhwinShift_mul (h i (Finset.mem_insert_self _ _))
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lhwinShift_algebraMap {R : Type*} [CommRing R] {r n : ℕ} (c : R) (δ : ℤ) :
    LhwinShift (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [MvPolynomial.algebraMap_eq]
    simpa using isWeightedHomogeneous_C (lhwinHt r n) c
  · exact isWeightedHomogeneous_zero R _ _

theorem lhwinShift_gen {R : Type*} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    LhwinShift (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (lhwinHt r n v) ((a.val : ℤ) - b.val) := by
  intro k
  have hX : IsWeightedHomogeneous (lhwinHt r n) (X v : MvPolynomial (Fin r × Fin n) R)
      (lhwinHt r n v) := isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (lhwinHt r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (lhwinHt r n (a, v.2)) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs with h
    · subst h; simpa using hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs with hb
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h
        have e : lhwinHt r n v + ((1 : ℕ) : ℤ) * ((a.val : ℤ) - b.val) = lhwinHt r n (a, v.2) := by
          simp [lhwinHt, hb]
        rw [e]; exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

theorem lhwinShift_rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    LhwinShift (rowGen R a b (monomial d c)) (Finsupp.weight (lhwinHt r n) d)
      ((a.val : ℤ) - b.val) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine lhwinShift_mul (lhwinShift_algebraMap c _) ?_
  unfold Finsupp.prod Finsupp.sum
  exact lhwinShift_prod _ _ _ _ fun v _ => lhwinShift_pow (lhwinShift_gen a b v) _

theorem lhwin_rowDiv_shift (R : Type*) [CommRing R] {r n : ℕ} (H : ℤ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (lhwinHt r n) f H) :
    IsWeightedHomogeneous (lhwinHt r n) (rowDiv R a b k f) (H + k * ((a.val : ℤ) - b.val)) := by
  unfold rowDiv
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := lhwinShift_rowGen_monomial R a b d (AddMonoidAlgebra.coeff f d) k
  rwa [hf (mem_support_iff.mp hd)] at this

theorem lhwin_weight_ht {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (lhwinHt r n) d =
      ∑ a : Fin r, (a.val : ℤ) * ((Finsupp.weight (rowW r n) d a : ℕ) : ℤ) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add (f := _), Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib, hf, hg]
  | single v c =>
    simp [Finsupp.weight_apply, lhwinHt, rowW, Pi.single_apply, Finsupp.sum_single_index, mul_comm]

theorem lhwin_weight_nonneg {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    0 ≤ Finsupp.weight (lhwinHt r n) d := by
  rw [lhwin_weight_ht]
  exact Finset.sum_nonneg fun a _ => by positivity

theorem lhwin_nonneg {R : Type*} [CommRing R] {r n : ℕ} {g : MvPolynomial (Fin r × Fin n) R} {z : ℤ}
    (hg : g ≠ 0) (hz : IsWeightedHomogeneous (lhwinHt r n) g z) : 0 ≤ z := by
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hg
  rw [← hz hd]
  exact lhwin_weight_nonneg d

theorem lhwin_exists_killed (h2 : RowDivClosedGraded) {r n : ℕ}
    (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℚ a b k v = 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ IsWeightedHomogeneous (lhwinHt r n) v (N : ℤ) := by
    obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hf0
    refine ⟨∑ a : Fin r, a.val * Finsupp.weight (rowW r n) d a,
      weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) d) f,
      h2 r n M hM f hfM _, ?_, ?_⟩
    · intro h
      apply hd
      have := congrArg (AddMonoidAlgebra.coeff · d) h
      simpa only [coeff_weightedHomogeneousComponent, if_pos rfl, if_true, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using this
    · intro e he
      rw [coeff_weightedHomogeneousComponent] at he
      split_ifs at he with hμ
      · rw [lhwin_weight_ht, hμ]; push_cast; rfl
      · exact absurd rfl he
  obtain ⟨v, hvM, hv0, hvH⟩ := Nat.find_spec hex
  refine ⟨v, hvM, hv0, fun a b hab k hk => ?_⟩
  by_contra hne'
  have hH := lhwin_rowDiv_shift ℚ _ a b k v hvH
  have hnn := lhwin_nonneg hne' hH
  have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hlt : ((Nat.find hex : ℕ) : ℤ) + k * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ) := by
    nlinarith
  have hmin := Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + k * ((a.val : ℤ) - b.val)).toNat)
    (by omega)
  apply hmin
  refine ⟨_, hM a b k v hvM, hne', ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  exact hH

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleMap : DualWeylMap := by
  intro R S _ _ φ r n ν f hf
  rw [lsat_mem_dualWeyl] at hf ⊢
  refine ⟨lsat_isWH_map φ _ _ f hf.1, fun l j hlj => ?_⟩
  rw [← lsat_map_colAddGen, hf.2 l j hlj, map_rename]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleRowActionStable : DualWeylRowStable := by
  intro R _ r n ν g f hf
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  obtain ⟨hw, hc⟩ := hf
  refine ⟨isWH_algHom (rowAct R g) (colW r n) (colW r n)
    (rowAct_X_isWH g) hw, ?_⟩
  intro l j hlj
  rw [colAddGen_rowAct, rename_rowAct, hc l j hlj]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCpeelLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcpeel_weight_apply {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (d : Fin r × Fin n →₀ ℕ)
    (b : Fin r) (t : Fin n) :
    Finsupp.weight (pairW l j) d (b, t) =
      if t = l then d (b, l) + d (b, j) else if t = j then 0 else d (b, t) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add (f := _), Finsupp.add_apply, hf, hg]
    split_ifs <;> omega
  | single v k =>
    obtain ⟨a, s⟩ := v
    simp only [Finsupp.weight_apply, Finsupp.sum_single_index, zero_smul, Finsupp.smul_apply,
      pairW, smul_eq_mul]
    by_cases hs : s = j <;> by_cases ht : t = l <;> by_cases htj : t = j <;> by_cases hab : a = b <;>
      simp_all [Finsupp.single_apply, Prod.ext_iff, eq_comm]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj
open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma LFocks_subAdj {σ : Type*} [Fintype σ] [DecidableEq σ] (U : Matrix σ σ ℂ)
    (f g : MvPolynomial σ ℂ) :
    fockF (sub U f) g = fockF f (sub U.conjTranspose g) := by
  induction f using MvPolynomial.induction_on generalizing g
  · rename_i a
    rw [LFocks_sub_C, LFocks_C_left, LFocks_C_left,
      LFocks_constantCoeff_sub]
  · rename_i p q hp hq
    rw [map_add (f := _), Formalism.REAL.fischerInner_add_left, Formalism.REAL.fischerInner_add_left, hp, hq]
  · rename_i p i hp
    rw [map_mul, LFocks_sub_X, mul_comm p (X i), Formalism.REAL.fischerInner_X_mul_left i p,
      LFocks_pderiv_sub, Formalism.REAL.fischerInner_sum_right, Finset.mul_sum, Formalism.REAL.fischerInner_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LFocks_C_mul_right, ← hp, Matrix.conjTranspose_apply, star_star,
      mul_comm (sub U p), mul_assoc, LFocks_C_mul_left,
      Formalism.REAL.fischerInner_X_mul_left]

theorem fischerInnerSubstitutionAdjoint : FockSubAdj :=
  fun _ _ _ U f g => LFocks_subAdj U f g

end Formalism.GradedWeylDivisibility
end
end
