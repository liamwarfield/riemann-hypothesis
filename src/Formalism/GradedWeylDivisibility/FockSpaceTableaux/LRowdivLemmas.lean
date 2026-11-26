module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero

@[expose] public section

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem rowDiv_add (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  simp only [rowDiv, map_add (f := _), Polynomial.coeff_add]

theorem rowDiv_smul (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (c : R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]

def rowDivL (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) :
    MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R where
  toFun := rowDiv R a b k
  map_add' := rowDiv_add R a b k
  map_smul' := rowDiv_smul R a b k

@[simp] theorem rowDivL_apply (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : rowDivL R a b k f = rowDiv R a b k f := rfl

theorem applyWord_nil (R : Type*) [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R [] f = f := rfl

theorem applyWord_cons (R : Type*) [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ)
    (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) f = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) := rfl

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

section general

variable {σ : Type*}

lemma LFocks_C_mul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (C c * f) g = c * fockF f g := by
  rw [C_mul', fischerInner_eq_sum_of_subset (c • f) g f.support support_smul, fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

lemma LFocks_C_mul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (C c * g) = star c * fockF f g := by
  simp only [fockF, coeff_C_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

lemma LFocks_C_left (a : ℂ) (g : MvPolynomial σ ℂ) :
    fockF (C a) g = a * star (constantCoeff g) := by
  rw [C_apply, fischerInner_monomial_left, Finsupp.support_zero, Finset.prod_empty, Nat.cast_one, mul_one,
    constantCoeff_eq]

end general

variable {σ : Type*} [Fintype σ]

lemma LFocks_sub_X (U : Matrix σ σ ℂ) (i : σ) :
    sub U (X i) = ∑ j, C (U i j) * X j := by
  unfold sub
  exact aeval_X _ _

lemma LFocks_sub_C (U : Matrix σ σ ℂ) (a : ℂ) :
    sub U (C a) = C a := by
  unfold sub
  rw [aeval_C, algebraMap_eq]

lemma LFocks_constantCoeff_sub (U : Matrix σ σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (sub U g) = constantCoeff g := by
  induction g using MvPolynomial.induction_on
  next a => rw [LFocks_sub_C]
  next p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  next p i hp =>
    rw [map_mul, map_mul, map_mul, LFocks_sub_X]
    simp

lemma LFocks_sub_comp (A B : Matrix σ σ ℂ) :
    (sub A).comp (sub B) = sub (B * A) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AlgHom.comp_apply, LFocks_sub_X, LFocks_sub_X, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, LFocks_sub_C, LFocks_sub_X, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

variable [DecidableEq σ]

lemma LFocks_sub_one : sub (1 : Matrix σ σ ℂ) = AlgHom.id ℂ (MvPolynomial σ ℂ) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [LFocks_sub_X, Matrix.one_apply]

lemma LFocks_pderiv_sub (V : Matrix σ σ ℂ) (i : σ) (g : MvPolynomial σ ℂ) :
    pderiv i (sub V g) = ∑ j, C (V j i) * sub V (pderiv j g) := by
  induction g using MvPolynomial.induction_on
  next a => simp
  next p q hp hq => simp only [map_add (f := _), mul_add, Finset.sum_add_distrib, hp, hq]
  next p k hp =>
    have hS : pderiv i (sub V (X k)) = C (V k i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LFocks_sub_X, map_sum]
      simp [pderiv_X, Pi.single_apply]
    have hT : ∀ j, sub V (pderiv j (X k : MvPolynomial σ ℂ)) = if j = k then 1 else 0 := by
      intro j
      rw [pderiv_X]
      by_cases h : j = k
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [map_mul, pderiv_mul, hp, hS]
    simp only [pderiv_mul, map_add (f := _), map_mul, hT, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp [mul_comm]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem mem_dualWeyl_iff {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔
      IsWeightedHomogeneous (colW r n) f ν ∧
        ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  unfold dualWeyl
  simp only [Submodule.mem_inf, mem_weightedHomogeneousSubmodule, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]

theorem dualWeyl_mul {R : Type*} [CommRing R] {r n : ℕ} {ν μ : Fin n → ℕ}
    {f g : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ dualWeyl R r n ν) (hg : g ∈ dualWeyl R r n μ) :
    f * g ∈ dualWeyl R r n (ν + μ) := by
  rw [mem_dualWeyl_iff] at *
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

theorem one_mem_dualWeyl {R : Type*} [CommRing R] {r n : ℕ} :
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  rw [mem_dualWeyl_iff]
  refine ⟨isWeightedHomogeneous_one _ _, fun l j _ => ?_⟩
  rw [map_one, map_one]

theorem dualWeyl_pow {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (k : ℕ) :
    f ^ k ∈ dualWeyl R r n (k • ν) := by
  induction k with
  | zero => simpa using (one_mem_dualWeyl (R := R) (r := r) (n := n))
  | succ k ih => rw [pow_succ, succ_nsmul]; exact dualWeyl_mul ih hf

theorem dualWeyl_prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (ν : ι → Fin n → ℕ) (f : ι → MvPolynomial (Fin r × Fin n) R)
    (hf : ∀ i ∈ s, f i ∈ dualWeyl R r n (ν i)) :
    (∏ i ∈ s, f i) ∈ dualWeyl R r n (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one_mem_dualWeyl (R := R) (r := r) (n := n))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact dualWeyl_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem dualWeyl_of_eq {R : Type*} [CommRing R] {r n : ℕ} {ν μ : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (h : ν = μ) :
    f ∈ dualWeyl R r n μ := h ▸ hf

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
namespace Formalism.GradedWeylDivisibility

open MvPolynomial

def idPoint (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → R :=
  fun v => if v.1.val = v.2.val then 1 else 0

theorem eval_idPoint_lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r)
    (hn : s ≤ n) : eval (idPoint R r n) (lpMinor R s hr hn) = 1 := by
  unfold lpMinor
  rw [RingHom.map_det]
  convert Matrix.det_one (R := R) (n := Fin s)
  ext p q
  simp [RingHom.mapMatrix_apply, idPoint, Matrix.one_apply]
  exact if_congr Fin.val_inj rfl rfl

theorem hwrow_sum_single_castLE {r s : ℕ} (hr : s ≤ r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      fun a => if a.val < s then 1 else 0 := by
  have h1 : (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      ∑ q : Fin s, (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ) :=
    Equiv.sum_comp σ (fun q => (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ))
  rw [h1]
  funext a
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · exact if_pos (Fin.ext rfl)
    · intro b _ hb
      rw [if_neg]
      intro hab
      subst hab
      exact hb (Fin.ext rfl)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hab
    subst hab
    exact h b.isLt

theorem lpMinor_rowHom (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (lpMinor R s hr hn)
      (fun a => if a.val < s then 1 else 0) := by
  unfold lpMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hk : IsWeightedHomogeneous (rowW r n)
      (∏ i, (Matrix.of fun p q : Fin s =>
        (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) (σ i) i)
      (fun a : Fin r => if a.val < s then 1 else 0) := by
    rw [← hwrow_sum_single_castLE hr σ]
    apply IsWeightedHomogeneous.prod
    intro i _
    simp only [Matrix.of_apply]
    exact isWeightedHomogeneous_X R (rowW r n) _
  rw [← mem_weightedHomogeneousSubmodule] at hk ⊢
  rw [Units.smul_def]
  exact zsmul_mem hk _

end Formalism.GradedWeylDivisibility
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockbLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open Formalism.REAL (fockF)

lemma LFockb_fockF_self {σ : Type*} (f : MvPolynomial σ ℂ) :
    fockF f f = ((∑ m ∈ f.support, Complex.normSq (f.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold Formalism.REAL.fockF
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, mul_comm (starRingEnd ℂ _)]
  push_cast
  rfl

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lsat_mem_dualWeyl {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]

theorem lsat_map_colAddGen {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (colAddGen R l j f) = colAddGen S l j (map φ f) := by
  induction f using MvPolynomial.induction_on
  next a =>
    simp [colAddGen]
  next p q hp hq =>
    simp only [map_add (f := _), hp, hq]
  next p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [colAddGen, aeval_X]
    split_ifs <;> simp

theorem lsat_isWH_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {σ M : Type*}
    [AddCommMonoid M] (w : σ → M) (m : M) (f : MvPolynomial σ R)
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w (map φ f) m := by
  intro d hd
  apply hf
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowstLemmas
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section General

variable {R : Type*} [CommRing R] {σ τ M : Type*} [AddCommMonoid M]

theorem isWH_algHom_monomial (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (m : σ →₀ ℕ) (c : R) :
    IsWeightedHomogeneous w' (φ (monomial m c)) (Finsupp.weight w m) := by
  have hC : φ (C c) = C c := by
    rw [← MvPolynomial.algebraMap_eq]
    exact φ.commutes c
  rw [monomial_eq, map_mul, hC, Finsupp.prod, map_prod]
  simp only [map_pow]
  have h := (isWeightedHomogeneous_C w' c).mul
    (IsWeightedHomogeneous.prod m.support (fun v => φ (X v) ^ m v) (fun v => m v • w v)
      (fun v _ => (hφ v).pow (m v)))
  rw [zero_add] at h
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact h

theorem isWH_algHom (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) {f : MvPolynomial σ R} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) d := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  have h := isWH_algHom_monomial φ w w' hφ s (AddMonoidAlgebra.coeff f s)
  rwa [hf (mem_support_iff.mp hs)] at h

private theorem weightedHomogeneousComponent_self_of_isWH {w : σ → M} {p : MvPolynomial σ R} {m : M}
    (hp : IsWeightedHomogeneous w p m) : weightedHomogeneousComponent w m p = p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h
  · rfl
  · by_contra hd
    exact h (hp (Ne.symm hd))

private theorem weightedHomogeneousComponent_eq_zero_of_isWH_ne {w : σ → M} {p : MvPolynomial σ R} {m μ : M}
    (hne : m ≠ μ) (hp : IsWeightedHomogeneous w p m) : weightedHomogeneousComponent w μ p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with h
  · by_contra hd
    exact hne ((hp hd).symm.trans h)
  · rfl

theorem algHom_weightedHomogeneousComponent (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (w : σ → M) (w' : τ → M) (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (μ : M)
    (f : MvPolynomial σ R) :
    φ (weightedHomogeneousComponent w μ f) = weightedHomogeneousComponent w' μ (φ f) := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs := isWH_algHom_monomial φ w w' hφ s (AddMonoidAlgebra.coeff f s)
  have hm : IsWeightedHomogeneous w (monomial s (AddMonoidAlgebra.coeff f s)) (Finsupp.weight w s) :=
    isWeightedHomogeneous_monomial w s (AddMonoidAlgebra.coeff f s) rfl
  by_cases h : Finsupp.weight w s = μ
  · subst h
    rw [weightedHomogeneousComponent_self_of_isWH hm, weightedHomogeneousComponent_self_of_isWH hs]
  · rw [weightedHomogeneousComponent_eq_zero_of_isWH_ne h hm, weightedHomogeneousComponent_eq_zero_of_isWH_ne h hs,
      map_zero]

end General

theorem rowst_mem_dualWeyl_iff {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule, AlgHom.toLinearMap_apply]

def rowActO (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun o => Option.elim o (X none) (fun v => ∑ b : Fin r, C (g v.1 b) * X (some (b, v.2)))

theorem colAddGen_rowAct {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l j (rowAct R g f) = rowActO R g (colAddGen R l j f) := by
  have key : (colAddGen R l j).comp (rowAct R g) =
      (rowActO R g).comp (colAddGen R (r := r) l j) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, colAddGen, rowAct, rowActO, aeval_X, map_sum,
      map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    by_cases h : t = j
    · simp only [h, if_true, aeval_X, map_add (f := _), map_mul, Option.elim]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    · simp [h]
  exact DFunLike.congr_fun key f

theorem rename_rowAct {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rename (some : Fin r × Fin n → Option (Fin r × Fin n)) (rowAct R g f) =
      rowActO R g (rename some f) := by
  have key : (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).comp (rowAct R g) =
      (rowActO R g).comp (rename some) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp [rowAct, rowActO, MvPolynomial.algebraMap_eq]
  exact DFunLike.congr_fun key f

theorem rowAct_X_isWH {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (v : Fin r × Fin n) : IsWeightedHomogeneous (colW r n) (rowAct R g (X v)) (colW r n v) := by
  simp only [rowAct, aeval_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
  convert (isWeightedHomogeneous_C (colW r n) (g v.1 b)).mul
    (isWeightedHomogeneous_X (R := R) (colW r n) (b, v.2)) using 1
  simp [colW]

end Formalism.GradedWeylDivisibility
end
end

section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance
section -- merged from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetdomLemmas
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem support_prod_le_of_additive {σ ι R : Type*} [CommSemiring R] [DecidableEq ι] [DecidableEq σ]
    (F : (σ →₀ ℕ) → ℕ) (hF0 : F 0 = 0) (hFa : ∀ a b, F (a + b) = F a + F b)
    (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ι → ℕ)
    (hb : ∀ i ∈ s, ∀ m ∈ (f i).support, F m ≤ b i) :
    ∀ m ∈ (∏ i ∈ s, f i).support, F m ≤ ∑ i ∈ s, b i := by
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.prod_empty, mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp [hF0]
    · exact absurd rfl hm
  | insert i s hi ih =>
    intro m hm
    rw [Finset.prod_insert hi] at hm
    obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    rw [hFa, Finset.sum_insert hi]
    exact Nat.add_le_add (hb i (mem_insert_self _ _) a ha)
      (ih (fun j hj => hb j (mem_insert_of_mem hj)) c hc)

theorem support_prod_eq_of_additive {σ ι R : Type*} [CommSemiring R] [DecidableEq ι] [DecidableEq σ]
    (F : (σ →₀ ℕ) → ℕ) (hF0 : F 0 = 0) (hFa : ∀ a b, F (a + b) = F a + F b)
    (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ι → ℕ)
    (hb : ∀ i ∈ s, ∀ m ∈ (f i).support, F m = b i) :
    ∀ m ∈ (∏ i ∈ s, f i).support, F m = ∑ i ∈ s, b i := by
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.prod_empty, mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp [hF0]
    · exact absurd rfl hm
  | insert i s hi ih =>
    intro m hm
    rw [Finset.prod_insert hi] at hm
    obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    rw [hFa, Finset.sum_insert hi, hb i (mem_insert_self _ _) a ha,
      ih (fun j hj => hb j (mem_insert_of_mem hj)) c hc]

theorem rowDeg_add {r n : ℕ} (m m' : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    rowDeg (m + m') a = rowDeg m a + rowDeg m' a := by
  simp [rowDeg, Finset.sum_add_distrib]

theorem rowDeg_zero {r n : ℕ} (a : Fin r) : rowDeg (0 : Fin r × Fin n →₀ ℕ) a = 0 := by
  simp [rowDeg]

theorem rowDeg_single {r n : ℕ} (b a : Fin r) (s : Fin n) :
    rowDeg (Finsupp.single (b, s) 1) a = if b = a then 1 else 0 := by
  classical
  unfold rowDeg
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases h : b = a
  · subst h; simp
  · simp [h]

def rowPart {r n : ℕ} (k : ℕ) (m : Fin r × Fin n →₀ ℕ) : ℕ :=
  ∑ a : Fin r with a.val < k, rowDeg m a

theorem rowPart_zero {r n : ℕ} (k : ℕ) : rowPart k (0 : Fin r × Fin n →₀ ℕ) = 0 := by
  simp [rowPart, rowDeg_zero]

theorem rowPart_add {r n : ℕ} (k : ℕ) (m m' : Fin r × Fin n →₀ ℕ) :
    rowPart k (m + m') = rowPart k m + rowPart k m' := by
  simp [rowPart, rowDeg_add, Finset.sum_add_distrib]

theorem rowPart_single {r n : ℕ} (k : ℕ) (b : Fin r) (s : Fin n) :
    rowPart k (Finsupp.single (b, s) 1 : Fin r × Fin n →₀ ℕ) = if b.val < k then 1 else 0 := by
  classical
  unfold rowPart
  simp only [rowDeg_single]
  rw [Finset.sum_ite_eq]
  simp

def rowTot {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) : ℕ := ∑ a : Fin r, rowDeg m a

theorem rowTot_zero {r n : ℕ} : rowTot (0 : Fin r × Fin n →₀ ℕ) = 0 := by
  simp [rowTot, rowDeg_zero]

theorem rowTot_add {r n : ℕ} (m m' : Fin r × Fin n →₀ ℕ) :
    rowTot (m + m') = rowTot m + rowTot m' := by
  simp [rowTot, rowDeg_add, Finset.sum_add_distrib]

theorem rowTot_single {r n : ℕ} (b : Fin r) (s : Fin n) :
    rowTot (Finsupp.single (b, s) 1 : Fin r × Fin n →₀ ℕ) = 1 := by
  classical
  unfold rowTot
  simp only [rowDeg_single]
  simp

theorem support_X_subset' {σ R : Type*} [CommSemiring R] (v : σ) :
    (X v : MvPolynomial σ R).support ⊆ {Finsupp.single v 1} :=
  support_monomial_subset

theorem initMinor_term_support {R : Type*} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (σ : Equiv.Perm (Fin s)) (m : Fin r × Fin n →₀ ℕ)
    (hm : m ∈ (∏ i : Fin s, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)).support) :
    (∀ k, rowPart k m = #{p : Fin s | (I p).val < k}) ∧ rowTot m = s := by
  classical
  constructor
  · intro k
    have h := support_prod_eq_of_additive (rowPart k) (rowPart_zero k) (rowPart_add k) Finset.univ
      (fun i : Fin s => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (fun i => if (I (σ i)).val < k then 1 else 0)
      (by
        intro i _ m' hm'
        have := support_X_subset' (R := R) _ hm'
        rw [Finset.mem_singleton] at this
        subst this
        exact rowPart_single k _ _) m hm
    rw [h, Equiv.sum_comp σ (fun p => if (I p).val < k then 1 else 0), Finset.sum_boole]
    simp
  · have h := support_prod_eq_of_additive rowTot rowTot_zero rowTot_add Finset.univ
      (fun i : Fin s => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (fun _ => 1)
      (by
        intro i _ m' hm'
        have := support_X_subset' (R := R) _ hm'
        rw [Finset.mem_singleton] at this
        subst this
        exact rowTot_single _ _) m hm
    rw [h]; simp

theorem initMinor_support {R : Type*} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ (initMinor R I hs).support) :
    (∀ k, rowPart k m ≤ min k s) ∧ rowTot m = s := by
  classical
  by_cases hI : Function.Injective I
  · unfold initMinor at hm
    rw [Matrix.det_apply] at hm
    have h1 := support_sum hm
    rw [Finset.mem_biUnion] at h1
    obtain ⟨σ, -, hσ⟩ := h1
    rw [Units.smul_def] at hσ
    have hσ' := support_smul hσ
    simp only [Matrix.of_apply] at hσ'
    obtain ⟨hp, ht⟩ := initMinor_term_support I hs σ m hσ'
    refine ⟨fun k => ?_, ht⟩
    rw [hp k]
    refine le_min ?_ ?_
    · calc #{p : Fin s | (I p).val < k} ≤ #{a : Fin r | a.val < k} := by
            apply Finset.card_le_card_of_injOn I
            · intro p hp'
              simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp' ⊢
              exact hp'
            · intro p _ q _ h; exact hI h
        _ = min r k := Fin.card_filter_val_lt
        _ ≤ k := min_le_right _ _
    · calc #{p : Fin s | (I p).val < k} ≤ #(Finset.univ : Finset (Fin s)) := Finset.card_filter_le _ _
        _ = s := by simp
  · exfalso
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨p, q, hpq, hne⟩ := hI
    have h0 : initMinor R I hs = 0 := by
      unfold initMinor
      apply Matrix.det_zero_of_row_eq hne
      funext j
      simp [hpq]
    rw [h0, support_zero] at hm
    exact Finset.notMem_empty _ hm

theorem sum_min_eq_shapeDeg {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : ℕ) :
    ∑ k' : Fin K, min k (sz k') = ∑ t : Fin n with t.val < k, shapeDeg sz t := by
  classical
  unfold shapeDeg
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k' _
  rw [Finset.sum_boole, Finset.filter_filter]
  have e : #{t : Fin n | t.val < k ∧ t.val < sz k'} = #{t : Fin n | t.val < min k (sz k')} := by
    congr 1; ext t; simp [lt_min_iff]
  rw [Nat.cast_id, e, Fin.card_filter_val_lt]
  have := hsz k'
  omega

end Formalism.GradedWeylDivisibility
end
end

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem bideterminantDominance : BideterminantDominance := by
  classical
  intro R _ r n K sz hsz I m hm
  have hm' : m ∈ (∏ k : Fin K, initMinor R (I k) (hsz k)).support := hm
  refine ⟨fun k => ?_, ?_⟩
  · have h := support_prod_le_of_additive (rowPart k) (rowPart_zero k)
      (rowPart_add k) Finset.univ (fun k' => initMinor R (I k') (hsz k'))
      (fun k' => min k (sz k'))
      (fun k' _ m' hm'' => (initMinor_support (I k') (hsz k') m' hm'').1 k)
      m hm'
    exact h.trans_eq (sum_min_eq_shapeDeg sz hsz k)
  · have h := support_prod_eq_of_additive rowTot rowTot_zero
      rowTot_add Finset.univ (fun k' => initMinor R (I k') (hsz k')) sz
      (fun k' _ m' hm'' => (initMinor_support (I k') (hsz k') m' hm'').2)
      m hm'
    have h2 := sum_min_eq_shapeDeg sz hsz n
    have h3 : ∑ t : Fin n with t.val < n, shapeDeg sz t =
        ∑ t : Fin n, shapeDeg sz t :=
      Finset.sum_congr (Finset.filter_true_of_mem fun t _ => t.isLt) fun _ _ => rfl
    have h4 : ∑ k' : Fin K, min n (sz k') = ∑ k' : Fin K, sz k' :=
      Finset.sum_congr rfl fun k' _ => min_eq_right (hsz k')
    exact h.trans (h4.symm.trans (h2.trans h3))

end Formalism.GradedWeylDivisibility
end
end
