module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
namespace GlobalTheory

open Finsupp

section Words

variable {R : Type*} [CommRing R] {Λ : Type*} {B : Type*} [Ring B] [Algebra R B]

def opWord (D : Λ → B) (w : List Λ) : B := (w.map D).prod

@[simp] theorem opWord_nil (D : Λ → B) : opWord D [] = 1 := rfl

@[simp] theorem opWord_cons (D : Λ → B) (l : Λ) (w : List Λ) :
    opWord D (l :: w) = D l * opWord D w := by simp [opWord]

theorem opWord_append (D : Λ → B) (w w' : List Λ) :
    opWord D (w ++ w') = opWord D w * opWord D w' := by simp [opWord]

theorem opWord_perm {D : Λ → B} (hD : ∀ l l', Commute (D l) (D l')) {w w' : List Λ}
    (h : w.Perm w') : opWord D w = opWord D w' := by
  induction h with
  | nil => rfl
  | cons l _ ih => simp [ih]
  | swap l l' w => simp only [opWord_cons, ← mul_assoc, (hD l l').eq]
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

def IsOrderingRule (ord : (Λ →₀ ℕ) → List Λ) : Prop :=
  ∀ α, (ord α : Multiset Λ) = Finsupp.toMultiset α

theorem isOrderingRule_toList :
    IsOrderingRule (fun α : Λ →₀ ℕ => (Finsupp.toMultiset α).toList) :=
  fun _ => Multiset.coe_toList _

noncomputable def opPoly (D : Λ → B) (ord : (Λ →₀ ℕ) → List Λ) : MvPolynomial Λ R →ₗ[R] B :=
  (MvPolynomial.basisMonomials Λ R).constr R (fun α => opWord D (ord α))

theorem opPoly_monomial (D : Λ → B) (ord : (Λ →₀ ℕ) → List Λ) (α : Λ →₀ ℕ) (c : R) :
    opPoly D ord (MvPolynomial.monomial α c) = c • opWord D (ord α) := by
  have h : MvPolynomial.monomial α c = c • MvPolynomial.basisMonomials Λ R α := by
    simp [MvPolynomial.smul_monomial]
  rw [h, map_smul, opPoly, Module.Basis.constr_basis]

theorem opPoly_mul_of_commute {D : Λ → B} (hD : ∀ l l', Commute (D l) (D l'))
    {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (P Q : MvPolynomial Λ R) :
    opPoly D ord (P * Q) = opPoly D ord P * opPoly D ord Q := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add (f := _), hp, hq]
  | monomial α a =>
    induction Q using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add (f := _), hp, hq]
    | monomial β b =>
      have hp : (ord (α + β)).Perm (ord α ++ ord β) := by
        rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, h, h, h, map_add (f := _)]
      rw [MvPolynomial.monomial_mul, opPoly_monomial, opPoly_monomial, opPoly_monomial,
        opWord_perm hD hp, opWord_append, smul_mul_smul_comm]

theorem IsOrderingRule.ord_zero {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) :
    ord 0 = [] := by
  have := h 0
  simpa using this

theorem IsOrderingRule.ord_single {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (l : Λ) :
    ord (single l 1) = [l] := by
  have := h (single l 1)
  rw [Finsupp.toMultiset_single, one_smul] at this
  exact List.perm_singleton.mp (Multiset.coe_eq_coe.mp this)

theorem opPoly_C (D : Λ → B) {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (c : R) :
    opPoly D ord (MvPolynomial.C c) = algebraMap R B c := by
  rw [MvPolynomial.C_apply, opPoly_monomial, h.ord_zero, opWord_nil, Algebra.algebraMap_eq_smul_one]

theorem opPoly_X (D : Λ → B) {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (l : Λ) :
    opPoly D ord (MvPolynomial.X l : MvPolynomial Λ R) = D l := by
  rw [MvPolynomial.X, opPoly_monomial, h.ord_single]
  simp

noncomputable def commEval (D : Λ → B) (hD : ∀ l l', Commute (D l) (D l')) :
    MvPolynomial Λ R →ₐ[R] B :=
  AlgHom.ofLinearMap (opPoly D fun α => (Finsupp.toMultiset α).toList)
    (by rw [← MvPolynomial.C_1, opPoly_C D isOrderingRule_toList, map_one])
    (opPoly_mul_of_commute hD isOrderingRule_toList)

@[simp] theorem commEval_X (D : Λ → B) (hD : ∀ l l', Commute (D l) (D l')) (l : Λ) :
    commEval D hD (MvPolynomial.X l : MvPolynomial Λ R) = D l :=
  opPoly_X D isOrderingRule_toList l

end Words

section General

variable {R A M Λ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]

end General

section Constant

open MvPolynomial

variable {R σ Λ : Type*} [CommRing R]

def multiFactorial (α : σ →₀ ℕ) : ℕ := α.prod fun _ n => n.factorial

end Constant

section Series

open MvPowerSeries

variable {R σ Λ M : Type*} [CommRing R]

noncomputable abbrev germIdeal (σ R : Type*) [CommRing R] : Ideal (MvPowerSeries σ R) :=
  RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R)

theorem X_mem_germIdeal (i : σ) : (X i : MvPowerSeries σ R) ∈ germIdeal σ R := by
  simp [RingHom.mem_ker]

theorem exists_eq_sum_X_mul [Fintype σ] {n : ℕ} {g : MvPowerSeries σ R}
    (hg : ∀ d : σ →₀ ℕ, degree d < n + 1 → coeff d g = 0) :
    ∃ h : σ → MvPowerSeries σ R, (∀ i (d : σ →₀ ℕ), degree d < n → coeff d (h i) = 0) ∧
      g = ∑ i, X i * h i := by
  classical
  have hidx : ∀ d : σ →₀ ℕ, d ≠ 0 → ∃ i, d i ≠ 0 := fun d hd => by
    by_contra hc
    push Not at hc
    exact hd (Finsupp.ext hc)
  choose idx hidx using hidx
  let part : σ → MvPowerSeries σ R := fun i d =>
    if hd : d ≠ 0 then (if idx d hd = i then coeff d g else 0) else 0
  have hpart : ∀ i d, coeff d (part i) =
      if hd : d ≠ 0 then (if idx d hd = i then coeff d g else 0) else 0 := fun _ _ => rfl
  have hdvd : ∀ i, (X i : MvPowerSeries σ R) ∣ part i := fun i => by
    rw [X_dvd_iff]
    intro d hd
    rw [hpart]
    split_ifs with h₁ h₂
    · exact absurd hd (h₂ ▸ hidx d h₁)
    · rfl
    · rfl
  choose h hh using hdvd
  refine ⟨h, fun i d hd => ?_, ?_⟩
  · have h₁ : coeff (single i 1 + d) (part i) = coeff d (h i) := by
      rw [hh, X_def, coeff_add_monomial_mul, one_mul]
    rw [← h₁, hpart]
    have h₂ : coeff (single i 1 + d) g = 0 := hg _ (by simp; omega)
    simp [h₂]
  · ext d
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← hh, map_sum, hpart]
    by_cases hd : d = 0
    · subst hd
      simpa using hg 0 (by simp)
    · simp [hd]

theorem germIdeal_eq_span [Finite σ] :
    germIdeal σ R = Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  cases nonempty_fintype σ
  refine le_antisymm (fun g hg => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨h, -, rfl⟩ := exists_eq_sum_X_mul (n := 0) (g := g) fun d hd => by
      obtain rfl : d = 0 := by simpa [degree_eq_zero_iff] using hd
      simpa using hg
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact X_mem_germIdeal i

theorem mem_germIdeal_pow_iff [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ ∀ d : σ →₀ ℕ, degree d < n → coeff d g = 0 := by
  cases nonempty_fintype σ
  constructor
  · intro hg
    suffices h : (n : ℕ∞) ≤ g.order from fun d hd =>
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      rw [pow_succ] at hg
      refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · refine le_trans ?_ le_order_mul
        push_cast
        refine add_le_add (ih ha) ?_
        exact_mod_cast nat_le_order (n := 1) fun d hd => by
          obtain rfl : d = 0 := by simpa [degree_eq_zero_iff] using hd
          simpa using hb
      · exact (le_min ha hb).trans min_order_le_add
  · induction n generalizing g with
    | zero => simp
    | succ n ih =>
      intro hg
      obtain ⟨h, hh, rfl⟩ := exists_eq_sum_X_mul hg
      rw [pow_succ']
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (X_mem_germIdeal i) (ih (hh i))

theorem mem_germIdeal_pow_iff_le_order [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ (n : ℕ∞) ≤ g.order := by
  rw [mem_germIdeal_pow_iff]
  exact ⟨nat_le_order, fun h d hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)⟩

variable [Finite σ]

end Series

section Symbol

open MvPowerSeries

variable {R σ Λ M : Type*} [CommRing R] [Finite σ] [AddCommGroup M] [Module R M]
  [Module (MvPowerSeries σ R) M]

variable [IsScalarTower R (MvPowerSeries σ R) M]

end Symbol

section Example

open MvPowerSeries

end Example

section Legendre

variable {l : ℕ} [hl : Fact l.Prime]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

end Legendre

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
open TensorProduct

namespace GlobalTheory

section General

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable {V V' : Type*} [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']

theorem baseChange_map (f : V →ₗ[R] V') (A : Submodule R V) :
    (A.map f).baseChange S = (A.baseChange S).map (f.baseChange S) := by
  simp only [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image]
  rfl

theorem baseChange_range (f : V →ₗ[R] V') :
    (LinearMap.range f).baseChange S = LinearMap.range (f.baseChange S) := by
  rw [← Submodule.map_top, baseChange_map, Submodule.baseChange_top, Submodule.map_top]

theorem ker_baseChange_mkQ (B : Submodule R V) :
    LinearMap.ker (B.mkQ.baseChange S) = B.baseChange S := by
  rw [Submodule.baseChange, ← LinearMap.exact_iff]
  exact lTensor_exact S (LinearMap.exact_subtype_mkQ B) B.mkQ_surjective

noncomputable def baseChangeQuotEquiv (B : Submodule R V) :
    S ⊗[R] (V ⧸ B) ≃ₗ[S] (S ⊗[R] V) ⧸ B.baseChange S :=
  TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S B

variable [Module.Flat R S]

theorem baseChange_ker (f : V →ₗ[R] V') :
    (LinearMap.ker f).baseChange S = LinearMap.ker (f.baseChange S) := by
  rw [Submodule.baseChange, eq_comm, ← LinearMap.exact_iff]
  exact Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map f)

theorem baseChange_comap (f : V →ₗ[R] V') (B : Submodule R V') :
    (B.comap f).baseChange S = (B.baseChange S).comap (f.baseChange S) := by
  rw [← ker_baseChange_mkQ S B, ← LinearMap.ker_comp, ← LinearMap.baseChange_comp,
    ← baseChange_ker, LinearMap.ker_comp, Submodule.ker_mkQ]

theorem baseChange_inf (A B : Submodule R V) :
    (A ⊓ B).baseChange S = A.baseChange S ⊓ B.baseChange S := by
  rw [← Submodule.map_comap_subtype, baseChange_map, baseChange_comap, Submodule.map_comap_eq]
  rfl

theorem baseChange_iInf {ι : Type*} [Finite ι] (A : ι → Submodule R V) :
    (⨅ i, A i).baseChange S = ⨅ i, (A i).baseChange S := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih => rw [← e.iInf_comp, ← e.iInf_comp, ih]
  | h_empty => rw [iInf_of_empty, iInf_of_empty, Submodule.baseChange_top]
  | h_option ih => rw [iInf_option, iInf_option, baseChange_inf, ih]

theorem baseChange_injective {f : V →ₗ[R] V'} (hf : Function.Injective f) :
    Function.Injective (f.baseChange S) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := S) f hf

noncomputable def baseChangeEquiv (A : Submodule R V) : S ⊗[R] A ≃ₗ[S] A.baseChange S :=
  LinearEquiv.ofInjective (A.subtype.baseChange S) (baseChange_injective S A.injective_subtype)

theorem map_baseChangeEquiv_submoduleOf (A B : Submodule R V) :
    ((B.submoduleOf A).baseChange S).map (baseChangeEquiv S A : S ⊗[R] A →ₗ[S] A.baseChange S) =
      (B.baseChange S).submoduleOf (A.baseChange S) := by
  rw [Submodule.submoduleOf, baseChange_comap, Submodule.map_equiv_eq_comap_symm,
    ← Submodule.comap_comp, Submodule.submoduleOf]
  congr 1
  ext1 x
  obtain ⟨y, rfl⟩ := (baseChangeEquiv S A).surjective x
  change (A.subtype.baseChange S) ((baseChangeEquiv S A).symm ((baseChangeEquiv S A) y)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

noncomputable def baseChangeSubquotEquiv (A B : Submodule R V) :
    S ⊗[R] (A ⧸ B.submoduleOf A) ≃ₗ[S]
      A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S) :=
  baseChangeQuotEquiv S (B.submoduleOf A) ≪≫ₗ
    Submodule.Quotient.equiv _ _ (baseChangeEquiv S A) (map_baseChangeEquiv_submoduleOf S A B)

theorem lift_rank_baseChange.{u, v, w} {R : Type u} (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] [NoZeroDivisors S] [FaithfulSMul R S]
    {V : Type w} [AddCommGroup V] [Module R V] (A : Submodule R V) :
    Cardinal.lift.{w} (Module.rank S (A.baseChange S)) = Cardinal.lift.{max v w} (Module.rank R A) := by
  rw [← (baseChangeEquiv S A).rank_eq]
  exact (TensorProduct.isBaseChange R A S).lift_rank_eq

theorem finrank_baseChange [NoZeroDivisors S] [FaithfulSMul R S] (A : Submodule R V) :
    Module.finrank S (A.baseChange S) = Module.finrank R A := by
  simpa using! congr_arg Cardinal.toNat (lift_rank_baseChange S A)

end General

section Lattice

variable {R : Type*} (K S L : Type*) [CommRing R] [Field K] [CommRing S] [CommRing L]
  [Algebra R K] [Algebra K L] [Algebra S L]
variable {V V' : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']

def spanBaseChange (M : Submodule R V) : Submodule S (L ⊗[K] V) :=
  Submodule.span S ((fun m => (1 : L) ⊗ₜ[K] m) '' (M : Set V))

variable [Algebra R S] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]


variable (R V) in
noncomputable def baseChangeToField : S ⊗[R] V →ₗ[S] L ⊗[K] V :=
  LinearMap.liftBaseChange S ((TensorProduct.mk K L V 1).restrictScalars R)

@[simp]
theorem baseChangeToField_tmul (s : S) (v : V) :
    baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V) (s ⊗ₜ v) = algebraMap S L s ⊗ₜ[K] v := by
  simp [baseChangeToField, smul_tmul', Algebra.smul_def]

theorem baseChangeToField_naturality (f : V →ₗ[K] V') (x : S ⊗[R] V) :
    f.baseChange L (baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V) x) =
      baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V') ((f.restrictScalars R).baseChange S x) := by
  induction x with
  | add x y hx hy => simp [hx, hy]
  | tmul s v => simp

theorem spanBaseChange_eq_map (M : Submodule R V) :
    spanBaseChange K S L M = (M.baseChange S).map (baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V)) := by
  simp only [spanBaseChange, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image, TensorProduct.mk_apply, baseChangeToField_tmul, map_one]

variable [IsFractionRing R K] [FaithfulSMul S L]


variable (R V) in
theorem baseChangeToField_injective : Function.Injective (baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V)) := by
  have hflat : Module.Flat R V :=
    (Module.flat_iff_of_isLocalization K (nonZeroDivisors R) V).1 inferInstance
  have h1 : Function.Injective ((IsScalarTower.toAlgHom R S L).toLinearMap.rTensor V) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective S L)
  have h2 : ∀ x, IsLocalization.moduleTensorEquiv (nonZeroDivisors R) K L V
      (baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V) x) = (IsScalarTower.toAlgHom R S L).toLinearMap.rTensor V x := by
    intro x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul s v => rw [baseChangeToField_tmul]; rfl
  intro x y hxy
  apply h1
  rw [← h2, ← h2, hxy]

theorem comap_baseChangeToField (W : Submodule K V) :
    ((W.baseChange L).restrictScalars S).comap (baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V)) =
      (W.restrictScalars R).baseChange S := by
  ext x
  have hker : (W.restrictScalars R).baseChange S =
      LinearMap.ker ((W.mkQ.restrictScalars R).baseChange S) :=
    (ker_baseChange_mkQ S (W.restrictScalars R)).symm
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem, ← ker_baseChange_mkQ L W, hker,
    LinearMap.mem_ker, LinearMap.mem_ker, baseChangeToField_naturality,
    map_eq_zero_iff _ (baseChangeToField_injective (R := R) (K := K) (S := S) (L := L) (V := V ⧸ W))]

variable [Module.Flat R S]

theorem spanBaseChange_inf_subspace (M : Submodule R V) (W : Submodule K V) :
    spanBaseChange K S L (M ⊓ W.restrictScalars R) =
      spanBaseChange K S L M ⊓ (W.baseChange L).restrictScalars S := by
  rw [spanBaseChange_eq_map, spanBaseChange_eq_map, baseChange_inf, ← comap_baseChangeToField K S L,
    Submodule.map_inf_eq_map_inf_comap]

noncomputable def spanBaseChangeEquiv (M : Submodule R V) :
    S ⊗[R] M ≃ₗ[S] spanBaseChange K S L M :=
  baseChangeEquiv S M ≪≫ₗ
    Submodule.equivMapOfInjective _ (baseChangeToField_injective (R := R) (K := K) (S := S) (L := L) (V := V)) _ ≪≫ₗ
    LinearEquiv.ofEq _ _ (spanBaseChange_eq_map K S L M).symm

@[simp]
theorem coe_spanBaseChangeEquiv_apply (M : Submodule R V) (x : S ⊗[R] M) :
    (spanBaseChangeEquiv K S L M x : L ⊗[K] V) =
      baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V) (M.subtype.baseChange S x) := rfl

theorem map_spanBaseChangeEquiv_submoduleOf (M N : Submodule R V) :
    ((N.submoduleOf M).baseChange S).map
        (spanBaseChangeEquiv K S L M : S ⊗[R] M →ₗ[S] spanBaseChange K S L M) =
      (spanBaseChange K S L N).submoduleOf (spanBaseChange K S L M) := by
  rw [Submodule.submoduleOf, baseChange_comap, Submodule.map_equiv_eq_comap_symm]
  ext x
  obtain ⟨y, rfl⟩ := (spanBaseChangeEquiv K S L M).surjective x
  rw [Submodule.submoduleOf, spanBaseChange_eq_map K S L N]
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Submodule.subtype_apply, coe_spanBaseChangeEquiv_apply]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨z, hz, h⟩ => baseChangeToField_injective (R := R) (K := K) (S := S) (L := L) (V := V) h ▸ hz⟩

noncomputable def spanBaseChangeSubquotEquiv (M N : Submodule R V) :
    S ⊗[R] (M ⧸ N.submoduleOf M) ≃ₗ[S]
      spanBaseChange K S L M ⧸ (spanBaseChange K S L N).submoduleOf (spanBaseChange K S L M) :=
  baseChangeQuotEquiv S (N.submoduleOf M) ≪≫ₗ
    Submodule.Quotient.equiv _ _ (spanBaseChangeEquiv K S L M)
      (map_spanBaseChangeEquiv_submoduleOf K S L M N)

theorem finrank_spanBaseChange [NoZeroDivisors S] [FaithfulSMul R S] (M : Submodule R V) :
    Module.finrank S (spanBaseChange K S L M) = Module.finrank R M := by
  rw [← (spanBaseChangeEquiv K S L M).finrank_eq]
  exact (TensorProduct.isBaseChange R M S).finrank_eq

end Lattice

theorem lift_rank_spanBaseChange.{u, v} {R : Type*} (K S : Type*) (L : Type u) [CommRing R]
    [Field K] [CommRing S] [CommRing L] [Algebra R K] [Algebra K L] [Algebra S L]
    {V : Type v} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [Algebra R S] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [IsFractionRing R K] [FaithfulSMul S L] [Module.Flat R S] [NoZeroDivisors S]
    [FaithfulSMul R S] (M : Submodule R V) :
    Cardinal.lift.{v} (Module.rank S (spanBaseChange K S L M)) =
      Cardinal.lift.{max u v} (Module.rank R M) :=
  (IsBaseChange.of_equiv (f := ((spanBaseChangeEquiv K S L M).toLinearMap.restrictScalars R) ∘ₗ
    TensorProduct.mk R S M 1) (spanBaseChangeEquiv K S L M) (fun _ => rfl)).lift_rank_eq

theorem flat_spanBaseChange_inf_subspace.{u, v} {R : Type*} (K S : Type*) (L : Type u)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Field K] [Field L]
    [Algebra R S] [FaithfulSMul R S] [Module.Flat R S]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    {V : Type v} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (M : Submodule R V) (W : Submodule K V) :
    spanBaseChange K S L (M ⊓ W.restrictScalars R) =
        spanBaseChange K S L M ⊓ (W.baseChange L).restrictScalars S ∧
      Cardinal.lift.{v} (Module.rank S (spanBaseChange K S L M)) =
        Cardinal.lift.{max u v} (Module.rank R M) ∧
      Cardinal.lift.{v} (Module.rank L (W.baseChange L)) =
        Cardinal.lift.{max u v} (Module.rank K W) ∧
      Module.finrank S (spanBaseChange K S L M) = Module.finrank R M ∧
      Module.finrank L (W.baseChange L) = Module.finrank K W :=
  ⟨spanBaseChange_inf_subspace K S L M W, lift_rank_spanBaseChange K S L M,
    lift_rank_baseChange L W, finrank_spanBaseChange K S L M, finrank_baseChange L W⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
namespace GlobalTheory.ClosedBallValuationSubring

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

def closedBallSubring : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg b) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

def closedBallValuationSubring : ValuationSubring K where
  toSubring := closedBallSubring K
  mem_or_inv_mem' := by
    intro x
    change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · right
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h

def openBallIdeal : Ideal (closedBallSubring K) where
  carrier := {x | ‖(x : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max (a : K) (b : K)).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hc : ‖(c : K)‖ ≤ 1 := c.2
    change ‖(c : K) * (x : K)‖ < 1
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc (norm_nonneg _) hx

variable {K}

theorem mem_closedBallSubring {x : K} : x ∈ closedBallSubring K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem mem_openBallIdeal {x : closedBallSubring K} :
    x ∈ openBallIdeal K ↔ ‖(x : K)‖ < 1 := Iff.rfl

theorem isUnit_iff_norm_eq_one {x : closedBallSubring K} : IsUnit x ↔ ‖(x : K)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hu : ‖((u : closedBallSubring K) : K)‖ ≤ 1 := (u : closedBallSubring K).2
    have hv : ‖((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).1‖ ≤ 1 :=
      ((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).2
    have hprod : ‖((u : closedBallSubring K) : K)‖ *
        ‖((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).1‖ = 1 := by
      rw [← norm_mul]
      have h := congrArg Subtype.val u.mul_inv
      simp only [Subring.coe_mul, Subring.coe_one] at h
      rw [h, norm_one]
    refine le_antisymm hu ?_
    calc (1 : ℝ) = _ := hprod.symm
      _ ≤ ‖((u : closedBallSubring K) : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ = _ := mul_one _
  · intro h
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      exact zero_ne_one h
    have hinv : (x : K)⁻¹ ∈ closedBallSubring K := by
      rw [mem_closedBallSubring, norm_inv, h, inv_one]
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : K)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_one]
    exact mul_inv_cancel₀ hx0

theorem mem_openBallIdeal_iff_not_isUnit {x : closedBallSubring K} :
    x ∈ openBallIdeal K ↔ ¬ IsUnit x := by
  rw [mem_openBallIdeal, isUnit_iff_norm_eq_one]
  have hle : ‖(x : K)‖ ≤ 1 := mem_closedBallSubring.mp x.2
  exact ⟨fun h he => (ne_of_lt h) he, fun h => lt_of_le_of_ne hle h⟩

variable (K)

instance isLocalRing_closedBallSubring : IsLocalRing (closedBallSubring K) :=
  inferInstanceAs (IsLocalRing (closedBallValuationSubring K))

theorem openBallIdeal_eq_maximalIdeal :
    openBallIdeal K = IsLocalRing.maximalIdeal (closedBallSubring K) := by
  ext x
  rw [mem_openBallIdeal_iff_not_isUnit, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem openBallIdeal_isMaximal : (openBallIdeal K).IsMaximal := by
  rw [openBallIdeal_eq_maximalIdeal]
  exact IsLocalRing.maximalIdeal.isMaximal _

end GlobalTheory.ClosedBallValuationSubring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthRestrictScalarsEqSumInertiaDegOfSubset
open IsLocalRing

namespace GlobalTheory

section Local

variable (R S X : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]

end Local

section Localized

variable {S : Type*} [CommRing S]

theorem length_eq_length_localizedModule (T : Submonoid S) (A : Type*) [CommRing A] [Algebra S A]
    [IsLocalization T A] {X X' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup X']
    [Module S X'] [Module A X'] [IsScalarTower S A X'] (f : X →ₗ[S] X') [IsLocalizedModule T f] :
    Module.length A X' = Module.length (Localization T) (LocalizedModule T X) := by
  let e : Localization T ≃ₐ[S] A := IsLocalization.algEquiv T _ _
  letI : Algebra (Localization T) A := e.toRingHom.toAlgebra
  letI : Module (Localization T) X' := Module.compHom X' e.toRingHom
  haveI : IsScalarTower (Localization T) A X' := ⟨fun a b x => mul_smul (e a) b x⟩
  haveI : IsScalarTower S (Localization T) X' := ⟨fun a b x => by
    change e (a • b) • x = a • (e b • x)
    rw [map_smul, smul_assoc]⟩
  rw [← Module.length_eq_of_surjective (S := Localization T) (R := A) (M := X') e.surjective]
  exact (((IsLocalizedModule.iso T f).extendScalarsOfIsLocalization T
    (Localization T)).length_eq).symm

theorem length_localizedModule_eq_add_of_exact (T : Submonoid S) {N M P : Type*}
    [AddCommGroup N] [AddCommGroup M] [AddCommGroup P] [Module S N] [Module S M] [Module S P]
    (f : N →ₗ[S] M) (g : M →ₗ[S] P) (hf : Function.Injective f) (hg : Function.Surjective g)
    (H : Function.Exact f g) :
    Module.length (Localization T) (LocalizedModule T M) =
      Module.length (Localization T) (LocalizedModule T N) +
        Module.length (Localization T) (LocalizedModule T P) :=
  Module.length_eq_add_of_exact (LocalizedModule.map T f) (LocalizedModule.map T g)
    (LocalizedModule.map_injective T f hf) (LocalizedModule.map_surjective T g hg)
    (LocalizedModule.map_exact T f g H)

theorem length_localizedModule_congr (T : Submonoid S) {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N] (e : M ≃ₗ[S] N) :
    Module.length (Localization T) (LocalizedModule T M) =
      Module.length (Localization T) (LocalizedModule T N) :=
  (IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T N) (Localization T) e).length_eq

theorem length_localizedModule_quotient_self (m : Ideal S) [hm : m.IsMaximal] :
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl (S ⧸ m)) = 1 := by
  haveI : IsSimpleModule S (S ⧸ m) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨m, hm, ⟨LinearEquiv.refl _ _⟩⟩
  haveI : IsLocalizedModule m.primeCompl (LinearMap.id : S ⧸ m →ₗ[S] S ⧸ m) :=
    { map_units := fun s => by
        rw [Module.End.isUnit_iff]
        refine LinearMap.bijective_of_ne_zero fun h => s.2 ?_
        have := LinearMap.congr_fun h (Ideal.Quotient.mk m 1)
        simp only [Module.algebraMap_end_apply, LinearMap.zero_apply] at this
        rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.mk_eq_zero] at this
        simpa using this
      surj := fun y => ⟨(y, 1), by simp⟩
      exists_of_eq := fun h => ⟨1, by simpa using h⟩ }
  let e := IsLocalizedModule.iso m.primeCompl (LinearMap.id : S ⧸ m →ₗ[S] S ⧸ m)
  haveI : Nontrivial (LocalizedModule m.primeCompl (S ⧸ m)) := e.toEquiv.nontrivial
  apply le_antisymm
  · rw [← Module.length_top]
    refine (Submodule.length_le_length_restrictScalars S _).trans ?_
    rw [Submodule.restrictScalars_top, Module.length_top, e.length_eq, Module.length_eq_one]
  · exact Order.one_le_iff_pos.mpr Module.length_pos

theorem length_localizedModule_quotient_of_ne (m n : Ideal S) [hm : m.IsMaximal] [hn : n.IsPrime]
    (h : n ≠ m) :
    Module.length (Localization.AtPrime n) (LocalizedModule n.primeCompl (S ⧸ m)) = 0 := by
  rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  have : ¬ m ≤ n := fun hle => h (hm.eq_of_le hn.ne_top hle).symm
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp this
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective m x
  refine ⟨s, hs', ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact m.mul_mem_right _ hs

theorem length_localizedModule_atPrime_le (n : Ideal S) [n.IsPrime] {X : Type*} [AddCommGroup X]
    [Module S X] (h : IsFiniteLength S X) :
    Module.length (Localization.AtPrime n) (LocalizedModule n.primeCompl X) ≤
      Module.length S X := by
  induction h with
  | of_subsingleton => simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    rw [length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
      Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), Module.length_eq_one S (M ⧸ N)]
    refine add_le_add ih ?_
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    rw [length_localizedModule_congr _ e]
    by_cases hnm : n = m
    · subst hnm
      exact (length_localizedModule_quotient_self n).le
    · rw [length_localizedModule_quotient_of_ne m n hnm]
      exact zero_le_one

end Localized

section General

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem length_restrictScalars_eq_sum_of_subset {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [iR : Module R X] [iT : IsScalarTower R S X]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0) :
    Module.length R X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * Module.length R (S ⧸ n.asIdeal) := by
  revert iR iT hT
  induction h with
  | of_subsingleton => intros; simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    intro iR iT hT
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have key : ∀ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl M) = Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl N) + Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl (S ⧸ m)) := fun n => by
      rw [length_localizedModule_eq_add_of_exact _ N.subtype N.mkQ
        N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
        length_localizedModule_congr _ e]
    have hmT : (⟨m, hm⟩ : MaximalSpectrum S) ∈ T := by
      by_contra hc
      have h0 := hT _ hc
      rw [key, length_localizedModule_quotient_self m] at h0
      simp at h0
    rw [Module.length_eq_add_of_exact (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R)
      N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
      ih (fun n hn => (add_eq_zero.mp ((key n).symm.trans (hT n hn))).1),
      (e.restrictScalars R).length_eq]
    simp_rw [key, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single_of_mem _ hmT]
    · rw [length_localizedModule_quotient_self m, one_mul]
    · intro n _ hn
      rw [length_localizedModule_quotient_of_ne m n.asIdeal
        (fun hc => hn (MaximalSpectrum.ext hc)), zero_mul]

theorem length_quotient_eq_finrank (p : Ideal R) (n : Ideal S) [p.IsMaximal] [n.LiesOver p]
    [Module.Finite (R ⧸ p) (S ⧸ n)] :
    Module.length R (S ⧸ n) = (Module.finrank (R ⧸ p) (S ⧸ n) : ℕ∞) := by
  letI := Ideal.Quotient.field p
  rw [Module.length_eq_of_surjective (S := R) (R := R ⧸ p) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]

theorem length_quotient_eq_inertiaDeg (p : Ideal R) (n : Ideal S) [p.IsMaximal] [n.IsMaximal]
    [n.LiesOver p] [Module.Finite (R ⧸ p) (S ⧸ n)] :
    Module.length R (S ⧸ n) = (n.inertiaDeg R : ℕ∞) := by
  rw [length_quotient_eq_finrank R p n, Ideal.inertiaDeg_eq_of_isMaximal p n]

theorem length_restrictScalars_eq_sum_inertiaDeg_of_subset [IsLocalRing R] {X : Type*}
    [AddCommGroup X] [Module S X] (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0)
    (hover : ∀ n ∈ T, n.asIdeal.LiesOver (maximalIdeal R))
    (hfin : ∀ n ∈ T, Module.Finite R (S ⧸ n.asIdeal)) :
    Module.length R X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞) := by
  rw [length_restrictScalars_eq_sum_of_subset R h T hT]
  refine Finset.sum_congr rfl fun n hn => ?_
  haveI := hover n hn
  haveI := hfin n hn
  haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ n.asIdeal) :=
    Module.Finite.of_restrictScalars_finite R _ _
  rw [length_quotient_eq_inertiaDeg R (maximalIdeal R) n.asIdeal]

end General

section Semilocal

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]

theorem liesOver_maximalIdeal_of_isIntegral [Algebra.IsIntegral R S] (n : Ideal S)
    [n.IsMaximal] : n.LiesOver (maximalIdeal R) :=
  ⟨(eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) n)).symm⟩

theorem finite_maximalSpectrum_of_finite [Module.Finite R S] : Finite (MaximalSpectrum S) := by
  haveI := (Algebra.QuasiFinite.finite_primesOver (S := S) (maximalIdeal R)).to_subtype
  refine Finite.of_injective (fun n : MaximalSpectrum S =>
    (⟨n.asIdeal, n.isMaximal.isPrime, liesOver_maximalIdeal_of_isIntegral R S n.asIdeal⟩ :
      (maximalIdeal R).primesOver S)) fun a b hab => ?_
  exact MaximalSpectrum.ext (congrArg Subtype.val hab)

theorem length_restrictScalars_eq_sum_inertiaDeg [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X] :
    Module.length R X = ∑ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞) :=
  length_restrictScalars_eq_sum_inertiaDeg_of_subset R h Finset.univ (by simp)
    (fun n _ => liesOver_maximalIdeal_of_isIntegral R S n.asIdeal) (fun _ _ => inferInstance)

theorem length_restrictScalars_eq_sum_inertiaDeg_of_isLocalizedModule [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X]
    (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)] [∀ n, Algebra S (A n)]
    [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
    (Y : MaximalSpectrum S → Type*) [∀ n, AddCommGroup (Y n)] [∀ n, Module S (Y n)]
    [∀ n, Module (A n) (Y n)] [∀ n, IsScalarTower S (A n) (Y n)]
    (f : ∀ n, X →ₗ[S] Y n) [∀ n, IsLocalizedModule n.asIdeal.primeCompl (f n)] :
    Module.length R X =
      ∑ n : MaximalSpectrum S, Module.length (A n) (Y n) * (n.asIdeal.inertiaDeg R : ℕ∞) := by
  rw [length_restrictScalars_eq_sum_inertiaDeg R S h]
  exact Finset.sum_congr rfl fun n _ => by
    rw [length_eq_length_localizedModule n.asIdeal.primeCompl (A n) (f n)]

end Semilocal

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MonomialCountAndBinomialEstimates
namespace GlobalTheory

open Finset

theorem setOf_degree_eq_coe_finsuppAntidiag (σ : Type*) [Fintype σ] [DecidableEq σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a} = ↑(finsuppAntidiag (univ : Finset σ) a) := by
  ext α
  simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]

theorem ncard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a}.ncard = (a + Fintype.card σ - 1).choose a := by
  classical
  rw [setOf_degree_eq_coe_finsuppAntidiag, Set.ncard_coe_finset,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Nat.add_comm]

theorem natCard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    Nat.card {α : σ →₀ ℕ // α.degree = a} = (a + Fintype.card σ - 1).choose a := by
  have h := ncard_degree_eq σ a
  rw [← Nat.card_coe_set_eq] at h
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ISmulOneMemUnitaryLie
open Matrix

namespace GlobalTheory.UnitaryLieAlgebra

variable {n : Type*} [Fintype n]

def unitaryLie (J : Matrix n n ℂ) : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' := by
    intro r X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX,
      smul_zero]

end GlobalTheory.UnitaryLieAlgebra
end
