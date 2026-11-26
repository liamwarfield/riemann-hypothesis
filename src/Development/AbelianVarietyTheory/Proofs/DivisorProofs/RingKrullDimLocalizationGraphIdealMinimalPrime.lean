module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphIdealLocalizationMaximalIdealEqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoePolyMapX
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def rightInc (A : Subalgebra ℂ K) : κ' →+* tens (κ' := κ') A :=
  (Algebra.TensorProduct.includeRight : κ' →ₐ[ℂ] K ⊗[ℂ] κ').toRingHom.codRestrict
    (tens (κ' := κ') A).toSubring fun b => tmul_mem (one_mem A) b

def polyMap (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) :
    MvPolynomial (Fin m) κ' →+* tens (κ' := κ') A :=
  MvPolynomial.eval₂Hom (rightInc A) fun i => ⟨(v i : K) ⊗ₜ 1, tmul_mem (v i).2 1⟩

@[simp] theorem coe_polyMap_X (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) (i : Fin m) :
    (polyMap (κ' := κ') A v (MvPolynomial.X i) : K ⊗[ℂ] κ') = (v i : K) ⊗ₜ 1 := by
  simp [polyMap]

@[simp] theorem coe_polyMap_C (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) (b : κ') :
    (polyMap (κ' := κ') A v (MvPolynomial.C b) : K ⊗[ℂ] κ') = 1 ⊗ₜ b := by
  simp [polyMap, rightInc]

end GlobalTheory.GraphLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSubalgebraMvPolynomialEvalOfFlatAeval
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSubalgebraMvPolynomialEvalOfFlatAeval
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

theorem flat_polyMap_of_flat_aeval : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] (A : Subalgebra ℂ K)
    (m : ℕ) (v : Fin m → A),
    (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A).toRingHom.Flat →
    (polyMap (κ' := κ') A v).Flat := by
  intro K κ' _ _ _ _ A m v h
  have h1 : (Algebra.TensorProduct.map (AlgHom.id ℂ κ')
      (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A)).toRingHom.Flat :=
    RingHom.Flat.tensorProductMap (f := AlgHom.id ℂ κ') (RingHom.Flat.id κ') h
  let e1 := (MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) ℂ κ').symm.toRingEquiv
  let e2 := ((Algebra.TensorProduct.comm ℂ κ' A).trans (tensEquiv (κ' := κ') A)).toRingEquiv
  have h2 := ((RingHom.Flat.of_bijective (f := e1.toRingHom) e1.bijective).comp h1).comp
    (RingHom.Flat.of_bijective (f := e2.toRingHom) e2.bijective)
  convert h2 using 1
  refine MvPolynomial.ringHom_ext (fun b => Subtype.ext ?_) (fun i => Subtype.ext ?_)
  · have : (MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) ℂ κ').symm (MvPolynomial.C b)
        = b ⊗ₜ 1 := by
      rw [AlgEquiv.symm_apply_eq]; simp [MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]
    simp [e1, e2, tensMap, this]
  · simp [e1, e2, tensMap]

end GlobalTheory.GraphLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSubalgebraMvPolynomialEvalOfFlatAevalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensorSubalgebraMvPolynomialEval_of_flat_aeval : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] (A : Subalgebra ℂ K)
    (m : ℕ) (v : Fin m → A),
    (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A).toRingHom.Flat →
    (polyMap (κ' := κ') A v).Flat := by
  first | exact @GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval | exact GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval | (intros; apply GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAevalDvrPlaceRingUniformiserResidueLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAevalDvrPlaceRingUniformiserResidueLifts
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal.FlatPlace

open MvPolynomial

instance isPrime_span_X_zero (m : ℕ) :
    (Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)}).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero 0)).2 prime_X

theorem exists_X_zero_pow_mul {m : ℕ} {f : MvPolynomial (Fin (m + 1)) ℂ} (hf : f ≠ 0) :
    ∃ (n : ℕ) (g : MvPolynomial (Fin (m + 1)) ℂ),
      g ∉ Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)} ∧ f = X 0 ^ n * g := by
  obtain ⟨n, g, hg, e⟩ := WfDvdMonoid.max_power_factor hf
    (prime_X (R := ℂ) (i := (0 : Fin (m + 1)))).irreducible
  exact ⟨n, g, fun h => hg (Ideal.mem_span_singleton.1 h), e⟩

theorem isDVR_atPrime (m : ℕ) : IsDiscreteValuationRing
    (Localization.AtPrime (Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)})) := by
  set q := Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)}
  set D := Localization.AtPrime q
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0), ?_, ?_⟩
  · have hmax : IsLocalRing.maximalIdeal D = Ideal.span {algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0)} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
    have h0 : algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0) ≠ 0 := by
      intro h
      refine X_ne_zero (R := ℂ) (0 : Fin (m + 1)) ?_
      exact IsLocalization.injective D (M := q.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors q)
        (h.trans (map_zero _).symm)
    refine Prime.irreducible ?_
    rw [← Ideal.span_singleton_prime h0, ← hmax]
    infer_instance
  · intro x hx
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    have hf : f ≠ 0 := by
      rintro rfl
      exact hx (IsLocalization.mk'_zero _)
    obtain ⟨n, g, hg, rfl⟩ := exists_X_zero_pow_mul hf
    refine ⟨n, ?_⟩
    have hgu : IsUnit (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D g) := IsLocalization.map_units D (⟨g, hg⟩ : q.primeCompl)
    have hsu : IsUnit (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D s) := IsLocalization.map_units D s
    have e : IsLocalization.mk' D (X 0 ^ n * g) s * algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D s =
        algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0) ^ n * algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D g := by
      rw [IsLocalization.mk'_spec, map_mul, map_pow]
    show Associated _ (IsLocalization.mk' D (X 0 ^ n * g) s)
    refine (associated_mul_unit_left (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0) ^ n) _ hgu).symm.trans ?_
    rw [← e]
    exact associated_mul_unit_left _ _ hsu

end GlobalTheory.GraphLocal.FlatPlace

namespace GlobalTheory.GraphLocal.FlatPlace

open MvPolynomial

variable {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ]

theorem isUnit_of_ord_eq_zero {E : Place (algebraMap ℂ K)} (y : E.ring) (hy : (y : K) ≠ 0)
    (h0 : E.ord y = 0) : IsUnit y := by
  refine IsUnit.of_mul_eq_one (b := ⟨(y : K)⁻¹, (E.ord_nonneg_iff (inv_ne_zero hy)).1
    (by rw [E.ord_inv, h0]; simp)⟩) (Subtype.ext ?_)
  simp [hy]

theorem flat_aeval_placeAlg (k : ℕ) (R : Subring K)
    (π : R →+* κ) (E : Place (algebraMap ℂ K)) (hER : E.Contains R) (t : E.ring) (zR : Fin k → R) :
    (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
    (∀ a, algebraMap ℂ K a ∈ R) →
    (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
    Irreducible t → AlgebraicIndependent ℂ (fun i => π (zR i)) →
    (MvPolynomial.aeval (Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
        (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E))) :
        MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ] placeAlg E).toRingHom.Flat := by
  intro hπ hc hord ht hind
  set x : Fin (k + 1) → placeAlg E := Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
    (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E)) with hx
  set φ := (MvPolynomial.aeval x : MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ] placeAlg E)
  set q := Ideal.span {(X 0 : MvPolynomial (Fin (k + 1)) ℂ)}

  let cR : ℂ →+* R := (algebraMap ℂ K).codRestrict R hc
  have hπc : π.comp cR = algebraMap ℂ κ := RingHom.ext fun a => hπ a (hc a)

  have hC : ∀ g : MvPolynomial (Fin k) ℂ,
      φ ((finSuccEquiv ℂ k).symm (Polynomial.C g)) = aeval (fun i : Fin k => x i.succ) g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a =>
      rw [show (Polynomial.C (MvPolynomial.C a) : Polynomial (MvPolynomial (Fin k) ℂ)) =
        algebraMap ℂ _ a from rfl, AlgEquiv.commutes, AlgHom.commutes, aeval_C]
    | add p r hp hr => simp only [map_add, hp, hr]
    | mul_X p i hp =>
      rw [Polynomial.C_mul, map_mul, map_mul, hp, ← finSuccEquiv_X_succ, AlgEquiv.symm_apply_apply,
        map_mul, aeval_X, aeval_X]
  have hX : φ ((finSuccEquiv ℂ k).symm Polynomial.X) = x 0 := by
    rw [← finSuccEquiv_X_zero, AlgEquiv.symm_apply_apply, aeval_X]

  have key : ∀ f ∉ q, IsUnit (φ f) := by
    intro f hf
    set p := finSuccEquiv ℂ k f with hpdef
    set g := p.coeff 0
    have hfp : f = (finSuccEquiv ℂ k).symm p := by simp [p]
    have hp : p = Polynomial.X * p.divX + Polynomial.C g := (Polynomial.X_mul_divX_add p).symm
    have hg : g ≠ 0 := by
      intro h0
      apply hf
      rw [hfp, hp, h0, map_zero, add_zero, map_mul, ← finSuccEquiv_X_zero, AlgEquiv.symm_apply_apply]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

    set wR : R := eval₂ cR zR g
    have hwK : (wR : K) = (aeval (fun i : Fin k => x i.succ) g : placeAlg E) := by
      have e1 : (wR : K) = eval₂ (algebraMap ℂ K) (fun i => (zR i : K)) g :=
        eval₂_comp_left R.subtype cR zR g
      have e2 := (comp_aeval (R := ℂ) (fun i : Fin k => x i.succ) (placeAlg E).val).symm
      have e3 := congrArg (fun F : MvPolynomial (Fin k) ℂ →ₐ[ℂ] K => F g) e2
      simp only [AlgHom.comp_apply] at e3
      rw [e1]
      change _ = (placeAlg E).val (aeval (fun i : Fin k => x i.succ) g)
      rw [← e3]
      simp only [x, Fin.cons_succ]
      rfl
    have hπw : π wR ≠ 0 := by
      have e : π wR = aeval (fun i => π (zR i)) g := by
        rw [eval₂_comp_left π cR zR g, hπc]
        rfl
      rw [e]
      intro h0
      exact hg (hind (h0.trans (map_zero _).symm))
    have hw0 : (wR : K) ≠ 0 := by
      intro h0
      apply hπw
      rw [show wR = 0 from Subtype.ext h0, map_zero]
    have hwo : E.ord wR = 0 := by
      have h1 := (E.ord_nonneg_iff hw0).2 (hER _ wR.2)
      have h2 : ¬ 0 < E.ord wR := fun h => hπw ((hord wR hw0).2 h)
      omega
    set u : placeAlg E := aeval (fun i : Fin k => x i.succ) g
    set v : placeAlg E := φ ((finSuccEquiv ℂ k).symm p.divX)
    have hf' : φ f = x 0 * v + u := by
      rw [hfp, hp, map_add (f := _), map_mul, map_add (f := _), map_mul, hX, hC]
    let uE : E.ring := ⟨(u : K), u.2⟩
    let vE : E.ring := ⟨(v : K), v.2⟩
    have huE : IsUnit uE := isUnit_of_ord_eq_zero uE (by rw [← hwK] at *; simpa [uE, ← hwK] using hw0)
      (by simpa [uE, ← hwK] using hwo)
    let yE : E.ring := ⟨(φ f : K), (φ f).2⟩
    have hyE : yE = t * vE + uE := Subtype.ext (by simp [yE, uE, vE, hf', x])
    have hyu : IsUnit yE := by
      by_contra hn
      have hy : yE ∈ IsLocalRing.maximalIdeal E.ring := hn
      have htm : t ∈ IsLocalRing.maximalIdeal E.ring := ht.not_isUnit
      have : uE ∈ IsLocalRing.maximalIdeal E.ring := by
        have := sub_mem hy (Ideal.mul_mem_right vE _ htm)
        rwa [hyE, add_sub_cancel_left] at this
      exact this huE
    let toA : E.ring →+* placeAlg E :=
      { toFun := fun y => ⟨y, y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    exact hyu.map toA
  set D := Localization.AtPrime q
  haveI : IsDiscreteValuationRing D := isDVR_atPrime k
  have hunits : ∀ s : q.primeCompl, IsUnit (φ.toRingHom s) := fun s => key s.1 s.2
  let ℓ : D →+* placeAlg E := IsLocalization.lift (M := q.primeCompl) hunits
  have hcomp : ℓ.comp (algebraMap _ D) = φ.toRingHom := IsLocalization.lift_comp hunits
  have hφ0 : ∀ f, f ≠ 0 → φ f ≠ 0 := by
    intro f hf
    obtain ⟨n, g, hg, rfl⟩ := exists_X_zero_pow_mul hf
    rw [map_mul, map_pow]
    refine mul_ne_zero (pow_ne_zero _ ?_) (key g hg).ne_zero
    intro h
    apply ht.ne_zero
    have e : ((φ (X 0) : placeAlg E) : K) = t := by simp [φ, x]
    exact Subtype.ext (by rw [← e, h]; rfl)
  have hℓ : ℓ.Flat := by
    letI := ℓ.toAlgebra
    rw [RingHom.Flat, Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro a ha
    obtain ⟨⟨d, hd⟩, hda⟩ := (Submodule.mem_torsion_iff _).1 ha
    rw [Submodule.mem_bot]
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl d
    have hf : f ≠ 0 := by
      rintro rfl
      exact nonZeroDivisors.ne_zero hd (IsLocalization.mk'_zero _)
    have hℓd : ℓ (IsLocalization.mk' D f s) ≠ 0 := by
      intro h0
      have := (IsLocalization.lift_mk'_spec hunits f 0 s).1 h0
      exact hφ0 f hf (by simpa using this)
    simp only [Submonoid.mk_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hda
    exact (mul_eq_zero.1 hda).resolve_left hℓd
  have h := (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat D q.primeCompl)).comp hℓ
  rw [hcomp] at h
  exact h

end GlobalTheory.GraphLocal.FlatPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAevalDvrPlaceRingUniformiserResidueLiftsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_aeval_dvrPlaceRing_uniformiser_residueLifts : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (k : ℕ) (R : Subring K)
    (π : R →+* κ) (E : Place (algebraMap ℂ K)) (hER : E.Contains R) (t : E.ring) (zR : Fin k → R),
    (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
    (∀ a, algebraMap ℂ K a ∈ R) →
    (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
    Irreducible t → AlgebraicIndependent ℂ (fun i => π (zR i)) →
    (MvPolynomial.aeval (Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
        (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E))) :
        MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ] placeAlg E).toRingHom.Flat := by
  first | exact @GlobalTheory.GraphLocal.FlatPlace.flat_aeval_placeAlg | exact GlobalTheory.GraphLocal.FlatPlace.flat_aeval_placeAlg | (intros; apply GlobalTheory.GraphLocal.FlatPlace.flat_aeval_placeAlg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLocalizationGraphIdealMinimalPrime
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

theorem height_ge_of_X_sub_C_mem : ∀ {F : Type} [Field F] (m : ℕ) (c : Fin m → F) (P : Ideal (MvPolynomial (Fin m) F))
    [P.IsPrime], (∀ i, MvPolynomial.X i - MvPolynomial.C (c i) ∈ P) → (m : ℕ∞) ≤ P.height := by
  intro F _ m c P _ hP
  have hmk : ∀ f : MvPolynomial (Fin m) F,
      Ideal.Quotient.mk P f = Ideal.Quotient.mk P (MvPolynomial.C (MvPolynomial.eval c f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add (f := _), hp, hq, map_add (f := _), map_add (f := _), map_add (f := _)]
    | mul_X p i hp =>
      have hi : Ideal.Quotient.mk P (MvPolynomial.X i) = Ideal.Quotient.mk P (MvPolynomial.C (c i)) :=
        Ideal.Quotient.eq.2 (hP i)
      rw [map_mul, hp, hi, ← map_mul, ← map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X,
        MvPolynomial.C_mul]
  have hsurj : Function.Surjective ((Ideal.Quotient.mk P).comp MvPolynomial.C) := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨MvPolynomial.eval c f, (hmk f).symm⟩
  have hmax : P.IsMaximal := by
    let e := RingEquiv.ofBijective _ ⟨((Ideal.Quotient.mk P).comp MvPolynomial.C).injective, hsurj⟩
    exact Ideal.Quotient.maximal_of_isField P (MulEquiv.isField (Field.toIsField F) e.symm.toMulEquiv)
  have htr : Algebra.trdeg F (MvPolynomial (Fin m) F) = m := by
    have h2 := (IsTranscendenceBasis.mvPolynomial (Fin m) F).cardinalMk_eq_trdeg
    rw [Cardinal.mk_fin] at h2
    exact h2.symm
  rw [ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field m htr P]

variable {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra (K ⊗[ℂ] κ') L]

theorem height_le_height_of_flat {A : Subalgebra ℂ K} {m : ℕ} (v : Fin m → A)
    (hf : (polyMap (κ' := κ') A v).Flat) (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] :
    (𝔭.comap (polyMap A v)).height ≤ 𝔭.height := by
  letI := (polyMap (κ' := κ') A v).toAlgebra
  haveI : Module.Flat (MvPolynomial (Fin m) κ') (tens (κ' := κ') A) := hf
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin m) κ') (tens (κ' := κ') A) :=
    Algebra.HasGoingDown.of_flat
  set q := 𝔭.comap (polyMap (κ' := κ') A v) with hq
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : 𝔭.LiesOver q := ⟨rfl⟩
  obtain ⟨l, hl, hlen⟩ := q.exists_ltSeries_length_eq_height
  haveI : 𝔭.LiesOver l.last.asIdeal := by rw [hl]; infer_instance
  obtain ⟨L', hlen', hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l 𝔭
  rw [← hlen, ← hlen', (⟨𝔭, ‹_›⟩ : PrimeSpectrum (tens (κ' := κ') A)).height_eq_orderHeight]
  exact Order.length_le_height (le_of_eq hlast)

theorem ringKrullDim_locAt {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L)) :
    ringKrullDim (locAt (L := L) 𝔭) = 𝔭.height := by
  letI := (toQ (L := L) 𝔭).toAlgebra
  haveI : IsLocalization.AtPrime (locAt (L := L) 𝔭) 𝔭 :=
    { map_units := fun s => isUnit_toQ 𝔭 hinj s.2
      surj := fun x => by
        obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 x
        exact ⟨(a, ⟨s, hs⟩), e⟩
      exists_of_eq := fun {a b} e => ⟨1, by
        have : a = b := Subtype.ext (hinj (congrArg Subtype.val e))
        rw [this]⟩ }
  exact IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 _

theorem dim_locAt_graph : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  ringKrullDim (locAt (L := L) 𝔭) = k + 1 := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ k R π ρ E 𝔭 _ hO' hc1 hc2 hfrac hER hcent hz h𝔭
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ L
  obtain ⟨zR, hzR⟩ := GlobalTheory.T.exists_trBasis_in_image_of_fractionField k R π hfrac hz
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  rw [ringKrullDim_locAt 𝔭 hinj]
  apply le_antisymm
  ·
    rw [← ringKrullDim_locAt 𝔭 hinj]
    letI : Algebra ℂ L := ((algebraMap (K ⊗[ℂ] κ') L).comp (algebraMap ℂ (K ⊗[ℂ] κ'))).toAlgebra
    haveI : IsScalarTower ℂ (K ⊗[ℂ] κ') L := IsScalarTower.of_algebraMap_eq' rfl
    have hQ := GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor (L := L) E 𝔭 hO'
    letI : IsLocalRing (locAt (L := L) 𝔭) := isLocalRing_locAt 𝔭 hinj
    letI : Algebra ℂ (locAt (L := L) 𝔭) :=
      ((algebraMap ℂ L).codRestrict _ hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ (locAt (L := L) 𝔭) := hQ.essFiniteType
    haveI : IsNoetherianRing (locAt (L := L) 𝔭) := Algebra.EssFiniteType.isNoetherianRing ℂ _
    have hmax := GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span (L := L) k R π ρ E hER t zR 𝔭 hO' hc1 hc2 hfrac hcent ht hzR h𝔭
    refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
    rw [hmax]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := locAt (L := L) 𝔭)
      (Set.finite_range fun i => toQ (L := L) 𝔭 (gens E R π ρ hER t zR i))
    have h2 : (Set.range fun i => toQ (L := L) 𝔭 (gens E R π ρ hER t zR i)).ncard ≤ k + 1 := by
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      simp [Set.ncard_univ]
    have h3 := h1.trans h2
    exact_mod_cast h3
  ·
    have e : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    have hzR' : IsTranscendenceBasis ℂ (fun i => π (zR i)) := by
      unfold TrBasis at hzR; rw [e] at hzR; exact hzR
    let v : Fin (k + 1) → placeAlg E := Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
        (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E))
    have hf := GlobalTheory.T.flat_tensorSubalgebraMvPolynomialEval_of_flat_aeval (κ' := κ') (placeAlg E) (k + 1) v
      (GlobalTheory.T.flat_aeval_dvrPlaceRing_uniformiser_residueLifts k R π E hER t zR hc1 hc2 hcent ht hzR'.1)
    have hle := height_le_height_of_flat v hf 𝔭
    have hgr : graphIdeal E R π ρ ≤ 𝔭 := h𝔭.1.2
    have hX : ∀ i, MvPolynomial.X i - MvPolynomial.C ((Fin.cons (0 : κ') fun j => ρ (π (zR j)) :
        Fin (k + 1) → κ') i) ∈ 𝔭.comap (polyMap (κ' := κ') (placeAlg E) v) := by
      intro i
      rw [Ideal.mem_comap]
      apply hgr
      apply Ideal.subset_span
      refine Fin.cases ?_ (fun j => ?_) i
      · left
        refine ⟨(t : K), ?_, ?_⟩
        · rw [E.ord_irreducible ht]; exact one_pos
        · simp [v]
      · right
        refine ⟨zR j, ?_⟩
        simp [v]
    have hB3 := height_ge_of_X_sub_C_mem (k + 1) _ _ hX
    have := hB3.trans hle
    exact_mod_cast this

end GlobalTheory.GraphLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLocalizationGraphIdealMinimalPrimeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_localization_graphIdeal_minimalPrime : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  ringKrullDim (locAt (L := L) 𝔭) = k + 1 := by
  first | exact @GlobalTheory.GraphLocal.dim_locAt_graph | exact GlobalTheory.GraphLocal.dim_locAt_graph | (intros; apply GlobalTheory.GraphLocal.dim_locAt_graph <;> assumption)
end
