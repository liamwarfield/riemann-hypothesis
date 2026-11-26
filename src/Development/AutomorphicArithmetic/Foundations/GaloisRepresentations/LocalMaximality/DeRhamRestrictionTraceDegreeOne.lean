module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceCechCochainFractionEqSumFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceFibreRingEqFinsumFibrePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceFibreRingEqFinsumFibrePoints
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.FibTrace

theorem trace_quot_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc hk hred h
  set J : Ideal (rB k K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))) with hJ
  haveI : Module.Finite k (rB k K x {0} ⧸ J) := GlobalTheory.PD.FibFin.finite_quot k K x hc
  haveI : Module.Free k (rB k K x {0} ⧸ J) := Module.Free.of_divisionRing k _
  have hred' : IsReduced (k ⊗[k] (rB k K x {0} ⧸ J)) :=
    isReduced_of_injective (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).toRingHom
      (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).injective
  have key := (GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange (O := k) (H := rB k K x {0} ⧸ J) (K := k) hred').2.2
    (Ideal.Quotient.mk J h)
  rw [Algebra.algebraMap_self, RingHom.id_apply] at key
  rw [key]
  have hker : ∀ e : fib k K x, ∀ a ∈ J, e.1 a = 0 := fun e a ha => by
    have : J ≤ RingHom.ker e.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact e.2 j
    exact this ha
  let E : fib k K x ≃ (rB k K x {0} ⧸ J →ₐ[k] k) :=
    { toFun := fun e => Ideal.Quotient.liftₐ J e.1 (hker e)
      invFun := fun φ => ⟨φ.comp (Ideal.Quotient.mkₐ k J), fun j => by
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        have hm : (⟨_, tco_mem k K x j⟩ : rB k K x {0}) ∈ J := by
          rw [hJ]; exact Ideal.subset_span ⟨j, rfl⟩
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero]⟩
      left_inv := fun e => Subtype.ext (AlgHom.ext fun a => rfl)
      right_inv := fun φ => by
        apply Ideal.Quotient.algHom_ext
        rfl }
  rw [← finsum_comp_equiv E]
  rfl

end GlobalTheory.PD.FibTrace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceFibreRingEqFinsumFibrePointsStatement
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  first | (exact @GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib) | (exact GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib) | (intros; apply GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEvalOriginEqFibreTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceQuotientEqOfProjective
namespace GlobalTheory

open IsLocalRing Module nonZeroDivisors IsLocalization.AtPrime

attribute [local instance] Ideal.Quotient.field

theorem trace_quotient_eq_of_projective (R S : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S]
    [Module.IsTorsionFree R S] [Module.Finite R S] [Module.Projective R S] (p : Ideal R)
    [p.IsMaximal] (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ p.map (algebraMap R S)) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk p (Algebra.intTrace R S x) := by
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let : Algebra Rₚ Sₚ := localizationAlgebra p.primeCompl S
  have hp0 : p.primeCompl ≤ R⁰ := p.primeCompl_le_nonZeroDivisors
  have : IsDomain Rₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hp0
  have : IsIntegrallyClosed Rₚ := isIntegrallyClosed_of_isLocalization _ _ hp0
  have : IsScalarTower R Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  have : IsLocalization (Submonoid.map (algebraMap R S) (Ideal.primeCompl p)) Sₚ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ)
  have e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : IsTorsionFree Rₚ Sₚ := by
    rw [isTorsionFree_iff_algebraMap_injective]
    exact IsLocalization.map_injective_of_injective p.primeCompl Rₚ Sₚ
      (FaithfulSMul.algebraMap_injective R S)
  have : Module.Finite Rₚ Sₚ := .of_isLocalization R S p.primeCompl
  have : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ e
  have : Module.Flat Rₚ Sₚ :=
    Module.Flat.of_isLocalizedModule Rₚ p.primeCompl (IsScalarTower.toAlgHom R S Sₚ).toLinearMap
  have : Module.Free Rₚ Sₚ := Module.free_of_flat_of_isLocalRing
  apply (equivQuotMaximalIdeal p Rₚ).injective
  rw [trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    ← Algebra.intTrace_eq_trace,
    ← Algebra.intTrace_eq_of_isLocalization R S p.primeCompl (Aₘ := Rₚ) (Bₘ := Sₚ) x]
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEvalOriginEqFibreTrace
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.TraceOrigin


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem ev_eq_trace_quot : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ ev : rA k x {0} →ₐ[k] k, RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) → ∀ (h : rB k K x {0}) (a : rA k x {0}), (a : F) = Algebra.trace F K (h : K) → ev a = Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) := by
  intro k _ _ F K _ _ _ _ _ _ d x hc ev hker h a ha
  haveI : Module.IsTorsionFree (rA k x {0}) (integralClosure (rA k x {0}) K) := inferInstance
  haveI : IsFractionRing (rA k x {0}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {0} (Finset.singleton_nonempty 0)).1
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd 0
  haveI : IsIntegrallyClosed (rA k x {0}) :=
    haveI : UniqueFactorizationMonoid (MvPolynomial (Fin d) k) := inferInstance
    haveI : UniqueFactorizationMonoid (rA k x {0}) :=
      (MulEquiv.uniqueFactorizationMonoid e.toMulEquiv inferInstance)
    inferInstance
  haveI := hc.fin
  haveI : Module.Finite (rA k x {0}) (integralClosure (rA k x {0}) K) :=
    (GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc {0} (Finset.singleton_nonempty 0)).1
  haveI := GlobalTheory.T.integralClosure_projective_over_standardOpenRing k F K d x hc 0
  haveI : IsIntegrallyClosed (integralClosure (rA k x {0}) K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension F
  have hsurj : Function.Surjective ev := fun c => ⟨algebraMap k _ c, ev.commutes c⟩
  haveI hmax : (RingHom.ker ev).IsMaximal := RingHom.ker_isMaximal_of_surjective ev hsurj
  let h' : integralClosure (rA k x {0}) K := ⟨h.1, h.2⟩
  have hint : a = Algebra.intTrace (rA k x {0}) (integralClosure (rA k x {0}) K) h' := by
    apply Subtype.ext
    exact ha.trans (Algebra.algebraMap_intTrace (A := rA k x {0}) (K := F) (L := K) h').symm
  have key := GlobalTheory.trace_quotient_eq_of_projective (rA k x {0}) (integralClosure (rA k x {0}) K) (RingHom.ker ev) h'
  set p := RingHom.ker ev with hp
  let e₁ : (rA k x {0}) ⧸ p ≃+* k := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
  have he₁ : ∀ y, e₁ (Ideal.Quotient.mk p y) = ev y := fun y => rfl
  let φ : integralClosure (rA k x {0}) K ≃+* rB k K x {0} :=
    { toFun := fun b => ⟨b.1, b.2⟩, invFun := fun b => ⟨b.1, b.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  set J : Ideal (rB k K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))) with hJdef
  have hJ : J = (p.map (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K))).map φ := by
    rw [hker, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    rfl
  let e₂ := Ideal.quotientEquiv (p.map (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K))) J φ hJ
  have hcomm : (algebraMap k (rB k K x {0} ⧸ J)).comp e₁.toRingHom =
      e₂.toRingHom.comp (algebraMap _ _) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun y => ?_)
    change Ideal.Quotient.mk J (algebraMap k _ (ev y)) = Ideal.Quotient.mk J (φ (algebraMap _ _ y))
    rw [Ideal.Quotient.eq]
    have hmem : y - algebraMap k _ (ev y) ∈ p := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h3 : φ (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K) (y - algebraMap k _ (ev y))) ∈ J :=
      hJ ▸ Ideal.mem_map_of_mem φ (Ideal.mem_map_of_mem _ hmem)
    convert J.neg_mem h3 using 1
    rw [map_sub, map_sub, neg_sub]
    congr 1
    apply Subtype.ext
    change algebraMap k K (ev y) = algebraMap F K (algebraMap k F (ev y))
    exact IsScalarTower.algebraMap_apply k F K _
  have htr := Algebra.trace_eq_of_equiv_equiv e₁ e₂ hcomm (Ideal.Quotient.mk _ h')
  rw [key] at htr
  have h2 : e₂ (Ideal.Quotient.mk _ h') = Ideal.Quotient.mk J h := rfl
  have := congrArg e₁ htr
  rw [RingEquiv.apply_symm_apply, h2, he₁] at this
  rw [hint, this]

end GlobalTheory.PD.TraceOrigin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEvalOriginEqFibreTraceStatement
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_eval_origin_eq_fibre_trace : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ ev : rA k x {0} →ₐ[k] k, RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) → ∀ (h : rB k K x {0}) (a : rA k x {0}), (a : F) = Algebra.trace F K (h : K) → ev a = Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) := by
  first | (exact @GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot) | (exact GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot) | (intros; apply GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LaurentConstantTermEqEvalOriginChart
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LaurentConstantTermEqEvalOriginChart
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.ResEv

open MvPolynomial

theorem ker_aeval_zero (k : Type) [Field k] (d : ℕ) :
    RingHom.ker (aeval (R := k) (fun _ : Fin d ↦ (0 : k))) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by ext i; simpa using h i (Set.mem_univ i)
    subst hm0
    rw [RingHom.mem_ker] at hp
    have : aeval (R := k) (fun _ : Fin d ↦ (0 : k)) p = AddMonoidAlgebra.coeff p 0 := by
      rw [show (fun _ : Fin d ↦ (0 : k)) = 0 from rfl, MvPolynomial.aeval_zero]
      simp [MvPolynomial.constantCoeff_eq]
    exact (mem_support_iff.mp hm) (this ▸ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp

theorem res_aeval (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F)
    (hx : IsPd k x) (ρ : F →ₗ[k] k) (hρ : IsRes k x ρ) (p : MvPolynomial (Fin d) k) :
    ρ (aeval (fun j : Fin d ↦ x j.succ / x 0) p) = aeval (R := k) (fun _ : Fin d ↦ (0 : k)) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_eq_mul]
    by_cases hn : n = 0
    · subst hn
      simp [hρ.1]
    · obtain ⟨j0, hj0⟩ : ∃ j, n j ≠ 0 := by
        by_contra h; push_neg at h; exact hn (Finsupp.ext h)
      have h0 : ∏ j : Fin d, (0 : k) ^ n j = 0 := Finset.prod_eq_zero (Finset.mem_univ j0) (zero_pow hj0)
      rw [h0, smul_zero]
      let m : Fin (d + 1) → ℤ := Fin.cons (-(∑ j, (n j : ℤ))) (fun j ↦ (n j : ℤ))
      have hsum : ∑ i, m i = 0 := by
        rw [Fin.sum_univ_succ]; simp [m]
      have hm : m ≠ 0 := by
        intro h
        have := congrFun h j0.succ
        simp [m] at this
        exact hj0 this
      have hprod : ∏ j : Fin d, (x j.succ / x 0) ^ n j = ∏ i, x i ^ m i := by
        rw [Fin.prod_univ_succ]
        simp only [m, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg]
        rw [Finset.prod_congr rfl (fun j _ ↦ div_pow (x j.succ) (x 0) (n j)), Finset.prod_div_distrib,
          Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast, div_eq_inv_mul]
      rw [hprod, hρ.2 m hsum hm, mul_zero]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]

end GlobalTheory.PD.ResEv

open MvPolynomial in
theorem GlobalTheory.PD.ResEv.chart0 : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∃ ev : rA k x {0} →ₐ[k] k, (∀ a : rA k x {0}, ρ a = ev a) ∧ RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) := by
  intro k _ F _ _ d x hx ρ hρ
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hx 0
  have hv : ∀ p : MvPolynomial (Fin d) k, ((e p : rA k x {0}) : F) = aeval (fun j : Fin d ↦ x j.succ / x 0) p := by
    intro p
    have h1 : ((rA k x {0}).val.comp e.toAlgHom) = aeval (fun j : Fin d ↦ x j.succ / x 0) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [he]
    exact congrArg (fun f => f p) (congrArg DFunLike.coe h1)
  refine ⟨(aeval (R := k) (fun _ : Fin d ↦ (0 : k))).comp e.symm.toAlgHom, fun a => ?_, ?_⟩
  · have := GlobalTheory.PD.ResEv.res_aeval k F d x hx ρ hρ (e.symm a)
    rw [← hv, AlgEquiv.apply_symm_apply] at this
    simpa using this
  · have ht : (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) = (e.toRingEquiv : MvPolynomial (Fin d) k →+* rA k x {0}) '' Set.range X := by
      rw [← Set.range_comp]
      congr 1
      funext j
      apply Subtype.ext
      simp [he]
    rw [ht, ← Ideal.map_span, ← GlobalTheory.PD.ResEv.ker_aeval_zero]
    ext a
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
    rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LaurentConstantTermEqEvalOriginChartStatement
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentConstantTerm_eq_eval_origin_chart : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∃ ev : rA k x {0} →ₐ[k] k, (∀ a : rA k x {0}, ρ a = ev a) ∧ RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) := by
  first | (exact @GlobalTheory.PD.ResEv.chart0) | (exact GlobalTheory.PD.ResEv.chart0) | (intros; apply GlobalTheory.PD.ResEv.chart0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceCechCochainFractionEqSumFibre
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem trF_locCoch_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ (ρ : F →ₗ[k] k), IsRes k x ρ → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), trF k τ ρ (locCoch k K x h Finset.univ) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ ρ hρ hac hred h
  have hloc : locCoch k K x (h : K) Finset.univ = (h : K) • vol0 k K x := if_pos rfl
  have h1 : trF k τ ρ (locCoch k K x (h : K) Finset.univ) = ρ (Algebra.trace F K (h : K)) := by
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [h1]
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd 0
  haveI : IsIntegrallyClosed (rA k x {0}) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  haveI : IsFractionRing (rA k x {0}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {0} (Finset.singleton_nonempty _)).1
  haveI := hc.fin
  have hint : IsIntegral (rA k x {0}) (h : K) := h.2
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := rA k x {0}) (K := F)).1 (Algebra.isIntegral_trace (L := F) hint)
  obtain ⟨ev, hev, hker⟩ := GlobalTheory.T.laurentConstantTerm_eq_eval_origin_chart k F d x hc.pd ρ hρ
  have ha' : (a : F) = Algebra.trace F K (h : K) := ha
  rw [← ha', hev, GlobalTheory.T.trace_eval_origin_eq_fibre_trace k F K d x hc ev hker h a ha', GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints k F K d x hc hac hred h]

end GlobalTheory.PD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceCechCochainFractionEqSumFibreStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_cechCochain_fraction_eq_sum_fibre : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ (ρ : F →ₗ[k] k), IsRes k x ρ → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), trF k τ ρ (locCoch k K x h Finset.univ) = ∑ᶠ e : fib k K x, e.1 h := by
  first | (exact @GlobalTheory.PD.trF_locCoch_eq_finsum_fib) | (exact GlobalTheory.PD.trF_locCoch_eq_finsum_fib) | (intros; apply GlobalTheory.PD.trF_locCoch_eq_finsum_fib  <;> assumption)
end
end

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.deRham_restriction_trace_degree_one :
    ResidueOfTraceIsFiberSum := by
  intro F L _ _ _ _ _ _ d x hc hred ρ hρ h
  obtain ⟨⟨τ, hτ⟩, -⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F L d (xv x) hc
  have hloc : locCoch ℂ L (xv x) (h : L) Finset.univ = (h : L) • vol0 ℂ L (xv x) := if_pos rfl
  have h1 : trF ℂ τ ρ (locCoch ℂ L (xv x) (h : L) Finset.univ) = ρ (Algebra.trace F L (h : L)) := by
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [← h1]
  exact GlobalTheory.T.trace_cechCochain_fraction_eq_sum_fibre ℂ F L d (xv x) hc τ hτ ρ hρ inferInstance hred h
