module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPolynomialSubMem
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatCokerOfInjectiveModMaximalIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem
open IsLocalRing TensorProduct

namespace GlobalTheory.CompleteBaseChange

open MvPowerSeries

theorem monomial_one_mem_span_X_pow {R σ : Type*} [CommRing R] (α : σ →₀ ℕ) :
    (monomial α (1 : R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ α.degree := by
  classical
  induction α using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    have : (monomial (a + b) (1 : R) : MvPowerSeries σ R) = monomial a 1 * monomial b 1 := by
      rw [monomial_mul_monomial, one_mul]
    rw [this, map_add (f := _), pow_add]
    exact Ideal.mul_mem_mul ha hb
  | single s n =>
    rw [← X_pow_eq, Finsupp.degree_single]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self s)) n

theorem exists_polynomial_totalDegree_le_sub_mem : ∀ (R : Type) [CommRing R] (J : Ideal R), J.FG → IsAdicComplete J R → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ R) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) J → ∀ g : MvPowerSeries σ R, ∃ P : MvPolynomial σ R, P.totalDegree ≤ M ∧ g - (P : MvPowerSeries σ R) ∈ Ideal.span (Set.range f) := by
  intro O _ J hJ hO σ τ _ _ f N hM g
  have := Fintype.ofFinite τ
  have hN : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : O) : MvPowerSeries σ O) ∈
      Ideal.span (Set.range f) ⊔ J.map (C : O →+* MvPowerSeries σ O) := fun α hα =>
    hM (hα ▸ monomial_one_mem_span_X_pow α)
  have : IsPrecomplete J (MvPowerSeries σ O) := isPrecomplete_pi (σ →₀ ℕ) hJ
  have : IsHausdorff J (MvPowerSeries σ O) := isHausdorff_pi (σ →₀ ℕ) hJ
  have : IsPrecomplete J (Option τ → MvPowerSeries σ O) := isPrecomplete_pi _ hJ
  let Φ : (Option τ → MvPowerSeries σ O) →ₗ[O] MvPowerSeries σ O :=
    { toFun := fun x => (truncTotal N (x none) : MvPolynomial σ O) + ∑ j, x (some j) * f j
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add (f := _), MvPolynomial.coe_add, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, map_smul, MvPolynomial.coe_smul, smul_add, Finset.smul_sum,
          smul_mul_assoc, RingHom.id_apply] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mkQ_comp_surjective (I := J) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    have h1 := mem_of_coeff_eq_zero N _ hN (G - (truncTotal N G : MvPolynomial σ O)) fun d hd => by
      rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 ha
    refine ⟨fun o => o.elim G c, ((Submodule.Quotient.eq _).2 ?_).symm⟩
    have h2 : G - Φ (fun o => o.elim G c) = b := by
      change G - (((truncTotal N G : MvPolynomial σ O) : MvPowerSeries σ O) + ∑ j, c j * f j) = b
      linear_combination -hab
    rw [h2, Ideal.smul_top_eq_map]
    exact hb
  obtain ⟨x, hx⟩ := hΦ g
  refine ⟨truncTotal N (x none), ?_,
    Ideal.mem_span_range_iff_exists_fun.2 ⟨fun j => x (some j), ?_⟩⟩
  · refine Finset.sup_le fun d hd => ?_
    by_contra hlt
    refine MvPolynomial.mem_support_iff.1 hd (coeff_truncTotal_eq_zero _ ?_)
    exact (not_le.1 hlt).le
  · rw [← hx]
    exact (add_sub_cancel_left _ _).symm

end GlobalTheory.CompleteBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem : ∀ (R : Type) [CommRing R] (J : Ideal R), J.FG → IsAdicComplete J R → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ R) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) J → ∀ g : MvPowerSeries σ R, ∃ P : MvPolynomial σ R, P.totalDegree ≤ M ∧ g - (P : MvPowerSeries σ R) ∈ Ideal.span (Set.range f) := by
  first | exact @GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem | exact GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem | (intros; apply GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.EqCOfPderivZero
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {σ τ : Type}

theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ k) (t : τ) :
    pderiv (R := k) t (subst a f) = ∑ s, subst a (pderiv (R := k) s f) * pderiv (R := k) t (a s) :=
  GlobalTheory.FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero ha) f t

theorem pderiv_comm (u v : τ) (g : MvPowerSeries τ k) : pderiv (R := k) u (pderiv (R := k) v g) = pderiv (R := k) v (pderiv (R := k) u g) := by
  classical
  ext n
  simp only [coeff_pderiv]
  by_cases h : u = v
  · subst h; rfl
  · rw [show n + Finsupp.single u 1 + Finsupp.single v 1 = n + Finsupp.single v 1 + Finsupp.single u 1 by abel]
    simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg h, if_neg (Ne.symm h), add_zero]
    ring

theorem eq_C_of_pderiv_zero [Algebra ℚ k] {g : MvPowerSeries τ k} (h : ∀ v, pderiv (R := k) v g = 0) :
    g = C (constantCoeff g) := by
  classical
  ext n
  rw [coeff_C]
  split_ifs with hn
  · subst hn; rfl
  · obtain ⟨v, hv⟩ : ∃ v, n v ≠ 0 := by
      by_contra hc; push Not at hc; exact hn (Finsupp.ext hc)
    have hle : Finsupp.single v 1 ≤ n := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hv)
    have h1 := congrArg (coeff (n - Finsupp.single v 1)) (h v)
    rw [coeff_pderiv, map_zero, tsub_add_cancel_of_le hle] at h1
    have hc' : (n - Finsupp.single v 1 : τ →₀ ℕ) v + 1 = n v := by
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
    have hc : (((n - Finsupp.single v 1 : τ →₀ ℕ) v : ℕ) : k) + 1 = ((n v : ℕ) : k) := by
      rw [← hc']; push_cast; ring
    rw [hc] at h1
    have hu : IsUnit ((n v : ℕ) : k) := by
      have : ((n v : ℕ) : k) = algebraMap ℚ k (n v : ℚ) := by simp
      rw [this]; exact (IsUnit.mk0 _ (by exact_mod_cast hv)).map _
    rcases hu with ⟨w, hw⟩
    rw [← hw] at h1
    simpa using congrArg (· * ((w⁻¹ : kˣ) : k)) h1

end GlobalTheory.FormalLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatQuotientWeaklyRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatQuotientWeaklyRegular
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem mkQ_mem_smul_top_iff_mem_sup {A : Type} [CommRing A] (J I : Ideal A) (a : A) :
    Submodule.mkQ J a ∈ (I • ⊤ : Submodule A (A ⧸ J)) ↔ a ∈ J ⊔ I := by
  rw [← Submodule.range_mkQ J, LinearMap.range_eq_map, ← Submodule.map_smul'',
    ← Submodule.mem_comap, Submodule.comap_map_mkQ, smul_eq_mul, Ideal.mul_top]

theorem flat_quotient_sup_span_singleton (V A : Type) [CommRing V] [IsNoetherianRing V]
    [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A]
    [IsLocalHom (algebraMap V A)] (J : Ideal A) [Module.Flat V (A ⧸ J)] (r : A)
    (hr : ∀ a : A, r * a ∈ J ⊔ (maximalIdeal V).map (algebraMap V A) →
      a ∈ J ⊔ (maximalIdeal V).map (algebraMap V A)) :
    Module.Flat V (A ⧸ (J ⊔ Ideal.span {r})) := by
  let u : (A ⧸ J) →ₗ[A] (A ⧸ J) := LinearMap.lsmul A (A ⧸ J) r
  have h := flat_coker_of_injective_mod_maximalIdeal V A (A ⧸ J) (A ⧸ J) u (by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective J x
    rw [mkQ_mem_smul_top_iff_mem_sup]
    apply hr
    rw [← mkQ_mem_smul_top_iff_mem_sup]
    exact hx)
  have hu : LinearMap.range u = Submodule.map (Submodule.mkQ J) (Ideal.span {r}) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective J y
      exact ⟨r * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r), rfl⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hb
      exact ⟨Submodule.mkQ J a, rfl⟩
  let e : ((A ⧸ J) ⧸ LinearMap.range u) ≃ₗ[A] (A ⧸ (J ⊔ Ideal.span {r})) :=
    (Submodule.quotEquivOfEq _ _ hu).trans
      (Submodule.quotientQuotientEquivQuotientSup J (Ideal.span {r}))
  exact Module.Flat.of_linearEquiv (e.restrictScalars V).symm

theorem mem_sup_of_isSMulRegular_quotient_quotient {A : Type} [CommRing A] (I J : Ideal A) (r : A)
    (h : IsSMulRegular ((A ⧸ I) ⧸ (J • ⊤ : Submodule A (A ⧸ I))) r) (a : A)
    (ha : r * a ∈ J ⊔ I) : a ∈ J ⊔ I := by
  rw [sup_comm, ← mkQ_mem_smul_top_iff_mem_sup, ← Submodule.Quotient.mk_eq_zero] at ha ⊢
  apply h
  simp only [smul_zero]
  exact ha

theorem flat_quotient_ofList_of_isWeaklyRegular_closedFibre : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) → RingTheory.Sequence.IsWeaklyRegular (A ⧸ (maximalIdeal V).map (algebraMap V A)) rs → Module.Flat V (A ⧸ Ideal.ofList rs) := by
  intro V A _ _ _ _ _ _ _ _ _ rs _ hreg
  have key : ∀ i, i ≤ rs.length → Module.Flat V (A ⧸ Ideal.ofList (rs.take i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [List.take_zero, Ideal.ofList_nil]
      exact Module.Flat.of_linearEquiv
        ((Submodule.quotEquivOfEqBot (⊥ : Ideal A) rfl).restrictScalars V)
    | succ i ih =>
      intro hi
      have hi' : i < rs.length := hi
      haveI := ih hi'.le
      rw [List.take_succ_eq_append_getElem hi', Ideal.ofList_append, Ideal.ofList_singleton]
      exact flat_quotient_sup_span_singleton V A _ _
        (mem_sup_of_isSMulRegular_quotient_quotient _ _ _ (hreg.regular_mod_prev i hi'))
  have h := key rs.length le_rfl
  rwa [List.take_length] at h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatQuotientWeaklyRegularStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_quotient_weakly_regular : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) → RingTheory.Sequence.IsWeaklyRegular (A ⧸ (maximalIdeal V).map (algebraMap V A)) rs → Module.Flat V (A ⧸ Ideal.ofList rs) := by
  first | exact @GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre | exact GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre | (intros; apply GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre <;> assumption)
end
end
