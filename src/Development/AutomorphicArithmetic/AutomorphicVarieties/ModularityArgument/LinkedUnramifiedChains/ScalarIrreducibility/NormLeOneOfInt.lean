module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoPoint
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ResidueHomNorm
theorem UpperTheory.residue_hom_norm :
    ∀ {O R Ω : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [NormedField Ω]
        [IsUltrametricDist Ω] [Algebra O Ω]
        (hres : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ IsLocalRing.maximalIdeal R)
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (hint : ∀ x : Ω, ‖x‖ ≤ 1 → IsIntegral O x)
        (y : R →ₐ[O] Ω),
        (∀ a, ‖y a‖ ≤ 1) ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
  intro O R Ω _ _ _ _ _ _ _ hres hO hint y
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
    intro m hmem
    by_contra hge
    have hge' : 1 ≤ ‖y m‖ := not_lt.mp hge
    have hne : y m ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hge'
      linarith
    have hu : ‖(y m)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hge'
    obtain ⟨p, hp, hev⟩ := hint _ hu
    have hrev : Polynomial.eval₂ (algebraMap O Ω) (y m) p.reverse = 0 := by
      haveI : Invertible (y m)⁻¹ := invertibleOfNonzero (inv_ne_zero hne)
      have h := Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) (y m)⁻¹ p
      rw [invOf_eq_inv, inv_inv, hev] at h
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (inv_ne_zero hne))
    have hq : y (Polynomial.aeval m p.reverse) = 0 := by
      rw [Polynomial.aeval_algHom_apply y m p.reverse |>.symm]
      simpa [Polynomial.aeval_def] using hrev
    have hdvd : m ∣ Polynomial.aeval m p.reverse - 1 := by
      have h := Polynomial.sub_dvd_eval_sub m 0 (p.reverse.map (algebraMap O R))
      have h0 : (p.reverse.map (algebraMap O R)).eval 0 = 1 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
          Polynomial.coeff_zero_reverse, hp.leadingCoeff, map_one]
      rw [h0, sub_zero, Polynomial.eval_map_algebraMap] at h
      exact h
    have hunit : IsUnit (Polynomial.aeval m p.reverse : R) := by
      by_contra hnu
      have h1 : (Polynomial.aeval m p.reverse : R) ∈ IsLocalRing.maximalIdeal R :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have h2 : Polynomial.aeval m p.reverse - 1 ∈ IsLocalRing.maximalIdeal R :=
        Ideal.mem_of_dvd _ hdvd hmem
      have h3 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        have := Ideal.sub_mem _ h1 h2
        simpa using this
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3
    have := hunit.map y
    rw [hq] at this
    exact not_isUnit_zero this
  refine ⟨fun x => ?_, hm⟩
  obtain ⟨a, ha⟩ := hres x
  have hx : y x = algebraMap O Ω a + y (x - algebraMap O R a) := by
    rw [map_sub, AlgHom.commutes]
    ring
  rw [hx]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (hO a) (hm _ ha).le)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DigitExpansionLattice
open IsLocalRing

theorem UpperTheory.digit_expansion_lattice :
    ∀ {O Ω : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [NormedField Ω] [IsUltrametricDist Ω] [Algebra O Ω]
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (ϖ : O) (hϖ : Irreducible ϖ) (hlt : ‖algebraMap O Ω ϖ‖ < 1)
        (S : Submodule O Ω) (hS : ∀ s ∈ S, ‖s‖ ≤ 1) (E : Finset Ω) (hE : ∀ e ∈ E, e ∈ S)
        (hdig : ∀ s ∈ S, ∃ e ∈ E, ∃ s' ∈ S, s = e + ϖ • s'),
        Module.Finite O S := by
  intro O Ω _ _ _ _ _ _ _ hO ϖ hϖ hlt S hS E hE hdig
  classical
  have hI : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hhaus : IsHausdorff (maximalIdeal O) S := by
    refine ⟨fun x hx => ?_⟩
    have hb : ∀ n : ℕ, ‖(x : Ω)‖ ≤ ‖algebraMap O Ω ϖ‖ ^ n := by
      intro n
      have h := hx n
      rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at h
      obtain ⟨t, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      have : (((ϖ ^ n) • t : S) : Ω) = algebraMap O Ω ϖ ^ n * (t : Ω) := by
        simp [Algebra.smul_def]
      rw [this, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hS _ t.2)
    have hlim : Filter.Tendsto (fun n : ℕ => ‖algebraMap O Ω ϖ‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt
    have h0 : ‖(x : Ω)‖ ≤ 0 := ge_of_tendsto' hlim hb
    exact Subtype.ext (norm_le_zero_iff.1 h0)
  have hpre : IsPrecomplete (maximalIdeal O) (E → O) := by
    refine ⟨fun g hg => ?_⟩
    have hcoord : ∀ {m : ℕ} (x : E → O),
        x ∈ (maximalIdeal O ^ m • ⊤ : Submodule O (E → O)) → ∀ i, x i ∈ maximalIdeal O ^ m := by
      intro m x hx i
      have h := Submodule.mem_map_of_mem (f := (LinearMap.proj i : (E → O) →ₗ[O] O)) hx
      rw [Submodule.map_smul''] at h
      have h2 : x i ∈ (maximalIdeal O ^ m • ⊤ : Submodule O O) :=
        Submodule.smul_mono le_rfl le_top h
      simpa using h2
    have hc : ∀ i : E, ∃ L : O, ∀ n, g n i ≡ L [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] := by
      intro i
      refine IsPrecomplete.prec (I := maximalIdeal O) (M := O) inferInstance (f := fun n => g n i) ?_
      intro m n hmn
      have h := (SModEq.sub_mem.1 (hg hmn))
      refine SModEq.sub_mem.2 ?_
      have h2 := hcoord _ h i
      simpa using h2
    choose L hL using hc
    refine ⟨L, fun n => ?_⟩
    refine SModEq.sub_mem.2 ?_
    have hsum : g n - L = ∑ i : E, (g n i - L i) • (Pi.single i 1 : E → O) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    have h := SModEq.sub_mem.1 (hL i n)
    simpa using h
  let v : E → S := fun e => ⟨e, hE e e.2⟩
  let f : (E → O) →ₗ[O] S := Fintype.linearCombination O v
  have hsurj : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := maximalIdeal O) ?_
    intro y
    obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨e, he, s', hs', hs⟩ := hdig s s.2
    refine ⟨Pi.single ⟨e, he⟩ 1, ?_⟩
    have hf : f (Pi.single ⟨e, he⟩ 1) = ⟨e, hE e he⟩ := by
      simp [f, v, Fintype.linearCombination_apply_single]
    simp only [LinearMap.comp_apply, hf]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hI,
      Submodule.ideal_span_singleton_smul]
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨-⟨s', hs'⟩, trivial, ?_⟩
    apply Subtype.ext
    simp [hs]
  exact Module.Finite.of_surjective f hsurj
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsUnitOfInvIntegral
open Polynomial

private lemma integral_of_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) :
    IsIntegral ℤ_[l] x := by
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hx
  have hl : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  have h0 := minpoly.aeval ℚ_[l] x
  rw [← hq, aeval_def, eval₂_map] at h0
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact h0

private lemma norm_of_integral {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l)
    (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hc : spectralValue (minpoly ℚ_[l] x) ≤ 1 := by
    rw [spectralValue_le_one_iff (minpoly.monic h.tower_top)]
    intro n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  exact hc

private lemma isUnit_of_inv_integral {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (a : R) (ha : algebraMap R K a ≠ 0)
    (h : IsIntegral R (algebraMap R K a)⁻¹) : IsUnit a := by
  obtain ⟨p, hp, he⟩ := h
  letI := invertibleOfNonzero (inv_ne_zero ha)
  have h1 := eval₂_reverse_mul_pow (algebraMap R K) ((algebraMap R K a)⁻¹) p
  rw [he, invOf_eq_inv, inv_inv] at h1
  have h2 : eval₂ (algebraMap R K) (algebraMap R K a) p.reverse = 0 := by
    simpa [ha] using h1
  have h3 : eval a p.reverse = 0 := by
    apply hinj
    rw [map_zero, ← h2, eval₂_at_apply]
  have h5 : p.reverse.coeff 0 = 1 := by
    simp [coeff_zero_reverse, hp.leadingCoeff]
  have h4 := divX_mul_X_add p.reverse
  rw [← h4, h5] at h3
  simp only [eval_add, eval_mul, eval_X, eval_C] at h3
  exact isUnit_iff_exists_inv.2 ⟨-(eval a p.reverse.divX), by linear_combination -h3⟩

theorem UpperTheory.integral_dvr_norm :
    ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O]
        [Module.Finite ℤ_[l] O],
        (∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → IsIntegral O x) ∧ (∀ a : O, ‖(a : PadicAlgCl l)‖ ≤ 1) ∧
          ∀ a : O, ¬ IsUnit a → ‖(a : PadicAlgCl l)‖ < 1 := by
  intro l _ O _ _
  have hfin : ∀ a : O, IsIntegral ℤ_[l] (a : PadicAlgCl l) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map O.val
  refine ⟨fun x hx => (integral_of_norm x hx).tower_top, fun a => norm_of_integral _ (hfin a),
    fun a ha => lt_of_le_of_ne (norm_of_integral _ (hfin a)) fun h1 => ha ?_⟩
  have ha0 : (a : PadicAlgCl l) ≠ 0 := by
    intro h
    simp [h] at h1
  have hinv : IsIntegral O (a : PadicAlgCl l)⁻¹ :=
    (integral_of_norm _ (by rw [norm_inv, h1, inv_one])).tower_top
  exact isUnit_of_inv_integral (K := PadicAlgCl l) Subtype.val_injective a ha0 hinv
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteOfIsFiniteLength
open IsLocalRing in
private lemma finite_of_isFiniteLength {S : Type} [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] {M : Type} [AddCommGroup M] [Module S M]
    (h : IsFiniteLength S M) : Finite M := by
  induction h with
  | of_subsingleton => exact Finite.of_subsingleton
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have hIm : I = maximalIdeal S := IsLocalRing.eq_maximalIdeal hI
    subst hIm
    haveI : Finite (S ⧸ maximalIdeal S) := ‹Finite (ResidueField S)›
    haveI : Finite (M ⧸ N) := Finite.of_equiv _ e.symm.toEquiv
    haveI : Finite (M ⧸ N.toAddSubgroup) := ‹Finite (M ⧸ N)›
    haveI : Finite N.toAddSubgroup := ih
    exact Finite.of_addSubgroup_quotient N.toAddSubgroup

open IsLocalRing in
theorem UpperTheory.monic_ideal_completion :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [Finite (IsLocalRing.ResidueField O)] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
        [IsLocalHom (algebraMap O R)]
        (hres : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ IsLocalRing.maximalIdeal R)
        (J : Ideal R) (hJ : ∀ x : R, ∃ P : Polynomial O, P.Monic ∧ Polynomial.aeval x P ∈ J)
        (ϖ : O) (hϖ : Irreducible ϖ),
        Finite (R ⧸ (J ⊔ Ideal.span {algebraMap O R ϖ})) := by
  intro O R _ _ _ _ _ _ _ _ _ hres J hJ ϖ hϖ
  obtain ⟨I, hIdef⟩ : ∃ I, I = J ⊔ Ideal.span {algebraMap O R ϖ} := ⟨_, rfl⟩
  rw [← hIdef]
  have hJI : J ≤ I := hIdef ▸ le_sup_left
  have hϖI : algebraMap O R ϖ ∈ I :=
    hIdef ▸ (le_sup_right : _ ≤ J ⊔ Ideal.span {algebraMap O R ϖ}) (Ideal.subset_span rfl)
  by_cases hI : I = ⊤
  · subst hI
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Finite.of_subsingleton
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral O (R ⧸ I) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, hP, hx⟩ := hJ x
    refine ⟨P, hP, ?_⟩
    rw [← Polynomial.aeval_def]
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ O I) x P
    rw [Ideal.Quotient.mkₐ_eq_mk] at h
    rw [h]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJI hx)⟩
  have hm : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_zero_iff.mpr fun Q hQ =>
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) Q (by
      have hle : Ideal.span {ϖ} ≤ Q.comap (algebraMap O (R ⧸ I)) := by
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
        have : algebraMap O (R ⧸ I) ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hϖI
        rw [this]
        exact Q.zero_mem
      have hne : Q.comap (algebraMap O (R ⧸ I)) ≠ ⊤ := (Ideal.comap_isPrime _ Q).ne_top
      change (Q.comap (algebraMap O (R ⧸ I))).IsMaximal
      rw [← hm.eq_of_le hne hle]
      exact hm)
  haveI : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩
  have hImax : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hmk : ∀ x ∈ maximalIdeal R, Ideal.Quotient.mk I x ∈ maximalIdeal (R ⧸ I) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨z, hz⟩ := hu.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hz
    have h1 := hImax hz
    have h2 : x * y ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hx
    have h3 : (1 : R) ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem h2 h1
      simpa using this
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3
  let φ : O →+* ResidueField (R ⧸ I) := (residue (R ⧸ I)).comp (algebraMap O (R ⧸ I))
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hres x
    refine ⟨a, ?_⟩
    have h := hmk _ ha
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at h
    exact h.symm
  have hφk : ∀ a ∈ maximalIdeal O, φ a = 0 := by
    intro a ha
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
      exact fun hu => ha (isUnit_of_map_unit (algebraMap O R) a hu)
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hmk _ h1)
  haveI : Finite (O ⧸ maximalIdeal O) := ‹Finite (ResidueField O)›
  haveI : Finite (ResidueField (R ⧸ I)) :=
    Finite.of_surjective (Ideal.Quotient.lift (maximalIdeal O) φ hφk)
      (Ideal.Quotient.lift_surjective_of_surjective _ _ hφs)
  exact finite_of_isFiniteLength (S := R ⧸ I) (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
end

theorem UpperTheory.Reformulated.B.CoPoint.coPt :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) [UpperTheory.V.Fr.IsCoef l ↥c.O] (R : Type)
    [inst_2 : CommRing R] [inst_3 : Algebra (↥c.O) R] [inst_4 : UpperTheory.V.Alg.IsCO (↥c.O) R]
    (y : R →ₐ[↥c.O] Formalism.ConjugateSelfDual.Qbar l),
    Module.Finite ↥c.O ↥y.range ∧
      (∀ (a : R), ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ ≤ (1 : ℝ)) ∧
        ∀ a ∈ IsLocalRing.maximalIdeal R,
          ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ <
            (1 :
              ℝ) := by
  intro l _ c _ R _ _ _ y
  obtain ⟨hint, hO, hm⟩ := UpperTheory.integral_dvr_norm l c.O
  have hO' : ∀ a : c.O, ‖algebraMap c.O (Formalism.ConjugateSelfDual.Qbar l) a‖ ≤ 1 := hO
  have hres : ∀ x : R, ∃ a : c.O, x - algebraMap c.O R a ∈ IsLocalRing.maximalIdeal R :=
    UpperTheory.V.Alg.IsCO.res_surj
  obtain ⟨hb1, hb2⟩ := UpperTheory.residue_hom_norm (O := c.O) (Ω := Formalism.ConjugateSelfDual.Qbar l) hres hO' hint y
  refine ⟨?_, hb1, hb2⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hJ : ∀ x : R, ∃ P : Polynomial c.O, P.Monic ∧ Polynomial.aeval x P ∈ RingHom.ker y := fun x => by
    obtain ⟨P, hP, h0⟩ := hint (y x) (hb1 x)
    refine ⟨P, hP, ?_⟩
    rw [RingHom.mem_ker]
    have h1 : Polynomial.aeval (y x) P = 0 := h0
    rw [Polynomial.aeval_algHom_apply] at h1
    exact h1
  have hfin := UpperTheory.monic_ideal_completion hres (RingHom.ker y) hJ ϖ hϖ
  have hlt : ‖algebraMap c.O (Formalism.ConjugateSelfDual.Qbar l) ϖ‖ < 1 :=
    hm ϖ hϖ.not_isUnit
  classical
  letI := Fintype.ofFinite (R ⧸ (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}))
  have key := UpperTheory.digit_expansion_lattice hO' ϖ hϖ hlt (Subalgebra.toSubmodule y.range)
    (fun s hs => by
      obtain ⟨r, rfl⟩ := hs
      exact hb1 r)
    (Finset.univ.image fun q : R ⧸ (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}) => y (Quotient.out q))
    (fun e he => by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 he
      exact ⟨_, rfl⟩)
    (fun s hs => by
      obtain ⟨r, rfl⟩ := hs
      have hq : r - Quotient.out (Ideal.Quotient.mk (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}) r) ∈
          RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ} := by
        rw [← Ideal.Quotient.eq]
        simp [Ideal.Quotient.mk_out]
      obtain ⟨j, hj, t, ht, hjt⟩ := Submodule.mem_sup.1 hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ht
      refine ⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ r, Finset.mem_univ _, rfl⟩, y a, ⟨a, rfl⟩, ?_⟩
      have h2 := congrArg y hjt
      rw [map_add (f := _), RingHom.mem_ker.1 hj, map_sub, map_mul, AlgHom.commutes] at h2
      rw [Algebra.smul_def, mul_comm]
      linear_combination -h2)
  exact key
end

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J

end UpperTheory.V.J

theorem UpperTheory.V.J.coPt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (y : R →ₐ[c.O] Qbar l),
        Module.Finite c.O y.range ∧ (∀ a, ‖y a‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal R, ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.CoPoint.coPt
