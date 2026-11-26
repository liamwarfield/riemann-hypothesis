module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import GroundTheory.GlobalFields.Artin.OneDim
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.PrincZl

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.FrobDense
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Tw.frobDense :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → Dense {σ : G K Ω | ∃ (w : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), ¬ w.asIdeal ∣ 𝔪 ∧ IsPlaceOver A w ∧ IsFrob A (normV w) σ} := by
  intro K Ω _ _ _ _ _ 𝔪 h𝔪
  have hS : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔪}.Finite := Ideal.finite_factors h𝔪
  refine (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := K) (Ω := Ω)
    GlobalTheory.Published.chebotarevDegreeOne' hS).mono ?_
  rintro σ ⟨v, hv, _, B, hB, hσ⟩
  exact ⟨v, B, hv, hB, hσ⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.RayChar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Tw

open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {C : Type} [CommGroup C]

private noncomputable def rcExt (f : Ideal (𝓞 K) → C) (I : FractionalIdeal (𝓞 K)⁰ K) : C :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), f v.asIdeal ^ FractionalIdeal.count K v I

private theorem rcExt_fin (f : Ideal (𝓞 K) → C) (I : FractionalIdeal (𝓞 K)⁰ K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => f v.asIdeal ^ FractionalIdeal.count K v I).Finite := by
  have h := FractionalIdeal.finite_factors (K := K) I
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv h0 => hv ?_
  simp only [h0, zpow_zero]

private theorem rcExt_mul (f : Ideal (𝓞 K) → C) {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    rcExt f (I * J) = rcExt f I * rcExt f J := by
  unfold rcExt
  rw [← finprod_mul_distrib (rcExt_fin f I) (rcExt_fin f J)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul K v hI hJ, zpow_add]

private theorem rcExt_one (f : Ideal (𝓞 K) → C) : rcExt f 1 = 1 := by
  unfold rcExt
  simp only [FractionalIdeal.count_one, zpow_zero, finprod_one]

private theorem rcExt_prime (f : Ideal (𝓞 K) → C) (w : HeightOneSpectrum (𝓞 K)) :
    rcExt f (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = f w.asIdeal := by
  unfold rcExt
  rw [finprod_eq_single _ w]
  · rw [FractionalIdeal.count_self, zpow_one]
  · intro v hv
    rw [FractionalIdeal.count_maximal_coprime K v hv.symm, zpow_zero]

private theorem rcExt_coe (𝔪 : Ideal (𝓞 K)) (f : Ideal (𝓞 K) → C)
    (hm : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪 → IsCoprime J 𝔪 → f (I * J) = f I * f J)
    (J : Ideal (𝓞 K)) : J ≠ ⊥ → IsCoprime J 𝔪 → rcExt f (J : FractionalIdeal (𝓞 K)⁰ K) = f J := by
  have h1 : f 1 = 1 := by
    have := hm 1 1 one_ne_zero one_ne_zero isCoprime_one_left isCoprime_one_left
    rw [mul_one] at this
    exact left_eq_mul.1 this
  refine UniqueFactorizationMonoid.induction_on_prime J (fun h => absurd rfl h) ?_ ?_
  · intro x hx _ _
    rw [isUnit_iff_eq_one.1 hx, h1, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top, rcExt_one]
  · intro a p ha hp ih _ hc
    have hp0 : p ≠ ⊥ := hp.ne_zero
    rw [FractionalIdeal.coeIdeal_mul, rcExt_mul f (FractionalIdeal.coeIdeal_ne_zero.2 hp0)
      (FractionalIdeal.coeIdeal_ne_zero.2 ha), ih ha hc.of_mul_left_right,
      hm p a hp0 ha hc.of_mul_left_left hc.of_mul_left_right]
    congr 1
    exact rcExt_prime f ⟨p, Ideal.isPrime_of_prime hp, hp0⟩

private theorem rc_frac (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) (x : K)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 →
      v.valuation K x ≤ WithZero.exp (-(multiplicity v.asIdeal 𝔪 : ℤ))) :
    ∃ c d : 𝓞 K, c ≠ 0 ∧ c - 1 ∈ 𝔪 ∧ d ∈ 𝔪 ∧ x * algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d := by
  let D : Ideal (𝓞 K) :=
    { carrier := {c | ∃ d : 𝓞 K, x * algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro a b ⟨d, hd⟩ ⟨e, he⟩
        exact ⟨d + e, by rw [map_add (f := _), mul_add, hd, he, map_add (f := _)]⟩
      smul_mem' := by
        rintro r a ⟨d, hd⟩
        exact ⟨r * d, by rw [smul_eq_mul, map_mul, map_mul, ← hd]; ring⟩ }
  have hsup : D ⊔ 𝔪 = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM0 : M ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ le_sup_right.trans hle))
    let v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hM0⟩
    have hv : v.asIdeal ∣ 𝔪 := Ideal.dvd_iff_le.2 (le_sup_right.trans hle)
    have h1 : v.valuation K x ≤ 1 := (hx v hv).trans (by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    obtain ⟨n, d, hd⟩ := v.exists_primeCompl_mul_eq_of_integer x h1
    exact d.2 (hle (Ideal.mem_sup_left (show (d : 𝓞 K) ∈ D from ⟨n, hd⟩)))
  obtain ⟨c, hc, hc0, hc1⟩ : ∃ c ∈ D, c ≠ 0 ∧ c - 1 ∈ 𝔪 := by
    obtain ⟨c, hc, m, hm, e⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ D ⊔ 𝔪)
    have h1 : c - 1 ∈ 𝔪 := by
      rw [← e, sub_add_cancel_left]; exact 𝔪.neg_mem hm
    by_cases h0 : c = 0
    · obtain ⟨n, d, hd, e'⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
      have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
      refine ⟨d, ⟨n, ?_⟩, hd0, ?_⟩
      · rw [← e', div_mul_cancel₀]
        exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd0
      · have : 𝔪 = ⊤ := by
          rw [h0, zero_add] at e
          exact (Ideal.eq_top_iff_one _).2 (e ▸ hm)
        rw [this]; trivial
    · exact ⟨c, hc, h0, h1⟩
  obtain ⟨d, hd⟩ := hc
  refine ⟨c, d, hc0, hc1, ?_, hd⟩
  rw [← Ideal.iInf_maxPowDividing_eq h𝔪, Submodule.mem_iInf]
  intro v
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity h𝔪]
  by_cases hv : v.asIdeal ∣ 𝔪
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
    change v.valuation K (algebraMap (𝓞 K) K d) ≤ _
    rw [← hd, map_mul]
    exact (mul_le_of_le_one_right' (v.valuation_le_one c)).trans (hx v hv)
  · rw [multiplicity_eq_zero_of_not_dvd hv, pow_zero, Ideal.one_eq_top]; trivial

private theorem rc_cop {𝔪 : Ideal (𝓞 K)} {a : 𝓞 K} (h : a - 1 ∈ 𝔪) : IsCoprime (Ideal.span {a}) 𝔪 := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have : (1 : 𝓞 K) = a - (a - 1) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) (Ideal.mem_sup_right h)

private theorem rc_hom (𝔪 : GroundTheory.Global.Modulus K) (f : Ideal (𝓞 K) → C)
    (hm : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪.ideal → IsCoprime J 𝔪.ideal → f (I * J) = f I * f J)
    (h1 : ∀ a : 𝓞 K, a ≠ 0 → a - 1 ∈ 𝔪.ideal → f (Ideal.span {a}) = 1) :
    ∃ F : 𝔪.IdealRayClassGroup →* C, ∀ (w : HeightOneSpectrum (𝓞 K)) (hw : ¬ w.asIdeal ∣ 𝔪.ideal),
      F (𝔪.primeClass hw) = f w.asIdeal := by
  let F₀ : 𝔪.coprimeIdeals →* C :=
    { toFun := fun I => rcExt f ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      map_one' := rcExt_one f
      map_mul' := fun I J => rcExt_mul f (Units.ne_zero _) (Units.ne_zero _) }
  have key : ∀ a : 𝓞 K, a ≠ 0 → a - 1 ∈ 𝔪.ideal →
      rcExt f (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a)) = 1 := fun a ha ha1 => by
    rw [← FractionalIdeal.coeIdeal_span_singleton, rcExt_coe 𝔪.ideal f hm _
      (by rwa [Ne, Ideal.span_singleton_eq_bot]) (rc_cop ha1), h1 a ha ha1]
  refine ⟨QuotientGroup.lift _ F₀ ?_, fun w hw => rcExt_prime f w⟩
  intro I hI
  obtain ⟨a, ha, e⟩ := 𝔪.mem_principalRay.1 hI
  have hval : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.ideal →
      v.valuation K ((a : K) - 1) ≤ WithZero.exp (-(multiplicity v.asIdeal 𝔪.ideal : ℤ)) := by
    intro v hv
    simpa [GroundTheory.Global.Modulus.exponent,
      FiniteMultiplicity.of_prime_left v.prime 𝔪.ideal_ne_bot] using (𝔪.mem_rayUnits.1 ha).1 v hv
  obtain ⟨c, d, hc0, hc1, hd, hcd⟩ := rc_frac 𝔪.ideal 𝔪.ideal_ne_bot ((a : K) - 1) hval
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hc0
  have e2 : (a : K) * algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K (c + d) := by
    rw [map_add (f := _), ← hcd]; ring
  have hb0 : c + d ≠ 0 := fun h => by
    rw [h, map_zero] at e2
    exact mul_ne_zero a.ne_zero hcK e2
  have hb1 : c + d - 1 ∈ 𝔪.ideal := by
    rw [add_sub_right_comm]; exact Ideal.add_mem _ hc1 hd
  have h3 := key _ hb0 hb1
  rw [← e2, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    rcExt_mul f (FractionalIdeal.spanSingleton_ne_zero_iff.2 a.ne_zero)
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hcK), key c hc0 hc1, mul_one] at h3
  change rcExt f ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 1
  rw [← e, coe_toPrincipalIdeal]
  exact h3

end UpperTheory.V.Ws.Tw

theorem UpperTheory.V.Ws.Tw.rayChar :
    ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → ∀ (C : Type) [CommGroup C] (f : Ideal (𝓞 K) → C), (∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪 → IsCoprime J 𝔪 → f (I * J) = f I * f J) → (∀ a : 𝓞 K, a ≠ 0 → a - 1 ∈ 𝔪 → f (Ideal.span {a}) = 1) → ∃ κ : G K Ω →* C, IsOpen (κ.ker : Set (G K Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 K), ¬ w.asIdeal ∣ 𝔪 → ∀ A : ValuationSubring Ω, IsPlaceOver A w → Ine (F := K) A ≤ κ.ker ∧ ∀ σ : G K Ω, IsFrob A (normV w) σ → κ σ = f w.asIdeal := by
  intro K Ω _ _ _ _ _ _ 𝔪 h𝔪 C _ f hm h1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let M : GroundTheory.Global.Modulus K := ⟨𝔪, h𝔪, ∅⟩
  obtain ⟨F, hF⟩ := rc_hom M f hm h1
  haveI : NumberField (M.rayClassField Ω) := NumberField.of_module_finite K _
  haveI : Algebra.IsAlgebraic (M.rayClassField Ω) Ω := Algebra.IsAlgebraic.tower_top (K := K) _
  haveI : IsAlgClosure (M.rayClassField Ω) Ω := ⟨inferInstance, inferInstance⟩
  let r : G K Ω →* (M.rayClassField Ω ≃ₐ[K] M.rayClassField Ω) := AlgEquiv.restrictNormalHom (M.rayClassField Ω)
  let κ : G K Ω →* C := (F.comp (M.rayClassArtinEquiv Ω).symm.toMonoidHom).comp r
  have hker : r.ker ≤ κ.ker := fun σ hσ => by
    change F ((M.rayClassArtinEquiv Ω).symm (r σ)) = 1
    rw [MonoidHom.mem_ker.1 hσ, map_one, map_one]
  refine ⟨κ, ?_, fun w hw A hA => ?_⟩
  · refine Subgroup.isOpen_mono hker ?_
    have : r.ker = (M.rayClassField Ω).fixingSubgroup := IntermediateField.restrictNormalHom_ker _
    rw [this]
    exact IntermediateField.fixingSubgroup_isOpen _
  · obtain ⟨u, hu, hl⟩ := CompanionTheory.FamInh.exists_place_between (L := M.rayClassField Ω) hA
    have hI : u.asIdeal.inertia (M.rayClassField Ω ≃ₐ[K] M.rayClassField Ω) = ⊥ :=
      (CompanionTheory.FamInh.inertia_eq_bot_iff w u).2 (M.ramificationIdx_rayClassField_eq_one Ω hw u)
    refine ⟨fun σ hσ => hker ?_, fun σ hσ => ?_⟩
    · have := CompanionTheory.FamInh.res_mem_inertia hu hσ
      rw [hI] at this
      exact this
    · haveI : Finite (𝓞 (M.rayClassField Ω) ⧸ u.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ u.ne_bot
      have e : r σ = M.rayClassArtinEquiv Ω (M.primeClass hw) := by
        rw [M.rayClassArtinEquiv_primeClass Ω hw u]
        exact GroundTheory.Global.IsArithFrobAt.eq_of_inertia_eq_bot (R := 𝓞 K) hI
          (CompanionTheory.FamInh.res_isArithFrobAt hu hσ) (_root_.IsArithFrobAt.arithFrobAt _ _ _)
      change F ((M.rayClassArtinEquiv Ω).symm (r σ)) = _
      rw [e, MulEquiv.symm_apply_apply, hF]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.RootChar
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ReducedCoefficients
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralOfNormLeOne
theorem UpperTheory.padicAlgCl_isIntegral_of_norm_le_one :
    ∀ {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l), ‖x‖ ≤ 1 → IsIntegral ℤ_[l] x := by
  intro l _ x hx
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hint
  have hs : spectralValue (minpoly ℚ_[l] x) ≤ 1 := hx
  have hc : ∀ n : ℕ, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hs
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq]
  exact minpoly.aeval _ _
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DvrOfNormIntegral
theorem UpperTheory.dvr_of_norm_integral :
    ∀ {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], (∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → IsIntegral ℤ_[l] x) → IsDiscreteValuationRing (integralClosure ℤ_[l] K) := by
  intro l _ K _ h
  have hded : IsDedekindDomain (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K _
  have hfr : IsFractionRing (integralClosure ℤ_[l] K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[l] ℚ_[l] K _
  have key : ∀ x : K, ‖(x : PadicAlgCl l)‖ ≤ 1 →
      IsLocalization.IsInteger (integralClosure ℤ_[l] K) x := by
    intro x hx
    have hi : IsIntegral ℤ_[l] x :=
      (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective).mp (h _ hx)
    exact ⟨⟨x, hi⟩, rfl⟩
  have hval : ValuationRing (integralClosure ℤ_[l] K) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _ K]
    intro x
    rcases le_total ‖(x : PadicAlgCl l)‖ 1 with hx | hx
    · exact Or.inl (key x hx)
    · refine Or.inr (key _ ?_)
      rw [IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ hx
  have hinjK : Function.Injective (algebraMap ℤ_[l] K) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K, RingHom.coe_comp]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K)) := by
    intro a b hab
    exact hinjK (congrArg Subtype.val hab)
  have hnf : ¬ IsField (integralClosure ℤ_[l] K) := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l]
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hf)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[l] K) hnf).out 1 2).mpr hval
end

namespace UpperTheory.Reformulated.B.CoefficientRingContainingIntegers

theorem rc_coef {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : UpperTheory.V.HV.Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O := by
  have hD : IsDiscreteValuationRing (integralClosure ℤ_[l] K) := UpperTheory.dvr_of_norm_integral K (fun x hx => UpperTheory.padicAlgCl_isIntegral_of_norm_le_one x hx)
  have hF : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x hx h1 => ?_⟩
  exact ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 (UpperTheory.padicAlgCl_isIntegral_of_norm_le_one x h1), rfl⟩

end UpperTheory.Reformulated.B.CoefficientRingContainingIntegers
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

open Polynomial

private theorem rc_coef {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O :=
  _root_.UpperTheory.Reformulated.B.CoefficientRingContainingIntegers.rc_coef K

private theorem rc_root {κ : Type} [NormedField κ] [IsAlgClosed κ] (γ : κ) (hγ : ‖γ - 1‖ < 1) (n : ℕ) (hn : 0 < n) :
    ∃ b : κ, b ^ n = γ ∧ ‖b - 1‖ < 1 := by
  by_contra hc
  push Not at hc
  have hm : (X ^ n - C γ : κ[X]).Monic := monic_X_pow_sub_C γ hn.ne'
  have hs := (IsAlgClosed.splits (X ^ n - C γ : κ[X])).eq_prod_roots_of_monic hm
  have he := congrArg (fun p => ‖eval 1 p‖) hs
  simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C, eval_multiset_prod, Multiset.map_map] at he
  have h1 : 1 ≤ ‖(Multiset.map (eval 1 ∘ fun a => X - C a) (X ^ n - C γ : κ[X]).roots).prod‖ := by
    refine Multiset.prod_induction (fun x : κ => 1 ≤ ‖x‖) _ (fun a b ha hb => ?_) (by simp) ?_
    · rw [norm_mul]; exact one_le_mul_of_one_le_of_one_le ha hb
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
      have hb' : b ^ n = γ := by
        have := (mem_roots hm.ne_zero).1 hb
        simpa [sub_eq_zero] using this
      have := hc b hb'
      rw [norm_sub_rev] at this
      simpa using this
  rw [norm_sub_rev] at hγ
  linarith

private theorem rc_pow {κ : Type} [NormedField κ] [IsUltrametricDist κ] (b : κ) (hb : ‖b - 1‖ < 1) (k : ℕ) :
    ‖b ^ k - 1‖ ≤ ‖b - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : b ^ (k + 1) - 1 = (b ^ k - 1) * (b - 1) + ((b ^ k - 1) + (b - 1)) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih le_rfl)))
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ih.trans hb.le)

private theorem rc_char {l : ℕ} [Fact l.Prime] (b : PadicAlgCl l) (hb : ‖b - 1‖ < 1) :
    ∃ (κ : AddChar ℤ_[l] (PadicAlgCl l)) (c : Coef l), Continuous κ ∧ κ 1 = b ∧ ∀ x, κ x ∈ c.O ∧ ‖κ x - 1‖ < 1 := by
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] {b}
  haveI : FiniteDimensional ℚ_[l] K := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral b)
  obtain ⟨c, hc⟩ := rc_coef K
  haveI : CompleteSpace K := by
    have h : IsClosed (K.toSubmodule : Set (PadicAlgCl l)) := Submodule.closed_of_finiteDimensional _
    have h2 : IsComplete (K.toSubmodule : Set (PadicAlgCl l)) := Submodule.complete_of_finiteDimensional _
    exact h2.completeSpace_coe
  haveI : IsBoundedSMul ℤ_[l] K := by
    refine IsBoundedSMul.of_norm_smul_le fun r x => ?_
    show ‖((r • x : K) : PadicAlgCl l)‖ ≤ ‖r‖ * ‖(x : PadicAlgCl l)‖
    have : ((r • x : K) : PadicAlgCl l) = (r : ℚ_[l]) • (x : PadicAlgCl l) := rfl
    rw [this, norm_smul]
    rfl
  let b' : K := ⟨b, IntermediateField.mem_adjoin_simple_self _ b⟩
  have hb' : ‖b' - 1‖ < 1 := hb
  have ht := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hb'
  let κ₀ : AddChar ℤ_[l] K := PadicInt.addChar_of_value_at_one (b' - 1) ht
  have h0 : Continuous κ₀ := PadicInt.continuous_addChar_of_value_at_one ht
  have h1 : κ₀ 1 = b' := by
    rw [PadicInt.addChar_of_value_at_one_def]; ring
  let κ : AddChar ℤ_[l] (PadicAlgCl l) := (K.val : K →* PadicAlgCl l).compAddChar κ₀
  have hκ : ∀ x, κ x = (κ₀ x : PadicAlgCl l) := fun _ => rfl
  have hcont : Continuous κ := continuous_subtype_val.comp h0
  have hone : κ 1 = b := by rw [hκ, h1]
  have hle : ∀ x, ‖κ x - 1‖ ≤ ‖b - 1‖ := by
    intro x
    refine PadicInt.denseRange_natCast.induction_on x
      (isClosed_le (hcont.sub continuous_const).norm continuous_const) fun k => ?_
    rw [← nsmul_one, AddChar.map_nsmul_eq_pow, hone]
    exact rc_pow b hb k
  refine ⟨κ, c, hcont, hone, fun x => ⟨hc _ (κ₀ x).2 ?_, (hle x).trans_lt hb⟩⟩
  have : κ x = (κ x - 1) + 1 := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hle x).trans hb.le) (by simp))

private theorem rc_princ {l : ℕ} [Fact l.Prime] (u : ℤ_[l]ˣ) : u ∈ KStar.TotallyRealRoots.princ l 1 ↔ ‖(u : ℤ_[l]) - 1‖ < 1 := by
  rw [KStar.TotallyRealRoots.mem_princ, pow_one, PadicInt.norm_lt_one_iff_dvd]

private theorem rc_equiv {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) :
    Nonempty (KStar.TotallyRealRoots.princ l 1 ≃ₜ* Multiplicative ℤ_[l]) := by
  refine (princZl l (KStar.TotallyRealRoots.princ l 1) ?_ (by rw [qExp, if_neg hl]) ?_).1
  · apply Subgroup.isClosed_of_isOpen
    have : (KStar.TotallyRealRoots.princ l 1 : Set ℤ_[l]ˣ) = {u : ℤ_[l]ˣ | ‖(u : ℤ_[l]) - 1‖ < 1} := Set.ext rc_princ
    rw [this]
    exact isOpen_lt (Units.continuous_val.sub continuous_const).norm continuous_const
  · have hn : ‖(l : ℤ_[l])‖ < 1 := by rw [PadicInt.norm_lt_one_iff_dvd]
    have hu : IsUnit (1 - (l : ℤ_[l])) := (Units.oneSub _ hn).isUnit
    intro h
    have h1 : hu.unit ∈ KStar.TotallyRealRoots.princ l 1 := by
      rw [rc_princ]; simpa using hn
    rw [h, Subgroup.mem_bot] at h1
    have h2 := congrArg Units.val h1
    have h3 : (l : ℤ_[l]) = 0 := by simpa using h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h3)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.Tw.rootChar :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (π : Γ →* ℤ_[l]ˣ), Continuous π → (∀ s, ‖(π s : ℤ_[l]) - 1‖ < 1) → ∀ n : ℕ, 0 < n → ∃ (t : Γ →* Multiplicative ℤ_[l]) (β : Γ →* (PadicAlgCl l)ˣ) (c₁ : Coef l), Continuous t ∧ t.ker = π.ker ∧ t.ker ≤ β.ker ∧ Continuous β ∧ (∀ s, (β s : PadicAlgCl l) ∈ c₁.O ∧ ‖(β s : PadicAlgCl l) - 1‖ < 1) ∧ (∀ s, (β s : PadicAlgCl l) ^ n = algebraMap ℤ_[l] (PadicAlgCl l) (π s : ℤ_[l])) ∧ ∀ s s', π s * π s' = 1 → β s * β s' = 1 := by
  intro l _ hl Γ _ _ _ _ π hπ h1 n hn
  obtain ⟨e⟩ := rc_equiv hl
  let π' : Γ →* KStar.TotallyRealRoots.princ l 1 := π.codRestrict _ fun s => (rc_princ _).2 (h1 s)
  have hπ' : Continuous π' := hπ.subtype_mk _
  let t : Γ →* Multiplicative ℤ_[l] := (e.toMulEquiv : _ →* _).comp π'
  have ht : ∀ s, t s = e (π' s) := fun _ => rfl
  have htc : Continuous t := e.continuous.comp hπ'
  have hnorm : ∀ x : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) x‖ = ‖x‖ := fun x => by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    rfl
  have hac : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)) :=
    (AddMonoidHomClass.isometry_of_norm _ hnorm).continuous
  let κ₀ : AddChar ℤ_[l] (PadicAlgCl l) := AddChar.toMonoidHomEquiv.symm
    ((algebraMap ℤ_[l] (PadicAlgCl l) : ℤ_[l] →* _).comp ((Units.coeHom _).comp
      ((KStar.TotallyRealRoots.princ l 1).subtype.comp (e.toMulEquiv.symm : _ →* _))))
  have hκ₀ : ∀ x, κ₀ x = algebraMap ℤ_[l] (PadicAlgCl l) ((e.symm (Multiplicative.ofAdd x) : ℤ_[l]ˣ) : ℤ_[l]) :=
    fun _ => rfl
  have hc₀ : Continuous κ₀ :=
    hac.comp (Units.continuous_val.comp (continuous_subtype_val.comp (e.symm.continuous.comp continuous_ofAdd)))
  have hγ : ‖κ₀ 1 - 1‖ < 1 := by
    rw [hκ₀, ← map_one (algebraMap ℤ_[l] (PadicAlgCl l)), ← map_sub, hnorm]
    exact (rc_princ _).1 (e.symm _).2
  obtain ⟨b, hbn, hb⟩ := rc_root _ hγ n hn
  obtain ⟨κ, c, hκc, hκ1, hκ⟩ := rc_char b hb
  have heq : κ ^ n = κ₀ := by
    refine PadicInt.denseRange_natCast.addChar_eq_of_eval_one_eq ?_ hc₀ ?_
    · exact (hκc.pow n).congr fun x => (AddChar.pow_apply κ n x).symm
    · rw [AddChar.pow_apply, hκ1, hbn]
  let β : Γ →* (PadicAlgCl l)ˣ := (κ.toMonoidHom.comp t).toHomUnits
  have hβ : ∀ s, (β s : PadicAlgCl l) = κ (Multiplicative.toAdd (t s)) := fun _ => rfl
  have hβv : Continuous fun s => (β s : PadicAlgCl l) := hκc.comp (continuous_toAdd.comp htc)
  have hker : t.ker = π.ker := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ht, map_eq_one_iff e e.injective]
    exact Subtype.ext_iff
  have hle : t.ker ≤ β.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    ext
    rw [hβ, hs]
    simp
  refine ⟨t, β, c, htc, hker, hle, ?_, fun s => hκ _, fun s => ?_, fun s s' h => ?_⟩
  · refine Units.continuous_iff.2 ⟨hβv, ?_⟩
    exact (hβv.comp continuous_inv).congr fun s => by simp
  · rw [hβ, ← AddChar.pow_apply, heq, hκ₀, ofAdd_toAdd, ht, e.symm_apply_apply]
    rfl
  · rw [← map_mul] at h ⊢
    exact hle (hker ▸ h)
end
