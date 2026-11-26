module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenseMvPolynomialEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AemeasurableFinsumSection
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAdmissible
public import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.AlgebraicIndependentFreeVar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteVerticalGaussValuations
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

namespace VerticalGauss

open IsLocalRing IsDedekindDomain

noncomputable def extPrime {K : Type} [Field K] [NumberField K] (σ : Type)
    (la : HeightOneSpectrum (𝓞 K)) : Ideal (MvPolynomial σ (𝓞 K)) :=
  la.asIdeal.map MvPolynomial.C

theorem mem_extPrime {K : Type} [Field K] [NumberField K] {σ : Type}
    (la : HeightOneSpectrum (𝓞 K)) (p : MvPolynomial σ (𝓞 K)) :
    p ∈ extPrime σ la ↔ ∀ m, p.coeff m ∈ la.asIdeal :=
  MvPolynomial.mem_map_C_iff

instance extPrime_isPrime {K : Type} [Field K] [NumberField K] (σ : Type)
    (la : HeightOneSpectrum (𝓞 K)) : (extPrime σ la).IsPrime := by
  haveI := la.isPrime
  unfold extPrime
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) la.asIdeal).symm.toMulEquiv.isDomain

theorem isDVR {K : Type} [Field K] [NumberField K] (σ : Type) [Finite σ]
    (la : HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (Localization.AtPrime (extPrime σ la)) := by
  classical
  set P := extPrime σ la
  set Ol := Localization.AtPrime la.asIdeal
  have : IsDiscreteValuationRing Ol :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) la.ne_bot Ol
  have hC : ∀ y : la.asIdeal.primeCompl,
      IsUnit ((algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)).comp
        (MvPolynomial.C) (y : 𝓞 K)) := by
    intro y
    apply IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P)
      ⟨MvPolynomial.C (y : 𝓞 K), _⟩
    intro hy
    apply y.2
    have := (MvPolynomial.mem_map_C_iff (I := la.asIdeal) (f := MvPolynomial.C (y : 𝓞 K))).mp hy 0
    simpa using this
  let φ : Ol →+* Localization.AtPrime P := IsLocalization.lift (M := la.asIdeal.primeCompl) hC
  have hφ : φ.comp (algebraMap (𝓞 K) Ol) =
      (algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)).comp MvPolynomial.C :=
    IsLocalization.lift_comp hC
  have hmax : maximalIdeal (Localization.AtPrime P) = (maximalIdeal Ol).map φ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map, hφ, ← Ideal.map_map]
    rfl
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    rw [isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
    intro h
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
    have hm : (algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)) (MvPolynomial.C a) ∈
        P.map (algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)) :=
      Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    rw [h, Ideal.mem_bot] at hm
    have hinj := IsLocalization.injective (Localization.AtPrime P) (M := P.primeCompl)
      P.primeCompl_le_nonZeroDivisors
    apply ha0
    have := hinj (hm.trans (map_zero _).symm)
    simpa using this
  refine ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr ?_
  rw [hmax]
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Ol))
  rw [hg]
  refine ⟨⟨φ g, ?_⟩⟩
  change Ideal.map φ (Ideal.span {g}) = Ideal.span {φ g}
  rw [Ideal.map_span, Set.image_singleton]

theorem injective_of_dvr {R Ω : Type} [CommRing R] [IsDomain R] [Field Ω] (φ : R →+* Ω)
    (P : Ideal R) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)]
    (hker : ∀ r, φ r = 0 → r ∈ P) (a : R) (ha : a ∈ P) (ha0 : φ a ≠ 0) :
    Function.Injective φ := by
  have hu : ∀ y : P.primeCompl, IsUnit (φ y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (hker _ h)
  let ψ : Localization.AtPrime P →+* Ω := IsLocalization.lift (M := P.primeCompl) hu
  have hψ : ∀ r, ψ (algebraMap R _ r) = φ r := fun r => IsLocalization.lift_eq hu r
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  have hϖ0 : ψ ϖ ≠ 0 := by
    intro h
    have hm : algebraMap R (Localization.AtPrime P) a ∈ maximalIdeal (Localization.AtPrime P) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P a).2 ha
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    apply ha0
    rw [← hψ, hc, map_mul, h, zero_mul]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have hinj := IsLocalization.injective (Localization.AtPrime P) (M := P.primeCompl)
    P.primeCompl_le_nonZeroDivisors
  have hr1 : algebraMap R (Localization.AtPrime P) r ≠ 0 := (map_ne_zero_iff _ hinj).2 hr0
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr1 hϖ
  rw [← hψ, hn, map_mul, map_pow] at hr
  exact mul_ne_zero (u.isUnit.map ψ).ne_zero (pow_ne_zero _ hϖ0) hr

theorem nonneg_of_isIntegral {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (w : AddValuation Ω (WithTop ℤ)) (h : ∀ r, 0 ≤ w (algebraMap R Ω r)) {b : Ω}
    (hb : IsIntegral R b) : 0 ≤ w b := by
  letI : Algebra R (vRing w) := ((algebraMap R Ω).codRestrict (vRing w) h).toAlgebra
  haveI : IsScalarTower R (vRing w) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hb' : IsIntegral (vRing w) b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
  rw [← hy]
  exact y.2

theorem finite_places {R Ω : Type} [CommRing R] [IsDomain R] [Field Ω] [CharZero Ω] [Algebra R Ω]
    [Algebra (FractionRing R) Ω] [IsScalarTower R (FractionRing R) Ω]
    [FiniteDimensional (FractionRing R) Ω]
    (P : Ideal R) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)] :
    {v : AddValuation Ω (WithTop ℤ) | IsNormDiscrete v ∧
      ∀ x : R, 0 ≤ v (algebraMap R Ω x) ∧ (0 < v (algebraMap R Ω x) ↔ x ∈ P)}.Finite := by
  set O := Localization.AtPrime P
  set F := FractionRing R
  letI : Algebra O Ω := ((algebraMap F Ω).comp (algebraMap O F)).toAlgebra
  haveI : IsScalarTower O F Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R O Ω := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply O F Ω, ← IsScalarTower.algebraMap_apply R O F,
      ← IsScalarTower.algebraMap_apply R F Ω])
  haveI : CharZero F := RingHom.charZero (algebraMap F Ω)
  obtain ⟨hD, _, _, _, hmax, _⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F Ω
  haveI : IsFractionRing (integralClosure O Ω) Ω :=
    integralClosure.isFractionRing_of_finite_extension F Ω
  haveI := hmax.to_subtype
  haveI : Finite (HeightOneSpectrum (integralClosure O Ω)) := by
    refine Finite.of_injective (fun v => (⟨v.asIdeal, v.isMaximal⟩ :
      {I : Ideal (integralClosure O Ω) | I.IsMaximal})) ?_
    intro v v' h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)
  obtain ⟨e, -⟩ := ValPl.placesOver_bij O F Ω
  have hfin : (ValPl.PlacesOver O Ω).Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e)
  refine hfin.subset ?_
  rintro v ⟨h1, h2⟩
  exact ⟨h1, (ValPl.placesOver_iff_loc P v).1 h2⟩

end VerticalGauss


open VerticalGauss IsDedekindDomain in
theorem finite_vertical_gauss_valuations : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D : ℕ) (x : Fin D → Ω), (⊤ : IntermediateField K Ω).FG → Algebra.trdeg K Ω = D → ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) | IsNormDiscrete v ∧ v g ≠ 0 ∧ ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ∀ p : MvPolynomial (Fin D) (𝓞 K), 0 ≤ v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ∧ (0 < v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ↔ ∀ m, p.coeff m ∈ la.asIdeal)}.Finite := by
  intro K Ω _ _ _ _ D x hFG htr g hg
  classical
  by_contra hinf
  obtain ⟨v₀, -, -, la₀, h₀⟩ := Set.Infinite.nonempty hinf
  apply hinf
  clear hinf
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let ι : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K)
  have hι : Function.Injective ι :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective (𝓞 K) K)
  let φ : MvPolynomial (Fin D) (𝓞 K) →+* Ω := MvPolynomial.eval₂Hom ι x
  have hinj : Function.Injective φ := by
    haveI := VerticalGauss.isDVR (Fin D) la₀
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la₀.ne_bot
    refine VerticalGauss.injective_of_dvr φ (VerticalGauss.extPrime (Fin D) la₀) (fun r hr => ?_) (MvPolynomial.C a)
      (Ideal.mem_map_of_mem _ ha) ?_
    · rw [VerticalGauss.mem_extPrime, ← (h₀ r).2]
      change 0 < v₀ (φ r)
      rw [hr]; simp
    · simp only [φ, MvPolynomial.eval₂Hom_C]
      exact (map_ne_zero_iff _ hι).2 ha0
  letI : Algebra (𝓞 K) Ω := ι.toAlgebra
  haveI : IsScalarTower (𝓞 K) K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul (𝓞 K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hι
  have hind : AlgebraicIndependent (𝓞 K) x := hinj
  haveI : Algebra.IsAlgebraic (𝓞 K) K := IsLocalization.isAlgebraic K (nonZeroDivisors (𝓞 K))
  have hB : IsTranscendenceBasis K x :=
    (hind.extendScalars K).isTranscendenceBasis_of_trdeg_le_of_finite (by simp [htr])
  have hB' : IsTranscendenceBasis (𝓞 K) x :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_iff (𝓞 K) K).2 hB
  set R := MvPolynomial (Fin D) (𝓞 K)
  letI : Algebra R Ω := φ.toAlgebra
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI halg : Algebra.IsAlgebraic R Ω := by
    have := hB'.isAlgebraic
    exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq hind.aevalEquiv.toRingEquiv.toRingHom
      (RingHom.id Ω) hind.aevalEquiv.surjective Function.injective_id
      (RingHom.ext fun p => hind.algebraMap_aevalEquiv p)
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  haveI : Algebra.IsAlgebraic (FractionRing R) Ω := Algebra.IsAlgebraic.extendScalars
    (IsFractionRing.injective R (FractionRing R))
  haveI : FiniteDimensional (FractionRing R) Ω := by
    obtain ⟨S, hS⟩ := hFG
    have htop : IntermediateField.adjoin (FractionRing R) (S : Set Ω) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ IntermediateField.adjoin K (S : Set Ω) := hS ▸ IntermediateField.mem_top
      have hO : ∀ a : 𝓞 K, ι a ∈ IntermediateField.adjoin (FractionRing R) (S : Set Ω) := by
        intro a
        have : ι a = algebraMap (FractionRing R) Ω (algebraMap R _ (MvPolynomial.C a)) := by
          rw [← IsScalarTower.algebraMap_apply]
          exact (MvPolynomial.eval₂Hom_C ι x a).symm
        rw [this]; exact IntermediateField.algebraMap_mem _ _
      induction hy using IntermediateField.adjoin_induction with
      | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
      | algebraMap k =>
        obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
        rw [map_div₀]
        exact div_mem (hO a) (hO b)
      | add a b _ _ ha hb => exact add_mem (ha trivial) (hb trivial)
      | inv a _ ha => exact inv_mem (ha trivial)
      | mul a b _ _ ha hb => exact mul_mem (ha trivial) (hb trivial)
    have : FiniteDimensional (FractionRing R)
        (IntermediateField.adjoin (FractionRing R) (S : Set Ω)) :=
      IntermediateField.finiteDimensional_adjoin fun y _ =>
        (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
    rw [htop] at this
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  obtain ⟨r, hr0, hr⟩ := (halg.isAlgebraic g).exists_integral_multiple
  obtain ⟨s, hs0, hs⟩ := (halg.isAlgebraic g⁻¹).exists_integral_multiple
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 (mul_ne_zero hr0 hs0)
  have hfin : {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      la.asIdeal ∣ Ideal.span {AddMonoidAlgebra.coeff (r * s) m}}.Finite :=
    Ideal.finite_factors (I := Ideal.span {AddMonoidAlgebra.coeff (r * s) m}) (by simpa using hm)
  refine (hfin.biUnion (t := fun la => {v : AddValuation Ω (WithTop ℤ) | IsNormDiscrete v ∧
      ∀ y : R, 0 ≤ v (algebraMap R Ω y) ∧ (0 < v (algebraMap R Ω y) ↔ y ∈ VerticalGauss.extPrime (Fin D) la)})
      (fun la _ => haveI := VerticalGauss.isDVR (Fin D) la; VerticalGauss.finite_places _)).subset ?_
  rintro v ⟨hv, hvg, la, hla⟩
  have hla' : ∀ y : R, 0 ≤ v (algebraMap R Ω y) ∧
      (0 < v (algebraMap R Ω y) ↔ y ∈ VerticalGauss.extPrime (Fin D) la) := fun y => by
    rw [VerticalGauss.mem_extPrime]; exact hla y
  refine Set.mem_biUnion (x := la) ?_ ⟨hv, hla'⟩
  rw [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  refine (VerticalGauss.mem_extPrime la _).1 ?_ m
  by_contra hrs
  have hz : ∀ y : R, y ∉ VerticalGauss.extPrime (Fin D) la → v (algebraMap R Ω y) = 0 := fun y hy =>
    le_antisymm (not_lt.1 fun h => hy ((hla' y).2.1 h)) (hla' y).1
  have h1 := VerticalGauss.nonneg_of_isIntegral v (fun y => (hla' y).1) hr
  have h2 := VerticalGauss.nonneg_of_isIntegral v (fun y => (hla' y).1) hs
  rw [Algebra.smul_def, AddValuation.map_mul,
    hz _ (fun h => hrs (Ideal.mul_mem_right _ _ h)), zero_add] at h1
  rw [Algebra.smul_def, AddValuation.map_mul,
    hz _ (fun h => hrs (Ideal.mul_mem_left _ _ h)), zero_add] at h2
  refine hvg (ValPl.wt_add_eq_zero h1 h2 ?_)
  rw [← AddValuation.map_mul, mul_inv_cancel₀ hg, AddValuation.map_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MeasurableSumEmbeddingsOverGenericPoint
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory


open Polynomial in
theorem finsum_embeddings_over_eq_sum_roots {F L : Type} [Field F] [Field L] [Algebra F L]
    [Algebra.IsSeparable F L] (pb : PowerBasis F L) (τ : F →+* ℂ) {δ : ℕ} (r : Fin δ → ℂ)
    (hr : ∏ i, (X - C (r i)) = (minpoly F pb.gen).map τ) (g : (L →+* ℂ) → ℝ) (g' : ℂ → ℝ)
    (hg : ∀ P : L →+* ℂ, P.comp (algebraMap F L) = τ → g P = g' (P pb.gen)) :
    ∑ᶠ P ∈ {P : L →+* ℂ | P.comp (algebraMap F L) = τ}, g P = ∑ k, g' (r k) := by
  classical
  letI : Algebra F ℂ := τ.toAlgebra
  have hτ : algebraMap F ℂ = τ := rfl
  have hroot : ∀ k, aeval (r k) (minpoly F pb.gen) = 0 := by
    intro k
    rw [aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hsep : (∏ i, (X - C (r i))).Separable := by
    rw [hr]
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F pb.gen)
  have hinj : Function.Injective r := separable_prod_X_sub_C_iff.mp hsep
  let P : Fin δ → (L →+* ℂ) := fun k => (pb.lift (r k) (hroot k)).toRingHom
  have hPgen : ∀ k, P k pb.gen = r k := fun k => pb.lift_gen (r k) (hroot k)
  have hPinj : Function.Injective P := by
    intro k l h
    apply hinj
    rw [← hPgen, ← hPgen, h]
  have hPτ : ∀ k, (P k).comp (algebraMap F L) = τ := by
    intro k
    ext x
    exact (pb.lift (r k) (hroot k)).commutes x
  have hset : {P : L →+* ℂ | P.comp (algebraMap F L) = τ} = Set.range P := by
    ext Q
    constructor
    · intro hQ
      have hQ' : Q.comp (algebraMap F L) = τ := hQ
      let Q' : L →ₐ[F] ℂ := { Q with commutes' := fun x => by rw [hτ, ← hQ']; rfl }
      have h0 : aeval (Q' pb.gen) (minpoly F pb.gen) = 0 := by
        rw [aeval_algHom_apply, minpoly.aeval, map_zero]
      rw [aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod, Finset.prod_eq_zero_iff] at h0
      obtain ⟨k, -, hk⟩ := h0
      refine ⟨k, ?_⟩
      have hk' : Q' pb.gen = r k := by simpa [sub_eq_zero] using hk
      have : pb.lift (r k) (hroot k) = Q' := by
        apply pb.algHom_ext
        rw [pb.lift_gen, hk']
      show (pb.lift (r k) (hroot k)).toRingHom = Q
      rw [this]
    · rintro ⟨k, rfl⟩
      exact hPτ k
  rw [hset, finsum_mem_range hPinj, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hg _ (hPτ k), hPgen]

theorem measurable_sum_embeddings_over_generic_point :
    (∀ δ : ℕ, ∃ ρ : (Fin δ → ℂ) → (Fin δ → ℂ), Measurable ρ ∧ ∀ c : Fin δ → ℂ, ∏ i, (Polynomial.X - Polynomial.C (ρ c i)) = Polynomial.X ^ δ + ∑ i : Fin δ, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) → ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ] (L : Type) [Field L] [Algebra (FractionRing (MvPolynomial σ K)) L] [FiniteDimensional (FractionRing (MvPolynomial σ K)) L] (sg : K →+* ℂ) (m : ℕ) (b : Fin m → L) (Nf : (Fin m → ℂ) → ℝ), Measurable Nf → ∃ Φ : (σ → ℂ) → ℝ, Measurable Φ ∧ ∀ t : σ → ℂ, (∀ p : MvPolynomial σ K, p ≠ 0 → MvPolynomial.eval₂ sg t p ≠ 0) → Φ t = ∑ᶠ P ∈ {P : L →+* ℂ | ∀ p : MvPolynomial σ K, P (algebraMap (FractionRing (MvPolynomial σ K)) L (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) = MvPolynomial.eval₂ sg t p}, Nf (fun i => P (b i)) := by
  intro hρ K _ _ σ _ L _ _ _ sg m b Nf hNf
  classical
  set R := MvPolynomial σ K with hR
  set F := FractionRing R with hF
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let pb : PowerBasis F L := Field.powerBasisOfFiniteOfSeparable F L
  obtain ⟨ρ, hρm, hρ⟩ := hρ pb.dim
  choose nu de hde hfr using fun z : F => IsFractionRing.div_surjective (A := R) z
  let ev : F → (σ → ℂ) → ℂ := fun f t =>
    MvPolynomial.eval₂ sg t (nu f) / MvPolynomial.eval₂ sg t (de f)
  have hpm : ∀ p : R, Measurable fun t : σ → ℂ => MvPolynomial.eval₂ sg t p := by
    intro p
    simp_rw [MvPolynomial.eval₂_eq_eval_map]
    exact (MvPolynomial.continuous_eval _).measurable
  have hev : ∀ f, Measurable (ev f) := fun f => (hpm _).div (hpm _)
  let cf : (σ → ℂ) → Fin pb.dim → ℂ := fun t i => ev ((minpoly F pb.gen).coeff i) t
  have hcf : Measurable cf := Measurable.of_eval fun i => hev _
  let G : (σ → ℂ) → ℂ → ℝ := fun t z =>
    Nf fun i => ∑ l : Fin pb.dim, ev (pb.basis.repr (b i) l) t * z ^ (l : ℕ)
  refine ⟨fun t => ∑ k, G t (ρ (cf t) k), ?_, ?_⟩
  · refine Finset.measurable_sum _ fun k _ => hNf.comp (Measurable.of_eval fun i => ?_)
    refine Finset.measurable_sum _ fun l _ => (hev _).mul (Measurable.pow_const ?_ _)
    exact (measurable_pi_apply k).comp (hρm.comp hcf)
  · intro t ht
    have hinj : Function.Injective (MvPolynomial.eval₂Hom sg t : R →+* ℂ) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro p hp
      by_contra h
      exact ht p h hp
    let τ : F →+* ℂ := IsFractionRing.lift hinj
    have hτa : ∀ p : R, τ (algebraMap R F p) = MvPolynomial.eval₂ sg t p := fun p =>
      IsFractionRing.lift_algebraMap hinj p
    have hτ : ∀ f, τ f = ev f t := by
      intro f
      conv_lhs => rw [← hfr f]
      rw [map_div₀, hτa, hτa]
    have hset : {P : L →+* ℂ | ∀ p : R, P (algebraMap F L (algebraMap R F p)) =
        MvPolynomial.eval₂ sg t p} = {P : L →+* ℂ | P.comp (algebraMap F L) = τ} := by
      ext P
      constructor
      · intro hP
        apply IsFractionRing.ringHom_ext (A := R)
        intro p
        rw [hτa]
        exact hP p
      · intro hP p
        have hP' : P.comp (algebraMap F L) = τ := hP
        rw [← hτa, ← hP']
        rfl
    rw [hset]
    symm
    refine finsum_embeddings_over_eq_sum_roots pb τ (ρ (cf t)) ?_ _ (G t) ?_
    · rw [hρ]
      have hmon : (minpoly F pb.gen).Monic := minpoly.monic pb.isIntegral_gen
      conv_rhs => rw [hmon.as_sum, pb.natDegree_minpoly]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
        Finset.sum_range]
      simp [cf, hτ]
    · intro P hP
      show Nf _ = Nf _
      congr 1
      funext i
      conv_lhs => rw [← pb.basis.sum_repr (b i)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Algebra.smul_def, map_mul, pb.basis_eq_pow, map_pow, ← hτ, ← hP]
      rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMeasurableRootsEnumeration
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsProdXSubCOfMonic
open Polynomial

namespace GlobalTheory.MonicRootsProduct

theorem exists_prod_X_sub_C_of_monic (p : ℂ[X]) (hm : p.Monic) :
    ∃ r : Fin p.natDegree → ℂ, ∏ j, (X - C (r j)) = p := by
  classical
  have hc : p.roots.toList.length = p.natDegree := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  refine ⟨fun j => p.roots.toList[(j : ℕ)]'(by rw [hc]; exact j.2), ?_⟩
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm
    IsAlgClosed.card_roots_eq_natDegree
  rw [← Multiset.coe_toList p.roots, Multiset.map_coe, Multiset.prod_coe,
    ← Fin.prod_univ_fun_getElem] at hprod
  exact (Fintype.prod_equiv (finCongr hc.symm) _ _ (fun j => rfl)).trans hprod

theorem exists_roots {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ, ∏ j : Fin δ, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  have hdeg := Polynomial.degree_sum_fin_lt c
  have hmon : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).Monic := Polynomial.monic_X_pow_add hdeg
  have hd : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).natDegree = δ := by
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_of_monic _ hmon
  exact ⟨fun j => r (Fin.cast hd.symm j),
    (Fintype.prod_equiv (finCongr hd.symm) _ _ (fun j => rfl)).trans hr⟩

end GlobalTheory.MonicRootsProduct
end

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

open Polynomial

theorem continuous_coeff_prod_X_sub_C {ι : Type} (s : Finset ι) (n : ℕ) :
    Continuous fun r : ι → ℂ => (∏ j ∈ s, (X - C (r j))).coeff n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, coeff_mul]
    refine continuous_finsetSum _ fun p _ => Continuous.mul ?_ (ih _)
    simp only [coeff_sub, coeff_C]
    refine continuous_const.sub ?_
    split_ifs
    · exact continuous_apply a
    · exact continuous_const

theorem prod_X_sub_C_eq_X_pow_add_sum {δ : ℕ} (r : Fin δ → ℂ) :
    ∏ j, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C ((∏ j, (X - C (r j))).coeff i) * X ^ (i : ℕ) := by
  have hm : (∏ j, (X - C (r j)) : ℂ[X]).Monic :=
    monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have hd : (∏ j, (X - C (r j)) : ℂ[X]).natDegree = δ := by
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp
  have := hm.as_sum
  rw [hd, Finset.sum_range] at this
  exact this

theorem exists_prod_X_sub_C_eq {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ,
      ∏ j, (X - C (r j)) = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  first
  | exact @_root_.GlobalTheory.MonicRootsProduct.exists_roots
  | exact _root_.GlobalTheory.MonicRootsProduct.exists_roots
  | (apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicRootsProduct.exists_roots <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicRootsProduct.exists_roots ..)

theorem exists_measurable_roots_enumeration :
    ∀ δ : ℕ, ∃ ρ : (Fin δ → ℂ) → (Fin δ → ℂ), Measurable ρ ∧ ∀ c : Fin δ → ℂ,
      ∏ i, (Polynomial.X - Polynomial.C (ρ c i)) =
        Polynomial.X ^ δ + ∑ i : Fin δ, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) := by
  intro δ
  let e : ℂ ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable
    (fun _ => not_countable_iff.mpr (inferInstance : Uncountable ℝ)
      Complex.ofReal_injective.countable) (not_countable_iff.mpr inferInstance)
  let S : Set (Fin δ → ℂ) := {r | Monotone (e ∘ r)}
  have hS : MeasurableSet S := by
    have : S = ⋂ i, ⋂ j, ⋂ _ : i ≤ j, {r : Fin δ → ℂ | e (r i) ≤ e (r j)} := by
      ext r
      simp only [S, Set.mem_setOf_eq, Set.mem_iInter, Monotone, Function.comp]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_le ?_ ?_
    · exact e.measurable.comp (measurable_pi_apply i)
    · exact e.measurable.comp (measurable_pi_apply j)
  let V : (Fin δ → ℂ) → (Fin δ → ℂ) := fun r i => (∏ j, (X - C (r j))).coeff i
  have hV : Measurable V :=
    (continuous_pi fun i => continuous_coeff_prod_X_sub_C _ _).measurable
  haveI : StandardBorelSpace S := hS.standardBorel
  have hinj : Function.Injective fun x : S => V x := by
    rintro ⟨r, hr⟩ ⟨s, hs⟩ h
    have h1 : (∏ j, (X - C (r j)) : ℂ[X]) = ∏ j, (X - C (s j)) := by
      refine (prod_X_sub_C_eq_X_pow_add_sum r).trans
        (Eq.trans ?_ (prod_X_sub_C_eq_X_pow_add_sum s).symm)
      refine congrArg (X ^ δ + ·) (Finset.sum_congr rfl fun i _ => ?_)
      exact congrArg (fun a => C a * X ^ (i : ℕ)) (congrFun h i)
    have h2 : Finset.univ.val.map r = Finset.univ.val.map s := by
      rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map r),
        ← roots_multiset_prod_X_sub_C (Finset.univ.val.map s), Multiset.map_map,
        Multiset.map_map]
      exact congrArg roots h1
    have h3 : Finset.univ.val.map (e ∘ r) = Finset.univ.val.map (e ∘ s) := by
      rw [← Multiset.map_map, ← Multiset.map_map, h2]
    rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h3
    have h4 := List.ofFn_injective
      (h3.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hr) (List.sortedLE_ofFn_iff.mpr hs))
    ext i
    exact e.injective (congrFun h4 i)
  have hemb : MeasurableEmbedding fun x : S => V x :=
    (hV.comp measurable_subtype_coe).measurableEmbedding hinj
  obtain ⟨ρ, hρ, hρV⟩ := hemb.exists_measurable_extend (g := fun x : S => (x : Fin δ → ℂ))
    measurable_subtype_coe fun _ => inferInstance
  refine ⟨ρ, hρ, fun c => ?_⟩
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_eq c
  have hrS : r ∘ Tuple.sort (e ∘ r) ∈ S := Tuple.monotone_sort (e ∘ r)
  have hp : (∏ j, (X - C ((r ∘ Tuple.sort (e ∘ r)) j)) : ℂ[X])
      = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
    rw [← hr]
    exact Equiv.prod_comp (Tuple.sort (e ∘ r)) fun j => X - C (r j)
  have hc : V (r ∘ Tuple.sort (e ∘ r)) = c := by
    funext i
    simp only [V]
    rw [hp, coeff_add, coeff_X_pow, if_neg i.2.ne, zero_add, Polynomial.finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      exact if_neg fun h => hj (Fin.ext h.symm)
    · simp
  have : ρ c = r ∘ Tuple.sort (e ∘ r) := by
    rw [← hc]
    exact congrFun hρV ⟨_, hrS⟩
  rw [this, hp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteNormDiscreteNeZeroOfIsDedekindDomain
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem finite_normDiscrete_ne_zero_of_isDedekindDomain {S L : Type*} [CommRing S]
    [IsDedekindDomain S] [Field L] [Algebra S L] [IsFractionRing S L] (g : L) (hg : g ≠ 0) :
    {w : AddValuation L (WithTop ℤ) |
      IsNormDiscrete w ∧ (∀ s : S, 0 ≤ w (algebraMap S L s)) ∧ w g ≠ 0}.Finite := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap S L b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective S L (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hg
  have hI : Ideal.span {a * b} ≠ (⊥ : Ideal S) := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero ha0 hb0
  refine ((Ideal.finite_factors hI).image (ValPl.addv L)).subset ?_
  rintro w ⟨hw, h0, hwg⟩
  let Q : Ideal S :=
    { carrier := {b | 0 < w (algebraMap S L b)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at ha hb ⊢
        exact lt_of_lt_of_le (lt_min ha hb) (w.map_add _ _)
      zero_mem' := by simp
      smul_mem' := fun c b hb => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hb ⊢
        exact lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 c)) }
  have hz : ∀ s : S, s ∉ Q → w (algebraMap S L s) = 0 := fun s hs =>
    le_antisymm (not_lt.1 (hs : ¬ 0 < w (algebraMap S L s))) (h0 s)
  have hprime : Q.IsPrime := by
    refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : S) ∈ Q := htop ▸ Submodule.mem_top
      simp [Q] at h1
    · change 0 < w (algebraMap _ L (a * b)) at hab
      rw [map_mul, AddValuation.map_mul] at hab
      by_contra hno
      rw [not_or] at hno
      rw [hz a hno.1, hz b hno.2, add_zero] at hab
      exact lt_irrefl _ hab
  have hab : a * b ∈ Q := by
    by_contra hno
    have ha := hz a fun h => hno (Q.mul_mem_right _ h)
    have hb := hz b fun h => hno (Q.mul_mem_left _ h)
    have h := w.map_mul (algebraMap S L a / algebraMap S L b) (algebraMap S L b)
    rw [div_mul_cancel₀ _ hb1, ha, hb, add_zero] at h
    exact hwg h.symm
  have hne : Q ≠ ⊥ := fun h => mul_ne_zero ha0 hb0 (by rwa [h, Ideal.mem_bot] at hab)
  refine ⟨⟨Q, hprime, hne⟩, ?_, (ValPl.eq_addv _ w hw h0 (fun s => Iff.rfl)).symm⟩
  exact Ideal.dvd_span_singleton.mpr hab


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem finite_zeros_poles_of_trdeg_one :
    ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (t : Ω),
      (⊤ : IntermediateField F Ω).FG → Algebra.trdeg F Ω = 1 → Transcendental F t →
      ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) |
        IsNormDiscrete v ∧ IsTrivOn F v ∧ 0 ≤ v t ∧ v g ≠ 0}.Finite := by
  open scoped IntermediateField.algebraAdjoinAdjoin in
  intro F Ω _ _ _ _ t hfg htr ht g hg
  have hind : AlgebraicIndependent F (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hbasis : IsTranscendenceBasis F (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by rw [htr]; simp)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin F ({t} : Set Ω)) Ω := by
    have h := hbasis.isAlgebraic_field
    rwa [Set.range_const] at h
  have : Algebra.EssFiniteType F Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType (IntermediateField.adjoin F ({t} : Set Ω)) Ω := .of_comp F _ _
  have : FiniteDimensional (IntermediateField.adjoin F ({t} : Set Ω)) Ω :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : IsPrincipalIdealRing (Algebra.adjoin F ({t} : Set Ω)) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental F t ht).toRingEquiv.toRingHom
      (Polynomial.algEquivOfTranscendental F t ht).surjective
  have : IsDedekindDomain (integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) :=
    integralClosure.isDedekindDomain _ (IntermediateField.adjoin F ({t} : Set Ω)) Ω
  have : IsFractionRing (integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) Ω :=
    integralClosure.isFractionRing_of_finite_extension (IntermediateField.adjoin F ({t} : Set Ω)) Ω
  refine (finite_normDiscrete_ne_zero_of_isDedekindDomain
    (S := integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) g hg).subset ?_
  rintro w ⟨hw, hF, hwt, hwg⟩
  refine ⟨hw, fun b => ?_, hwg⟩
  have hA : ∀ x ∈ Algebra.adjoin F ({t} : Set Ω), x ∈ vRing w := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      exact hwt
    | algebraMap r =>
      by_cases hr : r = 0
      · rw [hr, map_zero]; exact zero_mem _
      · exact (hF r hr).ge
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hb : IsIntegral (Algebra.adjoin F ({t} : Set Ω)) (b : Ω) := b.2
  let : Algebra (Algebra.adjoin F ({t} : Set Ω)) (vRing w) :=
    ((algebraMap (Algebra.adjoin F ({t} : Set Ω)) Ω).codRestrict (vRing w)
      (fun x => hA x x.2)).toAlgebra
  have : IsScalarTower (Algebra.adjoin F ({t} : Set Ω)) (vRing w) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hb' : IsIntegral (vRing w) (b : Ω) := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
  change 0 ≤ w (b : Ω)
  rw [← hy]
  exact y.2

end GlobalTheory
end

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem finite_support_and_density_and_aemeasurable :
    (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, 1 ≤ d.D → (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → (∀ G, Module.finrank (Ω c) (𝒜 c G) = 1) → (∀ j, d.w j c ∈ 𝒜 c d.wL) → d.w (d.jc c) c ≠ 0 → ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c → (∀ g : Ω c, g ≠ 0 → {v | d.admitted c v ∧ v g ≠ 0}.Finite) ∧ ∀ (G : WT) (e : A c) (S : Finset (Ω c)), e ∈ 𝒜 c G → e ≠ 0 → (∀ v, d.admitted c v → ∀ a : Ω c, a ≠ 0 → ((d.ord c v G (a • e) : ℤ) : WithTop ℤ) = v a + (d.ord c v G e : WithTop ℤ)) → (∀ v, d.admitted c v → (∀ s ∈ S, 0 ≤ v s) → d.ord c v G e = 0) → ∀ f ∈ 𝒜 c G, f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite) ∧ (∀ (K A Ω : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra K Ω] [IsScalarTower K A Ω] (sg : K →+* ℂ) (φ : A →+* ℂ), φ.comp (algebraMap K A) = sg → ∀ (S : Finset A) (ε : ℝ), 0 < ε → ∃ P ∈ PT (Ω := Ω) sg, ∀ a ∈ S, ‖P (algebraMap A Ω a) - φ a‖ < ε) ∧ (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → (∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) → ∀ (sg : K →+* ℂ) (m : ℕ) (a : Fin m → Ω c) (Nf : (Fin m → ℂ) → ℝ) (h : (Ω c →+* ℂ) → ℝ), Measurable Nf → (∀ P ∈ PT (Ω := Ω c) sg, h P = Nf (fun i => P (a i))) → AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 => ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j), h P) d.sphMeasure) :=
  ⟨finite_support_admissible finite_vertical_gauss_valuations finite_zeros_poles_of_trdeg_one,
    generic_points_dense exists_algIndep_tuple_near,
    aemeasurable_finsum_section ae_eval₂_ne_zero_pi_toSphere
      (measurable_sum_embeddings_over_generic_point exists_measurable_roots_enumeration)
      existsUnique_ringHom_OmS⟩

end GlobalTheory
