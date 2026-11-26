module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddValuation
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierExtractionTsumClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
namespace GlobalTheory

theorem integralClosure_finite_local_of_isAdicComplete :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
      [CharZero R], IsAdicComplete (IsLocalRing.maximalIdeal R) R →
      ∀ (L : Type) [Field L] [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [Algebra R L] [IsScalarTower R (FractionRing R) L],
        Module.Finite R (integralClosure R L) ∧ IsLocalRing (integralClosure R L) ∧
          IsNoetherianRing (integralClosure R L) ∧ IsIntegrallyClosed (integralClosure R L) ∧
          IsFractionRing (integralClosure R L) L := by
  intro R _ _ _ _ _ _ hR L _ _ _ _ _
  have : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  have : Algebra.IsSeparable (FractionRing R) L := inferInstance
  have hfin : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)
  have hfr : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing R) L
  refine ⟨hfin, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) _,
    IsNoetherianRing.of_finite R _, ?_, hfr⟩
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn L).2 inferInstance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddValuationLeIffEqIff
namespace GlobalTheory.PadicVal

theorem _root_.GlobalTheory.PadicVal.exists_addValuation_le_iff_eq_iff : ∀ (p : ℕ) [Fact p.Prime] (π : PadicAlgCl p),
    0 < ‖π‖ → ‖π‖ < 1 → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ),
      (∀ (c : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v c ↔
        ‖c‖ ≤ Real.exp (-(-Real.log ‖π‖ * r))) ∧
      ∀ (c : PadicAlgCl p) (r : ℚ), v c = (r : WithTop ℚ) ↔
        ‖c‖ = Real.exp (-(-Real.log ‖π‖ * r)) := by
  intro p _ π h0 h1
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.PadicVal.exists_addValuation π h0 h1
  refine ⟨v, fun c r => ?_, fun c r => ?_⟩
  · by_cases hc : c = 0
    · simp [hc, (Real.exp_pos _).le]
    obtain ⟨q, hvq, hlog⟩ := hv c hc
    rw [hvq, WithTop.coe_le_coe, neg_mul, neg_neg,
      ← Real.log_le_iff_le_exp (norm_pos_iff.2 hc), hlog, mul_comm (Real.log ‖π‖),
      mul_le_mul_right_of_neg hL]
    exact_mod_cast Iff.rfl
  · by_cases hc : c = 0
    · simp [hc, (Real.exp_pos _).ne]
    obtain ⟨q, hvq, hlog⟩ := hv c hc
    rw [hvq, WithTop.coe_inj, neg_mul, neg_neg]
    constructor
    · rintro rfl
      rw [mul_comm, ← hlog, Real.exp_log (norm_pos_iff.2 hc)]
    · intro h
      have h2 := congrArg Real.log h
      rw [Real.log_exp, hlog, mul_comm (Real.log ‖π‖)] at h2
      exact Rat.cast_injective (mul_right_cancel₀ hL.ne h2)

end GlobalTheory.PadicVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionTwistTsumNormGe
open Module

namespace GlobalTheory

theorem exists_torsion_twist_tsum_norm_ge :
    ∀ (K X : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : K), 0 < N → ‖(N : K)‖ = 1 → IsPrimitiveRoot ζ N → ∀ (σ : X → K) (q : X → ℝ) (r : ℝ), 0 < r → r < 1 → Filter.Tendsto q Filter.cofinite Filter.atTop → (∀ z, ‖σ z‖ ≤ r ^ q z) → ∀ z₀ : X, ‖σ z₀‖ = r ^ q z₀ → (∀ μ, μ ≠ 0 → q z₀ < q (z₀ + N • μ)) → ∃ t : Multiplicative X →* Kˣ, t ^ N = 1 ∧ r ^ q z₀ ≤ ‖∑' z, σ z * (t (Multiplicative.ofAdd z) : K)‖ := by
  classical
  intro K X _ _ _ _ _ _ N ζ hN hN1 hζ σ q r hr0 hr1 hq hσ z₀ hz₀ hlead
  have hσ0 : Filter.Tendsto σ Filter.cofinite (nhds 0) :=
    squeeze_zero_norm hσ ((tendsto_rpow_atTop_of_base_lt_one r (by linarith) hr1).comp hq)
  obtain ⟨hfin, hsum, hnorm⟩ :=
    fourier_extraction_tsum_class K X N ζ hN hN1 hζ σ hσ0 z₀
  have hclass : ‖∑' μ, σ (z₀ + N • μ)‖ = r ^ q z₀ := by
    rw [← hz₀]
    refine hnorm fun μ hμ => (hσ _).trans_lt ?_
    rw [hz₀]
    exact Real.rpow_lt_rpow_of_exponent_gt hr0 hr1 (hlead μ hμ)
  have hone : ∀ (t : {t : Multiplicative X →* Kˣ // t ^ N = 1}) (x : Multiplicative X),
      ‖(t.1 x : K)‖ = 1 := by
    intro t x
    have h1 : ‖(t.1 x : K)‖ ^ N = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, TorsionFourier.apply_pow_eq_one t.2,
        Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1
  haveI := Fintype.ofFinite {t : Multiplicative X →* Kˣ // t ^ N = 1}
  rw [finsum_eq_sum_of_fintype] at hsum
  obtain ⟨t, -, ht⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (t := (Finset.univ : Finset {t : Multiplicative X →* Kˣ // t ^ N = 1}))
    ⟨⟨1, one_pow N⟩, Finset.mem_univ _⟩
    (fun t => (((t.1 (Multiplicative.ofAdd z₀))⁻¹ : Kˣ) : K) *
      ∑' β, σ β * (t.1 (Multiplicative.ofAdd β) : K))
  refine ⟨t.1, t.2, ?_⟩
  rw [hsum, norm_mul, norm_pow, hN1, one_pow, one_mul, hclass, norm_mul,
    Units.val_inv_eq_inv_val, norm_inv, hone, inv_one, one_mul] at ht
  exact ht

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDiscreteValuationRingOfMemClosureC
open scoped BigOperators
open IsLocalRing

namespace GlobalTheory

theorem coeff_aeval_C_mul_X {K A J : Type*} [CommRing K] [CommRing A] [Algebra K A] (w : J → A)
    (G : MvPolynomial J K) (d : ℕ) :
    (MvPolynomial.aeval (fun j => Polynomial.C (w j) * Polynomial.X) G).coeff d =
      MvPolynomial.aeval w (MvPolynomial.homogeneousComponent d G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : MvPolynomial.aeval (fun j => Polynomial.C (w j) * Polynomial.X)
        (MvPolynomial.monomial u a) =
        Polynomial.C (MvPolynomial.aeval w (MvPolynomial.monomial u a)) *
          Polynomial.X ^ u.degree := by
      simp only [MvPolynomial.aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply,
        mul_assoc]
      rfl
    rw [h, Polynomial.coeff_C_mul_X_pow, MvPolynomial.homogeneousComponent_of_mem
      (MvPolynomial.isHomogeneous_monomial a (rfl : u.degree = u.degree))]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem exists_complete_discreteValuationRing_of_mem_closure_cone :
    ∀ (K A J : Type) [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Fintype J], Algebra.FiniteType K A → ∀ (w : J → A) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J K) (d : ℕ), G.IsHomogeneous d → MvPolynomial.aeval w G = 0 → MvPolynomial.eval v G = 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A →ₐ[K] FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro K A J _ _ _ _ _ hA w v hv hG
  let L := FractionRing (Polynomial A)
  have hinj : Function.Injective (algebraMap (Polynomial A) L) := IsFractionRing.injective _ _
  have : Algebra.EssFiniteType (Polynomial A) L := .of_isLocalization L (nonZeroDivisors _)
  have : Algebra.FiniteType K (Polynomial A) := .trans hA inferInstance
  have : Algebra.EssFiniteType K L := .comp K (Polynomial A) L
  let ψ : MvPolynomial J K →ₐ[K] Polynomial A :=
    MvPolynomial.aeval fun j => Polynomial.C (w j) * Polynomial.X
  let Φ : MvPolynomial J K →+* L := (algebraMap (Polynomial A) L).comp ψ.toRingHom
  have hker : RingHom.ker Φ ≤ RingHom.ker (MvPolynomial.eval v) := by
    intro G h
    have h1 : ψ G = 0 := hinj (h.trans (map_zero _).symm)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent G, map_sum]
    refine Finset.sum_eq_zero fun d _ => hG _ d (MvPolynomial.homogeneousComponent_isHomogeneous d G) ?_
    rw [← coeff_aeval_C_mul_X]
    change (ψ G).coeff d = 0
    rw [h1, Polynomial.coeff_zero]
  have hne : (RingHom.ker (MvPolynomial.eval v)).map Φ.rangeRestrict ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, Ideal.mem_map_iff_of_surjective _ Φ.rangeRestrict_surjective]
    rintro ⟨G, h1, h2⟩
    have h3 : G - 1 ∈ RingHom.ker Φ := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_one, sub_eq_zero]
      exact congrArg Subtype.val h2
    have h4 := hker h3
    rw [RingHom.mem_ker] at h1 h4
    simp [h1] at h4
  obtain ⟨U, hU, hU'⟩ := Ideal.image_subset_nonunits_valuationSubring (A := Φ.range) _ hne
  have hC : ∀ r : K, Φ (MvPolynomial.C r) = algebraMap K L r := fun r => by
    rw [IsScalarTower.algebraMap_apply K (Polynomial A) L, ← ψ.commutes]
    rfl
  let t : J → L := fun j => Φ (MvPolynomial.X j - MvPolynomial.C (v j))
  have ht : ∀ j, t j = algebraMap (Polynomial A) L
      (Polynomial.C (w j) * Polynomial.X - Polynomial.C (algebraMap K A (v j))) := fun j => by
    simp [t, Φ, ψ]
  obtain ⟨V, hV, hKV, -, htV⟩ := exists_discreteValuationSubring_of_valuationSubring (R := K) U
    (fun r => hU ⟨_, hC r⟩) Set.finite_empty (Set.finite_range t) (by simp)
    (by
      rintro _ ⟨j, rfl⟩
      exact hU' ⟨_, Ideal.mem_map_of_mem _
        (show MvPolynomial.X j - MvPolynomial.C (v j) ∈ _ by simp [RingHom.mem_ker]), rfl⟩)
    (by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
      refine ⟨_, ⟨j, rfl⟩, fun h => hj ?_⟩
      rw [ht, map_eq_zero_iff _ hinj] at h
      simpa using congrArg (fun p : Polynomial A => p.coeff 0) h)
  let W := AdicCompletion (maximalIdeal V) V
  let κ : K →+* V := (algebraMap K L).codRestrict V hKV
  let ι : V →+* W := algebraMap V W
  letI : Algebra K W := (ι.comp κ).toAlgebra
  have hι : Function.Injective ((algebraMap W (FractionRing W)).comp ι) :=
    (IsFractionRing.injective W _).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let g : L →+* FractionRing W := IsFractionRing.lift hι
  have hg : ∀ x : V, g x = algebraMap W (FractionRing W) (ι x) := fun x =>
    IsFractionRing.lift_algebraMap hι x
  let f : A →ₐ[K] FractionRing W :=
    { g.comp ((algebraMap (Polynomial A) L).comp Polynomial.C) with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply K W (FractionRing W)]
        exact hg (κ r) }
  have htm : ∀ j, t j ∈ V := fun j => V.nonunits_subset (htV _ ⟨j, rfl⟩)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, f,
    g (algebraMap (Polynomial A) L Polynomial.X), fun j => ι (⟨t j, htm j⟩ + κ (v j)),
    inferInstance, ?_, fun j => ⟨?_, ?_⟩⟩
  · rw [map_ne_zero, map_ne_zero_iff _ hinj]
    exact Polynomial.X_ne_zero
  · rw [← hg]
    change g (t j + algebraMap (Polynomial A) L (Polynomial.C (algebraMap K A (v j)))) =
      _ * g (algebraMap (Polynomial A) L (Polynomial.C (w j)))
    rw [ht, ← map_add (f := _), sub_add_cancel, mul_comm, map_mul, map_mul]
  · change ι _ - ι (κ (v j)) ∈ _
    rw [← map_sub, add_sub_cancel_right]
    exact map_nonunit ι _
      ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨t j, htm j⟩)).mp (htV _ ⟨j, rfl⟩))

end GlobalTheory
end
