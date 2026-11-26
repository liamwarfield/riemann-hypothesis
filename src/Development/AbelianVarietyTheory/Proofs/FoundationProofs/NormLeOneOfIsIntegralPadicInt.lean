module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CocyclesCyclotomicFinrankThree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegralPadicInt
namespace GlobalTheory.PadicIntegralNorm

theorem norm_le_one_of_isIntegral {R K : Type*} [CommRing R] [NormedField K] [IsUltrametricDist K] [Algebra R K]
    (hR : ∀ r : R, ‖algebraMap R K r‖ ≤ 1) (x : K) (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  obtain ⟨p, hpm, hpx⟩ := hx
  by_contra hlt
  rw [not_le] at hlt
  have h0 : (0 : ℝ) < ‖x‖ := zero_lt_one.trans hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hpx

  have hxn : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * x ^ i := by
    linear_combination hpx

  have hterm : ∀ i ∈ Finset.range p.natDegree,
      ‖algebraMap R K (p.coeff i) * x ^ i‖ < ‖x‖ ^ p.natDegree := by
    intro i hi
    rw [norm_mul, norm_pow]
    calc ‖algebraMap R K (p.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by gcongr; exact hR _
      _ = ‖x‖ ^ i := one_mul _
      _ < ‖x‖ ^ p.natDegree := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  rcases (Finset.range p.natDegree).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, neg_zero] at hxn
    have h1 : ‖x ^ p.natDegree‖ = 0 := by rw [hxn, norm_zero]
    rw [norm_pow] at h1
    exact (pow_pos h0 _).ne' h1
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun i => algebraMap R K (p.coeff i) * x ^ i)
    have h2 := congrArg norm hxn
    rw [norm_neg, norm_pow] at h2
    linarith [hterm i hi]

theorem norm_le_one_of_isIntegral_padicInt {l : ℕ} [inst : Fact (Nat.Prime l)] (x : Formalism.ConjugateSelfDual.Qbar l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  refine norm_le_one_of_isIntegral (R := ℤ_[l]) (fun r => ?_) x hx
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Formalism.ConjugateSelfDual.Qbar l), norm_algebraMap']
  exact PadicInt.norm_le_one r

end GlobalTheory.PadicIntegralNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoefficientRingFiniteExtensionPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoefficientRingFiniteExtensionPadic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.CoefJoin

theorem isIntegral_iff_norm_le {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (φ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : IsIntegral ℤ_[l] x ↔ ‖φ x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x)) := rfl
  rw [h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem coef_of_finite : ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (Qbar l)), FiniteDimensional ℚ_[l] E →
    ∃ c : Coef l, ∀ x : Qbar l, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1 := by
  intro l _ E hE
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E
  let f : E →ₐ[ℤ_[l]] PadicAlgCl l := E.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] E).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] E).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, ?_⟩
  intro x
  have hn := fun y : E => isIntegral_iff_norm_le (l := l) E.val y
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (hn y).1 hy⟩
  · rintro ⟨hx, hle⟩
    exact ⟨⟨x, hx⟩, (hn ⟨x, hx⟩).2 hle, rfl⟩

end GlobalTheory.CoefJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoefficientRingFiniteExtensionPadicStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientRing_finiteExtension_padic : ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (Qbar l)), FiniteDimensional ℚ_[l] E → ∃ c : Coef l, ∀ x : Qbar l, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1 := by
  first | exact @GlobalTheory.CoefJoin.coef_of_finite | exact GlobalTheory.CoefJoin.coef_of_finite | (intros; apply GlobalTheory.CoefJoin.coef_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitCharacterOfIntegralCyclotomicProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitCharacterOfIntegralCyclotomicProduct
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.LocChar.unit_of_integral :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' : G ℚ Ω → Qbar l), ContinuousOn k (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t) → ∃ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧ ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = k g := by
  intro l _ Ω _ _ c A k k' hcont hint hmul

  have heps : ∀ s : G ℚ Ω, eps l s * algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    intro s
    have h1 : algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = (((cycBar ℚ Ω l s)⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      rw [← map_inv]
      simp [cycBar, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
    rw [h1, eps]
    exact Units.mul_inv _
  have hmem : ∀ s : G ℚ Ω, algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ∈ c.O :=
    fun s => c.O.algebraMap_mem _
  let f : ↥(Dec (F := ℚ) A) → c.Oˣ := fun g =>
    Units.mkOfMulEqOne ⟨k g, (hint g g.2).1⟩
      (⟨k' g, (hint g g.2).2.1⟩ * ⟨_, hmem g⟩) (by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← mul_assoc, (hint g g.2).2.2]
        exact heps g)
  have hf : ∀ g, (((f g : c.Oˣ) : c.O) : Qbar l) = k g := fun g => rfl
  have hone : k 1 = 1 := by
    have h11 := hmul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [one_mul] at h11
    have hu : IsUnit (((f 1 : c.Oˣ) : c.O) : Qbar l) := by
      have : IsUnit ((f 1 : c.Oˣ) : c.O) := Units.isUnit _
      exact this.map c.O.val
    rw [hf, OneMemClass.coe_one] at hu
    exact hu.mul_left_cancel (by rw [mul_one]; exact h11.symm)
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_, hf⟩
  · ext
    change k _ = 1
    rw [OneMemClass.coe_one, hone]
  · intro g h
    ext
    change k _ = k _ * k _
    rw [Subgroup.coe_mul]
    exact hmul g g.2 h h.2
  · have hc : Continuous ((Dec (F := ℚ) A : Set (G ℚ Ω)).restrict k) :=
      continuousOn_iff_continuous_restrict.mp hcont
    exact hc.subtype_mk (fun g => (hint g g.2).1)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitCharacterOfIntegralCyclotomicProductStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' : G ℚ Ω → Qbar l), ContinuousOn k (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t) → ∃ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧ ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = k g := by
  first | exact @GlobalTheory.LocChar.unit_of_integral | exact GlobalTheory.LocChar.unit_of_integral | (intros; apply GlobalTheory.LocChar.unit_of_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCharacterH1FiniteLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoboundaryOfDualCoboundaries
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.V

namespace GlobalTheory.OrdLoc.Dcmp

open ReciprocityTheory.Gal (H0 H1 H2 Z2 B1 B2 ContAction charRep twDual cup20 TDual)

section Abstract

variable {n : ℕ} [NeZero n] {G : Type} [Group G] [TopologicalSpace G] {R : Type} [CommRing R] [Finite R]
  [Algebra (ZMod n) R] [TopologicalSpace R] [DiscreteTopology R]

end Abstract

private lemma span_prime_isMaximal_ratRingOfIntegers {l : ℕ} [hl : Fact l.Prime] :
    (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal := by
  have hZ : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have hc := Ideal.comap_isMaximal_of_surjective (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toRingHom
    (Rat.ringOfIntegersEquiv).surjective (K := Ideal.span {((l : ℕ) : ℤ)})
  have heq : Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toRingHom
      (Ideal.span {((l : ℕ) : ℤ)}) = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
    change Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) _ = _
    rw [← Ideal.map_symm, Ideal.map_span]
    simp
  rwa [heq] at hc

private lemma asIdeal_eq_span_of_prime_mem {l : ℕ} [Fact l.Prime] {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : w.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} :=
  (span_prime_isMaximal_ratRingOfIntegers.eq_of_le w.isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).2 hw)).symm

theorem _root_.GlobalTheory.OrdLoc.Dcmp.locDeg_rat {l : ℕ} [Fact l.Prime] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    _root_.ReciprocityTheory.Gal.locDeg v = 1 := by
  have hT : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∈ ({v} : Finset _) ↔ ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
    intro w
    rw [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact hv
    · intro hw
      exact HeightOneSpectrum.ext
        ((asIdeal_eq_span_of_prime_mem hw).trans (asIdeal_eq_span_of_prime_mem hv).symm)
  have h := _root_.ReciprocityTheory.Gal.sum_locDegree (F := ℚ) l {v} hT
  rw [Finset.sum_singleton, Module.finrank_self] at h
  exact h

variable {l : ℕ} [Fact l.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

end GlobalTheory.OrdLoc.Dcmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCharacterH1FiniteLevels
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocChar

private def repOverZMod {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M] (N : ℕ)
    [Module (ZMod N) M] (ρ : Representation O Γ M) : Representation (ZMod N) Γ M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap N
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul, Module.End.mul_apply]

theorem local_character_h1_bound : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → (∃ g, θ g ≠ 1) → (∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ∧ Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) := by
  open Formalism.GaloisCohomology IsLocalRing UpperTheory.V.Base UpperTheory.V.X in
  set_option synthInstance.maxHeartbeats 200000 in
  intro hF hT hE l _ Ω _ _ _ c A hA θ hθc hne₁ hne₂
  obtain ⟨g₁, hne₁⟩ := hne₁
  obtain ⟨g₂, hne₂⟩ := hne₂
  obtain ⟨v, hv, hlv⟩ := hA
  have hd₁ : (θ g₁ : c.O) - 1 ≠ 0 := fun h => hne₁ (Units.ext (sub_eq_zero.1 h))
  have hd₂ : ((chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ : c.Oˣ) : c.O) - 1 ≠ 0 := fun h => hne₂ (by
    have h' : chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ = 1 := Units.ext (sub_eq_zero.1 h)
    rw [map_inv, mul_inv_eq_one] at h'
    exact h'.symm)
  set d₂ := ((chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ : c.Oˣ) : c.O) - 1 with hd₂def
  have hK : Finite (LinearMap.ker (d₂ • (LinearMap.id : QO l c.O →ₗ[c.O] QO l c.O))) := by
    rw [← ((So.cardLen l c.O).2 _).1, (qoFacts l c.O).2.2.2]
    exact fun h => hd₂ (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  refine ⟨Nat.card (c.O ⧸ Ideal.span {(θ g₁ : c.O) - 1}) *
    Nat.card (LinearMap.ker (d₂ • (LinearMap.id : QO l c.O →ₗ[c.O] QO l c.O))), fun n hn => ?_⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have ha : ((l : ℕ) : c.O) ^ n ≠ 0 := pow_ne_zero _ hl0
  set a := ((l : ℕ) : c.O) ^ n with hadef
  obtain ⟨hM, ⟨r, hr, hkill⟩, htor⟩ := So.levFacts l c.O a ha (Lev a) ⟨LinearEquiv.refl c.O _⟩
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ r)) (Lev a)) := ⟨AddCommGroup.zmodModule hkill⟩
  set ρ := Formalism.GaloisCohomology.scalRep (Lev a) θ with hρ
  let ρ' : Representation (ZMod (l ^ r)) (Dec (F := ℚ) A) (Lev a) := repOverZMod (l ^ r) ρ
  have hact : ∀ (g : Dec (F := ℚ) A) (m : Lev a), ρ' g m = (θ g : c.O) • m := fun g m => rfl
  have hc : ContAction ρ' := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    obtain ⟨x, rfl⟩ := Lev.mk_surjective a m
    have h1 : Continuous fun g : Dec (F := ℚ) A => Lev.mk a ((θ g : c.O) * x) :=
      ((So.adicCont l c).1 a ha).comp (hθc.mul continuous_const)
    refine h1.congr fun g => ?_
    show Lev.mk a ((θ g : c.O) * x) = (θ g : c.O) • Lev.mk a x
    rw [← smul_eq_mul, map_smul]
  obtain ⟨f1, -, c2⟩ := So.locCard hF hT ℚ Ω l r hr v A hv (Lev a) ρ' hc
    (twDual ((cycMod ℚ Ω l r).comp (Dec (F := ℚ) A).subtype) ρ') fun g φ m => twDual_apply _ _ _ _ _
  have he := (hE ℚ Ω l r (Lev a) A ρ' v hr hv hc).1 hlv
  rw [GlobalTheory.OrdLoc.Dcmp.locDeg_rat hlv, pow_one] at he
  obtain ⟨-, ⟨e1⟩, -⟩ := So.scal c.O (ZMod (l ^ r)) _ (Lev a) ρ ρ' fun _ _ => rfl
  refine ⟨Finite.of_equiv _ e1.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e1.toEquiv, he, c2]
  refine Nat.mul_le_mul (Nat.mul_le_mul (le_trans ?_ (htor _ hd₁)) ?_) le_rfl
  · refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩)
      fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
    have := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 x.2 g₁
    rw [hact] at this
    exact (sub_smul _ _ _).trans (by rw [one_smul, this, sub_self])
  · obtain ⟨ι, hι, -, hιs⟩ := So.dualEmb l c.O a ha r (Lev a) ⟨LinearEquiv.refl c.O _⟩
    refine Nat.card_le_card_of_injective (fun x => ⟨ι x.1, ?_⟩)
      fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy))
    have hx := (Representation.mem_invariants _ _).1 x.2 g₂
    have := hιs (cycZ ℚ Ω l (g₂ : G ℚ Ω) : ℤ_[l]ˣ) ((θ g₂⁻¹ : c.Oˣ) : c.O) x.1 x.1 fun m => by
      conv_lhs => rw [← hx, twDual_apply, hact]
      rfl
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, hd₂def, sub_smul, one_smul, sub_eq_zero]
    exact this.symm

end GlobalTheory.LocChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCharacterH1FiniteLevelsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_h1_finite_levels : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → (∃ g, θ g ≠ 1) → (∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ∧ Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) := by
  first | exact @GlobalTheory.LocChar.local_character_h1_bound | exact GlobalTheory.LocChar.local_character_h1_bound | (intros; apply GlobalTheory.LocChar.local_character_h1_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeightCommutatorInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapLeOneBis
namespace GlobalTheory.AlgebraMapNormLeOne

open Polynomial

theorem norm_algebraMap_le_one (l : ℕ) [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  calc ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖
      = ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] a)‖ := by
        rw [← IsScalarTower.algebraMap_apply]
    _ = ‖algebraMap ℤ_[l] ℚ_[l] a‖ := PadicAlgCl.norm_extends l _
    _ ≤ 1 := PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral (l : ℕ) [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  let v : Valuation (PadicAlgCl l) NNReal := Valued.v
  have hle : ∀ y : PadicAlgCl l, v y ≤ 1 ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  let f : ℤ_[l] →+* v.integer := (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer
    fun a => (hle _).mpr (norm_algebraMap_le_one l a)
  let _ : Algebra ℤ_[l] v.integer := f.toAlgebra
  have : IsScalarTower ℤ_[l] v.integer (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxO : IsIntegral v.integer x := hx.tower_top
  exact (hle x).mp ((Valuation.Integers.isIntegral_iff_v_le_one (Valuation.integer.integers v)).mp hxO)

end GlobalTheory.AlgebraMapNormLeOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeightCommutatorInvariance
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

private theorem commHt_norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral ..)

theorem commHt_norm_le_one_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) (x : Qbar l) (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  commHt_norm_le_one_of_isIntegral l x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem commHt_cocycle_mulVec (V : R2 Ω l) {x : G ℚ Ω → Fin 2 → Qbar l} (hx : x ∈ Z1 (Loc.colRep V)) (s t : G ℚ Ω) :
    x (s * t) = x s + mat V s *ᵥ x t := by
  have := hx.2 s t
  simpa [Loc.colRep, Matrix.toLin'_apply] using this

theorem commHt_cocycle_commutator (V : R2 Ω l) {x : G ℚ Ω → Fin 2 → Qbar l} (hx : x ∈ Z1 (Loc.colRep V)) (a b : G ℚ Ω)
    (ha : V a = 1) (hb : V b = 1) : x (a * b * a⁻¹ * b⁻¹) = 0 := by
  have hm := commHt_cocycle_mulVec V hx
  have m1 : ∀ s, V s = 1 → mat V s = 1 := fun s hs => by simp [mat, hs]
  have h1 : x 1 = 0 := by
    have := hm 1 1
    rw [m1 1 (map_one V), Matrix.one_mulVec, mul_one] at this
    simpa using this
  have hinv : ∀ s, V s = 1 → x s⁻¹ = - x s := by
    intro s hs
    have := hm s s⁻¹
    rw [mul_inv_cancel, h1, m1 s hs, Matrix.one_mulVec] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hai : V a⁻¹ = 1 := by rw [map_inv, ha, inv_one]
  have hab : V (a * b) = 1 := by rw [map_mul, ha, hb, one_mul]
  have haba : V (a * b * a⁻¹) = 1 := by rw [map_mul, hab, hai, one_mul]
  rw [hm, m1 _ haba, Matrix.one_mulVec, hm, m1 _ hab, Matrix.one_mulVec, hm, m1 _ ha, Matrix.one_mulVec,
    hinv a ha, hinv b hb]
  abel

theorem commHt_dual1_eq_one {W : R2 Ω l} {s : G ℚ Ω} (hs : s ∈ N0g W) : dual1 W s = 1 := by
  obtain ⟨hc, hw⟩ := Subgroup.mem_inf.1 hs
  rw [MonoidHom.mem_ker] at hc hw
  have hd : dt W s = 1 := by simp [dt, hw]
  simp [dual1, Af.tw, hw, hc, hd]

theorem ht_commutator : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (c : Coef l) (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ φ ∈ H0g W, ∀ g ∈ N0g W, ∀ h ∈ N0g W, Cg n (ht W y z u (φ * (g * h * g⁻¹ * h⁻¹)) - ht W y z u φ) ((mat W φ - 1).det * (om (y h) (z g) - om (y g) (z h))) := by
  intro l _ Ω _ _ _ n c W y z u hO hy hz hu φ hφ g hg h hh
  have hk : g * h * g⁻¹ * h⁻¹ ∈ N0g W :=
    mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  set k := g * h * g⁻¹ * h⁻¹ with hkdef
  have kerW : ∀ s ∈ N0g W, W s = 1 := fun s hs => (Subgroup.mem_inf.1 hs).2
  have epsN : ∀ s ∈ N0g W, eps l s = 1 := fun s hs => by
    have := (Subgroup.mem_inf.1 hs).1
    rw [MonoidHom.mem_ker] at this
    simp [eps, this]
  have epsφ : eps l φ = 1 := by
    have := (Subgroup.mem_inf.1 hφ).1
    rw [MonoidHom.mem_ker] at this
    simp [eps, this]
  have matN : ∀ s ∈ N0g W, mat W s = 1 := fun s hs => by simp [mat, kerW s hs]
  have matD : ∀ s ∈ N0g W, mat (dual1 W) s = 1 := fun s hs => by simp [mat, commHt_dual1_eq_one hs]
  have hyk : y k = 0 := commHt_cocycle_commutator W hy g h (kerW g hg) (kerW h hh)
  have hzk : z k = 0 := commHt_cocycle_commutator (dual1 W) hz g h (commHt_dual1_eq_one hg) (commHt_dual1_eq_one hh)
  have hmat : mat W (φ * k) = mat W φ := by simp [mat, map_mul, kerW k hk]
  have hyφ : y (φ * k) = y φ := by rw [commHt_cocycle_mulVec W hy, hyk, Matrix.mulVec_zero, add_zero]
  have hzφ : z (φ * k) = z φ := by rw [commHt_cocycle_mulVec (dual1 W) hz, hzk, Matrix.mulVec_zero, add_zero]
  have hdiff : ht W y z u (φ * k) - ht W y z u φ = (mat W φ - 1).det * (u (φ * k) - u φ) := by
    simp only [ht, hmat, hyφ, hzφ]; ring
  have hkhg : k * (h * g) = g * h := by simp only [hkdef]; group

  set E : G ℚ Ω → G ℚ Ω → Qbar l := fun s t => cup W y z s t - (eps l s * u t - u (s * t) + u s) with hEdef
  have hE : ∀ s t, ‖E s t‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun s t => hu s t
  have c1 : cup W y z φ k = 0 := by simp [cup, hzk, om]
  have c2 : cup W y z k (h * g) = 0 := by simp [cup, hyk, om]
  have c3 : cup W y z g h = om (y g) (z h) := by simp [cup, matD g hg]
  have c4 : cup W y z h g = om (y h) (z g) := by simp [cup, matD h hh]
  have key : (u (φ * k) - u φ) - (om (y h) (z g) - om (y g) (z h)) =
      E φ k + E g h - E h g - E k (h * g) := by
    simp only [hEdef, c1, c2, c3, c4, hkhg, epsφ, epsN k hk, epsN g hg, epsN h hh]
    ring
  have hdet : ‖(mat W φ - 1).det‖ ≤ 1 := by
    apply commHt_norm_le_one_of_mem c
    rw [Matrix.det_fin_two]
    have he : ∀ i j, (mat W φ - 1) i j ∈ c.O := by
      intro i j
      rw [Matrix.sub_apply, Matrix.one_apply]
      split_ifs
      · exact sub_mem (hO φ i j) (one_mem _)
      · exact sub_mem (hO φ i j) (zero_mem _)
    exact sub_mem (mul_mem (he 0 0) (he 1 1)) (mul_mem (he 0 1) (he 1 0))
  have hsum : ‖E φ k + E g h - E h g - E k (h * g)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    have hs : ∀ a b : Qbar l, ‖a‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ → ‖b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ →
        ‖a - b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun a b ha hb => by
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))
    exact hs _ _ (hs _ _ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE _ _) (hE _ _))) (hE _ _)) (hE _ _)
  unfold Cg
  rw [hdiff, ← mul_sub, norm_mul, key]
  calc ‖(mat W φ - 1).det‖ * ‖E φ k + E g h - E h g - E k (h * g)‖ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ n‖ :=
        mul_le_mul hdet hsum (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.Ord2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeightCommutatorInvarianceStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_commutator_invariance : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (c : Coef l) (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ φ ∈ H0g W, ∀ g ∈ N0g W, ∀ h ∈ N0g W, Cg n (ht W y z u (φ * (g * h * g⁻¹ * h⁻¹)) - ht W y z u φ) ((mat W φ - 1).det * (om (y h) (z g) - om (y g) (z h))) := by
  first | exact @GlobalTheory.Ord2.ht_commutator | exact GlobalTheory.Ord2.ht_commutator | (intros; apply GlobalTheory.Ord2.ht_commutator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterPrimeConductorDegreePrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterPrimeConductorDegreePrimePow
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.PrimeChar

theorem normV_prime (v : Pl) : (normV v).Prime := by
  haveI := v.isPrime
  haveI := v.isMaximal
  haveI : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hp : (ringChar (𝓞 ℚ ⧸ v.asIdeal)).Prime := CharP.char_is_prime (𝓞 ℚ ⧸ v.asIdeal) _
  haveI : Fact (ringChar (𝓞 ℚ ⧸ v.asIdeal)).Prime := ⟨hp⟩
  have hs : Function.Surjective (ZMod.castHom (dvd_refl (ringChar (𝓞 ℚ ⧸ v.asIdeal))) (𝓞 ℚ ⧸ v.asIdeal)) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    exact ⟨(n : ZMod _), by simp⟩
  have hb := Nat.card_eq_of_bijective _ ⟨RingHom.injective _, hs⟩
  rw [normV, ← hb, Nat.card_zmod]
  exact hp

theorem normV_mem (v : Pl) : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h : Nat.card (𝓞 ℚ ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  change ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  rw [h]
  exact Ideal.absNorm_mem _

theorem val_normV_lt_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] {B : ValuationSubring Ω} {v : Pl}
    (h : IsPlaceOver B v) : B.valuation ((normV v : ℕ) : Ω) < 1 := by
  have := (h _).2 (normV_mem v)
  simpa using this

theorem eq_of_normV_eq {v w : Pl} (h : normV v = normV w) : v = w := by
  have hp := normV_prime w
  have hpr : Prime ((normV w : ℕ) : 𝓞 ℚ) := by
    have h1 : Prime ((normV w : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((normV w : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((normV w : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h1
  have hI : (Ideal.span {((normV w : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr)
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have hv : Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} = v.asIdeal :=
    hI.eq_of_le v.isPrime.ne_top (by rw [Ideal.span_singleton_le_iff_mem, ← h]; exact normV_mem v)
  have hw : Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} = w.asIdeal :=
    hI.eq_of_le w.isPrime.ne_top (by rw [Ideal.span_singleton_le_iff_mem]; exact normV_mem w)
  exact HeightOneSpectrum.ext (hv.symm.trans hw)

theorem exists_surj (p N : ℕ) [Fact p.Prime] (h : N ∣ p - 1) :
    ∃ f : (ZMod p)ˣ →* Multiplicative (ZMod N), Function.Surjective f := by
  have hc : IsCyclic (ZMod p)ˣ := inferInstance
  have hcard : N ∣ Nat.card (ZMod p)ˣ := by rw [Nat.card_eq_fintype_card, ZMod.card_units]; exact h
  let c : ZMod (Nat.card (ZMod p)ˣ) →+ ZMod N := (ZMod.castHom hcard (ZMod N)).toAddMonoidHom
  refine ⟨(AddMonoidHom.toMultiplicative c).comp (zmodCyclicMulEquiv hc).symm.toMonoidHom, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective hcard (Multiplicative.toAdd y)
  refine ⟨zmodCyclicMulEquiv hc (Multiplicative.ofAdd x), ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  show Multiplicative.ofAdd (c x) = y
  exact hx

theorem pow_self_eq_one (N : ℕ) (a : Multiplicative (ZMod N)) : a ^ N = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end GlobalTheory.Ord2.PrimeChar

namespace GlobalTheory.Ord2.PrimeChar

theorem exists_prime_char : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl),
    1 ≤ n → l ^ n ∣ normV w - 1 → ∃ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ ∧
      Function.Surjective ψ ∧ (∀ B : ValuationSubring Ω, IsPlaceOver B w → ∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) ∧
      ∀ v : Pl, v ≠ w → (∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w))) →
        ∀ B : ValuationSubring Ω, IsPlaceOver B v → Dec (F := ℚ) B ≤ ψ.ker := by
  intro l _ Ω _ _ _ n w _ hdiv
  have hp := normV_prime w
  haveI : Fact (normV w).Prime := ⟨hp⟩
  haveI : NeZero (normV w) := ⟨hp.ne_zero⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨f, hf⟩ := exists_surj (normV w) (l ^ n) hdiv

  have hine : ∀ B : ValuationSubring Ω, IsPlaceOver B w →
      ∃ τ ∈ Ine (F := ℚ) B, (f.comp (Chr.cls ℚ Ω (normV w)) τ).toAdd = 1 := by
    intro B hB
    have hBp := val_normV_lt_one hB
    obtain ⟨g0, hg0⟩ := hf (Multiplicative.ofAdd 1)
    have hd : normV w ^ 1 ∣ normV w := by rw [pow_one]
    obtain ⟨w0, hw0⟩ := KStar.TotallyRealRoots.redPow_surjective (l := normV w) 1 (ZMod.unitsMap hd g0)
    obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω (normV w) B hBp w0
    refine ⟨σ, hσ, ?_⟩
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    haveI : NeZero ((normV w : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
    have hX : PadicInt.toZModPow 1 (w0 : ℤ_[normV w]) = (((g0 : ZMod (normV w)).val : ℕ) : ZMod (normV w ^ 1)) := by
      have h2 := congrArg (fun u : (ZMod (normV w ^ 1))ˣ => (u : ZMod (normV w ^ 1))) hw0
      simp only [ZMod.unitsMap_val] at h2
      rw [← ZMod.cast_natCast (R := ZMod (normV w ^ 1)) hd ((g0 : ZMod (normV w)).val), ZMod.natCast_zmod_val]
      exact h2
    have hcls : Chr.cls ℚ Ω (normV w) σ = g0 := by
      refine (Chr.clsFacts ℚ Ω (normV w)).2.2.1 σ g0 fun ζ hζ => ?_
      have hζ' : ζ ^ (normV w ^ 1) = 1 := by rw [pow_one]; exact hζ
      have hspec : σ ζ = ζ ^ (PadicInt.toZModPow 1 ((cycZ ℚ Ω (normV w) σ : ℤ_[normV w]ˣ) : ℤ_[normV w])).val :=
        cyclotomicCharacter.spec (L := Ω) (normV w) (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ'
      rw [hspec, hσw, hX, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ']
    rw [MonoidHom.comp_apply, hcls, hg0, toAdd_ofAdd]
  refine ⟨f.comp (Chr.cls ℚ Ω (normV w)), fun s hs => ?_, fun y => ?_, hine, fun v hvw hx B hB => ?_⟩
  ·
    have h1 : Chr.cls ℚ Ω (normV w) s = 1 := (Chr.clsFacts ℚ Ω (normV w)).2.2.1 s 1 fun ζ hζ => by
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
      exact hs ζ hζ
    rw [MonoidHom.comp_apply, h1, map_one]
  ·
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
    obtain ⟨τ, -, hτ⟩ := hine B hB
    refine ⟨τ ^ (Multiplicative.toAdd y).val, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_pow, toAdd_pow, hτ, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  ·
    have hq := normV_prime v
    haveI : Fact (normV v).Prime := ⟨hq⟩
    have hne : normV v ≠ normV w := fun h => hvw (eq_of_normV_eq h)
    have hcop : (normV w).Coprime (normV v) := (Nat.coprime_primes hp hq).2 (Ne.symm hne)
    have hBq := val_normV_lt_one hB
    obtain ⟨x, hx⟩ := hx
    have hq0 : ((normV v : ℕ) : ZMod (normV w)) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod (normV w)) (normV w)]
      exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).1 h).symm
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hx
      exact hq0 hx.symm
    let uq : (ZMod (normV w))ˣ := ZMod.unitOfCoprime (normV v) hcop.symm
    have huq : uq = Units.mk0 x hx0 ^ (l ^ n) := by
      ext
      simp [uq, hx]
    have hfq : f uq = 1 := by rw [huq, map_pow, pow_self_eq_one]
    intro g hg
    obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω (normV v) B hBq (normV w) hcop g hg
    have hcls : Chr.cls ℚ Ω (normV w) g = uq ^ k := by
      refine (Chr.clsFacts ℚ Ω (normV w)).2.2.1 g (uq ^ k) fun ζ hζ => ?_
      rw [hk ζ hζ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast,
        ← pow_eq_pow_mod _ hζ]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hcls, map_pow, hfq, one_pow]

end GlobalTheory.Ord2.PrimeChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterPrimeConductorDegreePrimePowStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_primeConductor_degree_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl), 1 ≤ n → l ^ n ∣ normV w - 1 → ∃ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ ∧ Function.Surjective ψ ∧ (∀ B : ValuationSubring Ω, IsPlaceOver B w → ∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) ∧ ∀ v : Pl, v ≠ w → (∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w))) → ∀ B : ValuationSubring Ω, IsPlaceOver B v → Dec (F := ℚ) B ≤ ψ.ker := by
  first | exact @GlobalTheory.Ord2.PrimeChar.exists_prime_char | exact GlobalTheory.Ord2.PrimeChar.exists_prime_char | (intros; apply GlobalTheory.Ord2.PrimeChar.exists_prime_char <;> assumption)
end
end
