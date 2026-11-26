module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Kw
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RayPrimeSpan
theorem UpperTheory.Reformulated.B.Qi16.rayPrime_span :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ),
    Nat.Prime p →
      (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → v.asIdeal = Ideal.span {(↑p : NumberField.RingOfIntegers ℚ)} := by
  intro v p hp hmem
  have hprime : Prime (p : NumberField.RingOfIntegers ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv]
    rw [map_natCast]
    exact Nat.prime_iff_prime_int.mp hp
  have hP : (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hne : Ideal.span {(p : NumberField.RingOfIntegers ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hprime.ne_zero
  have hmax : (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}).IsMaximal :=
    hP.isMaximal hne
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsPrimeMemOfMem
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.BauerFixIff
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Cheb
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.cheb :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (σ : Gal(L/K)) (T : Set (HeightOneSpectrum (𝓞 K))), T.Finite → ∃ v ∉ T, ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal ∧ w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ IsArithFrobAt (𝓞 K) σ w.asIdeal := by
  intro K L _ _ _ _ _ _ σ T hT
  classical
  let C : Set Gal(L/K) := {τ | IsConj σ τ}
  have hCc : ∀ a ∈ C, ∀ τ : Gal(L/K), τ * a * τ⁻¹ ∈ C := by
    intro a ha τ
    exact IsConj.trans ha (isConj_iff.mpr ⟨τ, rfl⟩)
  have hD := GroundTheory.Global.hasDirichletDensity_setOf_exists_arithFrobAt_mem (K := K) (L := L) C hCc
  have hpos : (0 : ℝ) < (Nat.card C : ℝ) / Nat.card Gal(L/K) := by
    have : Nonempty C := ⟨⟨σ, IsConj.refl σ⟩⟩
    apply div_pos
    · exact_mod_cast Nat.card_pos
    · exact_mod_cast Nat.card_pos
  have key : ∀ S : Set (HeightOneSpectrum (𝓞 K)),
      Set.HasDirichletDensity S ((Nat.card C : ℝ) / Nat.card Gal(L/K)) → (S \ T).Nonempty := by
    intro S hS
    refine Set.Infinite.nonempty (Set.Infinite.diff ?_ hT)
    intro hfin
    have h0 := GroundTheory.Global.hasDirichletDensity_zero_of_finite hfin
    exact hpos.ne' (hS.dirichletDensity_eq.symm.trans h0.dirichletDensity_eq)
  obtain ⟨v, ⟨hram, w, hwv, hfw⟩, hvT⟩ := key _ hD
  obtain ⟨c, hc⟩ := isConj_iff.mp hfw
  have hne : c⁻¹ • w.asIdeal ≠ ⊥ := by
    intro h
    apply w.ne_bot
    have := congrArg (fun I : Ideal (𝓞 L) => c • I) h
    simpa using this
  let w' : HeightOneSpectrum (𝓞 L) := ⟨c⁻¹ • w.asIdeal, Ideal.IsPrime.smul c⁻¹, hne⟩
  have hw'v : w'.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.smul c⁻¹
  refine ⟨v, hvT, w', hw'v, (hram w' hw'v), ?_⟩
  have hF := (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal).conj c⁻¹
  rw [← hc] at hF
  have e : c⁻¹ * (c * σ * c⁻¹) * c⁻¹⁻¹ = σ := by group
  rw [e] at hF
  exact hF
end

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem UpperTheory.V.CF.bauer_fix_iff (K M N : Type) [Field K] [NumberField K] [Field M] [NumberField M]
    [Field N] [NumberField N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N]
    [IsGalois K N] (P : Ideal (𝓞 N)) [P.IsPrime] (hP : P ≠ ⊥) :
    (∀ σ : N ≃ₐ[K] N, σ • P = P → ∀ x : M, σ (algebraMap M N x) = algebraMap M N x) ↔
      (P.under (𝓞 M)).ramificationIdx (𝓞 K) * (P.under (𝓞 M)).inertiaDeg (𝓞 K) = 1 := by
  haveI : IsGalois M N := IsGalois.tower_top_of_isGalois K M N
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  have h1 := Ideal.card_stabilizer_eq (G := N ≃ₐ[K] N) (P.under (𝓞 K)) P
  have h2 := Ideal.card_stabilizer_eq (G := N ≃ₐ[M] N) (P.under (𝓞 M)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (N ≃ₐ[K] N),
    Ideal.inertiaDegIn_eq_inertiaDeg _ P (N ≃ₐ[K] N),
    Ideal.ramificationIdx_tower (P.under (𝓞 M)) P, Ideal.inertiaDeg_tower (P.under (𝓞 M)) P] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (N ≃ₐ[M] N),
    Ideal.inertiaDegIn_eq_inertiaDeg _ P (N ≃ₐ[M] N)] at h2
  have h3 : Nat.card (MulAction.stabilizer (N ≃ₐ[K] N) P) =
      ((P.under (𝓞 M)).ramificationIdx (𝓞 K) * (P.under (𝓞 M)).inertiaDeg (𝓞 K)) *
        Nat.card (MulAction.stabilizer (N ≃ₐ[M] N) P) := by
    rw [h1, h2]; ring
  let j : MulAction.stabilizer (N ≃ₐ[M] N) P → MulAction.stabilizer (N ≃ₐ[K] N) P :=
    fun σ => ⟨σ.1.restrictScalars K, σ.2⟩
  have hj : Function.Injective j := by
    intro a b e
    apply Subtype.ext
    exact AlgEquiv.restrictScalars_injective K (congrArg Subtype.val e)
  have hpos : 0 < Nat.card (MulAction.stabilizer (N ≃ₐ[M] N) P) := Nat.card_pos
  constructor
  · intro h
    have hs : Function.Surjective j := by
      rintro ⟨σ, hσ⟩
      exact ⟨⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (h σ hσ), hσ⟩, rfl⟩
    have := Nat.card_eq_of_bijective j ⟨hj, hs⟩
    rw [h3] at this
    exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← this, one_mul])).symm
  · intro h σ hσ x
    rw [h, one_mul] at h3
    have hb := (Nat.bijective_iff_injective_and_card j).2 ⟨hj, h3.symm⟩
    obtain ⟨τ, hτ⟩ := hb.2 ⟨σ, hσ⟩
    have : σ = τ.1.restrictScalars K := (congrArg Subtype.val hτ).symm
    rw [this]
    exact τ.1.commutes x

private theorem UpperTheory.V.CF.bauer_fix (K A C N : Type) [Field K] [NumberField K] [Field A] [NumberField A]
    [Field C] [NumberField C] [Field N] [NumberField N] [Algebra K A] [Algebra K C] [Algebra K N]
    [Algebra A N] [Algebra C N] [IsScalarTower K A N] [IsScalarTower K C N] [IsGalois K C] [IsGalois K N]
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite)
    (h : ∀ v ∉ T, GroundTheory.Global.SplitsCompletely C v → GroundTheory.Global.SplitsCompletely A v)
    (σ : Gal(N/K)) (hσ : ∀ x : C, σ (algebraMap C N x) = algebraMap C N x) (x : A) :
    σ (algebraMap A N x) = algebraMap A N x := by
  obtain ⟨v, hv, w, hw, he, hF⟩ := cheb K N σ T hT
  haveI := w.isPrime
  haveI := v.isPrime
  have hst := GroundTheory.Global.stabilizer_eq_zpowers_arithFrobAt v w he
  have hσF : σ = arithFrobAt (𝓞 K) Gal(N/K) w.asIdeal := by
    haveI : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := (Ideal.ramificationIdx_eq_one_iff ..).1 he
    have h1 := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hF
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(N/K) w.asIdeal) (Ideal.primeCompl_le_nonZeroDivisors _)
    refine AlgEquiv.ext fun y => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 N) y
    have h2 : ∀ a : 𝓞 N, σ (algebraMap (𝓞 N) N a) =
        (arithFrobAt (𝓞 K) Gal(N/K) w.asIdeal) (algebraMap (𝓞 N) N a) := fun a =>
      congrArg (algebraMap (𝓞 N) N) (DFunLike.congr_fun h1 a)
    rw [map_div₀, map_div₀, h2, h2]
  rw [← hσF] at hst
  have hC : (w.asIdeal.under (𝓞 C)).ramificationIdx (𝓞 K) * (w.asIdeal.under (𝓞 C)).inertiaDeg (𝓞 K) = 1 := by
    refine (bauer_fix_iff K C N w.asIdeal w.ne_bot).1 fun τ hτ y => ?_
    have hτ' : τ ∈ Subgroup.zpowers σ := hst ▸ (MulAction.mem_stabilizer_iff.2 hτ)
    have : Subgroup.zpowers σ ≤ MulAction.stabilizer Gal(N/K) (algebraMap C N y) :=
      Subgroup.zpowers_le.2 (hσ y)
    exact this hτ'
  have hsC : GroundTheory.Global.SplitsCompletely C v := by
    intro u hu
    haveI := u.isPrime
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal _ Gal(C/K),
      ← Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal _ Gal(C/K)] at hC ⊢
    exact mul_eq_one.1 hC
  have hA := h v hv hsC (w.under (𝓞 A)) (inferInstanceAs ((w.asIdeal.under (𝓞 A)).LiesOver v.asIdeal))
  refine (bauer_fix_iff K A N w.asIdeal w.ne_bot).2 ?_ σ hF.mem_stabilizer x
  exact mul_eq_one.2 hA

theorem UpperTheory.V.CF.bauer :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (A C : IntermediateField K Ω) [NumberField A] [NumberField C] [IsGalois K A] [IsGalois K C] (T : Set (HeightOneSpectrum (𝓞 K))), T.Finite → (∀ v ∉ T, GroundTheory.Global.SplitsCompletely C v → GroundTheory.Global.SplitsCompletely A v) → A ≤ C := by
  intro K Ω _ _ _ _ A C _ _ _ _ T hT h
  let N : IntermediateField K Ω := A ⊔ C
  haveI : NumberField N := NumberField.of_module_finite K N
  haveI : IsGalois K N := { to_isSeparable := inferInstance, to_normal := IntermediateField.normal_sup K Ω A C }
  letI : Algebra A N := (IntermediateField.inclusion (le_sup_left : A ≤ N)).toRingHom.toAlgebra
  letI : Algebra C N := (IntermediateField.inclusion (le_sup_right : C ≤ N)).toRingHom.toAlgebra
  haveI : IsScalarTower K A N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K C N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois C N := IsGalois.tower_top_of_isGalois K C N
  intro x hx
  have : algebraMap A N ⟨x, hx⟩ ∈ (⊥ : IntermediateField C N) := by
    rw [IsGalois.mem_bot_iff_fixed]
    intro τ
    exact bauer_fix K A C N T hT h (τ.restrictScalars K) τ.commutes ⟨x, hx⟩
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 this
  have : (y : Ω) = x := congrArg Subtype.val hy
  exact this ▸ y.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.SplitCyc
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.splitCyc :
    ∀ (N : ℕ) [NeZero N] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C] (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ), p.Prime → (p : 𝓞 ℚ) ∈ v.asIdeal → ¬ p ∣ N → GroundTheory.Global.SplitsCompletely C v → p ≡ 1 [MOD N] := by
  intro N _ C _ _ _ v p hp hpv hpN hspl
  haveI := Fact.mk hp
  haveI := v.isMaximal
  have hspan : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hvZ : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    refine (hspan.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap, map_natCast]
    exact hpv
  haveI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hvZ.symm⟩
  have hsurj : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := fun y => ⟨Rat.ringOfIntegersEquiv y, by
    have h : (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) :=
      Subsingleton.elim _ _
    rw [← h]
    exact Rat.ringOfIntegersEquiv.symm_apply_apply y⟩
  have hv1 : v.asIdeal.inertiaDeg ℤ = 1 := by
    letI := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
    letI := Ideal.Quotient.field v.asIdeal
    rw [Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {(p : ℤ)}) v.asIdeal,
      finrank_eq_one_iff_of_nonzero (1 : 𝓞 ℚ ⧸ v.asIdeal) one_ne_zero, eq_top_iff]
    rintro y -
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := hsurj y
    rw [Submodule.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Algebra.smul_def, mul_one]
    rfl
  obtain ⟨⟨P, hPp, hPl⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 C)
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hs := hspl ⟨P, hPp, hPne⟩ hPl
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  have ht := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal P
  rw [hv1, one_mul, hs.2, IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p C P hpN] at ht
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  exact orderOf_eq_one_iff.mp ht
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.RayPrime
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem rayPrime_span (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) (hp : p.Prime)
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
  _root_.UpperTheory.Reformulated.B.Qi16.rayPrime_span v p hp hv

theorem UpperTheory.V.CF.rayPrime :
    ∀ (𝔪 : GroundTheory.Global.Modulus ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ), p.Prime → (p : 𝓞 ℚ) ∈ v.asIdeal → p ≡ 1 [MOD Ideal.absNorm 𝔪.ideal] → ∃ hv : ¬ v.asIdeal ∣ 𝔪.ideal, 𝔪.primeClass hv = 1 := by
  intro 𝔪 v p hp hpv hmod
  have hm : (p : 𝓞 ℚ) - 1 ∈ 𝔪.ideal := by
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hp.one_le).1 hmod.symm
    have : (p : 𝓞 ℚ) - 1 = (Ideal.absNorm 𝔪.ideal : 𝓞 ℚ) * c := by
      rw [← Nat.cast_mul, ← hc, Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hv : ¬ v.asIdeal ∣ 𝔪.ideal := by
    intro h
    have h1 := (Ideal.dvd_iff_le.1 h) hm
    have h2 := v.asIdeal.sub_mem hpv h1
    rw [sub_sub_cancel] at h2
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  refine ⟨hv, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  unfold GroundTheory.Global.Modulus.primeClass
  rw [QuotientGroup.eq_one_iff, GroundTheory.Global.Modulus.mem_principalRay]
  refine ⟨Units.mk0 (p : ℚ) hp0, 𝔪.mem_rayUnits.2 ⟨fun w hw => ?_, fun w _ => ?_⟩, ?_⟩
  · have e : ((Units.mk0 (p : ℚ) hp0 : ℚˣ) : ℚ) - 1 = algebraMap (𝓞 ℚ) ℚ ((p : 𝓞 ℚ) - 1) := by simp
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact Ideal.dvd_iff_le.1 (𝔪.asIdeal_pow_exponent_dvd w) hm
  · simpa using hp.pos
  · apply Units.ext
    rw [coe_toPrincipalIdeal]
    change _ = ((v.asIdeal : Ideal (𝓞 ℚ)) : FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ)
    rw [rayPrime_span v p hp hpv, FractionalIdeal.coeIdeal_span_singleton]
    simp
end

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem exists_prime_mem_of_mem {R : Type} [CommRing R] (I : Ideal R) (hI : I.IsPrime) :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ I → ∃ p : ℕ, p.Prime ∧ (p : R) ∈ I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one I).mpr (by simpa using hmem)) hI.ne_top
    · have hp := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      rw [hm, Nat.cast_mul] at hmem
      rcases hI.mem_or_mem hmem with h | h
      · exact ⟨_, hp, h⟩
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hm
          exact hn hm
        have hlt : m < n := by
          conv_rhs => rw [hm]
          exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt
        exact ih m hlt hm0 h

private theorem cyc_adjoin (K : Type) {L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} [NeZero n] {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} K K⟮ζ⟯ := by
  change IsCyclotomicExtension {n} K (IntermediateField.adjoin K {ζ}).toSubalgebra
  have hi : IsIntegral K ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), ?_⟩
    simp [hζ.pow_eq_one]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension K

theorem UpperTheory.V.CF.kwRay :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (𝔪 : GroundTheory.Global.Modulus ℚ) (ζ : Ω), IsPrimitiveRoot ζ (Ideal.absNorm 𝔪.ideal) → 𝔪.rayClassField Ω ≤ ℚ⟮ζ⟯ := by
  intro Ω _ _ _ 𝔪 ζ hζ
  set N := Ideal.absNorm 𝔪.ideal with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]
    exact 𝔪.ideal_ne_bot
  haveI : NeZero N := ⟨hN0⟩
  have hcyc := cyc_adjoin ℚ hζ
  haveI : NumberField ℚ⟮ζ⟯ := @IsCyclotomicExtension.numberField {N} ℚ ℚ⟮ζ⟯ _ _ _ _ _ hcyc
  have hgal := @IsCyclotomicExtension.isGalois {N} ℚ ℚ⟮ζ⟯ _ _ _ hcyc
  haveI := (GroundTheory.Global.Modulus.isAbelianGalois_rayClassField 𝔪 Ω).toIsGalois
  have hfin : ({v | v.asIdeal ∣ 𝔪.ideal} ∪ {v | v.asIdeal ∣ Ideal.span {(N : 𝓞 ℚ)}} :
      Set (HeightOneSpectrum (𝓞 ℚ))).Finite := by
    refine (Ideal.finite_factors 𝔪.ideal_ne_bot).union (Ideal.finite_factors ?_)
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  refine @UpperTheory.V.CF.bauer ℚ Ω _ _ _ _ (𝔪.rayClassField Ω) ℚ⟮ζ⟯ _ _ _
    (by convert hgal) _ hfin ?_
  intro v hv hsplit
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hv
  obtain ⟨_, hv2⟩ := hv
  rw [Ideal.dvd_span_singleton] at hv2
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_of_mem v.asIdeal v.isPrime
    (Ideal.absNorm v.asIdeal) (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    (Ideal.absNorm_mem _)
  have hpN : ¬ p ∣ N := by
    rintro ⟨k, hk⟩
    apply hv2
    rw [hk, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hpv
  have hmod : p ≡ 1 [MOD N] := by
    haveI hc2 : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := by
      convert hcyc
      all_goals first
        | rfl
        | exact Subsingleton.elim _ _
    refine UpperTheory.V.CF.splitCyc N ℚ⟮ζ⟯ v p hp hpv hpN ?_
    convert hsplit
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
  obtain ⟨hv', hcls⟩ := UpperTheory.V.CF.rayPrime 𝔪 v p hp hpv hmod
  exact (GroundTheory.Global.Modulus.splitsCompletely_rayClassField_iff 𝔪 Ω hv').mpr hcls
end

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.kw :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (L : IntermediateField ℚ Ω) [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L], ∃ (N : ℕ) (ζ : Ω), 0 < N ∧ IsPrimitiveRoot ζ N ∧ L ≤ ℚ⟮ζ⟯ := by
  intro Ω _ _ _ L hfd hab
  obtain ⟨m, hm⟩ := GroundTheory.Global.exists_le_rayClassField Ω L
  have hn : Ideal.absNorm m.ideal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact m.ideal_ne_bot
  haveI : NeZero ((Ideal.absNorm m.ideal : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (Ideal.absNorm m.ideal)
  exact ⟨_, ζ, Nat.pos_of_ne_zero hn, hζ, hm.trans (kwRay Ω m ζ hζ)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.kwAbs :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Subgroup (G ℚ Ω)), IsOpen (V : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ V → ∃ N : ℕ, 0 < N ∧ ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ) → g ∈ V := by
  intro Ω _ alg hc V hV hcomm
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : alg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hcl : IsClosed (V : Set (Ω ≃ₐ[ℚ] Ω)) := Subgroup.isClosed_of_isOpen V hV
  set L : IntermediateField ℚ Ω := IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[ℚ] Ω)) with hL
  have hfix : L.fixingSubgroup = V := InfiniteGalois.fixingSubgroup_fixedField ⟨V, hcl⟩
  have hnorm : V.Normal := ⟨fun n hn g => by
    have h : g * n * g⁻¹ * n⁻¹ ∈ V :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have := mul_mem h hn
    rwa [inv_mul_cancel_right] at this⟩
  haveI hfin : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hfix]; exact hV)
  haveI hgal : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hfix]; exact hnorm)
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker = V :=
    (@IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ L hgal.to_normal).trans hfix
  haveI hab : IsAbelianGalois ℚ L :=
    { is_comm := ⟨fun a b => by
        obtain ⟨a, rfl⟩ := hsurj a
        obtain ⟨b, rfl⟩ := hsurj b
        have h : a * b * a⁻¹ * b⁻¹ ∈ V :=
          hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
        rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
          mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
        exact h⟩ }
  obtain ⟨N, ζ, hN, hζ, hle⟩ := UpperTheory.V.CF.kw Ω L
  refine ⟨N, hN, fun g hg => ?_⟩
  rw [← hfix]
  refine IntermediateField.fixingSubgroup_le hle ?_
  have h1 : ℚ⟮ζ⟯ ≤ IntermediateField.fixedField (Subgroup.zpowers (g : Ω ≃ₐ[ℚ] Ω)) := by
    rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers (g : Ω ≃ₐ[ℚ] Ω) ≤ MulAction.stabilizer _ ζ :=
      Subgroup.zpowers_le.2 (hg ζ hζ.pow_eq_one)
    exact this hf
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (h1 hx) g (Subgroup.mem_zpowers g)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwHom
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.kwHom :
    ∀ (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L], ∃ N : ℕ, 0 < N ∧ Nonempty (L →ₐ[ℚ] CyclotomicField N ℚ) := by
  intro L _ _ _
  let f : L →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : L ≃ₐ[ℚ] f.fieldRange := AlgEquiv.ofInjectiveField f
  haveI : IsAbelianGalois ℚ f.fieldRange := IsAbelianGalois.of_algHom e.symm.toAlgHom
  haveI : FiniteDimensional ℚ f.fieldRange := e.toLinearEquiv.finiteDimensional
  obtain ⟨N, ζ, hN, hζ, hle⟩ := UpperTheory.V.CF.kw (AlgebraicClosure ℚ) f.fieldRange
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI hNQ : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI hC : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    @CyclotomicField.isCyclotomicExtension N _ ℚ _ hNQ
  refine ⟨N, hN, ⟨?_⟩⟩
  exact ((IsCyclotomicExtension.algEquiv {N} ℚ ℚ⟮ζ⟯ (CyclotomicField N ℚ)).toAlgHom.comp
    (IntermediateField.inclusion hle)).comp e.toAlgHom
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneFixQ
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneMap
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineMap :
    ∀ (k K H : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field H] [NumberField H] [Algebra k K] [Algebra K H] [Algebra k H] [IsScalarTower k K H] [IsGalois k K] [IsGalois k H] (w : HeightOneSpectrum (𝓞 H)), (w.asIdeal.inertia Gal(H/k)).map (resTo k K H) = (w.asIdeal.under (𝓞 K)).inertia Gal(K/k) := by
  intro k K H _ _ _ _ _ _ _ _ _ _ _ _ w
  haveI : IsGalois K H := IsGalois.tower_top_of_isGalois k K H
  have comm : ∀ (σ : Gal(H/k)) (x : 𝓞 K),
      algebraMap (𝓞 K) (𝓞 H) (resTo k K H σ • x) = σ • algebraMap (𝓞 K) (𝓞 H) x := by
    intro σ x
    apply FaithfulSMul.algebraMap_injective (𝓞 H) H
    have e1 : algebraMap (𝓞 H) H (σ • algebraMap (𝓞 K) (𝓞 H) x) =
        σ • algebraMap (𝓞 H) H (algebraMap (𝓞 K) (𝓞 H) x) := algebraMap.smul' _ _ _
    have e2 : algebraMap (𝓞 K) K (resTo k K H σ • x) = resTo k K H σ • algebraMap (𝓞 K) K x :=
      algebraMap.smul' _ _ _
    rw [e1, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) K H, IsScalarTower.algebraMap_apply (𝓞 K) K H, e2]
    exact AlgEquiv.restrictNormal_commutes σ K _
  have comm2 : ∀ (τ : Gal(H/K)) (y : 𝓞 H), (τ.restrictScalars k) • y = τ • y := by
    intro τ y
    apply FaithfulSMul.algebraMap_injective (𝓞 H) H
    have e1 : algebraMap (𝓞 H) H ((τ.restrictScalars k) • y) =
        (τ.restrictScalars k) • algebraMap (𝓞 H) H y := algebraMap.smul' _ _ _
    have e2 : algebraMap (𝓞 H) H (τ • y) = τ • algebraMap (𝓞 H) H y := algebraMap.smul' _ _ _
    rw [e1, e2]
    rfl
  set P := w.asIdeal with hP
  set Q := P.under (𝓞 K) with hQ
  set p := P.under (𝓞 k) with hp
  haveI : Nonempty (Q.primesOver (𝓞 H)) := ⟨⟨P, inferInstance, inferInstance⟩⟩
  have hle : (P.inertia Gal(H/k)).map (resTo k K H) ≤ Q.inertia Gal(K/k) := by
    rintro _ ⟨σ, hσ, rfl⟩
    intro x
    have h1 := hσ (algebraMap (𝓞 K) (𝓞 H) x)
    show _ ∈ Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) P
    rw [Ideal.mem_comap, map_sub, comm]
    exact h1
  apply Subgroup.eq_of_le_of_card_ge hle
  have cG : Nat.card (P.inertia Gal(H/k)) = p.ramificationIdxIn (𝓞 H) :=
    Ideal.card_inertia_eq_ramificationIdxIn p P
  have cK : Nat.card (Q.inertia Gal(K/k)) = p.ramificationIdxIn (𝓞 K) :=
    Ideal.card_inertia_eq_ramificationIdxIn p Q
  have cH : Nat.card (P.inertia Gal(H/K)) = Q.ramificationIdxIn (𝓞 H) :=
    Ideal.card_inertia_eq_ramificationIdxIn Q P
  have hmul : p.ramificationIdxIn (𝓞 K) * Q.ramificationIdxIn (𝓞 H) = p.ramificationIdxIn (𝓞 H) :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn Q Gal(K/k) (𝓞 H) Gal(H/k) Gal(H/K)
  let f : (P.inertia Gal(H/k)) →* Gal(K/k) := (resTo k K H).comp (Subgroup.subtype _)
  have hrange : f.range = (P.inertia Gal(H/k)).map (resTo k K H) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let g : (P.inertia Gal(H/K)) →* (P.inertia Gal(H/k)) :=
    { toFun := fun τ => ⟨(τ.1.restrictScalars k), fun y => by
        rw [comm2]
        exact τ.2 y⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hker : f.ker ≤ g.range := by
    intro σ hσ
    have hfix : ∀ c : K, σ.1 (algebraMap K H c) = algebraMap K H c := by
      intro c
      have h2 : resTo k K H σ.1 = 1 := hσ
      rw [← AlgEquiv.restrictNormal_commutes σ.1 K c]
      have h3 : σ.1.restrictNormal K = 1 := h2
      rw [h3]
      rfl
    let τ : Gal(H/K) := AlgEquiv.ofRingEquiv (f := σ.1.toRingEquiv) hfix
    have hτ : τ ∈ P.inertia Gal(H/K) := by
      intro y
      have h4 := σ.2 y
      rw [← comm2] at *
      exact h4
    exact ⟨⟨τ, hτ⟩, by
      apply Subtype.ext
      ext z
      rfl⟩
  have hcardker : Nat.card f.ker ≤ Nat.card (P.inertia Gal(H/K)) :=
    (Subgroup.card_le_of_le hker).trans
      (Nat.card_le_card_of_surjective g.rangeRestrict g.rangeRestrict_surjective)
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have key := f.ker.card_mul_index
  rw [Subgroup.index_ker, hrange, cG, ← hmul] at key
  rw [cK]
  by_contra hlt
  push_neg at hlt
  have hQpos : 0 < Q.ramificationIdxIn (𝓞 H) := by
    rw [← cH]
    exact Nat.card_pos
  rw [cH] at hcardker
  nlinarith [Nat.mul_le_mul hcardker (le_of_lt hlt)]
end

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineFixQ :
    ∀ (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsGalois ℚ K] [IsGalois ℚ H] (p : ℕ), p.Prime → (UnramAt K p ↔ ∀ w : HeightOneSpectrum (𝓞 H), (p : 𝓞 H) ∈ w.asIdeal → w.asIdeal.inertia Gal(H/ℚ) ≤ (resTo ℚ K H).ker) := by
  intro K H _ _ _ _ _ _ _ p hp
  rw [UpperTheory.V.CF.unramIff.1 K p hp]
  constructor
  · intro h w hw
    have hv : (p : 𝓞 K) ∈ w.asIdeal.under (𝓞 K) := by
      simpa [Ideal.under, Ideal.mem_comap, map_natCast] using hw
    let v : HeightOneSpectrum (𝓞 K) := ⟨w.asIdeal.under (𝓞 K), inferInstance, fun hb => by
      rw [hb] at hv
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hv)⟩
    rw [← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w]
    exact h v hv
  · intro h v hv
    have hle : Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) ⊥ ≤ v.asIdeal := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 H) (by rw [hx, map_zero])
      rw [hx0]
      exact v.asIdeal.zero_mem
    obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal ⊥ hle
    have hpQ : (p : 𝓞 H) ∈ Q := by
      have hc : (p : 𝓞 K) ∈ Q.comap (algebraMap (𝓞 K) (𝓞 H)) := by
        change (p : 𝓞 K) ∈ Ideal.under (𝓞 K) Q
        rw [hQv]
        exact hv
      simpa [Ideal.mem_comap, map_natCast] using hc
    let w : HeightOneSpectrum (𝓞 H) := ⟨Q, hQ, fun hb => by
      rw [hb] at hpQ
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hpQ)⟩
    have h1 := h w hpQ
    rw [← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w] at h1
    have hw : Ideal.under (𝓞 K) w.asIdeal = v.asIdeal := hQv
    rwa [hw] at h1
end
