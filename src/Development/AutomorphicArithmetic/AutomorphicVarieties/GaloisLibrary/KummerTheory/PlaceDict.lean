module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem val_top {Ω : Type} [Field Ω] {x : Ω} (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
  by_contra hx
  have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
  rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
  exact lt_irrefl _ h2

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_place (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (A : ValuationSubring Ω) (hA : A ≠ ⊤) : ∃ v : HeightOneSpectrum (𝓞 K),
      ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ v.asIdeal := by
  have hm : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x =>
    (A.valuation_le_one_iff _).1 (int_le A (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom))
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hm
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
  rw [eq_top_iff]
  intro x _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have h1 : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).2 inferInstance
  have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ K Ω
  obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
  have h3 : ¬ A.valuation (algebraMap K Ω ((n : 𝓞 K) : K)) < 1 := by
    rw [hP, h0, Ideal.mem_bot]
    exact Int.cast_ne_zero.2 hn
  have h4 : A.valuation (n : Ω) = 1 :=
    le_antisymm (int_le A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
  have h5 := int_le A hi
  rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
  exact (A.valuation_le_one_iff x).1 h5

theorem UpperTheory.V.Kum.placeDict :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Ine (F := K) (⊤ : ValuationSubring Ω) = ⊥ ∧ (∀ A : ValuationSubring Ω, A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v) ∧
    (∀ (A : ValuationSubring Ω) (N : ℕ), N ≠ 0 → A.valuation (N : Ω) < 1 → A ≠ ⊤) ∧
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (N : ℕ), IsPlaceOver A v →
      (A.valuation (N : Ω) < 1 ↔ v ∈ Formalism.GaloisCohomology.Above (F := K) N) := by
  intro K Ω _ _ _ _ _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    have h := hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _))
    exact sub_eq_zero.1 (val_top h)
  · intro A hA
    exact exists_place K Ω A hA
  · rintro A N hN h rfl
    exact hN (Nat.cast_eq_zero.1 (val_top h))
  · intro A v N hv
    have h := hv (N : 𝓞 K)
    have e : algebraMap K Ω ((N : 𝓞 K) : K) = (N : Ω) := by simp
    rw [← e]
    exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.zmodToQZ :
    ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧ (∀ x, x ∈ Set.range ι ↔ (l : ℤ_[l]) ^ r • x = 0) ∧
    ∀ (z : ℤ_[l]) (a : ZMod (l ^ r)), ι (PadicInt.toZModPow r z * a) = z • ι a := by
  intro l _ r
  have hl : l.Prime := Fact.out
  have hlr0 : ((l : ℚ_[l]) ^ r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have zsm : ∀ (k : ℤ) (q : ℚ_[l]), k • QZ.mk l q = QZ.mk l ((k : ℚ_[l]) * q) := by
    intro k q
    rw [← Int.cast_smul_eq_zsmul ℤ_[l]]
    show QZ.mk l (((k : ℤ_[l]) : ℚ_[l]) * q) = _
    rw [PadicInt.coe_intCast]
  have hker : ((l ^ r : ℕ) : ℤ) • QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) = 0 := by
    rw [zsm]
    refine (Submodule.Quotient.mk_eq_zero (ZlSub l)).2 ⟨1, ?_⟩
    push_cast
    exact (mul_inv_cancel₀ hlr0).symm
  let ι : ZMod (l ^ r) →+ QZ l :=
    ZMod.lift (l ^ r) ⟨zmultiplesHom (QZ l) (QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹)), by
      rw [zmultiplesHom_apply]
      exact hker⟩
  have hι : ∀ k : ℤ, ι (k : ZMod (l ^ r)) = QZ.mk l ((k : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹) := by
    intro k
    simp only [ι, ZMod.lift_coe, zmultiplesHom_apply]
    exact zsm k _
  have hkill : ∀ a : ZMod (l ^ r), (l ^ r : ℕ) • ι a = 0 := by
    intro a
    rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]
  have h3 : ∀ (z : ℤ_[l]) (a : ZMod (l ^ r)), ι (PadicInt.toZModPow r z * a) = z • ι a := by
    intro z a
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec r z)
    have hz : PadicInt.toZModPow r z = ((z.appr r : ℕ) : ZMod (l ^ r)) := rfl
    rw [hz, ← nsmul_eq_mul, map_nsmul]
    have hzw : z = ((z.appr r : ℕ) : ℤ_[l]) + w * ((l ^ r : ℕ) : ℤ_[l]) := by
      push_cast
      rw [hw]
      ring
    conv_rhs => rw [hzw]
    rw [add_smul, Nat.cast_smul_eq_nsmul, mul_smul, Nat.cast_smul_eq_nsmul, hkill, smul_zero, add_zero]
  refine ⟨ι, ?_, ?_, h3⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
    rw [hι] at ha
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero (ZlSub l)).1 ha
    have hy' : (y : ℚ_[l]) = (k : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹ := hy
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hky : (k : ℤ_[l]) = y * (l : ℤ_[l]) ^ r := by
      apply PadicInt.ext
      push_cast
      rw [hy', mul_assoc, inv_mul_cancel₀ hlr0, mul_one]
    have hn : ‖(k : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
      rw [hky, norm_mul, PadicInt.norm_p_pow]
      exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one y)
    have hd := PadicInt.norm_int_le_pow_iff_dvd.1 hn
    exact_mod_cast hd
  · intro x
    constructor
    · rintro ⟨a, rfl⟩
      have h := h3 ((l : ℤ_[l]) ^ r) a
      rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, map_zero] at h
      exact h.symm
    · intro hx
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) x
      have hx' : QZ.mk l ((((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * q) = 0 := hx
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero (ZlSub l)).1 hx'
      have hz' : (z : ℚ_[l]) = (((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * q := hz
      push_cast at hz'
      refine ⟨PadicInt.toZModPow r z, ?_⟩
      rw [← mul_one (PadicInt.toZModPow r z), h3, show (1 : ZMod (l ^ r)) = ((1 : ℤ) : ZMod (l ^ r)) by simp, hι]
      show QZ.mk l ((z : ℚ_[l]) * (((1 : ℤ) : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹)) = Submodule.Quotient.mk q
      congr 1
      rw [hz']
      push_cast
      field_simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem frob_pow_fin (k L : Type) [Field k] [Finite k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (τ : L →ₐ[k] L) (S : Finset L) : ∃ i : ℕ, ∀ x ∈ S, τ x = x ^ Nat.card k ^ i := by
  classical
  haveI := Fintype.ofFinite k
  let E := IntermediateField.adjoin k (S : Set L)
  haveI : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : Finite E := Module.finite_of_finite k
  haveI : Normal k E := inferInstance
  let τE : E →ₐ[k] E := τ.restrictNormal E
  have hbij : Function.Bijective τE := Finite.injective_iff_bijective.1 τE.toRingHom.injective
  let e : E ≃ₐ[k] E := AlgEquiv.ofBijective τE hbij
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k E).2 e
  have hn' : FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ (n : ℕ) = e := hn
  refine ⟨n, fun x hx => ?_⟩
  have hxE : x ∈ E := IntermediateField.subset_adjoin k _ hx
  have h1 := τ.restrictNormal_commutes E ⟨x, hxE⟩
  have h3 : e ⟨x, hxE⟩ = ⟨x, hxE⟩ ^ Fintype.card k ^ (n : ℕ) := by
    rw [← hn', AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [Nat.card_eq_fintype_card]
  calc τ x = τ (algebraMap E L ⟨x, hxE⟩) := rfl
    _ = algebraMap E L (τE ⟨x, hxE⟩) := h1.symm
    _ = algebraMap E L (e ⟨x, hxE⟩) := rfl
    _ = x ^ Fintype.card k ^ (n : ℕ) := by
      rw [h3, map_pow]
      rfl

private theorem alg_residue {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) (k : Type) [Field k]
    [Algebra k (IsLocalRing.ResidueField A)] (x : A) (hx : IsAlgebraic ℤ (x : Ω)) :
    IsAlgebraic k (IsLocalRing.residue A x) := by
  obtain ⟨p, hp0, hpx⟩ := hx
  have hq : p.primPart.IsPrimitive := p.isPrimitive_primPart
  have hqx : Polynomial.aeval x p.primPart = 0 := by
    have h1 : Polynomial.aeval (x : Ω) p = (p.content : Ω) * Polynomial.aeval (x : Ω) p.primPart := by
      conv_lhs => rw [p.eq_C_content_mul_primPart]
      simp
    have hc : (p.content : Ω) ≠ 0 := by
      exact_mod_cast (Polynomial.content_eq_zero_iff.not.2 hp0)
    rw [hpx] at h1
    have h2 : Polynomial.aeval (x : Ω) p.primPart = 0 := (mul_eq_zero.1 h1.symm).resolve_left hc
    have h3 : ((Polynomial.aeval x p.primPart : A) : Ω) = Polynomial.aeval (x : Ω) p.primPart :=
      (Polynomial.aeval_algebraMap_apply Ω x p.primPart).symm
    apply Subtype.ext
    rw [h3, h2]
    rfl
  refine ⟨p.primPart.map (algebraMap ℤ k), ?_, ?_⟩
  · intro h
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hr | hr
    · have hdvd : Polynomial.C ((ringChar k : ℕ) : ℤ) ∣ p.primPart := by
        rw [Polynomial.C_dvd_iff_dvd_coeff]
        intro i
        have := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P i) h
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
        exact (CharP.intCast_eq_zero_iff k (ringChar k) _).1 this
      have hu := hq _ hdvd
      rw [Int.isUnit_iff] at hu
      have := hr.two_le
      omega
    · haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).1 hr
      have : p.primPart = 0 := by
        apply Polynomial.map_injective (algebraMap ℤ k) (RingHom.injective_int (algebraMap ℤ k))
        rw [h, Polynomial.map_zero]
      exact hq.ne_zero this
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have e : (algebraMap k (IsLocalRing.ResidueField A)).comp (algebraMap ℤ k) =
        algebraMap ℤ (IsLocalRing.ResidueField A) := RingHom.ext_int _ _
    rw [e, ← Polynomial.aeval_def]
    have := Polynomial.aeval_algebraMap_apply (IsLocalRing.ResidueField A) x p.primPart
    rw [IsLocalRing.ResidueField.algebraMap_eq] at this
    rw [this, hqx, map_zero]

private theorem frob_pow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : G F Ω} (hφ : IsFrob A q φ) (n : ℕ) :
    IsFrob A (q ^ n) (φ ^ n) := by
  have hD : φ ∈ ValuationSubring.decompositionSubgroup F A := hφ.1
  induction n with
  | zero =>
    refine ⟨by rw [pow_zero]; exact one_mem _, fun x _ => ?_⟩
    simp
  | succ n ih =>
    refine ⟨pow_mem hD (n + 1), fun x hx => ?_⟩
    have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx
    have hyA : (φ ^ n) x ∈ A := (apply_mem_iff_of_mem_Dec (pow_mem hD n) x).2 hxA
    have hxA' : x ^ q ^ n ∈ A := pow_mem hxA _
    have e1 : A.valuation (φ ((φ ^ n) x) - ((φ ^ n) x) ^ q) < 1 :=
      hφ.2 _ ((A.valuation_le_one_iff _).2 hyA)
    have e2 : A.valuation ((φ ^ n) x - x ^ q ^ n) < 1 := ih.2 x hx
    have e3 : A.valuation (((φ ^ n) x) ^ q - (x ^ q ^ n) ^ q) < 1 := by
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨(φ ^ n) x, hyA⟩ : A) ⟨x ^ q ^ n, hxA'⟩ q
      have h4 : ((φ ^ n) x) ^ q - (x ^ q ^ n) ^ q = ((φ ^ n) x - x ^ q ^ n) * c := by
        have := congrArg (fun z : A => (z : Ω)) hc
        push_cast at this
        exact this
      rw [h4, map_mul]
      have hc1 : A.valuation (c : Ω) ≤ 1 := A.valuation_le_one c
      calc _ ≤ A.valuation ((φ ^ n) x - x ^ q ^ n) * 1 := by gcongr
        _ < 1 := by
          rw [mul_one]
          exact e2
    have h5 : (φ ^ (n + 1)) x - x ^ q ^ (n + 1) =
        (φ ((φ ^ n) x) - ((φ ^ n) x) ^ q) + (((φ ^ n) x) ^ q - (x ^ q ^ n) ^ q) := by
      rw [pow_succ' φ n, AlgEquiv.mul_apply, pow_succ q n, pow_mul]
      ring
    rw [h5]
    exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt e1 e3)

private theorem dec_pow_fin {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) {g : G K Ω}
    (hg : g ∈ Dec (F := K) A) (S : Finset A) :
    ∃ i : ℕ, ∀ x ∈ S, A.valuation (g x - (x : Ω) ^ normV v ^ i) < 1 := by
  classical
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hint : ∀ a : 𝓞 K, ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) a ∈ A := fun a =>
    mem_of_isIntegral_int A ((NumberField.RingOfIntegers.isIntegral_coe a).algebraMap (B := Ω))
  let f0 : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hint
  let f1 : 𝓞 K →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp f0
  have hker : ∀ a ∈ v.asIdeal, f1 a = 0 := by
    intro a ha
    show IsLocalRing.residue A (f0 a) = 0
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact (hA a).2 ha
  letI : Algebra (𝓞 K ⧸ v.asIdeal) (IsLocalRing.ResidueField A) :=
    (Ideal.Quotient.lift v.asIdeal f1 hker).toAlgebra
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ K Ω
  haveI : Algebra.IsAlgebraic (𝓞 K ⧸ v.asIdeal) (IsLocalRing.ResidueField A) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    exact alg_residue A _ x ((IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic (x : Ω)))⟩
  let gD : ValuationSubring.decompositionSubgroup K A := ⟨g, hg⟩
  have hfix : ∀ a : 𝓞 K, gD • f0 a = f0 a := by
    intro a
    apply Subtype.ext
    show g (algebraMap K Ω (a : K)) = algebraMap K Ω (a : K)
    exact g.commutes _
  let τ : IsLocalRing.ResidueField A →ₐ[𝓞 K ⧸ v.asIdeal] IsLocalRing.ResidueField A :=
    { MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) gD with
      commutes' := by
        intro c
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        show gD • (Ideal.Quotient.lift v.asIdeal f1 hker (Ideal.Quotient.mk _ a)) = _
        rw [Ideal.Quotient.lift_mk]
        show gD • IsLocalRing.residue A (f0 a) = IsLocalRing.residue A (f0 a)
        rw [← IsLocalRing.ResidueField.residue_smul (ValuationSubring.decompositionSubgroup K A) gD (f0 a), hfix] }
  obtain ⟨i, hi⟩ := frob_pow_fin (𝓞 K ⧸ v.asIdeal) (IsLocalRing.ResidueField A) τ
    (S.image (IsLocalRing.residue A))
  refine ⟨i, fun x hx => ?_⟩
  have h1 : gD • IsLocalRing.residue A x = IsLocalRing.residue A x ^ normV v ^ i :=
    hi _ (Finset.mem_image_of_mem _ hx)
  have h2 : IsLocalRing.residue A (gD • x - x ^ normV v ^ i) = 0 := by
    rw [map_sub, IsLocalRing.ResidueField.residue_smul, map_pow, h1, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h2
  exact h2

private theorem closed_ev {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ω)
    (P : Ω → Prop) : IsClosed {h : G K Ω | P (h x)} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro h hh
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  refine ⟨(fun k => h * k) '' (((IntermediateField.adjoin K {x}).fixingSubgroup : Subgroup (G K Ω)) : Set (G K Ω)),
    ?_, ?_, ⟨1, one_mem _, mul_one h⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    have hkx : k x = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk x (IntermediateField.mem_adjoin_simple_self K x)
    show ¬ P ((h * k) x)
    rw [AlgEquiv.mul_apply, hkx]
    exact hh
  · exact isOpenMap_mul_left h _ (IntermediateField.fixingSubgroup_isOpen _)

theorem UpperTheory.V.Kum.decGen :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (σ : G K Ω) (H : Subgroup (G K Ω)),
    IsPlaceOver A v → IsFrob (F := K) A (normV v) σ → IsOpen (H : Set (G K Ω)) → Ine (F := K) A ≤ H → σ ∈ H → Dec (F := K) A ≤ H := by
  classical
  intro K Ω _ _ _ _ _ A v σ H hA hσ hHo hI hσH g hg
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have hHc : IsClosed (H : Set (G K Ω)) := Subgroup.isClosed_of_isOpen H hHo
  have hσD : σ ∈ Dec (F := K) A := hσ.1
  have hDc : IsClosed (Dec (F := K) A : Set (G K Ω)) := by
    have e : (Dec (F := K) A : Set (G K Ω)) = ⋂ x : Ω, {h : G K Ω | (h x ∈ A ↔ x ∈ A)} := by
      ext h
      simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
      constructor
      · intro hh x
        exact apply_mem_iff_of_mem_Dec hh x
      · intro hh
        rw [mem_Dec]
        ext y
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
        have h1 := hh (h⁻¹ y)
        rw [AlgEquiv.aut_inv] at h1 ⊢
        rw [AlgEquiv.apply_symm_apply] at h1
        exact h1.symm
    rw [e]
    exact isClosed_iInter fun x => closed_ev x (fun y => (y ∈ A ↔ x ∈ A))
  let Cl : Set (G K Ω) := closure (Set.range fun i : ℕ => σ ^ i)
  have hClH : Cl ⊆ H := closure_minimal (by
    rintro _ ⟨i, rfl⟩
    exact H.pow_mem hσH i) hHc
  have hClD : Cl ⊆ Dec (F := K) A := closure_minimal (by
    rintro _ ⟨i, rfl⟩
    exact (Dec (F := K) A).pow_mem hσD i) hDc
  let C : Finset A → Set (G K Ω) := fun S => Cl ∩ {τ | ∀ x ∈ S, A.valuation (g x - τ x) < 1}
  have hCcl : ∀ S, IsClosed (C S) := by
    intro S
    apply isClosed_closure.inter
    have e : {τ : G K Ω | ∀ x ∈ S, A.valuation (g x - τ x) < 1} =
        ⋂ x ∈ S, {τ : G K Ω | A.valuation (g x - τ x) < 1} := by
      ext τ
      simp
    rw [e]
    exact isClosed_biInter fun x _ => closed_ev (x : Ω) (fun y => A.valuation (g x - y) < 1)
  have hCne : ∀ S, (C S).Nonempty := by
    intro S
    obtain ⟨i, hi⟩ := dec_pow_fin hA hg S
    refine ⟨σ ^ i, subset_closure ⟨i, rfl⟩, fun x hx => ?_⟩
    have h1 := hi x hx
    have h2 := (frob_pow hσ i).2 x (A.valuation_le_one x)
    have e : g x - (σ ^ i) x = (g x - (x : Ω) ^ normV v ^ i) - ((σ ^ i) x - (x : Ω) ^ normV v ^ i) := by
      ring
    rw [e]
    exact lt_of_le_of_lt (A.valuation.map_sub _ _) (max_lt h1 h2)
  have hdir : Directed (fun s t => s ⊇ t) C := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩
    · rintro τ ⟨h1, h2⟩
      exact ⟨h1, fun x hx => h2 x (Finset.mem_union_left _ hx)⟩
    · rintro τ ⟨h1, h2⟩
      exact ⟨h1, fun x hx => h2 x (Finset.mem_union_right _ hx)⟩
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hCne
    (fun S => (hCcl S).isCompact) hCcl
  rw [Set.mem_iInter] at hτ
  have hτCl : τ ∈ Cl := (hτ ∅).1
  have hτD := hClD hτCl
  have hτx : ∀ x : A, A.valuation (g x - τ x) < 1 := fun x => (hτ {x}).2 x (Finset.mem_singleton_self x)
  have hι : τ⁻¹ * g ∈ Ine (F := K) A := by
    show τ⁻¹ * g ∈ Inertia A
    refine ⟨(Dec (F := K) A).mul_mem ((Dec (F := K) A).inv_mem hτD) hg, fun x hx => ?_⟩
    have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx
    have e : (τ⁻¹ * g) x - x = τ⁻¹ (g x - τ x) := by
      rw [AlgEquiv.mul_apply, map_sub, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [e, valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hτD)]
    exact hτx ⟨x, hxA⟩
  have e : g = τ * (τ⁻¹ * g) := by group
  rw [e]
  exact H.mul_mem (hClH hτCl) (hI hι)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped Pointwise

theorem UpperTheory.V.Kum.toGalDict :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω),
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A) ∧
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Ine (F := K) A ↔ u.1 ∈ Ine (F := F) A) ∧
    Continuous (toGal K hU) ∧ (galOf F K Ω ≤ U → IsHomeomorph (toGal K hU) ∧ IsOpen (U : Set (G F Ω))) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU
  obtain ⟨hE, hO, -⟩ := galEmbTop F K Ω
  have hD : ∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A := by
    intro A u
    rw [mem_Dec, mem_Dec]
    have e : toGal K hU u • A = u.1 • A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact Iff.rfl
    rw [e]
  have hcomp : galEmb F K Ω ∘ toGal K hU = Subtype.val := funext fun u => AlgEquiv.ext fun x => rfl
  have hc : Continuous (toGal K hU) := by
    rw [hE.isInducing.continuous_iff, hcomp]
    exact continuous_subtype_val
  refine ⟨hD, fun A u => ?_, hc, fun h => ⟨?_, ?_⟩⟩
  · exact ⟨fun h => ⟨(hD A u).1 h.1, h.2⟩, fun h => ⟨(hD A u).2 h.1, h.2⟩⟩
  · rw [isHomeomorph_iff_exists_inverse]
    refine ⟨hc, fun σ => ⟨galEmb F K Ω σ, h (galEmb_mem F K Ω σ)⟩, fun u => Subtype.ext (AlgEquiv.ext fun x => rfl),
      fun σ => AlgEquiv.ext fun x => rfl, hE.continuous.subtype_mk _⟩
  · rw [le_antisymm hU h]
    exact hO
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem qzB_smul_mk (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) (q : ℚ_[l]) :
    x • QZ.mk l q = QZ.mk l ((x : ℚ_[l]) * q) := rfl

private theorem qzB_mk_eq_zero (l : ℕ) [Fact l.Prime] (q : ℚ_[l]) :
    QZ.mk l q = 0 ↔ ∃ z : ℤ_[l], (z : ℚ_[l]) = q :=
  Submodule.Quotient.mk_eq_zero (ZlSub l)

private theorem qzB_mk_surj (l : ℕ) [Fact l.Prime] (a : QZ l) : ∃ q, QZ.mk l q = a :=
  Submodule.Quotient.mk_surjective (ZlSub l) a

theorem UpperTheory.V.Kum.qzBasic :
    ∀ (l : ℕ) [Fact l.Prime], (∀ u : ℤ_[l], u ≠ 0 → Function.Surjective fun x : QZ l => u • x) ∧ (∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0) ∧ (l ≠ 2 → ∀ x : QZ l, 2 • x = 0 → x = 0) := by
  intro l _
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have tors : ∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0 := by
    intro x
    obtain ⟨q, rfl⟩ := qzB_mk_surj l x
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hl1
    refine ⟨k, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], qzB_smul_mk, qzB_mk_eq_zero]
    have hpos : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (by linarith) k
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [PadicInt.mem_subring_iff]
    push_cast
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast, inv_mul_le_iff₀ hpos, mul_one]
    exact hk.le
  refine ⟨?_, tors, ?_⟩
  · intro u hu a
    obtain ⟨q, rfl⟩ := qzB_mk_surj l a
    have hu' : (u : ℚ_[l]) ≠ 0 := PadicInt.coe_ne_zero.2 hu
    refine ⟨QZ.mk l (q / u), ?_⟩
    show u • QZ.mk l (q / u) = QZ.mk l q
    rw [qzB_smul_mk, mul_div_cancel₀ q hu']
  · intro h2 x hx
    obtain ⟨k, hk⟩ := tors x
    have hc : IsCoprime (2 : ℤ) ((l ^ k : ℕ) : ℤ) := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm h2))
    obtain ⟨a, b, hab⟩ := hc
    calc x = (1 : ℤ) • x := (one_smul ℤ x).symm
      _ = (a * 2 + b * ((l ^ k : ℕ) : ℤ)) • x := by rw [hab]
      _ = a • ((2 : ℕ) • x) + b • ((l ^ k) • x) := by
        rw [add_smul, mul_smul, mul_smul]
        norm_cast
      _ = 0 := by rw [hx, hk, smul_zero, smul_zero, add_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.galOfCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (E K : Type) [Field E] [Field K] [Algebra E K] [Algebra E Ω] [Algebra K Ω] [IsScalarTower E K Ω] [IsCyclotomicExtension {l ^ n} E K], galOf F K Ω = levU l (galOf F E Ω) n := by
  intro F Ω _ _ _ _ _ l _ n E K _ _ _ _ _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  ext σ
  have key : ∀ t : Ω, t ^ (l ^ n) = 1 →
      σ t = t ^ ((cycZ F Ω l σ).val.toZModPow n).val := fun t ht =>
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω σ) t ht
  show σ ∈ galOf F K Ω ↔ σ ∈ galOf F E Ω ⊓ Subgroup.comap (cycZ F Ω l) (KStar.TotallyRealRoots.princ l n)
  rw [Subgroup.mem_inf, Subgroup.mem_comap, KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow]
  constructor
  · intro h
    have hE : σ ∈ galOf F E Ω := fun x => by
      have hx := h (algebraMap E K x)
      rwa [← IsScalarTower.algebraMap_apply] at hx
    refine ⟨hE, ?_⟩
    have hζ : IsPrimitiveRoot (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) (l ^ n) :=
      (IsCyclotomicExtension.zeta_spec (l ^ n) E K).map_of_injective (algebraMap K Ω).injective
    have h1 := key _ hζ.pow_eq_one
    rw [h (IsCyclotomicExtension.zeta (l ^ n) E K)] at h1
    have hfin : IsOfFinOrder (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) :=
      orderOf_pos_iff.mp (by rw [← hζ.eq_orderOf]; exact Nat.pos_of_neZero _)
    have e : (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) ^
        ((cycZ F Ω l σ).val.toZModPow n).val =
        (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) ^ 1 := by
      rw [pow_one]
      exact h1.symm
    have h3 : ((cycZ F Ω l σ).val.toZModPow n).val ≡ 1 [MOD l ^ n] := by
      have h5 := hfin.pow_eq_pow_iff_modEq.mp e
      rwa [← hζ.eq_orderOf] at h5
    ext
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h3
    rw [ZMod.natCast_zmod_val, Nat.cast_one] at h4
    simpa using h4
  · rintro ⟨hE, hc⟩
    have hc' : (cycZ F Ω l σ).val.toZModPow n = 1 := by
      have := congrArg Units.val hc
      simpa using this
    intro x
    let f1 : K →ₐ[E] Ω := IsScalarTower.toAlgHom E K Ω
    let f2 : K →ₐ[E] Ω :=
      { toRingHom := (σ : Ω →+* Ω).comp (algebraMap K Ω)
        commutes' := fun r => by
          show σ (algebraMap K Ω (algebraMap E K r)) = algebraMap E Ω r
          rw [← IsScalarTower.algebraMap_apply]
          exact hE r }
    have hx := IsCyclotomicExtension.adjoin_roots (S := {l ^ n}) (A := E) (B := K) x
    have hmem : x ∈ AlgHom.equalizer f1 f2 := by
      refine Algebra.adjoin_le (fun b hb => ?_) hx
      obtain ⟨m, hm, -, hbm⟩ := hb
      rw [Set.mem_singleton_iff] at hm
      subst hm
      have ht : (algebraMap K Ω b) ^ (l ^ n) = 1 := by rw [← map_pow, hbm, map_one]
      show algebraMap K Ω b = σ (algebraMap K Ω b)
      rw [key _ ht, hc', ZMod.val_one_eq_one_mod]
      conv_lhs => rw [← pow_one (algebraMap K Ω b), ← Nat.mod_add_div 1 (l ^ n), pow_add, pow_mul, ht, one_pow, mul_one]
    exact ((AlgHom.mem_equalizer f1 f2 x).mp hmem).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem rootSet_X_pow_sub_one_eq_setOf_exists_mem_singleton (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (k : ℕ) (hk : k ≠ 0) :
    (Polynomial.X ^ k - 1 : Polynomial F).rootSet Ω = {b : Ω | ∃ m ∈ ({k} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
  have hp : (Polynomial.X ^ k - 1 : Polynomial F) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hk) (1 : F)
  ext b
  rw [Polynomial.mem_rootSet_of_ne hp]
  simp [sub_eq_zero, hk]

private theorem apply_mem_fn_of_isLift (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (l n : ℕ) (τ : F ≃+* F)
    (σ : Ω ≃+* Ω) (h : IsLift τ σ) (x : Ω) (hx : x ∈ Fn F Ω l n) : σ x ∈ Fn F Ω l n := by
  have hx' : x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω) := hx
  show σ x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω)
  refine IntermediateField.adjoin_induction F
    (motive := fun x _ => σ x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω))
    ?_ ?_ ?_ ?_ ?_ hx'
  · intro y hy
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet] at hy ⊢
    obtain ⟨hp, hy⟩ := hy
    refine ⟨hp, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one] at hy ⊢
    rw [← map_pow, ← map_one σ, ← map_sub, hy, map_zero]
  · intro c
    rw [h c]
    exact IntermediateField.algebraMap_mem _ _
  · intro y z _ _ hy hz
    rw [map_add (f := _)]
    exact add_mem hy hz
  · intro y _ hy
    rw [map_inv₀]
    exact inv_mem hy
  · intro y z _ _ hy hz
    rw [map_mul]
    exact mul_mem hy hz

theorem UpperTheory.V.Kum.fnCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), IsCyclotomicExtension {l ^ n} F (Fn F Ω l n) ∧ (∀ (τ : F ≃+* F) (σ : Ω ≃+* Ω), IsLift τ σ → ∃ τ' : Fn F Ω l n ≃+* Fn F Ω l n, IsLift τ' σ) ∧ (2 ≤ n → IsTotallyComplex (Fn F Ω l n)) := by
  intro F Ω _ _ _ _ _ l _ n
  have hl : l.Prime := Fact.out
  have hk : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ n) := ⟨hk⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hFn : Fn F Ω l n = IntermediateField.adjoin F {b : Ω | ∃ m ∈ ({l ^ n} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
    show IntermediateField.adjoin F _ = _
    rw [rootSet_X_pow_sub_one_eq_setOf_exists_mem_singleton F Ω _ hk]
  refine ⟨?_, ?_, ?_⟩
  · rw [hFn]
    refine IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot (S := {l ^ n}) (K := F) (L := Ω) ?_
    intro m hm _
    rw [Set.mem_singleton_iff] at hm
    subst hm
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  · intro τ σ h
    have hs : IsLift τ.symm σ.symm := by
      intro x
      apply σ.injective
      rw [RingEquiv.apply_symm_apply, h, RingEquiv.apply_symm_apply]
    refine ⟨{ toFun := fun x => ⟨σ x, apply_mem_fn_of_isLift F Ω l n τ σ h x.1 x.2⟩,
              invFun := fun x => ⟨σ.symm x, apply_mem_fn_of_isLift F Ω l n τ.symm σ.symm hs x.1 x.2⟩,
              left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1),
              right_inv := fun x => Subtype.ext (σ.apply_symm_apply x.1),
              map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1),
              map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1) }, ?_⟩
    intro x
    rfl
  · intro hn2
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    have hzmem : z ∈ Fn F Ω l n := by
      rw [hFn]
      exact IntermediateField.subset_adjoin _ _ ⟨l ^ n, rfl, hk, hz.pow_eq_one⟩
    have hζ : IsPrimitiveRoot (⟨z, hzmem⟩ : Fn F Ω l n) (l ^ n) :=
      IsPrimitiveRoot.of_map_of_injective (f := (Fn F Ω l n).val) hz Subtype.val_injective
    have hcyc := IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := ℚ) hζ
    have h2 : 2 < l ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.two_le 2
        _ ≤ l ^ n := Nat.pow_le_pow_right hl.pos hn2
    have htc := @IsCyclotomicExtension.Rat.isTotallyComplex (l ^ n) _
      (IntermediateField.adjoin ℚ {(⟨z, hzmem⟩ : Fn F Ω l n)}) _ _ hcyc h2
    exact isTotallyComplex_of_algebra (IntermediateField.adjoin ℚ {(⟨z, hzmem⟩ : Fn F Ω l n)}) (Fn F Ω l n)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

open KStar.TotallyRealRoots in
private theorem eg_pow_mem {l : ℕ} [Fact l.Prime] {a : ℕ} (ha : 1 ≤ a) {u : ℤ_[l]ˣ} (hu : u ∈ princ l a) :
    u ^ l ∈ princ l (a + 1) := by
  rw [mem_princ] at hu ⊢
  obtain ⟨c, hc⟩ := hu
  obtain ⟨f, hf⟩ := sq_dvd_add_pow_sub_sub ((l : ℤ_[l]) ^ a * c) 1 l
  have hw : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ a * c := by rw [← hc]; ring
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  refine ⟨c + (l : ℤ_[l]) ^ m * c ^ 2 * f, ?_⟩
  rw [Units.val_pow_eq_pow_val, hw]
  simp only [one_pow, one_mul] at hf
  linear_combination hf

open KStar.TotallyRealRoots in
private theorem eg_exists_not_mem {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ≠ 1) :
    ∃ a, u ∉ princ l a := by
  by_contra h
  push Not at h
  apply hu
  have hb : IsClosed ((⊥ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_bot]
    exact isClosed_singleton
  have := mem_of_isClosed hb (x := u) fun b => ⟨1, Subgroup.one_mem _, by
    rw [map_one]; exact (MonoidHom.mem_ker.1 (h b)).symm⟩
  exact Subgroup.mem_bot.1 this

theorem UpperTheory.V.Kum.existsGen :
    ∀ (l : ℕ) [Fact l.Prime] (V : Subgroup ℤ_[l]ˣ), IsClosed (V : Set ℤ_[l]ˣ) → (l ≠ 2 ∨ V ≤ KStar.TotallyRealRoots.princ l 2) → ∃ γ ∈ V, V ≤ (Subgroup.zpowers γ).topologicalClosure := by
  classical
  intro l _ V _ hl
  have hp : l.Prime := Fact.out
  obtain ⟨⟨_, g, hg, rfl⟩, hgen⟩ := IsCyclic.exists_generator (α := V.map (KStar.TotallyRealRoots.red l))
  have key : ∀ γ ∈ V, KStar.TotallyRealRoots.red l γ = KStar.TotallyRealRoots.red l g →
      V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ (Subgroup.zpowers γ).topologicalClosure →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := by
    intro γ hγ e h v hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨_, Subgroup.mem_map_of_mem _ hv⟩)
    have hk' : KStar.TotallyRealRoots.red l g ^ k = KStar.TotallyRealRoots.red l v := congrArg Subtype.val hk
    have h1 : v * (γ ^ k)⁻¹ ∈ V ⊓ KStar.TotallyRealRoots.princ l 1 := by
      refine Subgroup.mem_inf.2 ⟨V.mul_mem hv (V.inv_mem (V.zpow_mem hγ k)), ?_⟩
      rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, e, hk',
        mul_inv_cancel]
    have h2 : γ ^ k ∈ (Subgroup.zpowers γ).topologicalClosure :=
      Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k)
    simpa using Subgroup.mul_mem _ (h h1) h2
  by_cases hW : V ⊓ KStar.TotallyRealRoots.princ l 1 = ⊥
  · exact ⟨g, hg, key g hg rfl (by rw [hW]; exact bot_le)⟩
  have hex : ∃ b, ¬ V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ KStar.TotallyRealRoots.princ l b := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
    obtain ⟨b, hb⟩ := eg_exists_not_mem (u := w) (fun h => hw1 (Subtype.ext h))
    exact ⟨b, fun h => hb (h hw)⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ KStar.TotallyRealRoots.princ l m :=
    fun m hm => not_not.1 (Nat.find_min hex hm)
  have h1 : 1 < Nat.find hex := by
    by_contra h
    exact hspec (inf_le_right.trans (KStar.TotallyRealRoots.princ_anti (by omega)))
  have h2 : l = 2 → 2 < Nat.find hex := by
    intro h2
    by_contra h
    exact hspec (inf_le_left.trans ((hl.resolve_left (not_not.2 h2)).trans (KStar.TotallyRealRoots.princ_anti (by omega))))
  obtain ⟨a, ha⟩ : ∃ a, Nat.find hex = a + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [ha] at hspec hmin h1 h2
  have hle := hmin a (Nat.lt_succ_self a)
  obtain ⟨u, hu, hua⟩ := SetLike.not_le_iff_exists.1 hspec
  have fin : ∀ γ ∈ V, KStar.TotallyRealRoots.red l γ = KStar.TotallyRealRoots.red l g → γ ^ (l - 1) ∉ KStar.TotallyRealRoots.princ l (a + 1) →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := by
    intro γ hγ e h
    refine key γ hγ e (hle.trans ?_)
    have hm : γ ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l a := by
      refine hle (Subgroup.mem_inf.2 ⟨V.pow_mem hγ _, ?_⟩)
      rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_pow, ZMod.units_pow_card_sub_one_eq_one]
    refine KStar.TotallyRealRoots.princ_le_of_isClosed (u := γ ^ (l - 1)) (by omega) (fun h => by have := h2 h; omega)
      (Subgroup.isClosed_topologicalClosure _)
      (Subgroup.le_topologicalClosure _ (Subgroup.npow_mem_zpowers γ _)) ?_
    exact emultiplicity_eq_coe.2 ⟨KStar.TotallyRealRoots.mem_princ.1 hm, fun h' => h (KStar.TotallyRealRoots.mem_princ.2 h')⟩
  by_cases hga : g ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l (a + 1)
  · refine ⟨g * u, V.mul_mem hg hu.1, fin _ (V.mul_mem hg hu.1) ?_ ?_⟩
    · have : u ∈ (KStar.TotallyRealRoots.red l).ker := by
        rw [← KStar.TotallyRealRoots.princ_one_eq_ker]
        exact (Subgroup.mem_inf.1 hu).2
      rw [map_mul, MonoidHom.mem_ker.1 this, mul_one]
    · intro h
      rw [mul_pow] at h
      have h3 := (mul_mem_cancel_left hga).1 h
      have h4 := eg_pow_mem (by omega) (hle hu)
      have h5 : u ^ l = u ^ (l - 1) * u := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
      rw [h5] at h4
      exact hua ((mul_mem_cancel_left h3).1 h4)
  · exact ⟨g, hg, fin g hg rfl hga⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenOfCard
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem card_simple (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    [h : IsSimpleModule ℤ_[l] M] : Nat.card M = l := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h
  have hIm : I = IsLocalRing.maximalIdeal ℤ_[l] := IsLocalRing.eq_maximalIdeal hI
  subst hIm
  rw [Nat.card_congr e.toEquiv]
  have f := RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZMod (p := l)))
  have g := Ideal.quotEquivOfEq (PadicInt.ker_toZMod (p := l))
  rw [← Nat.card_congr g.toEquiv, Nat.card_congr f.toEquiv, Nat.card_zmod]

private theorem aux (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (h : IsFiniteLength ℤ_[l] M) : ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  induction h with
  | of_subsingleton =>
    exact ⟨0, by rw [Module.length_eq_zero]; rfl, by rw [Nat.card_of_subsingleton (0 : _)]; simp⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨k, hk, hc⟩ := ih
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N)
        (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      have h1 : Nat.card (M ⧸ N.toAddSubgroup) = l := card_simple l (M ⧸ N)
      have h2 : Nat.card N.toAddSubgroup = l ^ k := hc
      rw [h1, h2, pow_succ, mul_comm]

theorem UpperTheory.V.Kum.lenOfCard :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M], ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  intro l _ M _ _ _
  exact aux l M (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClProd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mk_eq_finprod (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
    ClassGroup.mk K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ FractionalIdeal.count K v I.1 := by
  let P : HeightOneSpectrum (𝓞 K) → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := fun v =>
    FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have hfin : (Function.mulSupport fun v => P v ^ FractionalIdeal.count K v I.1).Finite :=
    (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I.1)).subset
      fun v hv h => hv (by simp only [h, zpow_zero])
  have hI : ∏ᶠ v, P v ^ FractionalIdeal.count K v I.1 = I := by
    apply Units.ext
    rw [← Units.coeHom_apply, map_finprod _ hfin]
    conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
    exact finprod_congr fun v => by simp [Units.val_zpow_eq_zpow_val, P]
  conv_lhs => rw [← hI]
  rw [map_finprod _ hfin]
  exact finprod_congr fun v => by rw [map_zpow, ClassGroup.mk_mk0]; rfl

private theorem count_eq_ordv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = ordv v a := by
  have hI : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K (IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).2)⁻¹ *
        ↑(Ideal.span {(IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).1} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsLocalization.sec_spec' (nonZeroDivisors (𝓞 K)) (a : K), inv_mul_cancel_left₀]
    simpa using nonZeroDivisors.coe_ne_zero _
  rw [FractionalIdeal.count_well_defined K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 a.ne_zero) hI]
  change _ = -Multiplicative.toAdd (v.valuationOfNeZeroToFun a)
  simp only [HeightOneSpectrum.valuationOfNeZeroToFun, toAdd_ofAdd]
  ring

theorem UpperTheory.V.Kum.clProd :
    ∀ (K : Type) [Field K] [NumberField K], (∀ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ FractionalIdeal.count K v I.1) ∧
    (∀ (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ), FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = ordv v a) ∧ (∀ a : Kˣ, {v : HeightOneSpectrum (𝓞 K) | ordv v a ≠ 0}.Finite) ∧ ∀ a : Kˣ, radCl 1 a = 1 := by
  intro K _ _
  refine ⟨mk_eq_finprod K, count_eq_ordv K, fun a => ?_, fun a => ?_⟩
  · simp only [← count_eq_ordv]
    exact Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)
  · have h := mk_eq_finprod K (toPrincipalIdeal (𝓞 K) K a)
    rw [coe_toPrincipalIdeal] at h
    simp only [count_eq_ordv] at h
    simp only [radCl, Nat.cast_one, Int.ediv_one]
    rw [← h, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
    exact (FractionalIdeal.isPrincipal_iff _).2 ⟨_, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.resInfConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ) (τ : F ≃+* F) (σ : Ω ≃+* Ω), IsLift τ σ → ∀ (x : H1 (qzTw D e)) (u u' : Uinf F Ω l), (∀ y, u'.1 (σ y) = σ (u.1 y)) → resInf D e (galoisActionOnCohomology D e τ x) u' = twScal l σ e • resInf D e x u := by
  intro F Ω _ _ _ _ _ l _ D e τ σ h x u u' hu
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  have hc : conjGal h u'.1 = u.1 :=
    AlgEquiv.ext fun y => by rw [conjGal_apply, hu, RingEquiv.symm_apply_apply]
  rw [galois_action_cohomology_eq_conj D e h, e₁, resInf_mk, resInf_mk, f₁, conjGS_toGS, hc]
end
