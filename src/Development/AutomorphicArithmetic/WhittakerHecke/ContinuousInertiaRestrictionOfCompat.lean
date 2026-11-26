module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlace
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotientEqOfPowSubSelfMemStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ContinuousInertiaRestrictionOfCompat
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

theorem UpperTheory.continuous_inertia_restriction_of_compat :
    ∀ {E L Ω : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Field Ω] [Algebra E L] [Algebra E Ω] [Algebra L Ω]
        [IsScalarTower E L Ω] (A : ValuationSubring Ω) (ι : Ine (F := E) A →* Ine (F := L) A),
        (∀ (t : Ine (F := E) A) (x : Ω), (ι t : G L Ω) x = (t : G E Ω) x) → Continuous ι := by
  intro E L Ω _ _ _ _ _ _ _ _ _ A ι hι
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  apply continuous_of_continuousAt_one ι
  rw [ContinuousAt, map_one, tendsto_subtype_rng, Filter.tendsto_def]
  intro s hs
  rw [OneMemClass.coe_one] at hs
  obtain ⟨K, hK, hKs⟩ := (krullTopology_mem_nhds_one_iff L Ω s).mp hs
  haveI : FiniteDimensional E K := Module.Finite.trans L K
  haveI : FiniteDimensional E (K.restrictScalars E) := inferInstanceAs (FiniteDimensional E K)
  have hopen := (K.restrictScalars E).fixingSubgroup_isOpen
  refine Filter.mem_of_superset ((hopen.preimage continuous_subtype_val).mem_nhds ?_) ?_
  · exact (K.restrictScalars E).fixingSubgroup.one_mem
  · intro t ht
    apply hKs
    rw [Set.mem_preimage, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at ht
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hι]
    exact ht x ((IntermediateField.mem_restrictScalars E).mpr hx)
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ExistsAdicCompletionRingEquivExtendingOfStable
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

private lemma intValuation_le_of_equiv {L : Type} [Field L] [NumberField L]
    (u : HeightOneSpectrum (𝓞 L)) (σ : 𝓞 L ≃+* 𝓞 L)
    (h : ∀ x : 𝓞 L, σ x ∈ u.asIdeal ↔ x ∈ u.asIdeal) (r : 𝓞 L) :
    u.intValuation (σ r) ≤ u.intValuation r := by
  by_cases hr : r = 0
  · simp [hr]
  have hc : Ideal.comap (σ : 𝓞 L →+* 𝓞 L) u.asIdeal = u.asIdeal := by
    ext x; exact h x
  have hm : ∀ n : ℕ, Ideal.comap (σ : 𝓞 L →+* 𝓞 L) (u.asIdeal ^ n) = u.asIdeal ^ n := fun n => by
    have e : Ideal.comap (σ : 𝓞 L →+* 𝓞 L) (u.asIdeal ^ n) =
        Ideal.map (σ.symm : 𝓞 L →+* 𝓞 L) (u.asIdeal ^ n) := Ideal.comap_symm (I := u.asIdeal ^ n) σ.symm
    have e1 : Ideal.map (σ.symm : 𝓞 L →+* 𝓞 L) u.asIdeal = u.asIdeal := by
      have e2 : Ideal.comap (σ : 𝓞 L →+* 𝓞 L) u.asIdeal =
          Ideal.map (σ.symm : 𝓞 L →+* 𝓞 L) u.asIdeal := Ideal.comap_symm (I := u.asIdeal) σ.symm
      rw [← e2, hc]
    rw [e, Ideal.map_pow, e1]
  rw [HeightOneSpectrum.intValuation_if_neg u hr]
  have hmem : r ∈ u.asIdeal ^ ((Associates.mk u.asIdeal).count
      (Associates.mk (Ideal.span {r})).factors) := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_if_neg u hr]
  have hmem' : σ r ∈ u.asIdeal ^ ((Associates.mk u.asIdeal).count
      (Associates.mk (Ideal.span {r})).factors) := by
    have := hm ((Associates.mk u.asIdeal).count (Associates.mk (Ideal.span {r})).factors)
    rw [← this] at hmem
    exact hmem
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem u _ _).2 hmem'

private lemma intValuation_eq_of_equiv {L : Type} [Field L] [NumberField L]
    (u : HeightOneSpectrum (𝓞 L)) (σ : 𝓞 L ≃+* 𝓞 L)
    (h : ∀ x : 𝓞 L, σ x ∈ u.asIdeal ↔ x ∈ u.asIdeal) (r : 𝓞 L) :
    u.intValuation (σ r) = u.intValuation r := by
  refine le_antisymm (intValuation_le_of_equiv u σ h r) ?_
  have h' : ∀ x : 𝓞 L, σ.symm x ∈ u.asIdeal ↔ x ∈ u.asIdeal := fun x => by
    rw [← h (σ.symm x), σ.apply_symm_apply]
  simpa using intValuation_le_of_equiv u σ.symm h' (σ r)

private lemma valuation_eq_of_equiv {L : Type} [Field L] [NumberField L]
    (u : HeightOneSpectrum (𝓞 L)) (s : L ≃+* L)
    (h : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom (s : L →+* L) x ∈ u.asIdeal ↔ x ∈ u.asIdeal) (y : L) :
    u.valuation L (s y) = u.valuation L y := by
  let σ : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv s
  have hσ : ∀ x : 𝓞 L, σ x ∈ u.asIdeal ↔ x ∈ u.asIdeal := fun x => h x
  have key : ∀ a : 𝓞 L, u.valuation L (s (algebraMap (𝓞 L) L a)) =
      u.valuation L (algebraMap (𝓞 L) L a) := fun a => by
    have e : s (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L (σ a) := rfl
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      intValuation_eq_of_equiv u σ hσ]
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) y
  rw [map_div₀, map_div₀, map_div₀, key, key]

open scoped WithZeroTopology in
theorem UpperTheory.exists_adicCompletion_ringEquiv_extending_of_stable :
    ∀ {L : Type} [Field L] [NumberField L] (u : HeightOneSpectrum (𝓞 L)) (s : L ≃+* L),
        (∀ x : 𝓞 L, RingOfIntegers.mapRingHom (s : L →+* L) x ∈ u.asIdeal ↔ x ∈ u.asIdeal) →
        ∃ i : u.adicCompletion L ≃+* u.adicCompletion L, Continuous i ∧
          (∀ x, i (algebraMap L _ x) = algebraMap L _ (s x)) ∧ ∀ x, Valued.v (i x) = Valued.v x := by
  intro L _ _ u s h
  have h' : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom (s.symm : L →+* L) x ∈ u.asIdeal ↔ x ∈ u.asIdeal := by
    intro x
    rw [← h (RingOfIntegers.mapRingHom (s.symm : L →+* L) x)]
    have e : RingOfIntegers.mapRingHom (s : L →+* L) (RingOfIntegers.mapRingHom (s.symm : L →+* L) x) = x := by
      apply RingOfIntegers.ext
      simp
    rw [e]
  obtain ⟨μ, hμc, hμ⟩ := GlobalTheory.CompositumCompletion.exists_completion_map (s : L →+* L) u u h
  obtain ⟨μ', hμ'c, hμ'⟩ := GlobalTheory.CompositumCompletion.exists_completion_map (s.symm : L →+* L) u u h'
  have h1 : ∀ a, μ' (μ a) = a := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap L u).equalizer (hμ'c.comp hμc) continuous_id
      (funext fun x => by simp [hμ, hμ'])) a
  have h2 : ∀ a, μ (μ' a) = a := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap L u).equalizer (hμc.comp hμ'c) continuous_id
      (funext fun x => by simp [hμ, hμ'])) a
  let i : u.adicCompletion L ≃+* u.adicCompletion L :=
    { μ with invFun := μ', left_inv := h1, right_inv := h2 }
  have hi : ∀ a, i a = μ a := fun _ => rfl
  refine ⟨i, hμc, fun x => hμ x, fun x => ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap L u).induction_on
    (p := fun x => Valued.v (i x) = Valued.v x) x
    (isClosed_eq
      ((Valued.continuous_valuation_of_surjective (u.valuedAdicCompletion_surjective L)).comp hμc)
      (Valued.continuous_valuation_of_surjective (u.valuedAdicCompletion_surjective L))) fun k => ?_
  rw [hi, hμ]
  have e : ∀ y : L, Valued.v (algebraMap L (u.adicCompletion L) y) = u.valuation L y := fun y =>
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u y)
  rw [e, e]
  exact valuation_eq_of_equiv u s h k
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ExistsUnitResidueLogarithmOfRootsOfUnity
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

private theorem one_add_pow_expansion' {R : Type} [CommRing R] (z : R) (N : ℕ) :
    ∃ r : R, (1 + z) ^ N = 1 + N * z + z ^ 2 * r := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨n + r + z * r, ?_⟩
    rw [pow_succ, hr]; push_cast; ring

theorem UpperTheory.exists_unit_residue_logarithm_of_roots_of_unity :
    ∀ {C Γ K : Type} [Field C] [LinearOrderedCommGroupWithZero Γ] [Field K] (v : Valuation C Γ) (ϖ : C),
        ϖ ≠ 0 → v ϖ < 1 → (∀ x, v x < 1 → v x ≤ v ϖ) → ∀ (ρ : v.valuationSubring →+* K), Function.Surjective ρ →
        (∀ x : v.valuationSubring, ρ x = 0 ↔ v (x : C) < 1) → ∀ N : ℕ, 0 < N → (∀ z : K, z ≠ 0 → z ^ N = 1) → (N : K) = -1 →
        ∃ abelian₂ : Cˣ → K,
          (∀ a b : Cˣ, v (a : C) = 1 → v (b : C) = 1 → abelian₂ (a * b) = abelian₂ a + abelian₂ b) ∧
          (∀ y : K, ∃ a : Cˣ, v (a : C) = 1 ∧ abelian₂ a = y) ∧
          (∀ a : Cˣ, v ((a : C) - 1) < v ϖ → abelian₂ a = 0) ∧
          ∀ (i : C ≃+* C) (f : K ≃+* K), i ϖ = ϖ → (∀ x, v (i x) = v x) →
            (∀ (x y : v.valuationSubring), (y : C) = i x → ρ y = f (ρ x)) →
            ∀ a : Cˣ, v (a : C) = 1 → abelian₂ (Units.map i.toRingHom.toMonoidHom a) = f (abelian₂ a) := by
  intro C Γ K _ _ _ v ϖ h0 h1 hmax ρ hsurj hker N hN hpow hNK
  classical
  have hv0 : v ϖ ≠ 0 := by simpa using h0
  have hvpos : 0 < v ϖ := zero_lt_iff.mpr hv0
  let abelian₂ : Cˣ → K := fun a =>
    if hy : ((a : C) ^ N - 1) / ϖ ∈ v.valuationSubring then ρ ⟨_, hy⟩ else 0
  have hlt : ∀ a : C, v a = 1 → v (a ^ N - 1) < 1 := by
    intro a ha
    have hm : a ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]; exact ha.le
    have hne : ρ ⟨a, hm⟩ ≠ 0 := by
      intro h
      have := (hker _).1 h
      simp [ha] at this
    have h2 : ρ ((⟨a, hm⟩ : v.valuationSubring) ^ N - 1) = 0 := by
      rw [map_sub, map_pow, hpow _ hne, map_one, sub_self]
    have := (hker _).1 h2
    simpa using this
  have hint : ∀ a : C, v a = 1 → (a ^ N - 1) / ϖ ∈ v.valuationSubring := by
    intro a ha
    rw [Valuation.mem_valuationSubring_iff, map_div₀, div_le_one₀ hvpos]
    exact hmax _ (hlt a ha)
  have key : ∀ (a : Cˣ) (y : v.valuationSubring), (y : C) = ((a : C) ^ N - 1) / ϖ → abelian₂ a = ρ y := by
    intro a y hy
    have hm : ((a : C) ^ N - 1) / ϖ ∈ v.valuationSubring := hy ▸ y.2
    simp only [abelian₂, dif_pos hm]
    congr 1
    exact Subtype.ext hy.symm
  have hϖm : ϖ ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]; exact h1.le
  have hρϖ : ρ ⟨ϖ, hϖm⟩ = 0 := (hker _).2 h1
  refine ⟨abelian₂, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    have hbm : (b : C) ^ N - 1 ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]; exact (hlt _ hb).le
    have hb0 : ρ ⟨_, hbm⟩ = 0 := (hker _).2 (hlt _ hb)
    rw [key a ⟨_, hint _ ha⟩ rfl, key b ⟨_, hint _ hb⟩ rfl,
      key (a * b) (⟨_, hint _ ha⟩ + ⟨_, hint _ hb⟩ + ⟨_, hint _ ha⟩ * ⟨_, hbm⟩) ?_]
    · rw [map_add (f := _), map_add (f := _), map_mul, hb0, mul_zero, add_zero]
    · push_cast
      field_simp
      ring
  · intro y
    obtain ⟨x, hx⟩ := hsurj (-y)
    have hx1 : v (x : C) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 x.2
    have hz : v (ϖ * x) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hx1) h1
    have ha : v (1 + ϖ * x) = 1 := v.map_one_add_of_lt hz
    have hne : (1 + ϖ * x : C) ≠ 0 := by
      intro h
      rw [h] at ha
      simp at ha
    obtain ⟨r, hr⟩ := one_add_pow_expansion' ((⟨ϖ, hϖm⟩ : v.valuationSubring) * x) N
    have hr' : (1 + ϖ * x : C) ^ N = 1 + N * (ϖ * x) + (ϖ * x) ^ 2 * r := by
      have := congrArg (fun t : v.valuationSubring => (t : C)) hr
      simpa using this
    refine ⟨Units.mk0 _ hne, ha, ?_⟩
    rw [key _ ((N : v.valuationSubring) * x + ⟨ϖ, hϖm⟩ * (x ^ 2 * r)) ?_]
    · rw [map_add (f := _), map_mul, map_mul, hρϖ, map_natCast, hNK, hx]; ring
    · rw [Units.val_mk0, hr']
      push_cast
      field_simp
      ring
  · intro a ha
    have ha1 : v (a : C) = 1 := by
      have := v.map_one_add_of_lt (lt_trans ha h1)
      simpa using this
    rw [key a ⟨_, hint _ ha1⟩ rfl, hker]
    have ham : (a : C) ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]; exact ha1.le
    obtain ⟨s, hs⟩ := sub_one_dvd_pow_sub_one (⟨_, ham⟩ : v.valuationSubring) N
    have hs' : (a : C) ^ N - 1 = ((a : C) - 1) * s := by
      have := congrArg (fun t : v.valuationSubring => (t : C)) hs
      simpa using this
    have hs1 : v (s : C) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 s.2
    show v (((a : C) ^ N - 1) / ϖ) < 1
    rw [map_div₀, div_lt_one₀ hvpos, hs', map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hs1) ha
  · intro i f hi hv hf a ha
    have hia : v ((Units.map i.toRingHom.toMonoidHom a : Cˣ) : C) = 1 := by
      show v (i a) = 1
      rw [hv, ha]
    rw [key a ⟨_, hint _ ha⟩ rfl, key _ ⟨_, hint _ hia⟩ rfl]
    apply hf
    show ((i a) ^ N - 1) / ϖ = i (((a : C) ^ N - 1) / ϖ)
    rw [map_div₀, map_sub, map_pow, map_one, hi]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ExistsNumberFieldExtensionPlaceFrobeniusDegree
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

theorem UpperTheory.exists_numberField_extension_place_frobenius_degree :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
        (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (n : ℕ), 2 ≤ n → ∀ (φ : G E Ω), IsFrob A (normV w) φ →
        ∀ (c : 𝓞 E), c ∉ w.asIdeal ^ 2 →
        ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra E L) (_ : Algebra L Ω) (_ : IsScalarTower E L Ω)
          (_ : IsAlgClosure L Ω) (u : HeightOneSpectrum (𝓞 L)) (_ : IsPlaceOver A u) (s : L ≃ₐ[E] L),
          (∀ x : L, φ (algebraMap L Ω x) = algebraMap L Ω (s x)) ∧
          (∀ t ∈ Ine (F := E) A, ∀ x : L, t (algebraMap L Ω x) = algebraMap L Ω x) ∧
          algebraMap (𝓞 E) (𝓞 L) c ∉ u.asIdeal ^ 2 ∧ normV u = normV w ^ n := by
  classical
  intro E Ω _ _ _ _ _ A w h n hn φ hφ c hc
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hfinw : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have hq2 : 2 ≤ normV w := Finite.one_lt_card (α := 𝓞 E ⧸ w.asIdeal)
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = normV w := ⟨_, rfl⟩
  rw [← hqdef] at hφ hq2 ⊢
  have hqw : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal :=
    DiscreteGroups.sglob.DzType.natCast_mem_of_normV w q 1 one_pos (by rw [pow_one, hqdef])
  have hqΩ : A.valuation ((q : ℕ) : Ω) < 1 := by
    have := (h ((q : ℕ) : 𝓞 E)).mpr hqw
    simpa using this
  have hQ4 : 4 ≤ q ^ n := by
    have h2 : q ^ 2 ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
    nlinarith
  have hQΩ : A.valuation ((q ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, Valuation.map_pow]
    exact pow_lt_one₀ zero_le hqΩ (by omega)
  have hN1 : A.valuation (((q ^ n - 1 : ℕ)) : Ω) = 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, ← neg_sub, Valuation.map_neg,
      Valuation.map_one_sub_of_lt _ hQΩ]
  have hN' : ¬ A.valuation (((q ^ n - 1 : ℕ)) : Ω) < 1 := by
    rw [hN1]; exact lt_irrefl 1
  haveI : NeZero (((q ^ n - 1 : ℕ)) : Ω) := ⟨by exact_mod_cast (show q ^ n - 1 ≠ 0 by omega)⟩
  haveI : NeZero (q ^ n - 1) := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q ^ n - 1)
  have hζ1 : A.valuation ζ = 1 := ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A (by omega) hζ.pow_eq_one
  have hζA : A.valuation ζ ≤ 1 := hζ1.le
  let f : ℤ[X] := X ^ (q ^ n - 1) - C 1
  have hf : f.Monic := monic_X_pow_sub_C 1 (by omega)
  have hfζ : aeval ζ f = 0 := by simp [f, hζ.pow_eq_one]
  have hder : ¬ A.valuation (aeval ζ (derivative f)) < 1 := by
    simp only [f]
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, aeval_C, map_pow, aeval_X,
      Valuation.map_mul, Valuation.map_pow, hζ1, one_pow, mul_one]
    have e : algebraMap ℤ Ω (((q ^ n - 1 : ℕ) : ℤ)) = (((q ^ n - 1 : ℕ)) : Ω) := by simp
    rw [e, hN1]
    exact lt_irrefl 1
  have hζE : IsIntegral E ζ := Algebra.IsIntegral.isIntegral ζ
  let L := IntermediateField.adjoin E ({ζ} : Set Ω)
  have hfd : FiniteDimensional E L := IntermediateField.adjoin.finiteDimensional hζE
  have : FiniteDimensional ℚ L := Module.Finite.trans E L
  haveI hNF : NumberField L := ⟨⟩
  haveI hAC' : IsAlgClosure L Ω := ⟨hAC, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  haveI hcyc : IsCyclotomicExtension {q ^ n - 1} E L := hζ.intermediateField_adjoin_isCyclotomicExtension E
  haveI hgal : IsGalois E L := IsCyclotomicExtension.isGalois {q ^ n - 1} E L

  have hroot : ∀ τ : Ω ≃ₐ[E] Ω, τ ∈ ReciprocityTheory.Gal.Dec (F := E) A → A.valuation (τ ζ - ζ) < 1 → τ ζ = ζ := by
    intro τ hτ hlt
    have hτA : A.valuation (τ ζ) ≤ 1 := by
      rw [A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hτ, ← A.valuation_le_one_iff]
      exact hζA
    refine (GlobalTheory.T.eq_of_roots_congr_of_derivative_unit A f ζ (τ ζ) hζA hτA hfζ (GlobalTheory.UnrCycExt.aeval_apply_eq_zero τ f hfζ) hder ?_).symm
    rw [Valuation.map_sub_swap]; exact hlt
  have hine : ∀ t ∈ Ine (F := E) A, ∀ x : L, t (algebraMap L Ω x) = algebraMap L Ω x := by
    intro t ht e
    have htζ : t ζ = ζ := hroot t ht.1 (ht.2 ζ hζA)
    exact GlobalTheory.UnrCycExt.fix_adjoin ζ hζE t htζ _ e.2
  have hφn : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation ((φ ^ n) x - x ^ (q ^ n)) < 1 :=
    GlobalTheory.T.frobenius_pow_apply_sub_pow_lt_one A q φ hφ n
  have hφD : φ ^ n ∈ ReciprocityTheory.Gal.Dec (F := E) A := Subgroup.pow_mem _ hφ.1 n
  have hζQ : ζ ^ (q ^ n) = ζ := by
    rw [show q ^ n = (q ^ n - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  have hφζ : (φ ^ n) ζ = ζ := by
    refine hroot _ hφD ?_
    have := hφn ζ hζA
    rwa [hζQ] at this
  have hfix : ∀ x ∈ L, (φ ^ n) x = x := GlobalTheory.UnrCycExt.fix_adjoin ζ hζE (φ ^ n) hφζ
  have hpowq : ∀ y : 𝓞 L, A.valuation (algebraMap L Ω ((y : L) ^ (q ^ n) - (y : L))) < 1 := by
    intro y
    have hyA := GlobalTheory.UnrCycExt.val_le_one_of_int A y
    have := hφn _ hyA
    have hy2 : (φ ^ n) (algebraMap L Ω (y : L)) = algebraMap L Ω (y : L) := hfix _ (y : L).2
    rw [hy2] at this
    rw [map_sub, map_pow, Valuation.map_sub_swap]
    exact this

  have hq0 : ((q : ℕ) : 𝓞 L) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hqv : A.valuation (algebraMap L Ω (((q : ℕ) : 𝓞 L) : L)) < 1 := by
    simpa using hqΩ
  let u := GlobalTheory.UnrCycExt.placeBelow L A ((q : ℕ) : 𝓞 L) hq0 hqv
  have hu : IsPlaceOver A u := GlobalTheory.UnrCycExt.isPlaceOver_placeBelow L A _ hq0 hqv
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζL : IsPrimitiveRoot ζL (q ^ n - 1) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L Ω) hζ (algebraMap L Ω).injective
  have hζint : IsIntegral ℤ ζL := hζL.isIntegral (by omega)
  let ζ' : 𝓞 L := ⟨ζL, hζint⟩
  refine ⟨L, inferInstance, hNF, inferInstance, inferInstance, inferInstance, hAC', u, hu,
    AlgEquiv.restrictNormal φ L, ?_, hine, ?_, ?_⟩
  · intro x
    exact (AlgEquiv.restrictNormal_commutes φ L x).symm
  · have hmap : ∀ p : ℤ[X], algebraMap L Ω ((aeval ζ' p : 𝓞 L) : L) = aeval ζ p := by
      intro p
      have h1 : ((aeval ζ' p : 𝓞 L) : L) = aeval (ζ' : L) p :=
        (Polynomial.aeval_algebraMap_apply L ζ' p).symm
      rw [h1, ← Polynomial.aeval_algebraMap_apply]
      rfl
    have hfζ' : aeval ζ' f = 0 := by
      have h2 := hmap f
      rw [hfζ, ← map_zero (algebraMap L Ω)] at h2
      exact_mod_cast (algebraMap L Ω).injective h2
    have hover : ∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) x ∈ u.asIdeal ↔ x ∈ w.asIdeal := by
      intro x
      rw [← h x]
      show A.valuation (algebraMap L Ω ((algebraMap (𝓞 E) (𝓞 L) x : 𝓞 L) : L)) < 1 ↔ _
      rw [show ((algebraMap (𝓞 E) (𝓞 L) x : 𝓞 L) : L) = algebraMap E L (x : E) from rfl,
        ← IsScalarTower.algebraMap_apply]
    have hder' : aeval ζ' (derivative f) ∉ u.asIdeal := fun hm => hder (by
      rw [← hmap]; exact hm)
    exact GlobalTheory.T.algebraMap_not_mem_sq_of_derivative_not_mem E L w u ζ' f hf hfζ' (GlobalTheory.UnrCycExt.adjoin_gen_eq_top E ζ hζE) hover hder' c hc
  · show Nat.card (𝓞 L ⧸ u.asIdeal) = q ^ n
    haveI : u.asIdeal.IsMaximal := u.isMaximal
    refine GlobalTheory.T.card_quotient_eq_of_pow_sub_self_mem' u.asIdeal (q ^ n) ζ' (by omega) ?_ ?_ ?_
    · apply Subtype.ext
      exact hζL.pow_eq_one
    · intro j hj0 hjq hm
      have hm1 : A.valuation (algebraMap L Ω (algebraMap (𝓞 L) L (ζ' ^ j - 1))) < 1 := hm
      rw [map_sub, map_pow, map_one, map_sub, map_pow, map_one] at hm1
      have hm' : A.valuation (ζ ^ j - 1) < 1 := hm1
      have := ReciprocityTheory.Gal.eq_of_pow_eq_one A hN'
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (one_pow _) hm'
      have hd := hζ.dvd_of_pow_eq_one j this
      exact absurd (Nat.le_of_dvd hj0 hd) (by omega)
    · intro y
      have := hpowq y
      show A.valuation (algebraMap L Ω (((y ^ (q ^ n) - y : 𝓞 L)) : L)) < 1
      simpa using this
end
