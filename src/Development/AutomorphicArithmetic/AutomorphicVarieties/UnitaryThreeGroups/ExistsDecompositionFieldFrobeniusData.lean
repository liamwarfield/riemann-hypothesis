module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDecompositionFieldFrobeniusData
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DfExistsPrime
theorem UpperTheory.Reformulated.B.Qj5.df_exists_prime :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime_mul p a hp ih =>
    intro h0 h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨q, hq, hqa, hqv⟩ := ih (right_ne_zero_of_mul h0) h
      exact ⟨q, hq, Dvd.dvd.mul_left hqa p, hqv⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section SlopeTestRemainingChoices

open Formalism.GaloisCohomology

private theorem df_locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

private theorem df_exists_prime (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : n ≠ 0) (h : (n : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : 𝓞 ℚ) ∈ v.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qj5.df_exists_prime v n hn h

private theorem df_not_both (v : HeightOneSpectrum (𝓞 ℚ)) {a b : ℕ} (hab : a.Coprime b) (ha : (a : 𝓞 ℚ) ∈ v.asIdeal)
    (hb : (b : 𝓞 ℚ) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, h⟩ : IsCoprime (a : 𝓞 ℚ) (b : 𝓞 ℚ) := hab.cast
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ ha) (v.asIdeal.mul_mem_left _ hb)))

private theorem df_val {Ω : Type} [Field Ω] [CharZero Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h := hv ((n : ℕ) : 𝓞 ℚ)
  have e : algebraMap ℚ Ω (((n : ℕ) : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
  rw [e] at h
  exact h

private theorem df_order {q n m : ℕ} (hq : 1 < q) (hn : 0 < n) (hm : m + 1 = q ^ n) (u : (ZMod m)ˣ)
    (hu : (u : ZMod m) = q) : orderOf u = n := by
  rw [orderOf_eq_iff hn]
  refine ⟨Units.ext ?_, fun k hk hk0 h => ?_⟩
  · rw [Units.val_pow_eq_pow_val, hu, ← Nat.cast_pow, ← hm]
    simp
  · have h1 : ((q ^ k : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
      rw [Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h]
      simp
    have h2 : 1 < q ^ k := Nat.one_lt_pow hk0.ne' hq
    have h3 : q ^ k < q ^ n := Nat.pow_lt_pow_right hq hk
    have h4 := (Nat.modEq_iff_dvd' h2.le).1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1).symm
    have h5 := Nat.le_of_dvd (by omega) h4
    omega

private theorem df_frob (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : IsPlaceOver A v) (D I : Subgroup (G ℚ Ω)) (hD : D = Dec (F := ℚ) A) (hI : I = Ine (F := ℚ) A) :
    ∃ φ : D, (I.subgroupOf D ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧
      ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I.subgroupOf D, d s = 1) ∧
        d φ = Multiplicative.ofAdd 1 := by
  subst hD hI
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨γ, hγ⟩ := exists_isFrob hv
  refine ⟨⟨γ, hγ.1⟩, ?_, fun n hn => ?_⟩
  · have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω)
      ⟨(Ine (F := ℚ) A ⊔ Subgroup.zpowers γ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
    have h1 : Dec (F := ℚ) A ≤ (Ine (F := ℚ) A ⊔ Subgroup.zpowers γ).topologicalClosure := by
      refine le_trans (le_sInf ?_) key.ge
      rintro N ⟨hNo, hN⟩
      have h := (Subgroup.le_topologicalClosure _).trans hN
      exact Kum.decGen ℚ Ω A _ γ N hv hγ hNo (le_sup_left.trans h)
        (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers γ)))
    have h2 : ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔
        Subgroup.zpowers (⟨γ, hγ.1⟩ : Dec (F := ℚ) A)).map (Dec (F := ℚ) A).subtype =
        Ine (F := ℚ) A ⊔ Subgroup.zpowers γ := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers, inf_eq_left.2 (Ine_le_Dec A)]
      rfl
    rw [eq_top_iff]
    intro x _
    have h3 := h1 x.2
    rw [← h2] at h3
    exact closure_subtype.2 h3
  · have hq : normV v = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    have hq1 : 1 < normV v := by
      rw [hq]
      have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
      have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      omega
    have hqv : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := hq ▸ Ideal.absNorm_mem _
    obtain ⟨p, hp, hpq, hpv⟩ := df_exists_prime v _ (by omega) hqv
    haveI : Fact p.Prime := ⟨hp⟩
    have h1 : 1 < normV v ^ n := Nat.one_lt_pow hn.ne' hq1
    obtain ⟨m, hm⟩ : ∃ m, m + 1 = normV v ^ n := ⟨normV v ^ n - 1, by omega⟩
    haveI : NeZero m := ⟨by omega⟩
    have hmp : m.Coprime p := by
      refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_).symm
      have h2 : p ∣ m + 1 := hm ▸ hpq.trans (dvd_pow_self _ hn.ne')
      exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
    have hA := (df_val hv p).2 hpv
    obtain ⟨hopen, -, -, -, hIne⟩ := Chr.clsFacts ℚ Ω m
    have hI := hIne A fun h => df_not_both v hmp ((df_val hv m).1 h) hpv
    have hu : ((Chr.cls ℚ Ω m γ : (ZMod m)ˣ) : ZMod m) = normV v := by
      haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
      have hv1 : A.valuation ζ ≤ 1 := by
        have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
        exact ((pow_eq_one_iff_left (NeZero.ne m)).1 h1).le
      have h2 : γ ζ = ζ ^ normV v := by
        refine (LDataCardLeFinrank.ineFixRoots ℚ Ω p A hA m hmp (ζ ^ normV v) ?_).1 (γ ζ) ?_ (hγ.2 ζ hv1)
        · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
        · rw [← map_pow, hζ.pow_eq_one, map_one]
      rw [Chr.cls_spec m γ ζ hζ.pow_eq_one, pow_eq_pow_mod (normV v) hζ.pow_eq_one] at h2
      have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos m)) h2
      rw [← ZMod.natCast_zmod_val ((Chr.cls ℚ Ω m γ : (ZMod m)ˣ) : ZMod m), h3, ZMod.natCast_mod]
    have hord := df_order hq1 hn hm _ hu
    have hle : Dec (F := ℚ) A ≤ (Subgroup.zpowers (Chr.cls ℚ Ω m γ)).comap (Chr.cls ℚ Ω m) := by
      have hk : (Chr.cls ℚ Ω m).ker ≤ (Subgroup.zpowers (Chr.cls ℚ Ω m γ)).comap (Chr.cls ℚ Ω m) :=
        Subgroup.ker_le_comap _ _
      exact Kum.decGen ℚ Ω A _ γ _ hv hγ (Subgroup.isOpen_mono hk hopen) (hI.trans hk) (Subgroup.mem_zpowers _)
    let f : Dec (F := ℚ) A →* Subgroup.zpowers (Chr.cls ℚ Ω m γ) :=
      ((Chr.cls ℚ Ω m).comp (Dec (F := ℚ) A).subtype).codRestrict _ fun x => hle x.2
    have hg : ∀ x : Subgroup.zpowers (Chr.cls ℚ Ω m γ), x ∈ Subgroup.zpowers (f ⟨γ, hγ.1⟩) := by
      rintro ⟨_, k, rfl⟩
      exact ⟨k, rfl⟩
    have hc : Nat.card (Subgroup.zpowers (Chr.cls ℚ Ω m γ)) = n := by rw [Nat.card_zpowers, hord]
    have hf1 : ∀ s : Dec (F := ℚ) A, Chr.cls ℚ Ω m s = 1 → f s = 1 := fun s hs => Subtype.ext hs
    refine ⟨(zmodMulEquivOfGenerator hg hc).symm.toMonoidHom.comp f, df_locConst _ ?_, fun s hs => ?_, ?_⟩
    · refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω m).ker.subgroupOf _) (fun s hs => ?_)
        (hopen.preimage continuous_subtype_val)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf1 s hs, map_one]
    · rw [MonoidHom.comp_apply, hf1 s (hI hs), map_one]
    · exact zmodMulEquivOfGenerator_symm_apply_generator hg hc

end SlopeTestRemainingChoices

open Formalism.GaloisCohomology in
theorem UpperTheory.exists_decompositionField_frobenius_data :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v →
          CompactSpace (Dec (F := ℚ) A) ∧ ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A)).Normal ∧ IsClosed (Ine (F := ℚ) A : Set (G ℚ Ω)) ∧
          (∃ fr : Dec (F := ℚ) A, ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤) ∧
          ∀ n : ℕ, 0 < n → ∃ U : Subgroup (Dec (F := ℚ) A), IsOpen (U : Set (Dec (F := ℚ) A)) ∧ (Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ≤ U ∧ U.index = n := by
  intro Ω _ _ _ A v hv
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨φ, h1, h2⟩ := df_frob Ω A v hv _ _ rfl rfl
  refine ⟨isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact, inferInstance, isClosed_Ine A, ⟨φ, h1⟩,
    fun n hn => ?_⟩
  obtain ⟨d, hd, hI, hφ⟩ := h2 n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  refine ⟨d.ker, hd {1}, fun s hs => hI s hs, ?_⟩
  have hs : d.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine ⟨φ ^ (Multiplicative.toAdd x).val, ?_⟩
    rw [map_pow, hφ, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [Subgroup.index_ker, hs, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.InertiaLeNormalIffKerLeAndInertiaLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem valuation_natCast_lt_one_iff_mem_asIdeal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (hA : IsPlaceOver A v) :
    A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h := hA ((l : ℕ) : 𝓞 ℚ)
  simpa using h

theorem UpperTheory.inertia_le_normal_iff_ker_le_and_inertia_le :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S), ContainsAbove S l → (∀ v, IsPlaceOver (A v) v.1) →
          (∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀) → ∀ (H : Subgroup (G ℚ Ω)) [H.Normal], (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker ≤ H →
          ∀ (M : Subgroup (G ℚ Ω)) [M.Normal], IsClosed (M : Set (G ℚ Ω)) →
          ((∀ g, (∃ A' : ValuationSubring Ω, ¬ A'.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A' ∧ g ∈ H) → g ∈ M) ↔
            ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker ≤ M ∧ ∀ v : S, v ≠ v₀ → Ine (F := ℚ) (A v) ⊓ H ≤ M)) := by
  intro Ω _ _ _ l _ S A v₀ hS hA hv₀ H _ hH M _ hM
  have hker : (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker = NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    simp [toGS, QuotientGroup.ker_mk']
  have hin : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 ℚ)), w ∉ (S : Set (HeightOneSpectrum (𝓞 ℚ))) →
      IsPlaceOver B w → (Ine (F := ℚ) B : Set (G ℚ Ω)) ⊆ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro B w hw hB g hg
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion]
    exact ⟨w, hw, B, hB, hg⟩
  constructor
  · intro h
    constructor
    · rw [hker]
      apply Subgroup.topologicalClosure_minimal _ _ hM
      apply Subgroup.normalClosure_le_normal
      intro g hg
      simp only [Set.mem_iUnion] at hg
      obtain ⟨w, hw, B, hB, hgB⟩ := hg
      have hgI : g ∈ Ine (F := ℚ) B := hgB
      apply h g
      refine ⟨B, ?_, hgI, ?_⟩
      · rw [valuation_natCast_lt_one_iff_mem_asIdeal l B w hB]
        intro hl
        exact hw (by simpa using hS w hl)
      · apply hH
        rw [hker]
        exact hin B w hw hB hgI
    · intro v hv g hg
      rw [Subgroup.mem_inf] at hg
      apply h g
      refine ⟨A v, ?_, hg.1, hg.2⟩
      rw [valuation_natCast_lt_one_iff_mem_asIdeal l (A v) v.1 (hA v), hv₀]
      exact hv
  · rintro ⟨h1, h2⟩ g ⟨B, hBl, hgB, hgH⟩
    by_cases hBt : B = ⊤
    · subst hBt
      rw [(Kum.placeDict ℚ Ω).1] at hgB
      rw [Subgroup.mem_bot] at hgB
      subst hgB
      exact M.one_mem
    obtain ⟨w, hw⟩ := (Kum.placeDict ℚ Ω).2.1 B hBt
    by_cases hwS : w ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    · let u : S := ⟨w, hwS⟩
      have hu0 : u ≠ v₀ := by
        intro hu
        rw [← hv₀ u] at hu
        exact hBl ((valuation_natCast_lt_one_iff_mem_asIdeal l B w hw).2 hu)
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hA u) hw
      rw [← hσ] at hgB
      have hc : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (A u) := ((ML.placeBasic Ω).2.2.2.2.2.2.2.2.2 (A u) σ).2.1 g |>.1 hgB
      have hcH : σ⁻¹ * g * σ ∈ H := by
        have := ‹H.Normal›.conj_mem g hgH σ⁻¹
        simpa [mul_assoc] using this
      have hcM := h2 u hu0 (Subgroup.mem_inf.2 ⟨hc, hcH⟩)
      have := ‹M.Normal›.conj_mem _ hcM σ
      simpa [mul_assoc] using this
    · apply h1
      rw [hker]
      exact hin B w hwS hw hgB
end
