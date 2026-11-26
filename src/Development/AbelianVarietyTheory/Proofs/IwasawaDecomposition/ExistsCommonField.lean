module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.LogRdSum
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WeightCongruences.ProdResidueCharNormOneUnitEqOne
open NumberField IsDedekindDomain
open scoped Pointwise

private theorem exists_nat_residue {L : Type} [Field L] [NumberField L] {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) (hn : Ideal.absNorm v.asIdeal = p)
    (x : 𝓞 L) : ∃ a : ℕ, Ideal.Quotient.mk v.asIdeal x = (a : 𝓞 L ⧸ v.asIdeal) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : CharP (𝓞 L ⧸ v.asIdeal) p := (CharP.charP_iff_prime_eq_zero hp).2 (by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hv)
  have hcard : Nat.card (𝓞 L ⧸ v.asIdeal) = p := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hn]
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) (𝓞 L ⧸ v.asIdeal)) :=
    (ZMod.castHom (dvd_refl p) _).injective
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])
  obtain ⟨k, hk⟩ := hbij.2 (Ideal.Quotient.mk v.asIdeal x)
  refine ⟨k.val, ?_⟩
  rw [← hk, ZMod.castHom_apply, ZMod.natCast_val]

private theorem smul_natCast_eq {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (n : ℕ) :
    σ • (n : 𝓞 L) = n :=
  map_natCast (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) σ) n

private theorem stab_trivial {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (hn : Ideal.absNorm w.asIdeal = p) (h2 : ((p : ℕ) : 𝓞 L) ∉ w.asIdeal ^ 2)
    (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal) : σ = 1 := by
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  haveI := w.isPrime
  let Q := w.under (𝓞 K)
  haveI := Q.isPrime
  haveI := Q.isMaximal
  haveI : w.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hin : σ ∈ w.asIdeal.inertia (L ≃ₐ[K] L) := by
    intro x
    obtain ⟨a, ha⟩ := exists_nat_residue hp w hv hn x
    have h1 : x - (a : 𝓞 L) ∈ w.asIdeal := by
      rw [← Ideal.Quotient.eq, ha, map_natCast]
    have h3 : σ • (x - (a : 𝓞 L)) ∈ w.asIdeal := by
      rw [← hσ]; exact Ideal.smul_mem_pointwise_smul _ _ _ h1
    rw [smul_sub, smul_natCast_eq] at h3
    have h4 := w.asIdeal.sub_mem h3 h1
    rw [sub_sub_sub_cancel_right] at h4
    exact h4
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx Q.asIdeal w.asIdeal Q.ne_bot]
    apply Ideal.ramificationIdx'_spec
    · rw [pow_one]; exact Ideal.map_le_iff_le_comap.2 le_rfl
    · intro h
      apply h2
      have h1 : ((p : ℕ) : 𝓞 K) ∈ Q.asIdeal := by
        show ((p : ℕ) : 𝓞 K) ∈ Ideal.under (𝓞 K) w.asIdeal
        rw [Ideal.mem_under, map_natCast]; exact hv
      have h5 := h (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) h1)
      rwa [map_natCast] at h5
  have hc : Nat.card (w.asIdeal.inertia (L ≃ₐ[K] L)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn Q.asIdeal w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal w.asIdeal (L ≃ₐ[K] L), he]
  rw [Subgroup.card_eq_one.1 hc] at hin
  exact Subgroup.mem_bot.1 hin

theorem UpperTheory.prod_residue_char_norm_one_unit_eq_one :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (p : ℕ), p.Prime →
      ∀ (Q : HeightOneSpectrum (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∈ S ↔ w.under (𝓞 K) = Q) →
      (∀ w ∈ S, Ideal.absNorm w.asIdeal = p ∧ ((p : ℕ) : 𝓞 L) ∉ w.asIdeal ^ 2) →
      ∀ (ω : (ZMod p)ˣ →* ℂˣ) (θ : ∀ w : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ),
      (∀ w ∈ S, ∀ (a : ℕ) (ha : a.Coprime p), ∃ b : (𝓞 L ⧸ w.asIdeal)ˣ,
        (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) ∧ θ w b = ω (ZMod.unitOfCoprime a ha)) →
      ∀ u : (𝓞 L)ˣ, Algebra.norm K ((u : 𝓞 L) : L) = 1 →
        ∏ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom u) = 1 := by
  intro K L _ _ _ _ _ _ p hp Q S memS hs ω θ hθ ζ hζ
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have overp : ∀ w ∈ S, ((p : ℕ) : 𝓞 L) ∈ w.asIdeal := by
    intro w hw
    rw [← (hs w hw).1]
    exact Ideal.absNorm_mem _
  rcases S.eq_empty_or_nonempty with hE | ⟨w₀, hw₀⟩
  · rw [hE, Finset.prod_empty]

  have hres : ∀ w ∈ S, ∃ a : ℕ, Ideal.Quotient.mk w.asIdeal (ζ : 𝓞 L) = (a : 𝓞 L ⧸ w.asIdeal) := fun w hw =>
    exists_nat_residue hp w (overp w hw) (hs w hw).1 _
  choose! a ha using hres
  have hcop : ∀ w ∈ S, (a w).Coprime p := by
    intro w hw
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_)
    have h0 : ((a w : ℕ) : 𝓞 L ⧸ w.asIdeal) = 0 := by
      obtain ⟨c, hc⟩ := hd
      rw [hc, Nat.cast_mul, ← map_natCast (Ideal.Quotient.mk w.asIdeal) p,
        Ideal.Quotient.eq_zero_iff_mem.2 (overp w hw), zero_mul]
    have hu : IsUnit (Ideal.Quotient.mk w.asIdeal (ζ : 𝓞 L)) := ζ.isUnit.map _
    rw [ha w hw, h0] at hu
    haveI : w.asIdeal.IsMaximal := w.isMaximal
    exact not_isUnit_zero hu

  have hσ : ∀ w ∈ S, ∃ σ : L ≃ₐ[K] L, σ • w.asIdeal = w₀.asIdeal := by
    intro w hw
    haveI := w.isPrime
    haveI := w₀.isPrime
    haveI : w.asIdeal.LiesOver Q.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal ((memS w).1 hw).symm⟩
    haveI : w₀.asIdeal.LiesOver Q.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal ((memS w₀).1 hw₀).symm⟩
    exact Ideal.exists_smul_eq_of_isGaloisGroup Q.asIdeal w.asIdeal w₀.asIdeal (L ≃ₐ[K] L)
  choose! σ hσw using hσ

  have hσres : ∀ w ∈ S, Ideal.Quotient.mk w₀.asIdeal (σ w • (ζ : 𝓞 L)) = (a w : 𝓞 L ⧸ w₀.asIdeal) := by
    intro w hw
    have h1 : (ζ : 𝓞 L) - (a w : 𝓞 L) ∈ w.asIdeal := by
      rw [← Ideal.Quotient.eq, ha w hw, map_natCast]
    have h2 : σ w • ((ζ : 𝓞 L) - (a w : 𝓞 L)) ∈ w₀.asIdeal := by
      rw [← hσw w hw]; exact Ideal.smul_mem_pointwise_smul _ _ _ h1
    rw [smul_sub, smul_natCast_eq] at h2
    rw [← map_natCast (Ideal.Quotient.mk w₀.asIdeal)]
    exact Ideal.Quotient.eq.2 h2

  have hprod : ∏ w ∈ S, σ w • (ζ : 𝓞 L) = 1 := by
    have hre : ∏ w ∈ S, σ w • (ζ : 𝓞 L) = ∏ τ : L ≃ₐ[K] L, τ • (ζ : 𝓞 L) := by
      refine Finset.prod_bij (fun w _ => σ w) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro w₁ h₁ w₂ h₂ h'
        apply HeightOneSpectrum.ext
        rw [eq_inv_smul_iff.2 (hσw w₁ h₁), eq_inv_smul_iff.2 (hσw w₂ h₂), h']
      · intro τ _
        haveI := w₀.isPrime
        have hne : τ⁻¹ • w₀.asIdeal ≠ ⊥ := by
          intro h
          apply w₀.ne_bot
          rw [← smul_inv_smul τ w₀.asIdeal, h]
          ext x
          simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        let w : HeightOneSpectrum (𝓞 L) := ⟨τ⁻¹ • w₀.asIdeal, inferInstance, hne⟩
        have hw : w ∈ S := by
          rw [memS, ← (memS w₀).1 hw₀]
          apply HeightOneSpectrum.ext
          exact Ideal.under_smul (𝓞 K) w₀.asIdeal τ⁻¹
        refine ⟨w, hw, ?_⟩
        have h1 := stab_trivial hp w (overp w hw) (hs w hw).1 (hs w hw).2 (τ⁻¹ * σ w)
          (by rw [mul_smul, hσw w hw])
        exact (inv_mul_eq_one.1 h1).symm
      · intro w hw
        rfl
    rw [hre]
    apply RingOfIntegers.ext
    have h := Algebra.norm_eq_prod_automorphisms K ((ζ : 𝓞 L) : L)
    rw [hζ, map_one] at h
    have h' : ∀ τ : L ≃ₐ[K] L, algebraMap (𝓞 L) L (τ • (ζ : 𝓞 L)) = τ ((ζ : 𝓞 L) : L) :=
      fun τ => rfl
    show algebraMap (𝓞 L) L (∏ τ : L ≃ₐ[K] L, τ • (ζ : 𝓞 L)) = algebraMap (𝓞 L) L 1
    rw [map_prod, map_one]
    exact (Finset.prod_congr rfl fun τ _ => h' τ).trans h.symm

  haveI : w₀.asIdeal.IsMaximal := w₀.isMaximal
  haveI : CharP (𝓞 L ⧸ w₀.asIdeal) p := (CharP.charP_iff_prime_eq_zero hp).2 (by
    rw [← map_natCast (Ideal.Quotient.mk w₀.asIdeal)]; exact Ideal.Quotient.eq_zero_iff_mem.2 (overp w₀ hw₀))
  have hmod : ∏ w ∈ S, ((a w : ℕ) : ZMod p) = 1 := by
    apply (ZMod.castHom (dvd_refl p) (𝓞 L ⧸ w₀.asIdeal)).injective
    rw [map_prod, map_one]
    have : ∏ w ∈ S, (ZMod.castHom (dvd_refl p) (𝓞 L ⧸ w₀.asIdeal)) ((a w : ℕ) : ZMod p) =
        ∏ w ∈ S, Ideal.Quotient.mk w₀.asIdeal (σ w • (ζ : 𝓞 L)) :=
      Finset.prod_congr rfl fun w hw => by rw [map_natCast, hσres w hw]
    rw [this, ← map_prod, hprod, map_one]

  let u : HeightOneSpectrum (𝓞 L) → (ZMod p)ˣ := fun w =>
    if h : (a w).Coprime p then ZMod.unitOfCoprime (a w) h else 1
  have hval : ∀ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = ω (u w) := by
    intro w hw
    simp only [u, dif_pos (hcop w hw)]
    obtain ⟨b, hb, hθb⟩ := hθ w hw (a w) (hcop w hw)
    rw [← hθb]
    congr 1
    apply Units.ext
    rw [hb, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ha w hw, map_natCast]
  rw [Finset.prod_congr rfl hval, ← map_prod]
  have hu1 : ∏ w ∈ S, u w = 1 := by
    apply Units.ext
    rw [Units.coe_prod, Units.val_one, ← hmod]
    refine Finset.prod_congr rfl fun w hw => ?_
    simp only [u, dif_pos (hcop w hw), ZMod.coe_unitOfCoprime]
  rw [hu1, map_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonField

open UpperTheory.HF

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

noncomputable section

namespace GlobalTheory.Mem.DatHecke

open Formalism.L2.Host (HChar embPsi)
open GlobalTheory.Mem.Chr (ConjPl CMData)

theorem exists_gen (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    ∃ α : ℂ, IsAlgebraic ℚ α ∧ ∀ (K : Type) [Field K] [CharZero K] (σ : K →+* ℂ), (∃ x, σ x = α) →
      ∀ z ∈ M, ∃ x, σ x = z := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element ℚ M
  refine ⟨a, (Algebra.IsAlgebraic.isAlgebraic a).algHom M.val, ?_⟩
  intro K _ _ σ ⟨x, hx⟩ z hz
  have h1 : (⊤ : IntermediateField ℚ M) ≤ (σ.toRatAlgHom.fieldRange).comap M.val := by
    rw [← ha]
    exact IntermediateField.adjoin_simple_le_iff.2 ⟨x, hx⟩
  exact h1 (IntermediateField.mem_top (x := (⟨z, hz⟩ : M)))

section Host

variable {R : Ranks} (H : Host R)

end Host

section PrimesOk

variable {X : Fields} {Pr : Primes X}

theorem mem_vG (h : Pr.Ok) (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.E)) :
    w ∈ Pr.vG i ↔ X.conjO (Pr.piG i) ∈ w.asIdeal := by
  refine mem_divs (fun h0 => ?_) w
  have h1 := h.piG_norm i
  rw [h0, mul_zero] at h1
  have h2 : (Pr.g i : 𝓞 X.E) ≠ 0 := by exact_mod_cast (h.g_prime i).ne_zero
  exact h2 h1.symm

theorem mem_vGs (w : HeightOneSpectrum (𝓞 X.E)) : w ∈ Pr.vGs ↔ ∃ i, w ∈ Pr.vG i := by
  classical
  unfold Primes.vGs
  rw [Fin.exists_fin_two]
  convert Finset.mem_union

theorem g_mem_of_mem_vG (h : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
  rw [← h.piG_norm i]
  exact w.asIdeal.mul_mem_left _ ((mem_vG h i w).1 hw)

end PrimesOk

end GlobalTheory.Mem.DatHecke

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAl
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAl
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

namespace GlobalTheory.Mem.MuZero

theorem exists_residue_char {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (ω : (ZMod p)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, θ (-1) = ω (-1) ∧ ∀ (a : ℕ) (ha : a.Coprime p),
      ∃ b : (𝓞 L ⧸ w.asIdeal)ˣ, (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) ∧
        θ b = ω (ZMod.unitOfCoprime a ha) := by
  have hc : Nat.card (𝓞 L ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  let _ : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  let ρ : ZMod p ≃+* (𝓞 L ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])
  refine ⟨ω.comp (Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p)), ?_, fun a ha => ?_⟩
  · rw [MonoidHom.comp_apply]
    congr 1
    ext
    simp
  · refine ⟨Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) (ZMod.unitOfCoprime a ha), ?_, ?_⟩
    · simp
    · rw [MonoidHom.comp_apply]
      congr 1
      ext
      simp

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem eq_of_overP {k k' : Fin 2} {w : HeightOneSpectrum (𝓞 H.E)} (h : OverP H (H.g k) w)
    (h' : OverP H (H.g k') w) : k = k' := by
  by_contra hne
  have hg : H.g k ≠ H.g k' := by
    fin_cases k <;> fin_cases k'
    · exact absurd rfl hne
    · exact H.g_ne
    · exact H.g_ne.symm
    · exact absurd rfl hne
  have hc : IsCoprime ((H.g k : ℕ) : 𝓞 H.E) ((H.g k' : ℕ) : 𝓞 H.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (H.g_prime k) (H.g_prime k')).2 hg)
  obtain ⟨s, t, hst⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ h')

open Classical in
theorem exists_unitary_mu_zero_characters_of_split_type_primes : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ), (∀ k, SplitsC H.E (H.g k)) → (∀ τ, ∃ z : ℤ, e τ = z) → UpperTheory.MUQ (embPsi H) e → Mu0Exists P W e j := by
  intro R H P W e j hs hint hev
  choose z hz using hint
  have hmu : UpperTheory.MU (embPsi H) z := hev.mu hz
  haveI := H.galois
  haveI : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hsp := fun k => GlobalTheory.T.completelySplitPrime_host_place_properties R H (H.g k) (H.g_prime k) (hs k)
  have hθ : ∀ w : HeightOneSpectrum (𝓞 H.E), ∃ θ : (𝓞 H.E ⧸ w.asIdeal)ˣ →* ℂˣ, θ (-1) = 1 ∧
      ∀ k, P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)),
        ∃ b : (𝓞 H.E ⧸ w.asIdeal)ˣ, (b : 𝓞 H.E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E) ∧
          θ b = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
    intro w
    by_cases h : ∃ k, P.Div k w
    · obtain ⟨k, hk⟩ := h
      obtain ⟨θ, h1, h2⟩ := exists_residue_char w (H.g_prime k) (hsp k w (P.overP hk)).1
        ((W.om k ^ (2 * (j + 1)))⁻¹)
      refine ⟨θ, ?_, fun k' hk' => ?_⟩
      · rw [h1, MonoidHom.inv_apply, MonoidHom.pow_apply, pow_mul, ← map_pow, neg_one_sq, map_one, one_pow, inv_one]
      · obtain rfl := eq_of_overP (P.overP hk) (P.overP hk')
        exact h2
    · exact ⟨1, rfl, fun k hk => absurd ⟨k, hk⟩ h⟩
  choose θ hθ1 hθ2 using hθ
  let S : Finset (HeightOneSpectrum (𝓞 H.E)) := Finset.univ.biUnion fun k => aboveF (L := H.E) H.K (P.pb k)
  have hS : ∀ w, w ∈ S ↔ ∃ k, P.Div k w := fun w => by
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rfl
  have hmem : ∀ k w, w ∈ aboveF (L := H.E) H.K (P.pb k) ↔ P.Div k w := fun k w => by
    simp only [aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rfl
  have hres : ∀ (k : Fin 2) (ζ : (𝓞 H.E)ˣ), (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 H.E) : H.E) ^ m = 1) →
      ∏ w ∈ aboveF (L := H.E) H.K (P.pb k), θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 :=
    fun k ζ hζ => UpperTheory.prod_residue_char_norm_one_unit_eq_one H.K H.E (H.g k) (H.g_prime k) (P.pb k) _ (fun w => hmem k w)
      (fun w hw => ⟨(hsp k w (P.overP ((hmem k w).1 hw))).1, (hsp k w (P.overP ((hmem k w).1 hw))).2.1⟩)
      ((W.om k ^ (2 * (j + 1)))⁻¹) θ (fun w hw a ha => hθ2 w k ((hmem k w).1 hw) a ha) ζ (H.der.norm_mu _ hζ)
  have hdisj : (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)).PairwiseDisjoint
      (fun k => aboveF (L := H.E) H.K (P.pb k)) := by
    intro k _ k' _ hkk'
    refine Finset.disjoint_left.2 fun w hw hw' => hkk' ?_
    exact eq_of_overP (P.overP ((hmem k w).1 hw)) (P.overP ((hmem k' w).1 hw'))
  obtain ⟨χ, hu, ht, hi, htame, hunr, hloc, -⟩ := GlobalTheory.T.exists_heckeChar_trivOn_realSubfield_infinityType H.F H.E c (R.Psi) (embPsi H) hcm z S θ
    (by
      intro w hw w' hcj hw'
      obtain ⟨k, hk⟩ := (hS w).1 hw
      obtain ⟨k', hk'⟩ := (hS w').1 hw'
      rw [hce] at hcj
      obtain ⟨ho, hiff⟩ := (hsp k w (P.overP hk)).2.2.2 (P.pb k) (P.pb_over k) w' hcj
      obtain rfl := eq_of_overP ho (P.overP hk')
      exact hiff.1 hk hk')
    (by
      intro ζ hζ
      have hinf : ∏ i, embPsi H i ((ζ : 𝓞 H.E) : H.E) ^ (-z i) = 1 := hmu.neg _ hζ
      have hfin : ∏ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 := by
        rw [Finset.prod_biUnion hdisj]
        exact Finset.prod_eq_one fun k _ => hres k ζ hζ
      rw [hinf, one_mul, ← Units.coe_prod]
      exact (congrArg Units.val hfin).trans Units.val_one)
  refine ⟨χ, hu, ht, ⟨_, fun τ => ?_, hi⟩, fun v hv => hunr v ?_ ?_, htame, fun k w hw a ha x hx => ?_⟩
  · show _ = 2 * -e τ
    rw [hz τ]
    push_cast
    ring
  · intro h
    obtain ⟨k, hk⟩ := (hS v).1 h
    exact hv k (P.overP hk)
  · intro w hw hcj
    obtain ⟨k, hk⟩ := (hS w).1 hw
    rw [hce] at hcj
    exact hv k ((hsp k w (P.overP hk)).2.2.2 (P.pb k) (P.pb_over k) v hcj).1
  · obtain ⟨b, hb, hb'⟩ := hθ2 w k hw a ha
    rw [← hb']
    exact hloc w ((hS w).2 ⟨k, hw⟩) x (a : 𝓞 H.E) b (by rw [hx]; simp) hb

end GlobalTheory.Mem.MuZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAlStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Classical
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu0Exists_of_splits_of_integral_of_MUQ : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ), (∀ k, SplitsC H.E (H.g k)) → (∀ τ, ∃ z : ℤ, e τ = z) → UpperTheory.MUQ (embPsi H) e → Mu0Exists P W e j := by
  first | exact @GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes | exact GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes | (intros; apply GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharPow
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

namespace GlobalTheory.Mem.PsiExist

section General

variable {L : Type} [Field L] [NumberField L]

theorem trivOn_pow {F : Type} [Field F] [NumberField F] [Algebra F L] {χ : HChar L} (h : χ.TrivOn F) (n : ℕ) :
    (χ ^ n).TrivOn F := by
  induction n with
  | zero => rw [pow_zero, ← mul_inv_cancel χ]; exact h.mul h.inv
  | succ n ih => rw [pow_succ]; exact ih.mul h

end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

end GlobalTheory.Mem.PsiExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedCmTypeHeckeCharOnHost
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedCmTypeHeckeCharOnHost
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

namespace GlobalTheory.Mem.ChiPsiExist

open Classical in
theorem exists_chiPsi : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ χ : HChar H.E, IsChiPsi H χ := by
  intro R H
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, hu, ht, hi, -, hunr, -⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (embPsi H) hcm (fun _ => -1) ∅ (fun _ => 1)
      (fun w hw => absurd hw (Finset.notMem_empty w))
      (by
        intro ζ hζ
        rw [Finset.prod_empty, mul_one]
        exact UpperTheory.Mu.prod_emb_zpow H (Equiv.refl _) hζ _)
  exact ⟨χ, hu, fun v => hunr v (Finset.notMem_empty v) (fun w hw => absurd hw (Finset.notMem_empty w)), ht, hi⟩

end GlobalTheory.Mem.ChiPsiExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedCmTypeHeckeCharOnHostStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Classical
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_cmType_heckeChar_on_host : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ χ : HChar H.E, IsChiPsi H χ := by
  first | exact @GlobalTheory.Mem.ChiPsiExist.exists_chiPsi | exact GlobalTheory.Mem.ChiPsiExist.exists_chiPsi | (intros; apply GlobalTheory.Mem.ChiPsiExist.exists_chiPsi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjQuotientOfRationalUnitaryDeterminantMa
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjQuotientOfRationalUnitaryDeterminantMa
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

namespace GlobalTheory.Mem.RatPts

theorem exists_mul_apply_eq_of_mul_apply_eq_one_of_involution {L : Type} [Field L] (c : L →+* L) (hc : ∀ x, c (c x) = x) (hne : ∃ a, c a ≠ a)
    (z : L) (hz : z * c z = 1) : ∃ k : Lˣ, z * c (k : L) = k := by
  by_cases h : 1 + z = 0
  · obtain ⟨a, ha⟩ := hne
    refine ⟨Units.mk0 (a - c a) (sub_ne_zero.2 ha.symm), ?_⟩
    have hz1 : z = -1 := by linear_combination h
    rw [Units.val_mk0, map_sub, hc, hz1]
    ring
  · refine ⟨Units.mk0 (1 + z) h, ?_⟩
    rw [Units.val_mk0, map_add (f := _), map_one]
    linear_combination hz

theorem fixed_of_two {L : Type} [Field L] (c : L →+* L) (z : L) (k k' : Lˣ)
    (h : z * c (k : L) = k) (h' : z * c (k' : L) = k') :
    c ((k⁻¹ * k' : Lˣ) : L) = ((k⁻¹ * k' : Lˣ) : L) := by
  have h0 : c (k : L) ≠ 0 := (map_ne_zero c).2 k.ne_zero
  have h1 : (k : L) ≠ 0 := k.ne_zero
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  field_simp
  linear_combination c (k : L) * h' - c (k' : L) * h

open Classical in
theorem rat_points : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsRationalUnitaryDeterminantMap H (e1T H) ∧ (letI := H.cmStar; ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k) := by
  intro R H
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  letI := H.cmStar
  have h90 : ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k := by
    intro z
    refine exists_mul_apply_eq_of_mul_apply_eq_one_of_involution (H.conj : H.E →+* H.E) (fun x => ?_) ?_ (z : H.E) ?_
    · show H.conj (H.conj x) = x
      rw [← hc, ← hc, IsCMField.complexConj_apply_apply]
    · by_contra hn
      push Not at hn
      exact IsCMField.complexConj_ne_one H.E (AlgEquiv.ext fun x => (hc x).trans (hn x))
    · show (z : H.E) * H.conj (z : H.E) = 1
      rw [← bridge_star_holds R H]
      exact z.2.2
  have hwd : ∀ (z : H.E) (k k' : (H.E)ˣ), z * H.conj (k : H.E) = k → z * H.conj (k' : H.E) = k' →
      (QuotientGroup.mk (diagUnits H.E k) : DtT H) = QuotientGroup.mk (diagUnits H.E k') := by
    intro z k k' h h'
    have hfix := fixed_of_two (H.conj : H.E →+* H.E) z k k' h h'
    have hF : ((k⁻¹ * k' : (H.E)ˣ) : H.E) ∈ H.F :=
      (IsCMField.complexConj_eq_self_iff H.E _).1 ((hc _).trans hfix)
    have hne : (⟨_, hF⟩ : H.F) ≠ 0 := fun e => (k⁻¹ * k').ne_zero (congrArg Subtype.val e)
    have e : upF H.F (Units.mk0 _ hne) = k⁻¹ * k' := Units.ext rfl
    have := (GlobalTheory.T.unitaryDeterminantKernel_open_and_factor R H).2.2.1 (Units.mk0 _ hne)
    change diagUnits H.E (upF H.F (Units.mk0 _ hne)) ∈ KD H at this
    rw [e, map_mul, map_inv] at this
    exact QuotientGroup.eq.2 this
  refine ⟨isRationalUnitaryDeterminantMap_rationalUnitaryToDeterminants H ?_, h90⟩
  choose s hs using h90
  refine ⟨MonoidHom.mk' (fun z => QuotientGroup.mk (diagUnits H.E (s z))) fun z z' => ?_,
    fun k z h => hwd z k (s z) h (hs z)⟩
  rw [← QuotientGroup.mk_mul, ← map_mul]
  refine hwd ((z * z' : unitary H.E) : H.E) _ _ (hs _) ?_
  rw [Submonoid.coe_mul, Units.val_mul, map_mul, mul_mul_mul_comm, hs, hs]

end GlobalTheory.Mem.RatPts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjQuotientOfRationalUnitaryDeterminantMaStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Classical
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_quotient_of_rationalUnitaryDeterminantMap : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsRationalUnitaryDeterminantMap H (e1T H) ∧ (letI := H.cmStar; ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k) := by
  first | exact @GlobalTheory.Mem.RatPts.rat_points | exact GlobalTheory.Mem.RatPts.rat_points | (intros; apply GlobalTheory.Mem.RatPts.rat_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatOfQuasiFiniteOfFlatFibres
open TensorProduct

namespace GlobalTheory

namespace QuasiFiniteFibreFlat

theorem flat_baseChange_trans (S C T D : Type) [CommRing S] [CommRing C] [CommRing T] [CommRing D]
    [Algebra S C] [Algebra S T] [Algebra S D] [Algebra T D] [IsScalarTower S T D]
    [Module.Flat T D] [h : Module.Flat C (C ⊗[S] T)] : Module.Flat C (C ⊗[S] D) := by
  let l := IsScalarTower.toAlgHom S T D
  have hl : (l : T →+* D).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have h1 := (RingHom.flat_algebraMap_iff.mpr h).comp (RingHom.Flat.lTensor (S := S) C hl)
  rw [← RingHom.flat_algebraMap_iff]
  convert h1 using 1
  ext c
  simp

theorem flat_away {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B]
    [hRB : Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Flat A A'] (e : A' ⊗[A] B)
    [Module.Finite A' (Localization.Away e)] : Module.Flat A' (Localization.Away e) := by
  let D := Localization.Away e
  letI : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Flat (A' ⊗[A] B) D := IsLocalization.flat _ (Submonoid.powers e)
  haveI : Algebra.FinitePresentation (A' ⊗[A] B) D := IsLocalization.Away.finitePresentation e
  haveI : Algebra.FinitePresentation A' D := .trans A' (A' ⊗[A] B) D
  haveI : Module.FinitePresentation A' D :=
    Module.FinitePresentation.of_finite_of_finitePresentation A' D
  haveI : Module.Flat R D := by
    have h1 : (algebraMap B (B ⊗[A] A')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    have h2 := h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B))
          (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)
    have h3 := ((RingHom.flat_algebraMap_iff.mpr hRB).comp h2).comp
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (A' ⊗[A] B) D))
    rw [← RingHom.flat_algebraMap_iff]
    convert h3 using 1
    ext r
    rw [IsScalarTower.algebraMap_apply R A' D]
    change algebraMap A' D (algebraMap A A' (algebraMap R A r)) =
      algebraMap (A' ⊗[A] B) D (1 ⊗ₜ algebraMap R B r)
    rw [IsScalarTower.algebraMap_apply A' (A' ⊗[A] B) D, IsScalarTower.algebraMap_apply R A B,
      Algebra.TensorProduct.algebraMap_apply]
    congr 1
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
  refine FinitePresFibreFlat.flat_of_flat_fibres (R := R) (A := A') (B := D)
    fun k C _ _ _ t h w => ?_
  letI : Algebra A C := ((algebraMap A' C).comp (algebraMap A A')).toAlgebra
  haveI : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq' rfl
  haveI := H k C t h w
  haveI : Module.Flat C (C ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A A' C C B)
  exact flat_baseChange_trans A' C (A' ⊗[A] B) D

end QuasiFiniteFibreFlat

theorem flat_of_quasiFinite_of_flat_fibres :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B] [Algebra.QuasiFinite A B] [Module.Flat R B], (∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C), (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) → Module.Flat A B := by
  intro R A B _ _ _ _ _ _ _ _ _ _ H
  refine Module.flat_of_isLocalized_maximal B B (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap B _) fun Q _ => ?_
  obtain ⟨A', _, _, _, P, _, _, e, -, Q', _, _, hQ, he, -, hfin, -⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (Q.under A) Q
  let T := A' ⊗[A] B
  let D := Localization.Away e
  have hD : Module.Flat A' D := QuasiFiniteFibreFlat.flat_away H A' e
  let i : B →+* T := Algebra.TensorProduct.includeRight.toRingHom
  have hi : i.Flat := by
    have h1 : (algebraMap B (B ⊗[A] A')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    exact h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B))
          (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)
  let β := Localization.localRingHom Q Q' i hQ.symm
  have hβ : β.Flat := RingHom.Flat.localRingHom hi Q' Q hQ.symm
  have hle : Submonoid.powers e ≤ Q'.primeCompl := by
    rw [Submonoid.powers_le]; exact he
  letI : Algebra D (Localization.AtPrime Q') :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  haveI : IsScalarTower T D (Localization.AtPrime Q') :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI := IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q') _ _ hle
  have hDQ : Module.Flat D (Localization.AtPrime Q') :=
    IsLocalization.flat _ (Q'.primeCompl.map (algebraMap T D))
  rw [← RingHom.flat_algebraMap_iff]
  refine ringHom_flat_of_square_of_isLocalHom (α := algebraMap A A') (β := β)
    (φ' := (algebraMap D (Localization.AtPrime Q')).comp (algebraMap A' D)) ?_
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hβ
    ((RingHom.flat_algebraMap_iff.mpr hD).comp (RingHom.flat_algebraMap_iff.mpr hDQ))
  ext a
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q), Localization.localRingHom_to_map,
    IsScalarTower.algebraMap_apply A' T D, ← IsScalarTower.algebraMap_apply T D]
  congr 1
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul a

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExists
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

namespace GlobalTheory.Mem.DeltaZero

theorem exists_char_of_dvd {G : Type} [Group G] [IsCyclic G] {m : ℕ} (hm : m ≠ 0) (h : m ∣ Nat.card G) :
    ∃ θ : G →* ℂˣ, ∀ n : ℕ, θ ^ n = 1 ↔ m ∣ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hζ := Complex.isPrimitiveRoot_exp m hm
  have hζ' := hζ.isUnit_unit hm
  set ζ : ℂˣ := (hζ.isUnit hm).unit
  have ho : orderOf ζ ∣ orderOf g := by
    rw [← hζ'.eq_orderOf, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact h
  refine ⟨monoidHomOfForallMemZpowers hg ho, fun n => ?_⟩
  rw [MonoidHom.eq_iff_eq_on_generator hg, MonoidHom.pow_apply, monoidHomOfForallMemZpowers_apply_gen,
    MonoidHom.one_apply]
  exact hζ'.pow_eq_one_iff_dvd n

theorem exists_place_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ Q : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ Q.asIdeal := by
  have hne : Ideal.span {((p : ℕ) : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 : IsUnit (algebraMap ℤ (𝓞 K) (p : ℤ)) := by simpa using hu
    have h2 : IsUnit (p : ℤ) := isUnit_of_map_unit _ _ h1
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((p : ℕ) : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))

private theorem exists_residue_read {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (ω : (ZMod p)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, (∀ (a : ℕ) (ha : a.Coprime p) (b : (𝓞 L ⧸ w.asIdeal)ˣ),
        (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) → θ b = ω (ZMod.unitOfCoprime a ha)) ∧
      ∀ n : ℕ, θ ^ n = 1 ↔ ω ^ n = 1 := by
  have hc : Nat.card (𝓞 L ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  let _ : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  let ρ : ZMod p ≃+* (𝓞 L ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])
  refine ⟨ω.comp (Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p)), fun a ha b hb => ?_, fun n => ?_⟩
  · rw [MonoidHom.comp_apply]
    congr 1
    ext
    simp [hb]
  · constructor
    · intro h
      ext u
      have := congrArg (fun f => f (Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) u)) h
      simp only [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply] at this
      have e : Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p) (Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) u) = u := by
        ext; simp
      rw [e] at this
      simp [MonoidHom.pow_apply, this]
    · intro h
      refine MonoidHom.ext fun u => ?_
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, h, MonoidHom.one_apply,
        MonoidHom.one_apply]

open Classical in
theorem delta_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → p % 15 = 1 → SplitsC H.E p → DeltaExists (H := H) p := by
  intro R H p hp h15 hs
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hsp := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs
  obtain ⟨Q, hQ⟩ := exists_place_over H.K hp
  have : Fact p.Prime := ⟨hp⟩
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  obtain ⟨ω, hω⟩ := exists_char_of_dvd (G := (ZMod p)ˣ) (m := 15) (by norm_num)
    (by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]; omega)
  have hθ : ∀ w : HeightOneSpectrum (𝓞 H.E), ∃ θ : (𝓞 H.E ⧸ w.asIdeal)ˣ →* ℂˣ,
      (OverP H p w → ∀ (a : ℕ) (ha : a.Coprime p) (b : (𝓞 H.E ⧸ w.asIdeal)ˣ),
        (b : 𝓞 H.E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E) → θ b = ω (ZMod.unitOfCoprime a ha)) ∧
      (OverP H p w → ∀ n : ℕ, θ ^ n = 1 ↔ 15 ∣ n) := by
    intro w
    by_cases h : OverP H p w
    · obtain ⟨θ, h1, h2⟩ := exists_residue_read w hp (hsp w h).1 ω
      exact ⟨θ, fun _ => h1, fun _ n => (h2 n).trans (hω n)⟩
    · exact ⟨1, fun h' => absurd h' h, fun h' => absurd h' h⟩
  choose θ hθ1 hθ2 using hθ
  let S : Finset (HeightOneSpectrum (𝓞 H.E)) := aboveF (L := H.E) H.K Q
  have hS : ∀ w, w ∈ S ↔ w.under (𝓞 H.K) = Q := fun w => by
    simp only [S, aboveF, Set.Finite.mem_toFinset]
    rfl
  have hov : ∀ w ∈ S, OverP H p w := fun w hw => by
    have h1 := hQ
    rw [← (hS w).1 hw] at h1
    have h2 : algebraMap (𝓞 H.K) (𝓞 H.E) ((p : ℕ) : 𝓞 H.K) ∈ w.asIdeal := h1
    rwa [map_natCast] at h2
  have hres := UpperTheory.prod_residue_char_norm_one_unit_eq_one H.K H.E p hp Q S hS (fun w hw => ⟨(hsp w (hov w hw)).1, (hsp w (hov w hw)).2.1⟩) ω θ
    (by
      intro w hw a ha
      have hu : IsUnit (Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E)) := by
        obtain ⟨s, t, hst⟩ : IsCoprime ((a : ℕ) : 𝓞 H.E) ((p : ℕ) : 𝓞 H.E) := Nat.Coprime.cast ha
        have h0 : Ideal.Quotient.mk w.asIdeal ((p : ℕ) : 𝓞 H.E) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hov w hw)
        have h1 := congrArg (Ideal.Quotient.mk w.asIdeal) hst
        rw [map_add (f := _), map_mul, map_mul, h0, mul_zero, add_zero, map_one] at h1
        exact IsUnit.of_mul_eq_one_right _ h1
      exact ⟨hu.unit, hu.unit_spec, hθ1 w (hov w hw) a ha _ hu.unit_spec⟩)
  obtain ⟨χ, -, ht, hi, htame, hunr, -, hord⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (embPsi H) hcm (fun _ => 0) S θ
    (by
      intro w hw w' hcj hw'
      rw [hce] at hcj
      exact ((hsp w (hov w hw)).2.2.2 Q hQ w' hcj).2.1 ((hS w).1 hw) ((hS w').1 hw'))
    (by
      intro ζ hζ
      have h1 := hres ζ (H.der.norm_mu _ hζ)
      have h2 : ∏ w ∈ S, ((θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1 := by
        rw [← Units.coe_prod]
        exact congrArg Units.val h1 |>.trans Units.val_one
      rw [h2]
      simp)
  refine ⟨χ, GlobalTheory.T.heckeChar_finiteOrder_of_trivial_at_infinity H.E χ fun k => ?_, ht, htame, fun v hv => hunr v (fun h => hv (hov v h)) ?_,
    fun v hv n => ?_⟩
  · apply Units.ext
    change ((χ.inf k : ℂˣ) : ℂ) = 1
    rw [hi k]
    simp
  · intro w hw hcj
    rw [hce] at hcj
    exact hv ((hsp w (hov w hw)).2.2.2 Q hQ v hcj).1
  · by_cases h : v ∈ S
    · exact (hord v h n).1.trans (hθ2 v hv n)
    · obtain ⟨w, hw, -⟩ := existsUnique_conjPl c.toRingEquiv.symm v
      have hcj : ConjPl c.toRingEquiv w v := fun x => by
        have := hw (c.toRingEquiv x)
        rw [RingEquiv.symm_apply_apply] at this
        exact this.symm
      have hwo : OverP H p w := by
        refine ((conjPl_iff_mem _ w v).1 hcj _ _ ?_).2 hv
        simp
      have hwS : w ∈ S := (hS w).2
        (((hsp w hwo).2.2.2 Q hQ v (hce ▸ hcj)).2.2 fun e => h ((hS v).2 e))
      exact ((hord w hwS n).2 v hcj).trans (hθ2 w hwo n)

end GlobalTheory.Mem.DeltaZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExistsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Classical
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → p % 15 = 1 → SplitsC H.E p → DeltaExists (H := H) p := by
  first | exact @GlobalTheory.Mem.DeltaZero.delta_exists | exact GlobalTheory.Mem.DeltaZero.delta_exists | (intros; apply GlobalTheory.Mem.DeltaZero.delta_exists <;> assumption)
end
end
