module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct Pointwise

namespace GlobalTheory.HostSplit

theorem jacobiSym_neg_eq_one {r p : ℕ} (hr : r % 2 = 1) (h4 : p % 4 = 1) (h1 : p % r = 1) :
    jacobiSym (-(r : ℤ)) p = 1 := by
  have hgo : Odd p := Nat.odd_iff.mpr (by omega)
  have hdo : Odd r := Nat.odd_iff.mpr hr
  rw [jacobiSym.neg _ hgo, ZMod.χ₄_nat_one_mod_four h4, one_mul,
    jacobiSym.quadratic_reciprocity_one_mod_four' hdo h4, jacobiSym.mod_left]
  have h2 : ((p : ℤ) % (r : ℤ)) = 1 := by
    rw [← Int.natCast_mod, h1]
    rfl
  rw [h2, jacobiSym.one_left]

theorem ncard_placesOver (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    (placesOver E p).ncard = (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have himg : HeightOneSpectrum.asIdeal '' placesOver E p =
      Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hPp := v.isPrime
      refine ⟨hPp, ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_⟩⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ v.asIdeal
      rw [map_natCast]
      exact hv
    · rintro ⟨h1, h2⟩
      refine ⟨⟨P, h1, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩
      have h3 : (p : ℤ) ∈ P.under ℤ := by
        rw [← Ideal.over_def P (Ideal.span {(p : ℤ)})]
        exact Ideal.mem_span_singleton_self _
      have h4 : algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ P := h3
      rw [map_natCast] at h4
      exact h4
  rw [← himg, Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)]

theorem ncard_primesOver_of_stabilizer (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (h : ∀ σ : E ≃ₐ[ℚ] E, σ ∈ MulAction.stabilizer (E ≃ₐ[ℚ] E) P → σ = 1) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hr : Set.range (fun σ : E ≃ₐ[ℚ] E => σ • P) = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hQ1, hQ2⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have hinj : Function.Injective (fun σ : E ≃ₐ[ℚ] E => σ • P) := by
    intro σ τ hστ
    have h1 : τ⁻¹ * σ = 1 := by
      apply h
      rw [MulAction.mem_stabilizer_iff, mul_smul]
      have h2 : σ • P = τ • P := hστ
      rw [h2, inv_smul_smul]
    exact (inv_mul_eq_one.mp h1).symm
  rw [← hr, Set.ncard_range_of_injective hinj, IsGalois.card_aut_eq_finrank]

theorem split_of_one_mod : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime → p % (H.QS * H.q * H.d) = 1 →
    (placesOver H.E p).ncard = Module.finrank ℚ H.E ∧ H.cls p = PrimeClass.splitK := by
  intro R H p hp hc
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hmod : ∀ m : ℕ, 1 < m → m ∣ H.QS * H.q * H.d → p % m = 1 := by
    intro m hm hdv
    rw [← Nat.mod_mod_of_dvd p hdv, hc]
    exact Nat.mod_eq_of_lt hm
  have h4Q : 4 ∣ H.QS := (show (2 : ℕ) ^ 2 ∣ 2 ^ (R.e + 2) from pow_dvd_pow 2 (by omega)).trans H.tower_dvd
  have h4 : p % 4 = 1 := hmod 4 (by norm_num) ((h4Q.mul_right _).mul_right _)
  have hd : p % H.d = 1 := hmod _ (by omega) (dvd_mul_left _ _)
  have hnd : ∀ m : ℕ, m ∣ H.QS * H.q * H.d → ¬ p ∣ m := by
    intro m hm hpm
    have h := hmod p hp.one_lt (hpm.trans hm)
    rw [Nat.mod_self] at h
    omega
  have hN : ¬ p ∣ H.condN := hnd _ dvd_rfl
  have hp2 : p ∉ H.small := fun h =>
    hnd H.QS (((dvd_refl _).mul_right _).mul_right _) (Nat.dvd_of_mem_primeFactors h)
  have hpq : p ≠ H.q := fun h => hnd H.q ((dvd_mul_left _ _).mul_right _) (h ▸ dvd_rfl)
  have hpd : p ≠ H.d := fun h => hnd H.d (dvd_mul_left _ _) (h ▸ dvd_rfl)
  have jd := jacobiSym_neg_eq_one (r := H.d) (by omega) h4 hd
  refine ⟨?_, ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hG : IsGalois ℚ H.E := H.galois
    have := Formalism.FrobeniusOrbits.SplitK.span_prime p
    obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E)))
    obtain ⟨-, hF, -, hI⟩ := H.der.frob p hN P
    have h1 : IsArithFrobAt ℤ (1 : H.E ≃ₐ[ℚ] H.E) P := by
      refine (hF 1 1 ?_).2 (by rw [map_one, map_one])
      rw [← ZMod.natCast_mod p, show p % H.condN = 1 from hc]
      simp
    rw [ncard_placesOver H.E hp]
    refine ncard_primesOver_of_stabilizer H.E p P fun σ hσ => ?_
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul p P 1 σ h1 hσ
    rw [(hI ρ).1 hρ, one_pow, mul_one]
  · unfold Host.cls primeClass
    rw [if_neg hp2, if_neg hpq, if_neg hpd, if_pos jd]

end GlobalTheory.HostSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.TameGenPowers
open scoped Pointwise

theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h := A.valuation.map_one_add_of_lt (hσ y hy)
    rw [add_sub_cancel, map_div₀, div_eq_one_iff_eq (by simpa using hy)] at h
    exact h
  refine ⟨?_, fun x hx => ?_⟩
  · show σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← A.valuation_le_one_iff, ← A.valuation_le_one_iff, ← hv, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) (hσ x hx0)

theorem finite_roots (K : Type) [Field K] (m : ℕ) (hm : m ≠ 0) :
    {u : Kˣ | u ^ m = 1}.Finite := by
  haveI : NeZero m := ⟨hm⟩
  have : Finite (rootsOfUnity m K) := inferInstance
  have h := Set.toFinite ((rootsOfUnity m K : Subgroup Kˣ) : Set Kˣ)
  exact h.subset fun u hu => (mem_rootsOfUnity m u).2 hu

theorem eq_one_of_wild_prime (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (hA : IsPlaceOver A v) (K : Type) [Field K] [TopologicalSpace K] [T2Space K]
    (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ) (hr : Continuous r) (l : ℕ) (hl : l.Prime)
    (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (σ : Formalism.ConjugateSelfDual.G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hσl : r σ ^ l = 1) : r σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  have hfin : ({u : Kˣ | u ^ l = 1} \ {1}).Finite := (finite_roots K l hl.ne_zero).diff
  have hop : IsOpen (r ⁻¹' ({u : Kˣ | u ^ l = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hr
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (by simp))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ n ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ n)
      (GlobalTheory.WildInertiaChar.wild_pow A σ hσ n) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : r σ ^ n = 1 := by
    have h2 : r (σ ^ n) ∉ ({u : Kˣ | u ^ l = 1} \ {1}) := hsub hτ
    by_contra hne
    apply h2
    refine ⟨?_, by rwa [map_pow]⟩
    show r (σ ^ n) ^ l = 1
    rw [map_pow, ← pow_mul, mul_comm, pow_mul, hσl, one_pow]
  have hc : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hn
  have := (pow_gcd_eq_one (a := r σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩
  rwa [hc, pow_one] at this

theorem mem_zpowers_of_tameGen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (γ : Formalism.ConjugateSelfDual.G E Ω), TameGenAt A γ → ∀ (K : Type) [Field K] [TopologicalSpace K] [T2Space K] (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ), Continuous r → ∀ m : ℕ, ((m : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ σ ∈ Ine (F := E) A, r σ ^ m = 1) → ∀ σ ∈ Ine (F := E) A, r σ ∈ Subgroup.zpowers (r γ) := by
  intro E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr m hm hI σ hσ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1 := by
    intro τ hτ
    by_contra hne
    have hd : orderOf (r τ) ∣ m := orderOf_dvd_of_pow_eq_one (hI τ (wild_mem_Ine hτ))
    have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
    have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
      intro h
      apply hm
      obtain ⟨c, hc⟩ := hd
      rw [hc, hk]
      push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
    have h1 : r (τ ^ k) = 1 := by
      refine eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
        (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
      rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    rw [map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have ho : orderOf (r τ) ≠ 0 := fun h => hm0 (by simpa [h] using hd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ho (by simpa using hk)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
    rw [hk] at h3
    have := hl.two_le
    have := Nat.pos_of_ne_zero hk0
    nlinarith
  have hfin : ((Subgroup.zpowers (r γ) : Subgroup Kˣ) : Set Kˣ).Finite := by
    refine (finite_roots K m hm0).subset ?_
    rintro u ⟨z, rfl⟩
    show (r γ ^ z) ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hI γ hγ.1, one_zpow]
  have hc : IsClosed (((Subgroup.zpowers (r γ)).comap r : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
      Set (Formalism.ConjugateSelfDual.G E Ω)) := hfin.isClosed.preimage hr
  refine closure_minimal (SetLike.coe_subset_coe.2 ((Subgroup.closure_le _).2 ?_)) hc (hγ.2 hσ)
  rintro τ (rfl | hτ)
  · exact Subgroup.mem_zpowers _
  · show r τ ∈ Subgroup.zpowers (r γ)
    rw [hw τ hτ]
    exact one_mem _

end GlobalTheory.TameGenPowers
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem host_cmData : ∀ (R : Ranks) (H : Host R), @CMData H.F H.E _ _ _ _ H.cmStar _ := by
  intro R H
  letI := H.cmStar
  have hcm := H.isCMField_hostE
  have hs : ∀ x : H.E, star x = H.conj x := bridge_star_holds R H
  refine ⟨⟨inferInstance, fun φ a => ?_, fun P hP => ?_⟩, inferInstance, ?_, fun a => ?_⟩
  · rw [hs]
    exact H.conjE_apply _ _
  · have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
    have h := H.der.unramEF P hP.isPrime hP0
    obtain ⟨x, hx⟩ := not_forall.1 h
    refine ⟨x, H.conj • x, ?_, fun h' => hx ?_⟩
    · rw [hs]; rfl
    · have := P.neg_mem h'
      rwa [neg_sub] at this
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · rw [hs]
    have h := H.conjE_mem_hostF_iff a
    constructor
    · intro ha
      exact ⟨⟨a, h.2 ha⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact h.1 y.2

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPowEqOneOfValuationSubLtOne
universe u_1

namespace GlobalTheory.PowEqOneValuation

theorem val_eq_one_of_pow_eq_one {Ω Γ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) {m : ℕ} (hm : m ≠ 0) {x : Ω} (hx : x ^ m = 1) : v x = 1 := by
  have h : v x ^ m = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_eq_one_iff_left hm).1 h

theorem val_one_sub_pow_lt {Ω Γ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) {u : Ω} (hu : v u = 1) (h : v (1 - u) < 1) (i : ℕ) :
    v (1 - u ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - u ^ (i + 1) = (1 - u) + u * (1 - u ^ i) := by ring
    rw [e]
    refine v.map_add_lt h ?_
    rw [map_mul, hu, one_mul]
    exact ih

theorem eq_of_pow_eq_one_of_valuation_sub_lt_one {Ω : Type u_1} [inst : Field Ω]
    (A : ValuationSubring Ω) (m : ℕ) {ζ ζ' : Ω} (h1 : ζ ^ m = 1) (h2 : ζ' ^ m = 1)
    (hm : ¬ A.valuation (m : Ω) < 1) (h : A.valuation (ζ - ζ') < 1) : ζ = ζ' := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hm
    simp
  have v1 := val_eq_one_of_pow_eq_one A.valuation hm0 h1
  have v2 := val_eq_one_of_pow_eq_one A.valuation hm0 h2
  have hz : ζ ≠ 0 := by
    rintro rfl
    simp at v1
  by_contra hne
  set u : Ω := ζ' / ζ with hu
  have hu1 : u ≠ 1 := by
    intro e
    apply hne
    rw [hu, div_eq_one_iff_eq hz] at e
    exact e.symm
  have hum : u ^ m = 1 := by rw [hu, div_pow, h1, h2, div_one]
  have vu : A.valuation u = 1 := by rw [hu, map_div₀, v1, v2, div_one]
  have v1u : A.valuation (1 - u) < 1 := by
    have e : 1 - u = (ζ - ζ') / ζ := by rw [hu, sub_div, div_self hz]
    rw [e, map_div₀, v1, div_one]
    exact h
  have hs : ∑ i ∈ Finset.range m, u ^ i = 0 := by
    have g := geom_sum_mul u m
    rw [hum, sub_self] at g
    exact (mul_eq_zero.1 g).resolve_right (sub_ne_zero.2 hu1)
  have hm' : (m : Ω) = ∑ i ∈ Finset.range m, (1 - u ^ i) := by
    rw [Finset.sum_sub_distrib, hs]
    simp
  apply hm
  rw [hm']
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => val_one_sub_pow_lt A.valuation vu v1u i

end GlobalTheory.PowEqOneValuation
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameTau

theorem root_eq_of_close {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (m : ℕ) {ζ ζ' : Ω}
    (h : ζ ^ m = 1) (h' : ζ' ^ m = 1) (hm : ¬ A.valuation (m : Ω) < 1)
    (hc : A.valuation (ζ - ζ') < 1) : ζ = ζ' := by
  first
  | exact @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one
  | exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one
  | (apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one ..)

theorem ine_fix_root {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) {ζ : Ω} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  refine root_eq_of_close A m (by rw [← map_pow, hζ, map_one]) hζ hm ?_
  exact hσ.2 ζ (valuation_eq_one_of_pow_eq_one A hm0 hζ).le

theorem quot_mul {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {σ τ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) {π : Ω} (hπ : π ≠ 0)
    {e : E} (he : π ^ m = algebraMap E Ω e) :
    (σ * τ) π / π = (σ π / π) * (τ π / π) := by
  have hτ : (τ π / π) ^ m = 1 := by
    rw [div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]
  have hfix := ine_fix_root hσ m hm hτ
  have e1 : τ π = (τ π / π) * π := by field_simp
  have e2 : (σ * τ) π = σ (τ π / π) * σ π := by
    rw [AlgEquiv.mul_apply, ← map_mul, div_mul_cancel₀ _ hπ]
  rw [e2, hfix]
  field_simp

end GlobalTheory.TameTau
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationApplyOfWild
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.TameCharUnique
open scoped Pointwise

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem _root_.GlobalTheory.TameCharUnique.mem_Ine_of_wild {A : ValuationSubring Ω} {σ : _root_.Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A := by
  have hval : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have h1 : A.valuation (σ y / y) = 1 := by
        have := A.valuation.map_one_add_of_lt (hσ y hy)
        rwa [add_sub_cancel] at this
      have h2 : σ y = σ y / y * y := (div_mul_cancel₀ _ hy).symm
      rw [h2, map_mul, h1, one_mul]
  rw [_root_.ReciprocityTheory.Gal.mem_Ine]
  unfold _root_.Formalism.ConjugateSelfDual.Inertia
  refine ⟨?_, fun x hx => ?_⟩
  · change (σ : Gal(Ω/E)) • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, AlgEquiv.smul_def]
    have hx := hval (σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at hx
    rw [← hx]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hsplit : σ x - x = (σ x / x - 1) * x := by
        rw [sub_mul, div_mul_cancel₀ _ hx0, one_mul]
      rw [hsplit, map_mul]
      calc A.valuation (σ x / x - 1) * A.valuation x ≤ A.valuation (σ x / x - 1) :=
            mul_le_of_le_one_right' hx
        _ < 1 := hσ x hx0

variable [IsAlgClosure E Ω]

theorem _root_.GlobalTheory.TameCharUnique.mem_of_tameGen {A : ValuationSubring Ω} {γ : _root_.Formalism.ConjugateSelfDual.G E Ω}
    (hγ : _root_.Formalism.BasicNotions.TameGenAt A γ)
    (S : Subgroup (_root_.ReciprocityTheory.Gal.Ine (F := E) A)) (hS : IsClosed (S : Set (_root_.ReciprocityTheory.Gal.Ine (F := E) A)))
    (h1 : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ S)
    (h2 : ∀ σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) → σ ∈ S)
    (σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) : σ ∈ S := by
  obtain ⟨C, hC, hCS⟩ := (Topology.IsInducing.subtypeVal.isClosed_iff).mp hS
  have hmapC : ((S.map (_root_.ReciprocityTheory.Gal.Ine (F := E) A).subtype : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)) :
      Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) ⊆ C := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact (Set.ext_iff.mp hCS τ).mpr hτ
  have hle : Subgroup.closure (insert γ {τ : _root_.Formalism.ConjugateSelfDual.G E Ω |
      ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1}) ≤ S.map (_root_.ReciprocityTheory.Gal.Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro τ (rfl | hτ)
    · exact ⟨_, h1, rfl⟩
    · exact ⟨⟨τ, _root_.GlobalTheory.TameCharUnique.mem_Ine_of_wild hτ⟩, h2 _ hτ, rfl⟩
  have hσC : (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ∈ C :=
    closure_minimal ((SetLike.coe_subset_coe.mpr hle).trans hmapC) hC (hγ.2 σ.2)
  exact (Set.ext_iff.mp hCS σ).mp hσC

private lemma exists_pow_fixes_finiteDimensional (K : IntermediateField E Ω)
    [FiniteDimensional E K] (τ : Gal(Ω/E)) : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ K, (τ ^ m) x = x := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => ((τ ^ n : Gal(Ω/E)).toAlgHom.comp K.val : K →ₐ[E] Ω))
  have hfix : ∀ a b : ℕ, a < b → (∀ x ∈ K, (τ ^ a) x = (τ ^ b) x) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ K, (τ ^ m) x = x := by
    intro a b hab hx
    refine ⟨b - a, Nat.sub_pos_of_lt hab, fun x hxK => ?_⟩
    apply (τ ^ a).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    exact (hx x hxK).symm
  have hij' : ∀ x ∈ K, (τ ^ i) x = (τ ^ j) x := fun x hx => by
    simpa using DFunLike.congr_fun heq ⟨x, hx⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hfix i j h hij'
  · exact hfix j i h fun x hx => (hij' x hx).symm

theorem _root_.GlobalTheory.TameCharUnique.eq_zero_of_wild {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {l : ℕ} [Fact l.Prime] (hlw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (t : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l]) (ht : Continuous t)
    (σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) : (t σ).toAdd = 0 := by
  have hl1 : l ≠ 1 := (Fact.out : l.Prime).ne_one
  rw [← norm_eq_zero]
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
  rw [zero_add]
  have hUo : IsOpen (t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε}) :=
    (isOpen_lt (continuous_norm.comp continuous_toAdd) continuous_const).preimage ht
  obtain ⟨V, hVo, hVU⟩ := (Topology.IsInducing.subtypeVal.isOpen_iff).mp hUo
  have h1V : (1 : Gal(Ω/E)) ∈ V := by
    have h1U : (1 : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε} := by
      simp [hε]
    rw [← hVU] at h1U
    exact h1U
  obtain ⟨K, hK, hKV⟩ := (krullTopology_mem_nhds_one_iff E Ω V).mp (hVo.mem_nhds h1V)
  obtain ⟨m, hm0, hmK⟩ := exists_pow_fixes_finiteDimensional K σ.1
  obtain ⟨e, m', hlm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' l hl1
  have hτ := _root_.GlobalTheory.WildInertiaChar.wild_pow A σ.1 hσ m'
  have hfix : (σ ^ m' : _root_.ReciprocityTheory.Gal.Ine (F := E) A).1 ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [Subgroup.coe_pow]
    refine _root_.GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A _ hτ (l ^ e) (_root_.ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver hlw h e) x ?_
    rw [← pow_mul, mul_comm, ← hm]
    exact hmK x hx
  have hmem : σ ^ m' ∈ t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε} := by
    rw [← hVU]
    exact hKV hfix
  have hnorm : ‖(t (σ ^ m')).toAdd‖ < ε := hmem
  rwa [map_pow, toAdd_pow, nsmul_eq_mul, norm_mul,
    PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hlm'),
    one_mul] at hnorm

theorem _root_.GlobalTheory.TameCharUnique.exists_eq_mul : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (l : ℕ) [Fact l.Prime], ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (t t' : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l]), Continuous t → Continuous t' → Function.Surjective t' → ∃ c : ℤ_[l], ∀ σ, (t σ).toAdd = c * (t' σ).toAdd := by
  intro E Ω _ _ _ _ _ A w h l _ hlw t t' ht ht' hsurj
  obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := E) A
  have hwild : ∀ s : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l], Continuous s →
      ∀ σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) →
        s σ = 1 := by
    intro s hs σ hσ
    rw [← toAdd_eq_zero]
    exact _root_.GlobalTheory.TameCharUnique.eq_zero_of_wild h hlw s hs σ hσ
  have hb : IsUnit (t' ⟨γ, hγ.1⟩).toAdd := by
    by_contra hb
    let S : Subgroup (_root_.ReciprocityTheory.Gal.Ine (F := E) A) :=
      { carrier := {σ | ‖(t' σ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_mul, toAdd_mul] at *
          exact (PadicInt.nonarchimedean _ _).trans (max_le ha hb)
        one_mem' := by simp
        inv_mem' := fun {a} ha => by simpa using ha }
    have hS : IsClosed (S : Set (_root_.ReciprocityTheory.Gal.Ine (F := E) A)) :=
      isClosed_le (continuous_norm.comp (continuous_toAdd.comp ht')) continuous_const
    have hγS : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ S := by
      show ‖(t' ⟨γ, hγ.1⟩).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)
      rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
      rw [PadicInt.isUnit_iff] at hb
      norm_num
      exact lt_of_le_of_ne (PadicInt.norm_le_one _) hb
    have hall : ∀ σ, σ ∈ S := fun σ =>
      _root_.GlobalTheory.TameCharUnique.mem_of_tameGen hγ S hS hγS
        (fun τ hτ => by
          show ‖(t' τ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)
          rw [hwild t' ht' τ hτ]
          simp) σ
    obtain ⟨σ, hσ⟩ := hsurj (Multiplicative.ofAdd 1)
    have h1 : ‖(t' σ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ) := hall σ
    rw [hσ, toAdd_ofAdd, norm_one, zpow_neg_one] at h1
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact absurd h1 (not_le.mpr (inv_lt_one_of_one_lt₀ hl))
  refine ⟨(t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹, fun σ => ?_⟩
  let f : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l] :=
    (AddMonoidHom.toMultiplicative
      (AddMonoidHom.mulLeft ((t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹))).comp t'
  have hf : Continuous f := by
    show Continuous fun τ => Multiplicative.ofAdd
      ((t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹ * (t' τ).toAdd)
    exact continuous_ofAdd.comp (continuous_const.mul (continuous_toAdd.comp ht'))
  have hγmem : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ MonoidHom.eqLocus t f := by
    show t ⟨γ, hγ.1⟩ = f ⟨γ, hγ.1⟩
    apply Multiplicative.toAdd.injective
    show (t ⟨γ, hγ.1⟩).toAdd = (t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹ * (t' ⟨γ, hγ.1⟩).toAdd
    rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
  have hwmem : ∀ τ : _root_.ReciprocityTheory.Gal.Ine (F := E) A,
      (∀ y : Ω, y ≠ 0 → A.valuation (τ.1 y / y - 1) < 1) → τ ∈ MonoidHom.eqLocus t f := by
    intro τ hτ
    show t τ = f τ
    simp [f, hwild t ht τ hτ, hwild t' ht' τ hτ]
  have hmem := _root_.GlobalTheory.TameCharUnique.mem_of_tameGen hγ (MonoidHom.eqLocus t f)
    (isClosed_eq ht hf) hγmem hwmem σ
  exact congrArg Multiplicative.toAdd hmem

end GlobalTheory.TameCharUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisSubfieldConjStable
open Polynomial

namespace GlobalTheory

theorem exists_galois_subfield_conj_stable (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ (∀ z ∈ S, z ∈ K) ∧
      Complex.I ∈ K ∧ ∀ z ∈ K, starRingEnd ℂ z ∈ K := by
  classical
  have hI : IsIntegral ℚ Complex.I := by
    refine ⟨X ^ 2 + C 1, monic_X_pow_add_C 1 two_ne_zero, ?_⟩
    simp [Complex.I_sq]
  have hint : ∀ z ∈ insert Complex.I S, IsIntegral ℚ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hI
    · exact (hS z hz).isIntegral
  obtain ⟨p, hp⟩ : ∃ p : ℚ[X], p = ∏ z ∈ insert Complex.I S, minpoly ℚ z := ⟨_, rfl⟩
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact Finset.prod_ne_zero_iff.2 fun z hz => minpoly.ne_zero (hint z hz)
  have hroot : ∀ z ∈ insert Complex.I S, z ∈ p.rootSet ℂ := by
    intro z hz
    rw [mem_rootSet]
    refine ⟨hp0, ?_⟩
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (minpoly ℚ) hz
    rw [hp, hq, map_mul, minpoly.aeval, zero_mul]
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (p.rootSet ℂ)
  have : p.IsSplittingField ℚ K :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits (p.map (algebraMap ℚ ℂ)))
  have hfin : FiniteDimensional ℚ K := Polynomial.IsSplittingField.finiteDimensional K p
  have : Normal ℚ K := Normal.of_isSplittingField p
  refine ⟨K, hfin, IsGalois.mk,
    fun z hz => IntermediateField.subset_adjoin ℚ _ (hroot z (Finset.mem_insert_of_mem hz)),
    IntermediateField.subset_adjoin ℚ _ (hroot _ (Finset.mem_insert_self _ _)), ?_⟩
  let φ : ℂ →ₐ[ℚ] ℂ := Complex.conjAe.toAlgHom.restrictScalars ℚ
  have hsub : φ '' (p.rootSet ℂ) ⊆ p.rootSet ℂ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_rootSet] at hw ⊢
    exact ⟨hw.1, by rw [Polynomial.aeval_algHom_apply, hw.2, map_zero]⟩
  have hle : K.map φ ≤ K := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  intro z hz
  exact hle ⟨z, hz, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQp
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQp
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem fund_phiB_alg (l : ℕ) [Fact l.Prime] (x : Per.Acris l) :
    Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) :=
  GlobalTheory.CrisMaps.φB_phiA l x

theorem fund_zB (l : ℕ) [Fact l.Prime] (z : ℤ_[l]) :
    Per.zB l z = algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z)) :=
  (GlobalTheory.RingIface.zB_eq_aB_zA l z).trans (GlobalTheory.RingIface.aB_eq_alg l _)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem fundamental_exact (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l)
    (hφ : Per.φB l b = b) (hF : C.ι b ∈ Per.FilD l 0) :
    ∃ c : ℚ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = b := by
  obtain ⟨r, x, hx⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
  obtain ⟨-, hinj, -, -⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨-, h1, hmul, -, -, -, hP⟩ := GlobalTheory.T.bdR_filtration_laws l
  have hj := GlobalTheory.T.acrisToBdRPlus_injective l C.j C.j_cris
  obtain ⟨htu, ht1, -, hlu⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  have htφ := GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C
  obtain ⟨-, -, huz, -, -, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  have hA : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
    intro y y' h
    apply hj
    apply hinj
    rw [← C.ι_j, ← C.ι_j, h]
  have e1 : phiA l x = (l : Per.Acris l) ^ r * x := by
    apply hA
    rw [← fund_phiB_alg, map_mul, map_pow, map_natCast, ← hx, map_mul, map_pow, hφ,
      fund_phiB_alg, htφ, map_mul, map_natCast, mul_pow]
    ring
  have ht1' : algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) ∈ Per.FilD l 1 :=
    (hP 1 _).2 ht1
  have htr : ∀ n : ℕ, algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) ^ n ∈ Per.FilD l (n : ℤ) := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact h1
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ]
      exact hmul _ _ _ _ ih ht1'
  have e2 : C.j x ∈ Per.FilP l r := by
    rw [← hP, ← C.ι_j, ← hx, map_mul, map_pow, C.ι_j]
    have := hmul _ _ _ _ hF (htr r)
    rwa [zero_add] at this
  obtain ⟨z, k, hz⟩ := GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow l C r x e1 e2
  have e3 : (l : Per.Bcris l) ^ k * b = Per.zB l z := by
    apply (htu.pow r).mul_right_cancel
    have := congrArg (algebraMap (Per.Acris l) (Per.Bcris l)) hz
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, ← hx, ← fund_zB, ← mul_assoc] at this
    exact this
  refine ⟨(z : ℚ_[l]) / (l : ℚ_[l]) ^ k, ?_⟩
  apply (hlu.pow k).mul_left_cancel
  rw [e3, ← huz]
  have hl : (l : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have e4 : (z : ℚ_[l]) = (l : ℚ_[l]) ^ k * ((z : ℚ_[l]) / (l : ℚ_[l]) ^ k) := by
    field_simp
  conv_rhs => rw [e4]
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQpStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_frobenius_fixed_fil_zero_eq_qp : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (b : Per.Bcris l), Per.φB l b = b → C.ι b ∈ Per.FilD l 0 → ∃ c : ℚ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = b := by
  first | exact @GlobalTheory.MemLoc.fundamental_exact | exact GlobalTheory.MemLoc.fundamental_exact | (intros; apply GlobalTheory.MemLoc.fundamental_exact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Formalism.UG.P Formalism.EigenvalueLevelCeiling GlobalTheory.AdeleBaseChange
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwistPlaces

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_int {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) :
    Valued.v (algebraMap K (P.adicCompletion K) (algebraMap (𝓞 K) K b)) = P.intValuation b := by
  rw [levelaf_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

theorem intValuation_eq_one {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K}
    (h : b ∉ P.asIdeal) : P.intValuation b = 1 :=
  le_antisymm (P.intValuation_le_one b) (not_lt.1 fun h' => h ((P.intValuation_lt_one_iff_mem b).1 h'))

variable (F E) in
abbrev toId : (RInt F E)ˣ →* (AfE F E)ˣ := Units.map (RInt F E).subtype.toMonoidHom

theorem exists_toId_eq {x : (AfE F E)ˣ} (hx : x ∈ intU F E) : ∃ u, toId F E u = x :=
  ⟨⟨⟨x, hx.1⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx.2⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩, Units.ext rfl⟩

section
variable {ι : AfE F E →+* FiniteAdeleRing (𝓞 E) E}
  (hι : ∀ x a, ι (x ⊗ₜ[F] a) = algebraMap E _ x * adMap F E a)
include hι

theorem mem_suppAt (v : HeightOneSpectrum (𝓞 F)) (y : (AfE F E)ˣ) :
    y ∈ suppAt E v ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ≠ v → ι (y : AfE F E) P = 1 := by
  have h1 : y ∈ suppAt E v ↔ ∀ v', v' ≠ v → prV (E := E) v' (y : AfE F E) = 1 := by
    simp only [suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [h1]
  simp only [prV_eq_one_iff hι]
  exact ⟨fun h P hP => h _ hP P rfl, fun h v' hv P hP => h P (hP ▸ hv)⟩

end

theorem inertAt_le_congN {v : HeightOneSpectrum (𝓞 F)} {N : ℕ} (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    inertAt E v ≤ congN F E N := by
  obtain ⟨ι, hι⟩ := exists_toAd F E
  rintro x ⟨h1, h2⟩
  obtain ⟨u, rfl⟩ := exists_toId_eq h1
  have hN0 : (N : E) ≠ 0 := by
    rintro h
    obtain rfl : N = 0 := by exact_mod_cast h
    exact hN (by simp)
  refine ⟨u, (mem_kerRed _ u).2 (Ideal.mem_span_singleton'.2
    ⟨⟨((N : E)⁻¹ ⊗ₜ[F] 1 : AfE F E) * (((u : RInt F E) - 1 : RInt F E) : AfE F E), mem_int_of_map hι fun P => ?_⟩, Subtype.ext ?_⟩), rfl⟩
  · rw [map_mul, map_tmul_one hι, afsplit_mul_apply, HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hP : P.under (𝓞 F) = v
    · have hNP : (N : 𝓞 E) ∉ P.asIdeal := fun h => hN (by
        rw [← hP]
        change algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
        rwa [map_natCast])
      have h3 : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P) = 1 := by
        change Valued.v (algebraMap E (P.adicCompletion E) (N : E)⁻¹) = 1
        rw [map_inv₀, map_inv₀, ← map_natCast (algebraMap (𝓞 E) E), valued_int, intValuation_eq_one P hNP, inv_one]
      rw [map_mul, h3, one_mul]
      exact map_mem_int hι ((u : RInt F E) - 1).2 P
    · have h3 : ι ((u : RInt F E) : AfE F E) P = 1 := (mem_suppAt hι v _).1 h2 P hP
      rw [AddSubgroupClass.coe_sub, map_sub, afsplit_sub_apply, h3, OneMemClass.coe_one, map_one, afsplit_one_apply, sub_self,
        mul_zero, map_zero]
      exact zero_le_one
  · apply map_injective hι
    rw [Subring.coe_mul, SubringClass.coe_natCast, map_mul, map_mul, map_natCast, map_tmul_one hι, mul_right_comm,
      ← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)), ← map_mul, inv_mul_cancel₀ hN0, map_one, one_mul]

variable {L : Type} [Field L]

theorem finite_Qprime {ξ : Chr F E L} (h : ξ ∈ openChr F E L) : (Qprime ξ).Finite := by
  obtain ⟨N, hN, hk⟩ := h
  have h0 : (Ideal.span {(N : 𝓞 F)}) ≠ ⊥ := by simpa using hN.ne'
  refine (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 (by_contra fun hn => hv ?_)
  exact (inertAt_le_congN hn).trans hk

end Local

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem under_eq_iff {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)} :
    P.under (𝓞 F) = v ↔ P.asIdeal.under (𝓞 F) = v.asIdeal :=
  ⟨fun h => h ▸ rfl, fun h => HeightOneSpectrum.ext h⟩

end Res

section Datum

open Formalism.L2.Col

variable {X : Fields}

theorem exists_of_conj_eq (hX : X.Ok) {a : 𝓞 X.E} (ha : X.conjO a = a) :
    ∃ r : 𝓞 X.F, algebraMap (𝓞 X.F) (𝓞 X.E) r = a := by
  let c : X.E →ₐ[X.F] X.E := { starRingEnd X.E with commutes' := hX.star_F }
  let M : IntermediateField X.F X.E :=
    (AlgHom.equalizer c (AlgHom.id _ _)).toIntermediateField fun x hx => by
      have hx' : star x = x := hx
      change star x⁻¹ = x⁻¹
      rw [star_inv₀, hx']
  have hM : M = ⊥ := by
    have := IntermediateField.isSimpleOrder_of_finrank_prime X.F X.E (by rw [hX.rankE]; exact Nat.prime_two)
    refine (eq_bot_or_eq_top M).resolve_right fun e => ?_
    obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hX.f_pos
    refine hX.emb_ne τ τ (RingHom.ext fun x => ?_)
    have h1 : x ∈ M := e ▸ IntermediateField.mem_top
    exact congrArg (X.emb τ) (show star x = x from h1).symm
  have h2 : (a : X.E) ∈ M := congrArg (fun z : 𝓞 X.E => (z : X.E)) ha
  rw [hM, IntermediateField.mem_bot] at h2
  obtain ⟨x, hx⟩ := h2
  have h3 : IsIntegral ℤ x := by
    rw [← isIntegral_algebraMap_iff (B := X.E), hx]
    exact RingOfIntegers.isIntegral_coe _
  exact ⟨⟨x, h3⟩, RingOfIntegers.ext hx⟩

variable {S : Set ℕ} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}

theorem mem_QE_iff (hsel : IsSel X sel) (ξ : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)} :
    P ∈ QE sel (ξ : Chr X.F X.E X.K) ↔
      P.under (𝓞 X.F) ∈ Qprime (ξ : Chr X.F X.E X.K) ∧ sel (P.under (𝓞 X.F)) = P := by
  classical
  have hf := finite_Qprime (ξ := (ξ : Chr X.F X.E X.K)) ξ.2.1.1.1.1.2
  rw [QE, dite_eq_left hf, Finset.mem_image]
  simp only [Set.Finite.mem_toFinset]
  refine ⟨?_, fun h => ⟨_, h.1, h.2⟩⟩
  rintro ⟨v, hv, rfl⟩
  rw [under_eq_iff.2 (hsel v)]
  exact ⟨hv, rfl⟩

end Datum

end GlobalTheory.TwistPlaces
end
end
