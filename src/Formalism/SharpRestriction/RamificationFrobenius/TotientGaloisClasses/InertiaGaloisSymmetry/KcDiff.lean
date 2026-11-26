module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcEqOfPowEqOne

@[expose] public section

section -- merged from Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcPair
namespace Formalism.HC.Der

section
open Ideal UniqueFactorizationMonoid

private theorem mulEquiv_ideal_bot_eq_bot {S : Type*} [CommRing S] [IsDedekindDomain S]
    (f : Ideal S ≃* Ideal S) : f ⊥ = ⊥ := by
  obtain ⟨J, hJ⟩ := f.surjective ⊥
  calc f ⊥ = f (⊥ * J) := by rw [Ideal.bot_mul]
    _ = f ⊥ * f J := map_mul f _ _
    _ = ⊥ := by rw [hJ, Ideal.mul_bot]

private theorem prime_mulEquiv_ideal_apply {S : Type*} [CommRing S] [IsDedekindDomain S]
    (f : Ideal S ≃* Ideal S) {P : Ideal S} (hP : Prime P) : Prime (f P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hP.ne_zero
    apply f.injective
    rw [Ideal.zero_eq_bot] at h ⊢
    rw [h, mulEquiv_ideal_bot_eq_bot f]
  · intro hu
    apply hP.not_unit
    rw [isUnit_iff_eq_one] at hu ⊢
    apply f.injective
    rw [hu, map_one]
  · intro a b h
    have h' : P ∣ f.symm a * f.symm b := by
      have := map_dvd f.symm h
      rwa [map_mul, MulEquiv.symm_apply_apply] at this
    rcases hP.dvd_or_dvd h' with h1 | h1
    · left
      have := map_dvd f h1
      rwa [MulEquiv.apply_symm_apply] at this
    · right
      have := map_dvd f h1
      rwa [MulEquiv.apply_symm_apply] at this

private theorem prod_normalizedFactors_ideal_eq_self {S : Type*} [CommRing S] [IsDedekindDomain S]
    {I : Ideal S} (hI : I ≠ ⊥) : (normalizedFactors I).prod = I := by
  have hI0 : I ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hI
  exact associated_iff_eq.mp (prod_normalizedFactors hI0)

theorem kc_nf_map {S : Type*} [CommRing S] [IsDedekindDomain S] (I : Ideal S) (hI : I ≠ ⊥)
    (f : Ideal S ≃* Ideal S) : normalizedFactors (f I) = (normalizedFactors I).map f := by
  calc normalizedFactors (f I) = normalizedFactors ((normalizedFactors I).map f).prod := by
        rw [← map_multiset_prod f, prod_normalizedFactors_ideal_eq_self hI]
    _ = (normalizedFactors I).map f := by
        apply normalizedFactors_prod_of_prime
        intro Q hQ
        obtain ⟨R, hR, rfl⟩ := Multiset.mem_map.mp hQ
        exact prime_mulEquiv_ideal_apply f (prime_of_normalized_factor R hR)

private theorem mem_of_prime_dvd_multiset_prod {S : Type*} [CommRing S] [IsDedekindDomain S]
    {s : Multiset (Ideal S)} (hs : ∀ Q ∈ s, Prime Q) {P : Ideal S} (hP : Prime P)
    (h : P ∣ s.prod) : P ∈ s := by
  obtain ⟨Q, hQ, hPQ⟩ := hP.exists_mem_multiset_dvd h
  rwa [(prime_dvd_prime_iff_eq hP (hs Q hQ)).mp hPQ]

theorem kc_pairing {S : Type*} [CommRing S] [IsDedekindDomain S] (D : Ideal S) (hD0 : D ≠ ⊥)
    (f : Ideal S ≃* Ideal S) (hfD : f D = D) (p : Ideal S → Prop)
    (hp : ∀ P ∈ normalizedFactors D, (p (f P) ↔ ¬ p P)) :
    ∃ B : Ideal S, D = B * f B ∧ (∀ P : Ideal S, P.IsPrime → P ∣ B → p P) ∧ B ⊔ f B = ⊤ ∧
      (∀ g : Ideal S ≃* Ideal S, g D = D → (∀ P ∈ normalizedFactors D, (p (g P) ↔ p P)) → g B = B) ∧
      ∀ B' : Ideal S, D = B' * f B' → (∀ P : Ideal S, P.IsPrime → P ∣ B' → p P) → B' = B := by
  classical
  obtain ⟨F, hFdef⟩ : ∃ F, F = normalizedFactors D := ⟨_, rfl⟩
  have hFp : ∀ Q ∈ F, Prime Q := fun Q hQ => prime_of_normalized_factor Q (hFdef ▸ hQ)
  have hpF : ∀ P ∈ F, (p (f P) ↔ ¬ p P) := fun P hP => hp P (hFdef ▸ hP)
  have hinv : ∀ g : Ideal S ≃* Ideal S, g D = D → F.map g = F := by
    intro g hg
    have := kc_nf_map D hD0 g
    rw [hg] at this
    rw [hFdef]
    exact this.symm
  have hFprod : F.prod = D := by rw [hFdef]; exact prod_normalizedFactors_ideal_eq_self hD0
  have hmap : (F.filter p).map f = F.filter (fun P => ¬ p P) := by
    have e1 : F.filter (fun P => ¬ p P) = (F.map f).filter (fun P => ¬ p P) := by
      rw [hinv f hfD]
    have e2 : (F.map f).filter (fun P => ¬ p P) = (F.filter (fun P => ¬ p (f P))).map f := by
      rw [Multiset.filter_map]
      rfl
    have e3 : F.filter (fun P => ¬ p (f P)) = F.filter p :=
      Multiset.filter_congr (fun P hP => by rw [hpF P hP]; exact not_not)
    rw [e1, e2, e3]
  have hsplit : D = (F.filter p).prod * f (F.filter p).prod := by
    rw [map_multiset_prod, hmap, Multiset.prod_filter_mul_prod_filter_not, hFprod]
  have hB0 : (F.filter p).prod ≠ ⊥ := by
    intro h
    apply hD0
    rw [hsplit, h, Ideal.bot_mul]
  have hprime_ne : ∀ {P J : Ideal S}, J ≠ ⊥ → P.IsPrime → P ∣ J → Prime P := by
    intro P J hJ hP hPJ
    refine Ideal.prime_of_isPrime ?_ hP
    rintro rfl
    exact hJ (zero_dvd_iff.mp hPJ)
  have hsupp : ∀ P : Ideal S, P.IsPrime → P ∣ (F.filter p).prod → p P := by
    intro P hP hdvd
    have hm := mem_of_prime_dvd_multiset_prod (fun Q hQ => hFp Q (Multiset.mem_of_mem_filter hQ))
      (hprime_ne hB0 hP hdvd) hdvd
    exact (Multiset.mem_filter.mp hm).2
  refine ⟨(F.filter p).prod, hsplit, hsupp, ?_, ?_, ?_⟩
  · by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM1 : M ∣ (F.filter p).prod := Ideal.dvd_iff_le.mpr (le_sup_left.trans hle)
    have hM2 : M ∣ f (F.filter p).prod := Ideal.dvd_iff_le.mpr (le_sup_right.trans hle)
    have hpM := hsupp M hM.isPrime hM1
    rw [map_multiset_prod, hmap] at hM2
    have hm := mem_of_prime_dvd_multiset_prod (fun Q hQ => hFp Q (Multiset.mem_of_mem_filter hQ))
      (hprime_ne hB0 hM.isPrime hM1) hM2
    exact (Multiset.mem_filter.mp hm).2 hpM
  · intro g hgD hgp
    have e1 : (F.map g).filter p = (F.filter (fun P => p (g P))).map g := by
      rw [Multiset.filter_map]
      rfl
    have e2 : F.filter (fun P => p (g P)) = F.filter p :=
      Multiset.filter_congr (fun P hP => hgp P (hFdef ▸ hP))
    rw [map_multiset_prod, ← e2, ← e1, hinv g hgD, e2]
  · intro B' hB' hsupp'
    have hB'0 : B' ≠ ⊥ := by
      intro h; apply hD0; rw [hB', h, Ideal.bot_mul]
    have hfB'0 : f B' ≠ ⊥ := by
      intro h; apply hD0; rw [hB', h, Ideal.mul_bot]
    have hB'0' : B' ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hB'0
    have hfB'0' : f B' ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hfB'0
    have hF' : F = normalizedFactors B' + (normalizedFactors B').map f := by
      rw [hFdef, hB', normalizedFactors_mul hB'0' hfB'0', kc_nf_map B' hB'0 f]
    have hpB' : ∀ Q ∈ normalizedFactors B', p Q := by
      intro Q hQ
      exact hsupp' Q (Ideal.isPrime_of_prime (prime_of_normalized_factor Q hQ))
        (dvd_of_mem_normalizedFactors hQ)
    have hfilt : F.filter p = normalizedFactors B' := by
      rw [hF', Multiset.filter_add, Multiset.filter_eq_self.mpr hpB',
        Multiset.filter_eq_nil.mpr, add_zero]
      intro Q hQ
      obtain ⟨R, hR, rfl⟩ := Multiset.mem_map.mp hQ
      have hRF : R ∈ F := by rw [hF']; exact Multiset.mem_add.mpr (Or.inl hR)
      exact fun h => ((hpF R hRF).mp h) (hpB' R hR)
    rw [hfilt, prod_normalizedFactors_ideal_eq_self hB'0]

end

open NumberField Ideal

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem kc_not_dvd_different (M E : Type) [Field M] [NumberField M] [Field E] [NumberField E] [Algebra M E] [IsGalois M E]
    (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : P ≠ ⊥ → ∀ σ : E ≃ₐ[M] E, (∀ x : 𝓞 E, σ • x - x ∈ P) → σ = 1) : ¬ P ∣ differentIdeal (𝓞 M) (𝓞 E) := by
  by_cases hP : P = ⊥
  · subst hP
    intro hdvd
    apply differentIdeal_ne_bot (A := 𝓞 M) (B := 𝓞 E)
    rw [← Ideal.zero_eq_bot] at hdvd ⊢
    exact zero_dvd_iff.mp hdvd
  · have hp0 : P.under (𝓞 M) ≠ ⊥ := fun h0 => hP (Ideal.eq_bot_of_comap_eq_bot h0)
    haveI hmax : (P.under (𝓞 M)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp0
    haveI hfin : Finite (P.under (𝓞 M)).ResidueField := by
      haveI : Finite ((𝓞 M) ⧸ P.under (𝓞 M)) := Ideal.finiteQuotientOfFreeOfNeBot _ hp0
      exact Finite.of_surjective _
        (Ideal.bijective_algebraMap_quotient_residueField (P.under (𝓞 M))).2
    rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 M)) P (E ≃ₐ[M] E),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[M] E) (P.under (𝓞 M)) P,
      Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
    intro σ hσ
    exact h hP σ hσ

end Formalism.HC.Der
end

open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

abbrev kcBelow (P : Ideal (𝓞 H.E)) : Ideal (𝓞 H.K) := P.comap (algebraMap (𝓞 H.K) (𝓞 H.E))

theorem kc_below_smul (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ ∈ φ.Psi) (P : Ideal (𝓞 H.E)) :
    kcBelow H (σ • P) = kcBelow H P := by
  ext a
  simp only [kcBelow, Ideal.mem_comap]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hσ' : H.gal σ⁻¹ ∈ φ.Psi := by
    rw [map_inv]
    exact inv_mem hσ
  have e : σ⁻¹ • algebraMap (𝓞 H.K) (𝓞 H.E) a = algebraMap (𝓞 H.K) (𝓞 H.E) a := by
    apply NumberField.RingOfIntegers.ext
    show σ⁻¹ ((a : H.K) : H.E) = ((a : H.K) : H.E)
    exact kc_fixK H σ⁻¹ hσ' (a : H.K)
  rw [e]

private theorem liesOver_span_of_natCast_mem_prime {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [hP : P.IsPrime] (p : ℕ)
    (hp : p.Prime) (h : (p : 𝓞 M) ∈ P) : P.LiesOver (span {(p : ℤ)}) := by
  constructor
  have hmax : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  refine hmax.eq_of_le (inferInstance : (P.under ℤ).IsPrime).ne_top ?_
  rw [Ideal.span_singleton_le_iff_mem]
  show algebraMap ℤ (𝓞 M) (p : ℤ) ∈ P
  simpa using h

theorem kc_exists_prime {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [hP : P.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (hm : (n : 𝓞 M) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ P.LiesOver (span {(p : ℤ)}) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hm))
  have hpm := Nat.minFac_prime hn1
  obtain ⟨k, hk⟩ := Nat.minFac_dvd n
  have hm' : (n.minFac : 𝓞 M) * (k : 𝓞 M) ∈ P := by
    rw [← Nat.cast_mul, ← hk]
    exact hm
  rcases hP.mem_or_mem hm' with h | h
  · exact ⟨n.minFac, hpm, Nat.minFac_dvd n, liesOver_span_of_natCast_mem_prime P _ hpm h⟩
  · have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
      exact hn hk
    have hkn : k < n := by
      have h2 := hpm.two_le
      have hkpos := Nat.pos_of_ne_zero hk0
      rw [hk]
      nlinarith
    obtain ⟨p, hp, hpk, hl⟩ := ih k hkn hk0 h
    exact ⟨p, hp, hpk.trans (Dvd.intro_left _ hk.symm), hl⟩

theorem kc_conj_sq : H.conj * H.conj = 1 := by
  apply H.gal.injective
  rw [map_mul, kc_gal_conj, map_one]
  ext <;> simp [Frame.cc, c0]

variable (C : HostCore H)
include C

theorem diffSupport : ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) →
    ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P := by
  intro P hP hdvd
  have := H.galois
  by_contra hnot
  refine kc_not_dvd_different H.K H.E P ?_ hdvd
  intro hbot σ hσ
  have hn0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  obtain ⟨l, hl, -, hlo⟩ := kc_exists_prime P (Ideal.absNorm P) hn0 (Ideal.absNorm_mem P)
  have : Fact l.Prime := ⟨hl⟩
  have hlP : (l : 𝓞 H.E) ∈ P := by
    have h1 : (l : ℤ) ∈ P.under ℤ := by
      rw [← hlo.over]
      exact Ideal.mem_span_singleton_self _
    simpa using h1
  have hlq : ¬ l ∣ H.QS * H.q := by
    rintro ⟨m, hm⟩
    apply hnot
    rw [hm, Nat.cast_mul]
    exact P.mul_mem_right _ hlP
  obtain ⟨u, hu, hgal⟩ := (C.inertia l P (σ.restrictScalars ℚ)).mp fun x => hσ x
  have hmod : (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] :=
    Nat.ModEq.of_dvd (Nat.dvd_ordCompl_of_dvd_not_dvd (Dvd.intro _ rfl) hlq) hu
  rcases H.art_d u hmod with h1 | h1
  · have h2 : σ.restrictScalars ℚ = 1 := H.gal.injective (by rw [hgal, h1, map_one])
    ext x
    exact congrArg (fun τ : H.E ≃ₐ[ℚ] H.E => τ x) h2
  · exfalso
    have hpsi := kc_restrict_mem_Psi H σ
    rw [hgal, h1] at hpsi
    exact kc_iod_not_mem hpsi

theorem kc_below_ne (P : Ideal (𝓞 H.E)) [P.IsPrime] (hm : ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P) :
    kcBelow H P ≠ kcBelow H (H.conj • P) := by
  have := H.galois
  intro heq
  have hn0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_pos.ne' (by
    rintro h0
    have := H.QS_coprime
    rw [h0, zero_mul, Nat.coprime_zero_right] at this
    have h2 := kc_two_dvd H
    rw [this] at h2
    omega)
  obtain ⟨l, hl, hldvd, hlo⟩ := kc_exists_prime P (H.QS * H.q) hn0 hm
  have : P.LiesOver (kcBelow H P) := ⟨rfl⟩
  have : (H.conj • P).LiesOver (kcBelow H P) := ⟨heq⟩
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isGaloisGroup (kcBelow H P) P (H.conj • P) (H.E ≃ₐ[H.K] H.E)
  have hτ' : (τ.restrictScalars ℚ) • P = H.conj • P := hτ
  have hst : (τ.restrictScalars ℚ)⁻¹ * H.conj ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← hτ', inv_smul_smul]
  have hpsi := C.decomp_typeI l hl hldvd P _ hst
  rw [map_mul, map_inv, Subgroup.mul_mem_cancel_left _ (inv_mem (kc_restrict_mem_Psi H τ)),
    kc_gal_conj] at hpsi
  exact kc_cc_not_mem hpsi

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem principal : ∃ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) ∧ 𝔟 ⊔ H.conj • 𝔟 = ⊤ ∧
    ∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ φ.Psi → σ • 𝔟 = 𝔟 := by
  have := H.galois
  obtain ⟨f, hf⟩ : ∃ f : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E), ∀ I, f I = H.conj • I :=
    ⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) H.conj).toMulEquiv, fun _ => rfl⟩
  have hD0 : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have hfD : f (differentIdeal (𝓞 H.K) (𝓞 H.E)) = differentIdeal (𝓞 H.K) (𝓞 H.E) := by
    rw [hf]
    exact kc_diff_smul_eq H H.conj
  have hcc : ∀ I : Ideal (𝓞 H.E), H.conj • H.conj • I = I := fun I => by
    rw [← mul_smul, kc_conj_sq, one_smul]
  let p : Ideal (𝓞 H.E) → Prop := fun P =>
    WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))
  have hp : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (differentIdeal (𝓞 H.K) (𝓞 H.E)),
      (p (f P) ↔ ¬ p P) := by
    intro P hP
    have hPp : P.IsPrime :=
      Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
    have hPd : P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hne := kc_below_ne H C P (diffSupport H C P hPp hPd)
    show WellOrderingRel (kcBelow H (f P)) (kcBelow H (H.conj • f P)) ↔
      ¬ WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))
    rw [hf, hcc]
    constructor
    · intro h1 h2
      exact asymm h1 h2
    · intro h1
      rcases trichotomous_of WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P)) with h | h | h
      · exact absurd h h1
      · exact absurd h hne
      · exact h
  obtain ⟨B, hB, -, hBtop, hinv, -⟩ := kc_pairing _ hD0 f hfD p hp
  refine ⟨B, ?_, ?_, fun σ hσ => ?_⟩
  · rw [← hf]
    exact hB
  · rw [← hf]
    exact hBtop
  · obtain ⟨g, hg⟩ : ∃ g : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E), ∀ I, g I = σ • I :=
      ⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) σ).toMulEquiv, fun _ => rfl⟩
    rw [← hg]
    refine hinv g (by rw [hg]; exact kc_diff_smul_eq H σ) fun P _ => ?_
    have hn : H.gal (H.conj * σ * H.conj⁻¹) ∈ φ.Psi := by
      have hσ' : φ.chD (H.gal σ) = 1 := hσ
      show φ.chD (H.gal (H.conj * σ * H.conj⁻¹)) = 1
      simp only [map_mul, map_inv, hσ', mul_one, mul_inv_cancel]
    have e1 : (H.conj * σ * H.conj⁻¹) • H.conj • P = H.conj • σ • P := by
      rw [← mul_smul, inv_mul_cancel_right, mul_smul]
    show WellOrderingRel (kcBelow H (g P)) (kcBelow H (H.conj • g P)) ↔
      WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))
    rw [hg, kc_below_smul H σ hσ P, ← e1, kc_below_smul H _ hn]

theorem discr_sq : discr H.E = discr H.F ^ 2 := by
  have := C.cm
  have hdiff : differentIdeal (𝓞 H.F) (𝓞 H.E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
    refine kc_not_dvd_different H.F H.E P ?_ (Ideal.dvd_iff_le.mpr hle)
    intro hbot σ hσ
    have hmem : σ ∈ Subgroup.zpowers (IsCMField.complexConj H.E) := by
      rw [IsCMField.zpowers_complexConj_eq_top]
      exact Subgroup.mem_top σ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h2 : k % (orderOf (IsCMField.complexConj H.E) : ℤ) = k % 2 := by
      rw [IsCMField.orderOf_complexConj]
      rfl
    rw [← zpow_mod_orderOf, h2] at hσ ⊢
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [hk, zpow_zero]
    · exfalso
      rw [hk, zpow_one] at hσ
      exact kc_unr H C P hPmax.isPrime hbot hσ
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow H.F (𝓞 H.F) H.E (𝓞 H.E)
  rw [hdiff, Ideal.absNorm_top, one_mul, Algebra.IsQuadraticExtension.finrank_eq_two] at h
  have hsign : (discr H.E).sign = 1 := by
    rw [sign_discr]
    have h1 := IsTotallyComplex.finrank H.E
    rw [C.finrank_E] at h1
    have h3 : NumberField.InfinitePlace.nrComplexPlaces H.E = 2 * φ.ord := by omega
    rw [h3, pow_mul, neg_one_sq, one_pow]
  rw [← Int.sign_mul_natAbs (discr H.E), hsign, one_mul, h, Nat.cast_pow, Int.natAbs_sq]

end Formalism.HC.Der

end
