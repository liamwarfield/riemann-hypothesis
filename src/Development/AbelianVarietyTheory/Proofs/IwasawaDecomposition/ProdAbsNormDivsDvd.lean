module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionReducedOfJacobson
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConductorAdicCompletionEssFiniteType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSingleSingle
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalValueLocalPrismAinfWittTensor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.BasePrimes

section General

variable {E : Type} [Field E] [NumberField E]

theorem prod_absNorm_divs_dvd {a : 𝓞 E} (ha : a ≠ 0) :
    ∏ P ∈ divs a, Ideal.absNorm P.asIdeal ∣ Ideal.absNorm (Ideal.span {a}) := by
  rw [← map_prod]
  apply map_dvd
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro P _ Q _ hPQ
    exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ)
  · intro P hP
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact (mem_divs ha P).1 hP

theorem le_absNorm_of_mem {p : ℕ} (hp : p.Prime) (P : HeightOneSpectrum (𝓞 E)) (h : (p : 𝓞 E) ∈ P.asIdeal) :
    p ≤ Ideal.absNorm P.asIdeal := by
  have h1 : Ideal.absNorm P.asIdeal ∣ p ^ Module.finrank ℚ E := by
    rw [← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h1
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
    exact absurd hk P.isPrime.ne_top
  · rw [hk]
    exact Nat.le_self_pow hk0.ne' p

theorem absNorm_eq_of_split {p : ℕ} (hp : p.Prime) (h : (divs (p : 𝓞 E)).card = Module.finrank ℚ E)
    (P : HeightOneSpectrum (𝓞 E)) (hP : (p : 𝓞 E) ∈ P.asIdeal) : Ideal.absNorm P.asIdeal = p := by
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 := prod_absNorm_divs_dvd hp0
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, ← h] at h1
  have h2 := Nat.le_of_dvd (pow_pos hp.pos _) h1
  by_contra hne
  have hlt : p < Ideal.absNorm P.asIdeal := lt_of_le_of_ne (le_absNorm_of_mem hp P hP) (Ne.symm hne)
  have h3 : ∏ _Q ∈ divs (p : 𝓞 E), p < ∏ Q ∈ divs (p : 𝓞 E), Ideal.absNorm Q.asIdeal :=
    Finset.prod_lt_prod₀ (fun _ _ => hp.pos) (fun Q hQ => le_absNorm_of_mem hp Q ((mem_divs hp0 Q).1 hQ))
      ⟨P, (mem_divs hp0 P).2 hP, hlt⟩
  rw [Finset.prod_const] at h3
  omega

theorem card_divs_map_le (s : 𝓞 E →+* 𝓞 E) (hs : Function.Surjective s) {a : 𝓞 E} (ha : a ≠ 0) (hsa : s a ≠ 0) :
    (divs (s a)).card ≤ (divs a).card := by
  refine Finset.card_le_card_of_injOn (fun P => HeightOneSpectrum.comap s hs P) ?_ ?_
  · intro P hP
    have h1 := (mem_divs hsa P).1 hP
    exact (mem_divs ha _).2 h1
  · intro P _ Q _ hPQ
    apply HeightOneSpectrum.ext
    exact Ideal.comap_injective_of_surjective s hs (congrArg HeightOneSpectrum.asIdeal hPQ)

theorem split_facts (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) {p f : ℕ} (hp : p.Prime)
    (hf : Module.finrank ℚ E = 2 * f) (h : (placesOver E p).ncard = Module.finrank ℚ E) {a : 𝓞 E}
    (ha : a * s a = (p : 𝓞 E)) :
    IsCoprime a (s a) ∧ ((divs a).card = f ∧ ∀ P ∈ divs a, Ideal.absNorm P.asIdeal = p) ∧
      ((divs (s a)).card = f ∧ ∀ P ∈ divs (s a), Ideal.absNorm P.asIdeal = p) := by
  classical
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (ha ▸ hp0)
  have hb0 : s a ≠ 0 := right_ne_zero_of_mul (ha ▸ hp0)
  have hsurj : Function.Surjective s := fun x => ⟨s x, hs x⟩
  have hc : (divs (p : 𝓞 E)).card = Module.finrank ℚ E := by
    rw [← h, ← Set.ncard_coe_finset]
    congr 1
    ext P
    exact mem_divs hp0 P
  have hna : ∀ P ∈ divs a, Ideal.absNorm P.asIdeal = p := fun P hP =>
    absNorm_eq_of_split hp hc P (ha ▸ Ideal.mul_mem_right _ _ ((mem_divs ha0 P).1 hP))
  have hnb : ∀ P ∈ divs (s a), Ideal.absNorm P.asIdeal = p := fun P hP =>
    absNorm_eq_of_split hp hc P (ha ▸ Ideal.mul_mem_left _ _ ((mem_divs hb0 P).1 hP))
  have hU : divs (p : 𝓞 E) = divs a ∪ divs (s a) := by
    ext P
    rw [Finset.mem_union, mem_divs hp0, mem_divs ha0, mem_divs hb0, ← ha]
    exact P.isPrime.mul_mem_iff_mem_or_mem
  have hle : (divs a).card + (divs (s a)).card ≤ Module.finrank ℚ E := by
    have h1 := prod_absNorm_divs_dvd ha0
    have h2 := prod_absNorm_divs_dvd hb0
    rw [Finset.prod_congr rfl hna, Finset.prod_const] at h1
    rw [Finset.prod_congr rfl hnb, Finset.prod_const] at h2
    have h3 := mul_dvd_mul h1 h2
    rw [← pow_add, ← map_mul, Ideal.span_singleton_mul_span_singleton, ha, Ideal.absNorm_span_natCast,
      RingOfIntegers.rank] at h3
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h3
  have hui := Finset.card_union_add_card_inter (divs a) (divs (s a))
  rw [← hU, hc] at hui
  have e1 := card_divs_map_le s hsurj ha0 hb0
  have e2 := card_divs_map_le s hsurj hb0 (by rw [hs]; exact ha0)
  rw [hs] at e2
  have hint : divs a ∩ divs (s a) = ∅ := Finset.card_eq_zero.1 (by omega)
  refine ⟨?_, ⟨by omega, hna⟩, ⟨by omega, hnb⟩⟩
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨M, hM, hle'⟩ := Ideal.exists_le_maximal _ hne
  have haM : a ∈ M := hle' (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))
  have hbM : s a ∈ M := hle' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (s a)))
  have hM0 : M ≠ ⊥ := fun h0 => ha0 (by rwa [h0, Ideal.mem_bot] at haM)
  have hmem : (⟨M, hM.isPrime, hM0⟩ : HeightOneSpectrum (𝓞 E)) ∈ divs a ∩ divs (s a) :=
    Finset.mem_inter.2 ⟨(mem_divs ha0 _).2 haM, (mem_divs hb0 _).2 hbM⟩
  rw [hint] at hmem
  exact Finset.notMem_empty _ hmem

theorem modEq_one_of_dvd (s : 𝓞 E →+* 𝓞 E) {a : 𝓞 E} {T c : ℕ} (ha : a * s a = (T : 𝓞 E))
    (h : (c : 𝓞 E) ∣ a - 1) : T ≡ 1 [MOD c] := by
  obtain ⟨y, hy⟩ := h
  have h1 : a = 1 + (c : 𝓞 E) * y := by
    rw [← hy]
    ring
  have h2 : s a = 1 + (c : 𝓞 E) * s y := by
    rw [h1, map_add (f := _), map_one, map_mul, map_natCast]
  have h3 : (c : 𝓞 E) ∣ (((T : ℤ) - 1 : ℤ) : 𝓞 E) := by
    refine ⟨y + s y + (c : 𝓞 E) * (y * s y), ?_⟩
    push_cast
    rw [← ha, h2]
    nth_rewrite 1 [h1]
    ring
  exact (Nat.modEq_iff_dvd.2 (Primes.natCast_dvd_intCast h3)).symm

end General

theorem conjO_conjO (B : Base) (x : 𝓞 B.fields.E) : B.fields.conjO (B.fields.conjO x) = x := by
  letI := B.fields.starE
  apply RingOfIntegers.ext
  exact star_star (x : B.fields.E)

theorem finrank_E (B : Base) : Module.finrank ℚ B.fields.E = 2 * B.fields.f := by
  rw [B.fields_f]
  show Module.finrank ℚ B.host.E = _
  rw [B.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

theorem mem_Kq (B : Base) {x : B.host.E} (hx : x ∈ B.host.K) : x ∈ B.fields.Kq := by
  intro τ τ'
  rw [B.fields_emb_apply, B.fields_emb_apply, Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K B.host _ τ.2 x hx,
    Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K B.host _ τ'.2 x hx]

theorem primes_ok : ∀ (B : Base) (X : PreX B.toPre), (B.primes X).Ok ∧ (B.primes X).PiGCong := by
  intro B X
  have hG := fun i => split_facts B.fields.conjO (conjO_conjO B) (B.host.g_prime i) (finrank_E B)
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ (B.host.g_prime i) (B.g_cond i)).1 (B.primes_piG_norm X i)
  have hT := fun u => split_facts B.fields.conjO (conjO_conjO B) (B.T_prime u) (finrank_E B)
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ (B.T_prime u) (B.T_cond u)).1 (B.primes_piT_norm X u)
  refine ⟨?_, B.primes_piGCong X⟩
  refine
    { g_prime := B.host.g_prime
      piG_Kq := fun i => mem_Kq B (X.piG_K i)
      piG_norm := B.primes_piG_norm X
      piG_cop := fun i => (hG i).1
      vG_card := fun i => (hG i).2.2.1
      vG_norm := fun i => (hG i).2.2.2
      g_cong := (B.primes_piGCong X).g_cong (B.primes_piG_norm X)
      g_ne := B.host.g_ne
      T_prime := B.T_prime
      piT_Kq := fun u => mem_Kq B (X.piT_K u)
      piT_norm := B.primes_piT_norm X
      piT_cop := fun u => (hT u).1
      vT_card := fun u => (hT u).2.1.1
      vT_norm := fun u => (hT u).2.1.2
      piT_cong := X.piT_cong
      T_ne_g := fun u i hi => ?_ }
  have h1 := modEq_one_of_dvd B.fields.conjO (B.primes_piT_norm X u) (X.piT_cong u)
  have hd : B.host.g i ∣ B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 := by
    refine Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have h2 : B.host.g i ≡ 1 [MOD B.host.g i] := by
    have h3 := h1.of_dvd hd
    rwa [hi] at h3
  have h4 : B.host.g i ∣ 1 := (Nat.modEq_zero_iff_dvd.1 (h2.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)))
  exact (B.host.g_prime i).one_lt.ne' (Nat.dvd_one.1 h4)

end GlobalTheory.BasePrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegrallyClosedOfConductorNonZeroDivisorOfAss
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegrallyClosedOfConductorNonZeroDivisorOfAss
open IsLocalRing

namespace GlobalTheory

theorem isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes
    (R : Type) [CommRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ nonZeroDivisors R)
    (hloc : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P))
    (hcond : ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) :
    IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro c hc
  obtain ⟨s, hs⟩ := hcond c hc

  suffices hmem : Ideal.Quotient.mk (Ideal.span {x}) s = 0 by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hmem
    obtain ⟨w, rfl⟩ := hmem
    refine ⟨w, ?_⟩
    have hu : IsUnit (algebraMap R (FractionRing R) x) :=
      IsLocalization.map_units (FractionRing R) ⟨x, hx⟩
    apply hu.mul_left_cancel
    rw [← hs, map_mul, mul_comm]
  have key := eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero
    (A := R) (M := R ⧸ Ideal.span {x}) (x := Ideal.Quotient.mk (Ideal.span {x}) s)
  apply key
  intro P hP
  haveI hPp : P.IsPrime := hP.isPrime
  obtain ⟨hdom, hic⟩ := hloc P hP
  let RP := Localization.AtPrime P
  let K := FractionRing RP

  have hreg : ∀ b ∈ nonZeroDivisors R, IsUnit (algebraMap R K b) := by
    intro b hb
    rw [IsScalarTower.algebraMap_apply R RP K]
    refine IsLocalization.map_units K (⟨algebraMap R RP b, ?_⟩ : nonZeroDivisors RP)
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl RP b).1 h0
    have : (t : R) = 0 := (mem_nonZeroDivisors_iff_right.1 hb) t ht
    exact t.2 (this ▸ P.zero_mem)
  let φ : FractionRing R →+* K :=
    IsLocalization.lift (M := nonZeroDivisors R) (g := algebraMap R K) fun b ↦ hreg b b.2
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap RP K (algebraMap R RP r) :=
    fun r ↦ by
      rw [IsLocalization.lift_eq, IsScalarTower.algebraMap_apply R RP K]
  have hint : IsIntegral RP (φ c) := by
    refine IsIntegral.map_of_comp_eq (algebraMap R RP) φ ?_ hc
    ext r
    simp only [RingHom.comp_apply]
    rw [hφ]
  obtain ⟨u, hu⟩ := (isIntegrallyClosed_iff K).1 hic hint
  have hxu : algebraMap R RP x * u = algebraMap R RP s := by
    apply IsFractionRing.injective RP K
    rw [map_mul, hu, ← hφ, ← hφ, hs, map_mul]
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj P.primeCompl u
  have h2 : algebraMap R RP (x * r) = algebraMap R RP (s * t) := by
    simp only at hrt
    rw [map_mul, map_mul, ← hxu, ← hrt]
    ring
  obtain ⟨t', ht'⟩ := (IsLocalization.eq_iff_exists P.primeCompl RP).1 h2
  refine ⟨t' * t, P.primeCompl.mul_mem t'.2 t.2, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton']
  refine ⟨t' * r, ?_⟩
  linear_combination ht'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegrallyClosedOfConductorNonZeroDivisorOfAssStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P)) → (∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) → IsIntegrallyClosed R := by
  first | exact @GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes | exact GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes | (intros; apply GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
namespace GlobalTheory.AnalyticNormality

open IsLocalRing

theorem completion_isDomain_and_isIntegrallyClosed :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  have hnoeth := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian
  have hquot := GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv
  have hengine := GlobalTheory.T.associated_prime_localization_dvr
  have hclosed := GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes
  have hdom := GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local
  have hred := GlobalTheory.T.adic_completion_reduced_of_jacobson
  have hcond := GlobalTheory.T.exists_conductor_adicCompletion_essFiniteType
  intro A _ _ _ _ _ _
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  set m := maximalIdeal A with hm
  let R := AdicCompletion m A
  haveI : IsNoetherianRing R := hnoeth A m
  haveI : Module.Flat A R := AdicCompletion.flat_of_isNoetherian m
  haveI : IsReduced R := hred A m (IsLocalRing.maximalIdeal_le_jacobson _)
  obtain ⟨x, hx0, hx⟩ := hcond A
  have hxR : algebraMap A R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular A x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap A R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hredq : ∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R)) := by
    intro q hq _
    obtain ⟨e⟩ := hquot A m q
    haveI : IsDomain (A ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType A (A ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (A ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (A ⧸ q)
      haveI : IsScalarTower ℤ A (A ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ A (A ⧸ q)
    have hj : m.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (A ⧸ q)) := by
      haveI : IsLocalRing (A ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      refine Ideal.mem_comap.mpr (IsLocalRing.maximalIdeal_le_jacobson _ ?_)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (hu.unit⁻¹ : (A ⧸ q)ˣ).1
      have h1 : Ideal.Quotient.mk q (a * b) = 1 := by
        rw [map_mul, hb]; exact hu.mul_val_inv
      have h2 : a * b - 1 ∈ q := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
      have h3 : a * b - 1 ∈ m := IsLocalRing.le_maximalIdeal hq.ne_top h2
      have h4 : (1 : A) ∈ m := by
        have := m.sub_mem (m.mul_mem_right b ha) h3
        simpa using this
      exact (Ideal.ne_top_iff_one m).mp (IsLocalRing.maximalIdeal.isMaximal A).ne_top h4
    haveI := hred (A ⧸ q) _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  have hcl : IsIntegrallyClosed R := by
    refine hclosed R (algebraMap A R x) hxR ?_ hx
    intro P _ hP
    obtain ⟨h1, h2⟩ := hengine A R x hx0 hredq P hP
    exact ⟨h1, inferInstance⟩
  exact ⟨hdom R hcl, hcl⟩

end GlobalTheory.AnalyticNormality
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosedStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  first | exact @GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed | exact GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed | (intros; apply GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpacesNormHasFrame
noncomputable section

namespace GlobalTheory.Mem.DiagSp

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain
open scoped TensorProduct

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem signSpace_cut_eq (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N N' p q : ℕ)
    (hN : N = N') (hp : p ≤ N) (hq : N - p = q) :
    signSpace hstar N (cut N p) = stdSpace hstar N' (fun i => decide (p ≤ i.1)) p q := by
  subst hN hq
  rw [signSpace, card_cut_false N p hp, card_cut_true N p hp]
  rfl

theorem signSpace_false_eq (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) :
    signSpace hstar N (fun _ => false) = stdSpace hstar N (fun _ => false) N 0 := by
  simp [signSpace]

def planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (a b : E) (i : Fin h) : Fin N → E :=
  Pi.single (⟨n + i, by omega⟩ : Fin N) a + Pi.single (⟨n + h + i, by omega⟩ : Fin N) b

theorem planeVec_planeVec (N n h p : ℕ) (hN : n + 2 * h ≤ N) (hp : p = n + h) (a b c d : E) (i j : Fin h) :
    diagForm N (cut N p) (planeVec N n h hN a b i) (planeVec N n h hN c d j) =
      if i = j then star a * c - star b * d else 0 := by
  subst hp
  have hi := i.isLt
  have hj := j.isLt
  have c1 : cut N (n + h) ⟨n + i, by omega⟩ = false := by simp [cut]
  have c2 : cut N (n + h) ⟨n + h + i, by omega⟩ = true := by simp [cut]
  simp only [planeVec, map_add (f := _), LinearMap.add_apply, diag_single_single, c1, c2]
  have e1 : ¬ (n + (i : ℕ) = n + h + j) := by omega
  have e2 : ¬ (n + h + (i : ℕ) = n + j) := by omega
  rw [if_neg e1, if_neg e2]
  by_cases hij : i = j
  · subst hij
    simp [sgn, sub_eq_add_neg]
  · have h' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have e3 : ¬ (n + (i : ℕ) = n + j) := by omega
    have e4 : ¬ (n + h + (i : ℕ) = n + h + j) := by omega
    rw [if_neg e3, if_neg e4, if_neg hij]
    simp

theorem ext_planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (neg : Fin N → Bool) (x : Fin n → E) (a b : E)
    (i : Fin h) : diagForm N neg (extTo n N x) (planeVec N n h hN a b i) = 0 := by
  rw [planeVec, map_add (f := _), diag_ext_single, diag_ext_single, add_zero]
  · simp only; omega
  · simp only; omega

theorem single_planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (neg : Fin N → Bool) (l : Fin N)
    (hl : n + 2 * h ≤ l) (c a b : E) (i : Fin h) :
    diagForm N neg (Pi.single l c) (planeVec N n h hN a b i) = 0 := by
  have hi := i.isLt
  rw [planeVec, map_add (f := _), diag_single_single, diag_single_single, if_neg, if_neg, add_zero]
  · simp only; omega
  · simp only; omega

end General

section Main

variable (R : Ranks)

theorem rankY_eq_N_add (j : ℕ) (hj : j < R.m) : R.rankY j = R.N j + (R.m - 1 - j) := by
  simp only [Ranks.rankY, Ranks.r, Ranks.N, mul_add]
  omega

theorem pY_eq_N_add (j : ℕ) (hj : j < R.m) : pY R j = R.N j + (R.m - 1 - j) / 2 := by
  have := rankY_eq_N_add R j hj
  simp only [pY]
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)

include hpz in
theorem top_line_norm :
    diagForm (R.N R.m) (fun _ => false)
      (Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz)
      (Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz) = (T : E) := by
  refine (diag_single_single _ (fun _ => false) _ _ pz pz).trans ?_
  rw [if_pos rfl, ← hpz]
  simp [sgn]

def spacesNorm : Spaces R F E :=
  { spacesStd R cm T hT pz hpz (fun _ => false) with
    z := Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz
    z_anis := ne_of_eq_of_ne (top_line_norm R T pz hpz) (Nat.cast_ne_zero.2 hT.ne_zero)
    z_orth := fun x => diag_ext_single _ _ (fun _ => false) x _ pz le_rfl }

theorem spacesNorm_z_norm :
    ((spacesNorm R cm T hT pz hpz).X R.m).hT (spacesNorm R cm T hT pz hpz).z (spacesNorm R cm T hT pz hpz).z =
      ((spacesNorm R cm T hT pz hpz).T : E) :=
  top_line_norm R T pz hpz

theorem spacesNorm_hasFrame (j : ℕ) (hj : j < R.m) : HasHyperbolicAuxiliaryFrame (spacesNorm R cm T hT pz hpz) j := by
  have h1 := rankY_eq_N_add R j hj
  have h2 := pY_eq_N_add R j hj
  have hN : R.N j + 2 * ((R.m - 1 - j) / 2) ≤ R.rankY j := by omega
  refine ⟨planeVec _ _ _ hN (1 : E) 1, planeVec _ _ _ hN (1 / 2 : E) (-(1 / 2)),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans (by simp),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans (by simp),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans ?_,
    fun i x => ⟨ext_planeVec _ _ _ hN (cut _ (pY R j)) x _ _ i, ext_planeVec _ _ _ hN (cut _ (pY R j)) x _ _ i⟩,
    fun he => ?_⟩
  · split_ifs
    · rw [star_one]; norm_num
    · rfl
  · obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := R.m_even
    have hl : R.N j + 2 * ((R.m - 1 - j) / 2) < R.rankY j := by omega
    refine ⟨(Pi.single (⟨_, hl⟩ : Fin (R.rankY j)) pz : Fin (R.rankY j) → E), ?_,
      fun x => diag_ext_single _ _ (cut _ (pY R j)) x _ pz (Nat.le_add_right _ _),
      fun i => ⟨single_planeVec _ _ _ hN (cut _ (pY R j)) _ le_rfl _ _ _ i,
        single_planeVec _ _ _ hN (cut _ (pY R j)) _ le_rfl _ _ _ i⟩⟩
    refine (diag_single_single _ (cut _ (pY R j)) _ _ pz pz).trans ?_
    have c : cut (R.rankY j) (pY R j) ⟨_, hl⟩ = true := by
      simp only [cut, decide_eq_true_eq]; omega
    rw [if_pos rfl, c]
    change _ = -(T : E)
    rw [← hpz]
    simp [sgn]

theorem spacesNorm_coord :
    ∃ hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x),
      (∀ j, (spacesNorm R cm T hT pz hpz).X j = posSpace hstar (R.N j)) ∧
      (spacesNorm R cm T hT pz hpz).X' = posSpace hstar R.rankX' ∧
      (∀ j, (spacesNorm R cm T hT pz hpz).Y j =
        stdSpace hstar (R.rankY j) (fun i => decide ((sigYD R j).1 ≤ i.1)) (sigYD R j).1 (sigYD R j).2) ∧
      (∀ j, 1 ≤ j → j ≤ R.m → (spacesNorm R cm T hT pz hpz).W j =
        stdSpace hstar R.r (fun i => decide ((R.sigW j).1 ≤ i.1)) (R.sigW j).1 (R.sigW j).2) ∧
      ∀ j, (spacesNorm R cm T hT pz hpz).V j =
        stdSpace hstar R.nV (fun _ => (spacesNorm R cm T hT pz hpz).Vneg j)
          (if (spacesNorm R cm T hT pz hpz).Vneg j then 0 else R.nV)
          (if (spacesNorm R cm T hT pz hpz).Vneg j then R.nV else 0) := by
  refine ⟨star_isIntegral, fun _ => rfl, rfl, fun j => ?_, fun j h1 h2 => ?_, fun j => ?_⟩
  · exact signSpace_cut_eq _ _ _ _ _ rfl (Nat.sub_le _ _) (sub_pY R j)
  · have h : R.rankY 0 = R.k + R.m - 1 := by simp [Ranks.rankY, Ranks.r]
    refine signSpace_cut_eq _ (R.rankY 0) R.r (R.k + j - 1) (R.m - j) h ?_ ?_ <;> omega
  · exact signSpace_false_eq _ _

theorem spacesNorm_Y_sig (j : ℕ) (τ : E →+* ℂ) : ((spacesNorm R cm T hT pz hpz).Y j).sig τ = sigYD R j :=
  spY_sig R j τ

end Main

end GlobalTheory.Mem.DiagSp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntSmulMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsTer
namespace GlobalTheory.IntSmulMemLattice

open NumberField

theorem exists_int_smul_mem {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) (hL : Submodule.span E (L : Set V) = ⊤) (v : V) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  have hden : ∀ a : E, ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • a) := fun a =>
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr
      (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
  have hv : v ∈ Submodule.span E (L : Set V) := by rw [hL]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨k, hk, hky⟩ := hy
    refine ⟨m * k, mul_ne_zero hm hk, ?_⟩
    have e1 : (m * k) • x = k • (m • x) := by rw [mul_comm, mul_smul]
    have e2 : (m * k) • y = m • (k • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L.add_mem (zsmul_mem hmx k) (zsmul_mem hky m)
  | smul a x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hint⟩ := hden a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩

    let b : RingOfIntegers E := ⟨d • a, hint⟩
    have hb : algebraMap (RingOfIntegers E) E b = (d : E) * a := by
      change d • a = (d : E) * a
      rw [zsmul_eq_mul]
    have e : (d * m) • (a • x) = b • (m • x) := by
      rw [← algebraMap_smul E b (m • x), hb, ← Int.cast_smul_eq_zsmul E (d * m),
        ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    exact L.smul_mem b hmx

end GlobalTheory.IntSmulMemLattice
end

open NumberField Formalism.BasicNotions

namespace GlobalTheory.AutLattice

section
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_int_smul_mem (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤) (v : V) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem ..)

theorem finrank_int_eq (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤) :
    Module.finrank ℤ L = Module.finrank ℚ E * Module.finrank E V := by
  let _i : Module ℚ V := Module.compHom V (algebraMap ℚ E)
  have : IsScalarTower ℚ E V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  rw [Module.finrank_mul_finrank ℚ E V,
    IsLocalization.finrank_eq ℚ (N := V) (nonZeroDivisors ℤ) le_rfl]
  let f : L →ₗ[ℤ] V := L.subtype.toAddMonoidHom.toIntLinearMap
  have : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    { map_units := fun s =>
        (isLocalizedModule_id (nonZeroDivisors ℤ) V ℚ).map_units s
      surj := fun v => by
        obtain ⟨n, hn, h⟩ := exists_int_smul_mem L hL v
        exact ⟨(⟨n • v, h⟩, ⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩), rfl⟩
      exists_of_eq := fun {x y} h => ⟨1, by
        have : x = y := Subtype.ext h
        rw [this]⟩ }
  exact (IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) f le_rfl).symm

end

theorem card_dvd_minkM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound → ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V), L.FG → Submodule.span E (L : Set V) = ⊤ → ∀ G : Subgroup (V ≃ₗ[E] V), Finite G → (∀ g ∈ G, ∀ x ∈ L, g x ∈ L) → Nat.card G ∣ minkM (Module.finrank ℚ E * Module.finrank E V) := by
  intro hM E V _ _ _ _ _ _ _ L hfg hL G hG hGL
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have : HasUniqueDiv V := HasUniqueDiv.of_isTorsionFree E V
  have : Module.Free ℤ L := inferInstance
  rw [← finrank_int_eq L hL]
  let b := Module.finBasis ℤ L
  let r : G →* Module.End ℤ L :=
    { toFun := fun g => AddMonoidHom.toIntLinearMap
        { toFun := fun x => ⟨g.1 x.1, hGL g.1 g.2 x.1 x.2⟩
          map_zero' := Subtype.ext (by simp)
          map_add' := fun x y => Subtype.ext (by simp) }
      map_one' := by ext x; rfl
      map_mul' := fun g h => by ext x; rfl }
  have hr : Function.Injective r := by
    intro g h hgh
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hL
    intro x hx
    exact congrArg Subtype.val (LinearMap.congr_fun hgh ⟨x, hx⟩)
  let φ : G →* GL (Fin (Module.finrank ℤ L)) ℤ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits
  have hφ : Function.Injective φ := by
    intro g h hgh
    apply hr
    apply (LinearMap.toMatrixAlgEquiv b).injective
    exact congrArg Units.val hgh
  have e := MonoidHom.ofInjective hφ
  rw [Nat.card_congr e.toEquiv]
  exact hM _ φ.range (Finite.of_equiv _ e.toEquiv)

end GlobalTheory.AutLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowJoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowJoint
open NumberField IsDedekindDomain

namespace GlobalTheory.TameJoint

theorem exists_pow_joint : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := by
  intro E Ω _ _ _ _ _ M _ φ P A L γ π w hA hker hL hγ hw hγL hπ he σ hσ
  have hL0 : L ≠ 0 := by rintro rfl; exact hL (by simp)
  have hn : 0 < L := Nat.pos_of_ne_zero hL0
  have hLA : ¬ A.valuation (L : Ω) < 1 := by
    intro h
    apply hL
    rw [← hA]
    simpa using h
  set ζ := γ π / π with hζ
  have hζn : ζ ^ L = 1 := by
    rw [hζ, div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
    rw [← he]; exact pow_ne_zero _ hπ
  have hred : ∀ {N : Type} [Monoid N] (x : N), x ^ L = 1 → ∀ a : ℕ, x ^ a = x ^ (a % L) := by
    intro N _ x hx a
    conv_lhs => rw [← Nat.div_add_mod a L, pow_add, pow_mul, hx, one_pow, one_mul]
  have hvζ : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ L = 1 := by rw [← map_pow, hζn, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hl | he' | hg
    · exact absurd hp (pow_lt_one₀ zero_le' hl hL0).ne
    · exact he'
    · exact absurd hp (one_lt_pow₀ hg hL0).ne'

  have hfixζ : ∀ τ ∈ ReciprocityTheory.Gal.Ine (F := E) A, τ ζ = ζ := by
    intro τ hτ
    refine GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA ?_ hζn (hτ.2 ζ hvζ.le)
    rw [← map_pow, hζn, map_one]

  have hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π := by
    intro τ hτ
    have h1 : (τ π / π) ^ L = 1 := by
      rw [div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
      rw [← he]; exact pow_ne_zero _ hπ
    have h2 := GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA h1 (one_pow L) (hτ π hπ)
    rwa [div_eq_one_iff_eq hπ] at h2

  have hopenH : ∀ (H : Subgroup (Formalism.ConjugateSelfDual.G E Ω)), IsOpen (H : Set (Formalism.ConjugateSelfDual.G E Ω)) →
      ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ H, τ * g ∈ U) → IsOpen U := by
    intro H hH U hU
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    rw [← map_mul_left_nhds_one τ]
    exact Filter.mem_map.2 (Filter.mem_of_superset (hH.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)
  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopenH _ hHo _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π
      (IntermediateField.mem_adjoin_simple_self E π)]
  have hfib : ∀ c : M, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | φ τ = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopenH _ hker _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [map_mul, (MonoidHom.mem_ker).1 hg, mul_one]
  let T : Set (Formalism.ConjugateSelfDual.G E Ω) := ⋃ a ∈ Finset.range L, {τ | φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π}
  have hTc : IsClosed T := by
    refine isClosed_biUnion_finset fun a _ => ?_
    exact (hfib _).inter (hloc _)
  let Q : Formalism.ConjugateSelfDual.G E Ω → Prop := fun τ =>
    τ ∈ ReciprocityTheory.Gal.Ine (F := E) A ∧ ∃ a : ℕ, φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π
  have hQ : ∀ τ ∈ Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), Q τ := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, 1, (pow_one _).symm, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ]⟩
      · exact ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hx, 0, by rw [hw x hx, pow_zero],
          by rw [hfixπ x hx, pow_zero, one_mul]⟩
    | one => exact ⟨one_mem _, 0, by rw [map_one, pow_zero], by rw [pow_zero, one_mul]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      obtain ⟨hyI, b, hb, hbπ⟩ := ihy
      refine ⟨mul_mem hxI hyI, a + b, by rw [map_mul, ha, hb, pow_add], ?_⟩
      rw [AlgEquiv.mul_apply, hbπ, map_mul, map_pow, hfixζ x hxI, haπ, pow_add]
      ring
    | inv x _ ihx =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      have hiI : x⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A := inv_mem hxI
      have hex : a * (L - 1) + a = a * L := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      refine ⟨hiI, a * (L - 1), ?_, ?_⟩
      · rw [map_inv, ha]
        symm
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_add, hex, pow_mul', hγL, one_pow]
      · have hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π := by
          rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
        have h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
          have h2 := congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ
          rw [hxx, map_mul, map_pow, hfixζ _ hiI] at h2
          exact h2
        calc (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π = ζ ^ (a * (L - 1) + a) * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
              rw [hex, pow_mul', hζn, one_pow, one_mul]
          _ = ζ ^ (a * (L - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring
          _ = ζ ^ (a * (L - 1)) * π := by rw [← h1]
  have hST : ((Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
        Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T := by
    intro τ hτ
    obtain ⟨-, a, ha, haπ⟩ := hQ τ hτ
    refine Set.mem_biUnion (x := a % L) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_
    exact ⟨by rw [ha, hred _ hγL a], by rw [haπ, hred _ hζn a]⟩
  have hσT : σ ∈ T := closure_minimal hST hTc (hγ.2 hσ)
  simp only [T, Set.mem_iUnion] at hσT
  obtain ⟨a, -, h⟩ := hσT
  exact ⟨a, h⟩

end GlobalTheory.TameJoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowJointStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_of_tameGenAt_of_char_pow_eq_one : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := by
  first | exact @GlobalTheory.TameJoint.exists_pow_joint | exact GlobalTheory.TameJoint.exists_pow_joint | (intros; apply GlobalTheory.TameJoint.exists_pow_joint <;> assumption)
end
end
