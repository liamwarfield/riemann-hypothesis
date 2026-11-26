module

public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamGeoEqFormula
namespace GlobalTheory.LowestKType

open Formalism.IndefR.IndefiniteWeightData Formalism.IndefR.IndefiniteWeightData.WeightData

variable {D : WeightData}

lemma r_eq (h : D.Hyp) : D.r = D.p + D.q := by
  obtain ⟨hk, hj, hjm, -⟩ := h
  unfold WeightData.r WeightData.p WeightData.q
  omega

lemma nV_eq (h : D.Hyp) : D.nV = D.p + D.q + D.t := by
  unfold WeightData.nV
  rw [r_eq h]

lemma nV_cast (h : D.Hyp) : (D.nV : ℚ) = D.p + D.q + D.t := by
  rw [nV_eq h]; push_cast; ring

lemma lam_tail (h : D.Hyp) (c : ℕ) : D.lam (D.p + c) = -D.b (D.j + c) := by
  obtain ⟨hk, hj, hjm, -⟩ := h
  unfold WeightData.lam WeightData.p
  rw [if_neg (by omega)]
  congr 2
  omega

lemma lam_step (h : D.Hyp) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < D.r) :
    (D.lam (i + 1) : ℚ) + 1 ≤ D.lam i := by
  have : D.lam (i + 1) + 1 ≤ D.lam i := h.2.2.2.2.2.1 i h1 h2
  exact_mod_cast this

lemma aMinus_rev (c : ℕ) (hc : c ≤ D.q + 1) :
    D.aMinus (D.q + 1 - c) = ((D.b (D.j + c) : ℚ) - D.e) + (1 - (D.t : ℚ) - 2 * (c : ℚ)) / 2 := by
  have : D.q + 1 - (D.q + 1 - c) = c := by omega
  unfold WeightData.aMinus
  rw [this]

lemma exists_half_r (h : D.Hyp) : ∃ u : ℕ, (D.q : ℚ) = 2 * u + 1 - D.p := by
  obtain ⟨u, hu⟩ := h.2.2.2.1
  rw [r_eq h] at hu
  have : (D.p : ℚ) + D.q = 2 * u + 1 := by exact_mod_cast hu
  exact ⟨u, by linarith⟩

lemma weightData_t_odd (h : D.Hyp) : ∃ w : ℕ, (D.t : ℚ) = 2 * w + 1 := by
  obtain ⟨u, hu⟩ := h.2.2.2.2.1
  exact ⟨u, by exact_mod_cast hu⟩

lemma aPlus_int (h : D.Hyp) (i : ℕ) : ∃ z : ℤ, D.aPlus i = z := by
  obtain ⟨u, hu⟩ := exists_half_r h
  obtain ⟨w, hw⟩ := weightData_t_odd h
  refine ⟨D.lam i + D.e - w - 1 + i - D.p, ?_⟩
  unfold WeightData.aPlus
  rw [nV_cast h, hu, hw]
  push_cast
  ring

lemma aMinus_int (h : D.Hyp) (s : ℕ) : ∃ z : ℤ, D.aMinus s = z := by
  obtain ⟨w, hw⟩ := weightData_t_odd h
  refine ⟨D.b (D.j + (D.q + 1 - s)) - D.e - w - ((D.q + 1 - s : ℕ) : ℤ), ?_⟩
  unfold WeightData.aMinus
  generalize D.q + 1 - s = c
  rw [hw]
  push_cast
  ring

lemma theta_param (h : D.Hyp) (i : ℕ) (h2 : i ≤ D.nV) :
    D.thetaWt i + ((D.p : ℚ) - D.q) / 2 - D.e + D.rhoNV i = D.uSideTarget i := by
  rw [nV_eq h] at h2
  unfold WeightData.thetaWt WeightData.rhoNV WeightData.uSideTarget
  by_cases hi : i ≤ D.p
  · simp only [if_pos hi]
    unfold WeightData.aPlus
    ring
  · by_cases hi' : i ≤ D.p + D.t
    · simp only [if_neg hi, if_pos hi']
      rw [nV_cast h]
      ring
    · obtain ⟨c, rfl⟩ : ∃ c, i = D.p + D.t + c := ⟨i - D.p - D.t, by omega⟩
      have e1 : D.p + D.t + c - D.p - D.t = c := by omega
      simp only [if_neg hi, if_neg hi', e1]
      rw [aMinus_rev c (by omega), nV_cast h]
      push_cast
      ring

lemma lamPrime_param (h : D.Hyp) (i : ℕ) (h2 : i ≤ D.nV) :
    D.lamPrime i + D.rhoNV i = D.uSideTarget i - 1 / 2 := by
  rw [← theta_param h i h2]
  unfold WeightData.lamPrime WeightData.dTau
  ring

lemma dTau_int (h : D.Hyp) : ∃ z : ℤ, D.dTau = z := by
  obtain ⟨u, hu⟩ := exists_half_r h
  refine ⟨D.p - u - 1 - D.e, ?_⟩
  unfold WeightData.dTau
  rw [hu]; push_cast; ring

lemma target_step (h : D.Hyp) (hg : D.GapHyp) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < D.nV) :
    D.uSideTarget (i + 1) + 1 ≤ D.uSideTarget i := by
  have hr := r_eq h
  rw [nV_eq h] at h2
  have ht : 1 ≤ D.t := h.2.2.2.2.1.pos
  unfold WeightData.uSideTarget
  rcases lt_trichotomy i D.p with hi | hi | hi
  · have a1 : i ≤ D.p := by omega
    have a2 : i + 1 ≤ D.p := by omega
    simp only [if_pos a1, if_pos a2]
    exact lam_step h i h1 (by omega)
  · subst hi
    have a2 : ¬ D.p + 1 ≤ D.p := by omega
    have a3 : D.p + 1 ≤ D.p + D.t := by omega
    have h4 := lam_tail h 0
    simp only [add_zero] at h4
    simp only [if_pos (le_refl D.p), if_neg a2, if_pos a3]
    rw [h4]
    have := hg.1
    push_cast
    linarith
  · have a1 : ¬ i ≤ D.p := by omega
    have a2 : ¬ i + 1 ≤ D.p := by omega
    simp only [if_neg a1, if_neg a2]
    rcases lt_trichotomy i (D.p + D.t) with hi' | hi' | hi'
    · have a3 : i ≤ D.p + D.t := by omega
      have a4 : i + 1 ≤ D.p + D.t := by omega
      simp only [if_pos a3, if_pos a4]
      push_cast
      linarith
    · subst hi'
      have a4 : ¬ D.p + D.t + 1 ≤ D.p + D.t := by omega
      have e1 : D.p + D.t + 1 - D.p - D.t = 1 := by omega
      have hq : D.q = D.m - D.j := rfl
      have := hg.2 (by omega)
      simp only [if_pos (le_refl (D.p + D.t)), if_neg a4, e1]
      push_cast
      linarith
    · have a3 : ¬ i ≤ D.p + D.t := by omega
      have a4 : ¬ i + 1 ≤ D.p + D.t := by omega
      simp only [if_neg a3, if_neg a4]
      obtain ⟨c, rfl⟩ : ∃ c, i = D.p + D.t + c := ⟨i - D.p - D.t, by omega⟩
      have e1 : D.p + D.t + c - D.p - D.t = c := by omega
      have e2 : D.p + D.t + c + 1 - D.p - D.t = c + 1 := by omega
      have h3 := lam_step h (D.p + c) (by omega) (by omega)
      rw [add_assoc, lam_tail h, lam_tail h] at h3
      rw [e1, e2]
      push_cast at h3
      linarith

theorem thetaSide : ThetaSideStatement := by
  intro D h hg
  refine ⟨fun i _ h2 => theta_param h i h2, fun i _ h2 => lamPrime_param h i h2, dTau_int h,
    ?_, ?_, ?_⟩
  · intro i _ _
    obtain ⟨d, hd⟩ := dTau_int h
    unfold WeightData.lamPrime WeightData.thetaWt
    rw [hd]
    split_ifs
    · obtain ⟨z, hz⟩ := aPlus_int h i
      exact ⟨z + d, by rw [hz]; push_cast; ring⟩
    · exact ⟨d, by ring⟩
    · obtain ⟨z, hz⟩ := aMinus_int h (D.q + 1 - (i - D.p - D.t))
      exact ⟨-z + d, by rw [hz]; push_cast; ring⟩
  · intro i h1 h2
    have h3 := target_step h hg i h1 h2
    have h4 := lamPrime_param h i h2.le
    have h5 := lamPrime_param h (i + 1) h2
    unfold WeightData.rhoNV at h4 h5
    push_cast at h5
    linarith
  · intro i h1 h2
    have h3 := target_step h hg i h1 h2
    rw [lamPrime_param h i h2.le, lamPrime_param h (i + 1) h2]
    linarith

end GlobalTheory.LowestKType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPrimeLocalizationDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPrimeLocalizationDvr
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_under_eq_of_mem_associatedPrimes_of_surjective {A A' M : Type*} [CommRing A]
    [CommRing A'] [Algebra A A'] [AddCommGroup M] [Module A M] [Module A' M]
    [IsScalarTower A A' M] (hs : Function.Surjective (algebraMap A A')) {q : Ideal A}
    (hq : q ∈ associatedPrimes A M) : ∃ q' ∈ associatedPrimes A' M, q'.under A = q := by
  obtain ⟨hp, v, hv⟩ := hq
  set q' : Ideal A' := ((⊥ : Submodule A' M).colon {v}).radical with hq'
  have hunder : q'.under A = q := by
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, hv]
    simp only [hq', Ideal.mem_radical_iff, Submodule.mem_colon_singleton, Submodule.mem_bot,
      ← map_pow, algebraMap_smul]
  have hmap : q.map (algebraMap A A') = q' := by
    rw [← hunder]
    exact Ideal.map_comap_of_surjective _ hs q'
  have hker : RingHom.ker (algebraMap A A') ≤ q := fun a ha ↦ by
    rw [hv]
    refine Ideal.le_radical ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← algebraMap_smul A',
      RingHom.mem_ker.1 ha, zero_smul]
  have hprime : q'.IsPrime := hmap ▸ Ideal.map_isPrime_of_surjective hs hker
  exact ⟨q', ⟨hprime, v, rfl⟩, hunder⟩

theorem exists_isDomain_isDiscreteValuationRing_of_maximalIdeal_eq_span {S : Type*} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] {t : S} (ht : maximalIdeal S = Ideal.span {t})
    (hreg : IsSMulRegular S t) : ∃ _ : IsDomain S, IsDiscreteValuationRing S := by
  have hfac : ∀ y : S, y ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ y = t ^ n * u := by
    intro y hy
    have hinf : (⨅ i : ℕ, maximalIdeal S ^ i) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'
    have hex : ∃ n : ℕ, y ∉ maximalIdeal S ^ n := by
      by_contra! h
      exact hy (by simpa [hinf] using (Submodule.mem_iInf _).2 h)
    classical
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero fun h0 ↦ ?_
      have := Nat.find_spec hex
      rw [h0] at this
      simp at this
    have h1 : y ∈ maximalIdeal S ^ k := by
      have := Nat.find_min hex (m := k) (by omega)
      simpa using this
    have h2 : y ∉ maximalIdeal S ^ (k + 1) := hk ▸ Nat.find_spec hex
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    obtain ⟨u, rfl⟩ := h1
    refine ⟨k, u, ?_, rfl⟩
    by_contra hu
    apply h2
    have hum : u ∈ maximalIdeal S := (mem_maximalIdeal u).2 hu
    rw [ht, Ideal.mem_span_singleton] at hum
    obtain ⟨c, rfl⟩ := hum
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨c, by ring⟩
  have hnzd : NoZeroDivisors S := by
    refine ⟨fun {a b} hab ↦ ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨m, u, hu, rfl⟩ := hfac a hne.1
    obtain ⟨n, v, hv, rfl⟩ := hfac b hne.2
    have h0 : t ^ (m + n) • (u * v) = 0 := by
      rw [smul_eq_mul, pow_add]
      linear_combination hab
    have h3 : u * v = 0 := (hreg.pow (m + n)).right_eq_zero_of_smul h0
    exact (hu.mul hv).ne_zero h3
  have hdom : IsDomain S := NoZeroDivisors.to_isDomain S
  refine ⟨hdom, ?_⟩
  have ht0 : t ≠ 0 := fun h ↦ by
    have : IsSMulRegular S (0 : S) := h ▸ hreg
    exact one_ne_zero (this.right_eq_zero_of_smul (zero_smul S (1 : S)))
  have hf : ¬ IsField S := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ht]
    simpa using ht0
  refine ((IsDiscreteValuationRing.TFAE S hf).out 5 1).mp ?_
  exact ⟨t, ht⟩

theorem exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [CommRing R] [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (x : A), x ≠ 0 →
      (∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R))) →
      ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {algebraMap A R x}) →
        ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) := by
  intro A R _ _ _ _ _ _ _ _ x hx hred P _ hP
  set I : Ideal A := Ideal.span {x} with hI
  have hIR : Ideal.span {algebraMap A R x} = I.map (algebraMap A R) := by
    rw [hI, Ideal.map_span, Set.image_singleton]
  rw [hIR] at hP
  set q : Ideal A := P.under A with hqdef
  have hqp : q.IsPrime := Ideal.IsPrime.under A P

  have hxq : x ∈ q := by
    have h1 := IsAssociatedPrime.annihilator_le hP
    rw [Submodule.annihilator_top, Ideal.annihilator_quotient] at h1
    exact h1 (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self x))

  have hqA : q ∈ associatedPrimes A (A ⧸ I) := by
    have h0 : q ∈ associatedPrimes A (R ⧸ I.map (algebraMap A R)) :=
      under_mem_associatedPrimes (A := A) hP
    let e : (R ⧸ I.map (algebraMap A R)) ≃ₗ[A] (A ⧸ I) ⊗[A] R :=
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R I).toLinearEquiv.restrictScalars A) ≪≫ₗ
        TensorProduct.comm A R (A ⧸ I)
    rw [LinearEquiv.AssociatedPrimes.eq e] at h0
    obtain ⟨q', hq', hu⟩ := exists_under_eq_of_mem_associatedPrimes_of_surjective (A' := A ⧸ I)
      Ideal.Quotient.mk_surjective h0
    have h2 : q' ∈ associatedPrimes (A ⧸ I) (A ⧸ I) := associatedPrimes_subset_of_flat hq'
    rw [← hu]
    exact under_mem_associatedPrimes (A := A) h2
  have hheight : q.height = 1 := height_eq_one_of_mem_associatedPrimes hx hqA

  have hPq : P ∈ associatedPrimes R (R ⧸ q.map (algebraMap A R)) := by
    rw [LinearEquiv.AssociatedPrimes.eq
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R I).toLinearEquiv] at hP
    rw [LinearEquiv.AssociatedPrimes.eq
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R q).toLinearEquiv]
    exact mem_associatedPrimes_tensor_quotient_under (A := A) hP

  obtain ⟨z, hzP, hz⟩ : ∃ z ∉ P, ∀ p ∈ P, p * z ∈ q.map (algebraMap A R) := by
    obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.mp hPq
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hmem : ∀ p, p ∈ P ↔ p * z ∈ q.map (algebraMap A R) := fun p ↦ by
      rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨z, fun hzP ↦ ?_, fun p hp ↦ (hmem p).1 hp⟩
    have := hred q hqp hxq
    have h2 : Ideal.Quotient.mk (q.map (algebraMap A R)) z ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_two]
      exact (hmem z).1 hzP
    have h3 : z ∈ q.map (algebraMap A R) :=
      Ideal.Quotient.eq_zero_iff_mem.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
    exact Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one P).2 ((hmem 1).2 (by simpa using h3)))

  obtain ⟨t, htq, ht⟩ : ∃ t ∈ q, ∀ b ∈ q, ∃ v ∉ q, ∃ c, v * b = t * c := by
    let B := Localization.AtPrime q
    have hdvr : IsDiscreteValuationRing B := isDiscreteValuationRing_of_height_eq_one q hheight B
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl ϖ
    have hmax : maximalIdeal B = Ideal.span {IsLocalization.mk' B a s} := hϖ.maximalIdeal_eq
    have h1 : IsLocalization.mk' B a s * algebraMap A B s = algebraMap A B a :=
      IsLocalization.mk'_spec B a s
    have haq : a ∈ q := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff B q a, ← h1, hmax]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    refine ⟨a, haq, fun b hb ↦ ?_⟩
    have hbB := (IsLocalization.AtPrime.to_map_mem_maximal_iff B q b).2 hb
    rw [hmax, Ideal.mem_span_singleton] at hbB
    obtain ⟨d, hd⟩ := hbB
    obtain ⟨c, u, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl d
    have h2 : IsLocalization.mk' B c u * algebraMap A B u = algebraMap A B c :=
      IsLocalization.mk'_spec B c u
    refine ⟨s * u, q.primeCompl.mul_mem s.2 u.2, c, ?_⟩
    apply IsLocalization.injective B q.primeCompl_le_nonZeroDivisors
    simp only [map_mul]
    linear_combination (algebraMap A B s * algebraMap A B u) * hd +
      (IsLocalization.mk' B c u * algebraMap A B u) * h1 + algebraMap A B a * h2

  let S := Localization.AtPrime P
  have hflatRS : Module.Flat R S := IsLocalization.flat S P.primeCompl
  have hflatAS : Module.Flat A S := Module.Flat.trans A R S
  have hnoeth : IsNoetherianRing S := IsLocalization.isNoetherianRing P.primeCompl S inferInstance
  have ht0 : t ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv, c, hvc⟩ := ht x hxq
    rw [zero_mul] at hvc
    rcases mul_eq_zero.1 hvc with h | h
    · exact hv (h ▸ q.zero_mem)
    · exact hx h
  have hreg : IsSMulRegular S (algebraMap A S t) := (IsSMulRegular.of_ne_zero ht0).of_flat
  have hunitS : ∀ r ∉ P, IsUnit (algebraMap R S r) := fun r hr ↦
    IsLocalization.map_units S (⟨r, hr⟩ : P.primeCompl)
  have hqS : ∀ b ∈ q, algebraMap A S b ∈ Ideal.span {algebraMap A S t} := fun b hb ↦ by
    obtain ⟨v, hv, c, hvc⟩ := ht b hb
    have hu : IsUnit (algebraMap A S v) := by
      rw [IsScalarTower.algebraMap_apply A R S]
      exact hunitS _ hv
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul, hvc, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hqRS : q.map (algebraMap A R) ≤ (Ideal.span {algebraMap A S t}).comap (algebraMap R S) :=
    Ideal.map_le_iff_le_comap.2 fun b hb ↦ by
      rw [Ideal.mem_comap, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hqS b hb
  have hmaxS : maximalIdeal S = Ideal.span {algebraMap A S t} := by
    refine le_antisymm ?_ ?_
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro p hp
      have h := hqRS (hz p hp)
      rw [Ideal.mem_comap, map_mul] at h
      exact (Ideal.mul_unit_mem_iff_mem _ (hunitS z hzP)).1 h
    · rw [Ideal.span_singleton_le_iff_mem, IsScalarTower.algebraMap_apply A R S,
        IsLocalization.AtPrime.to_map_mem_maximal_iff S P]
      exact htq
  exact exists_isDomain_isDiscreteValuationRing_of_maximalIdeal_eq_span hmaxS hreg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPrimeLocalizationDvrStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.associated_prime_localization_dvr : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing R] [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (x : A), x ≠ 0 → (∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R))) → ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {algebraMap A R x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) := by
  first | exact @GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient | exact GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient | (intros; apply GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeomRegFibAdicCompletionOfEssFiniteTypeInt
open IsLocalRing TensorProduct

namespace GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems

theorem exists_loc (A : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra.FiniteType ℤ A₀) (p : Ideal A₀) (_ : p.IsPrime),
      Nonempty (Localization.AtPrime p ≃+* A) := by
  refine ⟨Algebra.EssFiniteType.subalgebra ℤ A, inferInstance, inferInstance,
    (maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A), inferInstance, ?_⟩
  have hsub : Algebra.EssFiniteType.submonoid ℤ A =
      ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)).primeCompl := by
    ext x
    simp [Algebra.EssFiniteType.submonoid, Ideal.primeCompl, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, IsUnit.mem_submonoid_iff]
  have hloc := Algebra.EssFiniteType.isLocalization ℤ A
  rw [hsub] at hloc
  haveI : IsLocalization.AtPrime A ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)) := hloc
  exact ⟨(IsLocalization.algEquiv ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)).primeCompl
    (Localization.AtPrime _) A).toRingEquiv⟩

theorem evalₐ_factorPow {R : Type} [CommRing R] (I : Ideal R) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h a =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, AdicCompletion.Ideal.mk_eq_mk I hle]

theorem complMap_compat {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) : ∀ {m n : ℕ} (hle : m ≤ n),
    (Ideal.Quotient.factorPow J hle).comp ((fun n => (Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) n) =
      (fun n => (Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) m := by
      intro m n hle
      ext x
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
      have h1 := evalₐ_factorPow I hle x
      simp only [RingHom.comp_apply, RingHom.coe_coe] at h1 ⊢
      rw [← h1, ← hy, Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factorPow,
        Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]

noncomputable def complMap {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
    (complMap_compat e I J h)

theorem evalₐ_complMap {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (complMap e I J h x) =
      Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)
        (AdicCompletion.evalₐ I n x) := by
  unfold complMap
  exact AdicCompletion.evalₐ_liftRingHom J _ (complMap_compat e I J h) n x

theorem complMap_algebraMap {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) (r : R) :
    complMap e I J h (algebraMap R _ r) = algebraMap S _ (e r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap]
  simp [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]

theorem complMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (e : R →+* S)
    (e' : S →+* T) (I : Ideal R) (J : Ideal S) (K : Ideal T) (h : I.map e ≤ J) (h' : J.map e' ≤ K)
    (x : AdicCompletion I R) :
    complMap e' J K h' (complMap e I J h x) = complMap (e'.comp e) I K
      (by rw [← Ideal.map_map]; exact (Ideal.map_mono h).trans h') x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap, evalₐ_complMap, evalₐ_complMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hy]
  simp [Ideal.quotientMap_mk]

theorem complMap_id {R : Type} [CommRing R] (I : Ideal R) (h : I.map (RingHom.id R) ≤ I)
    (x : AdicCompletion I R) : complMap (RingHom.id R) I I h x = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hy]
  simp [Ideal.quotientMap_mk]

theorem compl_equiv (R S : Type) [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e = J) : ∃ f : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ r : R, f (algebraMap R _ r) = algebraMap S _ (e r) := by
  have h1 : I.map (e : R →+* S) ≤ J := h.le
  have h2 : J.map (e.symm : S →+* R) ≤ I := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [← h, Ideal.mem_map_of_equiv] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  refine ⟨RingEquiv.ofRingHom (complMap (e : R →+* S) I J h1) (complMap (e.symm : S →+* R) J I h2)
    ?_ ?_, complMap_algebraMap _ I J h1⟩
  · refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, complMap_comp]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.comp_symm, RingHom.id_apply]
    exact complMap_id J _ x
  · refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, complMap_comp]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, RingHom.id_apply]
    exact complMap_id I _ x

theorem fg_top_transfer {F F' K : Type} [Field F] [Field F'] [Field K] [Algebra F K] [Algebra F' K]
    (φ : F ≃+* F') (hφ : ∀ x, algebraMap F K x = algebraMap F' K (φ x))
    (h : (⊤ : IntermediateField F' K).FG) : (⊤ : IntermediateField F K).FG := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, ?_⟩
  apply IntermediateField.toSubfield_injective
  have hr : Set.range (algebraMap F K) = Set.range (algebraMap F' K) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨φ x, (hφ x).symm⟩
    · rintro ⟨x, rfl⟩; exact ⟨φ.symm x, by rw [hφ, RingEquiv.apply_symm_apply]⟩
  have h2 := congrArg IntermediateField.toSubfield hS
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h2 ⊢
  rw [hr]
  exact h2

noncomputable def tensorHom {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A →+* A') (f : B →+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) : B ⊗[A] K →+* B' ⊗[A'] K :=
  letI : Algebra A (B' ⊗[A'] K) := ((algebraMap A' (B' ⊗[A'] K)).comp e).toAlgebra
  (Algebra.TensorProduct.lift (S := A)
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[A'] K).comp f
      commutes' := fun a => by
        change Algebra.TensorProduct.includeLeftRingHom (f (algebraMap A B a)) =
          algebraMap A' (B' ⊗[A'] K) (e a)
        rw [hf]
        exact (Algebra.TensorProduct.includeLeft (S := A')).commutes (e a) }
    { toRingHom := (Algebra.TensorProduct.includeRight : K →ₐ[A'] B' ⊗[A'] K).toRingHom
      commutes' := fun a => by
        change (Algebra.TensorProduct.includeRight : K →ₐ[A'] B' ⊗[A'] K) (algebraMap A K a) =
          algebraMap A' (B' ⊗[A'] K) (e a)
        rw [hK]
        exact Algebra.TensorProduct.includeRight.commutes (e a) }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem tensorHom_tmul {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A →+* A') (f : B →+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) (b : B) (k : K) :
    tensorHom e f hf hK (b ⊗ₜ k) = f b ⊗ₜ k := by
  simp [tensorHom, Algebra.TensorProduct.lift_tmul]

theorem tensor_equiv {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A ≃+* A') (f : B ≃+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) : Nonempty (B ⊗[A] K ≃+* B' ⊗[A'] K) := by
  have hf' : ∀ a, f.symm (algebraMap A' B' a) = algebraMap A B (e.symm a) := fun a => by
    apply f.injective
    rw [RingEquiv.apply_symm_apply, hf, RingEquiv.apply_symm_apply]
  have hK' : ∀ a, algebraMap A' K a = algebraMap A K (e.symm a) := fun a => by
    rw [hK, RingEquiv.apply_symm_apply]
  refine ⟨RingEquiv.ofRingHom (tensorHom (e : A →+* A') (f : B →+* B') hf hK)
    (tensorHom (e.symm : A' →+* A) (f.symm : B' →+* B) hf' hK') ?_ ?_⟩
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [RingHom.comp_apply]
      erw [tensorHom_tmul, tensorHom_tmul]
      simp
    | add x y hx hy => simp only [RingHom.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [RingHom.comp_apply]
      erw [tensorHom_tmul, tensorHom_tmul]
      simp
    | add x y hx hy => simp only [RingHom.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]

theorem regular_transfer {T T' : Type} [CommRing T] [CommRing T'] (F : T ≃+* T')
    (hN : IsNoetherianRing T)
    (hR : ∀ (Q : Ideal T) [Q.IsPrime], IsRegularLocalRing (Localization.AtPrime Q)) :
    IsNoetherianRing T' ∧
      ∀ (Q' : Ideal T') [Q'.IsPrime], IsRegularLocalRing (Localization.AtPrime Q') := by
  refine ⟨isNoetherianRing_of_ringEquiv T F, fun Q' _ => ?_⟩
  haveI := hR (Q'.comap F)
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (Q'.comap F)) (Localization.AtPrime Q') F (F.map_primeCompl_comap_eq Q'))

theorem residueFieldRingEquiv_algebraMap {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (P' : Ideal A') [P'.IsPrime] (a : A) :
    Ideal.residueFieldRingEquiv (P'.comap (e : A →+* A')) P' e rfl
      (algebraMap A (P'.comap (e : A →+* A')).ResidueField a) =
      algebraMap A' P'.ResidueField (e a) :=
  Ideal.ResidueField.map_algebraMap _ P' (e : A →+* A') rfl a

theorem transport (A A' B B' : Type) [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B'] (e : A ≃+* A') (f : B ≃+* B')
    (hf : ∀ a : A, f (algebraMap A B a) = algebraMap A' B' (e a)) :
    GeomRegFib A B → GeomRegFib A' B' := by
  intro h P' _ K _ _ _ _ hfg
  let P : Ideal A := P'.comap (e : A →+* A')
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  let φ : P.ResidueField ≃+* P'.ResidueField := Ideal.residueFieldRingEquiv P P' e rfl
  letI : Algebra A K := ((algebraMap A' K).comp (e : A →+* A')).toAlgebra
  letI : Algebra P.ResidueField K := ((algebraMap P'.ResidueField K).comp (φ : _ →+* _)).toAlgebra
  haveI : IsScalarTower A P.ResidueField K := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A' K (e a) = algebraMap P'.ResidueField K (φ (algebraMap A P.ResidueField a))
    rw [residueFieldRingEquiv_algebraMap e P' a, ← IsScalarTower.algebraMap_apply]
  have hfg' : (⊤ : IntermediateField P.ResidueField K).FG := fg_top_transfer φ (fun _ => rfl) hfg
  obtain ⟨hN, hR⟩ := h P K hfg'
  obtain ⟨F⟩ := tensor_equiv (K := K) e f hf (fun _ => rfl)
  exact regular_transfer F hN hR

theorem geomRegFib_adicCompletion_of_essFiniteType_int :
    (∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], ReciprocityTheory.AnForm.R.FinalTheorems.QERing A) →
      ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A],
        ReciprocityTheory.AnForm.R.FinalTheorems.GeomRegFib A (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  intro hQE A _ _ _
  obtain ⟨A₀, _, _, p, _, ⟨e⟩⟩ := exists_loc A
  have h2 := ((hQE A₀).2.1 p).2
  obtain ⟨f, hf⟩ := compl_equiv _ _ e (maximalIdeal (Localization.AtPrime p)) (maximalIdeal A)
    (map_ringEquiv_maximalIdeal e)
  exact transport _ _ _ _ e f hf h2

end GlobalTheory.GeomRegFibTransport
end
