module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsFlatNormalStageAtOrigin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginNoeth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorDescentFlatNormalDomains
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOnePrimeAssociate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyAssociatedAtHeightOnePrime
open IsLocalRing

namespace GlobalTheory

theorem exists_notMem_dvd_mul_of_algebraMap_dvd {B : Type} [CommRing B] (Q : Ideal B) [Q.IsPrime]
    {a b : B}
    (h : algebraMap B (Localization.AtPrime Q) a ∣ algebraMap B (Localization.AtPrime Q) b) :
    ∃ t ∉ Q, a ∣ t * b := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨⟨z, s⟩, hs⟩ := IsLocalization.surj Q.primeCompl y
  have e : algebraMap B (Localization.AtPrime Q) (b * s) =
      algebraMap B (Localization.AtPrime Q) (a * z) := by
    rw [map_mul, map_mul, hy, mul_assoc, hs]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists Q.primeCompl _).mp e
  refine ⟨c * s, Q.primeCompl.mul_mem c.2 s.2, c * z, ?_⟩
  linear_combination hc

theorem exists_locally_associated_algebraMap_of_height_eq_one (A' B' : Type) [CommRing A']
    [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A' B']
    (𝔭 : Ideal A') (hQ : (𝔭.map (algebraMap A' B')).IsPrime)
    (h1 : (𝔭.map (algebraMap A' B')).height = 1) (c : B') (hc : c ≠ 0) :
    ∃ j : A', (∃ t ∉ 𝔭.map (algebraMap A' B'), c ∣ t * algebraMap A' B' j) ∧
      (∃ t ∉ 𝔭.map (algebraMap A' B'), algebraMap A' B' j ∣ t * c) := by
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime (𝔭.map (algebraMap A' B'))) :=
    isDiscreteValuationRing_of_height_eq_one _ h1 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (𝔭.map (algebraMap A' B')))
  have hm : maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  obtain ⟨p, hp𝔭, hp⟩ : ∃ p ∈ 𝔭, ¬ ϖ ^ 2 ∣
      algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) (algebraMap A' B' p) := by
    by_contra! H
    have hle : maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) ≤
        Ideal.span {ϖ ^ 2} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact H q hq
    have hmem : ϖ ∈ Ideal.span {ϖ ^ 2} := hle (hm ▸ Ideal.mem_span_singleton_self ϖ)
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨r, ?_⟩
    apply mul_left_cancel₀ hϖ.ne_zero
    rw [mul_one]
    linear_combination -hr
  have hxm : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (algebraMap A' B' p) ∈ maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hp𝔭)
  have hx0 : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (algebraMap A' B' p) ≠ 0 := fun h => hp (h ▸ dvd_zero _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hn : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at hu
      exact (mem_maximalIdeal _).mp hxm (hu ▸ u.isUnit)
    · rfl
    · exfalso
      apply hp
      rw [hu]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  subst hn
  have hc0 : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) c ≠ 0 := by
    intro h
    apply hc
    apply IsLocalization.injective (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (𝔭.map (algebraMap A' B')).primeCompl_le_nonZeroDivisors
    rw [h, map_zero]
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  have hass : Associated (algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) c)
      (algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
        (algebraMap A' B' (p ^ m))) := by
    rw [map_pow, map_pow, hu, hv, pow_one, mul_pow]
    exact (associated_unit_mul_left _ _ v.isUnit).trans
      (associated_unit_mul_left _ _ (u.isUnit.pow m)).symm
  exact ⟨p ^ m, exists_notMem_dvd_mul_of_algebraMap_dvd _ hass.dvd,
    exists_notMem_dvd_mul_of_algebraMap_dvd _ hass.symm.dvd⟩

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_prime_associate : ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [IsDomain B'] [IsNoetherianRing B']
    [IsIntegrallyClosed B'] [Algebra A' B'] (𝔭 : Ideal A'), (𝔭.map (algebraMap A' B')).IsPrime →
    (𝔭.map (algebraMap A' B')).height = 1 → ∀ c : B', c ≠ 0 →
    ∃ j : A', (∃ t ∉ 𝔭.map (algebraMap A' B'), c ∣ t * algebraMap A' B' j) ∧
      (∃ t ∉ 𝔭.map (algebraMap A' B'), algebraMap A' B' j ∣ t * c) := by
  first | (exact @GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one) | (exact GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one) | (intros; apply GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSubmonoidDvdMulOfForallHeightEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSubmonoidDvdMulOfForallHeightEqOne
open IsLocalRing

namespace GlobalTheory

theorem exists_mem_submonoid_dvd_mul_of_forall_height_eq_one :
    ∀ (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (S : Submonoid B), (0 : B) ∉ S → ∀ x y : B, y ≠ 0 →
    (∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → y ∈ Q → Disjoint (S : Set B) (Q : Set B) →
      ∃ t ∉ Q, y ∣ t * x) → ∃ u ∈ S, y ∣ u * x := by
  intro B _ _ _ _ S _ x y hy h
  by_contra! hS
  set M := B ⧸ Ideal.span {y}
  set N : Submodule B M := B ∙ (Ideal.Quotient.mk (Ideal.span {y}) x)
  have hmem : ∀ r : B, r ∈ Module.annihilator B N ↔ y ∣ r * x := by
    intro r
    change r ∈ Submodule.annihilator N ↔ _
    rw [Submodule.mem_annihilator_span_singleton, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  set I := Module.annihilator B N
  have hdisj : Disjoint (S : Set B) (I : Set B) := by
    rw [Set.disjoint_left]
    intro u hu huI
    exact hS u hu ((hmem u).mp huI)
  obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint I S hdisj.symm
  obtain ⟨P', hP'min, hP'P⟩ := Ideal.exists_minimalPrimes_le hIP
  have hass : P' ∈ associatedPrimes B N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B N hP'min
  have hass' : P' ∈ associatedPrimes B M :=
    associatedPrimes.subset_of_injective Subtype.val_injective (f := N.subtype) hass
  obtain ⟨hpr, h1, hyP⟩ := (mem_associatedPrimes_iff_height_eq_one hy).mp hass'
  obtain ⟨t, htQ, ht⟩ := h P' hpr h1 hyP (hPS.symm.mono_right hP'P)
  exact htQ (hP'min.1.2 ((hmem t).mpr ht))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSubmonoidDvdMulOfForallHeightEqOneStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one : ∀ (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (S : Submonoid B), (0 : B) ∉ S → ∀ x y : B, y ≠ 0 →
    (∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → y ∈ Q → Disjoint (S : Set B) (Q : Set B) →
      ∃ t ∉ Q, y ∣ t * x) → ∃ u ∈ S, y ∣ u * x := by
  first | (exact @GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one) | (exact GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one) | (intros; apply GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorDescentFlatNormalDomains
open IsLocalRing Polynomial

namespace GlobalTheory.DivDescent

theorem colonStep : ∀ (A' B' : Type) [CommRing A'] [IsNoetherianRing A'] [CommRing B'] [Algebra A' B']
    [Module.Flat A' B'] (b c : B') (s : A'), b * c = algebraMap A' B' s →
    (∀ x : A', (∀ j : A', c ∣ algebraMap A' B' j → ∃ a : A', x * j = s * a) →
      b ∣ algebraMap A' B' x) →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  intro A' B' _ _ _ _ _ b c s hbc h
  have hφ : (algebraMap A' B').Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hle : (Ideal.span {s}).colon (((Ideal.span {c}).comap (algebraMap A' B') : Ideal A') : Set A') ≤
      (Ideal.span {b}).comap (algebraMap A' B') := by
    intro x hx
    rw [Submodule.mem_colon] at hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    apply h x
    intro j hj
    have := hx j (by rw [SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_span_singleton]; exact hj)
    rw [smul_eq_mul, Ideal.mem_span_singleton] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, by rw [ha]⟩
  refine Ideal.map_mono hle ?_
  rw [GlobalTheory.ideal_map_colon_eq_of_flat (algebraMap A' B') hφ, Submodule.mem_colon]
  intro y hy
  have hy' : y ∈ Ideal.span {c} := Ideal.map_comap_le hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.1 hy'
  rw [Ideal.map_span, Set.image_singleton, smul_eq_mul, Ideal.mem_span_singleton]
  exact ⟨z, by rw [← hbc, mul_assoc]⟩

theorem primeDescent : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [CommRing B']
    [IsDomain B'] [IsNoetherianRing B'] [Algebra A' B'] [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ Q : Ideal B', Q.IsPrime → Q.height = 1 → algebraMap A' B' s ∈ Q →
    (Q.comap (algebraMap A' B')).height = 1 ∧
      (Q.comap (algebraMap A' B')).map (algebraMap A' B') = Q := by
  intro A' B' _ _ _ _ _ _ _ _ s hs hpr Q hQ hQ1 hsQ
  haveI : Algebra.HasGoingDown A' B' := Algebra.HasGoingDown.of_flat
  haveI hPp : (Q.comap (algebraMap A' B')).IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver (Q.comap (algebraMap A' B')) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Q.comap (algebraMap A' B')) Q
  have hle1 : (Q.comap (algebraMap A' B')).height ≤ 1 := by rw [← hQ1, h]; exact le_self_add
  have h1 : (Q.comap (algebraMap A' B')).height = 1 := by
    refine le_antisymm hle1 ?_
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hb
    have : s ∈ Q.comap (algebraMap A' B') := hsQ
    rw [hb, Ideal.mem_bot] at this
    exact hs this
  refine ⟨h1, ?_⟩
  haveI hP : ((Q.comap (algebraMap A' B')).map (algebraMap A' B')).IsPrime := hpr _ hPp h1 hsQ
  have hle : (Q.comap (algebraMap A' B')).map (algebraMap A' B') ≤ Q := Ideal.map_comap_le
  by_contra hne
  have hlt := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hQ1] at hlt
  have h0 : ((Q.comap (algebraMap A' B')).map (algebraMap A' B')).height = 0 :=
    ENat.lt_one_iff_eq_zero.mp hlt
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  have hm : algebraMap A' B' s ∈ (Q.comap (algebraMap A' B')).map (algebraMap A' B') :=
    Ideal.mem_map_of_mem _ hsQ
  rw [h0, Ideal.mem_bot] at hm
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B')
    (mem_nonZeroDivisors_of_ne_zero hs)
  have h2 : s • (1 : B') = s • (0 : B') := by
    rw [Algebra.smul_def, mul_one, smul_zero]; exact hm
  exact one_ne_zero (hreg h2)

theorem divisor_descent : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A']
    [IsIntegrallyClosed A'] [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B']
    [Algebra A' B'] [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ b c : B', b * c = algebraMap A' B' s →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  intro A' B' _ _ _ _ _ _ _ _ _ _ s hs hpr b c hbc
  have hinj : ∀ a : A', a ≠ 0 → algebraMap A' B' a ≠ 0 := by
    intro a ha h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B')
      (mem_nonZeroDivisors_of_ne_zero ha)
    have h1 : a • (1 : B') = a • (0 : B') := by
      rw [Algebra.smul_def, mul_one, smul_zero]; exact h0
    exact one_ne_zero (hreg h1)
  have hb0 : b ≠ 0 := by rintro rfl; exact hinj s hs (by rw [← hbc, zero_mul])
  have hc0 : c ≠ 0 := by rintro rfl; exact hinj s hs (by rw [← hbc, mul_zero])
  have hloc : ∀ Q : Ideal B', Q.IsPrime → Q.height = 1 → b ∈ Q →
      ∃ j : A', c ∣ algebraMap A' B' j ∧ ∃ t ∉ Q, algebraMap A' B' j ∣ t * c := by
    intro Q hQ hQ1 hbQ
    have hsQ : algebraMap A' B' s ∈ Q := by rw [← hbc]; exact Q.mul_mem_right c hbQ
    obtain ⟨h𝔭1, h𝔭Q⟩ := primeDescent A' B' s hs hpr Q hQ hQ1 hsQ
    obtain ⟨j₀, ⟨t₁, ht₁, hj₁⟩, ⟨t₂, ht₂, hj₂⟩⟩ :=
      GlobalTheory.T.height_one_prime_associate A' B' (Q.comap (algebraMap A' B')) (by rw [h𝔭Q]; exact hQ) (by rw [h𝔭Q]; exact hQ1) c hc0
    rw [h𝔭Q] at ht₁ ht₂
    have hS0 : (0 : B') ∉ (Q.comap (algebraMap A' B')).primeCompl.map (algebraMap A' B') := by
      intro h0
      obtain ⟨u', hu', h⟩ := Submonoid.mem_map.1 h0
      by_cases hu0 : u' = 0
      · exact hu' (hu0 ▸ (Q.comap (algebraMap A' B')).zero_mem)
      · exact hinj u' hu0 h
    obtain ⟨u, huS, hu⟩ := GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one B' ((Q.comap (algebraMap A' B')).primeCompl.map (algebraMap A' B'))
      hS0 (algebraMap A' B' j₀) c hc0 (by
        intro Q' hQ' hQ'1 hcQ' hdisj
        have hsQ' : algebraMap A' B' s ∈ Q' := by rw [← hbc]; exact Q'.mul_mem_left b hcQ'
        obtain ⟨h𝔭'1, h𝔭'Q'⟩ := primeDescent A' B' s hs hpr Q' hQ' hQ'1 hsQ'
        have hle : Q'.comap (algebraMap A' B') ≤ Q.comap (algebraMap A' B') := by
          intro x hx
          by_contra hx𝔭
          exact Set.disjoint_left.1 hdisj (Submonoid.mem_map_of_mem (algebraMap A' B') hx𝔭) hx
        have heq : Q'.comap (algebraMap A' B') = Q.comap (algebraMap A' B') := by
          by_contra hne
          have := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hle hne)
          rw [h𝔭'1, h𝔭1] at this
          exact lt_irrefl _ this
        have hQQ : Q' = Q := by rw [← h𝔭'Q', heq, h𝔭Q]
        subst hQQ
        exact ⟨t₁, ht₁, hj₁⟩)
    obtain ⟨u', hu', rfl⟩ := Submonoid.mem_map.1 huS
    refine ⟨u' * j₀, by rw [map_mul]; exact hu, algebraMap A' B' u' * t₂, ?_, ?_⟩
    · intro hm
      rcases hQ.mem_or_mem hm with h | h
      · exact hu' h
      · exact ht₂ h
    · rw [map_mul, mul_assoc]; exact mul_dvd_mul_left _ hj₂
  apply colonStep A' B' b c s hbc
  intro x hx
  obtain ⟨u, hu, hdiv⟩ := GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one B' ⊥ (by simp) (algebraMap A' B' x) b hb0 (by
    intro Q hQ hQ1 hbQ _
    obtain ⟨j, hcj, t, htQ, z, hz⟩ := hloc Q hQ hQ1 hbQ
    obtain ⟨a, ha⟩ := hx j hcj
    refine ⟨t, htQ, ?_⟩
    have hj0 : algebraMap A' B' j ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hz
      rcases mul_eq_zero.1 hz with h | h
      · exact htQ (h ▸ Q.zero_mem)
      · exact hc0 h
    have hx' : algebraMap A' B' x * algebraMap A' B' j = b * c * algebraMap A' B' a := by
      rw [← map_mul, ha, map_mul, hbc]
    refine ⟨algebraMap A' B' a * z, mul_left_cancel₀ hj0 ?_⟩
    linear_combination t * hx' + b * algebraMap A' B' a * hz)
  rw [Submonoid.mem_bot] at hu
  subst hu
  simpa using hdiv

end GlobalTheory.DivDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorDescentFlatNormalDomainsStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_descent_flat_normal_domains : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A' B']
    [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ b c : B', b * c = algebraMap A' B' s →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  first | (exact @GlobalTheory.DivDescent.divisor_descent) | (exact GlobalTheory.DivDescent.divisor_descent) | (intros; apply GlobalTheory.DivDescent.divisor_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginNoeth
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnitsNoeth

theorem exists_unit_of_mem_map_comap {A' B' : Type} [CommRing A'] [CommRing B'] [IsDomain B']
    [IsLocalRing B'] (f : A' →+* B') (b : B')
    (h : b ∈ ((Ideal.span {b}).comap f).map f) : ∃ (d : A') (w : B'ˣ), b = f d * w := by
  by_cases hb : b = 0
  · exact ⟨0, 1, by simp [hb]⟩
  by_contra hne
  push_neg at hne
  have hle : ((Ideal.span {b}).comap f).map f ≤ Ideal.span {b} * maximalIdeal B' := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hd
    obtain ⟨z, hz⟩ := hd
    rw [Ideal.mem_comap, hz]
    by_cases hzu : IsUnit z
    · exact absurd (by rw [hz]; exact (Units.mul_inv_cancel_right b hzu.unit).symm) (hne d hzu.unit⁻¹)
    · exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self b) ((mem_maximalIdeal z).2 hzu)
  obtain ⟨m, hm, hbm⟩ := (Ideal.mem_span_singleton_mul).1 (hle h)
  have h1 : m = 1 := by
    have : b * (m - 1) = 0 := by rw [mul_sub, hbm, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hb
    · exact sub_eq_zero.1 h0
  exact (mem_maximalIdeal m).1 hm (h1 ▸ isUnit_one)

theorem divConst_origin_noeth : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 →
      bA * cA = algebraMap A (Localization.AtPrime QA) sA →
    ∃ (a : T) (w : Oˣ), jA bA = algebraMap T O a * (w : O) := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ QA _ hQA jA hjA
    bA cA sA hs hbc
  obtain ⟨A', _, _, _, _, B', _, _, _, _, _, _, _, ι, α, β, γ, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin T O hT P φ hφ hsh hP A i hi hil EA QA hQA jA hjA sA hs
  have hbc' : β bA * β cA = algebraMap A' B' (ι sA) := by
    have e := congrArg (fun g => g sA) h1
    simp only [RingHom.comp_apply] at e
    rw [e, ← hbc, map_mul]
  have hmem := GlobalTheory.T.divisor_descent_flat_normal_domains A' B' (ι sA) h4 h5 (β bA) (β cA) hbc'
  obtain ⟨d, w, hdw⟩ := exists_unit_of_mem_map_comap (algebraMap A' B') (β bA) hmem
  have e3 := congrArg (fun g => g d) h3
  simp only [RingHom.comp_apply] at e3
  refine ⟨α d, Units.map γ.toMonoidHom w, ?_⟩
  rw [← h2, RingHom.comp_apply, hdw, map_mul, e3]
  rfl

end GlobalTheory.VertUnitsNoeth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginNoethStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divConst_origin_noeth_alt : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 →
      bA * cA = algebraMap A (Localization.AtPrime QA) sA →
    ∃ (a : T) (w : Oˣ), jA bA = algebraMap T O a * (w : O) := by
  first | (exact @GlobalTheory.VertUnitsNoeth.divConst_origin_noeth) | (exact GlobalTheory.VertUnitsNoeth.divConst_origin_noeth) | (intros; apply GlobalTheory.VertUnitsNoeth.divConst_origin_noeth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleStageDivisorStrictHenselisationOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleStageDivisorStrictHenselisationOrigin
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginCut

theorem exists_stage_divisor : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (b₁ c₁ : Localization.AtPrime Q),
        b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s ∧ j b₁ = b ∧ j c₁ = c := by
  intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hPeq b c s hs hbc
  classical
  let I : Ideal (MvPolynomial (Fin 2) (Polynomial T)) :=
    Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (Polynomial.C s)}
  haveI : Algebra.FinitePresentation (Polynomial T) (MvPolynomial (Fin 2) (Polynomial T) ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_singleton _))
  have hI : ∀ a ∈ I, MvPolynomial.aeval (R := Polynomial T) ![b, c] a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker (MvPolynomial.aeval (R := Polynomial T) ![b, c]) := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      simp only [map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
      show b * c - _ = 0
      rw [hbc, IsScalarTower.algebraMap_apply T (Polynomial T) O, Polynomial.algebraMap_eq, sub_self]
    exact hle ha
  let g : (MvPolynomial (Fin 2) (Polynomial T) ⧸ I) →ₐ[Polynomial T] O :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![b, c]) hI
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime
    (Polynomial T) O P φ hφ hSH.2.2.2 _ g
  letI : Algebra T W := ((algebraMap (Polynomial T) W).comp (algebraMap T (Polynomial T))).toAlgebra
  haveI : IsScalarTower T (Polynomial T) W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  set Q : Ideal W := (maximalIdeal O).comap v.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) := by
    haveI := hSH.2.2.1
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
    · intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x hu)
  have hQP : Q.comap (algebraMap (Polynomial T) W) = P := by
    rw [hQdef, Ideal.comap_comap]
    have h1 : v.toRingHom.comp (algebraMap (Polynomial T) W) = φ.comp (algebraMap (Polynomial T) _) := by
      rw [hφ]; exact v.comp_algebraMap
    rw [h1, ← Ideal.comap_comap, hloc]
    exact Localization.AtPrime.under_maximalIdeal (R := Polynomial T) (I := P)
  have hunit : ∀ y : Q.primeCompl, IsUnit (v.toRingHom (y : W)) := by
    intro y
    by_contra hy
    exact y.2 (show (y : W) ∈ Q from (IsLocalRing.mem_maximalIdeal _).2 hy)
  let j : Localization.AtPrime Q →+* O := IsLocalization.lift (M := Q.primeCompl) hunit
  have hjE : j.comp (algebraMap W (Localization.AtPrime Q)) = v.toRingHom :=
    IsLocalization.lift_comp hunit
  have hjR : j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O := by
    rw [IsScalarTower.algebraMap_eq (Polynomial T) W (Localization.AtPrime Q), ← RingHom.comp_assoc, hjE]
    exact v.comp_algebraMap
  have hjW : ∀ w : W, j (algebraMap W (Localization.AtPrime Q) w) = v w := fun w =>
    congrArg (fun f => f w) hjE
  have hgX : ∀ i : Fin 2, v (u (Ideal.Quotient.mk I (MvPolynomial.X i))) = ![b, c] i := by
    intro i
    rw [← AlgHom.comp_apply, huv]
    show Ideal.Quotient.liftₐ I _ hI (Ideal.Quotient.mk I _) = _
    change MvPolynomial.aeval ![b, c] (MvPolynomial.X i) = _
    rw [MvPolynomial.aeval_X]
  have hprod : Ideal.Quotient.mk I (MvPolynomial.X 0) * Ideal.Quotient.mk I (MvPolynomial.X 1) =
      algebraMap (Polynomial T) _ (Polynomial.C s) := by
    rw [← map_mul, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q, inferInstance,
    hQP.trans hPeq, j, hjR, algebraMap W _ (u (Ideal.Quotient.mk I (MvPolynomial.X 0))),
    algebraMap W _ (u (Ideal.Quotient.mk I (MvPolynomial.X 1))), ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hprod, AlgHom.commutes,
      IsScalarTower.algebraMap_apply T W (Localization.AtPrime Q)]
    rfl
  · rw [hjW, hgX]; rfl
  · rw [hjW, hgX]; rfl

end GlobalTheory.KeyOriginCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleStageDivisorStrictHenselisationOriginStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (b₁ c₁ : Localization.AtPrime Q),
        b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s ∧ j b₁ = b ∧ j c₁ = c := by
  first | (exact @GlobalTheory.KeyOriginCut.exists_stage_divisor) | (exact GlobalTheory.KeyOriginCut.exists_stage_divisor) | (intros; apply GlobalTheory.KeyOriginCut.exists_stage_divisor  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOrigin
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem divConstOrigin : GlobalTheory.VertUnits.DivConstOrigin := by
  have h₁ := GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin
  have h₂ := GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants
  have h₃ := GlobalTheory.T.divConst_origin_noeth_alt
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith GlobalTheory.VertUnits.DivConst
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh _ hPo b c s hs hbc
  have hPo' : P = GlobalTheory.KeyOriginCut.originIdeal T := hPo
  obtain ⟨E, _, _, _, _, _, Q, _, hQ, j, hj, b₁, c₁, hbc₁, hjb, hjc⟩ :=
    h₁ T O hT P φ hφ hsh hPo' b c s hs hbc
  obtain ⟨A, _, _, _, _, _, _, i, hi, hil, EA, _, _, _, _, _, QA, _, hQA, jA, hjA, bA, cA, sA, hsA, hisA,
    hbcA, hjbA⟩ := h₂ T O hT E Q hQ j hj b₁ c₁ s hs hbc₁
  obtain ⟨a, w, haw⟩ := h₃ T O hT P φ hφ hsh hPo' A i hi hil EA QA hQA jA hjA bA cA sA hsA hbcA
  exact ⟨a, w, by rw [← hjb, ← hjbA, haw]⟩

end GlobalTheory.VertUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.div_const_origin : GlobalTheory.VertUnits.DivConstOrigin := by
  first | (exact @GlobalTheory.VertUnits.divConstOrigin) | (exact GlobalTheory.VertUnits.divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstOrigin <;> assumption)
end
