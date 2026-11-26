module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.CoprimeOfNotMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.EqOfKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.V0ok

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.KapCyc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem torsion_combination_smul_eq_zero {M : Type} [AddCommGroup M] (x γ β ε ω : M) (m n k q r : ℕ) (j : ℤ)
    (hx : m • x = 0) (hω : n • ω = 0) (hγ : 2 • γ + ω = ε) (hβ : k • (2 • β + (-(2 * j + 1)) • ε) = 0) :
    (2 * k * m * n) • (x + (2 * q + r + 4) • (-γ) + r • β + (-(r * j - q - 2 : ℤ)) • ε) = 0 := by
  linear_combination (norm := module) (2 * k * n : ℤ) • hx + (k * m * (2 * q + r + 4) : ℤ) • hω - (k * m * n * (2 * q + r + 4) : ℤ) • hγ + (m * n * r : ℤ) • hβ

private theorem mul_aux {M : Type} [CommGroup M] (x γ β ε ω : M) (m n k q r : ℕ) (j : ℤ)
    (hx : x ^ m = 1) (hω : ω ^ n = 1) (hγ : γ ^ 2 * ω = ε) (hβ : (β ^ 2 * ε ^ (-(2 * j + 1))) ^ k = 1) :
    (x * γ⁻¹ ^ (2 * q + r + 4) * β ^ r * ε ^ (-(r * j - q - 2 : ℤ))) ^ (2 * k * m * n) = 1 := by
  have h := torsion_combination_smul_eq_zero (M := Additive M) (Additive.ofMul x) (Additive.ofMul γ) (Additive.ofMul β)
    (Additive.ofMul ε) (Additive.ofMul ω) m n k q r j
    (by rw [← ofMul_pow, hx, ofMul_one]) (by rw [← ofMul_pow, hω, ofMul_one])
    (by rw [← ofMul_pow, ← ofMul_mul, hγ])
    (by rw [← ofMul_zpow, ← ofMul_pow, ← ofMul_mul, ← ofMul_pow, hβ, ofMul_one])
  apply_fun Additive.toMul at h
  simpa [toMul_nsmul, toMul_zsmul, toMul_add, toMul_neg, mul_pow, inv_pow] using h

theorem UpperTheory.V.Ws.Lk.kapCyc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (a b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ g ∈ Ine (F := T.L) A, (P.κ g * cycBar T.L Ω l g ^ (-a)) ^ k = 1 ∧ (P.βL g ^ 2 * cycBar T.L Ω l g ^ (-b)) ^ k = 1 := by
  intro Ω _ _ _ l _ c D T P hG A hA
  obtain ⟨b, k, hk, hb, hcyc⟩ := P.cyc A hA
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
  have hl : l.Prime := Fact.out
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact absurd (Nat.coprime_zero_right l |>.1 hm) hl.one_lt.ne'
    · exact h
  have hn0 : 0 < l - 1 := Nat.sub_pos_of_lt hl.one_lt
  refine ⟨((D.e % 2 : ℕ) : ℤ) * j - ((D.e / 2 : ℕ) : ℤ) - 2, 2 * j + 1, 2 * k * m * (l - 1),
    by positivity, ⟨j, rfl⟩, ?_⟩
  intro g hg
  have hω : (toQ D.om (resQ T.L g)) ^ (l - 1) = 1 := by
    rw [show toQ D.om (resQ T.L g) = Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l)
        (D.om (resQ T.L g)) from rfl,
      ← map_pow, ← MonoidHom.pow_apply, hG.om_pow, MonoidHom.one_apply, map_one]
  have hγ : P.γ (resQ T.L g) ^ 2 * toQ D.om (resQ T.L g) = cycBar T.L Ω l g := P.γ_sq _
  have hβ : (P.β (resLe (K_le T) g) ^ 2 * cycBar T.L Ω l g ^ (-(2 * j + 1))) ^ k = 1 :=
    hcyc _ hg
  have hx : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
    rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
  have hκ : P.κ g = P.κ₀ (resLe (K_le T) g) * (P.γ (resQ T.L g))⁻¹ ^ (D.e + 4) *
      P.β (resLe (K_le T) g) ^ (D.e % 2) := rfl
  constructor
  · rw [hκ, show D.e + 4 = 2 * (D.e / 2) + D.e % 2 + 4 by omega]
    exact mul_aux _ _ _ _ _ m (l - 1) k (D.e / 2) (D.e % 2) j hx hω hγ hβ
  · show (P.β (resLe (K_le T) g) ^ 2 * cycBar T.L Ω l g ^ (-(2 * j + 1))) ^ (2 * k * m * (l - 1)) = 1
    rw [show 2 * k * m * (l - 1) = k * (2 * m * (l - 1)) by ring, pow_mul, hβ, one_pow]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PadicPowL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem kill {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommGroup M] (f : Γ →* M)
    (hf : IsClosed (f.ker : Set Γ)) {g : Γ} {n : ℕ} (hg : g ^ n ∈ (commutator Γ).topologicalClosure) : f g ^ n = 1 := by
  rw [← map_pow]
  have hle : (commutator Γ).topologicalClosure ≤ f.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker f) hf
  exact hle hg

private theorem padic_pow_l {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2) (x : ℤ_[l]) (hx : x ^ l = 1) : x = 1 := by
  have hp := PadicInt.prime_p (p := l)
  have hodd : Odd l := hl.out.odd_of_ne_two h2
  have hc : PadicInt.toZMod x = 1 := by
    have h1 : PadicInt.toZMod x ^ l = 1 := by rw [← map_pow, hx, map_one]
    rw [ZMod.pow_card] at h1
    exact h1
  have hdvd : (l : ℤ_[l]) ∣ x - 1 := by
    have hs := PadicInt.toZMod_spec x
    rw [hc, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton, ZMod.cast_eq_val, ZMod.val_one,
      Nat.cast_one] at hs
    exact hs
  have hnd : ¬ (l : ℤ_[l]) ∣ x := by
    intro h
    have h1 : (l : ℤ_[l]) ∣ x ^ l := dvd_pow h hl.out.ne_zero
    rw [hx] at h1
    exact hp.not_dvd_one h1
  have key := emultiplicity_pow_prime_sub_pow_prime hp hodd hdvd hnd
  rw [hx, one_pow, sub_self, emultiplicity_zero] at key
  by_contra hne
  have hfin : FiniteMultiplicity (l : ℤ_[l]) (x - 1) :=
    FiniteMultiplicity.of_not_isUnit hp.not_unit (sub_ne_zero.2 hne)
  rw [hfin.emultiplicity_eq_multiplicity] at key
  exact ENat.coe_ne_top (multiplicity (l : ℤ_[l]) (x - 1) + 1) (by push_cast; exact key.symm)

private theorem padic_pow {l : ℕ} [Fact l.Prime] (h2 : l ≠ 2) (a : ℕ) (x : ℤ_[l]) (hx : x ^ l ^ a = 1) : x = 1 := by
  induction a generalizing x with
  | zero => simpa using hx
  | succ a ih =>
    apply ih
    apply padic_pow_l h2
    rw [← pow_mul, ← pow_succ]
    exact hx

theorem UpperTheory.V.Ws.Lk.kapMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → ∀ (g : G T.L Ω) (a : ℕ), g ^ l ^ a ∈ (commutator (G T.L Ω)).topologicalClosure → P.κ g = 1 ∧ P.tL g = 1 := by
  intro Ω _ _ _ l _ c D T P hD g a hg
  have h2 : l ≠ 2 := Raw.Good.l_odd hD
  have hl := (Fact.out : l.Prime)
  have hcLe : Continuous (resLe (K_le T)) := by
    letI : Algebra T.K T.L := (IntermediateField.inclusion (K_le T)).toAlgebra
    haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    exact Af.continuous_restrictScalarsHom T.K T.L Ω
  have ht : P.tL g = 1 := by
    have hk : IsClosed ((P.t.comp (resLe (K_le T))).ker : Set (G T.L Ω)) :=
      isClosed_singleton.preimage (P.t_cont.comp hcLe)
    have hp := kill (P.t.comp (resLe (K_le T))) hk hg
    change (P.t.comp (resLe (K_le T))) g = 1
    have hz : (l ^ a) • Multiplicative.toAdd ((P.t.comp (resLe (K_le T))) g) = 0 := by
      rw [← toAdd_pow, hp, toAdd_one]
    have hz' := (smul_eq_zero.1 hz).resolve_left (pow_ne_zero _ hl.ne_zero)
    rw [← ofAdd_toAdd ((P.t.comp (resLe (K_le T))) g), hz', ofAdd_zero]
  refine ⟨?_, ht⟩
  have hβ : P.βL g = 1 := P.β_t ht
  have hγ : P.γ (resQ T.L g) = 1 := by
    have hcQ : Continuous (resQ T.L) := Af.continuous_restrictScalarsHom ℚ T.L Ω
    have hk : IsClosed (((cycZ ℚ Ω l).comp (resQ T.L)).ker : Set (G T.L Ω)) :=
      isClosed_singleton.preimage ((continuous_cycZ ℚ Ω l).comp hcQ)
    have hp := kill ((cycZ ℚ Ω l).comp (resQ T.L)) hk hg
    have hu : ((((cycZ ℚ Ω l).comp (resQ T.L)) g : ℤ_[l]ˣ) : ℤ_[l]) = 1 :=
      padic_pow h2 a _ (by rw [← Units.val_pow_eq_pow_val, hp, Units.val_one])
    exact P.γ_ker (Units.ext hu)
  have hκ : P.κ₀ (resLe (K_le T) g) = 1 := by
    have hk : IsClosed ((P.κ₀.comp (resLe (K_le T))).ker : Set (G T.L Ω)) :=
      (Subgroup.isClosed_of_isOpen _ P.κ₀_open).preimage hcLe
    have hp := kill (P.κ₀.comp (resLe (K_le T))) hk hg
    obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
    have hq : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
      rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
    have hcop : Nat.Coprime (l ^ a) m := Nat.Coprime.pow_left a hm
    have := pow_gcd_eq_one.2 ⟨hp, hq⟩
    rwa [hcop, pow_one] at this
  have hγ' : P.γ (AlgEquiv.restrictScalars ℚ g) = 1 := hγ
  simp only [Pre.κ, MonoidHom.mul_apply, MonoidHom.comp_apply, hβ, hγ, hκ]
  simp [hγ', hβ]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.KapCont
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem cont_resLe {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {F L : IntermediateField ℚ Ω} (h : F ≤ L) :
    Continuous (resLe h) := by
  letI : Algebra F L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Af.continuous_restrictScalarsHom F L Ω

private theorem cont_of_open_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (h : IsOpen (f.ker : Set Γ)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one]
  have hk : (f.ker : Set Γ) ∈ nhds (1 : Γ) := h.mem_nhds (one_mem _)
  exact (Filter.tendsto_pure.2 (Filter.mem_of_superset hk fun x hx => MonoidHom.mem_ker.1 hx)).mono_right (pure_le_nhds _)

theorem UpperTheory.V.Ws.Lk.kapCont :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), Continuous P.κ ∧ Continuous P.βL ∧ Continuous P.tL := by
  intro Ω _ _ _ l _ c D T P
  have hβ : Continuous P.βL := P.β_cont.comp (cont_resLe _)
  have ht : Continuous P.tL := P.t_cont.comp (cont_resLe _)
  refine ⟨?_, hβ, ht⟩
  have h0 : Continuous (P.κ₀.comp (resLe (K_le T))) :=
    (cont_of_open_ker P.κ₀ P.κ₀_open).comp (cont_resLe _)
  have h1 : Continuous (P.γ.comp (resQ T.L)) :=
    P.γ_cont.comp (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.L Ω)
  show Continuous fun g => P.κ₀.comp (resLe (K_le T)) g * ((P.γ.comp (resQ T.L)) g)⁻¹ ^ (D.e + 4) * P.βL g ^ (D.e % 2)
  exact (h0.mul ((h1.inv).pow _)).mul (hβ.pow _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.BetaCyc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
open scoped Pointwise

namespace UpperTheory.V.Ws.Lk.BetaCyclotomicPlace

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℤ)) := Nat.prime_iff_prime_int.1 hl.out
  have h2 := (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv.symm : ℤ ≃* 𝓞 ℚ)).2 h
  simpa using h2

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

variable {l} {Ω : Type} [Field Ω]

private theorem isPlaceOver_vQ [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, by rw [← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]⟩
  have hcast : algebraMap ℚ Ω (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := by simp
  rw [hcast]
  show _ ↔ (n : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  rw [Ideal.mem_span_singleton]
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m => (A.valuation_le_one_iff _).2 (intCast_mem A m)
  have hdvd : ((l : ℕ) : 𝓞 ℚ) ∣ (n : 𝓞 ℚ) ↔ (l : ℤ) ∣ n := by
    rw [show ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (l : ℤ) by simp,
      show (n : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n by simp, map_dvd_iff]
  rw [hdvd]
  constructor
  · intro hv
    by_contra hnd
    have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hnd
    have h1 : A.valuation ((a * l + b * n : ℤ) : Ω) < 1 := by
      push_cast
      apply lt_of_le_of_lt (A.valuation.map_add _ _)
      apply max_lt
      · rw [map_mul]
        calc A.valuation (a : Ω) * A.valuation ((l : ℕ) : Ω) ≤ 1 * A.valuation ((l : ℕ) : Ω) :=
              mul_le_mul' (hle a) le_rfl
          _ < 1 := by rw [one_mul]; exact hA
      · rw [map_mul]
        calc A.valuation (b : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) := mul_le_mul' (hle b) le_rfl
          _ < 1 := by rw [one_mul]; exact hv
    rw [hab] at h1
    simp at h1
  · rintro ⟨y, rfl⟩
    push_cast
    rw [map_mul]
    calc A.valuation ((l : ℕ) : Ω) * A.valuation (y : Ω) ≤ A.valuation ((l : ℕ) : Ω) * 1 :=
          mul_le_mul' le_rfl (hle y)
      _ < 1 := by rw [mul_one]; exact hA

end UpperTheory.V.Ws.Lk.BetaCyclotomicPlace

open UpperTheory.V.Ws.Lk.BetaCyclotomicPlace in
theorem UpperTheory.V.Ws.Lk.betaCyc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ Ω) [NumberField K], Module.finrank ℚ K = 2 → ∀ A₀ : ValuationSubring Ω, A₀.valuation (l : Ω) < 1 → ∀ β : G K Ω →* (PadicAlgCl l)ˣ, (∀ σ ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = σ * resQ K s * σ⁻¹ → β s * β s' = 1) → ∀ U : Subgroup (G K Ω), IsOpen (U : Set (G K Ω)) → (∀ B : ValuationSubring Ω, (∀ x ∈ K, x ∈ B ↔ x ∈ A₀) → ∀ s ∈ U ⊓ Ine (F := K) B, (β s : PadicAlgCl l) ^ 2 = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l s : ℤ_[l])) → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ s ∈ Ine (F := K) A, (β s ^ 2 * cycBar K Ω l s ^ (-b)) ^ k = 1 := by
  intro Ω _ _ _ l _ K _ hK A₀ hA₀ β hconj U hU hcyc A hA
  have hn : U.index ≠ 0 := by
    haveI : Finite (G K Ω ⧸ U) := U.quotient_finite_of_isOpen hU
    exact Subgroup.index_ne_zero_of_finite
  have hpow : ∀ s : G K Ω, s ^ U.index.factorial ∈ U := fun s =>
    Subgroup.pow_mem_of_index_ne_zero_of_dvd hn s (fun m h1 h2 => Nat.dvd_factorial h1 h2)
  have hkpos : 0 < U.index.factorial := Nat.factorial_pos _
  have hval : ∀ t : G K Ω, ((cycBar K Ω l t : (Qbar l)ˣ) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l t : ℤ_[l]) := fun t => rfl
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (isPlaceOver_vQ A₀ hA₀) (isPlaceOver_vQ A hA)
  by_cases hσK : σ ∈ K.fixingSubgroup
  · refine ⟨1, U.index.factorial, hkpos, odd_one, ?_⟩
    have hB : ∀ x ∈ K, x ∈ A ↔ x ∈ A₀ := by
      intro x hx
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have hfix : σ⁻¹ • x = x := (K.fixingSubgroup.inv_mem hσK) ⟨x, hx⟩
      rw [hfix]
    intro s hs
    have ht : s ^ U.index.factorial ∈ U ⊓ Ine (F := K) A := ⟨hpow s, pow_mem hs _⟩
    have h1 : β (s ^ U.index.factorial) ^ 2 = cycBar K Ω l (s ^ U.index.factorial) :=
      Units.ext (by push_cast; rw [hcyc A hB _ ht, hval])
    have e1 : (β s ^ 2 * cycBar K Ω l s ^ (-1 : ℤ)) ^ U.index.factorial =
        β (s ^ U.index.factorial) ^ 2 * (cycBar K Ω l (s ^ U.index.factorial))⁻¹ := by
      rw [map_pow, map_pow, zpow_neg, zpow_one]
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm 2]
    rw [e1, h1, mul_inv_cancel]
  · refine ⟨-1, U.index.factorial, hkpos, ⟨-1, by norm_num⟩, ?_⟩
    haveI hN : K.fixingSubgroup.Normal := by
      refine (InfiniteGalois.normal_iff_isGalois K).2 ?_
      haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
      exact isGalois_iff.2 ⟨Algebra.IsSeparable.of_integral _ _, Algebra.IsQuadraticExtension.normal ℚ K⟩
    intro s hs
    have hg : resQ K s ∈ Ine (F := ℚ) A := (resQ_Ine K A s).1 hs
    have hlift : IsLift (RingEquiv.refl ℚ) (σ : Ω ≃+* Ω) := fun y => by simp
    have hg' : conjGal hlift (resQ K s) ∈ Ine (F := ℚ) A₀ := by
      refine conjGal_mem_Ine hlift (fun x => ?_) hg
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      show σ⁻¹ • σ • x ∈ A₀ ↔ x ∈ A₀
      rw [inv_smul_smul]
    have heq : conjGal hlift (resQ K s) = σ⁻¹ * resQ K s * σ := by
      ext x
      rfl
    have hmem : σ⁻¹ * resQ K s * σ ∈ K.fixingSubgroup := by
      have h' := hN.conj_mem _ (resQ_mem K s) σ⁻¹
      rwa [inv_inv] at h'
    obtain ⟨s', hs'⟩ := exists_resQ hmem
    have hs'I : s' ∈ Ine (F := K) A₀ := (resQ_Ine K A₀ s').2 (by rw [hs', ← heq]; exact hg')
    have hσ' : σ⁻¹ ∉ K.fixingSubgroup := fun h' => hσK (by simpa using K.fixingSubgroup.inv_mem h')
    have hbb : β s * β s' = 1 := hconj σ⁻¹ hσ' s s' (by rw [hs', inv_inv])
    have hcy : cycBar K Ω l s' = cycBar K Ω l s := by
      show Units.map _ (cycZ K Ω l s') = Units.map _ (cycZ K Ω l s)
      have hz : cycZ ℚ Ω l (σ⁻¹ * resQ K s * σ) = cycZ ℚ Ω l (resQ K s) := by
        rw [map_mul, map_mul, map_inv, mul_comm (cycZ ℚ Ω l σ)⁻¹, inv_mul_cancel_right]
      rw [← resQ_cyc, ← resQ_cyc, hs', hz]
    have ht' : s' ^ U.index.factorial ∈ U ⊓ Ine (F := K) A₀ := ⟨hpow s', pow_mem hs'I _⟩
    have h1 : β (s' ^ U.index.factorial) ^ 2 = cycBar K Ω l (s' ^ U.index.factorial) :=
      Units.ext (by push_cast; rw [hcyc A₀ (fun _ _ => Iff.rfl) _ ht', hval])
    have hbs : β s = (β s')⁻¹ := eq_inv_of_mul_eq_one_left hbb
    have e2 : (β s ^ 2 * cycBar K Ω l s ^ (-(-1) : ℤ)) ^ U.index.factorial =
        (β (s' ^ U.index.factorial) ^ 2)⁻¹ * cycBar K Ω l (s' ^ U.index.factorial) := by
      rw [neg_neg, zpow_one, hbs, ← hcy, map_pow, map_pow]
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm 2]
    rw [e2, h1, inv_mul_cancel]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.NoMu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.noMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, D.Good → ∀ (L : IntermediateField ℚ Ω) (g : G L Ω), Raw.bar D.om (resQ L g) ≠ 1 → ¬ ∃ ζ : L, IsPrimitiveRoot ζ l := by
  intro Ω _ _ _ l _ c D hD L g hbar hroot
  obtain ⟨ζ, hζ⟩ := hroot
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  haveI := c.fin
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hζΩ : IsPrimitiveRoot (ζ : Ω) l := hζ.map_of_injective (L.val : L →+* Ω).injective
  set σ : G ℚ Ω := resQ L g with hσ
  set χ : ℤ_[l] := ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hχ
  have hfix : (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) (ζ : Ω) = (ζ : Ω) := g.commutes ζ
  have hspec := cyclotomicCharacter.spec (L := Ω) l (n := 1)
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) (ζ : Ω) (by rw [pow_one]; exact hζΩ.pow_eq_one)
  rw [hfix] at hspec
  have hmod : PadicInt.toZModPow 1 χ = 1 := by
    haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl⟩
    apply ZMod.val_injective
    rw [ZMod.val_one]
    have hlt : (PadicInt.toZModPow 1 χ).val < l :=
      lt_of_lt_of_eq (ZMod.val_lt (PadicInt.toZModPow 1 χ)) (pow_one l)
    apply hζΩ.pow_inj hlt hl
    exact hspec.symm.trans (pow_one _).symm
  have hmem : χ - 1 ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, hmod, map_one, sub_self]
  have hnu : algebraMap ℤ_[l] c.O (χ - 1) ∈ IsLocalRing.maximalIdeal c.O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem (IsUnit.of_map (algebraMap ℤ_[l] c.O) _ hu)
  apply hbar
  rw [hD.om_bar]
  change IsLocalRing.residue c.O (algebraMap ℤ_[l] c.O χ) = 1
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, map_one] at hnu
  exact sub_eq_zero.mp hnu
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.KapUnr
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.kapUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := T.L) A ≤ P.tL.ker) ∧ (∀ A, Raw.Away D.S A → Ine (F := T.L) A ≤ P.κ.ker) ∧ ∃ m : ℕ, l.Coprime m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A, P.κ g ^ m = 1 := by
  intro Ω _ _ _ l _ c D T P hG
  have hK : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := T.L) A, resLe (K_le T) g ∈ Ine (F := T.K) A :=
    fun A g hg => hg
  have hQ : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := T.L) A, resQ T.L g ∈ Ine (F := ℚ) A :=
    fun A g hg => hg
  have ht : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.t (resLe (K_le T) g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.t_unr A hA (hK A g hg))
  have hb : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.β (resLe (K_le T) g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.β_t (P.t_unr A hA (hK A g hg)))
  have hc : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.γ (resQ T.L g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.γ_ker ((places ℚ Ω l A).2.2.2 hA (hQ A g hg)))
  have hκ : ∀ g, P.κ g = P.κ₀ (resLe (K_le T) g) * (P.γ (resQ T.L g))⁻¹ ^ (D.e + 4) *
      P.β (resLe (K_le T) g) ^ (D.e % 2) := fun g => rfl
  obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
  refine ⟨fun A hA g hg => MonoidHom.mem_ker.2 (ht A hA g hg), ?_, m, hm, ?_⟩
  · intro A hA g hg
    have hl : ¬ A.valuation (l : Ω) < 1 := hA l hG.l_mem
    rw [MonoidHom.mem_ker, hκ, MonoidHom.mem_ker.1 (P.κ₀_unr A hA (hK A g hg)), hc A hl g hg,
      hb A hl g hg]
    simp
  · intro A hA g hg
    have h0 : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
      rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
    rw [hκ, hc A hA g hg, hb A hA g hg]
    simp [h0]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.UnitDivNear
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.MuChar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem unit_pow (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (h : Module.finrank ℚ K = 2) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : (𝓞 K)ˣ, u ^ m = 1 := by
  have hr : Units.rank K = 0 := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, h] at h1
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  refine ⟨Nat.card (Units.torsion K), Nat.card_pos, fun u => ?_⟩
  obtain ⟨⟨ζ, e⟩, h1, -⟩ := Units.exist_unique_eq_mul_prod K u
  haveI : IsEmpty (Fin (Units.rank K)) := by rw [hr]; infer_instance
  rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h1
  rw [h1, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]

private theorem class_pow (K : Type) [Field K] [NumberField K] :
    ∃ h : ℕ, 0 < h ∧ ∀ I : Ideal (𝓞 K), I ≠ ⊥ → ∃ a : 𝓞 K, I ^ h = Ideal.span {a} := by
  refine ⟨Nat.card (ClassGroup (𝓞 K)), Nat.card_pos, fun I hI => ?_⟩
  have hm : I ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hI
  have h1 : ClassGroup.mk0 ((⟨I, hm⟩ : nonZeroDivisors (Ideal (𝓞 K))) ^ Nat.card (ClassGroup (𝓞 K))) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact ((ClassGroup.mk0_eq_one_iff (Submonoid.pow_mem _ hm _)).1 h1).principal

private theorem exists_iota {R : Type} [CommRing R] {l : ℕ} [Fact l.Prime] (w : Ideal R)
    (h : ∀ n : ℕ, ∃ φ : R →+* ZMod (l ^ n), RingHom.ker φ = w ^ n) :
    ∃ ι : R →+* ℤ_[l], ∀ n x, PadicInt.toZModPow n (ι x) = 0 ↔ x ∈ w ^ n := by
  choose φ hφ using h
  have hc : ∀ (k1 k2) (hk : k1 ≤ k2), (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1))).comp (φ k2) = φ k1 := by
    intro k1 k2 hk
    ext x
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective (φ k2 x)
    have h1 : x - z ∈ RingHom.ker (φ k1) := by
      rw [hφ]
      refine Ideal.pow_le_pow_right hk ?_
      rw [← hφ, RingHom.mem_ker, map_sub, map_intCast, hz, sub_self]
    rw [RingHom.mem_ker, map_sub, map_intCast, sub_eq_zero] at h1
    rw [RingHom.comp_apply, ← hz, map_intCast, h1]
  refine ⟨PadicInt.lift hc, fun n x => ?_⟩
  rw [← RingHom.comp_apply, PadicInt.lift_spec, ← hφ, RingHom.mem_ker]

private theorem cont_of_open {Γ C : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group C]
    [TopologicalSpace C] [IsTopologicalGroup C] (κ : Γ →* C) (h : IsOpen (κ.ker : Set Γ)) : Continuous κ := by
  refine continuous_of_continuousAt_one κ ?_
  refine (continuousAt_const (y := (1 : C))).congr ?_
  filter_upwards [h.mem_nhds (one_mem κ.ker)] with x hx
  exact (MonoidHom.mem_ker.1 hx).symm

private theorem exists_limit {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {l : ℕ} [hl : Fact l.Prime]
    (D : Set Γ) (hD : Dense D) (κ : ∀ k : ℕ, Γ →* (ZMod (l ^ k))ˣ) (ho : ∀ k, IsOpen ((κ k).ker : Set Γ))
    (hx : ∀ s ∈ D, ∃ u : ℤ_[l], ∀ k, (κ k s : ZMod (l ^ k)) = PadicInt.toZModPow k u) :
    ∃ μ : Γ →* ℤ_[l]ˣ, Continuous μ ∧ ∀ k s, PadicInt.toZModPow k (μ s : ℤ_[l]) = κ k s := by
  let f : ∀ k : ℕ, MonoidAlgebra ℤ Γ →+* ZMod (l ^ k) := fun k =>
    (MonoidAlgebra.lift ℤ (ZMod (l ^ k)) Γ ((Units.coeHom _).comp (κ k))).toRingHom
  have hf : ∀ k s, f k (MonoidAlgebra.of ℤ Γ s) = κ k s := fun k s => MonoidAlgebra.lift_of _ _
  have hc : ∀ (k1 k2) (hk : k1 ≤ k2), (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1))).comp (f k2) = f k1 := by
    intro k1 k2 hk
    refine MonoidAlgebra.ringHom_ext' (RingHom.ext_int _ _) (MonoidHom.ext fun s => ?_)
    show ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1)) (f k2 (MonoidAlgebra.of ℤ Γ s)) = f k1 (MonoidAlgebra.of ℤ Γ s)
    rw [hf, hf]
    have c1 : Continuous fun s => (κ k1 s : ZMod (l ^ k1)) := Units.continuous_val.comp (cont_of_open _ (ho k1))
    have c2 : Continuous fun s => ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1)) (κ k2 s : ZMod (l ^ k2)) :=
      continuous_of_discreteTopology.comp (Units.continuous_val.comp (cont_of_open _ (ho k2)))
    refine congrFun (Continuous.ext_on hD c2 c1 fun t ht => ?_) s
    obtain ⟨u, hu⟩ := hx t ht
    show ZMod.castHom _ _ _ = _
    rw [hu, hu, ← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow _ _ hk]
  let ν : Γ →* ℤ_[l] := (PadicInt.lift hc).toMonoidHom.comp (MonoidAlgebra.of ℤ Γ)
  have hν : ∀ k s, PadicInt.toZModPow k (ν s) = κ k s := fun k s => by
    rw [← hf, ← PadicInt.lift_spec hc k]; rfl
  have cν : Continuous ν := by
    refine continuous_iff_continuousAt.2 fun s => Metric.continuousAt_iff'.2 fun ε hε => ?_
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
    have c1 : Continuous fun s => (κ k s : ZMod (l ^ k)) := Units.continuous_val.comp (cont_of_open _ (ho k))
    filter_upwards [((isOpen_discrete {(κ k s : ZMod (l ^ k))}).preimage c1).mem_nhds rfl] with t ht
    refine lt_of_le_of_lt ?_ hk
    rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hν, hν,
      sub_eq_zero]
    exact ht
  refine ⟨ν.toHomUnits, Units.continuous_iff.2 ⟨cν, ?_⟩, hν⟩
  have : (fun s => ((ν.toHomUnits s)⁻¹ : ℤ_[l]ˣ).val) = fun s => ν s⁻¹ := by
    funext s; rw [← map_inv]; rfl
  rw [this]
  exact cν.comp continuous_inv

private theorem iota_unit {R : Type} [CommRing R] {l : ℕ} [hl : Fact l.Prime] {w : Ideal R} {ι : R →+* ℤ_[l]}
    (h : ∀ n x, PadicInt.toZModPow n (ι x) = 0 ↔ x ∈ w ^ n) {a : R} (ha : IsCoprime (Ideal.span {a}) w) :
    IsUnit (ι a) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.1 ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  have h1 : ι y ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow, RingHom.mem_ker, h, pow_one]
    exact hy
  have h2 : IsUnit (1 - ι y) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h1
  rw [← map_one ι, ← map_sub, ← hxy, add_sub_cancel_right, map_mul] at h2
  exact isUnit_of_mul_isUnit_right h2

private theorem unit_fermat {l : ℕ} [hl : Fact l.Prime] {x : ℤ_[l]} (hx : IsUnit x) (m : ℕ) :
    ‖x ^ (m * (l - 1)) - 1‖ < 1 := by
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    mul_comm, pow_mul, ZMod.pow_card_sub_one_eq_one (hx.map _).ne_zero, one_pow, map_one, sub_self]

private theorem exists_F (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    {l : ℕ} [hl : Fact l.Prime] {w : Ideal (𝓞 K)} {ι : 𝓞 K →+* ℤ_[l]}
    (hι : ∀ n x, PadicInt.toZModPow n (ι x) = 0 ↔ x ∈ w ^ n) :
    ∃ (F : Ideal (𝓞 K) → ℤ_[l]ˣ) (n : ℕ), 0 < n ∧
      (∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I w → IsCoprime J w → F (I * J) = F I * F J) ∧
      (∀ a, IsCoprime (Ideal.span {a}) w → (F (Ideal.span {a}) : ℤ_[l]) = ι a ^ n) ∧
      ∀ I, I ≠ ⊥ → IsCoprime I w → ‖(F I : ℤ_[l]) - 1‖ < 1 := by
  classical
  obtain ⟨m, hm, hu⟩ := unit_pow K hK
  obtain ⟨h, hh, hc⟩ := class_pow K
  let P : Ideal (𝓞 K) → ℤ_[l]ˣ → Prop := fun I u => ∃ a, I ^ h = Ideal.span {a} ∧ (u : ℤ_[l]) = ι a ^ (m * (l - 1))
  have uniq : ∀ I u v, P I u → P I v → u = v := by
    rintro I u v ⟨a, ha, hu'⟩ ⟨b, hb, hv⟩
    obtain ⟨e, rfl⟩ := Ideal.span_singleton_eq_span_singleton.1 (ha.symm.trans hb)
    apply Units.ext
    rw [hu', hv, map_mul, mul_pow, ← map_pow ι (e : 𝓞 K), pow_mul (e : 𝓞 K), ← Units.val_pow_eq_pow_val, hu]
    simp
  let F : Ideal (𝓞 K) → ℤ_[l]ˣ := fun I => if hI : ∃ u, P I u then hI.choose else 1
  have hF : ∀ I u, P I u → F I = u := fun I u hI => by
    have h1 : ∃ u, P I u := ⟨u, hI⟩
    simp only [F, dif_pos h1]
    exact uniq I _ _ h1.choose_spec hI
  have ex : ∀ I, I ≠ ⊥ → IsCoprime I w → ∃ a, IsUnit (ι a) ∧ I ^ h = Ideal.span {a} ∧
      (F I : ℤ_[l]) = ι a ^ (m * (l - 1)) := fun I hI hw => by
    obtain ⟨a, ha⟩ := hc I hI
    have h1 : IsUnit (ι a) := iota_unit hι (ha ▸ hw.pow_left)
    refine ⟨a, h1, ha, ?_⟩
    rw [hF I (h1.unit ^ (m * (l - 1))) ⟨a, ha, by simp⟩]
    simp
  refine ⟨F, h * (m * (l - 1)), Nat.mul_pos hh (Nat.mul_pos hm (Nat.sub_pos_of_lt hl.out.one_lt)), ?_, ?_, ?_⟩
  · intro I J hI hJ hI' hJ'
    obtain ⟨a, -, ha, ha'⟩ := ex I hI hI'
    obtain ⟨b, -, hb, hb'⟩ := ex J hJ hJ'
    refine hF _ _ ⟨a * b, ?_, ?_⟩
    · rw [mul_pow, ha, hb, Ideal.span_singleton_mul_span_singleton]
    · rw [Units.val_mul, ha', hb', map_mul, mul_pow]
  · intro a ha
    have h1 : IsUnit (ι a) := iota_unit hι ha
    rw [hF _ (h1.unit ^ (h * (m * (l - 1)))) ⟨a ^ h, Ideal.span_singleton_pow _ _, by simp [pow_mul]⟩]
    simp
  · intro I hI hw
    obtain ⟨a, h1, -, ha⟩ := ex I hI hw
    rw [ha]
    exact unit_fermat h1 m

private theorem exists_conj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : IntermediateField ℚ Ω)
    [NumberField K] (hK : Module.finrank ℚ K = 2) (c : G ℚ Ω) :
    ∃ j : G K Ω → G K Ω, Continuous j ∧ (∀ s, resQ K (j s) = c * resQ K s * c⁻¹) ∧ Function.Injective (resQ K) := by
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK }
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  have he := (galEmbTop ℚ K Ω).1
  have h1 : ∀ s, ∃ t, galEmb ℚ K Ω t = c * galEmb ℚ K Ω s * c⁻¹ := fun s => by
    have := (galOf_normal ℚ K Ω).conj_mem _ (galEmb_mem ℚ K Ω s) c
    rwa [← range_galEmb] at this
  choose j hj using h1
  refine ⟨j, he.continuous_iff.2 ?_, hj, he.injective⟩
  have : galEmb ℚ K Ω ∘ j = fun s => c * galEmb ℚ K Ω s * c⁻¹ := funext hj
  rw [this]
  exact (continuous_const.mul he.continuous).mul continuous_const

theorem UpperTheory.V.Ws.Tw.muChar :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : IntermediateField ℚ Ω) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup → ∃ (μ : G K Ω →* ℤ_[l]ˣ) (n : ℕ), 0 < n ∧ Continuous μ ∧ (∀ s, ‖(μ s : ℤ_[l]) - 1‖ < 1) ∧ (∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ → μ s * μ s' = cycZ K Ω l s ^ n) ∧ ∀ B : ValuationSubring Ω, (∃ x ∈ K, ¬ (x ∈ B ↔ x ∈ A)) → Ine (F := K) B ≤ μ.ker := by
  intro Ω _ _ _ l hl hl2 K _ _ hK A hA hDec
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  obtain ⟨τ, -, hN, hconj, hsplit, -⟩ := Tw.quadFacts Ω l hl2 K hK
  obtain ⟨w, hw, -, -, hφ⟩ := hsplit l A hl.out hA hDec
  obtain ⟨ι, hι⟩ := exists_iota w.asIdeal hφ
  obtain ⟨F, n, hn, hmul, hpr, hone⟩ := exists_F K hK hι
  have hlw : (l : 𝓞 K) ∈ w.asIdeal := ((places K Ω l A).2.2.1 w hw).1 hA
  have hray : ∀ k : ℕ, ∃ κ : G K Ω →* (ZMod (l ^ k))ˣ, IsOpen (κ.ker : Set (G K Ω)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ≠ w → ∀ B : ValuationSubring Ω, IsPlaceOver B v → Ine (F := K) B ≤ κ.ker ∧
        ∀ σ : G K Ω, IsFrob B (normV v) σ → (κ σ : ZMod (l ^ k)) = PadicInt.toZModPow k (F v.asIdeal : ℤ_[l]) := by
    intro k
    obtain ⟨κ, h1, h2⟩ := Tw.rayChar K Ω (w.asIdeal ^ (k + 1)) (pow_ne_zero _ w.ne_bot) (ZMod (l ^ k))ˣ
      (fun I => Units.map (PadicInt.toZModPow k).toMonoidHom (F I))
      (fun I J hI hJ hI' hJ' => by
        rw [hmul I J hI hJ ((IsCoprime.pow_right_iff k.succ_pos).1 hI') ((IsCoprime.pow_right_iff k.succ_pos).1 hJ'),
          map_mul])
      (fun a _ ha => by
        have hc : IsCoprime (Ideal.span {a}) w.asIdeal :=
          Ideal.isCoprime_iff_exists.2 ⟨a, Ideal.mem_span_singleton_self a, -(a - 1),
            neg_mem (Ideal.pow_le_self k.succ_ne_zero ha), by ring⟩
        have h3 := (hι k _).2 (Ideal.pow_le_pow_right k.le_succ ha)
        rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h3
        apply Units.ext
        show PadicInt.toZModPow k (F _ : ℤ_[l]) = 1
        rw [hpr a hc, map_pow, h3, one_pow])
    refine ⟨κ, h1, fun v hv B hB => ?_⟩
    obtain ⟨h3, h4⟩ := h2 v (fun hd => hv (HeightOneSpectrum.ext
      ((prime_dvd_prime_iff_eq v.prime w.prime).1 (v.prime.dvd_of_dvd_pow hd)))) B hB
    exact ⟨h3, fun σ hσ => by rw [h4 σ hσ]; rfl⟩
  choose κ hκo hκ using hray
  have hl0 : Ideal.span {(l : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.out.ne_zero
  have hD := Tw.frobDense K Ω _ hl0
  simp only [Ideal.dvd_span_singleton] at hD
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ v.asIdeal → v ≠ w := fun v hv h => hv (h ▸ hlw)
  have hcop : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ w → IsCoprime v.asIdeal w.asIdeal := fun v hv =>
    Ideal.isCoprime_iff_sup_eq.2 (v.isMaximal.coprime_of_ne w.isMaximal fun h => hv (HeightOneSpectrum.ext h))
  obtain ⟨μ, hμc, hμ⟩ := exists_limit _ hD κ hκo (by
    rintro s ⟨v, B, hv, hB, hs⟩
    exact ⟨_, fun k => (hκ k v (hne v hv) B hB).2 s hs⟩)
  have hfr : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ w → ∀ B, IsPlaceOver B v → ∀ σ : G K Ω, IsFrob B (normV v) σ →
      μ σ = F v.asIdeal := fun v hv B hB σ hσ =>
    Units.ext (PadicInt.ext_of_toZModPow.1 fun k => by rw [hμ, (hκ k v hv B hB).2 σ hσ])
  refine ⟨μ, n, hn, hμc, fun s => ?_, fun c hc s s' hs => ?_, fun B ⟨x, hxK, hx⟩ => ?_⟩
  · have hcl : IsClosed {s : G K Ω | (μ s : ℤ_[l]) ∈ Metric.ball (1 : ℤ_[l]) 1} :=
      (IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp hμc)
    have h1 := hD.induction (P := fun s : G K Ω => (μ s : ℤ_[l]) ∈ Metric.ball (1 : ℤ_[l]) 1) ?_ hcl s
    · rwa [mem_ball_iff_norm] at h1
    · rintro t ⟨v, B, hv, hB, ht⟩
      rw [mem_ball_iff_norm, hfr v (hne v hv) B hB t ht]
      exact hone _ v.ne_bot (hcop v (hne v hv))
  · obtain ⟨j, hjc, hj, hinj⟩ := exists_conj K hK c
    obtain rfl : s' = j s := hinj (hs.trans (hj s).symm)
    refine congrFun (Continuous.ext_on hD (hμc.mul (hμc.comp hjc)) ((continuous_cycZ K Ω l).pow n) ?_) s
    rintro t ⟨v, B, hv, hB, ht⟩
    obtain ⟨v', B', e, hB', ht'⟩ := hconj c hc t (j t) (hj t) v B hB ht
    have hv' : (l : 𝓞 K) ∉ v'.asIdeal := by
      rw [e, Ideal.mem_map_iff_of_surjective τ τ.surjective]
      rintro ⟨y, hy, hy'⟩
      rw [← map_natCast τ] at hy'
      exact hv (τ.injective hy' ▸ hy)
    have c1 := hcop v (hne v hv)
    have c2 := hcop v' (hne v' hv')
    have c3 := c1.mul_left c2
    show μ t * μ (j t) = cycZ K Ω l t ^ n
    rw [hfr v (hne v hv) B hB t ht, hfr v' (hne v' hv') B' hB' _ ht', ← hmul _ _ v.ne_bot v'.ne_bot c1 c2]
    rw [e, hN] at c3
    apply Units.ext
    rw [e, hN, hpr _ c3, Units.val_pow_eq_pow_val, cycZ_of_isFrob hv hB ht, map_natCast]
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · by_cases hB : B = ⊤
    · rw [((places K Ω l B).2.1 hB).1]
      exact bot_le
    obtain ⟨v, hv⟩ := (places K Ω l B).1 hB
    have hvw : v ≠ w := by
      rintro rfl
      obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := K) hw hv
      apply hx
      have h1 : g • x = x := g.commutes ⟨x, hxK⟩
      rw [← hg]
      conv_lhs => rw [← h1]
      exact ValuationSubring.smul_mem_pointwise_smul_iff
    intro s hs
    rw [MonoidHom.mem_ker]
    refine Units.ext (PadicInt.ext_of_toZModPow.1 fun k => ?_)
    rw [hμ, MonoidHom.mem_ker.1 ((hκ k v hvw B hv).1 hs)]
    simp
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ Ω}

omit [IsAlgClosure ℚ Ω] in
private theorem res_mem (g : G K Ω) : resQ K g ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact g.commutes ⟨x, hx⟩

omit [IsAlgClosure ℚ Ω] in
private theorem val_agree {A B : ValuationSubring Ω} (h : ∀ x ∈ K, x ∈ B ↔ x ∈ A) {x : Ω} (hx : x ∈ K) :
    B.valuation x < 1 ↔ A.valuation x < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', h x hx, h _ (inv_mem hx)]

private theorem algClosure (K : IntermediateField ℚ Ω) : IsAlgClosure K Ω := by
  exact ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩

private theorem conj_of_agree [NumberField K] {A B : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1)
    (h : ∀ x ∈ K, x ∈ B ↔ x ∈ A) : ∃ g : G K Ω, ∀ x, g x ∈ B ↔ x ∈ A := by
  haveI := algClosure K
  have hAT : A ≠ ⊤ := fun hT => ((places K Ω l A).2.1 hT).2 hA
  obtain ⟨v, hv⟩ := (places K Ω l A).1 hAT
  have hBv : IsPlaceOver B v := fun x => (val_agree h (SetLike.coe_mem (x : K))).trans (hv x)
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hv hBv
  refine ⟨σ, fun x => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  show σ⁻¹ (σ x) ∈ A ↔ x ∈ A
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

private theorem differs [NumberField K] {A B B' : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1)
    (hD : Dec (F := ℚ) A ≤ K.fixingSubgroup) (h : ∀ x ∈ K, x ∈ B ↔ x ∈ A) {σ : G ℚ Ω} (hσ : σ ∉ K.fixingSubgroup)
    (hB : ∀ x, σ x ∈ B ↔ x ∈ B') : ∃ x ∈ K, ¬ (x ∈ B' ↔ x ∈ A) := by
  by_contra hne
  push_neg at hne
  obtain ⟨g, hg⟩ := conj_of_agree hA hne
  obtain ⟨g', hg'⟩ := conj_of_agree hA h
  set τ : G ℚ Ω := (resQ K g')⁻¹ * σ * resQ K g with hτ
  have key : ∀ y, τ y ∈ A ↔ y ∈ A := by
    intro y
    have e : g' (τ y) = σ (g y) := by
      show resQ K g' (((resQ K g')⁻¹ * σ * resQ K g) y) = σ (resQ K g y)
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    calc τ y ∈ A ↔ g' (τ y) ∈ B := (hg' _).symm
      _ ↔ σ (g y) ∈ B := by rw [e]
      _ ↔ g y ∈ B' := hB _
      _ ↔ y ∈ A := hg y
  have hτD : τ ∈ Dec (F := ℚ) A := by
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← key]
    show τ (τ⁻¹ x) ∈ A ↔ x ∈ A
    rw [mul_inv_apply]
  have hτK := hD hτD
  apply hσ
  have e2 : σ = resQ K g' * τ * (resQ K g)⁻¹ := by
    rw [hτ]
    group
  rw [e2]
  exact K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem (res_mem g') hτK)
    (K.fixingSubgroup.inv_mem (res_mem g))

private theorem exists_lift [NumberField K] (hK : Module.finrank ℚ K = 2) :
    ∃ (σ : G ℚ Ω) (τ : K ≃+* K), σ ∉ K.fixingSubgroup ∧ IsLift τ σ.toRingEquiv := by
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hc : Nat.card Gal(K/ℚ) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK]
  haveI : Nontrivial Gal(K/ℚ) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; norm_num)
  obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(K/ℚ))
  let σ : G ℚ Ω := τ.liftNormal Ω
  have hlift : ∀ x : K, σ (x : Ω) = (τ x : Ω) := fun x => AlgEquiv.liftNormal_commutes τ Ω x
  refine ⟨σ, τ.toRingEquiv, ?_, fun x => hlift x⟩
  intro hmem
  apply hτ
  ext x
  have h1 := (IntermediateField.mem_fixingSubgroup_iff K σ).mp hmem x x.2
  rw [hlift] at h1
  exact h1

private theorem unit_div_near {a b : ℤ_[l]ˣ} (ha : ‖(a : ℤ_[l]) - 1‖ < 1) (hb : ‖(b : ℤ_[l]) - 1‖ < 1) :
    ‖((a / b : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
  have hb1 : ‖((b⁻¹ : ℤ_[l]ˣ) : ℤ_[l])‖ = 1 := PadicInt.isUnit_iff.mp (Units.isUnit _)
  have e : ((a / b : ℤ_[l]ˣ) : ℤ_[l]) - 1 = ((a : ℤ_[l]) - b) * ((b⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [div_eq_mul_inv, Units.val_mul, sub_mul, Units.mul_inv]
  rw [e, norm_mul, hb1, mul_one]
  have e2 : (a : ℤ_[l]) - b = ((a : ℤ_[l]) - 1) + (1 - (b : ℤ_[l])) := by ring
  rw [e2]
  refine lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt ha ?_)
  rwa [norm_sub_rev]

private theorem exists_open [NumberField K] (f : G K Ω → PadicAlgCl l) (hf : Continuous f) (h1 : f 1 = 1) {n : ℕ} (hn : 0 < n) :
    ∃ U : Subgroup (G K Ω), IsOpen (U : Set (G K Ω)) ∧ ∀ s ∈ U, f s ^ n = 1 → f s = 1 := by
  classical
  haveI := algClosure K
  let F : Set (PadicAlgCl l) := {z | z ^ n = 1 ∧ z ≠ 1}
  have hF : F.Finite := by
    apply (Polynomial.nthRoots n (1 : PadicAlgCl l)).toFinset.finite_toSet.subset
    intro z hz
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hz.1
  have hV : IsOpen (f ⁻¹' Fᶜ) := hF.isClosed.isOpen_compl.preimage hf
  have h1V : (1 : G K Ω) ∈ f ⁻¹' Fᶜ := by
    simp [F, h1]
  set_option synthInstance.maxHeartbeats 200000 in
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1V
    refine ⟨H.toOpenSubgroup.toSubgroup, H.toOpenSubgroup.isOpen, fun s hs hsn => ?_⟩
    by_contra hne
    exact hH hs ⟨hsn, hne⟩

end SlopeTestRemainingChoices

private theorem padicInt_norm_units_mul_sub_one_lt_one {l : ℕ} [Fact l.Prime] {a b : ℤ_[l]ˣ} (ha : ‖(a : ℤ_[l]) - 1‖ < 1)
    (hb : ‖(b : ℤ_[l]) - 1‖ < 1) : ‖((a * b : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
  have e : ((a * b : ℤ_[l]ˣ) : ℤ_[l]) - 1 = ((a : ℤ_[l]) - 1) * b + ((b : ℤ_[l]) - 1) := by
    rw [Units.val_mul]
    ring
  rw [e]
  refine lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt ?_ hb)
  rw [norm_mul]
  calc ‖(a : ℤ_[l]) - 1‖ * ‖(b : ℤ_[l])‖ ≤ ‖(a : ℤ_[l]) - 1‖ * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact ha

theorem UpperTheory.V.Ws.Tw.bt0 :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : IntermediateField ℚ Ω) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup → ∃ (t : G K Ω →* Multiplicative ℤ_[l]) (β : G K Ω →* (PadicAlgCl l)ˣ) (c₁ : Coef l), Continuous t ∧ t.ker ≤ β.ker ∧ Continuous β ∧ (∀ s, (β s : PadicAlgCl l) ∈ c₁.O ∧ ‖(β s : PadicAlgCl l) - 1‖ < 1) ∧ (∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ → t s * t s' = 1) ∧ (∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ → β s * β s' = 1) ∧ (∀ B : ValuationSubring Ω, ¬ B.valuation (l : Ω) < 1 → Ine (F := K) B ≤ t.ker) ∧ ∃ U : Subgroup (G K Ω), IsOpen (U : Set (G K Ω)) ∧ ∀ B : ValuationSubring Ω, (∀ x ∈ K, x ∈ B ↔ x ∈ A) → ∀ s ∈ U ⊓ Ine (F := K) B, (β s : PadicAlgCl l) ^ 2 = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l s : ℤ_[l]) := by
  intro Ω _ _ _ l _ hl K _ _ hK A hA hD
  haveI := algClosure K
  obtain ⟨μ, n, hn, hμc, hμ1, hμconj, hμker⟩ := Tw.muChar Ω l hl K hK A hA hD
  obtain ⟨σ, τ, hσ, hlift⟩ := exists_lift hK
  have hσi : σ⁻¹ ∉ K.fixingSubgroup := fun h => hσ (by simpa using K.fixingSubgroup.inv_mem h)
  have hres : ∀ s, resQ K (conjGal hlift s) = σ⁻¹ * resQ K s * σ⁻¹⁻¹ := by
    intro s
    rw [inv_inv]
    ext x
    rfl
  have hconj : ∀ s, μ s * μ (conjGal hlift s) = cycZ K Ω l s ^ n :=
    fun s => hμconj σ⁻¹ hσi s _ (hres s)
  have hcyc : ∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ →
      cycZ K Ω l s' = cycZ K Ω l s := by
    intro c _ s s' h
    show cycZ ℚ Ω l (resQ K s') = cycZ ℚ Ω l (resQ K s)
    rw [h, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  let π : G K Ω →* ℤ_[l]ˣ :=
    { toFun := fun s => μ s ^ 2 / cycZ K Ω l s ^ n
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_pow]
        exact mul_div_mul_comm _ _ _ _ }
  have hπ : ∀ s, π s = μ s ^ 2 / cycZ K Ω l s ^ n := fun s => rfl
  have hπc : Continuous π := by
    show Continuous (fun s => μ s ^ 2 / cycZ K Ω l s ^ n)
    exact (hμc.pow 2).div' ((continuous_cycZ K Ω l).pow n)
  have hπ1 : ∀ s, ‖((π s : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
    intro s
    rw [hπ, ← hconj s, sq]
    exact unit_div_near (padicInt_norm_units_mul_sub_one_lt_one (hμ1 s) (hμ1 s)) (padicInt_norm_units_mul_sub_one_lt_one (hμ1 s) (hμ1 _))
  have hπconj : ∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ →
      π s * π s' = 1 := by
    intro c hc s s' h
    have e := hμconj c hc s s' h
    rw [hπ, hπ, hcyc c hc s s' h, div_mul_div_comm, div_eq_one]
    calc μ s ^ 2 * μ s' ^ 2 = (μ s * μ s') ^ 2 := (mul_pow _ _ _).symm
      _ = (cycZ K Ω l s ^ n) ^ 2 := by rw [e]
      _ = cycZ K Ω l s ^ n * cycZ K Ω l s ^ n := sq _
  obtain ⟨t, β, c₁, ht, hker, htβ, hβc, hβO, hβpow, hβconj⟩ :=
    Tw.rootChar l hl (G K Ω) π hπc hπ1 (2 * n) (by omega)
  let f : G K Ω → PadicAlgCl l := fun s => (β s : PadicAlgCl l) ^ 2 *
      algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  have hf : Continuous f := by
    have hc : Continuous (fun x : ℤ_[l] => algebraMap ℤ_[l] (PadicAlgCl l) x) := by
      have e : (fun x : ℤ_[l] => algebraMap ℤ_[l] (PadicAlgCl l) x) =
          fun x : ℤ_[l] => algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l]) := by
        funext x
        exact IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) x
      rw [e]
      exact (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
    exact ((Units.continuous_val.comp hβc).pow 2).mul
      (hc.comp (Units.continuous_val.comp ((continuous_cycZ K Ω l).inv)))
  have hf1 : f 1 = 1 := by simp [f]
  obtain ⟨U, hUo, hU⟩ := exists_open f hf hf1 hn
  refine ⟨t, β, c₁, ht, htβ, hβc, hβO, ?_, ?_, ?_, ?_⟩
  · intro c hc s s' h
    have hm : s * s' ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact hπconj c hc s s' h
    rw [← hker] at hm
    rw [← map_mul]
    exact hm
  · intro c hc s s' h
    exact hβconj s s' (hπconj c hc s s' h)
  · intro B hB
    rw [hker]
    intro s hs
    have hdis : ∃ x ∈ K, ¬(x ∈ B ↔ x ∈ A) := by
      by_contra hne
      push_neg at hne
      exact hB ((val_agree hne (natCast_mem K l)).mpr hA)
    have h1 : μ s = 1 := hμker B hdis hs
    have h2 : cycZ K Ω l s = 1 := (places K Ω l B).2.2.2 hB hs
    rw [MonoidHom.mem_ker, hπ, h1, h2, one_pow, one_pow, div_one]
  · refine ⟨U, hUo, fun B hB s hs => ?_⟩
    obtain ⟨hsU, hsI⟩ := Subgroup.mem_inf.mp hs
    have hBB : ∀ x, σ x ∈ B ↔ x ∈ σ⁻¹ • B := by
      intro x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
      rfl
    have hs' := conjGal_mem_Ine hlift (fun x => hBB x) hsI
    have hdis := differs hA hD hB hσ hBB
    have hμs' : μ (conjGal hlift s) = 1 := hμker _ hdis hs'
    have hμs : μ s = cycZ K Ω l s ^ n := by
      have e := hconj s
      rwa [hμs', mul_one] at e
    have hπs : π s = cycZ K Ω l s ^ n := by
      rw [hπ, hμs, div_eq_iff_eq_mul, sq]
    have hβ2n := hβpow s
    rw [hπs] at hβ2n
    have hab : algebraMap ℤ_[l] (PadicAlgCl l) ((cycZ K Ω l s : ℤ_[l])) *
        algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hpow : f s ^ n = 1 := by
      show ((β s : PadicAlgCl l) ^ 2 *
        algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) ^ n = 1
      rw [mul_pow, ← pow_mul, hβ2n, Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hab, one_pow]
    have h1 := hU s hsU hpow
    change (β s : PadicAlgCl l) ^ 2 *
      algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = 1 at h1
    calc (β s : PadicAlgCl l) ^ 2 = (β s : PadicAlgCl l) ^ 2 *
          (algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) *
            algebraMap ℤ_[l] (PadicAlgCl l) ((cycZ K Ω l s : ℤ_[l]))) := by
          rw [mul_comm (algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])), hab,
            mul_one]
      _ = algebraMap ℤ_[l] (PadicAlgCl l) ((cycZ K Ω l s : ℤ_[l])) := by
          rw [← mul_assoc, h1, one_mul]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

