module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointLatticeIffBaseLatticeDecorated

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedIntegralOfSeparatingElement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GalAlgClosureExistsPosPowApplyEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem galAlgClosure_exists_pos_pow_apply_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (σ : G E Ω) (t : Ω), ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t := by
  intro E Ω _ _ _ _ _ σ t
  have hint : IsIntegral E t :=
    ((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic t).isIntegral
  have hmem : ∀ i : ℕ, (σ ^ i) t ∈ (minpoly E t).rootSet Ω := by
    intro i
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    have h := Polynomial.aeval_algHom_apply ((σ ^ i : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) t (minpoly E t)
    rw [minpoly.aeval, map_zero] at h
    exact h
  haveI : Finite ((minpoly E t).rootSet Ω) := ((minpoly E t).rootSet_finite Ω).to_subtype
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => (⟨(σ ^ i) t, hmem i⟩ : (minpoly E t).rootSet Ω))
  have heq' : (σ ^ i) t = (σ ^ j) t := congrArg Subtype.val heq
  have key : ∀ a b : ℕ, a < b → (σ ^ a) t = (σ ^ b) t → ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t := by
    intro a b hab h
    refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
    apply (σ ^ a).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    exact h.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h heq'
  · exact key j i h heq'.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedIntegralOfSeparatingElement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem valuation_le_one_of_valuation_one_sub_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {a : Ω} (ha : A.valuation (1 - a) < 1) : A.valuation a ≤ 1 := by
  have e : a = 1 - (1 - a) := by ring
  rw [e]
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ha.le)
  rw [map_one]

theorem valuation_one_sub_mul_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω}
    (ha : A.valuation (1 - a) < 1) (hb : A.valuation (1 - b) < 1) :
    A.valuation (1 - a * b) < 1 := by
  have e : 1 - a * b = (1 - a) + a * (1 - b) := by ring
  rw [e]
  refine Valuation.map_add_lt _ ha ?_
  rw [map_mul]
  calc A.valuation a * A.valuation (1 - b) ≤ 1 * A.valuation (1 - b) :=
        by gcongr; exact valuation_le_one_of_valuation_one_sub_lt A ha
    _ = A.valuation (1 - b) := one_mul _
    _ < 1 := hb

theorem exists_fixed_of_separating :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (e₀ c : Ω), IsIntegral ℤ e₀ → A.valuation e₀ < A.valuation c → A'.valuation (1 - e₀) < 1 → ∃ e : Ω, IsIntegral ℤ e ∧ σ e = e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  intro E Ω _ _ _ _ _ A A' σ hσ e₀ c hint hA hA'
  obtain ⟨k, hk, hfix⟩ := galAlgClosure_exists_pos_pow_apply_eq E Ω σ e₀
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set f : ℕ → Ω := fun i => (σ ^ i) e₀ with hf
  have hfint : ∀ i, IsIntegral ℤ (f i) := fun i =>
    hint.map ((σ ^ i : Ω ≃ₐ[E] Ω).toRingEquiv.toRingHom.toIntAlgHom)
  have hshift : ∀ i, σ (f i) = f (i + 1) := by
    intro i
    simp only [hf, pow_succ', AlgEquiv.mul_apply]

  have hcong : ∀ i, A'.valuation (1 - f i) < 1 := by
    intro i
    induction i with
    | zero => simpa [hf] using hA'
    | succ i ih =>
      have hy : A'.valuation (f i) ≤ 1 := valuation_le_one_of_valuation_one_sub_lt A' ih
      have hmove := hσ.2 (f i) hy
      have e : 1 - f (i + 1) = (1 - f i) + -(σ (f i) - f i) := by
        rw [← hshift i]; ring
      rw [e]
      refine Valuation.map_add_lt _ ih ?_
      rw [Valuation.map_neg]
      exact hmove
  refine ⟨∏ i ∈ Finset.range (m + 1), f i, ?_, ?_, ?_, ?_⟩
  · exact IsIntegral.prod _ (fun i _ => hfint i)
  · rw [map_prod]
    simp only [hshift]
    rw [Finset.prod_range_succ (fun i => f (i + 1)), Finset.prod_range_succ' f]
    have h0 : f (m + 1) = f 0 := by simpa [hf] using hfix
    rw [h0]
  · rw [Finset.prod_range_succ']
    have hP : IsIntegral ℤ (∏ i ∈ Finset.range m, f (i + 1)) :=
      IsIntegral.prod _ (fun i _ => hfint (i + 1))
    have hPle : A.valuation (∏ i ∈ Finset.range m, f (i + 1)) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hP)
    rw [map_mul]
    calc A.valuation (∏ i ∈ Finset.range m, f (i + 1)) * A.valuation (f 0)
        ≤ 1 * A.valuation (f 0) := by gcongr
      _ = A.valuation e₀ := by simp [hf]
      _ < A.valuation c := hA
  · refine Finset.prod_induction f (fun x => A'.valuation (1 - x) < 1)
      (fun a b ha hb => valuation_one_sub_mul_lt A' ha hb) ?_ (fun i _ => hcong i)
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedIntegralOfSeparatingElementStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertiaFixed_integral_of_separating_element : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (e₀ c : Ω), IsIntegral ℤ e₀ → A.valuation e₀ < A.valuation c → A'.valuation (1 - e₀) < 1 → ∃ e : Ω, IsIntegral ℤ e ∧ σ e = e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  first | exact @GlobalTheory.exists_fixed_of_separating | exact GlobalTheory.exists_fixed_of_separating | (intros; apply GlobalTheory.exists_fixed_of_separating <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerDeepAtOnePlaceUnitAtOther
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowValuationLtOfIntegralAlgClosurePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowValuationLtOfIntegralAlgClosurePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MaxIdealPow

variable {Ω : Type} [Field Ω]

theorem aeval_eq_coeff_zero_add (A : ValuationSubring Ω) (g : ℤ[X]) {y : Ω} (hy : y ∈ A) :
    ∃ w ∈ A, aeval y g = ((g.coeff 0 : ℤ) : Ω) + y * w := by
  obtain ⟨r, hr⟩ := X_dvd_sub_C (p := g)
  have hg : g = C (g.coeff 0) + X * r := by rw [← hr]; ring
  refine ⟨((aeval (⟨y, hy⟩ : A) r : A) : Ω), SetLike.coe_mem _, ?_⟩
  have h1 : aeval y r = ((aeval (⟨y, hy⟩ : A) r : A) : Ω) :=
    aeval_algebraMap_apply Ω (⟨y, hy⟩ : A) r
  conv_lhs => rw [hg]
  rw [map_add (f := _), map_mul, aeval_C, aeval_X, h1]
  simp

theorem exists_nat_of_isPlaceOver (E : Type) [Field E] [NumberField E] [Algebra E Ω]
    (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (hP : IsPlaceOver (F := E) A P) :
    ∃ p : ℕ, p ≠ 0 ∧ p ≠ 1 ∧ ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  let I : Ideal ℤ := P.asIdeal.comap (Int.castRingHom (𝓞 E))
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ a ∣ n := by
    intro n
    have h1 := hP (n : 𝓞 E)
    have h2 : (algebraMap E Ω) (((n : 𝓞 E)) : E) = (n : Ω) := by simp
    rw [h2] at h1
    rw [h1]
    have h3 : (n : 𝓞 E) ∈ P.asIdeal ↔ n ∈ I := by simp [I]
    rw [h3, ha, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨k, rfl⟩; exact Dvd.intro_left k rfl
    · rintro ⟨k, rfl⟩; exact ⟨k, by rw [smul_eq_mul, mul_comm]⟩
  refine ⟨a.natAbs, ?_, ?_, fun n => by rw [hmem n, Int.natAbs_dvd]⟩
  · intro h0
    have ha0 : a = 0 := Int.natAbs_eq_zero.mp h0
    have hN := Ideal.absNorm_mem P.asIdeal
    have hNv : A.valuation (((Ideal.absNorm P.asIdeal : ℕ) : ℤ) : Ω) < 1 := by
      have h1 := (hP ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)).mpr hN
      simpa using h1
    rw [hmem, ha0, zero_dvd_iff] at hNv
    have : Ideal.absNorm P.asIdeal = 0 := by exact_mod_cast hNv
    exact P.ne_bot (Ideal.absNorm_eq_zero_iff.mp this)
  · intro h1
    have : A.valuation ((1 : ℤ) : Ω) < 1 := by
      rw [hmem, ← Int.natAbs_dvd, h1]; simp
    simp at this

end GlobalTheory.MaxIdealPow

namespace GlobalTheory.MaxIdealPow

theorem exists_pow_lt_valuation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → ∀ x c : Ω, IsIntegral ℤ x → IsIntegral ℤ c → c ≠ 0 → A.valuation x < 1 → ∃ k : ℕ, A.valuation x ^ k < A.valuation c := by
  intro E Ω _ _ _ _ _ A P hP x c hx hc hc0 hvx
  obtain ⟨p, hp0, hp1, hpv⟩ := exists_nat_of_isPlaceOver E A P hP
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hvp : A.valuation (p : Ω) < 1 := by
    have := (hpv p).2 dvd_rfl
    simpa using this
  have hvp0 : A.valuation (p : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact_mod_cast hp0
  have hunit : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → A.valuation (n : Ω) = 1 := fun n hn =>
    le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A n))
      (not_lt.1 (fun h => hn ((hpv n).1 h)))
  have hxA : x ∈ A := ReciprocityTheory.Gal.mem_of_isIntegral_int A hx
  have hcA : c ∈ A := ReciprocityTheory.Gal.mem_of_isIntegral_int A hc

  have hstep2 : ∃ s : ℕ, A.valuation x ^ s ≤ A.valuation (p : Ω) := by
    haveI : Fact (1 < p) := ⟨by omega⟩
    let f := minpoly ℤ x
    have hfm : f.Monic := minpoly.monic hx
    let fb := f.map (Int.castRingHom (ZMod p))
    have hfb0 : fb ≠ 0 := (hfm.map _).ne_zero
    obtain ⟨q, hq, hqX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd fb hfb0 0
    simp only [map_zero, sub_zero] at hq hqX
    set s := rootMultiplicity 0 fb
    have hq0 : q.coeff 0 ≠ 0 := fun h => hqX (X_dvd_iff.mpr h)
    obtain ⟨g, hg⟩ := map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective q
    have hker : f - X ^ s * g ∈ RingHom.ker (mapRingHom (Int.castRingHom (ZMod p))) := by
      rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, map_X, hg]
      exact sub_eq_zero.mpr hq
    rw [ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hker
    obtain ⟨h, hh⟩ := hker
    have hev := congrArg (aeval x) hh
    rw [map_sub, map_mul, map_pow, aeval_X, minpoly.aeval, map_mul, aeval_C] at hev
    have hg0 : ¬ (p : ℤ) ∣ g.coeff 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h0; apply hq0; rw [← hg, coeff_map]; simpa using h0
    obtain ⟨w, hwA, hw⟩ := aeval_eq_coeff_zero_add A g hxA
    have hvg : A.valuation (aeval x g) = 1 := by
      rw [hw, Valuation.map_add_eq_of_lt_left, hunit _ hg0]
      rw [hunit _ hg0, Valuation.map_mul]
      calc A.valuation x * A.valuation w ≤ A.valuation x * 1 :=
            mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hwA) |>.trans_eq (mul_one _).symm
        _ = A.valuation x := mul_one _
        _ < 1 := hvx
    have hhA : aeval x h ∈ A := by
      obtain ⟨w', hw'A, hw'⟩ := aeval_eq_coeff_zero_add A h hxA
      rw [hw']; exact add_mem (intCast_mem A _) (mul_mem hxA hw'A)
    refine ⟨s, ?_⟩
    have hev2 : x ^ s * aeval x g = -((algebraMap ℤ Ω p) * aeval x h) := by
      rw [← hev]; ring
    have := congrArg A.valuation hev2
    rw [Valuation.map_neg, Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hvg,
      mul_one] at this
    rw [this]
    have hp' : (algebraMap ℤ Ω (p : ℤ)) = (p : Ω) := by simp
    rw [hp']
    calc A.valuation (p : Ω) * A.valuation (aeval x h) ≤ A.valuation (p : Ω) * 1 :=
          mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hhA) |>.trans_eq (mul_one _).symm
      _ = A.valuation (p : Ω) := mul_one _

  have hstep3 : ∃ t : ℕ, A.valuation (p : Ω) ^ t ≤ A.valuation c := by
    let f := minpoly ℤ c
    have hf0 : f ≠ 0 := (minpoly.monic hc).ne_zero
    obtain ⟨f₁, hf, hfX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
    simp only [map_zero, sub_zero] at hf hfX
    have ha0 : f₁.coeff 0 ≠ 0 := fun h => hfX (X_dvd_iff.mpr h)
    have hev : aeval c f₁ = 0 := by
      have h1 := minpoly.aeval ℤ c
      change aeval c f = 0 at h1
      rw [hf, map_mul, map_pow, aeval_X] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc0)
    obtain ⟨w, hwA, hw⟩ := aeval_eq_coeff_zero_add A f₁ hcA
    rw [hev] at hw
    have hle : A.valuation ((f₁.coeff 0 : ℤ) : Ω) ≤ A.valuation c := by
      have he : ((f₁.coeff 0 : ℤ) : Ω) = -(c * w) := by linear_combination -hw
      rw [he, Valuation.map_neg, Valuation.map_mul]
      calc A.valuation c * A.valuation w ≤ A.valuation c * 1 :=
            mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hwA) |>.trans_eq (mul_one _).symm
        _ = A.valuation c := mul_one _
    have hn0 : (f₁.coeff 0).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha0
    obtain ⟨t, u, hu, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp1
    refine ⟨t, le_trans (le_of_eq ?_) hle⟩
    have habs : A.valuation ((f₁.coeff 0 : ℤ) : Ω) = A.valuation (((f₁.coeff 0).natAbs : ℤ) : Ω) := by
      rcases Int.natAbs_eq (f₁.coeff 0) with h | h
      · rw [← h]
      · conv_lhs => rw [h]
        rw [Int.cast_neg, Valuation.map_neg]
    rw [habs, hfac]
    have hu1 : A.valuation ((u : ℤ) : Ω) = 1 := hunit u (by exact_mod_cast hu)
    push_cast
    rw [Valuation.map_mul, Valuation.map_pow]
    push_cast at hu1
    rw [hu1, mul_one]
  obtain ⟨s, hs⟩ := hstep2
  obtain ⟨t, ht⟩ := hstep3
  refine ⟨s * (t + 1), ?_⟩
  calc A.valuation x ^ (s * (t + 1)) = (A.valuation x ^ s) ^ (t + 1) := pow_mul _ _ _
    _ ≤ A.valuation (p : Ω) ^ (t + 1) := pow_le_pow_left₀ zero_le' hs _
    _ = A.valuation (p : Ω) ^ t * A.valuation (p : Ω) := pow_succ _ _
    _ < A.valuation (p : Ω) ^ t * 1 :=
        mul_lt_mul_of_pos_left hvp (zero_lt_iff.mpr (pow_ne_zero _ hvp0))
    _ = A.valuation (p : Ω) ^ t := mul_one _
    _ ≤ A.valuation c := ht

end GlobalTheory.MaxIdealPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowValuationLtOfIntegralAlgClosurePlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_valuation_lt_of_integral_algClosure_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → ∀ x c : Ω, IsIntegral ℤ x → IsIntegral ℤ c → c ≠ 0 → A.valuation x < 1 → ∃ k : ℕ, A.valuation x ^ k < A.valuation c := by
  first | exact @GlobalTheory.MaxIdealPow.exists_pow_lt_valuation | exact GlobalTheory.MaxIdealPow.exists_pow_lt_valuation | (intros; apply GlobalTheory.MaxIdealPow.exists_pow_lt_valuation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerDeepAtOnePlaceUnitAtOther
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TwoPlaces

theorem exists_deep_one_sub :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω)
      (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → A ≠ A' →
      ∀ c : Ω, IsIntegral ℤ c → c ≠ 0 →
        ∃ e : Ω, IsIntegral ℤ e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  intro E Ω _ _ _ _ _ A A' P hA hA' hne c hc hc0
  have hQ : (primeBelow (F := E) A).under (𝓞 E) = P.asIdeal := under_primeBelow hA
  have hQ' : (primeBelow (F := E) A').under (𝓞 E) = P.asIdeal := under_primeBelow hA'
  haveI : (primeBelow (F := E) A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) _
      (by change (Ideal.under (𝓞 E) (primeBelow (F := E) A)).IsMaximal; rw [hQ]; exact P.isMaximal)
  haveI : (primeBelow (F := E) A').IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) _
      (by change (Ideal.under (𝓞 E) (primeBelow (F := E) A')).IsMaximal; rw [hQ']; exact P.isMaximal)
  have hQne : primeBelow (F := E) A ≠ primeBelow (F := E) A' := by
    intro h
    apply hne
    refine eq_of_valuation_lt_one_iff E fun b hb => ?_
    have hb' : IsIntegral (𝓞 E) b := hb.tower_top
    have := congrArg (fun I : Ideal (IntCl E Ω) => (⟨b, hb'⟩ : IntCl E Ω) ∈ I) h
    simpa [mem_primeBelow] using this
  have hnle : ¬ primeBelow (F := E) A ≤ primeBelow (F := E) A' := fun h =>
    hQne (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) h)
  obtain ⟨x, hxQ, hxQ'⟩ := SetLike.not_le_iff_exists.mp hnle
  rw [mem_primeBelow] at hxQ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_pow_valuation_lt_of_integral_algClosure_place E Ω A P hA (x : Ω) c (isIntegral_int_of_isIntegral x.2) hc hc0 hxQ
  have hxk : x ^ k ∉ primeBelow (F := E) A' := fun h => hxQ' (Ideal.IsPrime.mem_of_pow_mem inferInstance k h)
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv inferInstance hxk
  refine ⟨((y * x ^ k : IntCl E Ω) : Ω), isIntegral_int_of_isIntegral (y * x ^ k).2, ?_, ?_⟩
  · rw [MulMemClass.coe_mul, Valuation.map_mul, SubmonoidClass.coe_pow, Valuation.map_pow]
    calc A.valuation (y : Ω) * A.valuation (x : Ω) ^ k ≤ 1 * A.valuation (x : Ω) ^ k :=
          mul_le_mul_left (valuation_le_one_intCl A y) _
      _ < A.valuation c := by rw [one_mul]; exact hk
  · have e1 : (1 : Ω) - ((y * x ^ k : IntCl E Ω) : Ω) = (i : Ω) := by
      have := congrArg (fun z : IntCl E Ω => (z : Ω)) hyi
      simp only [AddMemClass.coe_add, OneMemClass.coe_one] at this
      rw [← this]; ring
    rw [e1]
    exact hi

end GlobalTheory.TwoPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerDeepAtOnePlaceUnitAtOtherStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_deep_at_one_place_unit_at_other : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → A ≠ A' → ∀ c : Ω, IsIntegral ℤ c → c ≠ 0 → ∃ e : Ω, IsIntegral ℤ e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  first | exact @GlobalTheory.TwoPlaces.exists_deep_one_sub | exact GlobalTheory.TwoPlaces.exists_deep_one_sub | (intros; apply GlobalTheory.TwoPlaces.exists_deep_one_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedRootsPerturbedPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedRootsPerturbedPolynomial
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem eq_of_perturbed_pow_sub_one {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (y z u : R) (m : ℕ) (h : Polynomial ℤ)
    (hy : y ^ m - 1 = u * Polynomial.aeval y h) (hz : z ^ m - 1 = u * Polynomial.aeval z h)
    (hu : u ∈ IsLocalRing.maximalIdeal R) (hzy : z - y ∈ IsLocalRing.maximalIdeal R)
    (hm : (m : R) ∉ IsLocalRing.maximalIdeal R) : z = y := by
  by_contra hne
  have hne' : z - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨k, hk⟩ : z - y ∣ Polynomial.aeval z h - Polynomial.aeval y h := by
    have := Polynomial.sub_dvd_eval_sub z y (h.map (algebraMap ℤ R))
    simpa only [Polynomial.eval_map_algebraMap] using this
  have hS := Commute.geom_sum₂_mul (Commute.all z y) m
  have hS' : (∑ i ∈ Finset.range m, z ^ i * y ^ (m - 1 - i)) = u * k := by
    apply mul_right_cancel₀ hne'
    rw [hS]
    linear_combination hz - hy + u * hk
  have hu0 : IsLocalRing.residue R u = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hu
  have hzy0 : IsLocalRing.residue R z = IsLocalRing.residue R y := by
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hzy
    rwa [map_sub, sub_eq_zero] at this
  have hm0 : (m : IsLocalRing.ResidueField R) ≠ 0 := by
    intro h0
    apply hm
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, h0]
  have hmpos : m ≠ 0 := by
    rintro rfl
    simp at hm0
  have hy1 : (IsLocalRing.residue R y) ^ m = 1 := by
    have := congrArg (IsLocalRing.residue R) hy
    rwa [map_sub, map_mul, hu0, zero_mul, map_pow, map_one, sub_eq_zero] at this
  have hy0 : IsLocalRing.residue R y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hmpos] at hy1
    exact zero_ne_one hy1
  have := congrArg (IsLocalRing.residue R) hS'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, hu0, zero_mul, hzy0] at this
  rw [geom_sum₂_self] at this
  exact mul_ne_zero hm0 (pow_ne_zero _ hy0) this

theorem exists_roots_fixed_of_mem_Ine (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A' : ValuationSubring Ω) (σ : G E Ω)
    (hσ : σ ∈ Ine (F := E) A') (b e : Ω) (m : ℕ) (f : Polynomial ℤ) (he : IsIntegral ℤ e)
    (hσe : σ e = e) (hv : A'.valuation (1 - e) < 1) (hm : A'.valuation (m : Ω) = 1)
    (hf : f.Monic) (hfm : f.natDegree = m) (hb : Polynomial.aeval b f = 0) :
    ∃ ys : Multiset Ω, Multiset.card ys = m ∧ (∀ y ∈ ys, IsIntegral ℤ y ∧ σ y = y) ∧
      e * (b ^ m - 1) = (ys.map (fun y => b - y)).prod := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  set h : Polynomial ℤ := X ^ m - C 1 - f with hh
  have hdeg : h.degree < (m : WithBot ℕ) := by
    have h1 : (X ^ m - C 1 : Polynomial ℤ).Monic := Polynomial.monic_X_pow_sub_C 1 hm0
    have h2 : (X ^ m - C 1 : Polynomial ℤ).degree = m :=
      Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hm0) 1
    have h3 : f.degree = m := by rw [Polynomial.degree_eq_natDegree hf.ne_zero, hfm]
    rw [← h2]
    exact Polynomial.degree_sub_lt (h2.trans h3.symm) h1.ne_zero
      (by rw [h1.leadingCoeff, hf.leadingCoeff])
  let R := integralClosure ℤ Ω
  let e0 : R := ⟨e, he⟩
  let g0 : Polynomial R := f.map (algebraMap ℤ R) + C e0 * h.map (algebraMap ℤ R)
  have hf0 : (f.map (algebraMap ℤ R)).Monic := hf.map _
  have hf0d : (f.map (algebraMap ℤ R)).degree = m := by
    rw [hf.degree_map, Polynomial.degree_eq_natDegree hf.ne_zero, hfm]
  have hlt : (C e0 * h.map (algebraMap ℤ R)).degree < (f.map (algebraMap ℤ R)).degree := by
    rw [hf0d, ← Polynomial.smul_eq_C_mul]
    exact lt_of_le_of_lt ((Polynomial.degree_smul_le _ _).trans Polynomial.degree_map_le) hdeg
  have hg0 : g0.Monic := hf0.add_of_left hlt
  have hg0d : g0.degree = m := by
    rw [← hf0d]; exact Polynomial.degree_add_eq_left_of_degree_lt hlt
  have hev : ∀ y : Ω, Polynomial.aeval y g0 = Polynomial.aeval y f + e * Polynomial.aeval y h := by
    intro y
    simp only [g0, map_add (f := _), map_mul, Polynomial.aeval_map_algebraMap, Polynomial.aeval_C]
    rfl
  have hhev : ∀ y : Ω, Polynomial.aeval y h = y ^ m - 1 - Polynomial.aeval y f := by
    intro y
    simp [hh]
  let g : Polynomial Ω := g0.map (algebraMap R Ω)
  have hg : g.Monic := hg0.map _
  have hgd : g.natDegree = m := by
    rw [hg0.natDegree_map, Polynomial.natDegree_eq_of_degree_eq_some hg0d]
  have hcard : Multiset.card g.roots = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨g.roots, hcard.trans hgd, ?_, ?_⟩
  · intro y hy
    have hy0 : Polynomial.aeval y g0 = 0 := by
      have := (Polynomial.mem_roots hg.ne_zero).mp hy
      rwa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at this
    have hyint : IsIntegral ℤ y := by
      have : IsIntegral R y := ⟨g0, hg0, hy0⟩
      exact isIntegral_trans y this
    refine ⟨hyint, ?_⟩
    have hyA : y ∈ A' := mem_of_isIntegral_int A' hyint
    have hσ' := mem_Ine.mp hσ
    have hzA : σ y ∈ A' := (apply_mem_iff_of_mem_Dec hσ'.1 y).mpr hyA
    have huA : 1 - e ∈ A' := (A'.valuation_le_one_iff _).mp hv.le
    have e1 : y ^ m - 1 = (1 - e) * Polynomial.aeval y h := by
      rw [hev] at hy0
      linear_combination hy0 - hhev y
    have e2 : (σ y) ^ m - 1 = (1 - e) * Polynomial.aeval (σ y) h := by
      have := congrArg σ e1
      rw [map_sub, map_pow, map_one, map_mul, map_sub, map_one, hσe] at this
      rw [this]
      congr 1
      exact (Polynomial.aeval_algHom_apply (σ : Ω →+* Ω).toIntAlgHom y h).symm
    have hae : ∀ x : A', ((Polynomial.aeval x h : A') : Ω) = Polynomial.aeval (x : Ω) h :=
      fun x => (Polynomial.aeval_algHom_apply A'.subtype.toIntAlgHom x h).symm
    have := eq_of_perturbed_pow_sub_one (R := A') ⟨y, hyA⟩ ⟨σ y, hzA⟩ ⟨1 - e, huA⟩ m h
      (Subtype.ext (by simpa [hae] using e1)) (Subtype.ext (by simpa [hae] using e2))
      ((A'.valuation_lt_one_iff _).mpr hv)
      ((A'.valuation_lt_one_iff _).mpr (hσ'.2 y ((A'.valuation_le_one_iff _).mpr hyA)))
      (fun hh' => by
        have := (A'.valuation_lt_one_iff _).mp hh'
        rw [show ((m : A') : Ω) = m from by simp, hm] at this
        exact lt_irrefl _ this)
    exact congrArg Subtype.val this
  · have := congrArg (Polynomial.eval b)
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hg hcard)
    rw [Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_map_algebraMap, hev,
      hhev, hb] at this
    simp only [Function.comp_def, eval_sub, eval_X, eval_C] at this
    rw [this]; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedRootsPerturbedPolynomialStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_fixed_roots_perturbed_polynomial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (b e : Ω) (m : ℕ) (f : Polynomial ℤ), IsIntegral ℤ e → σ e = e → A'.valuation (1 - e) < 1 → A'.valuation (m : Ω) = 1 → f.Monic → f.natDegree = m → Polynomial.aeval b f = 0 → ∃ ys : Multiset Ω, Multiset.card ys = m ∧ (∀ y ∈ ys, IsIntegral ℤ y ∧ σ y = y) ∧ e * (b ^ m - 1) = (ys.map (fun y => b - y)).prod := by
  first | exact @GlobalTheory.exists_roots_fixed_of_mem_Ine | exact GlobalTheory.exists_roots_fixed_of_mem_Ine | (intros; apply GlobalTheory.exists_roots_fixed_of_mem_Ine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.InertiaTwoPlaces

open Polynomial

theorem fix_of_fix_integral {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (h : ∀ b : Ω, IsIntegral ℤ b → σ b = b) : σ = 1 := by
  ext x
  obtain ⟨s, t, hs, ht, hs1, e⟩ := ReciprocityTheory.Gal.exists_den E (⊤ : ValuationSubring Ω) (x := x)
    ((ValuationSubring.valuation_le_one_iff _ _).mpr trivial)
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have h2 : σ s * σ x = σ t := by rw [← map_mul, e]
  rw [h s hs, h t ht, ← e] at h2
  exact mul_left_cancel₀ hs0 h2

theorem eq_of_mem_Ine_of_mem_Ine : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)),
    IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A,
    σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  intro E Ω _ _ _ _ _ A A' P hA hA' σ hσ hσ' hne
  by_contra hAA
  apply hne
  apply fix_of_fix_integral
  intro b hb
  by_contra hD
  have hD0 : σ b - b ≠ 0 := sub_ne_zero.mpr hD
  set f0 := minpoly ℤ b with hf0
  have hf0m : f0.Monic := minpoly.monic hb
  have hf0b : Polynomial.aeval b f0 = 0 := minpoly.aeval ℤ b
  set d := f0.natDegree with hd
  have hnat : ∀ n : ℕ, A'.valuation (n : Ω) ≤ 1 := fun n => ReciprocityTheory.Gal.valuation_natCast_le_one A' n
  obtain ⟨m, hdm, hmu⟩ : ∃ m : ℕ, d ≤ m ∧ A'.valuation (m : Ω) = 1 := by
    by_cases h1 : A'.valuation (d : Ω) = 1
    · exact ⟨d, le_rfl, h1⟩
    refine ⟨d + 1, Nat.le_succ d, ?_⟩
    by_contra h2
    have l1 : A'.valuation (d : Ω) < 1 := lt_of_le_of_ne (hnat d) h1
    have l2 : A'.valuation ((d + 1 : ℕ) : Ω) < 1 := lt_of_le_of_ne (hnat _) h2
    have : A'.valuation (((d + 1 : ℕ) : Ω) - (d : Ω)) < 1 := by
      rw [sub_eq_add_neg]
      exact Valuation.map_add_lt _ l2 (by rw [Valuation.map_neg]; exact l1)
    push_cast at this
    simp at this
  set f1 : Polynomial ℤ := Polynomial.X ^ (m - d) * f0 with hf1
  have hf1m : f1.Monic := (Polynomial.monic_X_pow _).mul hf0m
  have hf1d : f1.natDegree = m := by
    rw [hf1, (Polynomial.monic_X_pow _).natDegree_mul hf0m, Polynomial.natDegree_X_pow, ← hd]
    omega
  have hf1b : Polynomial.aeval b f1 = 0 := by simp [hf1, hf0b]
  have hσA : σ ∈ Dec (F := E) A := Ine_le_Dec A hσ
  have hbD : IsIntegral ℤ (σ b - b) :=
    (hb.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)).sub hb
  have hc : IsIntegral ℤ ((σ b - b) ^ m) := hbD.pow m
  have hc0 : (σ b - b) ^ m ≠ 0 := pow_ne_zero _ hD0
  obtain ⟨e0, he0i, he0A, he0A'⟩ := GlobalTheory.T.exists_integer_deep_at_one_place_unit_at_other E Ω A A' P hA hA' (Ne.symm hAA) _ hc hc0
  obtain ⟨e, hei, hef, heA, heA'⟩ := GlobalTheory.T.exists_inertiaFixed_integral_of_separating_element E Ω A A' σ hσ' e0 _ he0i he0A he0A'
  obtain ⟨ys, hcard, hys, hprod⟩ := GlobalTheory.T.exists_inertia_fixed_roots_perturbed_polynomial E Ω A' σ hσ' b e m f1 hei hef heA' hmu hf1m hf1d hf1b
  have hbm : A.valuation (b ^ m - 1) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (ReciprocityTheory.Gal.mem_of_isIntegral_int A ((hb.pow m).sub isIntegral_one))
  have h1 : A.valuation (e * (b ^ m - 1)) < A.valuation (σ b - b) ^ m := by
    rw [Valuation.map_mul, ← Valuation.map_pow]
    calc A.valuation e * A.valuation (b ^ m - 1) ≤ A.valuation e * 1 := mul_le_mul_of_nonneg_left hbm zero_le'
      _ = A.valuation e := mul_one _
      _ < _ := heA
  have h2 : A.valuation (σ b - b) ^ m ≤ A.valuation ((ys.map (fun y => b - y)).prod) := by
    rw [map_multiset_prod, Multiset.map_map, ← hcard]
    rw [← Multiset.card_map (fun y => A.valuation (b - y)) ys]
    apply Multiset.pow_card_le_prod
    intro z hz
    rw [Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hyf := (hys y hy).2
    have e1 : σ b - b = σ (b - y) - (b - y) := by rw [map_sub, hyf]; ring
    rw [e1, sub_eq_add_neg]
    refine (Valuation.map_add _ _ _).trans ?_
    rw [Valuation.map_neg, GlobalTheory.T.iwasawaDecomposition_fact E Ω A σ hσA, max_self]
  rw [← hprod] at h2
  exact absurd h2 (not_le.mpr h1)

end GlobalTheory.InertiaTwoPlaces
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeetStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_two_places_over_same_prime_trivial_meet : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A, σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  first | exact @GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | exact GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | (intros; apply GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine <;> assumption)
end
