module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.FreshChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SatSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SplitIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.IndexComap
namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem indexComap : IndexComap := by
  intro Γ Γ' _ _ f H H' hc hle hp ⟨τ, hτ, hτ'⟩
  have hN : H'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H' :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have h2 : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [h2]
    exact H'.mul_mem h1 hn
  rw [Subgroup.relIndex_comap]
  set J := (H.comap f).map f with hJ
  have hJH : J ≤ H := Subgroup.map_comap_le _ _
  have hmul : H'.relIndex (H' ⊔ J) * (H' ⊔ J).relIndex H = H'.relIndex H :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hle hJH)
  rw [Subgroup.relIndex_sup_left] at hmul
  have hne : H'.relIndex J ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hτ' (h ⟨τ, hτ, rfl⟩)
  exact (hp.eq_one_or_self_of_dvd _ ⟨_, hmul.symm⟩).resolve_left hne

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.RootMod
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem natCast_mem_asIdeal_of_normV_eq {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) (p : ℕ)
    (hN : normV u = p) : ((p : 𝓞 F)) ∈ u.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hN]
  unfold Formalism.ConjugateSelfDual.normV
  simpa using card_nsmul_eq_zero' (G := 𝓞 F ⧸ u.asIdeal) (x := 1)

private theorem valuation_le_one_of_pow_eq_one' {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (y : Ω) (n : ℕ) (hn : 0 < n)
    (h : y ^ n = 1) : A.valuation y ≤ 1 := by
  have h1 : A.valuation y ^ n = 1 := by rw [← map_pow, h, map_one]
  exact (pow_le_one_iff hn.ne').mp h1.le

private theorem not_valuation_natCast_lt_one_of_prime_not_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p n : ℕ) (hp : Nat.Prime p)
    (hpn : ¬ p ∣ n) (hvp : A.valuation (p : Ω) < 1) : ¬ A.valuation (n : Ω) < 1 := by
  intro hvn
  have hc : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
  have hb : ((Nat.gcd p n : ℤ)) = p * Nat.gcdA p n + n * Nat.gcdB p n := Nat.gcd_eq_gcd_ab p n
  rw [hc.gcd_eq_one] at hb
  have hb' : (1 : Ω) = (p : Ω) * (Nat.gcdA p n : Ω) + (n : Ω) * (Nat.gcdB p n : Ω) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : Ω)) hb
  have hA : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have h1 : A.valuation ((p : Ω) * (Nat.gcdA p n : Ω)) < 1 := by
    rw [map_mul]; exact mul_lt_one_of_lt_of_le hvp (hA _)
  have h2 : A.valuation ((n : Ω) * (Nat.gcdB p n : Ω)) < 1 := by
    rw [map_mul]; exact mul_lt_one_of_lt_of_le hvn (hA _)
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [← hb', map_one] at h3
  exact lt_irrefl _ h3

open Polynomial in
private theorem exists_zmod_castHom_eq_of_pow_char_eq_self {K : Type} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (z : K)
    (hz : z ^ p = z) : ∃ k : ZMod p, (ZMod.castHom (dvd_refl p) K) k = z := by
  set f := ZMod.castHom (dvd_refl p) K
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rwa [hcard] at this
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]; exact_mod_cast hp.out.one_lt
  have hdeg : (X ^ p - X : (ZMod p)[X]).roots.card = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, Polynomial.natDegree_X_pow_sub_X hp.out.one_lt]
    simp [hcard]
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hdeg
  have hev := congrArg (fun P => (P.map f).eval z) hprod
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_pow, eval_multiset_prod, eval_sub, eval_X, eval_C,
    eval_pow, hz, sub_self] at hev
  obtain ⟨w, -, hw0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hev)
  exact ⟨w, (sub_eq_zero.mp hw0).symm⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.rootMod :
    RootMod := by
  intro F Ω _ _ _ _ _ A u hu p hp hN y n hn hfix
  obtain ⟨σ, hσD, hσ⟩ := exists_isFrob hu
  have hfy : σ y = y := hfix σ hσD
  have hvp : A.valuation (p : Ω) < 1 := by
    have h := (hu (p : 𝓞 F)).mpr (natCast_mem_asIdeal_of_normV_eq u p hN)
    simpa using h
  refine ⟨fun m hm => ?_, fun hprim hpn => ?_⟩
  · have hvy : A.valuation y ≤ 1 := by
      have h1 : A.valuation y ^ n ≤ 1 := by
        rw [← map_pow, hm]; exact valuation_natCast_le_one A m
      exact (pow_le_one_iff hn.ne').mp h1
    have hyA : y ∈ A := (A.valuation_le_one_iff y).mp hvy
    set yA : A := ⟨y, hyA⟩
    set r := IsLocalRing.residue A
    have hp0 : ((p : IsLocalRing.ResidueField A)) = 0 := by
      rw [← map_natCast r, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      simpa using hvp
    have hch : ringChar (IsLocalRing.ResidueField A) = p :=
      (hp.eq_one_or_self_of_dvd _ (ringChar.dvd hp0)).resolve_left (CharP.ringChar_ne_one)
    haveI := ringChar.of_eq hch
    haveI : Fact p.Prime := ⟨hp⟩
    have hlt := hσ y hvy
    rw [hfy, hN] at hlt
    have hry : r yA ^ p = r yA := by
      have h0 : r (yA - yA ^ p) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
        simpa using hlt
      rw [map_sub, map_pow, sub_eq_zero] at h0
      exact h0.symm
    obtain ⟨k, hk⟩ := exists_zmod_castHom_eq_of_pow_char_eq_self p (r yA) hry
    have hyn : yA ^ n = (m : A) := by
      apply Subtype.ext
      simpa using hm
    have hkm : (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) (k ^ n) =
        (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) (m : ZMod p) := by
      rw [map_pow, hk, ← map_pow, hyn, map_natCast, map_natCast]
    exact ⟨k, (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)).injective hkm⟩
  · have hyn : y ^ n = 1 := hprim.pow_eq_one
    have hvy := valuation_le_one_of_pow_eq_one' A y n hn hyn
    have hlt := hσ y hvy
    rw [hfy, hN] at hlt
    have hvn := not_valuation_natCast_lt_one_of_prime_not_dvd A p n hp hpn hvp
    have hyp : y = y ^ p := by
      refine eq_of_pow_eq_one A hvn hyn ?_ hlt
      rw [← pow_mul, mul_comm, pow_mul, hyn, one_pow]
    have hy0 : y ≠ 0 := hprim.ne_zero hn.ne'
    have hp1 : y ^ (p - 1) = 1 := by
      have h2 : y ^ (p - 1) * y = 1 * y := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hp.one_le]
        exact hyp.symm
      exact mul_right_cancel₀ hy0 h2
    exact hprim.dvd_of_pow_eq_one _ hp1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.DecPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameQuot

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem decPow : DecPow := by
  intro F Ω _ _ _ _ _ A t hA p hp hpt ζ hζ
  have hN : ¬ A.valuation (p : Ω) < 1 := by
    simpa using not_valuation_lt_one_of_isPlaceOver hpt hA 1
  have hz1 : ζ ^ p = 1 := hζ.pow_eq_one
  have hint : ζ ∈ IntCl F Ω :=
    IsIntegral.of_pow hp.pos (by rw [hz1]; exact isIntegral_one)
  have hv : A.valuation ζ ≤ 1 := by
    have h1 : A.valuation ζ ^ p = 1 := by rw [← map_pow, hz1, map_one]
    exact ((pow_eq_one_iff.1 h1).resolve_right hp.ne_zero).le
  refine ⟨fun g hg => ?_, fun τ hτ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_pow_cong hA hg {⟨ζ, hint⟩}
    refine ⟨i, eq_of_pow_eq_one A hN ?_ ?_ (hi ⟨ζ, hint⟩ (Finset.mem_singleton_self _))⟩
    · rw [← map_pow, hz1, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
  · exact eq_of_pow_eq_one A hN (by rw [← map_pow, hz1, map_one]) hz1 ((mem_Ine.1 hτ).2 ζ hv)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.TwoPrimes
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_conj (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic ℚ Ω] :
    ∃ (j : Ω →+* ℂ) (c : Ω ≃+* Ω), ∀ z, j (c z) = starRingEnd ℂ (j z) := by
  haveI : Normal ℚ Ω := normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  haveI : IsGalois ℚ Ω := ⟨⟩
  let j : Ω →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Ω) : Ω →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j
    (ComplexEmbedding.conjugate j) (Subsingleton.elim _ _)
  exact ⟨j, σ.symm.toRingEquiv, fun x => DFunLike.congr_fun hσ x⟩

private theorem conj_of_sq {w : ℂ} {q : ℕ} (hq : 0 < q) (h : w ^ 2 = (q : ℂ)) :
    starRingEnd ℂ w = w :=
  _root_.UpperTheory.Reformulated.B.Qh56.conj_of_sq hq h

private theorem sq_fix {E Y Ω : Type} [Field E] [Field Y] [Field Ω] [Algebra E Y] [Algebra Y Ω]
    (δ : Y) (q : ℕ) (hq : δ ^ 2 = (q : Y))
    (hspan : ∀ y : Y, ∃ a b : E, y = algebraMap E Y a + algebraMap E Y b * δ)
    (g : Ω ≃+* Ω) (hδ : g (algebraMap Y Ω δ) = -algebraMap Y Ω δ)
    (hE : ∀ (j : E →+* Ω) (x : E), g (g (j x)) = j x) (j : Y →+* Ω) (y : Y) :
    g (g (j y)) = j y := by
  have h2 : (j δ) ^ 2 = (algebraMap Y Ω δ) ^ 2 := by
    rw [← map_pow, ← map_pow, hq, map_natCast, map_natCast]
  have hfix : g (g (j δ)) = j δ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp [hδ]
  obtain ⟨a, b, rfl⟩ := hspan y
  have ha := hE (j.comp (algebraMap E Y)) a
  have hb := hE (j.comp (algebraMap E Y)) b
  simp only [RingHom.comp_apply] at ha hb
  simp only [map_add (f := _), map_mul, ha, hb, hfix]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.twoPrimes :
    PrimeWith → TwoPrimes := by
  intro PW E Y Ω _ _ _ _ _ _ _ _ δ hδ M B hM
  obtain ⟨⟨q, hq0, hq⟩, hspan, s, hsE, hsδ⟩ := hδ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Y
  haveI : Algebra.IsAlgebraic Y Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ Y Ω
  obtain ⟨j0, c, hc⟩ := exists_conj Ω
  have hδ2 : (algebraMap Y Ω δ) ^ 2 = (q : Ω) := by rw [← map_pow, hq, map_natCast]
  have hcc : ∀ z, c (c z) = z := fun z => j0.injective (by rw [hc, hc, Complex.conj_conj])
  have hcδ : c (algebraMap Y Ω δ) = algebraMap Y Ω δ := j0.injective (by
    rw [hc]
    exact conj_of_sq hq0 (by rw [← map_pow, hδ2, map_natCast]))
  have hcroot : ∀ ξ : Ω, ξ ^ M = 1 → c ξ = ξ⁻¹ := fun ξ h => j0.injective (by
    have h1 : (j0 ξ) ^ M = 1 := by rw [← map_pow, h, map_one]
    rw [hc, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hM.ne')])
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hsc : ∀ (j : E →+* Ω) (x : E), s (c (j x)) = c (j x) :=
    fun j x => hsE ((c : Ω →+* Ω).comp j) x
  have hsinv : ∀ (j : E →+* Ω) (x : E), s.symm (j x) = j x := fun j x => by
    rw [RingEquiv.symm_apply_eq, hsE]
  have hsinvδ : s.symm (algebraMap Y Ω δ) = -algebraMap Y Ω δ := by
    rw [RingEquiv.symm_apply_eq, map_neg, hsδ, neg_neg]
  have h1δ : (s.trans c) (algebraMap Y Ω δ) = -algebraMap Y Ω δ := by
    show c (s _) = _
    rw [hsδ, map_neg, hcδ]
  have h11 : ∀ (j : Y →+* Ω) (y : Y), (s.trans c) ((s.trans c) (j y)) = j y :=
    sq_fix (E := E) δ q hq hspan (s.trans c) h1δ (fun j x => by
      show c (s (c (s (j x)))) = j x
      rw [hsE j x, hsc j x, hcc])
  have h22 : ∀ (j : Y →+* Ω) (y : Y), s.symm (s.symm (j y)) = j y :=
    sq_fix (E := E) δ q hq hspan s.symm hsinvδ (fun j x => by rw [hsinv, hsinv])
  obtain ⟨p₁, hp₁, hB, hz₁, hA₁⟩ := PW Y Ω (algebraMap Y Ω δ) q hq0 hδ2 (s.trans c) h1δ h11 M ζ hM hζ B
  obtain ⟨p₂, hp₂, hB₂, hz₂, hA₂⟩ := PW Y Ω (algebraMap Y Ω δ) q hq0 hδ2 s.symm hsinvδ h22 M ζ hM hζ p₁
  have hsζ : (s ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have e1 : (s ζ)⁻¹ = ζ ^ p₁ := by rw [← hcroot _ hsζ]; exact hz₁
  have e2 : ζ = (s ζ) ^ p₂ := by
    rw [← map_pow, ← hz₂, RingEquiv.apply_symm_apply]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hdvd : M ∣ p₁ * p₂ + 1 := by
    refine hζ.dvd_of_pow_eq_one _ ?_
    rw [pow_succ, pow_mul, ← e1, inv_pow, ← e2, inv_mul_cancel₀ hζ0]
  refine ⟨p₁, p₂, hp₁, hp₂, hB, hB₂, hdvd, fun A hA h hh hδh y => ?_⟩
  have hle : ∀ n : ℕ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).2 (natCast_mem A n)
  rw [Nat.cast_mul, map_mul] at hA
  by_cases h₁ : A.valuation (p₁ : Ω) < 1
  · exact hA₁ A h₁ h hh hδh y
  · have e : A.valuation (p₁ : Ω) = 1 := le_antisymm (hle _) (not_lt.1 h₁)
    rw [e, one_mul] at hA
    exact hA₂ A hA h hh hδh y
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ConjOfSqNonneg
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion
open Polynomial
open scoped IntermediateField

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign

private theorem sq_parts (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) :
    z.re ^ 2 - z.im ^ 2 = a ∧ z.re * z.im = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at h1 h2
  exact ⟨by linarith, by linarith⟩

private theorem conj_of_sq_nonneg (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) (ha : 0 ≤ a) :
    z = starRingEnd ℂ z := by
  obtain ⟨h1, h2⟩ := sq_parts z a h
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have him : z.im = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [h3] at h1
      nlinarith [sq_nonneg z.im]
    · exact h3
  exact (Complex.conj_eq_iff_im.mpr him).symm

private theorem conj_of_sq_nonpos (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) (ha : a ≤ 0) :
    -z = starRingEnd ℂ z := by
  obtain ⟨h1, h2⟩ := sq_parts z a h
  have ha' : (a : ℝ) ≤ 0 := by exact_mod_cast ha
  have hre : z.re = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [h3] at h1
      nlinarith [sq_nonneg z.re]
  apply Complex.ext
  · simp [hre]
  · simp

end UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.mkQ :
    MkQ := by
  intro Y Ω _ _ _ _ _ _ x a hx ⟨g, hg⟩
  have hxa : x ^ 2 = algebraMap Y Ω (a : Y) := by rw [hx, map_intCast]
  have heval : aeval x (X ^ 2 - C (a : Y) : Y[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hxa, sub_self]
  have hint : IsIntegral Y x := ⟨X ^ 2 - C (a : Y), monic_X_pow_sub_C _ two_ne_zero, heval⟩
  have hirr : Irreducible (X ^ 2 - C (a : Y) : Y[X]) := by
    refine X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hg ?_)
    have h2 : x ^ 2 = (algebraMap Y Ω b) ^ 2 := by rw [hxa, ← map_pow, hb]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · rw [h]; exact g.commutes b
    · rw [h, map_neg]; congr 1; exact g.commutes b
  have hmin : minpoly Y x = X ^ 2 - C (a : Y) :=
    (minpoly.eq_of_irreducible_of_monic hirr heval (monic_X_pow_sub_C _ two_ne_zero)).symm
  have hdeg : (minpoly Y x).natDegree = 2 := by rw [hmin, natDegree_X_pow_sub_C _]
  have hfin : Module.finrank Y Y⟮x⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI nf : NumberField Y⟮x⟯ := NumberField.of_module_finite Y _
  have hconj : x ∈ GlobalTheory.CMSub.conjStable Ω := by
    have hφ : ∀ φ : Ω →+* ℂ, (φ x) ^ 2 = (a : ℂ) := fun φ => by rw [← map_pow, hx, map_intCast]
    rcases le_total 0 a with ha | ha
    · exact ⟨x, fun φ => UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign.conj_of_sq_nonneg _ a (hφ φ) ha⟩
    · exact ⟨-x, fun φ => by rw [map_neg]; exact UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign.conj_of_sq_nonpos _ a (hφ φ) ha⟩
  have hle : Y⟮x⟯ ≤ GlobalTheory.CMSub.conjField Y Ω := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hconj
  have cm : IsCMField Y⟮x⟯ := GlobalTheory.CMSub.isCMField_of_le _ hle
  have hxK : x ∈ Y⟮x⟯ := IntermediateField.mem_adjoin_simple_self Y x
  have hspan : ∀ y : Y⟮x⟯, ∃ b c : Y, y = algebraMap Y Y⟮x⟯ b + algebraMap Y Y⟮x⟯ c * ⟨x, hxK⟩ := by
    intro y
    obtain ⟨f, hf, rfl⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval y
    rw [IntermediateField.adjoin.powerBasis_dim, hdeg] at hf
    refine ⟨f.coeff 0, f.coeff 1, ?_⟩
    have hf' : f = C (f.coeff 1) * X + C (f.coeff 0) := Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
    rw [hf', map_add (f := _), map_mul, aeval_C, aeval_C, aeval_X, IntermediateField.adjoin.powerBasis_gen, add_comm]
    simp only [coeff_add, coeff_C_mul, coeff_X_zero, coeff_X_one, coeff_C_zero, coeff_C_succ, mul_zero, mul_one, zero_add, add_zero]
    rfl
  refine ⟨⟨Y⟮x⟯, nf, cm, hfin⟩, hxK, hspan, ?_⟩
  intro F _ _ h hY hhx y
  obtain ⟨b, c, rfl⟩ := hspan y
  have hb : ∀ e : Y, h (algebraMap Y Ω e) = algebraMap Y Ω e := hY
  show h ((algebraMap Y Ω b) + (algebraMap Y Ω c) * x) = (algebraMap Y Ω b) + (algebraMap Y Ω c) * x
  rw [map_add (f := _), map_mul, hb, hb, hhx]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfOf
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.infOf :
    InfOf := by
  intro F Ω _ _ _ _ _ P hP hfin
  have hopen : ∀ Q : QCM F Ω, IsOpen ((Q.K.fixingSubgroup : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro Q
    haveI : FiniteDimensional F ↥Q.K :=
      Module.finite_of_finrank_pos (by rw [Q.two]; exact two_pos)
    exact IntermediateField.fixingSubgroup_isOpen Q.K
  have hS : (⋃ Q ∈ {Q | P Q}, {u : HeightOneSpectrum (𝓞 F) | ∃ A : ValuationSubring Ω,
      IsPlaceOver A u ∧ ¬ Ine (F := F) A ≤ Q.K.fixingSubgroup}).Finite :=
    Set.Finite.biUnion hfin fun Q _ => GlobalTheory.T.finite_places_inertia_not_le_openSubgroup Ω F Q.K.fixingSubgroup (hopen Q)
  obtain ⟨Q, hQ, u, hu, A, hA, τ, hτ, hfix⟩ := hP _ hS
  refine hu (Set.mem_biUnion (show Q ∈ {Q | P Q} from hQ) ⟨A, hA, fun hle => hfix ?_⟩)
  intro x
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hle hτ) _ x.2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrLarge
noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem natCast_notMem_sq {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr K) (w : HeightOneSpectrum (𝓞 K)) : (p : 𝓞 K) ∉ w.asIdeal ^ 2 := by
  intro h
  have hv : (p : 𝓞 K) ∈ w.asIdeal := Ideal.pow_le_self two_ne_zero h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hP := w.isPrime
  have hlo : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hpz).2 (by simpa using hv)
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hun := (not_dvd_discr_iff_forall_mem K (𝓞 K) hpz).1 hd w.asIdeal hP (by simpa using hv)
  have hu : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := hlo.over.symm
  have : Finite (ℤ ⧸ w.asIdeal.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)
  have : (w.asIdeal.under ℤ).IsMaximal := hu ▸ hmax
  have : Finite (w.asIdeal.under ℤ).ResidueField := inferInstance
  have he : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb] at he
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h

theorem unrLarge : UnrLarge := by
  intro K _ _
  refine ⟨(discr K).natAbs, fun p hp hB w => natCast_notMem_sq hp (fun hd => ?_) w⟩
  have h1 : p ∣ (discr K).natAbs := Int.natCast_dvd.mp hd
  have h2 : 0 < (discr K).natAbs := Int.natAbs_pos.mpr (discr_ne_zero K)
  exact absurd (Nat.le_of_dvd h2 h1) (not_le.mpr hB)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.PrimeWith
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion
open scoped Pointwise

private theorem pw_normV (v : HeightOneSpectrum (𝓞 ℚ)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

private theorem eq_of_pow_eq_one_of_valuation_sub_lt_one' {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (M : ℕ) (hM0 : 0 < M)
    (hMv : ¬ A.valuation (M : Ω) < 1) (a b : Ω) (ha : a ^ M = 1) (hb : b ^ M = 1)
    (hab : A.valuation (a - b) < 1) : a = b := by
  by_contra hne
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp [zero_pow hM0.ne'] at hb
  set u := a / b with hudef
  have hu : u ^ M = 1 := by rw [hudef, div_pow, ha, hb, div_one]
  have hu1 : u ≠ 1 := fun h => hne ((div_eq_one_iff_eq hb0).1 h)
  have hvb : A.valuation b = 1 := by
    have h1 : A.valuation b ^ M = 1 := by rw [← map_pow, hb, map_one]
    exact (pow_eq_one_iff.1 h1).resolve_right hM0.ne'
  have hsub : A.valuation (u - 1) < 1 := by
    have he : u - 1 = (a - b) / b := by
      rw [hudef]
      field_simp
    rw [he, map_div₀, hvb, div_one]
    exact hab
  have hvu : A.valuation u = 1 := by
    have := Valuation.map_eq_of_sub_lt A.valuation (x := 1) (y := u) (by rwa [map_one])
    rwa [map_one] at this
  have hsum : ∑ i ∈ Finset.range M, u ^ i = 0 := by
    have h := geom_sum_mul u M
    rw [hu, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hu1)
  have hMeq : (M : Ω) = ∑ i ∈ Finset.range M, (1 - u ^ i) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero]
    simp
  apply hMv
  rw [hMeq]
  refine Valuation.map_sum_lt _ one_ne_zero ?_
  intro i _
  have he : 1 - u ^ i = -((∑ j ∈ Finset.range i, u ^ j) * (u - 1)) := by
    rw [geom_sum_mul]
    ring
  rw [he, Valuation.map_neg, map_mul]
  have hle : A.valuation (∑ j ∈ Finset.range i, u ^ j) ≤ 1 :=
    Valuation.map_sum_le _ (fun j _ => by rw [map_pow, hvu, one_pow])
  rw [mul_comm]
  exact mul_lt_one_of_lt_of_le hsub hle

private theorem valuation_intCast_le_one' {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (z : ℤ) :
    A.valuation (z : Ω) ≤ 1 := by
  have := A.valuation_le_one (z : A)
  simpa using this

private theorem not_valuation_natCast_lt_one_of_not_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p m : ℕ) (hp : p.Prime)
    (hpA : A.valuation (p : Ω) < 1) (hm : ¬ p ∣ m) : ¬ A.valuation (m : Ω) < 1 := by
  intro hm1
  have hcop : Nat.gcd p m = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have h := Nat.gcd_eq_gcd_ab p m
  rw [hcop, Nat.cast_one] at h
  have h' : (1 : Ω) = (p : Ω) * ((Nat.gcdA p m : ℤ) : Ω) + (m : Ω) * ((Nat.gcdB p m : ℤ) : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) h
    push_cast at this
    exact this
  have : A.valuation (1 : Ω) < 1 := by
    rw [h']
    apply Valuation.map_add_lt
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hpA (valuation_intCast_le_one' A _)
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hm1 (valuation_intCast_le_one' A _)
  simp at this

private theorem valuation_intCast_lt_one_iff_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p : ℕ) (hp : p.Prime)
    (hpA : A.valuation (p : Ω) < 1) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  constructor
  · intro hn
    by_contra hnd
    have hnd' : ¬ p ∣ n.natAbs := by
      intro h
      exact hnd (Int.natCast_dvd.2 h)
    apply not_valuation_natCast_lt_one_of_not_dvd A p n.natAbs hp hpA hnd'
    rcases Int.natAbs_eq n with h | h
    · rw [h] at hn
      simpa using hn
    · rw [h] at hn
      simpa [Valuation.map_neg] using hn
  · rintro ⟨c, rfl⟩
    push_cast
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hpA (valuation_intCast_le_one' A _)

private theorem algebraMap_ratInt_eq_intCast_ringOfIntegersEquiv {Ω : Type} [Field Ω] [CharZero Ω] (x : 𝓞 ℚ) :
    algebraMap ℚ Ω (x : ℚ) = ((Rat.ringOfIntegersEquiv x : ℤ) : Ω) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Rat.ringOfIntegersEquiv x = n := ⟨_, rfl⟩
  have h1 : x = (n : 𝓞 ℚ) := by
    rw [← hn, ← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]
  rw [hn]
  subst h1
  simp

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.primeWith :
    DecGen → PrimeWith := by
  intro hDec Y Ω _ _ _ _ _ δ q hq hδ g hg hgg M ζ hM hζ B
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ Y Ω
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed Y, inferInstance⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ Y
  set X : Set Ω := insert δ (insert ζ (Set.range (fun j : Y →+* Ω => j α))) with hXdef
  have hXfin : X.Finite := ((Set.finite_range _).insert _).insert _
  haveI : Finite X := hXfin.to_subtype
  set K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ X with hKdef
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  set L : IntermediateField ℚ Ω := IntermediateField.normalClosure ℚ K Ω with hLdef
  have hKL : K ≤ L := K.le_normalClosure
  haveI : FiniteDimensional ℚ L := inferInstance
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois ℚ L := IsGalois.normalClosure ℚ K Ω
  have hXL : ∀ x ∈ X, x ∈ L := fun x hx => hKL (IntermediateField.subset_adjoin ℚ X hx)
  set gA : Ω ≃ₐ[ℚ] Ω := g.toRatAlgEquiv with hgA
  have hgAapp : ∀ z, gA z = g z := fun z => rfl
  set S : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | normV v ≤ B + M} with hSdef
  have hS : S.Finite := by
    have hfin : (⋃ n ∈ Finset.range (B + M + 1),
        {I : Ideal (𝓞 ℚ) | Ideal.absNorm I = n}).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) (fun n _ => Ideal.finite_setOf_absNorm_eq n)
    refine (hfin.preimage (f := fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal) ?_).subset ?_
    · intro a _ b _ hab
      exact HeightOneSpectrum.ext hab
    · intro w hw
      simp only [hSdef, Set.mem_setOf_eq, pw_normV] at hw
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range,
        Finset.mem_coe, exists_prop]
      exact ⟨_, by omega, rfl⟩
  obtain ⟨v, hvS, -, B0, hB0, hIne, φ, hφ, hφg⟩ :=
    GlobalTheory.Published.chebotarevDegreeOne' ℚ Ω L (AlgEquiv.restrictNormalHom L gA) S hS
  set p := normV v with hpdef
  have hp : p.Prime := by
    set e := Rat.ringOfIntegersEquiv with hedef
    set J : Ideal ℤ := Ideal.map e v.asIdeal with hJdef
    haveI : J.IsPrime := Ideal.map_isPrime_of_equiv e
    have hJ0 : J ≠ ⊥ := fun hJ => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective e.injective).1 hJ)
    have hJp : Prime J := Ideal.prime_of_isPrime hJ0 inferInstance
    have hcard : Ideal.absNorm v.asIdeal = Ideal.absNorm J := by
      rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Submodule.cardQuot_apply]
      exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal J e rfl).toEquiv
    rw [hpdef, pw_normV, hcard]
    exact (Int.prime_absNorm J).2 hJp
  have hpB : B + M < p := by
    simp only [hSdef, Set.mem_setOf_eq, not_le] at hvS
    exact hvS
  have hφL : ∀ x ∈ L, φ x = g x := by
    intro x hx
    have h1 := congrArg (fun τ => ((τ ⟨x, hx⟩ : L) : Ω)) hφg
    have h2 : φ x = gA x := by simpa only [AlgEquiv.restrictNormalHom_apply] using h1
    exact h2
  have hpv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [hpdef, pw_normV]
    exact Ideal.absNorm_mem v.asIdeal
  have hB0p : B0.valuation (p : Ω) < 1 := by
    have := (hB0 ((p : ℕ) : 𝓞 ℚ)).2 hpv
    simpa using this
  have hcrit : ∀ (A' : ValuationSubring Ω), A'.valuation (p : Ω) < 1 → ∀ x : 𝓞 ℚ,
      (A'.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ (p : ℤ) ∣ Rat.ringOfIntegersEquiv x) := by
    intro A' hA' x
    rw [algebraMap_ratInt_eq_intCast_ringOfIntegersEquiv]
    exact valuation_intCast_lt_one_iff_dvd A' p hp hA' _
  have hM0 : ¬ B0.valuation (M : Ω) < 1 := not_valuation_natCast_lt_one_of_not_dvd B0 p M hp hB0p (fun hd => by
    have := Nat.le_of_dvd hM hd
    omega)
  refine ⟨p, hp, by omega, ?_, ?_⟩
  · rw [← hφL ζ (hXL ζ (by simp [hXdef]))]
    refine eq_of_pow_eq_one_of_valuation_sub_lt_one' B0 M hM hM0 _ _ ?_ ?_ ?_
    · rw [← map_pow, hζ.pow_eq_one, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · have hζ1 : B0.valuation ζ ≤ 1 := by
        have h1 : B0.valuation ζ ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
        exact le_of_eq ((pow_eq_one_iff.1 h1).resolve_right hM.ne')
      exact hφ.2 ζ hζ1
  · intro A hA h hhA hhδ y
    have hAv : IsPlaceOver A v := fun x =>
      (hcrit A hA x).trans ((hcrit B0 hB0p x).symm.trans (hB0 x))
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver hB0 hAv
    set hA' : Ω ≃ₐ[ℚ] Ω := h.toRatAlgEquiv with hhA'
    have hfixA : hA' • A = A := by
      ext z
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have h3 := hhA (hA'⁻¹ • z)
      have hz : h (hA'⁻¹ • z) = z := by
        show hA' (hA'.symm z) = z
        exact AlgEquiv.apply_symm_apply _ _
      rw [hz] at h3
      exact h3.symm
    set h' : G ℚ Ω := σ⁻¹ * hA' * σ with hh'
    have hh'mem : h' ∈ Dec B0 := by
      refine MulAction.mem_stabilizer_iff.2 ?_
      rw [hh', mul_smul, mul_smul, hσ, hfixA, ← hσ, inv_smul_smul]
    obtain ⟨k, hk⟩ := hDec ℚ Ω B0 v hB0 φ hφ X hXfin
      (fun τ hτ x hx => ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (hIne hτ)) x (hXL x hx))
      h' hh'mem
    have hpowL : ∀ x ∈ L, (φ ^ k) x = (gA ^ k) x := by
      intro x hx
      have h1 := congrArg (fun τ => ((τ ^ k) ⟨x, hx⟩ : Ω)) hφg
      simp only [← map_zpow, AlgEquiv.restrictNormalHom_apply] at h1
      exact h1
    have hstab : ∀ z : Ω, (gA ^ 2) z = z → ∀ m : ℤ, ((gA ^ 2) ^ m) z = z := by
      intro z hz m
      have hmem2 : gA ^ 2 ∈ MulAction.stabilizer (Ω ≃ₐ[ℚ] Ω) z := hz
      exact Subgroup.zpow_mem _ hmem2 m
    have hg2δ : (gA ^ 2) δ = δ := by
      rw [pow_two, AlgEquiv.mul_apply, hgAapp, hgAapp, hg, map_neg, hg, neg_neg]
    have hσδ : σ δ = δ ∨ σ δ = -δ := by
      have h2 : (σ δ) ^ 2 = δ ^ 2 := by rw [← map_pow, hδ, map_natCast]
      exact sq_eq_sq_iff_eq_or_eq_neg.1 h2
    have hh'δ : h' δ = δ := by
      have h2 : hA' (σ δ) = σ δ := by
        rcases hσδ with h4 | h4 <;> rw [h4]
        · exact hhδ
        · show h (-δ) = -δ
          rw [map_neg, hhδ]
      show σ.symm (hA' (σ δ)) = δ
      rw [h2]
      exact σ.symm_apply_apply δ
    have hδX : δ ∈ X := by simp [hXdef]
    have hkδ : (gA ^ k) δ = δ := by rw [← hpowL δ (hXL δ hδX), ← hk δ hδX, hh'δ]
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      have : (q : Ω) = 0 := by rw [← hδ]; ring
      exact_mod_cast (Nat.pos_iff_ne_zero.1 hq) (by exact_mod_cast this)
    obtain ⟨r, hr⟩ : Even k := by
      rcases Int.even_or_odd k with he | ⟨r, hr⟩
      · exact he
      · exfalso
        have e1 : gA ^ k = (gA ^ 2) ^ r * gA := by
          rw [hr, zpow_add_one, zpow_mul]
          norm_cast
        have h5 : (gA ^ k) δ = -δ := by
          rw [e1, AlgEquiv.mul_apply, hgAapp, hg, map_neg, hstab δ hg2δ r]
        rw [h5] at hkδ
        exact hδ0 (by linear_combination (-1/2 : Ω) * hkδ)
    have hkpow : gA ^ k = (gA ^ 2) ^ r := by
      rw [hr, ← two_mul, zpow_mul]
      norm_cast
    set j' : Y →+* Ω := (σ⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.toRingHom.comp (algebraMap Y Ω) with hj'
    have hj'X : j' α ∈ X := Or.inr (Or.inr ⟨j', rfl⟩)
    have hg2j : (gA ^ 2) (j' α) = j' α := by
      rw [pow_two, AlgEquiv.mul_apply, hgAapp, hgAapp]
      exact hgg j' α
    have hh'j : h' (j' α) = j' α := by
      rw [hk _ hj'X, hpowL _ (hXL _ hj'X), hkpow]
      exact hstab _ hg2j r
    have hα' : h (algebraMap Y Ω α) = algebraMap Y Ω α := by
      have e2 : σ (j' α) = algebraMap Y Ω α := by
        show σ (σ.symm _) = _
        exact σ.apply_symm_apply _
      have e3 : σ (h' (j' α)) = hA' (σ (j' α)) := by
        show σ (σ.symm (hA' (σ (j' α)))) = _
        exact σ.apply_symm_apply _
      have h6 : σ (h' (j' α)) = σ (j' α) := by rw [hh'j]
      rw [e3, e2] at h6
      exact h6
    have hext : (hA'.toAlgHom.comp (IsScalarTower.toAlgHom ℚ Y Ω)) = IsScalarTower.toAlgHom ℚ Y Ω := by
      apply AlgHom.ext_of_adjoin_eq_top (s := {α})
      · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
          (Algebra.IsAlgebraic.isAlgebraic α), hα]
        exact IntermediateField.top_toSubalgebra
      · intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hα'
    have h7 := congrArg (fun f => f y) hext
    have h8 : hA' (algebraMap Y Ω y) = algebraMap Y Ω y := by simpa using h7
    exact h8
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.DecGen
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem valuation_apply_le_one_of_mem_dec {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (e : G F Ω) (he : e ∈ Dec A) (x : Ω) (hx : A.valuation x ≤ 1) : A.valuation (e x) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
  have h2 := ValuationSubring.smul_mem_pointwise_smul e x A hx
  open Pointwise in
  have h3 : e • A = A := he
  rw [h3] at h2
  exact h2

private theorem valuation_apply_lt_one_of_mem_dec {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (e : G F Ω) (he : e ∈ Dec A) (z : Ω) (hz : A.valuation z < 1) : A.valuation (e z) < 1 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa using hz
  have hez : e z ≠ 0 := by simpa using hz0
  have key : 1 < A.valuation z⁻¹ := by
    rw [Valuation.one_lt_val_iff _ (inv_ne_zero hz0), inv_inv]
    exact hz
  have h1 : 1 < A.valuation (e z)⁻¹ := by
    by_contra hc
    push_neg at hc
    have h4 := valuation_apply_le_one_of_mem_dec A e⁻¹ (inv_mem he) _ hc
    have h5 : e⁻¹ (e z)⁻¹ = z⁻¹ := by
      rw [map_inv₀, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [h5] at h4
    exact absurd key (not_lt.mpr h4)
  rw [Valuation.one_lt_val_iff _ (inv_ne_zero hez), inv_inv] at h1
  exact h1

private theorem inv_mul_mul_mem_ine_of_mem_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (d τ : G F Ω) (hd : d ∈ Dec A) (hτ : τ ∈ Ine A) :
    d⁻¹ * τ * d ∈ Ine A := by
  have hτD : τ ∈ Dec A := Ine_le_Dec A hτ
  obtain ⟨_, hτ2⟩ := hτ
  refine ⟨(Dec A).mul_mem ((Dec A).mul_mem ((Dec A).inv_mem hd) hτD) hd, fun x hx => ?_⟩
  have h1 := hτ2 (d x) (valuation_apply_le_one_of_mem_dec A d hd x hx)
  have h2 := valuation_apply_lt_one_of_mem_dec A d⁻¹ ((Dec A).inv_mem hd) _ h1
  have e : (d⁻¹ * τ * d) x - x = d⁻¹ (τ (d x) - d x) := by
    rw [map_sub, ← AlgEquiv.mul_apply d⁻¹ d, inv_mul_cancel, AlgEquiv.one_apply, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply]
  rw [e]
  exact h2

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.decGen :
    DecGen := by
  intro F Ω _ _ _ _ _ A v hAv φ hφ X hX hXI g hg
  set Y : Set Ω := {y | ∀ τ ∈ Ine (F := F) A, τ y = y} with hYdef
  have hφD : φ ∈ Dec A := hφ.1
  have hstab : ∀ (k : ℤ) (y : Ω), y ∈ Y → (φ ^ k) y ∈ Y := by
    intro k y hy τ hτ
    have h1 := hy _ (inv_mul_mul_mem_ine_of_mem_dec A (φ ^ k) τ (zpow_mem hφD k) hτ)
    have h2 := congrArg (φ ^ k) h1
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply (φ ^ k) (φ ^ k)⁻¹,
      mul_inv_cancel, AlgEquiv.one_apply] at h2
    exact h2
  let φ' : Dec A := ⟨φ, hφD⟩
  have hdense := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hAv φ' hφ
  have hP : ∀ h ∈ (Subgroup.zpowers φ' ⊔ (Ine A).subgroupOf (Dec A)),
      ∃ k : ℤ, ∀ y ∈ Y, (h : G F Ω) y = (φ ^ k) y := by
    intro h hh
    rw [Subgroup.sup_eq_closure] at hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ⟨k, fun y _ => by rw [Subgroup.coe_zpow]⟩
      · refine ⟨0, fun y hy => ?_⟩
        rw [zpow_zero, AlgEquiv.one_apply]
        exact hy _ (Subgroup.mem_subgroupOf.mp hx)
    | one => exact ⟨0, fun y _ => by rw [zpow_zero]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, fun z hz => ?_⟩
      rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hb z hz, ha _ (hstab b z hz), zpow_add,
        AlgEquiv.mul_apply]
    | inv x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨-a, fun z hz => ?_⟩
      have hw := ha _ (hstab (-a) z hz)
      have e1 : (φ ^ a) ((φ ^ (-a)) z) = z := by
        rw [← AlgEquiv.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, AlgEquiv.one_apply]
      rw [e1] at hw
      rw [Subgroup.coe_inv]
      calc ((x : G F Ω)⁻¹) z = ((x : G F Ω)⁻¹) ((x : G F Ω) ((φ ^ (-a)) z)) := by rw [hw]
        _ = (φ ^ (-a)) z := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Finite X := hX.to_subtype
  haveI : FiniteDimensional F (IntermediateField.adjoin F X) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let O : Set (Dec A) := Subtype.val ⁻¹' ((fun σ : G F Ω => g⁻¹ * σ) ⁻¹'
    ((IntermediateField.adjoin F X).fixingSubgroup : Set (G F Ω)))
  have hO : IsOpen O :=
    ((IntermediateField.adjoin F X).fixingSubgroup_isOpen.preimage (continuous_const_mul g⁻¹)).preimage
      continuous_subtype_val
  have hgO : (⟨g, hg⟩ : Dec A) ∈ O := by
    show g⁻¹ * g ∈ (IntermediateField.adjoin F X).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
  have hmem : (⟨g, hg⟩ : Dec A) ∈
      ((Subgroup.zpowers φ' ⊔ (Ine A).subgroupOf (Dec A)).topologicalClosure : Set (Dec A)) := by
    rw [hdense]
    exact Subgroup.mem_top _
  rw [Subgroup.topologicalClosure_coe] at hmem
  obtain ⟨h, hhO, hhK⟩ := (mem_closure_iff.mp hmem) O hO hgO
  obtain ⟨k, hk⟩ := hP h hhK
  refine ⟨k, fun x hx => ?_⟩
  have hfix : g⁻¹ * (h : G F Ω) ∈ (IntermediateField.adjoin F X).fixingSubgroup := hhO
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix x
    (IntermediateField.subset_adjoin F X hx)
  have hxY : x ∈ Y := fun τ hτ => hXI τ hτ x hx
  rw [← hk x hxY]
  have h2 := congrArg g h1
  rw [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹, mul_inv_cancel, AlgEquiv.one_apply] at h2
  exact h2.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SqrtFix
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.sqrtFix :
    SqrtFix := by
  intro F Ω _ _ _ _ A x a hx
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hsq : ∀ g : G F Ω, g x = x ∨ g x = -x := by
    intro g
    have hgx : (g x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
    have h0 : (g x - x) * (g x + x) = 0 := by linear_combination hgx
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hint : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1 := fun k => by
    exact_mod_cast A.valuation_le_one (k : A)
  refine ⟨?_, ?_⟩
  · intro t _ hvt hdiv g hg
    rcases hsq g with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hdiv
      have hk' : (a : Ω) - 1 = 8 * (t : Ω) * (k : Ω) := by
        have hc := congrArg (fun z : ℤ => (z : Ω)) hk
        push_cast at hc
        linear_combination hc
      set y : Ω := (x - 1) / 2 with hy
      set y' : Ω := (-x - 1) / 2 with hy'
      have hgy : g y = y' := by
        rw [hy, hy', map_div₀, map_sub, map_one, map_ofNat, h]
      have hsum : y + y' = -1 := by
        rw [hy, hy']
        ring
      have hprod : y * y' = ((-2 * k : ℤ) : Ω) * (t : Ω) := by
        rw [hy, hy']
        push_cast
        linear_combination (-1 / 4 : Ω) * hx - (1 / 4 : Ω) * hk'
      have hvp : A.valuation (y * y') < 1 := by
        rw [hprod, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint _)) hvt
      have hvs : A.valuation (y + y') = 1 := by
        rw [hsum, Valuation.map_neg, Valuation.map_one]
      have hiff := valuation_apply_lt_one_iff hg y
      rw [hgy] at hiff
      by_cases hyl : A.valuation y < 1
      · have hs := Valuation.map_add_lt A.valuation hyl (hiff.2 hyl)
        rw [hvs] at hs
        exact lt_irrefl _ hs
      · have hyl' : ¬ A.valuation y' < 1 := fun h' => hyl (hiff.1 h')
        push_neg at hyl hyl'
        have hge : 1 ≤ A.valuation (y * y') := by
          rw [map_mul]
          exact one_le_mul hyl hyl'
        exact absurd hvp (not_lt.2 hge)
  · intro h2a τ hτ
    obtain ⟨-, hI⟩ : τ ∈ ValuationSubring.decompositionSubgroup F A ∧
        ∀ (y : Ω), A.valuation y ≤ 1 → A.valuation (τ y - y) < 1 := hτ
    rcases hsq τ with h | h
    · exact h
    · exfalso
      have hv2 : A.valuation (2 : Ω) ≤ 1 := by simpa using hint 2
      have hva : A.valuation (a : Ω) ≤ 1 := hint a
      have e2a : A.valuation (2 : Ω) * A.valuation (a : Ω) = 1 := by
        rw [← map_mul]
        push_cast at h2a
        exact h2a
      have hv2' : A.valuation (2 : Ω) = 1 :=
        le_antisymm hv2 (e2a ▸ mul_le_of_le_one_right' hva)
      have hva' : A.valuation (a : Ω) = 1 :=
        le_antisymm hva (e2a ▸ mul_le_of_le_one_left' hv2)
      have hvx2 : A.valuation x ^ 2 = 1 := by
        rw [← Valuation.map_pow, hx, hva']
      have hvx : A.valuation x = 1 := by
        rcases lt_trichotomy (A.valuation x) 1 with hl | he | hg
        · exact absurd hvx2 (ne_of_lt (pow_lt_one' hl two_ne_zero))
        · exact he
        · exact absurd hvx2 (ne_of_gt (one_lt_pow' hg two_ne_zero))
      have key := hI x hvx.le
      rw [h, show -x - x = -(2 * x) by ring, Valuation.map_neg, map_mul, hv2', hvx, one_mul] at key
      exact lt_irrefl _ key
end

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem freshChar_holds : FreshChar := freshChar powChar inertiaGen decPow (freshPrime splitPlace rootMod)
theorem layerOf_holds : LayerOf := layerOf inclOf indexComap
theorem noSelfTwist_holds : NoSelfTwist := noSelfTwist_of normRam
theorem infinitely_many_real_quadratic_steps : Quad0 := quadraticCharTwist_of_exists_of_infinity (quad0Ex sqrtFix mkQ unrLarge) infOf
theorem allUnr_holds : AllUnr := allUnr splitIff
theorem threeApart_holds : ThreeApart := threeApart_of double apartUp
theorem satSplit_holds : SatSplit := satSplit

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
