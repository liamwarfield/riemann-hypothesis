module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimple
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FrobTeich

variable {Ω : Type} [Field Ω]

theorem eq_of_pow_eq_self_of_cong (A : ValuationSubring Ω) {N : ℕ} (hN : A.valuation (N : Ω) < 1)
    {a b : Ω} (ha : a ^ N = a) (hb : b ^ N = b) (hab : A.valuation (a - b) < 1) : a = b := by
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · interval_cases N
    · rw [pow_zero] at ha hb; rw [← ha, ← hb]
    · simp at hN
  have hle : ∀ c : Ω, c ^ N = c → A.valuation c ≤ 1 := by
    intro c hc
    by_contra hc1
    have h1 : 1 < A.valuation c := not_le.mp hc1
    have h2 : A.valuation c ^ 1 < A.valuation c ^ N := pow_lt_pow_right₀ h1 (by omega)
    rw [← map_pow, ← map_pow, hc, pow_one] at h2
    exact lt_irrefl _ h2
  have ha1 := hle a ha
  have hb1 := hle b hb
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  set S := ∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i) with hS
  have hS1 : S = 1 := by
    have h1 : S * (a - b) = a - b := by rw [hS, geom_sum₂_mul, ha, hb]
    have h2 : (S - 1) * (a - b) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hsub
  have hdiff : A.valuation (S - ∑ i ∈ Finset.range N, a ^ i * a ^ (N - 1 - i)) < 1 := by
    rw [hS, ← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [← mul_sub, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (GlobalTheory.WeilDeligne.val_pow_le_one ha1 i))
      (GlobalTheory.WeilDeligne.cong_pow hb1 ha1 (GlobalTheory.WeilDeligne.cong_symm hab) _)
  rw [geom_sum₂_self] at hdiff
  have hNa : A.valuation ((N : Ω) * a ^ (N - 1)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (GlobalTheory.WeilDeligne.val_pow_le_one ha1 _)) hN
  have hS' : A.valuation S < 1 := by
    have e : S = (S - (N : Ω) * a ^ (N - 1)) + (N : Ω) * a ^ (N - 1) := by ring
    rw [e]; exact Valuation.map_add_lt _ hdiff hNa
  rw [hS1, map_one] at hS'
  exact lt_irrefl _ hS'


open Polynomial in
theorem exists_pow_eq_self_cong [IsAlgClosed Ω] (A : ValuationSubring Ω) {N : ℕ} (hN : 2 ≤ N)
    {x : Ω} (hx : A.valuation (x ^ N - x) < 1) : ∃ ζ : Ω, ζ ^ N = ζ ∧ A.valuation (x - ζ) < 1 := by
  set P : Polynomial Ω := X ^ N - X with hP
  have hdeg : P.natDegree = N := by
    rw [hP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp; omega
  have hmon : P.Monic := by
    rw [hP]; exact monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by omega : 1 < N))
  have hsplit : P = (P.roots.map fun a => X - C a).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (by rw [IsAlgClosed.card_roots_eq_natDegree])).symm
  have hev : x ^ N - x = (P.roots.map fun a => x - a).prod := by
    have := congrArg (eval x) hsplit
    rw [eval_multiset_prod, Multiset.map_map] at this
    simpa [hP, Function.comp_def] using this
  by_contra hno
  push_neg at hno
  have hge : ∀ a ∈ P.roots, 1 ≤ A.valuation (x - a) := by
    intro a ha
    refine hno a ?_
    have := (mem_roots hmon.ne_zero).mp ha
    simpa [hP, sub_eq_zero] using this
  have h1 : 1 ≤ A.valuation (x ^ N - x) := by
    rw [hev, map_multiset_prod]
    refine Multiset.prod_induction (fun c => 1 ≤ c) _ (fun a b ha hb => ?_) le_rfl ?_
    · simpa using mul_le_mul' ha hb
    · intro c hc
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hc
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
      exact hge a ha
  exact absurd hx (not_lt.mpr h1)

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

theorem exists_prime_pow_normV (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) : ∃ p f : ℕ, p.Prime ∧ 0 < f ∧ normV w = p ^ f ∧ A.valuation (p : Ω) < 1 := by
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  set p := ringChar (𝓞 E ⧸ w.asIdeal) with hp_def
  obtain ⟨n, hp, hn⟩ := FiniteField.card (𝓞 E ⧸ w.asIdeal) p
  have hpw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  refine ⟨p, n, hp, n.pos, ?_, ?_⟩
  · show Nat.card (𝓞 E ⧸ w.asIdeal) = p ^ (n : ℕ)
    rw [Nat.card_eq_fintype_card, hn]
  · have := (h _).mpr hpw
    simpa using this

theorem exists_pow_char_pow_eq_self {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (P : Polynomial ℤ) (hP : P.map (Int.castRingHom k) ≠ 0) {y : k}
    (hy : P.eval₂ (Int.castRingHom k) y = 0) : ∃ r : ℕ, 0 < r ∧ y ^ p ^ r = y := by
  have hroot : ∀ i : ℕ, y ^ p ^ i ∈ {z : k | (P.map (Int.castRingHom k)).IsRoot z} := by
    intro i
    show (P.map (Int.castRingHom k)).eval (y ^ p ^ i) = 0
    rw [Polynomial.eval_map, ← iterateFrobenius_def (R := k) p i,
      ← RingHom.ext_int ((iterateFrobenius k p i).comp (Int.castRingHom k)) (Int.castRingHom k),
      ← Polynomial.hom_eval₂, hy, map_zero]
  obtain ⟨i, j, hij, heq⟩ := (Polynomial.finite_setOf_isRoot hP).exists_lt_map_eq_of_forall_mem hroot
  refine ⟨j - i, by omega, ?_⟩
  apply (iterateFrobenius k p i).injective
  rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
  exact heq.symm

theorem exists_pow_prime_pow_cong [CharZero Ω] (A : ValuationSubring Ω) {x : Ω}
    (halg : IsAlgebraic ℤ x) (hx : A.valuation x ≤ 1) {p : ℕ} (hp : p.Prime)
    (hpA : A.valuation (p : Ω) < 1) : ∃ r : ℕ, 0 < r ∧ A.valuation (x ^ p ^ r - x) < 1 := by
  obtain ⟨P, hP0, hPx⟩ := halg
  set Q := P.primPart with hQ
  have hQprim : Q.IsPrimitive := P.isPrimitive_primPart
  have hQx : Polynomial.aeval x Q = 0 := by
    have e := congrArg (Polynomial.aeval x) P.eq_C_content_mul_primPart
    rw [hPx, map_mul, Polynomial.aeval_C] at e
    have hc : (algebraMap ℤ Ω) P.content ≠ 0 := by
      rw [eq_intCast, Int.cast_ne_zero]; exact (Polynomial.content_eq_zero_iff.not).mpr hP0
    exact (mul_eq_zero.mp e.symm).resolve_left hc
  haveI : Fact p.Prime := ⟨hp⟩
  set k := IsLocalRing.ResidueField A
  set y : A := ⟨x, (A.valuation_le_one_iff x).mp hx⟩ with hy_def
  haveI : CharP k p := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      A.valuation_lt_one_iff]
    simpa using hpA
  have hmap : Q.map (Int.castRingHom k) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ Q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun g => _root_.AddMonoidAlgebra.coeff (M := ℕ) g i) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
      exact (CharP.intCast_eq_zero_iff k p _).mp this
    have hu := hQprim (p : ℤ) hdvd
    rw [Int.isUnit_iff] at hu
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    rcases hu with hu | hu <;> omega
  have hyA : Q.eval₂ (Int.castRingHom A) y = 0 := by
    apply Subtype.ext
    have e := Polynomial.hom_eval₂ Q (Int.castRingHom A) A.subtype y
    rw [RingHom.ext_int (A.subtype.comp (Int.castRingHom A)) (algebraMap ℤ Ω)] at e
    change A.subtype _ = A.subtype 0
    rw [e, map_zero]; exact hQx
  have hyk : Q.eval₂ (Int.castRingHom k) (IsLocalRing.residue A y) = 0 := by
    rw [← RingHom.ext_int ((IsLocalRing.residue A).comp (Int.castRingHom A)) (Int.castRingHom k),
      ← Polynomial.hom_eval₂, hyA, map_zero]
  obtain ⟨r, hr, hyr⟩ := exists_pow_char_pow_eq_self p Q hmap hyk
  refine ⟨r, hr, ?_⟩
  have hmem : y ^ p ^ r - y ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hyr, sub_self]
  have := (A.valuation_lt_one_iff _).mp hmem
  simpa [hy_def] using this

theorem exists_pow_normV_pow_cong [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) {x : Ω} (hx : A.valuation x ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ A.valuation (x ^ normV w ^ m - x) < 1 := by
  obtain ⟨p, f, hp, hf, hq, hpA⟩ := exists_prime_pow_normV A w h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨r, hr, hxr⟩ := exists_pow_prime_pow_cong A halg hx hp hpA
  refine ⟨r, hr, ?_⟩
  have key : ∀ j : ℕ, A.valuation (x ^ (p ^ r) ^ j - x) < 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := GlobalTheory.WeilDeligne.cong_pow (GlobalTheory.WeilDeligne.val_pow_le_one hx _) hx ih (p ^ r)
      rw [← pow_mul, ← pow_succ] at h1
      exact GlobalTheory.WeilDeligne.cong_trans h1 hxr
  have e : normV w ^ r = (p ^ r) ^ f := by rw [hq, ← pow_mul, ← pow_mul, mul_comm]
  rw [e]; exact key f

end GlobalTheory.FrobTeich

open GlobalTheory.FrobTeich in
theorem GlobalTheory.FrobTeich.isFrob_iff_teichmuller : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (σ : G E Ω), IsFrob (F := E) A (normV w) σ ↔ σ ∈ Dec (F := E) A ∧ ∀ (ζ : Ω) (m : ℕ), 0 < m → ζ ^ normV w ^ m = ζ → σ ζ = ζ ^ normV w := by
  intro E Ω _ _ _ _ _ A w h σ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨p, f, hp, hf, hq, hpA⟩ := exists_prime_pow_normV A w h
  set q := normV w with hq_def
  have hqA : A.valuation (q : Ω) < 1 := by
    rw [hq, Nat.cast_pow, map_pow]; exact pow_lt_one₀ zero_le hpA hf.ne'
  have hq2 : 2 ≤ q := by rw [hq]; exact le_trans hp.two_le (Nat.le_self_pow hf.ne' p)
  constructor
  · rintro ⟨hD, hc⟩
    refine ⟨hD, fun ζ m hm hζ => ?_⟩
    have hNA : A.valuation ((q ^ m : ℕ) : Ω) < 1 := by
      rw [Nat.cast_pow, map_pow]; exact pow_lt_one₀ zero_le hqA hm.ne'
    have hζ1 : A.valuation ζ ≤ 1 := by
      by_contra hc1
      have h1 : 1 < A.valuation ζ := not_le.mp hc1
      have h2 : A.valuation ζ ^ 1 < A.valuation ζ ^ (q ^ m) :=
        pow_lt_pow_right₀ h1 (Nat.one_lt_pow hm.ne' (by omega))
      rw [← map_pow, ← map_pow, hζ, pow_one] at h2
      exact lt_irrefl _ h2
    refine eq_of_pow_eq_self_of_cong A hNA ?_ ?_ (hc ζ hζ1)
    · rw [← map_pow, hζ]
    · rw [← pow_mul, mul_comm, pow_mul, hζ]
  · rintro ⟨hD, hT⟩
    refine ⟨hD, fun x hx => ?_⟩
    obtain ⟨m, hm, hxm⟩ := exists_pow_normV_pow_cong A w h hx
    obtain ⟨ζ, hζ, hxζ⟩ := exists_pow_eq_self_cong A
      (le_trans hq2 (Nat.le_self_pow hm.ne' q)) hxm
    have hσζ := hT ζ m hm hζ
    have hζ1 : A.valuation ζ ≤ 1 := by
      have e : ζ = x - (x - ζ) := by ring
      rw [e]
      exact le_trans (Valuation.map_sub _ _ _) (max_le hx hxζ.le)
    have e : σ x - x ^ q = σ (x - ζ) + (ζ ^ q - x ^ q) := by
      rw [map_sub, hσζ]; ring
    rw [e]
    refine Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hD _).mpr hxζ) ?_
    exact GlobalTheory.WeilDeligne.cong_pow hζ1 hx (GlobalTheory.WeilDeligne.cong_symm hxζ) q
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordsOfMemAdjoin
namespace GlobalTheory.CoordsOfMemAdjoin

open IntermediateField

theorem exists_coords_of_mem_adjoin {F : Type*} [Field F] [Algebra ℚ F] {s : F} {c : ℚ}
    (hs : s ^ 2 = algebraMap ℚ F c) {x : F} (hx : x ∈ ℚ⟮s⟯) :
    ∃ a b : ℚ, x = algebraMap ℚ F a + algebraMap ℚ F b * s := by
  have hint : IsIntegral ℚ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hs]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set F) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    refine ⟨0, 1, ?_⟩
    rw [Set.mem_singleton_iff.mp hy]
    simp
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a + a', b + b', ?_⟩
    simp only [map_add (f := _)]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a * a' + b * b' * c, a * b' + b * a', ?_⟩
    simp only [map_add (f := _), map_mul, ← hs]
    ring

theorem exists_rat_coords {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) {x : H.E} (hx : x ∈ H.K) :
    ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqrtMinusD := by
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hs : H.sqrtMinusD ^ 2 = algebraMap ℚ H.E (-(H.d : ℚ)) := by
    rw [map_neg, map_natCast]
    exact hb
  obtain ⟨a, b, h⟩ := exists_coords_of_mem_adjoin hs hx
  exact ⟨a, b, by simpa only [eq_ratCast] using h⟩

end GlobalTheory.CoordsOfMemAdjoin
end

noncomputable section

namespace GlobalTheory.Mem.Col2.HostK

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.UnusedSlot33.HK
open scoped BigOperators

variable {R : Ranks} (H : Host R)

theorem emb_conj (f : H.E →+* ℂ) (y : H.E) : f (H.conj y) = starRingEnd ℂ (f y) := Formalism.HC.HostAx.conjE_apply _ _ _

theorem sqrt_mem : H.sqrtMinusD ∈ H.K := bE_mem H

theorem φ₀_sqrt : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem exists_coords {x : H.E} (hx : x ∈ H.K) : ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqrtMinusD :=
  by apply _root_.GlobalTheory.CoordsOfMemAdjoin.exists_rat_coords <;> assumption

theorem conj_coords (a b : ℚ) :
    H.conj ((a : H.E) + (b : H.E) * H.sqrtMinusD) = (a : H.E) - (b : H.E) * H.sqrtMinusD := by
  rw [map_add (f := _), map_mul, map_ratCast, map_ratCast, H.conj_sqrtMinusD]
  ring

theorem conj_mem {x : H.E} (hx : x ∈ H.K) : H.conj x ∈ H.K := by
  obtain ⟨a, b, rfl⟩ := exists_coords H hx
  rw [conj_coords]
  exact sub_mem (SubfieldClass.ratCast_mem _ a) (mul_mem (SubfieldClass.ratCast_mem _ b) (sqrt_mem H))

def conjK : H.K →+* H.K :=
  RingHom.codRestrict ((H.conj : H.E →+* H.E).comp H.K.val.toRingHom) H.K (fun x => conj_mem H x.2)

theorem coe_conjK (x : H.K) : ((conjK H x : H.K) : H.E) = H.conj (x : H.E) := rfl

theorem conjK_conjK (x : H.K) : conjK H (conjK H x) = x := Subtype.ext (conj_conj H x)

theorem exists_norm_int (x : 𝓞 H.K) : ∃ m : ℤ, (x : H.K) * conjK H x = m :=
  ⟨Algebra.intNorm ℤ (𝓞 H.K) x, Subtype.ext (by
    have := norm_int H x
    simpa [coe_conjK] using this.symm)⟩

theorem isGalois_over : IsGalois H.K H.E := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  exact IsGalois.tower_top_of_isGalois ℚ _ _

theorem coe_trace (y : H.E) : ((Algebra.trace H.K H.E y : H.K) : H.E) = ∑ τ : H.E ≃ₐ[H.K] H.E, τ y := by
  have := isGalois_over H
  exact trace_eq_sum_automorphisms (K := H.K) y

theorem conj_comm (τ : H.E ≃ₐ[H.K] H.E) (y : H.E) : H.conj (τ y) = τ (H.conj y) :=
  H.φ₀.injective (by
    rw [emb_conj H H.φ₀ (τ y)]
    exact (emb_conj H (H.φ₀.comp (τ : H.E →+* H.E)) y).symm)

theorem trace_conj (y : H.E) : Algebra.trace H.K H.E (H.conj y) = conjK H (Algebra.trace H.K H.E y) := by
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_conjK, coe_trace, coe_trace, map_sum]
  exact Finset.sum_congr rfl fun τ _ => (conj_comm H τ y).symm

theorem trace_pos (y : H.E) (hy : y ≠ 0) : ∃ a : ℚ, 0 < a ∧ Algebra.trace H.K H.E (y * H.conj y) = (a : H.K) := by
  obtain ⟨a, b, hab⟩ := exists_coords H (Algebra.trace H.K H.E (y * H.conj y)).2
  have hfix : H.conj ((Algebra.trace H.K H.E (y * H.conj y) : H.K) : H.E)
      = ((Algebra.trace H.K H.E (y * H.conj y) : H.K) : H.E) := by
    rw [← coe_conjK, ← trace_conj, map_mul, conj_conj, mul_comm]
  rw [hab, conj_coords] at hfix
  have hb : (b : H.E) * H.sqrtMinusD = 0 := by linear_combination (-1 / 2 : H.E) * hfix
  rw [hb, add_zero] at hab
  refine ⟨a, ?_, Subtype.ext (by rw [hab]; simp)⟩
  have h1 := congrArg H.φ₀ hab
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_trace, map_sum, map_ratCast] at h1
  have h2 : ∀ τ : H.E ≃ₐ[H.K] H.E, H.φ₀ (τ (y * H.conj y)) = ((Complex.normSq (H.φ₀ (τ y)) : ℝ) : ℂ) := by
    intro τ
    rw [map_mul, ← conj_comm, map_mul, emb_conj, Complex.mul_conj]
  simp only [h2] at h1
  have h3 : ∑ τ : H.E ≃ₐ[H.K] H.E, Complex.normSq (H.φ₀ (τ y)) = (a : ℝ) := by
    exact_mod_cast h1
  have h4 : (0 : ℝ) < a := by
    rw [← h3]
    refine Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ?_) Finset.univ_nonempty
    simpa using hy
  exact_mod_cast h4

theorem card_tau : Fintype.card (Tau R) = Module.finrank H.K H.E := by
  have := isGalois_over H
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  exact Fintype.card_of_bijective (GlobalTheory.InducedType.galK_bijective H)

theorem embT_K (τ : Tau R) (a : H.K) : embT H τ (a : H.E) = H.φ₀ (a : H.E) := by
  change H.φ₀ (H.sigmaOf _ _) = _
  rw [sigmaOf_fix_K H _ τ.2 _ a.2]

theorem sum_embT (y : H.E) : ∑ τ, embT H τ y = H.φ₀ ((Algebra.trace H.K H.E y : H.K) : H.E) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_trace, map_sum]
  exact Fintype.sum_bijective (GlobalTheory.InducedType.galK H) (GlobalTheory.InducedType.galK_bijective H) _ _ (fun τ => rfl)

theorem isIntegral_half : IsIntegral ℤ ((1 + (⟨H.sqrtMinusD, sqrt_mem H⟩ : H.K)) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := by
    have := H.hyp.2.2.2.1
    exact ⟨(H.d + 1) / 4, by omega⟩
  have hs : (⟨H.sqrtMinusD, sqrt_mem H⟩ : H.K) ^ 2 = -(H.d : H.K) := Subtype.ext (by simpa using H.sqrtMinusD_sq)
  have hm' : (H.d : H.K) + 1 = 4 * m := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp only [eq_intCast, Int.cast_natCast]
  linear_combination (1 / 4 : H.K) * hs - (1 / 4 : H.K) * hm'

end GlobalTheory.Mem.Col2.HostK

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegShaOK
noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem shaOK_shaTrue (B : Pre) : ShaOK B (GaloisStage.shaTrue B.host) := by
  refine ⟨fun p _ => GaloisStage.lData B.host p, ?_⟩
  intro p hp e _ _ n h
  rw [GaloisStage.shaTrue, dite_eq_left hp.out]
  show ((Formalism.GaloisCohomology.shaLen (GaloisStage.lData B.host p) (e : ℤ)).toNat : ℚ) = n
  rw [h, ENat.toNat_natCast]

end GlobalTheory.MemN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodAtOfFixRed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

variable {D : D7}

def FixRed (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd)
    (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) : Prop :=
  ∀ kv : (Σ k : Fin 2, D.nd.PlG k), IsRedBasis X (D.naut.plGw kv.1 kv.2) (b kv) ∧ ∀ k ∈ X.B.I.Kset, ∀ i,
    X.B.I.fmat k *ᵥ incl X.B.I (b kv i) -
      ∑ j, (((((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) •
        incl X.B.I (b kv j) ∈ wLf X (D.naut.plGw kv.1 kv.2)

theorem goodAt_of_fixRed {X : HidaSetting D} {red : X.B.I.Gf → G0g D.nd}
    {b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E} (hf : FixRed X red b) :
    ∀ k ∈ X.B.I.Kset, GoodAt X k (red k) :=
  fun k hk kv => ⟨b kv, (hf kv).1, (hf kv).2 k hk⟩

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyFreeSumIrreducibles
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
  GlobalTheory.LocLanglands Module

namespace GlobalTheory.WeilDeligne.IrrDecomp

theorem isIrreducible_of_equiv {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : V ≃ₗ[ℂ] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (hρ : ρ.IsIrreducible) :
    ρ'.IsIrreducible := by
  have he' : ∀ g v, e.symm (ρ' g v) = ρ g (e.symm v) := fun g v => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  let F : Subrepresentation ρ ≃o Subrepresentation ρ' :=
    { toFun := fun U => ⟨U.toSubmodule.map (e : V →ₗ[ℂ] V'), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ g u, U.apply_mem_toSubmodule g hu, he g u⟩⟩
      invFun := fun U => ⟨U.toSubmodule.map (e.symm : V' →ₗ[ℂ] V), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ' g u, U.apply_mem_toSubmodule g hu, he' g u⟩⟩
      left_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      right_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      map_rel_iff' := by
        intro U U'
        show U.toSubmodule.map (e : V →ₗ[ℂ] V') ≤ U'.toSubmodule.map (e : V →ₗ[ℂ] V') ↔
          U.toSubmodule ≤ U'.toSubmodule
        exact Submodule.map_le_map_iff_of_injective e.injective _ _ }
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  exact F.symm.isSimpleOrder

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.WeilDeligne.IrrDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExt
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

section Helpers

variable {F : Type} [Field F]

theorem spMap_comp_apply_field {Z : Scheme.{0}} {k K : Type} [Field k] [Field K] (σ : k →+* K) (p : Sp k ⟶ Z)
    (w : Sp K) (w' : Sp k) : (spMap σ ≫ p) w = p w' := by
  rw [Scheme.Hom.comp_apply]
  exact congrArg p (Subsingleton.elim (α := PrimeSpectrum k) _ _)

theorem val_spMap_comp_field {Ω : Type} [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {k K : Type} [Field k]
    [Field K] (σ : k →+* K) (p : Sp k ⟶ M.Z) (y : Ω) : M.val (spMap σ ≫ p) y = σ (M.val p y) := by
  by_cases hy : y ∈ M.O (p (IsLocalRing.closedPoint k))
  · have := RatModel.val_spMap_comp σ p specializes_rfl ⟨y, hy⟩
    rw [RatModel.valLoc_eq_val] at this
    exact this
  · rw [RatModel.val_of_notMem (y := p) (IsLocalRing.closedPoint k) hy, map_zero,
      RatModel.val_of_notMem (y := spMap σ ≫ p) (IsLocalRing.closedPoint K)
        (fun h' => hy (by convert h' using 2; exact (spMap_comp_apply_field σ p _ _).symm))]

theorem bears_spMap {ι : Type} {m : ι → ℕ} {X Y : Var F} (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn)
    (A : Mat m X.Fn) {k K : Type} [Field k] [Field K] (σ : k →+* K) (h : Mat m k) (p : Sp k ⟶ Y.X)
    (hb : Bears S φ A h p) : Bears S φ A (h.map σ) (spMap σ ≫ p) := by
  obtain ⟨A', hA', hP⟩ := hb
  refine ⟨A', ?_, ?_⟩
  · convert hA' using 2
    exact spMap_comp_apply_field σ p _ _
  have e : (A' * (A.map φ)⁻¹).map ((ratOf Y).val (spMap σ ≫ p)) =
      ((A' * (A.map φ)⁻¹).map ((ratOf Y).val p)).map σ := by
    funext τ
    ext i j
    exact val_spMap_comp_field (ratOf Y) σ p _
  rw [e, ← Mat.map_inv, ← Mat.map_mul]
  exact hP.map σ fun _ _ => trivial

end Helpers

theorem coBear_spMap : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (x : Sp k ⟶ X.X) (p₁ : Sp k ⟶ Y₁.X) (p₂ : Sp k ⟶ Y₂.X), CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap σ ≫ x) (spMap σ ≫ p₁) (spMap σ ≫ p₂) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ _ _ k K _ _ σ x p₁ p₂ hc
  obtain ⟨A, hA, h, hh, h1, h2⟩ := hc
  refine ⟨A, ?_, h.map σ, hh.map σ fun _ _ => trivial, bears_spMap S₁ φ₁ A σ h p₁ h1,
    bears_spMap S₂ φ₂ A σ h p₂ h2⟩
  convert hA using 2
  exact congrArg Eb.S (spMap_comp_apply_field σ x _ _)

end GlobalTheory.FlagBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExtStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (x : Sp k ⟶ X.X) (p₁ : Sp k ⟶ Y₁.X) (p₂ : Sp k ⟶ Y₂.X), CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap σ ≫ x) (spMap σ ≫ p₁) (spMap σ ≫ p₂) := by
  first | exact @GlobalTheory.FlagBundle.coBear_spMap | exact GlobalTheory.FlagBundle.coBear_spMap | (intros; apply GlobalTheory.FlagBundle.coBear_spMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointCarriesFrameFlagsOwnFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointCarriesFrameFlagsOwnFrame
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory

theorem FlagBundle.bears_self : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y : Var F) (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Reps Eb S φ f → ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ∃ A ∈ Eb.S ((w ≫ f) (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S φ A h w := by
  intro F _ ι _ m X Y Eb S φ f hR K _ w
  obtain ⟨A, hA⟩ := Eb.nonempty ((w ≫ f) (IsLocalRing.closedPoint K))
  obtain ⟨A', hA'⟩ := S.nonempty (w (IsLocalRing.closedPoint K))
  have hA₁ : A ∈ Eb.S (f (w (IsLocalRing.closedPoint K))) := (Scheme.Hom.comp_apply w f (IsLocalRing.closedPoint K)) ▸ hA
  have hN := hR.2.1 _ A' hA' A hA₁
  have hh : Par 0 ⊤ ((A' * (A.map φ)⁻¹).map ((ratOf Y).val w)) := by
    have hz := RatModel.range_eq_singleton (M := ratOf Y) w (IsLocalRing.closedPoint K)
    exact hN.map_of ((ratOf Y).val w) (RatModel.valHom (M := ratOf Y) w _ hz)
      (fun x => (RatModel.valHom_apply (M := ratOf Y) w _ hz x).symm)
  refine ⟨A, hA, _, hh, A', hA', ?_⟩
  rw [Mat.mul_inv hh.det_ne]
  exact Par.one
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointCarriesFrameFlagsOwnFrameStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y : Var F) (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Reps Eb S φ f → ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ∃ A ∈ Eb.S ((w ≫ f) (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S φ A h w := by
  first | exact @GlobalTheory.FlagBundle.bears_self | exact GlobalTheory.FlagBundle.bears_self | (intros; apply GlobalTheory.FlagBundle.bears_self <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPowClassNumber
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2
open GlobalTheory.Mem.Chr hiding HChar HChar.valTw HChar.val_mul HChar.val_inv
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.ChiVal

theorem val_pow_classNumber {L : Type} [Field L] [NumberField L] (ξ : HChar L) (hu : ∀ v, ξ.UnrAt v) (hi : ∀ k, ξ.inf k = 1)
    (v : HeightOneSpectrum (𝓞 L)) : ξ.val v ^ classNumber L = 1 := by
  obtain ⟨γ, h0, hγ⟩ := GlobalTheory.Mem.FieldsEx.exists_gen v.asIdeal v.ne_bot
  have h1 : (γ : L) ≠ 0 := by exact_mod_cast h0
  have h2 := GlobalTheory.Mem.ValPow.inf_mul_val_pow L ξ ∅ (fun w _ => hu w) (fun w hw => absurd hw (Finset.notMem_empty w)) v
    (Finset.notMem_empty v) (classNumber L) (Units.mk0 _ h1)
    (by rw [← FractionalIdeal.coeIdeal_pow, hγ, FractionalIdeal.coeIdeal_span_singleton]; rfl)
    (fun w hw => absurd hw (Finset.notMem_empty w))
  rwa [hi, one_mul] at h2

theorem mem_of_pow_eq_one (M : Subfield ℂ) {n : ℕ} (hn : n ≠ 0)
    (hM : Complex.exp (2 * Real.pi * Complex.I / (n : ℕ)) ∈ M) {x : ℂ} (hx : x ^ n = 1) : x ∈ M := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, -, rfl⟩ := (Complex.isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one hx
  exact pow_mem hM i

theorem val_sq_eq {L : Type} [Field L] [NumberField L] (η : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    ((η.val v : ℂˣ) : ℂ) * ((η.val v : ℂˣ) : ℂ) = η.valTw (1 / 2) v ^ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by
  have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(((1 / 2 : ℝ)) : ℂ))) ^ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = 1 := by
    rw [sq, ← Complex.cpow_add _ _ h0, show -(((1 / 2 : ℝ)) : ℂ) + -(((1 / 2 : ℝ)) : ℂ) = -1 by push_cast; ring,
      Complex.cpow_neg_one, inv_mul_cancel₀ h0]
  unfold HChar.valTw
  rw [mul_pow, mul_assoc, h1, mul_one, sq]

theorem chiId_mem {L : Type} [Field L] [NumberField L] (χ : HChar L) (M : Subfield ℂ)
    (h : ∀ w, ((χ.val w : ℂˣ) : ℂ) ∈ M) (𝔞 : Submodule (𝓞 L) L) : chiId χ 𝔞 ∈ M := by
  unfold chiId
  refine finprod_induction (fun u : ℂˣ => (u : ℂ) ∈ M) (one_mem M) (fun a b ha hb => mul_mem ha hb) fun w => ?_
  rw [Units.val_pow_eq_pow_val]
  exact pow_mem (h w) _

theorem chi_values : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok →
    (∀ w, ∃ k : B.LL, B.embLL k = ((I.C.chiPsi.val w : ℂˣ) : ℂ)) ∧ ∀ 𝔞, ∃ k : B.LL, B.embLL k = I.chi 𝔞 := by
  intro B X I h
  have key : ∀ w, ((I.C.chiPsi.val w : ℂˣ) : ℂ) ∈ B.embLL.fieldRange := by
    intro w
    have hc := I.C.isEta.sq_chiPsi.div_cls I.C.isChi
    have h1 := val_pow_classNumber _ hc.unr hc.inf w
    obtain ⟨z, -, hz⟩ := B.roots_Ks' (classNumber B.host.E) (by simp)
    have h2 : (((I.C.chiPsi * (I.C.eta * I.C.eta)⁻¹).val w : ℂˣ) : ℂ) ∈ B.embLL.fieldRange :=
      mem_of_pow_eq_one B.embLL.fieldRange (classNumber_ne_zero B.host.E) ⟨z, hz⟩
        (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
    have h3 : I.C.eta.valTw (1 / 2) w ∈ B.embLL.fieldRange := ⟨_, h.ch_tied.etaVal w⟩
    have h4 : I.C.chiPsi.val w = (I.C.chiPsi * (I.C.eta * I.C.eta)⁻¹).val w * (I.C.eta.val w * I.C.eta.val w) := by
      rw [HChar.val_mul, HChar.val_inv, HChar.val_mul, inv_mul_cancel_right]
    rw [h4, Units.val_mul, Units.val_mul (I.C.eta.val w), val_sq_eq]
    exact mul_mem h2 (mul_mem (pow_mem h3 2) (natCast_mem _ _))
  exact ⟨key, fun 𝔞 => chiId_mem _ _ key 𝔞⟩

end GlobalTheory.Mem.ChiVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubStdL
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2
open Neutral.B1 hiding localIdele
open GlobalTheory.Mem.Chr hiding HChar ordF IsChiPsi unif atFin

namespace GlobalTheory.Mem.ChiDet

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem detId_stdL (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)) : Th.detId H (Th.stdL H N) M = detSub M := by
  classical
  unfold Th.detId detSub
  congr 1
  ext z
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨fun j i => A i j, fun j => ?_, (Matrix.det_transpose A).symm⟩
    have h1 : (Pi.single j 1 : Fin N → H.E) ∈ Th.stdL H N := fun k _ => by
      by_cases e : k = j
      · subst e
        rw [Pi.single_eq_same]
        exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne e]
        exact Submodule.zero_mem _
    have h2 := hA _ h1
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(Matrix.of x).transpose, fun v hv => ?_, (Matrix.det_transpose _).symm⟩
    choose b hb using fun i => Submodule.mem_one.1 (hv i trivial)
    have e : (Matrix.of x).transpose.mulVec v = ∑ i, b i • x i := by
      funext j
      rw [Finset.sum_apply]
      show ∑ i, x i j * v i = ∑ i, b i • x i j
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, hb, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx i)

theorem ordSub_detSub_stdL (N : ℕ) (w : HeightOneSpectrum (𝓞 H.E)) : ordSub w (detSub (Th.stdL H N)) = 0 := by
  rw [← detId_stdL, detId_std, Submodule.one_eq_span]
  have h := ordSub_span_singleton w (1 : H.Eˣ)
  rw [Units.val_one] at h
  rw [h]
  simp [ordF]

theorem tildeD_eq_chiId : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsChiPsi H χ → ∀ (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)), Submodule.IsLattice H.E M → ∀ x : DtT H, (QuotientGroup.mk x : DtT H ⧸ UOT H) = relDetT H N (Th.stdL H N) M → ((tildeD H χ x : ℂˣ) : ℂ) = chiId χ (Th.detId H (Th.stdL H N) M) := by
  intro R H χ hχ N M hM x hx
  have hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
    (KerDet.kernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v y hy _ => hχ.unr v y hy) fun v _ => hχ.unr v
  have hU := (ChiLaws.chi_laws R H χ hχ).1
  have hfin : {w : HeightOneSpectrum (𝓞 H.E) | ordSub w (detSub M) ≠ 0}.Finite := by
    by_cases h : ∃ k : H.Eˣ, (k : H.E) ∈ detSub M
    · obtain ⟨k, hk⟩ := h
      exact DetOrd.ordSub_finite (DetOrd.isFractional_detSub M hM.fg) k hk
    · have hz : ∀ w, ordSub w (detSub M) = 0 := by
        intro w
        unfold ordSub
        have he : {n : ℤ | ∃ k : H.Eˣ, (k : H.E) ∈ detSub M ∧ ordF w k = n} = ∅ := by
          ext n
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨k, hk, _⟩
          exact h ⟨k, hk⟩
        rw [he]
        simp
      simp [hz]
  unfold relDetT at hx
  have h1 := hU _ (QuotientGroup.eq.1 hx)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [h1, tildeD_mk H hK, detId_stdL]
  unfold chiId
  congr 1
  simp only [ordSub_detSub_stdL, sub_zero]
  have h2 : Function.HasFiniteMulSupport fun w : HeightOneSpectrum (𝓞 H.E) =>
      localIdele H.E w (atFin w (unif w)) ^ (ordSub w (detSub M)).toNat := by
    refine hfin.subset fun w hw h0 => hw ?_
    simp only [h0, Int.toNat_zero, pow_zero]
  refine ((χ.1.comp (finPartI H.E)).map_finprod h2).trans (finprod_congr fun w => ?_)
  rw [map_pow, MonoidHom.comp_apply, KerDet.finPartI_localIdele]
  rfl

end GlobalTheory.Mem.ChiDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BddAboveSubDegsOfJointlyMono
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)

namespace GlobalTheory.VB

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]

theorem IsProjCurve.bddAbove_subDegs_of_kernel (hC : IsProjCurve k C) {B Q : C.Modules}
    [IsFiniteQC Q] (p : B ⟶ Q) (hK : BddAbove (subDegs k (kernel p)))
    (hQ : BddAbove (subDegs k Q)) : BddAbove (subDegs k B) := by
  have := hC.isNoetherian
  obtain ⟨a, ha⟩ := hK
  obtain ⟨b, hb⟩ := hQ
  refine ⟨a + b, ?_⟩
  rintro _ ⟨G, i, hi, rfl⟩
  have := hi.mono
  have := hi.isFiniteQC
  let q : G ⟶ Q := i ≫ p
  have hKG : IsFiniteQC (kernel q) := .of_mono (kernel.ι q)
  have hm : Mono (Abelian.factorThruCoimage q) := inferInstance
  have hc : IsFiniteQC (cokernel (kernel.ι q)) := .of_mono (Abelian.factorThruCoimage q)
  let j : kernel q ⟶ kernel p := kernel.lift p (kernel.ι q ≫ i) (by
    rw [Category.assoc]; exact kernel.condition q)
  have hj : Mono j := mono_of_mono_fac (kernel.lift_ι p (kernel.ι q ≫ i) _)
  have h₁ : deg k (kernel q) ≤ a := ha (IsCohSub.deg_mem (i := j) ⟨hj, hKG⟩)
  have h₂ : deg k (cokernel (kernel.ι q)) ≤ b :=
    hb (IsCohSub.deg_mem (i := Abelian.factorThruCoimage q) ⟨hm, hc⟩)
  rw [hC.deg_cokernel] at h₂
  omega

theorem IsProjCurve.bddAbove_subDegs_of_jointly_mono (hC : IsProjCurve k C) {D : C.Modules}
    [IsFiniteQC D] (hD : BddAbove (subDegs k D)) (n : ℕ) :
    ∀ (Z : C.Modules) [IsFiniteQC Z] (ψ : Fin n → (Z ⟶ D)),
      (∀ (W : C.Modules) (g : W ⟶ Z), (∀ j, g ≫ ψ j = 0) → g = 0) →
      BddAbove (subDegs k Z) := by
  have := hC.isNoetherian
  induction n with
  | zero =>
    intro Z _ ψ h
    have hZ : IsZero Z := (IsZero.iff_id_eq_zero Z).2 (h Z (𝟙 Z) fun j => j.elim0)
    refine ⟨0, ?_⟩
    rintro _ ⟨G, i, hi, rfl⟩
    have := hi.mono
    exact (deg_eq_zero_of_isZero k (hZ.of_mono i)).le
  | succ n ih =>
    intro Z _ ψ h
    have : IsFiniteQC (kernel (ψ 0)) := .of_mono (kernel.ι (ψ 0))
    refine hC.bddAbove_subDegs_of_kernel (ψ 0)
      (ih (kernel (ψ 0)) (fun j => kernel.ι (ψ 0) ≫ ψ j.succ) fun W g hg => ?_) hD
    have h0 : g ≫ kernel.ι (ψ 0) = 0 := h W _ fun j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [Category.assoc, kernel.condition, comp_zero]
      · rw [Category.assoc]; exact hg j
    exact (cancel_mono (kernel.ι (ψ 0))).1 (h0.trans (zero_comp).symm)

theorem dualMap_sum {F G : C.Modules} {ι : Type} (s : Finset ι) (f : ι → (F ⟶ G)) :
    dualMap (∑ j ∈ s, f j) = ∑ j ∈ s, dualMap (f j) :=
  map_sum (AddMonoidHom.mk' (dualMap (F := F) (G := G)) dualMap_add) f s

theorem bddAbove_subDegs_of_isVB : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    [IsIntegral C], IsProjCurve k C → ∀ (F : C.Modules) (r : ℕ), IsVB F r →
    BddAbove (subDegs k F) := by
  intro k _ C _ _ hC F r hF
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hC.isProjOver
  have := hF.isFiniteQC
  have := hF.dual.isFiniteQC
  obtain ⟨m, n, φ, hφ⟩ := (hA.eventually_exists_epi_sigma (dual F)).exists
  have hL := Twist.isLB_lbZPow hA.isLB (-m)
  have hT := isVB_toMod hL
  let T := GlobalTheory.LB.toMod (lbZPow A (-m))
  have hD : IsVB (dual T) 1 := hT.dual
  have := hD.isFiniteQC
  have := Abelian.hasFiniteBiproducts (C := C.Modules)
  let φ' : (⨁ fun _ : Fin n => T) ⟶ dual F := (biproduct.isoCoproduct _).hom ≫ φ
  have hφ' : Epi φ' := inferInstance
  have hb := hF.isIso_toBidual_of_local_frames
  refine hC.bddAbove_subDegs_of_jointly_mono (hC.isMaxSubDeg_of_rank_one hD).bddAbove n F
    (fun j => cartierDualToBidual F ≫ dualMap (biproduct.ι (fun _ : Fin n => T) j ≫ φ')) fun W g hg => ?_
  have h0 : (g ≫ cartierDualToBidual F) ≫ dualMap φ' = 0 := by
    rw [← Category.comp_id ((g ≫ cartierDualToBidual F) ≫ dualMap φ'), ← dualMap_id,
      ← biproduct.total, dualMap_sum, Preadditive.comp_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := hg j
    rw [dualMap_comp, dualMap_comp] at *
    simp only [Category.assoc] at *
    rw [reassoc_of% this, zero_comp]
  have h1 : g ≫ cartierDualToBidual F = 0 := (cancel_mono (dualMap φ')).1 (h0.trans zero_comp.symm)
  exact (cancel_mono (cartierDualToBidual F)).1 (h1.trans zero_comp.symm)

end GlobalTheory.VB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerMaps
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem exists_teichmuller_maps : ∀ (g : ℕ) (hg : g.Prime), (∃ τ : Fb g hg →* ℂ, ∀ x y, x ≠ 0 → y ≠ 0 → τ x = τ y → x = y) ∧ ∀ (l : ℕ) (hl : l.Prime), ∃ ι : Fb g hg →* Fb l hl, ∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l → ι x = ι y → x = y :=
  fun g hg => ⟨@GaloisStage.exists_teichC g ⟨hg⟩, fun l hl => @GaloisStage.exists_iota g l ⟨hg⟩ ⟨hl⟩⟩

end GlobalTheory.MemN
end
