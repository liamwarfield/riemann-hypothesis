module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaEqJacobiSym
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open scoped Pointwise

namespace GlobalTheory.EtaJacobi

theorem jacobi_flip {p d : ℕ} (hp : Odd p) (hd : d % 4 = 3) :
    jacobiSym (p : ℤ) d = jacobiSym (-(d : ℤ)) p := by
  have hdo : Odd d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hp]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hdo]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four h hd]
    ring

theorem pow_prime_pow {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : p ≠ 2)
    (m : ℤ) (x : k) (hx : x ^ 2 = (m : k)) (f : ℕ) :
    x ^ (p ^ f) = ((legendreSym p m ^ f : ℤ) : k) * x := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  have h1 : x ^ p = ((legendreSym p m : ℤ) : k) * x := by
    have h := congrArg (ZMod.castHom (dvd_refl p) k) (legendreSym.eq_pow p m)
    rw [map_intCast, map_pow, map_intCast] at h
    rw [h, ← hx, ← pow_mul, ← pow_succ]
    congr 1
    omega
  have h2 : ∀ z : ℤ, (z : k) ^ p = z := fun z => by
    have := map_intCast (frobenius k p) z
    rwa [frobenius_def] at this
  induction f with
  | zero => simp
  | succ f ih =>
    rw [pow_succ, pow_mul, ih, mul_pow, h2, h1]
    push_cast
    ring

section CM

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

theorem frob_eq
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP0 : P ≠ ⊥) (x : 𝓞 K) :
    (if (Ideal.primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 1 then IsCMField.complexConj K • x else x)
      - x ^ Ideal.absNorm (P.under (𝓞 K⁺)) ∈ P := by
  have h𝔭 : P.under (𝓞 K⁺) ≠ ⊥ := Ideal.under_ne_bot (𝓞 K⁺) hP0
  have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have hfin : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  obtain ⟨g, hg⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K⁺) (K ≃ₐ[K⁺] K) P
  have hN : Ideal.absNorm (P.under (𝓞 K⁺)) = Nat.card (𝓞 K⁺ ⧸ P.under (𝓞 K⁺)) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hg' : ∀ y : 𝓞 K, g • y - y ^ Ideal.absNorm (P.under (𝓞 K⁺)) ∈ P := by
    intro y; rw [hN]; exact hg y
  rcases Eta.cases K g with rfl | rfl
  · have hne : ¬ (Ideal.primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 1 := by
      intro h1
      rcases Eta.split_or_inert K hunr (P.under (𝓞 K⁺)) h𝔭 with h | ⟨-, h⟩
      · omega
      rw [Ideal.inertiaDegIn_eq_inertiaDeg (P.under (𝓞 K⁺)) P (K ≃ₐ[K⁺] K)] at h
      have hc := Ideal.absNorm_pow_inertiaDeg (P.under (𝓞 K⁺)) P
      rw [h, Ideal.absNorm_apply P, Submodule.cardQuot_apply] at hc
      set N := Ideal.absNorm (P.under (𝓞 K⁺)) with hNdef
      have hN0 : N ≠ 0 := by rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔭
      have hN1 : N ≠ 1 := by
        rw [hNdef, Ne, Ideal.absNorm_eq_one_iff]
        exact Ideal.IsPrime.ne_top inferInstance
      letI := Ideal.Quotient.field P
      letI := Fintype.ofFinite (𝓞 K ⧸ P)
      have hall : ∀ u : (𝓞 K ⧸ P)ˣ, u ^ (N - 1) = 1 := by
        intro u
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 K ⧸ P)
        have h3 := Ideal.Quotient.eq.mpr (hg' y)
        rw [one_smul, map_pow, hy] at h3
        have h4 : u ^ (N - 1) * u = 1 * u := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul]
          ext
          rw [Units.val_pow_eq_pow_val]
          exact h3.symm
        exact mul_right_cancel h4
      have hd := (FiniteField.forall_pow_eq_one_iff (𝓞 K ⧸ P) (N - 1)).mp hall
      rw [← Nat.card_eq_fintype_card, ← hc] at hd
      have := Nat.le_of_dvd (by omega) hd
      have h5 : N * 2 ≤ N * N := Nat.mul_le_mul_left _ (by omega)
      rw [sq] at this
      omega
    rw [if_neg hne]
    simpa using hg' x
  · have hst : IsCMField.complexConj K • P = P := hg.mem_stabilizer
    have h1 : (Ideal.primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 1 := by
      rcases Eta.split_or_inert K hunr (P.under (𝓞 K⁺)) h𝔭 with h | ⟨h, -⟩
      · exact absurd hst ((Eta.ncard_eq_two_iff K hunr P hP0).mp h)
      · exact h
    rw [if_pos h1]
    exact hg' x

end CM

theorem card_aboveF {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F]
    [Algebra F L] (v : HeightOneSpectrum (𝓞 F)) :
    (aboveF (L := L) F v).card = (Ideal.primesOver v.asIdeal (𝓞 L)).ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _
    (f := HeightOneSpectrum.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)]
  congr 1
  ext Q
  simp only [aboveF, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, rfl, rfl⟩
    exact ⟨P.isPrime, ⟨rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      HeightOneSpectrum.ext h2.over.symm, rfl⟩


open Classical in
theorem eta_eq_jacobiSym : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (v : HeightOneSpectrum (𝓞 H.F)),
    ((H.d : ℕ) : 𝓞 H.F) ∉ v.asIdeal →
    (if (aboveF (L := H.E) H.F v).card = 1 then (-1 : ℤ) else 1) =
      jacobiSym (Ideal.absNorm v.asIdeal : ℕ) H.d := by
  intro R H v hv
  have hCM : IsCMField H.E := H.isCMField_hostE
  have hcc : ∀ x : H.E, IsCMField.complexConj H.E x = H.conj x := fun x => by
    apply H.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, H.conjE_apply]
  have hsm : ∀ x : 𝓞 H.E, IsCMField.complexConj H.E • x = H.conj • x := fun x =>
    RingOfIntegers.ext (hcc x)
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  rw [card_aboveF]
  have hvp := v.isPrime
  obtain ⟨⟨P, hPp, hPo⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver v.asIdeal (𝓞 H.E)))
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hunder : P.under (𝓞 H.F) = v.asIdeal := hPo.over.symm
  have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have hfin : Finite (𝓞 H.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  letI := Ideal.Quotient.field P
  obtain ⟨p, hchar⟩ := CharP.exists (𝓞 H.E ⧸ P)
  have hp : p.Prime := CharP.char_is_prime (𝓞 H.E ⧸ P) p
  haveI : Fact p.Prime := ⟨hp⟩
  have hpP : (p : 𝓞 H.E) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  have hPZ : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hpP
  have hvZ : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.tower_bot P v.asIdeal _
  have hN := Ideal.pow_inertiaDeg p v.asIdeal
  set f := v.asIdeal.inertiaDeg ℤ
  rw [← hN, Nat.cast_pow, jacobiSym.pow_left]
  by_cases hp2 : p = 2
  · have h2N : p ∣ H.condN := by
      rw [hp2]
      exact ((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans H.tower_dvd).trans
        (Dvd.dvd.mul_right (dvd_mul_right _ _) _)
    have he := H.der.eta.2.2 p h2N P
    unfold Formalism.HC.HostRaw.etaF at he
    change (if (Ideal.primesOver (P.under (𝓞 H.F)) (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 at he
    rw [hunder] at he
    have h2 : (Ideal.primesOver v.asIdeal (𝓞 H.E)).ncard = 2 := by
      by_contra hc
      rw [if_neg hc] at he
      exact absurd he (by decide)
    have hj : jacobiSym (p : ℤ) H.d = 1 := by
      rw [hp2, Nat.cast_ofNat, jacobiSym.at_two (Nat.odd_iff.mpr (by omega)),
        ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_pos (by omega)]
    rw [h2, hj, if_neg (by decide), one_pow]
  · have hunr : ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ≠ ⊥ →
        ¬ ∀ x : 𝓞 H.E, IsCMField.complexConj H.E • x - x ∈ P :=
      fun P hP hP0 hx => H.der.unramEF P hP hP0 (fun x => hsm x ▸ hx x)
    have hsq := H.sqd_sq
    have hint : IsIntegral ℤ (H.sqd) := by
      refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
      rw [hsq]
      exact (isIntegral_natCast _).neg
    let β : 𝓞 H.E := ⟨_, hint⟩
    have hβsq : β ^ 2 = -(H.d : 𝓞 H.E) := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 H.E) H.E (β ^ 2) = algebraMap (𝓞 H.E) H.E (-(H.d : 𝓞 H.E))
      rw [map_pow, map_neg, map_natCast]
      exact hsq
    have hcβ : IsCMField.complexConj H.E • β = -β := by
      apply RingOfIntegers.ext
      have h1 := H.galE_bE H.conj
      rw [H.galE_conjE] at h1
      change IsCMField.complexConj H.E (H.sqd) = -(H.sqd)
      rw [hcc, h1]
      simp [Formalism.HC.Frame.cc, c0]
    have hfr := Ideal.Quotient.eq.mpr (frob_eq H.E hunr P hP0 β)
    rw [hunder, ← hN, map_pow, hcβ] at hfr
    have hx : (Ideal.Quotient.mk P β) ^ 2 = ((-(H.d : ℤ) : ℤ) : 𝓞 H.E ⧸ P) := by
      rw [← map_pow, hβsq]; simp
    have hdP : ((H.d : ℕ) : 𝓞 H.E ⧸ P) ≠ 0 := by
      intro h0
      apply hv
      rw [← hunder, Ideal.mem_comap, map_natCast, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact h0
    have hx0 : Ideal.Quotient.mk P β ≠ 0 := by
      intro h0
      rw [h0] at hx
      apply hdP
      simpa using hx
    rw [pow_prime_pow p hp2 _ _ hx f] at hfr
    rw [jacobi_flip (hp.odd_of_ne_two hp2) (by omega), ← jacobiSym.legendreSym.to_jacobiSym]
    have hs : legendreSym p (-(H.d : ℤ)) ^ f = 1 ∨ legendreSym p (-(H.d : ℤ)) ^ f = -1 := by
      have hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_neg, Int.natCast_dvd_natCast] at h0
        exact hdP ((CharP.cast_eq_zero_iff _ p _).mpr h0)
      rcases legendreSym.eq_one_or_neg_one p hne with h1 | h1
      · left; rw [h1, one_pow]
      · rw [h1]; exact neg_one_pow_eq_or ℤ f
    have h2 : (2 : 𝓞 H.E ⧸ P) ≠ 0 := by
      intro h0
      have : p ∣ 2 := (CharP.cast_eq_zero_iff (𝓞 H.E ⧸ P) p 2).mp (by simpa using h0)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    have hneg : Ideal.Quotient.mk P β ≠ -Ideal.Quotient.mk P β := by
      intro h0
      have : 2 * Ideal.Quotient.mk P β = 0 := by linear_combination h0
      exact (mul_ne_zero h2 hx0) this
    split_ifs at hfr ⊢ with hc
    · rcases hs with hs | hs
      · rw [hs, map_neg] at hfr
        exact absurd (by simpa using hfr.symm) hneg
      · exact hs.symm
    · rcases hs with hs | hs
      · exact hs.symm
      · rw [hs] at hfr
        exact absurd (by simpa using hfr) hneg

end GlobalTheory.EtaJacobi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitNormOfIsCoprime
open NumberField IsDedekindDomain

namespace GlobalTheory.NormSquareRamified

theorem dvd_of_mul_sq {p : ℕ} (hp : p.Prime) {q D : ℤ} (hq : ¬ (p : ℤ) ∣ q) (B : ℚ)
    (h : ((q * p : ℤ) : ℚ) * B ^ 2 = D) : (p : ℤ) ∣ D := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_contra hD
  have hden : (B.den : ℚ) ≠ 0 := by exact_mod_cast B.den_nz
  have h1 : q * p * B.num ^ 2 = D * (B.den : ℤ) ^ 2 := by
    have hB : (B.num : ℚ) = B * B.den := by
      rw [Rat.mul_den_eq_num]
    have : ((q * p * B.num ^ 2 : ℤ) : ℚ) = ((D * (B.den : ℤ) ^ 2 : ℤ) : ℚ) := by
      push_cast at h ⊢
      rw [hB, ← h]; ring
    exact_mod_cast this
  have h2 : (p : ℤ) ∣ (B.den : ℤ) := by
    have : (p : ℤ) ∣ D * (B.den : ℤ) ^ 2 := ⟨q * B.num ^ 2, by rw [← h1]; ring⟩
    exact hpp.dvd_of_dvd_pow ((hpp.dvd_or_dvd this).resolve_left hD)
  obtain ⟨c, hc⟩ := h2
  have h3 : q * B.num ^ 2 = p * (D * c ^ 2) := by
    apply mul_left_cancel₀ hpp.ne_zero
    rw [hc] at h1
    linear_combination h1
  have h4 : (p : ℤ) ∣ B.num :=
    hpp.dvd_of_dvd_pow ((hpp.dvd_or_dvd ⟨_, h3⟩).resolve_left hq)
  have h5 : IsCoprime B.num (B.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using B.reduced
  exact hpp.not_isUnit (h5.isUnit_of_dvd' h4 ⟨c, hc⟩)

theorem isUnit_norm_of_isCoprime {F : Type*} [Field F] [NumberField F] (n : ℕ) (y : 𝓞 F)
    (h : IsCoprime y (n : 𝓞 F)) : IsUnit ((Algebra.norm ℤ y : ℤ) : ZMod n) := by
  classical
  obtain ⟨u, v, huv⟩ := h
  let b := RingOfIntegers.basis F
  have h1 : u * y = 1 - (n : ℤ) • v := by
    rw [← huv]; simp [mul_comm]
  have h2 : ((Algebra.norm ℤ (u * y) : ℤ) : ZMod n) = 1 := by
    rw [Algebra.norm_eq_matrix_det b, h1, map_sub, map_one, map_zsmul]
    have := (Int.castRingHom (ZMod n)).map_det (1 - (n : ℤ) • Algebra.leftMulMatrix b v)
    rw [eq_intCast] at this
    rw [this, map_sub, map_one, map_zsmul]
    have h0 : (n : ℤ) • (Int.castRingHom (ZMod n)).mapMatrix (Algebra.leftMulMatrix b v) = 0 := by
      ext i j
      simp
    rw [h0, sub_zero, Matrix.det_one]
  rw [map_mul, Int.cast_mul, mul_comm] at h2
  exact IsUnit.of_mul_eq_one _ h2

theorem exists_sq_sub_norm {F : Type*} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) {q : ℤ}
    (hq : ¬ (p : ℤ) ∣ q) (s : F) (hs : s * s = ((q * p : ℤ) : F)) (y : 𝓞 F) :
    ∃ A : ℤ, (p : ℤ) ∣ A ^ 2 - 4 * Algebra.norm ℤ y := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set m : ℚ := ((q * p : ℤ) : ℚ) with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Int.cast_ne_zero]
    exact mul_ne_zero (fun h => hq (h ▸ dvd_zero _)) hpp.ne_zero
  have : Fact (∀ r : ℚ, r ^ 2 ≠ m + 0 * r) := ⟨fun r hr => by
    rw [zero_mul, add_zero] at hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hm0 (by rw [← hr]; simp)
    have : m * r⁻¹ ^ 2 = ((1 : ℤ) : ℚ) := by
      rw [← hr]; field_simp; simp
    exact hpp.not_dvd_one (dvd_of_mul_sq hp hq _ this)⟩
  let K := QuadraticAlgebra ℚ m 0
  let φ : K →ₐ[ℚ] F := QuadraticAlgebra.lift ⟨s, by
    rw [hs, zero_smul, add_zero, hm, Algebra.smul_def, mul_one, map_intCast]⟩
  let : Algebra K F := φ.toRingHom.toAlgebra
  have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : Module.Finite ℚ K := Module.Finite.of_basis (QuadraticAlgebra.basis m 0)
  set w : K := Algebra.norm K (y : F) with hw
  have hwi : IsIntegral ℤ w := Algebra.isIntegral_norm K y.isIntegral_coe
  have hn : ((Algebra.norm ℤ y : ℤ) : ℚ) = w.norm := by
    rw [Algebra.coe_norm_int, ← Algebra.norm_norm (S := K), ← hw,
      ← QuadraticAlgebra.det_toLinearMap_eq_norm, Algebra.norm_apply]
    rfl
  have hst : IsIntegral ℤ (star w) := hwi.map (starRingEnd K).toIntAlgHom
  have htr : IsIntegral ℤ (QuadraticAlgebra.trace w) := by
    have := hwi.add hst
    rw [← QuadraticAlgebra.algebraMap_trace_eq_add_star] at this
    exact (isIntegral_algebraMap_iff ).mp this
  obtain ⟨A, hA⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htr
  refine ⟨A, dvd_of_mul_sq hp hq (2 * w.im) ?_⟩
  rw [← hm]
  rw [eq_intCast] at hA
  push_cast
  rw [hA, hn, QuadraticAlgebra.trace_def, QuadraticAlgebra.norm_def]
  ring

theorem jacobiSym_norm_eq_one {F : Type*} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {q : ℤ} (hq : ¬ (p : ℤ) ∣ q) (s : F) (hs : s * s = ((q * p : ℤ) : F)) (y : 𝓞 F)
    (hy : IsCoprime y (p : 𝓞 F)) : jacobiSym (Algebra.norm ℤ y) p = 1 := by
  have := Fact.mk hp
  obtain ⟨A, hA⟩ := exists_sq_sub_norm hp hq s hs y
  have hu := isUnit_norm_of_isCoprime p y hy
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hu.ne_zero]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hA
  push_cast at hA
  refine ⟨(A : ZMod p) / 2, ?_⟩
  field_simp
  linear_combination -hA

theorem host_jacobiSym_norm : ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R) (y : 𝓞 H.F),
    IsCoprime y ((H.d : ℕ) : 𝓞 H.F) → jacobiSym (Algebra.norm ℤ y) H.d = 1 := by
  intro R H y hy
  obtain ⟨hq, hd, hqd, -, hd2⟩ := H.hypOdd
  have hneg : ∀ (z : ℂ) (n : ℕ), 0 < n → z ^ 2 = -(n : ℂ) → star z = -z := by
    intro z n hn h
    have hr : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [sq, Complex.mul_re, Complex.mul_im] at h1 h2
    have hre : z.re = 0 := by
      have h3 : z.re * z.im = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · rw [h4] at h1; nlinarith [sq_nonneg z.re]
    apply Complex.ext <;> simp [hre]
  have hmem : H.sqq * H.sqd ∈ H.F := by
    intro φ
    have ha : star (φ H.sqq) = -φ H.sqq :=
      hneg _ H.q hq.pos (by rw [← map_pow, H.sqq_sq]; simp)
    have hb : star (φ H.sqd) = -φ H.sqd :=
      hneg _ H.d hd.pos (by rw [← map_pow, H.sqd_sq]; simp)
    rw [map_mul, star_mul, ha, hb]; ring
  refine jacobiSym_norm_eq_one hd hd2 (q := (H.q : ℤ)) ?_ ⟨_, hmem⟩ ?_ y hy
  · intro h
    exact hqd ((Nat.prime_dvd_prime_iff_eq hd hq).mp (by exact_mod_cast h)).symm
  · apply Subtype.ext
    change (H.sqq * H.sqd) * (H.sqq * H.sqd) = _
    have : (H.sqq * H.sqd) * (H.sqq * H.sqd) = H.sqq ^ 2 * H.sqd ^ 2 := by ring
    rw [this, H.sqq_sq, H.sqd_sq]
    push_cast
    ring

end GlobalTheory.NormSquareRamified
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticCharProductFormulaCMHost
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.EtaProduct

section General

variable {F : Type} [Field F] [NumberField F]

theorem val_ne_zero (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) : v.valuation F (a : F) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr a.ne_zero

theorem ordF_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    ordF v (a * b) = ordF v a + ordF v b := by
  unfold ordF
  rw [Units.val_mul, map_mul, WithZero.log_mul (val_ne_zero v a) (val_ne_zero v b)]
  ring

theorem val_eq_exp (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    v.valuation F (a : F) = WithZero.exp (-ordF v a) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log (val_ne_zero v a)]

theorem finite_ordF (a : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordF v a ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (a : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((a⁻¹ : Fˣ) : F))).subset fun v hv => ?_
  have h1 := val_eq_exp v a
  simp only [HeightOneSpectrum.Support, Set.mem_union, Set.mem_ofPred_eq, Units.val_inv_eq_inv_val,
    map_inv₀, h1, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hv ⊢
  omega

theorem exists_val_eq (T : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    ∃ b : Fˣ, ∀ w ∈ T, w.valuation F (b : F) = WithZero.exp (-(n w : ℤ)) := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
  · exact ⟨1, by simp⟩
  choose π hπ using fun w : HeightOneSpectrum (𝓞 F) => w.intValuation_exists_uniformizer
  obtain ⟨y, hy⟩ := exists_forall_sub_mem_ideal (s := T) (fun w => w.asIdeal) (fun w => n w + 1)
    (fun w _ => w.prime) (fun w _ w' _ h h' => h (HeightOneSpectrum.ext h'))
    (fun w => π w ^ n w)
  have key : ∀ w ∈ T, w.intValuation y = WithZero.exp (-(n w : ℤ)) := by
    intro w hw
    have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem w _ _).mpr (hy w hw)
    have h2 : w.intValuation (π w ^ n w) = WithZero.exp (-(n w : ℤ)) := by
      rw [map_pow, hπ, ← WithZero.exp_nsmul]; simp
    rw [← h2]
    apply Valuation.map_eq_of_sub_lt
    refine h1.trans_lt ?_
    rw [h2, WithZero.exp_lt_exp]
    push_cast
    omega
  have hy0 : (y : F) ≠ 0 := by
    intro h
    have h' : y = 0 := RingOfIntegers.ext h
    have := key w₀ hw₀
    rw [h', map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨Units.mk0 _ hy0, fun w hw => ?_⟩
  rw [← key w hw]
  exact HeightOneSpectrum.valuation_of_algebraMap w y

omit [NumberField F] in
theorem sup_eq_top_of_forall {m : 𝓞 F} (hm : m ≠ 0) (D : Ideal (𝓞 F))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal → ¬ D ≤ v.asIdeal) :
    D ⊔ Ideal.span {m} = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmM : m ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self m))
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    exact hm hmM
  exact h ⟨M, hM.isPrime, hM0⟩ hmM (le_sup_left.trans hle)

theorem exists_coprime_mul_eq {m : 𝓞 F} (hm : m ≠ 0) (a : F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal → v.valuation F a = 1) :
    ∃ y z : 𝓞 F, z ≠ 0 ∧ IsCoprime y m ∧ IsCoprime z m ∧ a * z = y := by
  let D : Ideal (𝓞 F) :=
    Submodule.comap (LinearMap.toSpanSingleton (𝓞 F) F a) (1 : Submodule (𝓞 F) F)
  have hD : ∀ z, z ∈ D ↔ ∃ y : 𝓞 F, a * z = y := by
    intro z
    simp only [D, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one,
      Algebra.smul_def]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, by rw [mul_comm]; exact hy.symm⟩
    · rintro ⟨y, hy⟩; exact ⟨y, by rw [mul_comm]; exact hy.symm⟩
  have htop : D ⊔ Ideal.span {m} = ⊤ := by
    apply sup_eq_top_of_forall hm
    intro v hv hle
    obtain ⟨y, z, hz⟩ := v.exists_primeCompl_mul_eq_of_integer a (h v hv).le
    exact z.2 (hle ((hD z).mpr ⟨y, hz⟩))
  obtain ⟨z, hzD, hz0, hzc⟩ : ∃ z ∈ D, z ≠ 0 ∧ IsCoprime z m := by
    obtain ⟨z, hz, t, ht, hzt⟩ := Submodule.mem_sup.mp (htop.ge (Submodule.mem_top (x := 1)))
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    by_cases hz0 : z = 0
    · obtain ⟨y, z', hz', hyz⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
      have hz'0 := nonZeroDivisors.ne_zero hz'
      refine ⟨z', (hD z').mpr ⟨y, ?_⟩, hz'0, 0, s, by rw [← hzt, hz0]; ring⟩
      rw [← hyz]
      exact div_mul_cancel₀ _ (RingOfIntegers.coe_ne_zero_iff.mpr hz'0)
    · exact ⟨z, hz, hz0, 1, s, by rw [one_mul]; exact hzt⟩
  obtain ⟨y, hy⟩ := (hD z).mp hzD
  refine ⟨y, z, hz0, ?_, hzc, hy⟩
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
  apply sup_eq_top_of_forall hm
  intro v hv hle
  rw [Ideal.span_singleton_le_iff_mem] at hle
  have hzv : z ∉ v.asIdeal := fun hz => by
    obtain ⟨r, s, hrs⟩ := hzc
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
      (hrs ▸ add_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_left _ _ hv)))
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)] at hle hzv
  apply hzv
  have := congrArg (v.valuation F) hy
  rw [map_mul, h v hv, one_mul] at this
  exact this.trans_lt hle

variable (L : Type) [Field L] [NumberField L] [Algebra F L]

theorem etaFin_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    etaFin (L := L) F v (a * b) = etaFin (L := L) F v a * etaFin (L := L) F v b := by
  unfold etaFin
  split_ifs
  · rw [ordF_mul, zpow_add]
  · simp

theorem etaFin_finite (a : Fˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => etaFin (L := L) F v a := by
  refine (finite_ordF a).subset fun v hv h0 => hv ?_
  simp [etaFin, h0]

omit [NumberField F] in
theorem etaInf_mul_abs [IsTotallyReal F] (w : InfinitePlace F) (a : Fˣ) :
    (etaInf F w a : ℂ) * (w (a : F) : ℝ) = w.embedding (a : F) := by
  have hr := IsTotallyReal.complexEmbedding_isReal w.embedding
  have h1 : w.embedding (a : F) = (hr.embedding (a : F) : ℝ) :=
    (ComplexEmbedding.IsReal.coe_embedding_apply hr _).symm
  rw [← InfinitePlace.norm_embedding_eq, etaInf, h1, Complex.ofReal_re, Complex.norm_real,
    Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_neg h]; simp
  · rw [abs_of_nonneg (not_lt.mp h)]; simp

omit [NumberField F] in
theorem etaInf_mul [IsTotallyReal F] (w : InfinitePlace F) (a b : Fˣ) :
    etaInf F w (a * b) = etaInf F w a * etaInf F w b := by
  have h := etaInf_mul_abs w (a * b)
  rw [Units.val_mul, map_mul, map_mul, ← etaInf_mul_abs w a, ← etaInf_mul_abs w b] at h
  have ha : ((w (a : F) : ℝ) : ℂ) ≠ 0 := by simp
  have hb : ((w (b : F) : ℝ) : ℂ) ≠ 0 := by simp
  apply Units.ext
  apply mul_right_cancel₀ (mul_ne_zero ha hb)
  push_cast at h ⊢
  linear_combination h

theorem prod_etaInf_mul_abs [IsTotallyReal F] (a : Fˣ) :
    ((∏ w : InfinitePlace F, etaInf F w a : ℂˣ) : ℂ) * ((|Algebra.norm ℚ (a : F)| : ℚ) : ℂ) =
      ((Algebra.norm ℚ (a : F) : ℚ) : ℂ) := by
  have h1 := InfinitePlace.prod_eq_abs_norm (a : F)
  simp only [IsTotallyReal.mult_eq, pow_one] at h1
  have h2 : ((Algebra.norm ℚ (a : F) : ℚ) : ℂ) = ∏ σ : F →+* ℂ, σ a := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f a) (fun φ => φ a)
      (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ (a : F)]
    simp
  have hb : Function.Bijective (fun w : InfinitePlace F => w.embedding) := by
    refine ⟨fun w w' h => ?_, fun φ => ⟨InfinitePlace.mk φ, ?_⟩⟩
    · rw [← w.mk_embedding, ← w'.mk_embedding]; exact congrArg _ h
    · exact InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)
  rw [h2, ← hb.prod_comp (fun φ => φ (a : F)), ← Complex.ofReal_ratCast, ← h1,
    Complex.ofReal_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => etaInf_mul_abs w a

noncomputable def etaAll [IsTotallyReal F] : Fˣ →* ℂˣ :=
  MonoidHom.mk' (fun a => (∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) *
    ∏ w : InfinitePlace F, etaInf F w a) fun a b => by
    simp only [etaFin_mul, etaInf_mul]
    rw [finprod_mul_distrib (etaFin_finite L a) (etaFin_finite L b), Finset.prod_mul_distrib,
      mul_mul_mul_comm]

theorem ordF_int (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (y : 𝓞 F) (hy : (a : F) = y) :
    ordF v a = ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors : ℕ) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact a.ne_zero hy
  unfold ordF
  rw [hy, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hy0,
    WithZero.log_exp, neg_neg]

theorem finprod_etaFin (d : ℕ)
    (hj : ∀ v : HeightOneSpectrum (𝓞 F), (d : 𝓞 F) ∉ v.asIdeal →
      (if (aboveF (L := L) F v).card = 1 then (-1 : ℤ) else 1) =
        jacobiSym (Ideal.absNorm v.asIdeal : ℕ) d)
    (a : Fˣ) (y : 𝓞 F) (hy : (a : F) = y) (hc : IsCoprime y (d : 𝓞 F)) :
    ((∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a : ℂˣ) : ℂ) =
      jacobiSym ((Algebra.norm ℤ y).natAbs : ℕ) d := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact a.ne_zero hy
  have hI : Ideal.span {y} ≠ 0 := by simpa using hy0
  let φ : Ideal (𝓞 F) →* ℂ :=
    { toFun := fun I => (jacobiSym (Ideal.absNorm I : ℕ) d : ℤ)
      map_one' := by simp
      map_mul' := fun I J => by simp [jacobiSym.mul_left] }
  have h1 := φ.map_finprod (Ideal.hasFiniteMulSupport hI)
  rw [Ideal.finprod_heightOneSpectrum_factorization hI] at h1
  rw [← Ideal.absNorm_span_singleton]
  refine ((Units.coeHom ℂ).map_finprod (etaFin_finite L a)).trans (Eq.trans ?_ h1.symm)
  refine finprod_congr fun v => ?_
  rw [HeightOneSpectrum.maxPowDividing, map_pow, etaFin, ordF_int v a y hy]
  by_cases hv : (d : 𝓞 F) ∈ v.asIdeal
  · have hyv : y ∉ v.asIdeal := fun hz => by
      obtain ⟨r, s, hrs⟩ := hc
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
        (hrs ▸ add_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_left _ _ hv)))
    have h0 : (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors = 0 := by
      by_contra h
      apply hyv
      rw [← Ideal.dvd_span_singleton]
      exact (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp h
    rw [h0]
    simp
  · change _ = ((jacobiSym (Ideal.absNorm v.asIdeal : ℕ) d : ℤ) : ℂ) ^ _
    rw [← hj v hv]
    split_ifs <;> simp

theorem etaAll_coprime [IsTotallyReal F] (d : ℕ) (hd : d % 4 = 3)
    (hj : ∀ v : HeightOneSpectrum (𝓞 F), (d : 𝓞 F) ∉ v.asIdeal →
      (if (aboveF (L := L) F v).card = 1 then (-1 : ℤ) else 1) =
        jacobiSym (Ideal.absNorm v.asIdeal : ℕ) d)
    (a : Fˣ) (y : 𝓞 F) (hy : (a : F) = y) (hc : IsCoprime y (d : 𝓞 F))
    (hn : jacobiSym (Algebra.norm ℤ y) d = 1) : etaAll L a = 1 := by
  apply Units.ext
  have h2 := prod_etaInf_mul_abs a
  have hN : Algebra.norm ℚ (a : F) ≠ 0 := Algebra.norm_ne_zero_iff.mpr a.ne_zero
  rw [hy, ← Algebra.coe_norm_int] at h2 hN
  change (((∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) *
    ∏ w : InfinitePlace F, etaInf F w a : ℂˣ) : ℂ) = 1
  rw [Units.val_mul, finprod_etaFin L d hj a y hy hc]
  set N := Algebra.norm ℤ y
  have hN' : N ≠ 0 := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN'
  rcases lt_or_gt_of_ne hN' with h | h
  · rw [abs_of_neg (by exact_mod_cast h)] at h2
    rw [Int.natCast_natAbs, abs_of_neg h, jacobiSym.neg _ (Nat.odd_iff.mpr (by omega)),
      ZMod.χ₄_nat_three_mod_four hd, hn]
    apply mul_right_cancel₀ hNC
    push_cast at h2 ⊢
    linear_combination h2
  · rw [abs_of_pos (by exact_mod_cast h)] at h2
    rw [Int.natCast_natAbs, abs_of_pos h, hn]
    apply mul_right_cancel₀ hNC
    push_cast at h2 ⊢
    linear_combination h2

end General

section CM

open GlobalTheory.Mem.Chr

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

theorem val_under (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 K⁺))
    (hwv : w.under (𝓞 K⁺) = v)
    (h : (Ideal.primesOver v.asIdeal (𝓞 K)).ncard = 2 ∨
      ((Ideal.primesOver v.asIdeal (𝓞 K)).ncard = 1 ∧ v.asIdeal.inertiaDegIn (𝓞 K) = 2))
    (x : K⁺) : v.valuation K⁺ x = w.valuation K (algebraMap K⁺ K x) := by
  subst hwv
  have := w.isPrime
  have := (w.under (𝓞 K⁺)).isPrime
  have hl : w.asIdeal.LiesOver (w.under (𝓞 K⁺)).asIdeal := ⟨rfl⟩
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (w.under (𝓞 K⁺)).asIdeal (𝓞 K) (K ≃ₐ[K⁺] K)
  rw [Eta.card_gal] at hf
  have he : (w.under (𝓞 K⁺)).asIdeal.ramificationIdxIn (𝓞 K) = 1 := by
    rcases h with h | ⟨h, h'⟩
    · rw [h] at hf
      exact Nat.eq_one_of_mul_eq_one_right (Nat.eq_of_mul_eq_mul_left two_pos (hf.trans (mul_one 2).symm))
    · rw [h, h'] at hf
      omega
  rw [← HeightOneSpectrum.valuation_liesOver K (w.under (𝓞 K⁺)) w x,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (w.under (𝓞 K⁺)).asIdeal w.asIdeal (K ≃ₐ[K⁺] K),
    he, pow_one]

theorem exists_norm (b : Kˣ) :
    ∃ a : (K⁺)ˣ, algebraMap K⁺ K (a : K⁺) = b * IsCMField.complexConj K b := by
  have hmem : (b : K) * IsCMField.complexConj K b ∈ K⁺ := by
    rw [← IsCMField.complexConj_eq_self_iff, map_mul, IsCMField.complexConj_apply_apply, mul_comm]
  refine ⟨Units.mk0 ⟨_, hmem⟩ fun h => ?_, rfl⟩
  have := congrArg Subtype.val h
  simp at this

theorem exists_conj (w : HeightOneSpectrum (𝓞 K)) :
    ∃ w' : HeightOneSpectrum (𝓞 K), w'.under (𝓞 K⁺) = w.under (𝓞 K⁺) ∧
      (∀ x : K, w.valuation K (IsCMField.complexConj K x) = w'.valuation K x) ∧
      ∀ w'' : HeightOneSpectrum (𝓞 K), w''.under (𝓞 K⁺) = w.under (𝓞 K⁺) → w'' = w ∨ w'' = w' := by
  have key := under_eq_iff_conjPl (IsCMField.complexConj K)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one K) w
  obtain ⟨w', h, hu⟩ := existsUnique_conjPl (IsCMField.complexConj K).toRingEquiv w
  refine ⟨w', (key w').mpr (Or.inr h), fun x => ?_, fun w'' h'' => ((key w'').mp h'').imp id (hu w'')⟩
  rw [← h (IsCMField.complexConj K x)]
  exact congrArg _ (IsCMField.complexConj_apply_apply K x)

omit [IsCMField K] in
theorem mem_aboveF (v : HeightOneSpectrum (𝓞 K⁺)) (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ aboveF (L := K) K⁺ v ↔ w.under (𝓞 K⁺) = v := by
  simp [aboveF]

variable (hu : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield K)),
  (Ideal.primesOver v.asIdeal (𝓞 K)).ncard = 2 ∨
    ((Ideal.primesOver v.asIdeal (𝓞 K)).ncard = 1 ∧ v.asIdeal.inertiaDegIn (𝓞 K) = 2))

include hu

theorem etaAll_norm (b : Kˣ) (a : (K⁺)ˣ)
    (ha : algebraMap K⁺ K (a : K⁺) = b * IsCMField.complexConj K b) : etaAll K a = 1 := by
  change (∏ᶠ v : HeightOneSpectrum (𝓞 K⁺), etaFin (L := K) K⁺ v a) *
    ∏ w : InfinitePlace K⁺, etaInf K⁺ w a = 1
  rw [finprod_eq_one_of_forall_eq_one, Finset.prod_eq_one, one_mul]
  · intro w _
    have h := ComplexEmbedding.lift_algebraMap_apply K w.embedding (a : K⁺)
    rw [ha, map_mul, IsCMField.complexEmbedding_complexConj, Complex.mul_conj] at h
    rw [etaInf, ← h, Complex.ofReal_re, if_neg (not_lt.mpr (Complex.normSq_nonneg _))]
  · intro v
    unfold etaFin
    split_ifs with hc
    · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc
      have hwv : w.under (𝓞 K⁺) = v := (mem_aboveF K v w).mp (hw ▸ Finset.mem_singleton_self w)
      obtain ⟨w', h1, h2, -⟩ := exists_conj K w
      have hw' : w' = w := Finset.mem_singleton.mp (hw ▸ (mem_aboveF K v w').mpr (h1.trans hwv))
      have h3 := val_under K w v hwv (hu v) a
      rw [ha, map_mul, h2, hw', val_eq_exp, val_eq_exp, ← WithZero.exp_add, WithZero.exp_inj] at h3
      exact Even.neg_one_zpow ⟨ordF w b, by omega⟩
    · rfl

theorem exists_norm_val_eq {m : 𝓞 K⁺} (hm : m ≠ 0)
    (hs : ∀ v : HeightOneSpectrum (𝓞 K⁺), m ∈ v.asIdeal → (aboveF (L := K) K⁺ v).card = 2)
    (y : 𝓞 K⁺) (hy : y ≠ 0) :
    ∃ a : (K⁺)ˣ, etaAll K a = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 K⁺), m ∈ v.asIdeal →
      v.valuation K⁺ (a : K⁺) = v.valuation K⁺ (y : K⁺) := by
  classical
  have hex : ∀ v : HeightOneSpectrum (𝓞 K⁺), ∃ w : HeightOneSpectrum (𝓞 K),
      w.under (𝓞 K⁺) = v := by
    intro v
    have := v.isPrime
    obtain ⟨⟨P, hPp, hPo⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver v.asIdeal (𝓞 K)))
    exact ⟨⟨P, hPp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      HeightOneSpectrum.ext hPo.over.symm⟩
  choose s hs' using hex
  have hfin := Ideal.finite_factors (I := Ideal.span {m}) (by simpa using hm)
  let n : HeightOneSpectrum (𝓞 K⁺) → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors
  obtain ⟨b, hb⟩ := exists_val_eq (hfin.toFinset.biUnion (aboveF (L := K) K⁺))
    (fun w => if w = s (w.under (𝓞 K⁺)) then n (w.under (𝓞 K⁺)) else 0)
  obtain ⟨a, ha⟩ := exists_norm K b
  refine ⟨a, etaAll_norm K hu b a ha, fun v hv => ?_⟩
  have hT : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 K⁺) = v →
      w ∈ hfin.toFinset.biUnion (aboveF (L := K) K⁺) := fun w hw =>
    Finset.mem_biUnion.mpr ⟨v, by simpa [Ideal.dvd_span_singleton] using hv,
      (mem_aboveF K v w).mpr hw⟩
  obtain ⟨w', h1, h2, h3⟩ := exists_conj K (s v)
  rw [hs'] at h1 h3
  have hne : w' ≠ s v := by
    intro h
    have hsub : aboveF (L := K) K⁺ v ⊆ {s v} := fun w hw =>
      Finset.mem_singleton.mpr ((h3 w ((mem_aboveF K v w).mp hw)).elim id fun h' => h'.trans h)
    have := Finset.card_le_card hsub
    rw [hs v hv, Finset.card_singleton] at this
    omega
  rw [val_under K (s v) v (hs' v) (hu v), ha, map_mul, h2, hb _ (hT _ (hs' v)), hb _ (hT _ h1),
    hs', h1, if_pos rfl, if_neg hne, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ hy]
  simp [n]

theorem etaAll_eq_one {m : 𝓞 K⁺} (hm : m ≠ 0)
    (hs : ∀ v : HeightOneSpectrum (𝓞 K⁺), m ∈ v.asIdeal → (aboveF (L := K) K⁺ v).card = 2)
    (hc : ∀ (a : (K⁺)ˣ) (y : 𝓞 K⁺), (a : K⁺) = y → IsCoprime y m → etaAll K a = 1)
    (a : (K⁺)ˣ) : etaAll K a = 1 := by
  have hint : ∀ (a : (K⁺)ˣ) (y : 𝓞 K⁺), (a : K⁺) = y → etaAll K a = 1 := by
    intro a y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact a.ne_zero hy
    obtain ⟨c, hc1, hc2⟩ := exists_norm_val_eq K hu hm hs y hy0
    obtain ⟨y', z, hz0, hy', hz, h⟩ := exists_coprime_mul_eq hm ((a * c⁻¹ : (K⁺)ˣ) : K⁺)
      fun v hv => by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, ← hc2 v hv,
          mul_inv_cancel₀ (val_ne_zero v c)]
    have h1 := hc (Units.mk0 (z : K⁺) (RingOfIntegers.coe_ne_zero_iff.mpr hz0)) z rfl hz
    have h2 := hc (a * c⁻¹ * Units.mk0 (z : K⁺) (RingOfIntegers.coe_ne_zero_iff.mpr hz0)) y' h hy'
    rwa [map_mul, map_mul, map_inv, h1, hc1, inv_one, mul_one, mul_one] at h2
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := 𝓞 K⁺) (a : K⁺)
  have hz0 : (z : K⁺) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.ne_zero hz)
  have h1 := hint (Units.mk0 _ hz0) z rfl
  have h2 := hint (a * Units.mk0 _ hz0) y (by
    rw [Units.val_mul, ← hyz]
    exact div_mul_cancel₀ _ hz0)
  rwa [map_mul, h1, mul_one] at h2

end CM


open Classical in
theorem eta_product_formula : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (a : (H.F)ˣ), (∏ᶠ v : HeightOneSpectrum (𝓞 H.F), etaFin (L := H.E) H.F v a) * ∏ w : InfinitePlace H.F, etaInf H.F w a = 1 := by
  intro R H a
  have hCM : IsCMField H.E := H.der.cm
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hd : H.d.Prime := H.hyp.2.1
  have : Fact H.d.Prime := ⟨hd⟩
  have hE := H.der.eta
  have key := etaAll_eq_one H.E (fun v => hE.1 v.asIdeal v.isPrime v.ne_bot)
    (m := (H.d : 𝓞 H.F)) (by exact_mod_cast hd.ne_zero) ?_
    (fun a y hy hc => etaAll_coprime H.E H.d (by omega) (GlobalTheory.EtaJacobi.eta_eq_jacobiSym R H) a y hy hc
      (GlobalTheory.NormSquareRamified.host_jacobiSym_norm R H y hc)) a
  · convert key using 1
    rfl
  intro v hv
  rw [GlobalTheory.EtaJacobi.card_aboveF]
  have hvp := v.isPrime
  obtain ⟨⟨P, hPp, hPo⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver v.asIdeal (𝓞 H.E)))
  have hunder : P.under (𝓞 H.F) = v.asIdeal := hPo.over.symm
  have hPZ : P.LiesOver (Ideal.span {(H.d : ℤ)}) := by
    have hm : (Ideal.span {(H.d : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hd).irreducible
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [← hunder, Ideal.mem_comap, map_natCast] at hv
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hv
  have he := hE.2.2 H.d (Dvd.intro_left _ rfl) P
  unfold Formalism.HC.HostRaw.etaF at he
  change (if (Ideal.primesOver (P.under (𝓞 H.F)) (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 at he
  rw [hunder] at he
  by_contra hc
  rw [if_neg hc] at he
  exact absurd he (by decide)

end GlobalTheory.EtaProduct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticCharProductFormulaCMHostStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticChar_product_formula_CM_host : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (a : (H.F)ˣ), (∏ᶠ v : HeightOneSpectrum (𝓞 H.F), etaFin (L := H.E) H.F v a) * ∏ w : InfinitePlace H.F, etaInf H.F w a = 1 := by
  first | exact @GlobalTheory.EtaProduct.eta_product_formula | exact GlobalTheory.EtaProduct.eta_product_formula | (intros; apply GlobalTheory.EtaProduct.eta_product_formula <;> assumption)
end
