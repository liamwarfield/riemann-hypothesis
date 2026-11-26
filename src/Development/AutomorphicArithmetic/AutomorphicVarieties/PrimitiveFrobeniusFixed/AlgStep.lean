module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XJacPowNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.DegOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XCongJac
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem relNorm_ker (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (p : ℕ) [hp : Fact p.Prime] (π : 𝓞 K' →+* ZMod p) :
    Ideal.relNorm (𝓞 K) (RingHom.ker π) = RingHom.ker (π.comp (algebraMap (𝓞 K) (𝓞 K'))) := by
  obtain ⟨h1, -⟩ := (UpperTheory.V.Stick.red K' p (RingHom.ker π)).2 π rfl
  obtain ⟨h2, h3, -⟩ := (UpperTheory.V.Stick.red K p _).2 (π.comp (algebraMap (𝓞 K) (𝓞 K'))) rfl
  haveI : (RingHom.ker π).LiesOver (RingHom.ker (π.comp (algebraMap (𝓞 K) (𝓞 K')))) := ⟨by
    ext x; simp [Ideal.under, RingHom.mem_ker]⟩
  haveI := h3.isPrime
  obtain ⟨s, hs⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime (RingHom.ker π)
    (RingHom.ker (π.comp (algebraMap (𝓞 K) (𝓞 K'))))
  have h4 := Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') (RingHom.ker π)
  rw [hs, map_pow, h2, h1] at h4
  have : s = 1 := Nat.pow_right_injective hp.out.two_le (by simpa using h4)
  rw [hs, this, pow_one]

private theorem root_inj {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime] (π : R →+* ZMod p) (N : ℕ)
    [NeZero N] (ζ : R) (hζ : IsPrimitiveRoot ζ N) (hπ : IsPrimitiveRoot (π ζ) N) (a b : R) (ha : a ^ N = 1)
    (hb : b ^ N = 1) (h : π a = π b) : a = b := by
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one ha
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hb
  rw [map_pow, map_pow] at h
  rw [hπ.pow_inj hi hj h]

private theorem jac_cong {F R R' S : Type} [Field F] [Fintype F] [CommRing R] [CommRing R'] [CommRing S]
    (f : R →+* S) (g : R' →+* S) (χ : MulChar F R) (χ' : MulChar F R') (h : ∀ x, f (χ x) = g (χ' x)) (b : ℕ) :
    f (∏ j ∈ Finset.Ico 1 b, jacobiSum χ (χ ^ j)) = g (∏ j ∈ Finset.Ico 1 b, jacobiSum χ' (χ' ^ j)) := by
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.1 hj).1; omega
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [jacobiSum, map_sum, map_mul, MulChar.pow_apply' _ hj0, map_pow, h]

private theorem pow_cong {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] (q : ℕ) (hq : q.Prime)
    (hqP : (q : R) ∈ P) (a c : R) (h : a ^ q = c ^ q) : Ideal.Quotient.mk P a = Ideal.Quotient.mk P c := by
  haveI := Fact.mk hq
  haveI : CharP (R ⧸ P) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hqP)
  have : (Ideal.Quotient.mk P a - Ideal.Quotient.mk P c) ^ q = 0 := by
    rw [sub_pow_char, ← map_pow, ← map_pow, h, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff hq.ne_zero |>.1 this)

private theorem jac_notMem {R : Type} [CommRing R] [IsDomain R] [CharZero R] (p : ℕ) [Fact p.Prime]
    (χ : MulChar (ZMod p) R) (b : ℕ) (hb : b < orderOf χ) (P : Ideal R) [hP : P.IsPrime] (hpP : (p : R) ∉ P) :
    (∏ j ∈ Finset.Ico 1 b, jacobiSum χ (χ ^ j)) ∉ P := by
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨j, hj, hm⟩
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hj
  have hd := UpperTheory.V.Stick.jacDvd R p χ (χ ^ j)
    (by simpa using pow_ne_one_of_lt_orderOf (x := χ) (n := 1) one_ne_zero (by omega))
    (pow_ne_one_of_lt_orderOf (by omega) (by omega))
    (by rw [← pow_succ']; exact pow_ne_one_of_lt_orderOf (by omega) (by omega))
  exact hpP (Ideal.mem_of_dvd _ hd hm)

private theorem val_lt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a b c d : 𝓞 K) (ζ : K)
    (n : ℕ) (hn : n ≠ 0) (hζ : ζ ^ n = 1) (hb : b ∉ v.asIdeal)
    (h1 : Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal c)
    (h2 : Ideal.Quotient.mk v.asIdeal b = Ideal.Quotient.mk v.asIdeal d) :
    v.valuation K (ζ * ((a : K) / b) - ζ * ((c : K) / d)) < 1 := by
  have hd : d ∉ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hb ⊢; rwa [← h2]
  have hb0 : (b : K) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact zero_mem _)
  have hd0 : (d : K) ≠ 0 := fun h => hd (by rw [show d = 0 from Subtype.ext h]; exact zero_mem _)
  have hz : v.valuation K ζ = 1 := by
    have := congrArg (v.valuation K) hζ
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hn).1 this
  have vb : v.valuation K (b : K) = 1 := (v.valuation_eq_one_iff_notMem (K := K)).2 hb
  have vd : v.valuation K (d : K) = 1 := (v.valuation_eq_one_iff_notMem (K := K)).2 hd
  have hm : a * d - c * b ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, h1, h2, sub_self]
  have vm : v.valuation K ((a * d - c * b : 𝓞 K) : K) < 1 := (v.valuation_lt_one_iff_mem (K := K) _).2 hm
  have : ζ * ((a : K) / b) - ζ * ((c : K) / d) = ζ * ((a * d - c * b : 𝓞 K) : K) / (b * d) := by
    push_cast; field_simp
  rw [this, map_div₀, map_mul, map_mul, hz, vb, vd]
  simpa using vm

private theorem neg_mul_self (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]
    (y : 𝓞 K) (hy : y ^ M = 1) : sgO M K (-1) y * y = 1 := by
  rw [sgO_apply M K _ hy, ← pow_succ]
  have : M ∣ (((-1 : (ZMod M)ˣ) : ZMod M)).val + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; simp
  obtain ⟨k, hk⟩ := this
  rw [hk, pow_mul, hy, one_pow]

private theorem inv_pow_q (M q : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]
    (u : (ZMod M)ˣ) (hu : (u : ZMod M) = q) (y : 𝓞 K) (hy : y ^ M = 1) : ((sgO M K u).symm y) ^ q = y := by
  have : sgO M K u y = y ^ q := by
    rw [sgO_apply M K _ hy, hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hy]
  rw [← map_pow, ← this, RingEquiv.symm_apply_apply]

theorem UpperTheory.V.ML.xCongJac :
    ∀ (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'], q.Prime → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ (b : ℕ), b < M → ∀ (p : ℕ) [Fact p.Prime] (π : 𝓞 K' →+* ZMod p), p.Coprime (q * M) → ∀ (X' : K') (X : K),
    IsX (q * M) K' b (RingHom.ker π) X' → IsX M K b (Ideal.relNorm (𝓞 K) (RingHom.ker π)) X →
    ∃ ζ : K', ζ ^ (2 * (q * M)) = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → v.valuation K' (X' - ζ * algebraMap K K' ((sg M K u)⁻¹ X)) < 1 := by
  intro M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hb p hp π hcop X' X hX' hX
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hcM : p.Coprime M := Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hcop
  have hcq : p.Coprime q := Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) hcop
  set ι := algebraMap (𝓞 K) (𝓞 K') with hι
  rw [relNorm_ker, ← hι] at hX
  have hz' := (IsCyclotomicExtension.zeta_spec (q * M) ℚ K').toInteger_isPrimitiveRoot
  have hz := (IsCyclotomicExtension.zeta_spec M ℚ K).toInteger_isPrimitiveRoot
  obtain ⟨hπ', d, hd⟩ := UpperTheory.V.Stick.redRoot _ p π _ _ hcop hz'
  obtain ⟨hπ, -⟩ := UpperTheory.V.Stick.redRoot _ p (π.comp ι) _ _ hcM hz
  obtain ⟨χ', hχ', ho'⟩ := UpperTheory.V.Stick.teich _ p π _ d _ hz' hπ' hd.symm
  obtain ⟨χ, hχ, -⟩ := UpperTheory.V.Stick.teich _ p (π.comp ι) _ (d * q) _ hz hπ (by rw [hd]; ring)
  have e' : (p - 1) / (q * M) = d := by rw [hd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne _))]
  have e : (p - 1) / M = d * q := by
    rw [hd, show q * M * d = M * (d * q) by ring, Nat.mul_div_cancel_left _ hM]
  have hbq : b < q * M := lt_of_lt_of_le hb (Nat.le_mul_of_pos_left _ hq.pos)
  have hJ' := UpperTheory.V.ML.xJac (q * M) K' b p π χ' hcop hbq (by rw [e']; exact hχ')
  have hJ := UpperTheory.V.ML.xJac M K b p (π.comp ι) χ hcM hb (by rw [e]; exact hχ)
  obtain ⟨-, -, k', hpk⟩ := (UpperTheory.V.Stick.red K' p (RingHom.ker π)).2 π rfl
  obtain ⟨-, -, k, -⟩ := (UpperTheory.V.Stick.red K p _).2 (π.comp ι) rfl
  obtain ⟨ζ', hζ', rfl⟩ := UpperTheory.V.ML.xUniq _ _ _ _ _ _ k'.ne_zero hJ' hX'
  obtain ⟨ζ, hζ, rfl⟩ := UpperTheory.V.ML.xUniq _ _ _ _ _ _ k.ne_zero hJ hX
  have key : ∀ x, x ≠ 0 → χ' x ^ q = ι (χ x) := fun x hx => by
    refine root_inj p π _ _ hz' hπ' _ _ ?_ ?_ ?_
    · rw [← pow_mul, mul_comm, pow_mul, (hχ' x hx).1, one_pow]
    · rw [← map_pow, mul_comm, pow_mul, (hχ x hx).1, one_pow, map_one]
    · rw [map_pow, (hχ' x hx).2, ← pow_mul]; exact (hχ x hx).2.symm
  set w : K' := algebraMap K K' ((sg M K u)⁻¹ ζ) with hw
  have hwp : w ^ (2 * (q * M)) = 1 := by
    rw [hw, ← map_pow, ← map_pow, show 2 * (q * M) = 2 * M * q by ring, pow_mul, hζ, one_pow, map_one, map_one]
  have hn : 2 * (q * M) ≠ 0 := mul_ne_zero two_ne_zero (NeZero.ne _)
  have hw0 : w ≠ 0 := by rintro h; rw [h, zero_pow hn] at hwp; exact zero_ne_one hwp
  refine ⟨ζ' / w, by rw [div_pow, hζ', hwp, div_one], fun v hv => ?_⟩
  haveI := v.isPrime
  have hpv : (p : 𝓞 K') ∉ v.asIdeal := fun h => by
    obtain ⟨a, c, hac⟩ := (Nat.isCoprime_iff_coprime.2 hcq).map (Int.castRingHom (𝓞 K'))
    simp only [eq_intCast, Int.cast_natCast] at hac
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hac ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hv)))
  set g : 𝓞 K →+* 𝓞 K' := ι.comp (sgO M K u).symm.toRingHom with hg
  have hgq : ∀ y : 𝓞 K, y ^ M = 1 → g y ^ q = ι y := fun y hy => by
    rw [hg, RingHom.comp_apply, ← map_pow]
    exact congrArg ι (inv_pow_q M q K u hu y hy)
  have c1 := jac_cong (Ideal.Quotient.mk v.asIdeal) ((Ideal.Quotient.mk v.asIdeal).comp g) χ' χ (fun x => by
    by_cases hx : x = 0
    · subst hx; simp [MulChar.map_zero]
    · exact pow_cong _ q hq hv _ _ (by rw [key x hx, hgq _ (hχ x hx).1])) b
  have c2 := jac_cong ((Ideal.Quotient.mk v.asIdeal).comp (sgO (q * M) K' (-1)).toRingHom)
    (((Ideal.Quotient.mk v.asIdeal).comp g).comp (sgO M K (-1)).toRingHom) χ' χ (fun x => by
    by_cases hx : x = 0
    · subst hx; simp [MulChar.map_zero]
    · refine pow_cong _ q hq hv (sgO (q * M) K' (-1) (χ' x)) (g (sgO M K (-1) (χ x))) ?_
      rw [hgq _ (by rw [← map_pow, (hχ x hx).1, map_one]), ← map_pow, key x hx]
      have h1 := neg_mul_self (q * M) K' (ι (χ x))
        (by rw [← map_pow, mul_comm, pow_mul, (hχ x hx).1, one_pow, map_one])
      have h2 := congrArg ι (neg_mul_self M K (χ x) (hχ x hx).1)
      rw [map_mul, map_one] at h2
      exact left_inv_eq_right_inv h1 (by rw [mul_comm]; exact h2)) b
  have hn' := jac_notMem p χ' b (ho'.symm ▸ hbq) v.asIdeal hpv
  generalize (∏ j ∈ Finset.Ico 1 b, jacobiSum χ' (χ' ^ j)) = J' at *
  generalize (∏ j ∈ Finset.Ico 1 b, jacobiSum χ (χ ^ j)) = J at *
  have hgc : ∀ y : 𝓞 K, ((g y : 𝓞 K') : K') = algebraMap K K' ((sg M K u)⁻¹ (y : K)) := fun y => rfl
  have := val_lt K' v (sgO (q * M) K' (-1) J') J' (g (sgO M K (-1) J)) (g J) ζ' _ hn hζ' hn' c2 c1
  rw [hgc, hgc] at this
  convert this using 3
  · rfl
  rw [map_mul, map_mul, ← hw, map_div₀, map_div₀, ← mul_assoc, div_mul_cancel₀ _ hw0]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XCongPrin
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

namespace UpperTheory.V.ML.XCP

private def Rel {K' k : Type} [Field K'] [NumberField K'] [Field k] (π : 𝓞 K' →+* k) (a : K') (b : k) : Prop :=
  ∃ n d : 𝓞 K', π n ≠ 0 ∧ π d ≠ 0 ∧ a * algebraMap _ K' d = algebraMap _ K' n ∧ b * π d = π n

section
variable {K' k : Type} [Field K'] [NumberField K'] [Field k] {π : 𝓞 K' →+* k}

private theorem rel_int (x : 𝓞 K') (hx : π x ≠ 0) : Rel π (x : K') (π x) :=
  ⟨x, 1, hx, by simp, by simp, by simp⟩

private theorem rel_one : Rel π 1 1 := ⟨1, 1, by simp, by simp, by simp, by simp⟩

private theorem rel_mul {a a' : K'} {b b' : k} (h : Rel π a b) (h' : Rel π a' b') : Rel π (a * a') (b * b') := by
  obtain ⟨n, d, hn, hd, h1, h2⟩ := h
  obtain ⟨n', d', hn', hd', h1', h2'⟩ := h'
  refine ⟨n * n', d * d', by simp [hn, hn'], by simp [hd, hd'], ?_, ?_⟩
  · rw [map_mul, map_mul, ← h1, ← h1']; ring
  · rw [map_mul, map_mul, ← h2, ← h2']; ring

private theorem rel_inv {a : K'} {b : k} (h : Rel π a b) : Rel π a⁻¹ b⁻¹ := by
  obtain ⟨n, d, hn, hd, h1, h2⟩ := h
  have hn0 : algebraMap _ K' n ≠ 0 := by
    intro h
    have : n = 0 := by simpa using h
    exact hn (by simp [this])
  have ha : a ≠ 0 := by rintro rfl; exact hn0 (by simpa using h1.symm)
  have hb : b ≠ 0 := by rintro rfl; exact hn (by simpa using h2.symm)
  refine ⟨d, n, hd, hn, ?_, ?_⟩
  · rw [← h1]; field_simp
  · rw [← h2]; field_simp

private theorem rel_pow {a : K'} {b : k} (h : Rel π a b) (n : ℕ) : Rel π (a ^ n) (b ^ n) := by
  induction n with
  | zero => simpa using rel_one
  | succ n ih => rw [pow_succ, pow_succ]; exact rel_mul ih h

private theorem rel_zpow {a : K'} {b : k} (h : Rel π a b) (n : ℤ) : Rel π (a ^ n) (b ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using rel_pow h m
  · simpa using rel_inv (rel_pow h m)

private theorem rel_prod {ι : Type} (s : Finset ι) {a : ι → K'} {b : ι → k} (h : ∀ i, Rel π (a i) (b i)) :
    Rel π (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_one
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi]; exact rel_mul (h i) ih

private theorem rel_val (v : HeightOneSpectrum (𝓞 K')) (hv : ∀ x, π x = 0 ↔ x ∈ v.asIdeal) {a a' : K'} {b : k}
    (h : Rel π a b) (h' : Rel π a' b) : v.valuation K' (a - a') < 1 := by
  obtain ⟨n, d, hn, hd, h1, h2⟩ := h
  obtain ⟨n', d', hn', hd', h1', h2'⟩ := h'
  have e : (a - a') * algebraMap _ K' (d * d') = algebraMap _ K' (n * d' - n' * d) := by
    rw [map_mul, map_sub, map_mul, map_mul, ← h1, ← h1']; ring
  have e1 : v.valuation K' (algebraMap _ K' (d * d')) = 1 := by
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem, ← hv]
    simp [hd, hd']
  have e2 : v.valuation K' (algebraMap _ K' (n * d' - n' * d)) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem, ← hv, map_sub, map_mul, map_mul, ← h2, ← h2']
    ring
  rwa [← e, map_mul, e1, mul_one] at e2

private theorem hom_ext {N q : ℕ} [NeZero N] [IsCyclotomicExtension {N} ℚ K'] (hq : q.Prime) [CharP k q]
    {ζ : K'} (hζ : IsPrimitiveRoot ζ N) (φ ψ : 𝓞 K' →+* k) (h : φ hζ.toInteger ^ q = ψ hζ.toInteger ^ q) :
    φ = ψ := by
  haveI := Fact.mk hq
  have h1 : φ hζ.toInteger = ψ hζ.toInteger := frobenius_inj k q h
  have h2 : φ.toIntAlgHom = ψ.toIntAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ) (by
      rintro _ rfl; exact h1)
  ext x
  exact DFunLike.congr_fun h2 x

end

private theorem compat (M N : ℕ) [NeZero M] [NeZero N] (K K' : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] [Algebra K K']
    (h : M ∣ N) (t : (ZMod N)ˣ) (x : K) :
    sg N K' t (algebraMap K K' x) = algebraMap K K' (sg M K (ZMod.unitsMap h t) x) := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {M} ℚ K
  have h1 := IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K' K h (sg N K' t)
  rw [sg, MulEquiv.apply_symm_apply] at h1
  rw [← h1, sg, sg, MulEquiv.symm_apply_apply, AlgEquiv.restrictNormal_commutes]

private theorem comb {G G' k : Type} [CommGroup G] [Fintype G] [DecidableEq G] [Fintype G'] [Field k] (p : G' → G) (u : G) (q : ℕ)
    (hq : 0 < q) (f : G → k) (hf : ∀ t, f t ≠ 0) (hfu : ∀ t, f t = f (u * t) ^ q) (a : G → ℤ) (a' : G' → ℤ)
    (ha : ∀ t, ∑ t' ∈ Finset.univ.filter (fun t' => p t' = t), a' t' = a t - a (u⁻¹ * t)) :
    ∏ t', f (p t') ^ a' t' = ∏ t, (f (u * t) ^ (q - 1)) ^ a t := by
  rw [← Finset.prod_fiberwise Finset.univ p]
  have h1 : ∀ t, ∏ t' ∈ Finset.univ.filter (fun t' => p t' = t), f (p t') ^ a' t'
      = f t ^ a t / f t ^ a (u⁻¹ * t) := by
    intro t
    rw [← zpow_sub₀ (hf t), ← ha, Finset.prod_congr rfl (g := fun t' => f t ^ a' t')
      (fun t' ht' => by rw [(Finset.mem_filter.1 ht').2])]
    induction (Finset.univ.filter (fun t' => p t' = t)) using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ (hf t)]
  rw [Finset.prod_congr rfl (fun t _ => h1 t), Finset.prod_div_distrib,
    ← Equiv.prod_comp (Equiv.mulLeft u) (fun t => f t ^ a (u⁻¹ * t)), ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
  rw [← div_zpow, hfu t]
  congr 1
  obtain ⟨q, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have := hf (u * t)
  rw [pow_succ, Nat.add_sub_cancel]
  field_simp

private theorem card_gal (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K']
    [IsGalois K K'] (hq : q.Prime) (hc : q.Coprime M) : Fintype.card Gal(K'/K) = q - 1 := by
  have h1 := Module.finrank_mul_finrank ℚ K K'
  rw [IsCyclotomicExtension.Rat.finrank M K, IsCyclotomicExtension.Rat.finrank (q * M) K', Nat.totient_mul hc,
    Nat.totient_prime hq, mul_comm] at h1
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.2 (NeZero.pos M)) h1

end UpperTheory.V.ML.XCP

open UpperTheory.V.ML.XCP in
theorem UpperTheory.V.ML.xCongPrin :
    ∀ (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'], q.Prime → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ (b : ℕ), b < q → ∀ y : 𝓞 K', (∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → y ∉ v.asIdeal) →
    ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal →
    v.valuation K' ((∏ t : (ZMod (q * M))ˣ, (sg (q * M) K' t)⁻¹ (y : K') ^ th (q * M) b t) -
      algebraMap K K' ((sg M K u)⁻¹ (∏ t : (ZMod M)ˣ, (sg M K t)⁻¹ (Algebra.norm K (y : K')) ^ th M b t))) < 1 := by
  intro M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hb y hy v hv
  classical
  haveI := Fact.mk hq
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  haveI := v.isMaximal
  letI : Field (𝓞 K' ⧸ v.asIdeal) := Ideal.Quotient.field _
  obtain ⟨π, hπ⟩ : ∃ π : 𝓞 K' →+* (𝓞 K' ⧸ v.asIdeal), ∀ x, π x = 0 ↔ x ∈ v.asIdeal :=
    ⟨Ideal.Quotient.mk _, fun x => Ideal.Quotient.eq_zero_iff_mem⟩
  haveI : CharP (𝓞 K' ⧸ v.asIdeal) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    rw [← map_natCast π, hπ]; exact hv)
  have hc : q.Coprime M := by
    rw [← ZMod.isUnit_iff_coprime, ← hu]; exact u.isUnit
  have hd : M ∣ q * M := Dvd.intro_left q rfl

  let act : Gal(K'/ℚ) → 𝓞 K' →+* 𝓞 K' := fun σ => (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom
  have hact : ∀ σ x, ((act σ x : 𝓞 K') : K') = σ (x : K') := fun _ _ => rfl
  have hmul : ∀ σ τ x, act (σ * τ) x = act σ (act τ x) := fun _ _ _ => rfl
  have hne : ∀ σ, π (act σ y) ≠ 0 := by
    intro σ h
    have hq0 : (q : 𝓞 K') ∈ RingHom.ker (π.comp (act σ)) := by
      rw [RingHom.mem_ker, map_natCast]; exact CharP.cast_eq_zero _ q
    refine hy ⟨RingHom.ker (π.comp (act σ)), RingHom.ker_isPrime _, fun h0 => ?_⟩ hq0 h
    rw [h0, Ideal.mem_bot] at hq0
    exact hq.ne_zero (by exact_mod_cast hq0)
  have hζ := IsCyclotomicExtension.zeta_spec (q * M) ℚ K'
  set ζ := IsCyclotomicExtension.zeta (q * M) ℚ K'
  obtain ⟨w, hw, hwζ⟩ : ∃ w : K, w ^ M = 1 ∧ algebraMap K K' w = ζ ^ q := by
    have h0 := IsCyclotomicExtension.zeta_spec M ℚ K
    have h1 := h0.map_of_injective (algebraMap K K').injective
    obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one (ξ := ζ ^ q) (by rw [← pow_mul, hζ.pow_eq_one])
    exact ⟨_ ^ i, by rw [pow_right_comm, h0.pow_eq_one, one_pow], by rw [map_pow, hi]⟩
  have hcoe : ((hζ.toInteger : 𝓞 K') : K') = ζ := rfl
  have hA : ∀ σ τ : Gal(K'/ℚ), σ (algebraMap K K' w) = τ (algebraMap K K' w) → ∀ x, π (act σ x) = π (act τ x) := by
    intro σ τ h x
    have : π.comp (act σ) = π.comp (act τ) := by
      refine hom_ext hq hζ _ _ ?_
      rw [← map_pow, ← map_pow, RingHom.comp_apply, RingHom.comp_apply]
      congr 1
      apply RingOfIntegers.ext
      rw [hact, hact]
      rw [hwζ] at h
      exact h
    exact DFunLike.congr_fun this x
  choose s hs using ZMod.unitsMap_surjective hd
  have hB : ∀ x, π (act (sg (q * M) K' (s u)) x) = π x ^ q := by
    intro x
    have : π.comp (act (sg (q * M) K' (s u))) = (frobenius _ q).comp π := by
      refine hom_ext hq hζ _ _ ?_
      rw [← map_pow, ← map_pow, RingHom.comp_apply, RingHom.comp_apply, frobenius_def, ← map_pow π]
      congr 1
      apply RingOfIntegers.ext
      rw [hact]
      change sg (q * M) K' (s u) (ζ ^ q) = (ζ ^ q) ^ q
      rw [← hwζ, compat M (q * M) K K' hd, hs, sg_apply M K u hw, ← map_pow, hu, ZMod.val_natCast,
        ← pow_eq_pow_mod _ hw]
    exact DFunLike.congr_fun this x
  let f : (ZMod M)ˣ → 𝓞 K' ⧸ v.asIdeal := fun t => π (act (sg (q * M) K' (s t)⁻¹) y)
  have hf : ∀ t' : (ZMod (q * M))ˣ, π (act (sg (q * M) K' t'⁻¹) y) = f (ZMod.unitsMap hd t') := by
    intro t'
    refine hA _ _ ?_ y
    rw [compat M (q * M) K K' hd, compat M (q * M) K K' hd, map_inv (ZMod.unitsMap hd), map_inv (ZMod.unitsMap hd), hs]
  have hfu : ∀ t, f t = f (u * t) ^ q := by
    intro t
    have h1 := hf ((s u)⁻¹ * s (u * t))
    rw [map_mul (ZMod.unitsMap hd), map_inv (ZMod.unitsMap hd), hs, hs, inv_mul_cancel_left, mul_inv, inv_inv, map_mul, hmul, hB] at h1
    exact h1.symm
  have hcomb := comb (ZMod.unitsMap hd) u q hq.pos f (fun t => hne _) hfu (fun t => th M b t)
    (fun t => th (q * M) b t) (fun t => by convert thDist M q b hq hb u hu t)
  refine rel_val v hπ (b := ∏ t' : (ZMod (q * M))ˣ, f (ZMod.unitsMap hd t') ^ th (q * M) b t') ?_ ?_
  · refine rel_prod _ fun t => rel_zpow ?_ _
    rw [← hf, ← map_inv, ← hact]
    exact rel_int _ (hne _)
  · rw [hcomb, map_prod, map_prod]
    refine rel_prod _ fun t => ?_
    rw [map_zpow₀, map_zpow₀]
    refine rel_zpow ?_ _
    have h1 : (sg M K u)⁻¹ ((sg M K t)⁻¹ (Algebra.norm K (y : K')))
        = sg M K (ZMod.unitsMap hd (s (u * t))⁻¹) (Algebra.norm K (y : K')) := by
      rw [map_inv (ZMod.unitsMap hd), hs, mul_inv, map_mul, map_inv, map_inv]; rfl
    rw [h1, ← compat M (q * M) K K' hd, Algebra.norm_eq_prod_automorphisms, map_prod,
      ← card_gal M q K K' hq hc, ← Finset.card_univ, ← Finset.prod_const]
    refine rel_prod _ fun σ => ?_
    have h2 : f (u * t) = π (act (sg (q * M) K' (s (u * t))⁻¹ * σ.restrictScalars ℚ) y) := by
      refine hA _ _ ?_ y
      rw [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
    rw [h2]
    exact rel_int (act (sg (q * M) K' (s (u * t))⁻¹ * σ.restrictScalars ℚ) y) (hne _)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem alg_step {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (A B x z ζ : L)
    (hA : w A = 1) (hx : w x = 1) (hζ : w ζ = 1) (h1 : w (A - B) < 1) (h2 : w (A / x - ζ * (B / z)) < 1) :
    w (x - ζ⁻¹ * z) < 1 := by
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, map_zero] at hA
    exact zero_ne_one hA
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, map_zero] at hζ
    exact zero_ne_one hζ
  have hB : w B = 1 := by
    have e : B = (B - A) + A := by ring
    rw [e, w.map_add_eq_of_lt_right (by rwa [w.map_sub_swap, hA]), hA]
  have hAx : w (A / x) = 1 := by rw [map_div₀, hA, hx, div_one]
  have hz : w z = 1 := by
    have h3 : w (ζ * (B / z)) = 1 := by
      have e : ζ * (B / z) = (ζ * (B / z) - A / x) + A / x := by ring
      rw [e, w.map_add_eq_of_lt_right (by rwa [w.map_sub_swap, hAx]), hAx]
    rw [map_mul, map_div₀, hζ, hB, one_mul, one_div] at h3
    exact inv_eq_one.mp h3
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    exact zero_ne_one hz
  have e : x - ζ⁻¹ * z = x * (A - B) / A - (A / x - ζ * (B / z)) * (x * z * ζ⁻¹ / A) := by
    field_simp
    ring
  rw [e]
  refine lt_of_le_of_lt (w.map_sub _ _) (max_lt ?_ ?_)
  · rw [map_div₀, map_mul, hx, hA, one_mul, div_one]
    exact h1
  · rw [map_mul, map_div₀, map_mul, map_mul, map_inv₀, hx, hz, hζ, hA]
    simpa using h2

private theorem isX_unit (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]
    (b q : ℕ) (𝔞 : Ideal (𝓞 K)) (X : K) (h0 : 𝔞 ≠ ⊥) (hc : IsCoprime 𝔞 (Ideal.span {(q : 𝓞 K)})) (hX : IsX N K b 𝔞 X)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (q : 𝓞 K) ∈ v.asIdeal) : v.valuation K X = 1 := by
  haveI := v.isPrime
  obtain ⟨a, ha, c, hc', hac⟩ := Ideal.isCoprime_iff_exists.mp hc
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hc'
  have hne : ∀ t, conjI N K 𝔞 t ≠ ⊥ := by
    intro t hb
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hm : (sgO N K t).symm e ∈ conjI N K 𝔞 t := by
      rw [mem_conjI, RingEquiv.apply_symm_apply]
      exact he
    rw [hb, Ideal.mem_bot] at hm
    exact he0 (by simpa using hm)
  have hnle : ∀ t, ¬ conjI N K 𝔞 t ≤ v.asIdeal := by
    intro t ht'
    have ha' : (sgO N K t).symm a ∈ v.asIdeal := by
      apply ht'
      rw [mem_conjI, RingEquiv.apply_symm_apply]
      exact ha
    have hc'' : (sgO N K t).symm (r * (q : 𝓞 K)) ∈ v.asIdeal := by
      rw [map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ hv
    have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
      have e : (1 : 𝓞 K) = (sgO N K t).symm a + (sgO N K t).symm (r * (q : 𝓞 K)) := by
        rw [← map_add (f := _), hac, map_one]
      rw [e]
      exact Ideal.add_mem _ ha' hc''
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hcount : ∀ t, FractionalIdeal.count K v ((conjI N K 𝔞 t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    intro t
    rw [FractionalIdeal.count_coe K v (hne t), Nat.cast_eq_zero]
    by_contra hc0
    have hdvd := (Associates.count_ne_zero_iff_dvd (hne t) v.irreducible).mp hc0
    exact hnle t (Ideal.le_of_dvd hdvd)
  have hX0 : X ≠ 0 := by
    intro h
    have h1 := hX.1
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hcs := GroundTheory.Global.count_spanSingleton v hX0
  rw [hX.2, FractionalIdeal.count_prod K v _ _
    (fun t _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (hne t))),
    Finset.sum_eq_zero (fun t _ => by rw [FractionalIdeal.count_zpow, hcount t, mul_zero])] at hcs
  have hv0 : v.valuation K X ≠ 0 := (Valuation.ne_zero_iff _).mpr hX0
  have hl : WithZero.log (v.valuation K X) = 0 := by linarith
  rw [← WithZero.exp_log hv0, hl, WithZero.exp_zero]

theorem UpperTheory.V.ML.xCong :
    ∀ (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'], q.Prime → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ (b : ℕ), b < M → b < q → ∀ (𝔞 : Ideal (𝓞 K')) (X' : K') (X : K), IsCoprime 𝔞 (Ideal.span {(q : 𝓞 K')}) →
    IsX (q * M) K' b 𝔞 X' → IsX M K b (Ideal.relNorm (𝓞 K) 𝔞) X →
    ∃ ζ : K', ζ ^ (2 * (q * M)) = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → v.valuation K' (X' - ζ * algebraMap K K' ((sg M K u)⁻¹ X)) < 1 := by
  intro M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hbM hbq 𝔞 X' X hc hX' hX
  have key : ∀ I : Ideal (𝓞 K'), IsCoprime I (Ideal.span {(q : 𝓞 K')}) →
      ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → ¬ I ≤ v.asIdeal := by
    intro I hI v hv hle
    rw [Ideal.isCoprime_iff_sup_eq] at hI
    apply v.isPrime.ne_top
    rw [eq_top_iff, ← hI]
    exact sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  by_cases h0 : 𝔞 = ⊥
  · refine ⟨1, one_pow _, fun v hv => ?_⟩
    exact (key 𝔞 hc v hv (by rw [h0]; exact bot_le)).elim
  have h𝔞nz : 𝔞 ∈ (Ideal (𝓞 K'))⁰ := mem_nonZeroDivisors_of_ne_zero h0
  have hS : {v : HeightOneSpectrum (𝓞 K') | ((q * M : ℕ) : 𝓞 K') ∈ v.asIdeal}.Finite := by
    have hne : Ideal.span {((q * M : ℕ) : 𝓞 K')} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr (NeZero.ne _)
    exact (Ideal.finite_factors hne).subset (fun v hv => Ideal.dvd_span_singleton.mpr hv)
  obtain ⟨P, hPS, hPp, hPcl⟩ := degOne K' _ hS (ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩)⁻¹
  set p := Ideal.absNorm P.asIdeal with hpdef
  haveI : Fact p.Prime := ⟨hPp⟩
  obtain ⟨π, hπ⟩ := (red K' p P.asIdeal).1 rfl
  have hPnz : P.asIdeal ∈ (Ideal (𝓞 K'))⁰ := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have hprin : Submodule.IsPrincipal (P.asIdeal * 𝔞) := by
    rw [← ClassGroup.mk0_eq_one_iff (mul_mem hPnz h𝔞nz)]
    have hm : ClassGroup.mk0 ⟨P.asIdeal * 𝔞, mul_mem hPnz h𝔞nz⟩ =
        ClassGroup.mk0 ⟨P.asIdeal, hPnz⟩ * ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩ := by
      rw [← map_mul]
      rfl
    have hcl : ClassGroup.mk0 ⟨P.asIdeal, hPnz⟩ = (ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩)⁻¹ := hPcl
    rw [hm, hcl, inv_mul_cancel]
  obtain ⟨⟨y, hy⟩⟩ := hprin
  rw [Ideal.submodule_span_eq] at hy
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hy
    exact (Ideal.mul_eq_bot.mp hy).elim P.ne_bot h0
  have hPc : IsCoprime P.asIdeal (Ideal.span {(q : 𝓞 K')}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := P.isMaximal.eq_of_le hne le_sup_left
    have hqP : (q : 𝓞 K') ∈ P.asIdeal := by
      rw [heq]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    apply hPS
    show ((q * M : ℕ) : 𝓞 K') ∈ P.asIdeal
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqP
  have hpcop : p.Coprime (q * M) := by
    rw [Nat.Prime.coprime_iff_not_dvd hPp]
    rintro ⟨k, hk⟩
    apply hPS
    show ((q * M : ℕ) : 𝓞 K') ∈ P.asIdeal
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ ((red K' p P.asIdeal).2 π hπ).2.2.2
  obtain ⟨-, hm2, -, -, hm5⟩ := xMul (q * M) K' b
  obtain ⟨-, hn2, -, -, hn5⟩ := xMul M K b
  have hA : IsX (q * M) K' b (Ideal.span {y}) (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) :=
    hm5 y hy0
  have hXP' := hm2 P.asIdeal 𝔞 _ X' P.ne_bot h0 (by rw [hy]; exact hA) hX'
  have hrel : Ideal.relNorm (𝓞 K) (Ideal.span {y}) ≠ ⊥ := by
    rw [Ne, Ideal.relNorm_eq_bot_iff, Ideal.span_singleton_eq_bot]
    exact hy0
  have hB : IsX M K b (Ideal.relNorm (𝓞 K) (Ideal.span {y}))
      (∏ t, ((sg M K) t)⁻¹ (Algebra.norm K (y : K')) ^ th M b ↑t) := by
    rw [Ideal.relNorm_singleton] at hrel ⊢
    have hn0 : Algebra.intNorm (𝓞 K) (𝓞 K') y ≠ 0 := by
      intro h
      apply hrel
      rw [h]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    have h5 := hn5 _ hn0
    have hcoe : ((Algebra.intNorm (𝓞 K) (𝓞 K') y : 𝓞 K) : K) = Algebra.norm K (y : K') :=
      Algebra.algebraMap_intNorm y
    rw [hcoe] at h5
    exact h5
  have hXP := hn2 _ _ _ X (mt Ideal.relNorm_eq_bot_iff.mp P.ne_bot) (mt Ideal.relNorm_eq_bot_iff.mp h0)
    (by rw [← map_mul, hy]; exact hB) hX
  obtain ⟨ζ1, hζ1, hjac⟩ := xCongJac M q K K' hq u hu b hbM p π hpcop _ _
    (by rw [hπ]; exact hXP') (by rw [hπ]; exact hXP)
  refine ⟨ζ1⁻¹, by rw [inv_pow, hζ1, inv_one], fun v hv => ?_⟩
  have hyv : ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → y ∉ v.asIdeal := by
    intro v hv hyv
    apply key _ (IsCoprime.mul_left hPc hc) v hv
    rw [hy, Ideal.span_singleton_le_iff_mem]
    exact hyv
  have hpr := xCongPrin M q K K' hq u hu b hbq y hyv v hv
  have hX'1 := isX_unit (q * M) K' b q 𝔞 X' h0 hc hX' v hv
  have hP1 := isX_unit (q * M) K' b q P.asIdeal _ P.ne_bot hPc hXP' v hv
  have hX'0 : X' ≠ 0 := by
    intro h
    rw [h, map_zero] at hX'1
    exact zero_ne_one hX'1
  have hAv : v.valuation K' (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) = 1 := by
    rw [← div_mul_cancel₀ (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) hX'0, map_mul, hP1, hX'1, one_mul]
  have hζv : v.valuation K' ζ1 = 1 := by
    have h := congrArg (v.valuation K') hζ1
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff.mp h).resolve_right (mul_ne_zero two_ne_zero (NeZero.ne _))
  have h2 := hjac v hv
  rw [map_div₀, map_div₀] at h2
  exact alg_step (v.valuation K') _ _ X' _ ζ1 hAv hX'1 hζv hpr h2
