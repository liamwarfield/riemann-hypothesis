module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.TorsionIntegralDistinctOfPos
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.TorsionIntegralDistinctOfPos
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.TorsionIntegralPos
open GlobalTheory.TorsionIntegral


open IsLocalRing in
theorem torsion_integral_distinct_of_pos : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ),
    (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W →
    0 < m → (m : ℂ)⁻¹ ∈ W →
    (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W) ∧
    ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice →
      t' ∉ L.lattice → L.weierstrassP t - L.weierstrassP t' ∈ W.nonunits →
      t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice := by
  intro L W m h2 _ hg2 hg3 hΔ hpos hm
  have hI : ∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W :=
    fun t a b => integral L W m h2 hg2 hg3 hpos.ne' hm a b
  refine ⟨hI, fun t t' a b a' b' hn => ?_⟩
  by_contra hc
  have hne : L.weierstrassP t ≠ L.weierstrassP t' := mt (GlobalTheory.weierstrassP_eq_iff L b b').1 hc
  rw [not_or] at hc
  obtain ⟨hs, hp⟩ := sum_prod L b b' hne
  let x1 : W := ⟨_, hI t a b⟩
  let x2 : W := ⟨_, hI t' a' b'⟩
  let x3 : W := ⟨_, hI (t + t') (by rw [mul_add]; exact add_mem a a') hc.2⟩
  let x4 : W := ⟨_, hI (t - t') (by rw [mul_sub]; exact sub_mem a a') hc.1⟩
  let g2 : W := ⟨L.g₂, hg2⟩
  let g3 : W := ⟨L.g₃, hg3⟩
  let h : W := ⟨2⁻¹, h2⟩
  let e : W := ⟨_, hΔ⟩
  have c2 : ((2 : W) : ℂ) = 2 := rfl
  have c27 : ((27 : W) : ℂ) = 27 := rfl
  have e1 : (x3 + x4) * (x1 - x2) ^ 2 = 2 * x1 * x2 * (x1 + x2) - g2 * h * (x1 + x2) - g3 := by
    apply Subtype.ext
    simp [x1, x2, x3, x4, g2, g3, h, c2]
    linear_combination hs
  have e2 : x3 * x4 * (x1 - x2) ^ 2 = (x1 * x2 + g2 * h ^ 2) ^ 2 + g3 * (x1 + x2) := by
    apply Subtype.ext
    simp [x1, x2, x3, x4, g2, g3, h]
    linear_combination hp
  have e3 : 2 * h = 1 := by
    apply Subtype.ext
    simp [h, c2]
  have e4 : (g2 ^ 3 - 27 * g3 ^ 2) * e = 1 := by
    apply Subtype.ext
    simp [g2, g3, e, c27, disc L]
  have e5 : residue W (x1 - x2) = 0 :=
    (residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hn)
  have f1 := congrArg (residue W) e1
  have f2 := congrArg (residue W) e2
  have f3 := congrArg (residue W) e3
  have f4 := congrArg (residue W) e4
  simp only [map_mul, map_add (f := _), map_sub, map_pow, map_ofNat, map_one] at f1 f2 f3 f4 e5
  rw [sub_eq_zero] at e5
  rw [← e5] at f1 f2
  generalize residue W x1 = x at *
  generalize residue W g2 = A at *
  generalize residue W g3 = B at *
  generalize residue W h = u at *
  have k1 : 4 * x ^ 3 - A * x - B = 0 := by linear_combination (A * x) * f3 - f1
  have k2 : (4 * x ^ 2 + A) ^ 2 + 32 * B * x = 0 := by
    have hA : 4 * (x * x + A * u ^ 2) = 4 * x ^ 2 + A := by
      linear_combination A * (2 * u + 1) * f3
    rw [← hA]; linear_combination -16 * f2
  have k3 : A ^ 3 - 27 * B ^ 2 = 0 := by
    linear_combination (A - 3 * x ^ 2) * k2 + (12 * x ^ 3 + 5 * A * x + 27 * B) * k1
  rw [k3, zero_mul] at f4
  exact zero_ne_one f4

end GlobalTheory.TorsionIntegralPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.TorsionIntegralDistinctOfPosStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → 0 < m → (m : ℂ)⁻¹ ∈ W → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W) ∧ ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → L.weierstrassP t - L.weierstrassP t' ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice := by
  first | exact @GlobalTheory.TorsionIntegralPos.torsion_integral_distinct_of_pos | exact GlobalTheory.TorsionIntegralPos.torsion_integral_distinct_of_pos | (intros; apply GlobalTheory.TorsionIntegralPos.torsion_integral_distinct_of_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.PrimesOneModNSplitCompletelyWeberField
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.WeberSplit

theorem isCyclotomic_of_root {k K : Type} [Field k] [Field K] [Algebra k K] (h2 : Module.finrank k K = 2) {n : ℕ}
    [NeZero n] (hirr : Irreducible (cyclotomic n k))
    (hn : n.totient = 2) {ζ : K} (hζ : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} k K := by
  haveI : NeZero ((n : ℕ) : K) := hζ.neZero'
  haveI : NeZero ((n : ℕ) : k) := ⟨fun h => NeZero.ne ((n : ℕ) : K) (by rw [← map_natCast (algebraMap k K), h, map_zero])⟩
  haveI : FiniteDimensional k K := Module.finite_of_finrank_eq_succ h2
  have hint : IsIntegral k ζ := IsIntegral.of_finite k ζ
  have hmin : cyclotomic n k = minpoly k ζ := hζ.minpoly_eq_cyclotomic_of_irreducible hirr
  have hfr : Module.finrank k k⟮ζ⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hint, ← hmin, natDegree_cyclotomic, hn]
  have htop : k⟮ζ⟯ = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [hfr, IntermediateField.finrank_top', h2])
  have h1 : Algebra.adjoin k {ζ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]
  refine (IsCyclotomicExtension.iff_singleton n k K).2 ⟨⟨ζ, hζ⟩, fun x => ?_⟩
  have hx : x ∈ Algebra.adjoin k {ζ} := by rw [h1]; exact Algebra.mem_top
  refine Algebra.adjoin_mono ?_ hx
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact hζ.pow_eq_one

section Lattice

variable (K : IntermediateField ℚ ℂ) [NumberField K] (h2 : Module.finrank ℚ K = 2) (L : PeriodPair)
  (hL : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z)


include hL in
theorem mem_of_invariant (m : ℂ) (hm0 : m ≠ 0) (e2 : (m ^ 4)⁻¹ * L.g₂ = L.g₂) (e3 : (m ^ 6)⁻¹ * L.g₃ = L.g₃) :
    ∃ a : K, (a : ℂ) = m := by
  have hh : GlobalTheory.IsHomothetic m L (GlobalTheory.scalePeriods L m hm0) := GlobalTheory.isHomothetic_scalePeriods L m hm0
  have h2' : (GlobalTheory.scalePeriods L m hm0).g₂ = L.g₂ := by rw [GlobalTheory.IsHomothetic.g₂_eq hh]; exact e2
  have h3' : (GlobalTheory.scalePeriods L m hm0).g₃ = L.g₃ := by rw [GlobalTheory.IsHomothetic.g₃_eq hh]; exact e3
  have hlat : (GlobalTheory.scalePeriods L m hm0).lattice = L.lattice := GlobalTheory.lattice_eq_of_g₂_eq_of_g₃_eq h2' h3'
  have h1 : (1 : ℂ) ∈ L.lattice := (hL 1).2 ⟨1, by simp⟩
  have hm : m ∈ L.lattice := by
    have := (hh 1).2 h1
    rwa [hlat, mul_one] at this
  obtain ⟨a, ha⟩ := (hL m).1 hm
  exact ⟨(a : K), ha⟩

include h2 hL in
theorem g₂_ne_zero (hd : discr K < -4) : L.g₂ ≠ 0 := by
  intro h0
  have hm : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))) 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have hm0 : Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) ≠ 0 := Complex.exp_ne_zero _
  have hm6 : Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hm.pow_eq_one, one_pow]
  obtain ⟨a, ha⟩ := mem_of_invariant K L hL _ hm0 (by rw [h0, mul_zero])
    (by rw [hm6, inv_one, one_mul])
  have haK : IsPrimitiveRoot a 3 := by
    rw [← ha] at hm
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp hm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclotomicExtension {3} ℚ K :=
    isCyclotomic_of_root h2 (cyclotomic.irreducible_rat (by norm_num))
      (by rw [Nat.totient_prime Nat.prime_three] <;> norm_num) haK
  have hdisc := IsCyclotomicExtension.Rat.discr_prime 3 K
  norm_num at hdisc
  rw [hdisc] at hd
  norm_num at hd

include h2 hL in
theorem g₃_ne_zero (hd : discr K < -4) : L.g₃ ≠ 0 := by
  intro h0
  have hm : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ))) 4 :=
    Complex.isPrimitiveRoot_exp 4 (by norm_num)
  have hm0 : Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ)) ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨a, ha⟩ := mem_of_invariant K L hL _ hm0 (by rw [hm.pow_eq_one, inv_one, one_mul])
    (by rw [h0, mul_zero])
  have haK4 : IsPrimitiveRoot a 4 := by
    rw [← ha] at hm
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp hm
  have haK : IsPrimitiveRoot a (2 ^ 2) := by norm_num; exact haK4
  haveI : IsCyclotomicExtension {2 ^ 2} ℚ K :=
    isCyclotomic_of_root h2 (cyclotomic.irreducible_rat (by norm_num))
      (by rw [Nat.totient_prime_pow Nat.prime_two (by norm_num)] <;> norm_num) haK
  have hdisc := IsCyclotomicExtension.Rat.discr_prime_pow 2 2 K
  rw [Nat.totient_prime_pow Nat.prime_two (by norm_num)] at hdisc
  norm_num at hdisc
  rw [hdisc] at hd
  norm_num at hd

include h2 hL in
theorem invariant_isAlgebraic : IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) := by
  obtain ⟨a, τ, ha, hlat⟩ := (GlobalTheory.weierstrass_uniformisation.2.2.1 L).1
  have hj := GlobalTheory.g₂_cube_div_eq_modularJ ha hlat
  have hΔ := GlobalTheory.g₂_cube_sub_g₃_sq_ne_zero L
  have hstab : ∀ α : 𝓞 K, ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1},
      (algebraMap K ℂ) (α : K) * x ∈ Submodule.span ℤ {(τ : ℂ), 1} := by
    intro α x hx
    rw [Submodule.mem_span_pair] at hx ⊢
    obtain ⟨c, d, rfl⟩ := hx
    have hax : a * (c • (τ : ℂ) + d • (1 : ℂ)) ∈ L.lattice :=
      (hlat _).2 ⟨c, d, by simp [zsmul_eq_mul]⟩
    obtain ⟨b, hb⟩ := (hL _).1 hax
    have hmem : (((α * b : 𝓞 K) : K) : ℂ) ∈ L.lattice := (hL _).2 ⟨α * b, rfl⟩
    obtain ⟨c', d', h'⟩ := (hlat _).1 hmem
    refine ⟨c', d', ?_⟩
    apply mul_left_cancel₀ ha
    have e1 : (((α * b : 𝓞 K) : K) : ℂ) = (algebraMap K ℂ) (α : K) * (((b : 𝓞 K) : K) : ℂ) := by
      simp
    rw [hb] at e1
    simp only [zsmul_eq_mul, mul_one] at h' e1 ⊢
    rw [h', e1]
    ring
  have hint := GlobalTheory.isIntegral_modularJ_of_ringOfIntegers (K := K) h2 (algebraMap K ℂ) hstab
  have e : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = GlobalTheory.modularJ τ * algebraMap ℚ ℂ (1728 : ℚ)⁻¹ := by
    rw [← hj]
    simp only [map_inv₀, map_ofNat]
    field_simp
  rw [e]
  exact ((hint.tower_top (A := ℚ)).mul isIntegral_algebraMap).isAlgebraic

private lemma ncard_primes_over_eq_of_ringEquiv_comp {A B C : Type} [CommRing A] [CommRing B] [IsDedekindDomain B]
    [CommRing C] [IsDedekindDomain C] (e : B ≃+* C) (i : A →+* B) (j : A →+* C)
    (hij : ∀ a, e (i a) = j a) (p : Ideal A) :
    {Q : HeightOneSpectrum B | Q.asIdeal.comap i = p}.ncard =
      {Q : HeightOneSpectrum C | Q.asIdeal.comap j = p}.ncard := by
  have back : ∀ I : Ideal B, (I.map (e : B →+* C)).map (e.symm : C →+* B) = I := fun I => by
    rw [Ideal.map_map, RingEquiv.symm_comp, Ideal.map_id]
  have fwd : ∀ I : Ideal C, (I.map (e.symm : C →+* B)).map (e : B →+* C) = I := fun I => by
    rw [Ideal.map_map, RingEquiv.comp_symm, Ideal.map_id]
  refine Set.ncard_congr (fun Q _ => (⟨Q.asIdeal.map (e : B →+* C), ?_, ?_⟩ : HeightOneSpectrum C))
    ?_ ?_ ?_
  · rw [Ideal.map_comap_of_equiv]
    haveI := Q.isPrime
    exact Ideal.comap_isPrime _ _
  · exact (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr Q.ne_bot
  · intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ ⊢
    rw [← hQ]
    ext a
    simp only [Ideal.mem_comap]
    rw [Ideal.map_comap_of_equiv]
    simp only [Ideal.mem_comap]
    rw [← hij, RingEquiv.symm_apply_apply]
  · intro Q₁ Q₂ _ _ h
    have h' := congrArg (fun Q : HeightOneSpectrum C => Q.asIdeal.map (e.symm : C →+* B)) h
    simp only [back] at h'
    exact HeightOneSpectrum.ext h'
  · intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ
    have hp : (Q.asIdeal.map (e.symm : C →+* B)).IsPrime := by
      rw [Ideal.map_comap_of_equiv]
      haveI := Q.isPrime
      exact Ideal.comap_isPrime _ _
    refine ⟨⟨Q.asIdeal.map (e.symm : C →+* B), hp,
      (Ideal.map_eq_bot_iff_of_injective e.symm.injective).not.mpr Q.ne_bot⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      rw [← hQ]
      ext a
      simp only [Ideal.mem_comap]
      rw [Ideal.map_comap_of_equiv]
      simp only [Ideal.mem_comap, RingEquiv.symm_symm]
      rw [hij]
    · exact HeightOneSpectrum.ext (fwd Q.asIdeal)

end Lattice

theorem ncard_eq_of_tower (K M N : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field N] [NumberField N]
    [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] [IsGalois K N] (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ∀ σ : N ≃ₐ[K] N, GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x : M, σ (algebraMap M N x) = algebraMap M N x) :
    {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard =
      Module.finrank K M := by
  let φ : M →ₐ[K] N := IsScalarTower.toAlgHom K M N
  let e : M ≃ₐ[K] φ.fieldRange := φ.equivFieldRange
  have h1 := GlobalTheory.T.ncard_primes_eq_finrank_of_frobenius_fixes K N φ.fieldRange 𝔭 (fun σ hσ x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact h σ hσ y)
  rw [ncard_primes_over_eq_of_ringEquiv_comp (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv)
    (algebraMap (𝓞 K) (𝓞 M)) (algebraMap (𝓞 K) (𝓞 φ.fieldRange)) ?_ 𝔭.asIdeal, h1]
  · exact e.toLinearEquiv.finrank_eq.symm
  · intro a
    apply NumberField.RingOfIntegers.ext
    simp only [NumberField.RingOfIntegers.mapRingEquiv_apply]
    exact e.commutes (a : K)

theorem exists_valuationSubring {N : Type} [Field N] (ι : N →+* ℂ) (P : Ideal (𝓞 N)) (hP : P ≠ ⊤) :
    ∃ W : ValuationSubring ℂ, ∀ x ∈ P, W.valuation (ι x) < 1 := by
  set f : 𝓞 N →+* ℂ := ι.comp (algebraMap (𝓞 N) N) with hf
  have hinj : Function.Injective f := ι.injective.comp RingOfIntegers.coe_injective
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨fun a b h => hinj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hI : P.map f.rangeRestrict ≠ ⊤ := by
    rwa [Ne, Ideal.map_eq_top_of_bijective (f := f.rangeRestrict) (hf := hbij)]
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  refine ⟨W, fun x hx => ?_⟩
  have h1 : (f.range.subtype (f.rangeRestrict x)) ∈ W.nonunits :=
    hW ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩
  exact (ValuationSubring.mem_nonunits_iff W).mp h1

theorem valuation_le_one_of_isIntegral (W : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) :
    W.valuation x ≤ 1 := by
  have h1 : IsIntegral W.toLocalSubring.toSubring x := hx.tower_top
  exact (W.valuation_le_one_iff x).mpr
    (LocalSubring.mem_of_isMax_of_isIntegral W.isMax_toLocalSubring h1)

theorem valuation_intCast_eq_one (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime) (hW : W.valuation p < 1) {d : ℤ}
    (hd : ¬ (p : ℤ) ∣ d) : W.valuation d = 1 := by
  have hle : ∀ m : ℤ, W.valuation (m : ℂ) ≤ 1 := fun m =>
    (W.valuation_le_one_iff _).mpr (intCast_mem W m)
  refine le_antisymm (hle d) (not_lt.mp fun hlt => ?_)
  obtain ⟨u, w, huw⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hd
  have h : (u : ℂ) * (p : ℂ) + (w : ℂ) * (d : ℂ) = 1 := by exact_mod_cast huw
  have h2 : W.valuation ((u : ℂ) * (p : ℂ) + (w : ℂ) * (d : ℂ)) < 1 := by
    apply Valuation.map_add_lt
    · rw [map_mul]
      calc W.valuation (u : ℂ) * W.valuation (p : ℂ) ≤ 1 * W.valuation (p : ℂ) := by
            gcongr; exact hle u
        _ < 1 := by rwa [one_mul]
    · rw [map_mul]
      calc W.valuation (w : ℂ) * W.valuation (d : ℂ) ≤ 1 * W.valuation (d : ℂ) := by
            gcongr; exact hle w
        _ < 1 := by rwa [one_mul]
  rw [h, map_one] at h2
  exact lt_irrefl _ h2

theorem frob_congr {K N : Type} [Field K] [Field N] [Algebra K N] (ι : N →+* ℂ) (σ : N ≃ₐ[K] N)
    (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime) (hW : W.valuation p < 1)
    (hσ : ∀ x : 𝓞 N, W.valuation (ι (σ • x - x ^ p : 𝓞 N)) < 1) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) {x : N}
    (hx : IsIntegral ℤ (d • x)) : W.valuation (ι (σ x) - ι x ^ p) < 1 := by
  have hd1 : W.valuation (d : ℂ) = 1 := valuation_intCast_eq_one W hp hW hd
  have hle : ∀ m : ℤ, W.valuation (m : ℂ) ≤ 1 := fun m =>
    (W.valuation_le_one_iff _).mpr (intCast_mem W m)
  have hy : W.valuation (ι (σ (d • x) - (d • x) ^ p)) < 1 := hσ ⟨d • x, hx⟩
  simp only [map_sub, map_pow, map_zsmul, zsmul_eq_mul, map_mul, map_intCast] at hy
  have hX : W.valuation (ι x) ≤ 1 := by
    have h0 := valuation_le_one_of_isIntegral W (hx.map ι.toIntAlgHom)
    have e : ι.toIntAlgHom (d • x) = (d : ℂ) * ι x := by
      simp [RingHom.toIntAlgHom, map_zsmul, zsmul_eq_mul]
    rw [e, map_mul, hd1, one_mul] at h0
    exact h0
  have hdvd : (p : ℤ) ∣ d ^ p - d := by
    haveI := Fact.mk hp
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  obtain ⟨k, hk⟩ := hdvd
  have hk' : ((d : ℂ) ^ p - d) = (p : ℂ) * k := by exact_mod_cast hk
  have hsum : (d : ℂ) * (ι (σ x) - ι x ^ p) =
      ((d : ℂ) * ι (σ x) - ((d : ℂ) * ι x) ^ p) + ((d : ℂ) ^ p - d) * ι x ^ p := by ring
  have h2 : W.valuation ((d : ℂ) * (ι (σ x) - ι x ^ p)) < 1 := by
    rw [hsum]
    apply Valuation.map_add_lt _ hy
    rw [hk', map_mul, map_mul, map_pow]
    calc W.valuation (p : ℂ) * W.valuation (k : ℂ) * W.valuation (ι x) ^ p
        ≤ W.valuation (p : ℂ) * 1 * 1 := by
          gcongr
          · exact hle k
          · exact pow_le_one' hX p
      _ < 1 := by rwa [mul_one, mul_one]
  rwa [map_mul, hd1, one_mul] at h2

theorem eq_zero_of_valuation_lt_one {N : Type} [Field N] (ι : N →+* ℂ)
    (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime) (hW : W.valuation p < 1) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) {x : N}
    (hx : IsIntegral ℤ (d • x⁻¹)) (h : W.valuation (ι x) < 1) : x = 0 := by
  by_contra hx0
  have hd1 : W.valuation (d : ℂ) = 1 := valuation_intCast_eq_one W hp hW hd
  have h1 := valuation_le_one_of_isIntegral W (hx.map ι.toIntAlgHom)
  have e : ι.toIntAlgHom (d • x⁻¹) = (d : ℂ) * (ι x)⁻¹ := by
    simp [RingHom.toIntAlgHom, map_zsmul, zsmul_eq_mul, map_inv₀]
  rw [e, map_mul, hd1, one_mul, map_inv₀] at h1
  have hne : W.valuation (ι x) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero ι).mpr hx0)
  have h3 : W.valuation (ι x) * (W.valuation (ι x))⁻¹ ≤ W.valuation (ι x) * 1 := by
    gcongr
  rw [mul_inv_cancel₀ hne, mul_one] at h3
  exact absurd h (not_lt.mpr h3)

theorem exists_isGalois (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [Algebra M ℂ] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra K N) (_ : Algebra M N),
      IsScalarTower K M N ∧ IsGalois K N ∧ ∃ ι : N →+* ℂ, ∀ x : M, ι (algebraMap M N x) = algebraMap M ℂ x := by
  letI : Algebra K ℂ := ((algebraMap M ℂ).comp (algebraMap K M)).toAlgebra
  haveI : IsScalarTower K M ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K M
  let f := minpoly K α
  let N : IntermediateField K ℂ := IntermediateField.adjoin K (f.rootSet ℂ)
  haveI hS : f.IsSplittingField K N :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : FiniteDimensional K N := Polynomial.IsSplittingField.finiteDimensional N f
  haveI : Normal K N := Normal.of_isSplittingField f
  haveI : NumberField N := NumberField.of_module_finite K N
  haveI : IsGalois K N := ⟨⟩
  let φ : M →ₐ[K] ℂ := IsScalarTower.toAlgHom K M ℂ
  have hroot : φ α ∈ f.rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral α), ?_⟩
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hle : (⊤ : IntermediateField K M).map φ ≤ N := by
    rw [← hα, IntermediateField.adjoin_map, Set.image_singleton]
    exact IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr (IntermediateField.subset_adjoin K _ hroot))
  have hmem : ∀ x : M, φ x ∈ N := fun x => hle ⟨x, trivial, rfl⟩
  let ψ : M →+* N := (φ : M →+* ℂ).codRestrict N hmem
  letI : Algebra M N := ψ.toAlgebra
  haveI : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq (fun k => Subtype.ext rfl)
  exact ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (N.val : N →+* ℂ), fun x => rfl⟩

end GlobalTheory.WeberSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesCongruencesModDegreeOnePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPMulCongrFrobeniusOfPrimeNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPMulCongrFrobeniusOfPrimeNorm
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.EisensteinCongruence

theorem weierstrassP_mul_congr_pow_of_pos : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (α : ℂ) (p : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → p.Prime → (p : ℂ) ∈ W.nonunits → α ∈ W.nonunits → (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ‖α‖ ^ 2 = p → ∃ a : ℂ, a ∈ W ∧ a⁻¹ ∈ W ∧ a ≠ 0 ∧ L.g₂ - a ^ 2 * L.g₂ ^ p ∈ W.nonunits ∧ L.g₃ - a ^ 3 * L.g₃ ^ p ∈ W.nonunits ∧ ∀ (m : ℕ) (t : ℂ), 0 < m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP (α * t) - a * L.weierstrassP t ^ p ∈ W.nonunits := by
  intro L W α p h2 h3 hg₂ hg₃ hΔ hp hpW hαW hα hN
  have hΔ0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := TorsionIntegral.disc L
  have h0 : α ≠ 0 := by
    rintro rfl
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hN
    exact hp.ne_zero (by exact_mod_cast hN.symm)
  haveI : Fact p.Prime := ⟨hp⟩
  set ρ := IsLocalRing.residue W with hρ
  have hpk : (p : IsLocalRing.ResidueField W) = 0 := by
    rw [← map_natCast ρ, residue_eq_zero_iff']
    simpa using hpW
  haveI : CharP (IsLocalRing.ResidueField W) p := (CharP.charP_iff_prime_eq_zero hp).mpr hpk
  have hcop : ∀ m : ℕ, 0 < m → (m : ℂ)⁻¹ ∈ W → p.Coprime m := by
    intro m hm hmW
    rw [hp.coprime_iff_not_dvd, ← CharP.cast_eq_zero_iff (IsLocalRing.ResidueField W) p,
      ← map_natCast ρ]
    apply residue_ne_zero_of_inv_mem
    · simpa using hm.ne'
    · simpa using hmW
  obtain ⟨A, D, hD, hAd, hDd, hev, hode⟩ := exists_weierstrassP_mul_ode L α p h0 hα hN
  obtain ⟨c, A₀, D₀, hc, hA₀, hD₀, hne⟩ := exists_scaling W A D hD
  have hmul : ∀ (m : ℕ) (t : ℂ), (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (α * t) ∈ L.lattice := by
    intro m t h
    have := hα _ h
    rwa [mul_left_comm] at this

  have rel : ∀ (m : ℕ) (t : ℂ), 0 < m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice →
      t ∉ L.lattice → ∃ x y : W, (x : ℂ) = L.weierstrassP t ∧ (y : ℂ) = L.weierstrassP (α * t) ∧
        (A₀.map ρ).eval (ρ x) = ρ y * (D₀.map ρ).eval (ρ x) := by
    intro m t hm hmW hmt ht
    have hαt : α * t ∉ L.lattice := fun h => ht (mem_of_mul_mem L h0 hα hN (hcop m hm hmW) hmt h)
    have T := (GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits L W m h2 h3 hg₂ hg₃ hΔ hm hmW).1
    refine ⟨⟨_, T t hmt ht⟩, ⟨_, T _ (hmul m t hmt) hαt⟩, rfl, rfl, ?_⟩
    rw [eval_map_apply, eval_map_apply, ← map_mul]
    congr 1
    apply W.subtype_injective
    rw [map_mul, ← eval_map_apply, ← eval_map_apply, hA₀, hD₀]
    obtain ⟨e1, e2⟩ := hev t hαt
    simp only [eval_mul, eval_C, ValuationSubring.coe_subtype]
    rw [e2]
    field_simp
  have h3n : ∀ n : ℕ, ((3 ^ n : ℕ) : ℂ)⁻¹ ∈ W := fun n => by
    rw [Nat.cast_pow, ← inv_pow]
    exact pow_mem (by simpa using h3) n
  have hpos : ∀ n : ℕ, 0 < 3 ^ n := fun n => by positivity
  have hpow : ∀ i j : ℕ, i + 1 ≤ j → ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (i + 1)) ∈ L.lattice := by
    intro i j hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    convert L.lattice.smul_mem ((3 : ℤ) ^ d) L.ω₁_mem_lattice using 1
    simp only [zsmul_eq_mul]
    push_cast
    field_simp
    ring
  have hthird : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (j + 1)) = L.ω₁ / 3 := by
    intro j
    push_cast
    field_simp
    ring
  have hns : ∀ (n : ℕ) (z : ℂ), z ∈ L.lattice → (n : ℂ) * z ∈ L.lattice := fun n z hz => by
    simpa using L.lattice.smul_mem (n : ℤ) hz
  have hnot : ∀ j : ℕ, L.ω₁ / 3 ^ (j + 1) ∉ L.lattice := fun j h =>
    third_notMem L (hthird j ▸ hns _ _ h)
  have h33 : ((3 : ℕ) : ℂ) * (L.ω₁ / 3) ∈ L.lattice := by simpa using hpow 0 1 le_rfl
  have hαthird : α * (L.ω₁ / 3) ∉ L.lattice := fun h => third_notMem L
    (mem_of_mul_mem L h0 hα hN (hcop 3 (by decide) (by simpa using h3)) h33 h)

  have dist : ∀ β : ℂ, (∀ l ∈ L.lattice, β * l ∈ L.lattice) → β * (L.ω₁ / 3) ∉ L.lattice →
      ∀ x : ℕ → W, (∀ j, (x j : ℂ) = L.weierstrassP (β * (L.ω₁ / 3 ^ (j + 1)))) →
      Function.Injective fun j => ρ (x j) := by
    intro β hβ hβ3 x hx
    have hm : ∀ i j : ℕ, i + 1 ≤ j →
        ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (i + 1))) ∈ L.lattice := by
      intro i j hij
      rw [mul_left_comm]
      exact hβ _ (hpow i j hij)
    have hn : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (j + 1))) ∉ L.lattice := by
      intro j
      rw [mul_left_comm, hthird]
      exact hβ3
    refine Function.Injective.of_lt_imp_ne fun i j hij h => ?_
    have T := (GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits L W (3 ^ (j + 1)) h2 h3 hg₂ hg₃ hΔ
      (hpos _) (h3n _)).2 _ _ (hm i _ (by omega)) (fun h => hn i (hns _ _ h))
      (hm j _ le_rfl) (fun h => hn j (hns _ _ h)) (by
        rw [← hx, ← hx]
        have : ρ (x i - x j) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h
        exact (residue_eq_zero_iff' W _).mp this)
    apply hn j
    rcases T with T | T
    · convert L.lattice.sub_mem (hm i j hij) (hns (3 ^ j) _ T) using 1
      ring
    · convert L.lattice.sub_mem (hns (3 ^ j) _ T) (hm i j hij) using 1
      ring
  choose x y hx hy hxy using fun j : ℕ =>
    rel (3 ^ (j + 1)) (L.ω₁ / 3 ^ (j + 1)) (hpos _) (h3n _) (hpow j _ le_rfl) (hnot j)
  have hxi := dist 1 (by simp) (by simpa using third_notMem L) x (by simpa using hx)
  have hyi := dist α hα hαthird y hy
  let g₂ : W := ⟨L.g₂, hg₂⟩
  let g₃ : W := ⟨L.g₃, hg₃⟩
  let α₀ : W := ⟨α, W.nonunits_subset hαW⟩
  have hode' : C (α ^ 2) * (C c * D) * (4 * (C c * A) ^ 3 - C L.g₂ * (C c * A) * (C c * D) ^ 2 -
      C L.g₃ * (C c * D) ^ 3) = (derivative (C c * A) * (C c * D) -
        (C c * A) * derivative (C c * D)) ^ 2 * (4 * X ^ 3 - C L.g₂ * X - C L.g₃) := by
    simp only [derivative_C_mul]
    linear_combination C c ^ 4 * hode
  have hode₀ : C (α₀ ^ 2) * D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3) =
      (derivative A₀ * D₀ - A₀ * derivative D₀) ^ 2 * (4 * X ^ 3 - C g₂ * X - C g₃) := by
    apply Polynomial.map_injective W.subtype W.subtype_injective
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
      Polynomial.map_ofNat, ← derivative_map, hA₀, hD₀]
    exact hode'
  have hdvd₀ : (4 * X ^ 3 - C g₂ * X - C g₃ : W[X]) ∣
      D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3) := by
    apply cubic_dvd W h2
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C,
      Polynomial.map_ofNat, hA₀, hD₀]
    have hu : IsUnit (C (α ^ 2) : ℂ[X]) := isUnit_C.mpr (Ne.isUnit (pow_ne_zero _ h0))
    rw [← hu.dvd_mul_left, ← mul_assoc]
    exact Dvd.intro_left _ hode'.symm
  have hdeg : ∀ (B₀ : W[X]) (B : ℂ[X]), B₀.map W.subtype = C c * B →
      (B₀.map ρ).natDegree ≤ B.natDegree := by
    intro B₀ B h
    refine natDegree_map_le.trans ?_
    rw [← natDegree_map_eq_of_injective W.subtype_injective, h, natDegree_C_mul hc]
  have hα₀ : ρ α₀ = 0 := (residue_eq_zero_iff' W _).mpr hαW
  obtain ⟨a, d, ha, hd, eD, eA, e2, e3⟩ := residue_form p (ρ g₂) (ρ g₃) (A₀.map ρ) (D₀.map ρ)
    (by
      rw [← map_ofNat ρ 2]
      exact residue_ne_zero_of_inv_mem W _ (two_ne_zero (α := ℂ)) h2)
    (by
      rw [← map_ofNat ρ 3]
      exact residue_ne_zero_of_inv_mem W _ (three_ne_zero (α := ℂ)) h3)
    (by
      have := residue_ne_zero_of_inv_mem W (g₂ ^ 3 - 27 * g₃ ^ 2) hΔ0 hΔ
      simpa [map_ofNat] using this)
    hne (hAd ▸ hdeg A₀ A hA₀) (lt_of_le_of_lt (hdeg D₀ D hD₀) (by omega))
    _ _ hxi hyi hxy
    (by
      have := congrArg (Polynomial.map ρ) hode₀
      simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
        Polynomial.map_ofNat, ← derivative_map, map_pow, hα₀, map_zero] at this
      rw [← this]
      ring)
    (by
      have := Polynomial.map_dvd ρ hdvd₀
      simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
        Polynomial.map_ofNat] using this)
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
  have ha' : (a₀ : ℂ) ∉ W.nonunits := fun h => ha ((residue_eq_zero_iff' W _).mpr h)
  rw [W.mem_nonunits_iff_or] at ha'
  push Not at ha'
  refine ⟨a₀, a₀.2, ha'.2, ha'.1, ?_, ?_, ?_⟩
  · refine (residue_eq_zero_iff' W (g₂ - a₀ ^ 2 * g₂ ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow, map_pow]
    exact sub_eq_zero.mpr e2
  · refine (residue_eq_zero_iff' W (g₃ - a₀ ^ 3 * g₃ ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow, map_pow]
    exact sub_eq_zero.mpr e3
  · intro m t hm hmW hmt ht
    obtain ⟨u, v, hu, hv, huv⟩ := rel m t hm hmW hmt ht
    rw [← hu, ← hv]
    refine (residue_eq_zero_iff' W (v - a₀ * u ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow]
    rw [eA, eD] at huv
    simp only [eval_mul, eval_C, eval_pow, eval_X] at huv
    apply mul_left_cancel₀ hd
    linear_combination -huv

end GlobalTheory.EisensteinCongruence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPMulCongrFrobeniusOfPrimeNormStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_mul_congr_frobenius_of_primeNorm : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (α : ℂ) (p : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → p.Prime → (p : ℂ) ∈ W.nonunits → α ∈ W.nonunits → (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ‖α‖ ^ 2 = p → ∃ a : ℂ, a ∈ W ∧ a⁻¹ ∈ W ∧ a ≠ 0 ∧ L.g₂ - a ^ 2 * L.g₂ ^ p ∈ W.nonunits ∧ L.g₃ - a ^ 3 * L.g₃ ^ p ∈ W.nonunits ∧ ∀ (m : ℕ) (t : ℂ), 0 < m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP (α * t) - a * L.weierstrassP t ^ p ∈ W.nonunits := by
  first | exact @GlobalTheory.EisensteinCongruence.weierstrassP_mul_congr_pow_of_pos | exact GlobalTheory.EisensteinCongruence.weierstrassP_mul_congr_pow_of_pos | (intros; apply GlobalTheory.EisensteinCongruence.weierstrassP_mul_congr_pow_of_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesCongruencesModDegreeOnePrime
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize GlobalTheory.WeberCongruence
open scoped IntermediateField

namespace GlobalTheory.WeberCongruenceAnyOrder

theorem weber_congruences : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ (W : ValuationSubring ℂ) (π : 𝓞 K) (p : ℕ), p.Prime → 5 ≤ p → Ideal.absNorm (Ideal.span {π}) = p → ((π : K) : ℂ) ∈ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∈ W ∧ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ^ p ∈ W.nonunits ∧ ∀ (m : ℕ), ¬ p ∣ m → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ∈ W ∧ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (((π : K) : ℂ) * t)) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ^ p ∈ W.nonunits) ∧ ((L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∉ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - 1 ∉ W.nonunits → ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice) := by
  intro K _ _ hK L hL W π p hp h5 hN hπ
  have hcm : ∀ a : 𝓞 K, ∀ z ∈ L.lattice, ((a : K) : ℂ) * z ∈ L.lattice := fun a z hz ↦ by
    obtain ⟨b, rfl⟩ := (hL z).mp hz
    exact (hL _).mpr ⟨a * b, by simp⟩
  have hj := mem_of_isIntegral W
    (CMCurves.isIntegral_latticeJ hK (K.val : K →+* ℂ) L hcm)
  have hn : ‖((π : K) : ℂ)‖ ^ 2 = p := by
    rw [← hN]; exact norm_sq_eq_absNorm hK (K.val : K →+* ℂ) π
  have hπi : IsIntegral ℤ ((π : K) : ℂ) :=
    (RingOfIntegers.isIntegral_coe π).map (K.val : K →+* ℂ).toIntAlgHom
  have hpW : (p : ℂ) ∈ W.nonunits := by
    have := mul_mem_nonunits W hπ
      (mem_of_isIntegral W (hπi.map (starRingEnd ℂ).toIntAlgHom))
    convert this using 1
    change _ = _ * (starRingEnd ℂ) _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  have i2 : (2 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 2) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have i3 : (3 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 3) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have hΔ := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (n := 12) (by norm_num)
  have hc0 : c ≠ 0 := by rintro rfl; exact hΔ (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  generalize scalePeriods L c hc0 = L' at H
  have hΔ' : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = 1 := by
    rw [H.g₂_eq, H.g₃_eq]; field_simp; linear_combination -hc
  have eJ : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = L'.g₂ ^ 3 := by
    rw [H.g₂_eq, ← hc]; field_simp
  have eW : ∀ t, L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t =
      L'.g₂ * L'.g₃ * L'.weierstrassP (c * t) := fun t ↦ by
    rw [H.g₂_eq, H.g₃_eq, H.weierstrassP_mul, ← hc]; field_simp
  have hJ : L'.g₂ ^ 3 ∈ W := by
    have := mul_mem (mul_mem (pow_mem i2 6) (pow_mem i3 3)) hj
    convert this using 1
    rw [← eJ, CMCurves.latticeJ]; ring
  have hg := mem_of_pow_mem W three_ne_zero hJ
  have hh : L'.g₃ ∈ W := by
    refine mem_of_pow_mem W two_ne_zero ?_
    have := mul_mem (pow_mem i3 3) (sub_mem hJ (one_mem W))
    convert this using 1
    linear_combination (-1 / 27 : ℂ) * hΔ'
  have hD : (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)⁻¹ ∈ W := by rw [hΔ', inv_one]; exact one_mem W
  obtain ⟨a, ha, -, -, a2, a3, a4⟩ := GlobalTheory.T.weierstrassP_mul_congr_frobenius_of_primeNorm L' W ((π : K) : ℂ) p i2 i3 hg hh hD hp hpW hπ
    (fun l hl ↦ by
      obtain ⟨z, rfl⟩ : ∃ z, l = c * z := ⟨c⁻¹ * l, by field_simp⟩
      rw [mul_left_comm]
      exact (H _).mpr (hcm π z ((H z).mp hl))) hn
  obtain ⟨c1, c2⟩ := congruences W hp hpW hg hh ha hΔ' a2 a3
  simp only [eW]
  rw [eJ]
  refine ⟨hJ, c1, fun m hpm ↦ ?_⟩
  have hm : 0 < m := Nat.pos_of_ne_zero fun h ↦ hpm (h ▸ dvd_zero p)
  have im := inv_natCast_mem W hp hpW hpm
  obtain ⟨t1, t2⟩ := GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits L' W m i2 i3 hg hh hD hm im
  have s1 : ∀ t, (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (c * t) ∈ L'.lattice := fun t ht ↦ by
    rw [mul_left_comm]; exact (H _).mpr ht
  refine ⟨fun t ht ht' ↦ ?_, fun n1 n2 t t' ht ht0 ht' ht0' h ↦ ?_⟩
  · have hx := t1 (c * t) (s1 t ht) ((H t).not.mpr ht')
    refine ⟨mul_mem (mul_mem hg hh) hx, c2 _ _ hx ?_⟩
    rw [mul_left_comm]
    exact a4 m (c * t) hm im (s1 t ht) ((H t).not.mpr ht')
  · have n3 : L'.g₂ ∉ W.nonunits := fun h ↦ n1 (by
      simpa [pow_succ'] using mul_mem_nonunits W h (pow_mem hg 2))
    have n4 : L'.g₃ ∉ W.nonunits := fun h ↦ n2 (by
      have := mul_mem_nonunits W h (mul_mem (ofNat_mem W 27) hh)
      convert this using 1
      linear_combination hΔ')
    rw [← mul_sub, mul_assoc] at h
    have := t2 (c * t) (c * t') (s1 t ht) ((H t).not.mpr ht0) (s1 t' ht') ((H t').not.mpr ht0')
      (mem_nonunits_of_mul W n4 (mem_nonunits_of_mul W n3 h))
    rwa [← mul_sub, ← mul_add, H, H] at this

end GlobalTheory.WeberCongruenceAnyOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesCongruencesModDegreeOnePrimeStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weber_values_congruences_mod_degree_one_prime : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ (W : ValuationSubring ℂ) (π : 𝓞 K) (p : ℕ), p.Prime → 5 ≤ p → Ideal.absNorm (Ideal.span {π}) = p → ((π : K) : ℂ) ∈ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∈ W ∧ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ^ p ∈ W.nonunits ∧ ∀ (m : ℕ), ¬ p ∣ m → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ∈ W ∧ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (((π : K) : ℂ) * t)) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ^ p ∈ W.nonunits) ∧ ((L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∉ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - 1 ∉ W.nonunits → ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice) := by
  first | exact @GlobalTheory.WeberCongruenceAnyOrder.weber_congruences | exact GlobalTheory.WeberCongruenceAnyOrder.weber_congruences | (intros; apply GlobalTheory.WeberCongruenceAnyOrder.weber_congruences <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValues
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize GlobalTheory.WeberSplit
open scoped IntermediateField

namespace GlobalTheory.WeberSplitAny

theorem splits_completely_of_three_le : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → ∃ (_ : NumberField (IntermediateField.adjoin K (weberSet L n))) (S : Finset ℕ), ∀ (π : 𝓞 K) (p : ℕ), p.Prime → p ∉ S → Ideal.absNorm (Ideal.span {π}) = p → π - 1 ∈ Ideal.span {(n : 𝓞 K)} → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin K (weberSet L n))) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 (IntermediateField.adjoin K (weberSet L n)))) = Ideal.span {π}}.ncard = Module.finrank K (IntermediateField.adjoin K (weberSet L n)) := by
  classical
  intro K _ _ h2 hd L hL n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have g2 := g₂_ne_zero K h2 L hL hd
  have g3 := g₃_ne_zero K h2 L hL hd
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨hfin, halg, hperm⟩ := GlobalTheory.T.weberValues_finite_algebraic_permuted L n (by omega) g2 g3
  replace halg := halg (invariant_isAlgebraic K h2 L hL)
  have hweb := GlobalTheory.T.weber_values_congruences_mod_degree_one_prime K h2 L hL
  have hJw : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∈ weberSet L n := Or.inl rfl
  have hJ0 : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ≠ 0 := div_ne_zero (pow_ne_zero _ g2) hD
  have hJ1 : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, div_eq_one_iff_eq hD]
    intro h
    exact g3 (pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination h / 27))
  have hw : ∀ w ∈ weberSet L n, w = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∨ ∃ t, (n : ℂ) * t ∈ L.lattice ∧
      t ∉ L.lattice ∧ w = L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t := by
    rintro w (h | ⟨z, hz, hz', e⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z / n, by rwa [mul_div_cancel₀ _ hn0], hz', e⟩
  generalize L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = J at *
  generalize L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = u at *
  generalize weberSet L n = T at *
  have := hfin.to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K T) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral.tower_top
  have hM : NumberField (IntermediateField.adjoin K T) := NumberField.of_module_finite K _
  refine ⟨hM, ?_⟩
  have hTM := IntermediateField.subset_adjoin K T
  set M := IntermediateField.adjoin K T
  have hext : ∀ (N : Type) [Field N] [Algebra K N] (f g : M →ₐ[K] N),
      (∀ x (hx : x ∈ T), f ⟨x, hTM hx⟩ = g ⟨x, hTM hx⟩) → f = g :=
    fun N _ _ f g h => IntermediateField.adjoin_algHom_ext K h
  clear_value M
  obtain ⟨N, _, _, _, _, _, _, ι, hι⟩ := exists_isGalois K M
  replace hι : ∀ x : M, ι (algebraMap M N x) = x := hι
  have hιK : ∀ x : K, ι (algebraMap K N x) = x := fun x => by
    rw [IsScalarTower.algebraMap_apply K M N, hι]; rfl
  let j : N := algebraMap M N ⟨J, hTM hJw⟩
  have hj : ι j = J := hι _
  have hfin' : (ι ⁻¹' T).Finite := hfin.preimage ι.injective.injOn
  obtain ⟨d, hd0, hdi⟩ := exists_integral_multiples ℤ ℚ (hfin'.toFinset ∪ {j⁻¹, (j - 1)⁻¹} ∪
    Finset.univ.image fun σ : N ≃ₐ[K] N => (σ j - j)⁻¹)
  refine ⟨(6 * n * d.natAbs).primeFactors, fun π p hp hpS hN hπ => ?_⟩
  have hnd : ¬ p ∣ 6 * n * d.natAbs := fun h => hpS (Nat.mem_primeFactors.2 ⟨hp, h, by positivity⟩)
  have hpn : ¬ p ∣ n := fun h => hnd ((h.mul_left _).mul_right _)
  have hpd : ¬ (p : ℤ) ∣ d := fun h => hnd ((Int.natCast_dvd.1 h).mul_left _)
  have hp5 : 5 ≤ p := by
    by_contra h
    have h6 : ¬ p ∣ 6 := fun h => hnd ((h.mul_right _).mul_right _)
    have := hp.two_le
    have : p < 5 := by omega
    interval_cases p
    exacts [h6 (by norm_num), h6 (by norm_num), absurd hp (by norm_num)]
  have hprime : (Ideal.span {π}).IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp)
  have hbot : Ideal.span {π} ≠ ⊥ := fun h => hp.ne_zero (by rw [← hN, h]; simp)
  refine ncard_eq_of_tower K M N ⟨Ideal.span {π}, hprime, hbot⟩ ?_
  rintro σ ⟨P, hP, hPo, hσ⟩
  simp only [hN] at hσ hPo
  obtain ⟨W, hW⟩ := exists_valuationSubring ι P hP.ne_top
  have hover : ∀ x ∈ Ideal.span {π}, W.valuation ((x : K) : ℂ) < 1 := fun x hx => by
    have h := hW _ ((Ideal.mem_of_liesOver P (Ideal.span {π}) x).1 hx)
    rw [← hιK]
    exact h
  have hpW : W.valuation p < 1 := by
    simpa [hN] using hover _ (Ideal.absNorm_mem (Ideal.span {π}))
  obtain ⟨-, hJp, hm⟩ := hweb W π p hp hp5 hN (W.mem_nonunits_iff.2 (hover _ (Ideal.mem_span_singleton_self _)))
  obtain ⟨hm1, hm2⟩ := hm n hpn
  simp only [ValuationSubring.mem_nonunits_iff] at hJp hm1 hm2
  have hc : ∀ x : N, ι x ∈ T → W.valuation (ι (σ x) - ι x ^ p) < 1 := fun x hx =>
    frob_congr ι σ W hp hpW (fun y => hW _ (hσ y)) hpd (hdi x (by simp [hx]))
  have hz : ∀ x : N, IsIntegral ℤ (d • x⁻¹) → W.valuation (ι x) < 1 → x = 0 := fun x =>
    eq_zero_of_valuation_lt_one ι W hp hpW hpd
  have hσj : σ j = j := by
    refine sub_eq_zero.1 (hz _ (hdi _ (by simp)) ?_)
    have := Valuation.map_sub_lt _ (hc j (hj ▸ hJw)) hJp
    rw [map_sub ι]
    rw [hj] at this ⊢
    convert this using 2
    ring
  have hm3 := hm2 (fun h => hJ0 (by rw [← hj, hz j (hdi _ (by simp)) (hj ▸ h), map_zero]))
    (fun h => hJ1 (by
      have e : ι (j - 1) = J - 1 := by rw [map_sub, hj, map_one]
      rw [← e, hz (j - 1) (hdi _ (by simp)) (e ▸ h), map_zero]))
  have : Countable N := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq N ι (ι.comp σ.toRingEquiv.toRingHom)
  have hτ' : ∀ x, τ (ι x) = ι (σ x) := hτ
  have key : (σ : N →ₐ[K] N).comp (IsScalarTower.toAlgHom K M N) = IsScalarTower.toAlgHom K M N := by
    refine hext N _ _ fun w hwT => ?_
    change σ (algebraMap M N ⟨w, hTM hwT⟩) = algebraMap M N ⟨w, hTM hwT⟩
    rcases hw w hwT with rfl | ⟨t, ht, ht', rfl⟩
    · exact hσj
    · set x := algebraMap M N ⟨_, hTM hwT⟩
      have hx : ι x = u * L.weierstrassP t := hι _
      obtain ⟨s, hs, hs', e⟩ := hperm τ (by rw [← hj, hτ', hσj]) t ht ht'
      have h1 := hc x (hx ▸ hwT)
      rw [← hτ', hx, e] at h1
      have h3 := (hm1 t ht ht').2
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hπ
      obtain ⟨a, ha⟩ := (hL _).1 ht
      have e1 : ((π : K) : ℂ) * t = t + ((c * a : 𝓞 K) : K) := by
        have : ((c : K) : ℂ) * n = ((π : K) : ℂ) - 1 := by
          simpa using congrArg (fun y : 𝓞 K => ((y : K) : ℂ)) hc
        push_cast
        rw [ha]
        linear_combination -t * this
      rw [e1, L.weierstrassP_add_coe t ⟨_, (hL _).2 ⟨_, rfl⟩⟩] at h3
      have h4 := Valuation.map_sub_lt _ h3 h1
      rw [sub_sub_sub_cancel_right] at h4
      apply ι.injective
      rw [← hτ', hx, e]
      congr 1
      rcases hm3 t s ht ht' hs hs' h4 with h | h
      · rw [← L.weierstrassP_add_coe s ⟨_, h⟩]
        simp
      · rw [← L.weierstrassP_neg s, ← L.weierstrassP_add_coe (-s) ⟨_, h⟩]
        simp
  exact fun x => DFunLike.congr_fun key x

end GlobalTheory.WeberSplitAny
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValuesStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalRayPrimes_splitCompletely_weberValues : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → ∃ (_ : NumberField (IntermediateField.adjoin K (weberSet L n))) (S : Finset ℕ), ∀ (π : 𝓞 K) (p : ℕ), p.Prime → p ∉ S → Ideal.absNorm (Ideal.span {π}) = p → π - 1 ∈ Ideal.span {(n : 𝓞 K)} → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin K (weberSet L n))) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 (IntermediateField.adjoin K (weberSet L n)))) = Ideal.span {π}}.ncard = Module.finrank K (IntermediateField.adjoin K (weberSet L n)) := by
  first | exact @GlobalTheory.WeberSplitAny.splits_completely_of_three_le | exact GlobalTheory.WeberSplitAny.splits_completely_of_three_le | (intros; apply GlobalTheory.WeberSplitAny.splits_completely_of_three_le <;> assumption)
end
