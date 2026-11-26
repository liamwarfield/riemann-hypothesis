module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HMinus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ConjEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ThetaFull

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.CycIne
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.cycIne :
    ∀ (N : ℕ) [NeZero N] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C] (ζ : C) (p : ℕ), p.Prime → IsPrimitiveRoot ζ N → ∀ w : HeightOneSpectrum (𝓞 C), (p : 𝓞 C) ∈ w.asIdeal → ∀ (σ : Gal(C/ℚ)) (a : ℕ), σ ζ = ζ ^ a → (σ ∈ w.asIdeal.inertia Gal(C/ℚ) ↔ a ≡ 1 [MOD ordCompl[p] N]) ∧ (σ ∈ MulAction.stabilizer Gal(C/ℚ) w.asIdeal ↔ ∃ i : ℕ, a ≡ p ^ i [MOD ordCompl[p] N]) := by
  intro N _ C _ _ _ ζ p hp hζ w hw σ a hσ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := w.isPrime
  haveI : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
        (Nat.prime_iff_prime_int.1 hp)).isMaximal (by simpa using hp.ne_zero)
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
    simpa using hw
  have hne : NeZero (ordCompl[p] N) := ⟨(Nat.ordCompl_pos p (NeZero.ne N)).ne'⟩
  have hmem : ∀ H : Subgroup Gal(C/ℚ), σ ∈ H ↔ IsCyclotomicExtension.Rat.galEquivZMod N C σ ∈
      H.map (IsCyclotomicExtension.Rat.galEquivZMod N C).toMonoidHom := fun H =>
    (Subgroup.mem_map_iff_mem (f := (IsCyclotomicExtension.Rat.galEquivZMod N C).toMonoidHom)
      (IsCyclotomicExtension.Rat.galEquivZMod N C).injective).symm
  have ha : ((IsCyclotomicExtension.Rat.galEquivZMod N C σ : (ZMod N)ˣ) : ZMod N) = (a : ZMod N) := by
    have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N C σ hζ.pow_eq_one
    rw [hσ, (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζ.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val] at h
    exact h.symm
  have hb : ((ZMod.unitsMap (Nat.ordCompl_dvd N p) (IsCyclotomicExtension.Rat.galEquivZMod N C σ) :
      (ZMod (ordCompl[p] N))ˣ) : ZMod (ordCompl[p] N)) = (a : ZMod (ordCompl[p] N)) := by
    rw [ZMod.unitsMap_val, ha, ZMod.cast_natCast (Nat.ordCompl_dvd N p)]
  constructor
  · rw [hmem, KStar.Ram.map_inertia_eq p, KStar.Ram.inertiaUnits, MonoidHom.mem_ker, Units.ext_iff, hb,
      ← ZMod.natCast_eq_natCast_iff, Nat.cast_one, Units.val_one]
  · rw [hmem, KStar.Ram.map_stabilizer_eq p, KStar.Ram.decompUnits, Subgroup.mem_comap,
      ← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]
    refine exists_congr fun i => ?_
    rw [Units.ext_iff, hb, ← ZMod.natCast_eq_natCast_iff, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime, Nat.cast_pow, eq_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.UnrJPrime
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem unrJ_prime (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal := by
  have := w.isPrime
  have : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  refine ⟨ringChar (𝓞 L ⧸ w.asIdeal), CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact (ringChar.spec _ _).2 dvd_rfl

private theorem unrJ_arith (f n p : ℕ) (hp : p.Prime) (hf : Odd f) (h1 : 1 < f) (hn : 2 ≤ n) :
    ¬ (f * 2 ^ n - 1 ≡ 1 [MOD ordCompl[p] (f * 2 ^ n)]) := by
  intro h
  have hM : f * 2 ^ n ≠ 0 := by positivity
  have hd : ordCompl[p] (f * 2 ^ n) ∣ 2 := by
    have h2 := h.add_right 1
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hM)] at h2
    exact (h2.dvd_iff dvd_rfl).1 (Nat.ordCompl_dvd _ _)
  have key : ∀ d : ℕ, d ∣ f * 2 ^ n → ¬ p ∣ d → d ∣ 2 := fun d hd1 hd2 =>
    (Nat.dvd_ordCompl_of_dvd_not_dvd hd1 hd2).trans hd
  by_cases h2 : p = 2
  · subst h2
    have h3 := Nat.le_of_dvd two_pos (key f (dvd_mul_right _ _) hf.not_two_dvd_nat)
    obtain ⟨k, rfl⟩ := hf
    omega
  · have h4 : 2 ^ 2 ∣ f * 2 ^ n := (pow_dvd_pow 2 hn).mul_left f
    have h3 := key _ h4 fun h5 => h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h5))
    omega

private theorem unrJ_conj (L : Type) [Field L] [NumberField L] [IsCMField L] (M : ℕ) (hM : M ≠ 0) (ζ : L)
    (hζ : ζ ^ M = 1) : IsCMField.complexConj L ζ = ζ ^ (M - 1) := by
  let φ : L →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h1 : (φ ζ) ^ M = 1 := by rw [← map_pow, hζ, map_one]
  have h2 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 hM
  rw [IsCMField.complexEmbedding_complexConj, map_pow, ← Complex.inv_eq_conj h2]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hM), h1]

theorem UpperTheory.V.FW.unrJ :
    ∀ (f n : ℕ) [NeZero (f * 2 ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * 2 ^ n} ℚ L] [IsCMField L], Odd f → 1 < f → 2 ≤ n → UnrFin L := by
  intro f n _ L _ _ _ _ hf h1 hn w
  rw [← UpperTheory.V.CF.ineCard.1 (maximalRealSubfield L) L w, Subgroup.card_eq_one, eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  by_contra hne
  have hc : Nat.card Gal(L/maximalRealSubfield L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hτc : τ = IsCMField.complexConj L :=
    ((Nat.card_eq_two_iff' 1).1 hc).unique hne (IsCMField.complexConj_ne_one L)
  subst hτc
  obtain ⟨p, hp, hw⟩ := unrJ_prime L w
  have hζ := IsCyclotomicExtension.zeta_spec (f * 2 ^ n) ℚ L
  have h := (UpperTheory.V.CF.cycIne (f * 2 ^ n) L _ p hp hζ w hw
    (UpperTheory.V.CF.relIncl ℚ (maximalRealSubfield L) L (IsCMField.complexConj L)) (f * 2 ^ n - 1)
    (unrJ_conj L _ (NeZero.ne _) _ hζ.pow_eq_one)).1.1 (fun z => hτ z)
  exact unrJ_arith f n p hp hf h1 hn h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnStab
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem embT_mul (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L]
    (φ : L →+* ℂ) (g x : (ZMod M)ˣ) (a : L) : embT M L φ (g * x) a = embT M L φ x (sg M L g a) := by
  rw [mul_comm g x]
  simp [embT, map_mul, AlgEquiv.mul_apply]

theorem UpperTheory.V.FW.sgnStab :
    ∀ (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L] [IsCMField L] (φ : L →+* ℂ), Function.Surjective (embT M L φ) ∧ (∀ a : L, cE L a = a → sgn (embT M L φ) a ∈ evenF (-1 : (ZMod M)ˣ)) ∧ (∀ f ∈ sgnE (embT M L φ), ∀ g, (fun x => f (g * x)) ∈ sgnE (embT M L φ)) ∧ (fun _ => (1 : ZMod 2)) ∈ sgnE (embT M L φ) := by
  intro M _ L _ _ _ _ φ
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {M} ℚ L
  have hc : ∀ a : L, sg M L (-1) a = cE L a := fun a => by
    have h := congrArg (fun e : L ≃+* L => e a) (conjEq M L).1
    exact h
  have hcomm : ∀ (g : (ZMod M)ˣ) (a : L), cE L (sg M L g a) = sg M L g (cE L a) := by
    intro g a
    rw [← hc, ← hc, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ψ
    obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) φ ψ
      (Subsingleton.elim _ _)
    refine ⟨(sg M L).symm σ.symm, ?_⟩
    rw [← hσ]
    ext x
    simp [embT]
  · intro a ha g
    simp only [sgn]
    rw [embT_mul, hc, ha]
  · intro f hf g
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
      obtain ⟨u, hu, rfl⟩ := hf
      apply AddSubgroup.subset_closure
      have hv : ((Units.map (sgO M L g).toMonoidHom u : 𝓞 L) : L) = sg M L g ((u : 𝓞 L) : L) := by
        simp [sgO, RingOfIntegers.mapRingEquiv_apply]
      refine ⟨Units.map (sgO M L g).toMonoidHom u, ?_, ?_⟩
      · rw [hv, hcomm, hu]
      · funext x
        simp only [sgn, hv, embT_mul]
    | zero => exact zero_mem _
    | add f h _ _ hf hh => exact add_mem hf hh
    | neg f _ hf => exact neg_mem hf
  · apply AddSubgroup.subset_closure
    refine ⟨-1, ?_, ?_⟩
    · simp
    · funext x
      simp [sgn]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.UnitSurj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem isUnit_one_sub {R : Type} [CommRing R] [IsDomain R] {M : ℕ} (hM : 0 < M) {z : R}
    (hz : IsPrimitiveRoot z M) (h : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ M) : IsUnit (1 - z) := by
  have hroot := hz.isRoot_cyclotomic hM
  have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
  have h1 := congrArg (Polynomial.eval 1) hfac
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one_cyclotomic_not_prime_pow h] at h1
  exact IsUnit.of_mul_eq_one _ h1

private theorem exists_finset_adjoin_laurent_preimage (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {M} ℚ L] [IsCMField L] (h4 : 4 ∣ M)
    (h : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ M) :
    Function.Surjective (IsCMField.unitsMulComplexConjInv L) := by
  have hM : 0 < M := NeZero.pos M
  obtain ⟨k, hk⟩ := h4
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ L
  set ζ := IsCyclotomicExtension.zeta M ℚ L
  have hη := hζ.toInteger_isPrimitiveRoot
  have hu : IsUnit (1 - hζ.toInteger) := isUnit_one_sub hM hη h
  have hm1 : ζ ^ (2 * k) = -1 := by
    have hsq : ζ ^ (2 * k) * ζ ^ (2 * k) = 1 := by
      rw [← pow_add, show 2 * k + 2 * k = M by omega]
      exact hζ.pow_eq_one
    have hne : ζ ^ (2 * k) ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    exact (mul_self_eq_one_iff.mp hsq).resolve_left hne
  have hneg : IsPrimitiveRoot (-ζ) M := by
    have hpow : -ζ = ζ ^ (2 * k + 1) := by
      rw [pow_succ, hm1, neg_one_mul]
    rw [hpow]
    apply hζ.pow_of_coprime
    rw [hk, Nat.coprime_comm, show 4 * k = 2 * (2 * k) by ring]
    refine Nat.Coprime.mul_left ?_ ?_
    · exact Nat.coprime_two_left.mpr (odd_two_mul_add_one k)
    · exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hζne : ζ ≠ 1 := hζ.ne_one (by omega)
  set g := IsCMField.unitsMulComplexConjInv L hu.unit with hgdef
  have hg : algebraMap (𝓞 L) L ((g : (𝓞 L)ˣ) : 𝓞 L) = -ζ := by
    have hc : IsCMField.complexConj L ζ = ζ⁻¹ := by
      obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
      refine eq_inv_of_mul_eq_one_left ?_
      apply φ.injective
      have hz : ‖φ ζ‖ = 1 := (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne M)
      rw [map_mul, map_one, IsCMField.complexEmbedding_complexConj, Complex.conj_mul', hz]
      simp
    rw [hgdef, IsCMField.unitsMulComplexConjInv_apply, Units.coe_mul, map_units_inv]
    simp
    have e1 : (algebraMap (𝓞 L) L) hζ.toInteger = ζ := rfl
    have e2 : ((hζ.toInteger : 𝓞 L) : L) = ζ := rfl
    rw [e1, e2, hc]
    have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne M)
    have h1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζne
    have h2 : (1 : L) - ζ⁻¹ = (ζ - 1) / ζ := by
      field_simp
    rw [h2, inv_div]
    field_simp
    ring
  have hgp : IsPrimitiveRoot g M := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff,
      ← IsPrimitiveRoot.map_iff_of_injective (f := algebraMap (𝓞 L) L)
        (FaithfulSMul.algebraMap_injective _ _), hg]
    exact hneg
  have htop : Subgroup.zpowers g = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, ← hgp.eq_orderOf]
    have ht := IsCyclotomicExtension.Rat.torsionOrder_eq (n := M) (K := L)
    rw [if_pos ⟨2 * k, by omega⟩] at ht
    exact ht.symm
  intro y
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top y)
  exact ⟨hu.unit ^ j, by rw [map_zpow, hj]⟩

theorem UpperTheory.V.FW.unitSurj :
    ∀ (f n : ℕ) [NeZero (f * 2 ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * 2 ^ n} ℚ L] [IsCMField L], Odd f → 1 < f → 2 ≤ n → Function.Surjective (IsCMField.unitsMulComplexConjInv L) := by
  intro f n _ L _ _ _ _ hf hf1 hn
  apply exists_finset_adjoin_laurent_preimage (f * 2 ^ n) L
  · have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 hn) f
  · intro p hp k hk
    have h2 : 2 ∣ p ^ k := hk ▸ Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) f
    have hp2 : p = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
    subst hp2
    have hfd : f ∣ 2 ^ k := hk ▸ Dvd.intro _ rfl
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hfd
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      simp at hf1
    · have hev : Even (2 ^ i) := (Nat.even_pow).mpr ⟨even_two, hi.ne'⟩
      exact (Nat.not_even_iff_odd.mpr hf) hev
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnUnit
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinSign
open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinSign :
    ∀ x : ℝ, 0 ≤ x → Real.sin (Real.pi * x) ≠ 0 → (Real.sin (Real.pi * x) < 0 ↔ Odd ⌊x⌋₊) := by
  intro x hx hne
  set n := ⌊x⌋₊ with hn
  have h0 : (0 : ℝ) ≤ x - n := sub_nonneg.mpr (Nat.floor_le hx)
  have h1 : x - n ≤ 1 := by
    have := Nat.lt_floor_add_one x
    linarith
  have hs : 0 ≤ Real.sin (Real.pi * (x - n)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le h0)
      (mul_le_of_le_one_right Real.pi_pos.le h1)
  have he : Real.sin (Real.pi * x) = (-1) ^ n * Real.sin (Real.pi * (x - n)) := by
    rw [← Real.sin_add_nat_mul_pi]
    congr 1
    ring
  rw [he] at hne ⊢
  have hpos : 0 < Real.sin (Real.pi * (x - n)) :=
    lt_of_le_of_ne hs (fun h => hne (by rw [← h, mul_zero]))
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, one_mul]
    exact ⟨fun hlt => absurd hlt (not_lt.mpr hpos.le), fun ho => absurd ho (Nat.not_odd_iff_even.mpr h)⟩
  · rw [h.neg_one_pow]
    exact ⟨fun _ => h, fun _ => by linarith⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem geom_sin (k : ℕ) (θ : ℝ) (h : Real.sin θ ≠ 0) (w : ℂ) (hw : w = Complex.exp (θ * Complex.I) ^ 2) :
    (w ^ k)⁻¹ * ∑ j ∈ Finset.range (2 * k + 1), w ^ j =
      ((Real.sin ((2 * k + 1 : ℕ) * θ) / Real.sin θ : ℝ) : ℂ) := by
  have hs : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h
  obtain ⟨e, he⟩ : ∃ e, e = Complex.exp (θ * Complex.I) := ⟨_, rfl⟩
  have he0 : e ≠ 0 := he ▸ Complex.exp_ne_zero _
  have h1 : ((Real.sin θ : ℝ) : ℂ) = (e⁻¹ - e) * Complex.I / 2 := by
    rw [Complex.ofReal_sin, Complex.sin, neg_mul, Complex.exp_neg, he]
  have h2 : ((Real.sin ((2 * k + 1 : ℕ) * θ) : ℝ) : ℂ) = ((e ^ (2 * k + 1))⁻¹ - e ^ (2 * k + 1)) * Complex.I / 2 := by
    rw [Complex.ofReal_sin, Complex.sin, neg_mul, Complex.exp_neg, he, ← Complex.exp_nat_mul]
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc]
  have h3 := geom_sum_mul w (2 * k + 1)
  rw [← he] at hw
  subst hw
  rw [Complex.ofReal_div, eq_div_iff hs, h1, h2]
  generalize ∑ j ∈ Finset.range (2 * k + 1), (e ^ 2) ^ j = S at h3 ⊢
  have h4 : (e ^ 2) ^ k = e ^ (2 * k) := by rw [← pow_mul]
  have h5 : (e ^ 2) ^ (2 * k + 1) = e ^ (2 * k) * e ^ (2 * k) * e ^ 2 := by ring
  rw [h5] at h3
  rw [h4, pow_succ]
  have h6 : e ^ (2 * k) ≠ 0 := pow_ne_zero _ he0
  generalize e ^ (2 * k) = a at h3 h6 ⊢
  field_simp
  linear_combination (-1 : ℂ) * h3

private theorem exists_zeta (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L]
    (φ : L →+* ℂ) : ∃ ζ : L, IsPrimitiveRoot ζ M ∧ φ ζ = Complex.exp (2 * Real.pi * Complex.I / M) := by
  have h0 := (IsCyclotomicExtension.zeta_spec M ℚ L).map_of_injective φ.injective
  have h1 := Complex.isPrimitiveRoot_exp M (NeZero.ne M)
  obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have h2 : φ (IsCyclotomicExtension.zeta M ℚ L ^ i) = Complex.exp (2 * Real.pi * Complex.I / M) := by
    rw [map_pow, hi]
  exact ⟨_, IsPrimitiveRoot.of_map_of_injective (h2 ▸ h1) φ.injective, h2⟩

private theorem sin_ne (M a : ℕ) (hM : 2 < M) (h : a.Coprime M) : Real.sin (Real.pi * ((a : ℝ) / M)) ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h0
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have h1 : (n : ℝ) * M = a := by
    have := Real.pi_pos
    field_simp at hn
    linarith
  have h2 : n * (M : ℤ) = a := by exact_mod_cast h1
  have h3 : M ∣ a := Int.natCast_dvd_natCast.1 ⟨n, by rw [← h2, mul_comm]⟩
  have := Nat.Coprime.eq_one_of_dvd h.symm h3
  omega

theorem UpperTheory.V.FW.sgnUnit :
    ∀ (M c : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L] [IsCMField L], c.Coprime M → Odd c → 2 < M → ∃ φ : L →+* ℂ, (fun t : (ZMod M)ˣ => ((c * (t : ZMod M).val / M : ℕ) : ZMod 2)) ∈ sgnE (embT M L φ) := by
  intro M c _ L _ _ _ _ hc hodd hM
  obtain ⟨k, rfl⟩ := hodd
  obtain ⟨φ⟩ : Nonempty (L →+* ℂ) := inferInstance
  obtain ⟨ζ, hζ, hφ⟩ := exists_zeta M L φ
  refine ⟨φ, AddSubgroup.subset_closure ?_⟩
  have hz := hζ.toInteger_isPrimitiveRoot
  have hu : IsUnit (hζ.toInteger ^ (k * (M - 1)) * ∑ j ∈ Finset.range (2 * k + 1), hζ.toInteger ^ j) :=
    ((hz.isUnit (by omega)).pow _).mul (hz.geom_sum_isUnit (by omega) hc)
  have hinv : ζ ^ (k * (M - 1)) = (ζ ^ k)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega), mul_comm, pow_mul,
      hζ.pow_eq_one, one_pow]
  have hval : ((hu.unit : 𝓞 L) : L) = (ζ ^ k)⁻¹ * ∑ j ∈ Finset.range (2 * k + 1), ζ ^ j := by
    rw [IsUnit.unit_spec, ← hinv]
    change algebraMap (𝓞 L) L _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_pow, map_sum]
    rfl
  have hM0 : (0 : ℝ) < M := by positivity
  have key : ∀ a : ℕ, a.Coprime M → ∀ ψ : L →+* ℂ, ψ ζ = φ ζ ^ a → ψ ((hu.unit : 𝓞 L) : L) =
      ((Real.sin ((2 * k + 1 : ℕ) * (Real.pi * ((a : ℝ) / M))) / Real.sin (Real.pi * ((a : ℝ) / M)) : ℝ) : ℂ) := by
    intro a ha ψ hψ
    rw [hval, ← geom_sin k _ (sin_ne M a hM ha) (ψ ζ)]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_mul, map_pow, map_sum, map_inv₀]
    · rw [hψ, hφ, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
  refine ⟨hu.unit, ?_, ?_⟩
  · apply φ.injective
    have h2 : φ (cE L ((hu.unit : 𝓞 L) : L)) = starRingEnd ℂ (φ ((hu.unit : 𝓞 L) : L)) :=
      IsCMField.complexEmbedding_complexConj L φ _
    rw [h2, key 1 (Nat.coprime_one_left M) φ (pow_one _).symm, Complex.conj_ofReal]
  · funext t
    have ht := ZMod.val_coe_unit_coprime t
    have htl := ZMod.val_lt (t : ZMod M)
    have h1 : embT M L φ t ζ = φ ζ ^ (t : ZMod M).val := by
      change φ (sg M L t ζ) = _
      rw [sg_apply M L t hζ.pow_eq_one, map_pow]
    simp only [sgn]
    rw [key _ ht _ h1, Complex.ofReal_re]
    generalize (t : ZMod M).val = a at ht htl
    have hlt : (a : ℝ) / M < 1 := (div_lt_one hM0).2 (by exact_mod_cast htl)
    have hpos : 0 < Real.sin (Real.pi * ((a : ℝ) / M)) := by
      refine lt_of_le_of_ne (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_) (sin_ne M a hM ht).symm
      have := Real.pi_pos
      nlinarith
    have he : ((2 * k + 1 : ℕ) : ℝ) * (Real.pi * ((a : ℝ) / M)) = Real.pi * ((((2 * k + 1) * a : ℕ) : ℝ) / M) := by
      push_cast
      ring
    have hs := sinSign ((((2 * k + 1) * a : ℕ) : ℝ) / M) (by positivity) (sin_ne M _ hM (Nat.Coprime.mul_left hc ht))
    rw [Nat.floor_div_eq_div] at hs
    rw [he]
    simp only [div_lt_iff₀ hpos, zero_mul, hs]
    split_ifs with h
    · exact h.natCast_zmod_two
    · exact (Nat.not_odd_iff_even.1 h).natCast_zmod_two
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnAlg
open UpperTheory.V.FW

private theorem gen2 {G Q W : Type} [Group G] [Finite Q] [AddCommGroup W] (h2 : ∀ w : W, 2 • w = 0)
    (ψ : MonoidAlgebra ℤ G →+ W) (hψ : Function.Surjective ψ) (p : G → Q) (v : Q → W)
    (hv : ∀ g, ψ (MonoidAlgebra.single g 1) = v (p g)) :
    Finite W ∧ Nat.card W ≤ 2 ^ Nat.card Q := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Module (ZMod 2) W := AddCommGroup.zmodModule h2
  let φ : (Q → ZMod 2) →ₗ[ZMod 2] W := Fintype.linearCombination (ZMod 2) v
  have hs : Function.Surjective φ := by
    intro w
    obtain ⟨x, rfl⟩ := hψ w
    change ψ x ∈ (LinearMap.range φ).toAddSubgroup
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add ψ]; exact add_mem ha hb
    | single g n =>
      have : (MonoidAlgebra.single g n : MonoidAlgebra ℤ G) = n • MonoidAlgebra.single g 1 := by simp
      rw [this, map_zsmul]
      refine zsmul_mem ?_ _
      rw [hv]
      exact ⟨Pi.single (p g) 1, by simp [φ]⟩
  refine ⟨Finite.of_surjective φ hs, ?_⟩
  have := Nat.card_le_card_of_surjective φ hs
  simpa [Nat.card_fun] using this

private noncomputable def kap {G : Type} [CommGroup G] (J : G) : MonoidAlgebra ℤ G →+ (G → ZMod 2) where
  toFun x := fun g => (((x * (1 + MonoidAlgebra.of ℤ G J)).coeff g : ℤ) : ZMod 2)
  map_zero' := by ext g; simp
  map_add' a b := by ext g; simp [add_mul]

private theorem kap_apply {G : Type} [CommGroup G] {J : G} (hJ : J * J = 1) (x : MonoidAlgebra ℤ G) (g : G) :
    kap J x g = (x.coeff g : ZMod 2) + (x.coeff (J * g) : ZMod 2) := by
  have : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ
  simp [kap, mul_add, this, mul_comm J g]

private theorem kap_single_mul {G : Type} [CommGroup G] {J : G} (hJ : J * J = 1) (x : MonoidAlgebra ℤ G) (g : G) :
    kap J (MonoidAlgebra.single g 1 * x) = fun h => kap J x (g⁻¹ * h) := by
  ext h
  simp [kap_apply hJ, mul_left_comm]

private theorem kap_range {G : Type} [CommGroup G] [Finite G] {J : G} (hJ : J * J = 1) (hJ1 : J ≠ 1) :
    (kap J).range = evenF J := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩ g
    rw [kap_apply hJ, kap_apply hJ, ← mul_assoc, hJ, one_mul, add_comm]
  · intro f hf
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
    refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => if e g < e (J * g) then ((f g).val : ℤ) else 0), ?_⟩
    ext g
    have hne : e g ≠ e (J * g) := fun h => hJ1 (by simpa using e.injective h)
    have hfg : f (J * g) = f g := hf g
    rw [kap_apply hJ]
    simp only [MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm, ← mul_assoc, hJ, one_mul]
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, h.le]
    · simp [h, h.le, hfg]

theorem UpperTheory.V.FW.sgnAlg :
    ∀ (G : Type) [CommGroup G] [Finite G] (J γ : G) (θ : MonoidAlgebra ℤ G) (N : ℕ) (S : AddSubgroup (G → ZMod 2)), J * J = 1 → J ≠ 1 → (∀ f ∈ S, ∀ g, (fun x => f (g * x)) ∈ S) → (fun g => (((θ * (1 + MonoidAlgebra.of ℤ G J)).coeff g : ℤ) : ZMod 2)) ∈ S → (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, ((2 : ℕ) : MonoidAlgebra ℤ G)} → S.relIndex (evenF J) ≤ (2 ^ (Subgroup.zpowers γ).index) ^ N := by
  intro G _ _ J γ θ N S hJ hJ1 hS hθ hN
  have hdbl : ∀ y, kap J (y + y) ∈ S := fun y => by
    have : kap J (y + y) = 0 := by
      rw [map_add (f := _)]; ext g; simp [CharTwo.add_self_eq_zero]
    rw [this]; exact zero_mem _
  let I : Ideal (MonoidAlgebra ℤ G) :=
    { (S.comap (kap J)).toAddSubmonoid with
      smul_mem' := fun r x hx => by
        change kap J (r * x) ∈ S
        induction r using MonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => rw [add_mul, map_add (f := _)]; exact add_mem ha hb
        | single g n =>
          have : (MonoidAlgebra.single g n : MonoidAlgebra ℤ G) = n • MonoidAlgebra.single g 1 := by simp
          rw [this, smul_mul_assoc, map_zsmul, kap_single_mul hJ]
          exact zsmul_mem (hS _ hx _) _ }
  have hI : ∀ x, x ∈ I ↔ kap J x ∈ S := fun x => Iff.rfl
  have hNI : (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ I := by
    refine Ideal.span_le.2 ?_ hN
    rintro x (rfl | rfl | rfl)
    · exact hθ
    · change kap J _ ∈ S
      have : kap J (1 + MonoidAlgebra.of ℤ G J) = kap J (1 + 1) := by
        ext g
        have h1 : MonoidAlgebra.of ℤ G J * MonoidAlgebra.of ℤ G J = 1 := by rw [← map_mul, hJ, map_one]
        have : (1 + MonoidAlgebra.of ℤ G J) * (1 + MonoidAlgebra.of ℤ G J) = (1 + 1) * (1 + MonoidAlgebra.of ℤ G J) := by
          linear_combination h1
        simp only [kap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, this]
      rw [this]; exact hdbl 1
    · change kap J _ ∈ S
      have : ((2 : ℕ) : MonoidAlgebra ℤ G) = 1 + 1 := by norm_num
      rw [this]; exact hdbl 1
  have hidx : S.relIndex (evenF J) = Nat.card (MonoidAlgebra ℤ G ⧸ I) := by
    rw [← kap_range hJ hJ1, ← AddSubgroup.index_comap]
    rfl
  have h2 : ∀ w : MonoidAlgebra ℤ G ⧸ I, 2 • w = 0 := fun w => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [two_nsmul, ← map_add (f := _), Ideal.Quotient.eq_zero_iff_mem]
    exact hdbl x
  haveI hfin : Finite (MonoidAlgebra ℤ G ⧸ I) :=
    (gen2 h2 (Ideal.Quotient.mk I).toAddMonoidHom Ideal.Quotient.mk_surjective id
      (fun g => Ideal.Quotient.mk I (MonoidAlgebra.single g 1)) fun _ => rfl).1
  set t : MonoidAlgebra ℤ G ⧸ I := Ideal.Quotient.mk I (MonoidAlgebra.of ℤ G γ - 1) with ht
  let T : AddMonoid.End (MonoidAlgebra ℤ G ⧸ I) := Module.toAddMonoidEnd (MonoidAlgebra ℤ G ⧸ I) (MonoidAlgebra ℤ G ⧸ I) t
  have hT : T ^ N = 0 := by
    have : t ^ N = 0 := by rw [ht, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hNI
    rw [← map_pow, this, map_zero]
  rw [hidx]
  refine (nilCard _ T N hT).trans (Nat.pow_le_pow_left ?_ N)
  let ψ : MonoidAlgebra ℤ G →+ (MonoidAlgebra ℤ G ⧸ I) ⧸ AddMonoidHom.range T :=
    (QuotientAddGroup.mk' _).comp (Ideal.Quotient.mk I).toAddMonoidHom
  have hstep : ∀ g, ψ (MonoidAlgebra.single (γ * g) 1) = ψ (MonoidAlgebra.single g 1) := fun g => by
    rw [← sub_eq_zero, ← map_sub]
    refine (QuotientAddGroup.eq_zero_iff _).2 ⟨Ideal.Quotient.mk I (MonoidAlgebra.single g 1), ?_⟩
    change t * _ = Ideal.Quotient.mk I _
    rw [ht, ← map_mul, sub_mul]
    simp [MonoidAlgebra.single_mul_single]
  have hpow : ∀ (n : ℕ) g, ψ (MonoidAlgebra.single (γ ^ n * g) 1) = ψ (MonoidAlgebra.single g 1) := fun n g => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, hstep, ih]
  refine (gen2 (Q := G ⧸ Subgroup.zpowers γ) ?_ ψ ?_ QuotientGroup.mk
    (fun q => ψ (MonoidAlgebra.single q.out 1)) ?_).2
  · intro w
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ w
    rw [← map_nsmul, h2, map_zero]
  · exact (QuotientAddGroup.mk'_surjective _).comp Ideal.Quotient.mk_surjective
  · intro g
    obtain ⟨⟨h, hh⟩, e⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.zpowers γ) g
    obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hh)
    simp only at e ⊢
    rw [e, mul_comm, hpow]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.sgnCyc :
    ∀ (f n c N : ℕ) [NeZero (f * 2 ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * 2 ^ n} ℚ L] [IsCMField L] (γ : (ZMod (f * 2 ^ n))ˣ), Odd f → 1 < f → 2 ≤ n → c.Coprime (f * 2 ^ n) → Odd c → (MonoidAlgebra.of ℤ _ γ - 1) ^ N ∈ Ideal.span {thetaH (f * 2 ^ n) c, 1 + MonoidAlgebra.of ℤ _ (-1 : (ZMod (f * 2 ^ n))ˣ), ((2 : ℕ) : MonoidAlgebra ℤ (ZMod (f * 2 ^ n))ˣ)} → (difR (clMap (cE L))).relIndex (minK (clMap (cE L))) ≤ (2 ^ (Subgroup.zpowers γ).index) ^ N := by
  intro f n c N _ L _ _ _ _ γ hf hf1 hn hc ho hmem
  have hM : 2 < f * 2 ^ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    nlinarith
  obtain ⟨φ, hφ⟩ := sgnUnit (f * 2 ^ n) c L hc ho hM
  obtain ⟨h1, h2, h3, h4⟩ := sgnStab (f * 2 ^ n) L φ
  refine (hMinus L _ (embT (f * 2 ^ n) L φ) (evenF (-1 : (ZMod (f * 2 ^ n))ˣ))
    (unrJ f n L hf hf1 hn) (unitSurj f n L hf hf1 hn) h1 h2).trans ?_
  haveI : Fact (2 < f * 2 ^ n) := ⟨hM⟩
  refine sgnAlg _ (-1) γ (thetaH (f * 2 ^ n) c) N _ (by simp) ?_ h3 ?_ hmem
  · intro h
    have h' := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    exact ZMod.neg_one_ne_one h'
  · have h5 := (sgnE (embT (f * 2 ^ n) L φ)).sub_mem (h3 _ hφ (ZMod.unitOfCoprime c hc)⁻¹)
      ((sgnE (embT (f * 2 ^ n) L φ)).nsmul_mem h4 ((c - 1) / 2))
    convert h5 using 1
    funext s
    rw [(thetaFull (f * 2 ^ n) c hc ho hM).2 s]
    have hi : (((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod (f * 2 ^ n))ˣ) : ZMod (f * 2 ^ n)) = (c : ZMod (f * 2 ^ n))⁻¹ := by
      rw [← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime]
    rw [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, mul_one]
    simp only [gc, Units.val_mul, hi, Int.cast_sub, Int.cast_natCast]
