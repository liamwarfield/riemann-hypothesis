module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

variable {l : ℕ} [Fact l.Prime]

private theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c := c) ((u : c.O)).2
  have h2 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c := c) (((u⁻¹ : c.Oˣ) : c.O)).2
  have h3 : ((u : c.O) : PadicAlgCl l) * (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  have h4 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, h3, norm_one]
  nlinarith [norm_nonneg ((u : c.O) : PadicAlgCl l), norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)]

private theorem norm_pos_and_lt_one_of_irreducible (c : Coef l) (ϖ : c.O) (hϖ : Irreducible ϖ) :
    0 < ‖(ϖ : PadicAlgCl l)‖ ∧ ‖(ϖ : PadicAlgCl l)‖ < 1 := by
  haveI := c.dvr
  have hne : (ϖ : PadicAlgCl l) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  refine ⟨norm_pos_iff.2 hne, ?_⟩
  have hl : (l : c.O) ≠ 0 := by
    intro h
    apply (GlobalTheory.LambdaValuationPowers.natCast_ne_zero (l := l))
    have := congrArg (fun z : c.O => (z : PadicAlgCl l)) h
    simpa using this
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  have h1 : ‖((l : c.O) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ e := by
    rw [he]
    push_cast
    rw [norm_mul, norm_unit c u, one_mul, norm_pow]
  have h2 : ‖((l : c.O) : PadicAlgCl l)‖ < 1 := by
    have := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)
    simpa using this
  have h3 : ‖(ϖ : PadicAlgCl l)‖ ≤ 1 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem ϖ.2
  rcases h3.lt_or_eq with h | h
  · exact h
  · rw [h1, h, one_pow] at h2
    exact absurd h2 (lt_irrefl 1)

private theorem dvd_of_norm_le (c : Coef l) (x y : c.O) (hy : y ≠ 0)
    (h : ‖(x : PadicAlgCl l)‖ ≤ ‖(y : PadicAlgCl l)‖) : y ∣ x := by
  haveI := c.dvr
  by_cases hx : x = 0
  · rw [hx]
    exact dvd_zero y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨h0, h1⟩ := norm_pos_and_lt_one_of_irreducible c ϖ hϖ
  have hn : ∀ (k : ℕ) (w : c.Oˣ),
      ‖(((w : c.O) * ϖ ^ k : c.O) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ k := by
    intro k w
    push_cast
    rw [norm_mul, norm_unit c w, one_mul, norm_pow]
  obtain ⟨a, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨b, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [hn, hn] at h
  have hba : b ≤ a := (pow_le_pow_iff_right_of_lt_one₀ h0 h1).1 h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hba
  refine ⟨((v⁻¹ : c.Oˣ) : c.O) * u * ϖ ^ k, ?_⟩
  calc (u : c.O) * ϖ ^ (b + k) = ((v : c.O) * ((v⁻¹ : c.Oˣ) : c.O)) * u * ϖ ^ (b + k) := by
        rw [Units.mul_inv, one_mul]
    _ = _ := by ring

private theorem div_pow_of_cg (c : Coef l) (n : ℕ) (x : c.O) (h : Cg n (x : PadicAlgCl l) 0) :
    ∃ y : c.O, x = (l : c.O) ^ n * y := by
  have hl0 : (l : c.O) ≠ 0 := fun h0 => GlobalTheory.LambdaValuationPowers.natCast_ne_zero (l := l) (by simpa using congrArg Subtype.val h0)
  refine dvd_of_norm_le c x _ (pow_ne_zero n hl0) ?_
  simpa [Cg] using h

theorem pBasEx : SBasEx := by
  intro l _ c
  haveI := c.fin
  haveI := c.dvr
  refine ⟨⟨⟨_, Module.finBasis ℤ_[l] c.O⟩⟩, fun β => ⟨fun i => GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (β.e i).2,
    ?_, fun n x h => div_pow_of_cg c n x h, ?_⟩⟩
  · intro n x h i
    have hzc : ((∑ j, x j • β.e j : c.O) : PadicAlgCl l)
        = ∑ j, β.val j * algebraMap ℤ_[l] (PadicAlgCl l) (x j) := by
      simp [Bas.val, Algebra.smul_def, mul_comm]
    obtain ⟨y, hy⟩ := div_pow_of_cg c n (∑ j, x j • β.e j) (by rw [hzc]; exact h)
    have hs : (∑ j, x j • β.e j : c.O) = ((l : ℤ_[l]) ^ n) • y := by
      rw [hy, Algebra.smul_def, map_pow, map_natCast]
    have hx : β.e.repr (∑ j, x j • β.e j) i = x i := by
      rw [β.e.repr_sum_self]
    refine ⟨β.e.repr y i, ?_⟩
    rw [← hx, hs, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · intro x hx h1
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at h1
    obtain ⟨z, hz⟩ := dvd_of_norm_le c 1 ⟨x, hx⟩
      (fun h0 => hx0 (by simpa using congrArg Subtype.val h0)) (by simp [h1])
    have hz' : (1 : PadicAlgCl l) = x * (z : PadicAlgCl l) := by
      have := congrArg Subtype.val hz
      simpa using this
    rw [← eq_inv_of_mul_eq_one_right hz'.symm]
    exact z.2

end UpperTheory.Kd.C7
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem frobEx_norm {l : ℕ} (hl : l.Prime) {v : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : normV v = l := by
  haveI : Fact l.Prime := ⟨hl⟩
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = v.asIdeal.map (e : 𝓞 ℚ →+* ℤ) := by
    have hmax : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
    apply hmax.eq_of_le
    · intro htop
      apply v.isPrime.ne_top
      exact (Ideal.map_eq_top_of_bijective _ e.bijective).1 htop
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have := Ideal.mem_map_of_mem (e : 𝓞 ℚ →+* ℤ) hv
      simpa using this
  unfold normV
  rw [Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ e hJ).toEquiv,
    Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]

theorem UpperTheory.Kd.C7.pFrobEx :
    UpperTheory.Kd.C7.SFrobEx := by
  intro l _ _ Ω _ _ _ A hA
  obtain ⟨v, hv, hlv⟩ := hA
  have hnorm : normV v = l := frobEx_norm Fact.out hlv
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  refine ⟨?_, fun σ _ σ' _ hσ hσ' => inv_mul_mem_Ine_of_isFrob hσ hσ',
    GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval⟩
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hv
  rw [hnorm] at hσ
  obtain ⟨ι, hι, hιu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval (cycZ ℚ Ω l σ)⁻¹
  have hfr : IsFrob A l (σ * ι) := isFrob_mul_of_mem_Ine hσ hι
  refine ⟨σ * ι, hfr.1, hfr, ?_⟩
  unfold cycBar
  rw [MonoidHom.comp_apply, map_mul, hιu, mul_inv_cancel, map_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem wd_irr (R : Type) [CommRing R] [IsDomain R] (l : ℕ) [hl : Fact l.Prime] (hp : Prime (l : R)) (n : ℕ) :
    Irreducible (Polynomial.cyclotomic (l ^ (n + 1)) R) := by
  classical
  have hlpos : 0 < l := hl.out.pos
  set fZ := (Polynomial.cyclotomic (l ^ (n + 1)) ℤ).comp (Polynomial.X + Polynomial.C 1) with hfZ
  set g := (Polynomial.cyclotomic (l ^ (n + 1)) R).comp (Polynomial.X + Polynomial.C 1) with hg
  have hgZ : g = fZ.map (Int.castRingHom R) := by
    rw [hg, hfZ, Polynomial.map_comp, Polynomial.map_cyclotomic]
    simp
  have hE : fZ.IsEisensteinAt (Submodule.span ℤ {(l : ℤ)}) := by
    rw [hfZ, Polynomial.C_1]
    exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt l n
  have hq : (Polynomial.X + Polynomial.C (1 : R)).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_X_add_C]
    exact one_ne_zero
  have hqZ : (Polynomial.X + Polynomial.C (1 : ℤ)).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_X_add_C]
    exact one_ne_zero
  have hmon : g.Monic := (Polynomial.cyclotomic.monic _ R).comp (Polynomial.monic_X_add_C 1) hq
  have hmonZ : fZ.Monic := (Polynomial.cyclotomic.monic _ ℤ).comp (Polynomial.monic_X_add_C 1) hqZ
  have hdeg : g.natDegree = fZ.natDegree := by
    rw [hgZ, hmonZ.natDegree_map]
  have hP : (Ideal.span {(l : R)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hgpos : 0 < g.natDegree := by
    rw [hg, Polynomial.natDegree_comp, Polynomial.natDegree_cyclotomic, Polynomial.natDegree_X_add_C,
      mul_one]
    exact Nat.totient_pos.2 (pow_pos hlpos _)
  have hirr : Irreducible g := by
    apply Polynomial.irreducible_of_eisenstein_criterion hP
    · rw [hmon.leadingCoeff]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro k hk
      have hk' : k < fZ.natDegree := by
        rw [← hdeg]
        exact Polynomial.coe_lt_degree.mp hk
      have hmem := hE.mem hk'
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hmem
      rw [hgZ, Polynomial.coeff_map, Ideal.mem_span_singleton]
      have := map_dvd (Int.castRingHom R) hmem
      simpa using this
    · exact Polynomial.natDegree_pos_iff_degree_pos.mp hgpos
    · rw [Polynomial.coeff_zero_eq_eval_zero, hg, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C, zero_add, Polynomial.eval_one_cyclotomic_prime_pow,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨a, ha⟩
      apply hp.not_unit
      have h1 : (l : R) * 1 = (l : R) * ((l : R) * a) := by
        rw [mul_one]
        calc (l : R) = (l : R) ^ 2 * a := ha
          _ = (l : R) * ((l : R) * a) := by ring
      have h2 := mul_left_cancel₀ hp.ne_zero h1
      exact isUnit_iff_exists_inv.2 ⟨a, h2.symm⟩
    · exact hmon.isPrimitive
  have ht : (Polynomial.taylorEquiv (1 : R)) (Polynomial.cyclotomic (l ^ (n + 1)) R) = g := by
    rw [hg, ← Polynomial.taylor_apply]
    rfl
  rw [← ht] at hirr
  exact (MulEquiv.irreducible_iff _).1 hirr

private theorem wd_val {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) : ValuationRing (R0 A) := by
  refine { cond' := ?_ }
  intro a b
  have ha : (a : Ω) ∈ A ∧ ∀ s ∈ Ine A, s (a : Ω) = a := a.2
  have hb : (b : Ω) ∈ A ∧ ∀ s ∈ Ine A, s (b : Ω) = b := b.2
  by_cases ha0 : (a : Ω) = 0
  · refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    simp [ha0]
  by_cases hb0 : (b : Ω) = 0
  · refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simp [hb0]
  rcases A.mem_or_inv_mem ((b : Ω) / a) with h | h
  · have hc : (b : Ω) / a ∈ R0 A := by
      refine ⟨h, fun s hs => ?_⟩
      rw [map_div₀, ha.2 s hs, hb.2 s hs]
    refine ⟨⟨_, hc⟩, Or.inl ?_⟩
    apply Subtype.ext
    simp [mul_div_cancel₀ _ ha0]
  · rw [inv_div] at h
    have hc : (a : Ω) / b ∈ R0 A := by
      refine ⟨h, fun s hs => ?_⟩
      rw [map_div₀, ha.2 s hs, hb.2 s hs]
    refine ⟨⟨_, hc⟩, Or.inr ?_⟩
    apply Subtype.ext
    simp [mul_div_cancel₀ _ hb0]

private theorem wd_res {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (l : ℕ) [hl : Fact l.Prime]
    (h : A.valuation (l : Ω) < 1) (m : ℕ) (z : Ω) (hz : z ^ l ^ m = 1) :
    z ∈ A ∧ A.valuation (z - 1) < 1 := by
  have hN : l ^ m ≠ 0 := pow_ne_zero _ hl.out.ne_zero
  have hvz : A.valuation z = 1 := by
    have h1 : A.valuation z ^ (l ^ m) = 1 := by
      rw [← map_pow, hz, map_one]
    rcases lt_trichotomy (A.valuation z) 1 with h2 | h2 | h2
    · exact absurd h1 (ne_of_lt (pow_lt_one₀ zero_le' h2 hN))
    · exact h2
    · exact absurd h1 (ne_of_gt (one_lt_pow₀ h2 hN))
  have hzA : z ∈ A := (A.valuation_le_one_iff z).1 hvz.le
  refine ⟨hzA, ?_⟩
  let zA : A := ⟨z, hzA⟩
  have hlmax : (l : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [A.valuation_lt_one_iff]
    simpa using h
  haveI : CharP (IsLocalRing.ResidueField A) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out]
    have := (IsLocalRing.residue_eq_zero_iff _).2 hlmax
    simpa using this
  have hzN : zA ^ (l ^ m) = 1 := Subtype.ext (by simpa using hz)
  have hres : (IsLocalRing.residue A zA - 1) ^ (l ^ m) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← map_pow, hzN, map_one, sub_self]
  have h0 := (pow_eq_zero_iff hN).1 hres
  have hmem : zA - 1 ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one]
    exact h0
  have := (A.valuation_lt_one_iff (zA - 1)).1 hmem
  simpa using this

private theorem prime_natCast_r0_of_valuation_lt_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (j : Ω →+* Qbar l) (Φ : Fr l A j) (hval : A.valuation (l : Ω) < 1) :
    Prime (l : R0 A) := by
  have hl0 : (l : R0 A) ≠ 0 := by
    intro h0
    have h1 : ((l : R0 A) : Ω) = 0 := by
      rw [h0]
      rfl
    push_cast at h1
    rw [← map_natCast (algebraMap ℚ Ω)] at h1
    have h2 := (map_eq_zero_iff _ (algebraMap ℚ Ω).injective).1 h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  refine ⟨hl0, ?_, ?_⟩
  · intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hw' : (l : Ω) * (w : Ω) = 1 := by
      have := congrArg Subtype.val hw
      simpa using this
    have h2 : A.valuation (l : Ω) * A.valuation (w : Ω) < 1 :=
      (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 w.2.1)).trans_lt hval
    rw [← map_mul, hw', map_one] at h2
    exact lt_irrefl 1 h2
  · intro a b hab
    have hab' : (l : Φ.R) ∣ Φ.i0 a * Φ.i0 b := by
      have := map_dvd Φ.i0 hab
      simpa [map_mul] using this
    have hback : ∀ c : R0 A, (l : Φ.R) ∣ Φ.i0 c → (l : R0 A) ∣ c := by
      intro c hc
      have := Φ.sep c 1 (by rw [pow_one]; exact Ideal.mem_span_singleton.2 hc)
      rw [pow_one] at this
      exact Ideal.mem_span_singleton.1 this
    rcases Φ.fl.prime.2.2 _ _ hab' with h | h
    · exact Or.inl (hback a h)
    · exact Or.inr (hback b h)

theorem UpperTheory.Kd.C7.pWD :
    UpperTheory.Kd.C7.SWD := by
  intro l _ _ Ω _ _ _ A hA j Φ ζ hζ m hm P
  obtain ⟨v, hv, hlv⟩ := hA
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  haveI := wd_val A
  have hroot : ∀ i : ℕ, (ζ m ^ i) ^ l ^ m = 1 := by
    intro i
    rw [← pow_mul, mul_comm, pow_mul, (hζ m).1.pow_eq_one, one_pow]
  have hdiff : pv P (ζ m) - ((P.eval 1 : R0 A) : Ω)
      = ∑ i ∈ Finset.range (P.natDegree + 1), ((P.coeff i : R0 A) : Ω) * (ζ m ^ i - 1) := by
    rw [pv, Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_sub]
  have hcc : PowerSeries.constantCoeff (Φ.ser P) = Φ.i0 (P.eval 1) := by
    unfold Fr.ser
    rw [Polynomial.hom_eval₂]
    simp
  constructor
  · intro hP
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hirr := wd_irr (R0 A) l (prime_natCast_r0_of_valuation_lt_one l A j Φ hval) k
    classical
    letI := IsBezout.toGCDDomain (R0 A)
    have hcycroot : Polynomial.aeval (ζ (k + 1)) (Polynomial.cyclotomic (l ^ (k + 1)) (R0 A)) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact (hζ (k + 1)).1.isRoot_cyclotomic (pow_pos (Fact.out : l.Prime).pos _)
    have hint : IsIntegral (R0 A) (ζ (k + 1)) := ⟨_, Polynomial.cyclotomic.monic _ _, hcycroot⟩
    have hdvdP : minpoly (R0 A) (ζ (k + 1)) ∣ P := minpoly.isIntegrallyClosed_dvd hint hP
    have hdvdC : minpoly (R0 A) (ζ (k + 1)) ∣ Polynomial.cyclotomic (l ^ (k + 1)) (R0 A) :=
      minpoly.isIntegrallyClosed_dvd hint hcycroot
    obtain ⟨q, hq⟩ := hdvdC
    have hqu : IsUnit q := (hirr.isUnit_or_isUnit hq).resolve_left (minpoly.not_isUnit _ _)
    have hCP : Polynomial.cyclotomic (l ^ (k + 1)) (R0 A) ∣ P := by
      refine dvd_trans ?_ hdvdP
      rw [hq]
      exact hqu.mul_right_dvd.2 dvd_rfl
    obtain ⟨Q, hQ⟩ := hCP
    unfold Fr.ser
    rw [hQ, Polynomial.map_mul, Polynomial.eval₂_mul, Polynomial.map_cyclotomic, map_mul]
    have hc : Polynomial.eval₂ PowerSeries.C (1 + PowerSeries.X)
        (Polynomial.cyclotomic (l ^ (k + 1)) Φ.R) = cyc Φ.R l (k + 1) := rfl
    rw [hc, ev_cyc_self, zero_mul]
  · rintro ⟨hA1, hne, hinv⟩
    rw [PowerSeries.isUnit_iff_constantCoeff, hcc]
    apply Φ.unit
    intro hmem
    have hy : P.eval 1 ∈ Ideal.span {(l : R0 A)} := by
      have := Φ.sep (P.eval 1) 1 (by rw [pow_one]; exact hmem)
      rwa [pow_one] at this
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hy
    have hvy : A.valuation ((P.eval 1 : R0 A) : Ω) < 1 := by
      rw [← ha]
      push_cast
      rw [map_mul]
      exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 a.2.1)).trans_lt hval
    have hvd : A.valuation (pv P (ζ m) - ((P.eval 1 : R0 A) : Ω)) < 1 := by
      rw [hdiff]
      apply Valuation.map_sum_lt _ one_ne_zero
      intro i _
      rw [map_mul]
      refine (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (P.coeff i).2.1)).trans_lt ?_
      exact (wd_res A l hval m _ (hroot i)).2
    have hvp : A.valuation (pv P (ζ m)) < 1 := by
      have := Valuation.map_add_lt _ hvd hvy
      simpa using this
    have h1 : A.valuation (pv P (ζ m)) * A.valuation (pv P (ζ m))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    have h2 : A.valuation (pv P (ζ m)) * A.valuation (pv P (ζ m))⁻¹ < 1 :=
      (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hinv)).trans_lt hvp
    rw [h1] at h2
    exact lt_irrefl 1 h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumAlg
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem ka_pw {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {z : Ω} (hz : z ^ N = 1) (a : ℕ) (k : ZMod N)
    (h : (a : ZMod N) = k) : z ^ k.val = z ^ a := by
  rw [← h, ZMod.val_natCast]
  exact (pow_eq_pow_mod a hz).symm

private theorem ka_down {Ω : Type} [Field Ω] {l : ℕ} {ζ : ℕ → Ω} (h : ∀ m, ζ (m + 1) ^ l = ζ m) (n d : ℕ) :
    ζ (n + d) ^ l ^ d = ζ n := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ', pow_mul, ← Nat.add_assoc, h, ih]

theorem UpperTheory.Kd.C7.pKumAlg :
    UpperTheory.Kd.C7.SKumAlg := by
  intro l hl _ Ω _ _ _ A _ ζ hζ m n _ s _
  have hne : ∀ r : ℕ, NeZero (l ^ r) := fun r => ⟨(pow_pos hl.out.pos r).ne'⟩
  have h1 : ∀ r, ζ r ^ l ^ r = 1 := fun r => (hζ r).1.pow_eq_one
  haveI := hne n
  refine ⟨?_, ?_, ?_⟩
  · rintro u u' k k' ⟨v, rfl, hv⟩ ⟨v', rfl, hv'⟩
    refine ⟨⟨v * v', mul_pow _ _ _, ?_⟩, ⟨v⁻¹, inv_pow _ _, ?_⟩, fun a => ⟨v ^ a, ?_, ?_⟩⟩
    · rw [map_mul, hv, hv', ka_pw (h1 n) (k.val + k'.val) (k + k') (by simp), pow_add]
      ring
    · have e : ζ n ^ (-k).val * ζ n ^ k.val = 1 := by
        rw [← pow_add, ← ka_pw (h1 n) ((-k).val + k.val) 0 (by simp), ZMod.val_zero, pow_zero]
      rw [map_inv₀, hv, mul_inv, eq_inv_of_mul_eq_one_left e]
    · rw [← pow_mul, ← pow_mul, mul_comm]
    · rw [map_pow, hv, ka_pw (h1 n) (k.val * a) (a * k) (by simp [mul_comm]), mul_pow, pow_mul]
  · rintro u k n' hn' - ⟨v, rfl, hv⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn'
    haveI := hne n'
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, add_comm], ?_⟩
    rw [map_pow, hv, ka_pw (h1 n') k.val _ rfl, mul_pow, ← pow_mul, mul_comm k.val, pow_mul,
      ka_down (fun r => (hζ r).2)]
  · rintro u k t ⟨v, hu, hv⟩
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
    have ht : t (ζ n) = ζ n ^ ((cycMod ℚ Ω l n t : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω t) (ζ n) (h1 n)
    refine ⟨t v, ?_, ?_⟩
    · rw [← map_pow, hu, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    · rw [← AlgEquiv.mul_apply, inv_mul_cancel_right, AlgEquiv.mul_apply, hv, map_mul, map_pow, ht, ← pow_mul,
        ka_pw (h1 n) (((cycMod ℚ Ω l n t : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val * k.val) _ (by simp)]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresMono
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

private theorem roots_pow {Ω : Type} [Field Ω] {l : ℕ} {ζ : ℕ → Ω} (h : Roots l ζ) (n d : ℕ) :
    ζ (n + d) ^ l ^ d = ζ n := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ', pow_mul, ← add_assoc, (h (n + d)).2, ih]

private theorem nat_le_one {l : ℕ} [Fact l.Prime] (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a

private theorem add_le {l : ℕ} [Fact l.Prime] {a b : Qbar l} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max (S := PadicAlgCl l) a b).trans (max_le ha hb)

theorem pPresMono : SPresMono := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ Z Z' m n n' P hn hZ hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hlp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hlp.pos i).ne'⟩
    infer_instance
  haveI : NeZero (l ^ n') := ⟨(pow_pos hlp.pos n').ne'⟩
  refine ⟨(hζ n').1, hn.trans h2, h3, h4, fun s hs hc _ => ?_⟩
  obtain ⟨k, hk, hcg⟩ := h5 s hs hc (fix_of_cycMod h2 hc h1.pow_eq_one)
  refine ⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩
  · obtain ⟨v, hv, hsv⟩ := hk i
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, add_comm d n', hv], ?_⟩
    rw [map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, roots_pow hζ, ZMod.val_natCast]
    congr 1
    conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n'), pow_add, pow_mul, (hζ n').1.pow_eq_one, one_pow, one_mul]
  · have hz := hZ s ⟨hs, hc⟩
    unfold Cg at hz hcg ⊢
    have e1 : ‖Z m s 1 - ∑ i, β.val i * (((k i).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      refine hcg.trans ?_
      rw [pow_add, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      exact_mod_cast nat_le_one (l := l) (l ^ d)
    have e2 : ‖∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ 1 := by
      refine Finset.sum_induction _ (fun x : Qbar l => ‖x‖ ≤ 1) (fun a b => add_le) (by simp) (fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_one₀ (h4 i) (norm_nonneg _) (nat_le_one _)
    have e3 : ‖((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) e2
    rw [norm_sub_rev] at hz
    have e4 : ∑ i, β.val i * (((k i).val : ℕ) : Qbar l) =
        ((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l)) +
        ∑ i, β.val i * (((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ZMod.val_natCast]
      conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n')]
      push_cast
      ring
    have := add_le (add_le hz e1) e3
    rw [e4] at this
    convert this using 2
    ring

end UpperTheory.Kd.C7
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PConj
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

theorem pConj : SConj := by
  intro l _ _ Ω _ _ _ A _ c Z hZ m s hs t ht
  have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
  have hsk : cycMod ℚ Ω l m s = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).2
  have hti : t⁻¹ ∈ Ine (F := ℚ) A := inv_mem ht
  have h1I : (1 : G ℚ Ω) ∈ Ine (F := ℚ) A := one_mem _
  refine ⟨Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hsI) hti, ?_⟩, fun x => ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_mul, hsk, mul_one, ← map_mul, mul_inv_cancel, map_one]
  · have h0 : Z m 1 x = 0 := by
      have h := hZ.coc m 1 h1I 1 h1I x
      rw [mul_one, map_one, inv_one, mul_one] at h
      linear_combination -h
    have h2 := hZ.coc m t ht t⁻¹ hti x
    rw [mul_inv_cancel, h0] at h2
    have h3 := hZ.coc m t ht (s * t⁻¹) (mul_mem hsI hti) x
    have h4 := hZ.coc m s hsI t⁻¹ hti (x * (cycMod ℚ Ω l m t)⁻¹)
    rw [hsk, inv_one, mul_one] at h4
    rw [mul_assoc, h3, h4]
    linear_combination -h2

end UpperTheory.Kd.C7
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumTriv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

theorem UpperTheory.Kd.C7.pKumTriv :
    UpperTheory.Kd.C7.SKumTriv := by
  intro l _ _ Ω _ _ _ A _ ζ hζ m n hnm u hu h
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
    exact ⟨⟨ζ i, (hζ i).1⟩, inferInstance⟩
  have hpos : 0 < l ^ n := pow_pos hp.pos n
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq u hpos
  refine ⟨v, hv, fun s hs => ?_⟩
  obtain ⟨w, hw, hsw⟩ := h s hs
  rw [ZMod.val_zero, pow_zero, one_mul] at hsw
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hu (by rw [← hw, zero_pow hpos.ne'])
  have h1 : (v / w) ^ (l ^ n) = 1 := by rw [div_pow, hv, hw, div_self hu]
  have hc : cycMod ℚ Ω l m s = 1 := (Subgroup.mem_inf.1 hs).2
  have h2 : s (v / w) = v / w := fix_of_cycMod hnm hc h1
  have e : v = v / w * w := by field_simp
  calc s v = s (v / w * w) := by rw [← e]
    _ = v / w * w := by rw [map_mul, h2, hsw]
    _ = v := e.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DlogCmp
noncomputable section

open GlobalTheory.Col

namespace UpperTheory.Kd.C7

theorem pDlogCmp : SDlogCmp := by
  intro R _ p hp m n N hm F g w hF hg hw hL
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  set k := min n (min (j + 1 - 1) N) with hk
  have hkn : k ≤ n := by omega
  have hkj : k ≤ j := by omega
  have hkN : k ≤ N := by omega
  set D := PowerSeries.derivative (R := R) with hD
  set W := w ^ p ^ n with hW
  let J : Ideal (PowerSeries R) := Ideal.span {(p : PowerSeries R) ^ k, cyc R p (j + 1)}
  have hpow : ∀ i, k ≤ i → ∀ y : PowerSeries R, (p : PowerSeries R) ^ i * y ∈ J := by
    intro i hi y
    have e : (p : PowerSeries R) ^ i * y = (p : PowerSeries R) ^ k * ((p : PowerSeries R) ^ (i - k) * y) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi]
    rw [e]
    exact J.mul_mem_right _ (Ideal.subset_span (by simp))
  have hcyc : ∀ y, cyc R p (j + 1) * y ∈ J := fun y =>
    J.mul_mem_right _ (Ideal.subset_span (by simp))
  have hev : ∀ x ∈ J, ev R p (j + 1) x ∈ Ideal.span {((p : ℕ) : lev R p (j + 1)) ^ k} := by
    intro x hx
    have hle : J ≤ (Ideal.span {((p : ℕ) : lev R p (j + 1)) ^ k}).comap (ev R p (j + 1)) := by
      rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · simp only [SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
        exact Ideal.subset_span rfl
      · simp only [SetLike.mem_coe, Ideal.mem_comap]
        have h0 : ev R p (j + 1) (cyc R p (j + 1)) = 0 := by
          unfold ev
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        rw [h0]
        exact Ideal.zero_mem _
    exact hle hx
  obtain ⟨a, b, hab⟩ : ∃ a b : PowerSeries R,
      F - g * W = (p : PowerSeries R) ^ N * a + cyc R p (j + 1) * b := by
    unfold LC at hL
    rw [← map_sub] at hL
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hL
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {cyc R p (j + 1)}) c
    have h0 : ev R p (j + 1) (F - g * W - (p : PowerSeries R) ^ N * a) = 0 := by
      have hea : ev R p (j + 1) a = c := by
        unfold ev
        exact ha
      rw [map_sub, ← hc, map_mul, map_pow, map_natCast, hea, mul_comm]
      exact sub_self _
    unfold ev at h0
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    exact ⟨a, b, by linear_combination -hb⟩
  have hEJ : F - g * W ∈ J := by
    rw [hab]
    exact J.add_mem (hpow N hkN a) (hcyc b)
  have hDcyc : D (cyc R p (j + 1)) ∈ J := by
    have hc : cyc R p (j + 1) = ∑ i ∈ Finset.range p, (1 + PowerSeries.X) ^ (p ^ j * i) := by
      unfold cyc
      rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp.out, Polynomial.eval₂_finsetSum]
      simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Derivation.leibniz_pow, map_add (f := _), Derivation.map_one_eq_zero, PowerSeries.derivative_X,
      zero_add, smul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, mul_assoc]
    exact hpow j hkj _
  have hDE : D (F - g * W) ∈ J := by
    rw [hab, map_add (f := _), Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow,
      Derivation.map_natCast]
    simp only [smul_zero, mul_zero, add_zero, smul_eq_mul]
    exact J.add_mem (hpow N hkN _) (J.add_mem (hcyc _) (J.mul_mem_left _ hDcyc))
  have hDW : D W ∈ J := by
    rw [hW, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.cast_pow]
    exact hpow n hkn _
  have hdd : ∀ x, dd x = (1 + PowerSeries.X) * D x := by
    intro x
    unfold dd
    rfl
  have hFi := Ring.mul_inverse_cancel F hF
  have hgi := Ring.mul_inverse_cancel g hg
  have key : dl F - dl g =
      Ring.inverse F * Ring.inverse g * ((1 + PowerSeries.X) * (D F * g - D g * F)) := by
    unfold dl
    rw [hdd F, hdd g]
    linear_combination (-(1 + PowerSeries.X) * D F * Ring.inverse F) * hgi +
      ((1 + PowerSeries.X) * D g * Ring.inverse g) * hFi
  have hmid : D F * g - D g * F = g * g * D W + g * D (F - g * W) - D g * (F - g * W) := by
    have hDF : D F = D (F - g * W) + g * D W + W * D g := by
      rw [map_sub, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [hDF]
    ring
  unfold LC
  rw [← map_sub]
  apply hev
  rw [key]
  refine J.mul_mem_left _ (J.mul_mem_left _ ?_)
  rw [hmid]
  exact J.sub_mem (J.add_mem (J.mul_mem_left _ hDW) (J.mul_mem_left _ hDE)) (J.mul_mem_left _ hEJ)

end UpperTheory.Kd.C7
end
end
