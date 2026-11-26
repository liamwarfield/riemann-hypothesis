module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.ConjLoc
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.conjLoc :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.ConjLoc := by
  intro E _ _ _ a u
  have hp : ∀ (b : Af E) (v : Plc E), b v = pLoc E v b := fun _ _ => rfl
  refine ⟨fun h => ?_, ?_, fun m => ?_, ?_, continuous_conjFin _⟩
  · rw [hp, pLoc_conjFin, ← hp, h, map_one]
  · rw [hp, pLoc_conjFin, (conjLoc_spec (conjE E) u).2.2, ← hp]
  · have h := (conjLoc_spec (conjE E) u).2.2 ((m : ℕ) : (cj u).adicCompletion E)
    rwa [map_natCast] at h
  · refine FiniteAdeleRing.ext (R := 𝓞 E) E fun v => ?_
    rw [hp, hp a, pLoc_conjFin, pLoc_conjFin, GlobalTheory.SplitPts.conjLoc_pLoc, GlobalTheory.SplitPts.conjLoc_psi]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.KPlace
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnipotentFundamentalDomain
theorem UpperTheory.Reformulated.B.UnipotentFundamentalDomain.val_two :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K],
    Module.finrank ℚ K ≤ (2 : ℕ) →
      ∀ (P Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        P ≠ Q →
          Ideal.under ℤ P.asIdeal = Ideal.under ℤ Q.asIdeal →
            (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion K P → WithZero (Multiplicative ℤ))
                (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) P.asIdeal) :
                  IsDedekindDomain.HeightOneSpectrum.adicCompletion K P) =
              WithZero.exp (-1 : ℤ) := by
  intro K _ _ hn P Q hPQ hunder
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have hQm : Q.asIdeal.IsMaximal := Q.isMaximal
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (IsDedekindDomain.HeightOneSpectrum.ext h)
  have hIprime : (Ideal.under ℤ P.asIdeal).IsPrime := Ideal.IsPrime.under ℤ P.asIdeal
  have hNP0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  have hNmem : ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) ∈ Ideal.under ℤ P.asIdeal := by
    have := Ideal.absNorm_mem P.asIdeal
    simpa [Ideal.under_def, Ideal.mem_comap] using this
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.under ℤ P.asIdeal)).principal
  have hg' : Ideal.under ℤ P.asIdeal = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [hg', Ideal.mem_span_singleton] at hNmem
    exact hNP0 (by simpa using hNmem)
  have hgprime : Prime g := by
    rw [hg'] at hIprime
    exact (Ideal.span_singleton_prime hg0).1 hIprime
  set p : ℕ := g.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hgprime
  have hpI : (p : ℤ) ∈ Ideal.under ℤ P.asIdeal := by
    rw [hg', Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.2 dvd_rfl
  have hpP : (p : NumberField.RingOfIntegers K) ∈ P.asIdeal := by
    simpa [Ideal.under_def, Ideal.mem_comap] using hpI
  have hpQ : (p : NumberField.RingOfIntegers K) ∈ Q.asIdeal := by
    rw [hunder] at hpI
    simpa [Ideal.under_def, Ideal.mem_comap] using hpI
  have hnorm : Ideal.absNorm (Ideal.span {(p : NumberField.RingOfIntegers K)}) =
      p ^ Module.finrank ℚ K := by
    have h : (p : NumberField.RingOfIntegers K) =
        algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ) := by simp
    rw [Ideal.absNorm_span_singleton, h, Algebra.norm_algebraMap, Int.natAbs_pow,
      Int.natAbs_natCast, NumberField.RingOfIntegers.rank]
  have hdvd : P.asIdeal * Q.asIdeal ∣ Ideal.span {(p : NumberField.RingOfIntegers K)} := by
    rw [Ideal.dvd_iff_le, Ideal.mul_eq_inf_of_coprime (hPm.coprime_of_ne hQm hne)]
    exact le_inf ((Ideal.span_singleton_le_iff_mem _).2 hpP)
      ((Ideal.span_singleton_le_iff_mem _).2 hpQ)
  obtain ⟨J, hJ⟩ := hdvd
  have hprod : p ^ Module.finrank ℚ K =
      Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal * Ideal.absNorm J := by
    rw [← hnorm, hJ, map_mul, map_mul]
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro _ (by rw [hprod, mul_assoc]) : Ideal.absNorm P.asIdeal ∣ p ^ Module.finrank ℚ K)
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro _ (by rw [hprod, mul_comm (Ideal.absNorm P.asIdeal), mul_assoc]) :
      Ideal.absNorm Q.asIdeal ∣ p ^ Module.finrank ℚ K)
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro_left _ hprod.symm : Ideal.absNorm J ∣ p ^ Module.finrank ℚ K)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at ha
    exact hPm.ne_top ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at hb
    exact hQm.ne_top hb
  have hexp : Module.finrank ℚ K = a + b + c := by
    apply Nat.pow_right_injective hp.two_le
    simp only
    rw [hprod, ha, hb, hc, pow_add, pow_add]
  have ha1 : a = 1 := by omega
  have hc0 : c = 0 := by omega
  have hNP : Ideal.absNorm P.asIdeal = p := by rw [ha, ha1, pow_one]
  have hJtop : J = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, hc, hc0, pow_zero]
  have hspan : Ideal.span {(p : NumberField.RingOfIntegers K)} = P.asIdeal * Q.asIdeal := by
    rw [hJ, hJtop, Ideal.mul_top]
  have hp0 : (p : NumberField.RingOfIntegers K) ≠ 0 := by
    intro h
    rw [h] at hnorm
    rw [Set.singleton_zero, Ideal.span_zero, Ideal.absNorm_bot] at hnorm
    exact pow_ne_zero _ hp.ne_zero hnorm.symm
  have h1 : P.intValuation (p : NumberField.RingOfIntegers K) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_one]
    exact Dvd.intro _ rfl
  have h2 : ¬ P.intValuation (p : NumberField.RingOfIntegers K) ≤
      WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_two]
    intro h
    have h3 : P.asIdeal ∣ Q.asIdeal := (mul_dvd_mul_iff_left P.ne_bot).1 h
    exact hne (hQm.eq_of_le hPm.ne_top (Ideal.dvd_iff_le.1 h3)).symm
  have hval : P.intValuation (p : NumberField.RingOfIntegers K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hp0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    omega
  rw [hNP]
  have key := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) P
    (p : NumberField.RingOfIntegers K)
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval] at key
  simpa using key
end

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

private theorem val_two (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K ≤ 2)
    (P Q : HeightOneSpectrum (𝓞 K)) (hne : P ≠ Q) (h : P.asIdeal.under ℤ = Q.asIdeal.under ℤ) :
    Valued.v ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
  _root_.UpperTheory.Reformulated.B.UnipotentFundamentalDomain.val_two K hK P Q hne h

private theorem finrank_Kx_le {E : Type} [Field E] [NumberField E] (d : ℕ) (x : E)
    (hx : x ^ 2 = -(d : E)) : Module.finrank ℚ (Kx x) ≤ 2 := by
  have hi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have e : Module.finrank ℚ (Kx x) = (minpoly ℚ x).natDegree := IntermediateField.adjoin.finrank hi
  rw [e]
  have hm : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic :=
    Polynomial.monic_X_pow_add_C _ two_ne_zero
  have hz : Polynomial.aeval x (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) = 0 := by
    simp [hx]
  have hd := minpoly.min ℚ x hm hz
  have := Polynomial.natDegree_le_natDegree hd
  rwa [Polynomial.natDegree_X_pow_add_C] at this

private theorem sameK_iff {E : Type} [Field E] [NumberField E] (x : E) (w w' : Plc E) :
    SameK x w w' ↔ w.under (𝓞 (Kx x)) = w'.under (𝓞 (Kx x)) := by
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    exact h (algebraMap (𝓞 (Kx x)) (𝓞 E) a) ((a : Kx x)).2
  · intro h y hy
    have hk : IsIntegral ℤ (⟨y, hy⟩ : Kx x) := by
      have h1 : IsIntegral ℤ (algebraMap (Kx x) E ⟨y, hy⟩) := y.isIntegral_coe
      exact (isIntegral_algebraMap_iff ).1 h1
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 (Kx x), algebraMap (𝓞 (Kx x)) (𝓞 E) a = y :=
      ⟨⟨⟨y, hy⟩, hk⟩, RingOfIntegers.ext rfl⟩
    have hm : ∀ u : Plc E, a ∈ (u.under (𝓞 (Kx x))).asIdeal ↔ y ∈ u.asIdeal := by
      intro u
      rw [← ha]
      rfl
    rw [← hm w, ← hm w', h]

private theorem under_int_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (K : Type) [Field K]
    [NumberField K] [Algebra K E] (w : Plc E) :
    (w.under (𝓞 K)).asIdeal.under ℤ = ((cj w).under (𝓞 K)).asIdeal.under ℤ := by
  have key : (cj w).asIdeal = Ideal.comap (RingOfIntegers.mapRingEquiv (conjE E)) w.asIdeal :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (GlobalTheory.CuspRep.conjPl_conjSrc (conjE E) w)
  have hm : ∀ (u : Plc E) (n : ℤ), n ∈ (u.under (𝓞 K)).asIdeal.under ℤ ↔ (n : 𝓞 E) ∈ u.asIdeal := by
    intro u n
    have e : algebraMap (𝓞 K) (𝓞 E) (algebraMap ℤ (𝓞 K) n) = (n : 𝓞 E) := by simp
    rw [← e]
    rfl
  refine Ideal.ext fun n => ?_
  rw [hm, hm, key, Ideal.mem_comap, map_intCast]

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.kPlace :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.KPlace := by
  intro E _ _ _ d x _ hx
  refine ⟨sameK_iff x, fun w hw => ?_⟩
  rw [sameK_iff] at hw
  exact val_two (Kx x) (finrank_Kx_le d x hx) _ _ (Ne.symm hw) (under_int_cj (Kx x) w)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConj
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Conjugation
@[reducible] noncomputable def UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conjE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → E ≃+* E :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] ↦ (NumberField.IsCMField.complexConj E).toRingEquiv

private theorem UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_eq_neg_of_sq {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ^ 2 = -(r : ℂ)) : starRingEnd ℂ z = -z := by
  have hre : z.re * z.re - z.im * z.im = -r := by
    simpa [pow_two] using congrArg Complex.re hz
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa [pow_two] using congrArg Complex.im hz
  have hprod : z.re * z.im = 0 := by linarith
  have h0 : z.re = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [h0]

theorem UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_alt_bis :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {d : ℕ} {x : E},
      (0 : ℕ) < d → x ^ (2 : ℕ) = -(↑d : E) → (UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conjE E : E → E) x = -x := by
  intro E _ _ _ d x hd hx
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  change φ (NumberField.IsCMField.complexConj E x) = φ (-x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg]
  refine UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_eq_neg_of_sq (r := (d : ℝ)) (Nat.cast_pos.mpr hd) ?_
  rw [← map_pow, hx, map_neg, map_natCast, Complex.ofReal_natCast]
end

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂
open scoped NumberField.AdeleRing

noncomputable section
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem conj_alt_bis {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : conjE E x = -x :=
  _root_.UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_alt_bis hd hx

private theorem conj_conj' (a : E) : conjE E (conjE E a) = a := IsCMField.complexConj_apply_apply E a

private theorem conj_mem {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (a : E)
    (ha : a ∈ IntermediateField.adjoin ℚ {x}) : conjE E a ∈ IntermediateField.adjoin ℚ {x} := by
  induction ha using IntermediateField.adjoin_induction with
  | mem a h =>
    rw [Set.mem_singleton_iff.1 h, conj_alt_bis hd hx]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ x)
  | algebraMap q =>
    have : conjE E (algebraMap ℚ E q) = algebraMap ℚ E q := by simp
    rw [this]
    exact IntermediateField.algebraMap_mem _ q
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

private def cK {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : Kx x ≃ₐ[ℚ] Kx x :=
  let c0 : Kx x →ₐ[ℚ] Kx x :=
    { toFun := fun a => ⟨conjE E a, conj_mem hd hx a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp)
      commutes' := fun q => Subtype.ext (by
        change conjE E ((algebraMap ℚ (Kx x) q : Kx x) : E) = ((algebraMap ℚ (Kx x) q : Kx x) : E)
        simp) }
  AlgEquiv.ofAlgHom c0 c0 (AlgHom.ext fun a => Subtype.ext (conj_conj' _))
    (AlgHom.ext fun a => Subtype.ext (conj_conj' _))

private theorem aut_cases {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (σ : Kx x ≃ₐ[ℚ] Kx x) :
    σ = 1 ∨ σ = cK hd hx := by
  have hmem : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
  let xk : Kx x := ⟨x, hmem⟩
  have hxk : xk ^ 2 = algebraMap ℚ (Kx x) (-(d : ℚ)) := Subtype.ext (by
    change x ^ 2 = algebraMap ℚ E (-(d : ℚ))
    rw [hx]; simp)
  have hsq : (σ xk) ^ 2 = xk ^ 2 := by rw [← map_pow, hxk, AlgEquiv.commutes]
  have ext' : ∀ τ : Kx x ≃ₐ[ℚ] Kx x, σ xk = τ xk → σ = τ := fun τ h => by
    have : (σ : Kx x →ₐ[ℚ] Kx x) = (τ : Kx x →ₐ[ℚ] Kx x) := IntermediateField.adjoin_algHom_ext ℚ (by
      intro a ha
      obtain rfl : a = x := Set.mem_singleton_iff.1 ha
      exact h)
    exact AlgEquiv.coe_toAlgHom_injective this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact Or.inl (ext' 1 h)
  · refine Or.inr (ext' _ (h.trans (Subtype.ext ?_)))
    change -x = conjE E x
    rw [conj_alt_bis hd hx]

private theorem cK_ne {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : cK hd hx ≠ 1 := by
  intro h
  have hmem : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
  have h1 : conjE E x = x := congrArg (fun σ : Kx x ≃ₐ[ℚ] Kx x => ((σ ⟨x, hmem⟩ : Kx x) : E)) h
  rw [conj_alt_bis hd hx] at h1
  have h0 : x = 0 := by
    have : (2 : E) * x = 0 := by linear_combination -h1
    simpa using this
  rw [h0] at hx
  have : (d : E) = 0 := by simpa using hx.symm
  exact hd.ne' (by exact_mod_cast this)

private theorem finrank_K {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) :
    Module.finrank ℚ (Kx x) = 2 := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hmonic : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp) fun q hq => ?_
    have hd' : (0 : ℚ) < d := by exact_mod_cast hd
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hq
    nlinarith [sq_nonneg q]
  have hmin : Polynomial.X ^ 2 + Polynomial.C (d : ℚ) = minpoly ℚ x :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hx]) hmonic
  have := IntermediateField.adjoin.finrank hint
  rw [← hmin, hdeg] at this
  exact this

private theorem univ_eq {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) :
    (Finset.univ : Finset (Kx x ≃ₐ[ℚ] Kx x)) = {1, cK hd hx} := by
  ext σ
  simpa using aut_cases hd hx σ

private theorem isGalois_K {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : IsGalois ℚ (Kx x) := by
  refine IsGalois.of_card_aut_eq_finrank ℚ (Kx x) ?_
  rw [finrank_K hd hx, Nat.card_eq_fintype_card, ← Finset.card_univ, univ_eq hd hx, Finset.card_pair (cK_ne hd hx).symm]

private theorem conjFin_rat (a : Af ℚ) : conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a := by
  have h := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing ℚ).equalizer
    ((continuous_conjFin (conjE E)).comp continuous_finiteAdeleMap)
    (continuous_finiteAdeleMap (K := ℚ) (L := E)) (funext fun q => ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply]
    rw [finiteAdeleMap_algebraMap, conjFin_algebraMap]
    simp

private theorem fin_conj {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (y : 𝔸[Kx x]) :
    finiteAdeleMap (Kx x) E ((cK hd hx • y).2) = conjFin (conjE E) (finiteAdeleMap (Kx x) E y.2) := by
  let Φ : 𝔸[Kx x] →+* Af E := (finiteAdeleMap (Kx x) E).comp
    ((RingHom.snd _ _).comp (adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x)).toRingHom)
  let Ψ : 𝔸[Kx x] →+* Af E := ((conjFin (conjE E)).comp (finiteAdeleMap (Kx x) E)).comp (RingHom.snd _ _)
  have h : Φ = Ψ := by
    refine adeleRingHom_ext_rat (fun l => ?_) (fun a => ?_)
    · change finiteAdeleMap (Kx x) E ((adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x) (algebraMap (Kx x) 𝔸[Kx x] l)).2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E ((algebraMap (Kx x) 𝔸[Kx x] l).2))
      rw [adeleRingEquiv_algebraMap]
      change finiteAdeleMap (Kx x) E (algebraMap (Kx x) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x)) _) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E (algebraMap (Kx x) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x)) l))
      rw [finiteAdeleMap_algebraMap, finiteAdeleMap_algebraMap, conjFin_algebraMap]
      rfl
    · change finiteAdeleMap (Kx x) E ((adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x) (adeleMap ℚ (Kx x) a)).2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E ((adeleMap ℚ (Kx x) a).2))
      rw [adeleRingEquiv_adeleMap_rat]
      change finiteAdeleMap (Kx x) E (finiteAdeleMap ℚ (Kx x) a.2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E (finiteAdeleMap ℚ (Kx x) a.2))
      rw [finiteAdeleMap_finiteAdeleMap, conjFin_rat]
  exact congrArg (· y) h

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.quadConj :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.QuadConj := by
  intro E _ _ _ d x hd hx z
  haveI := isGalois_K hd hx
  let y : IdeleGroup (Kx x) := Units.map (MonoidHom.inr (InfiniteAdeleRing (Kx x)) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x))) z
  have h1 := ideleEmbedding_ideleNorm (K := ℚ) y
  have h2 : (∏ σ : Kx x ≃ₐ[ℚ] Kx x, σ • y) = y * cK hd hx • y := by
    rw [univ_eq hd hx, Finset.prod_pair (cK_ne hd hx).symm, one_smul]
  rw [h2] at h1
  have h3 := congrArg (fun u : IdeleGroup (Kx x) => ((u : 𝔸[Kx x]).2)) h1
  have h4 : finiteAdeleMap ℚ (Kx x) ((fN ℚ (Kx x) z : (Af ℚ)ˣ) : Af ℚ) =
      (z : Af (Kx x)) * ((cK hd hx • (y : 𝔸[Kx x])).2) := h3
  have h5 := congrArg (finiteAdeleMap (Kx x) E) h4
  rw [finiteAdeleMap_finiteAdeleMap, map_mul, fin_conj] at h5
  exact h5.symm

end
end
