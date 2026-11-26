module

public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsInfiniteQcmSplitRam

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotSqMulUnit
open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise

namespace GlobalTheory.UnramSquare

theorem not_sq_mul_unit (K : Type) [Field K] [NumberField K] (Q : Ideal (𝓞 K)) [Q.IsMaximal] :
    Algebra.IsUnramifiedAt ℤ Q → ∀ p : ℕ, p.Prime → (p : 𝓞 K) ∈ Q → ∀ y u : 𝓞 K, u ∉ Q →
      y ^ 2 = (p : 𝓞 K) * u → False := by
  intro h p hp hpQ y u hu hyu
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hPr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hPr.isMaximal (by simpa using hpZ.ne_zero)
  haveI hQp : Q.IsPrime := inferInstance
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ Q).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hpQ
  letI := Localization.AtPrime.algebraOfLiesOver (Ideal.span {(p : ℤ)}) Q
  have h2 := ((Algebra.isUnramifiedAt_iff_map_eq ℤ (Ideal.span {(p : ℤ)}) Q).1 h).2
  have hyQ : y ∈ Q := hQp.mem_of_pow_mem 2 (by rw [hyu]; exact Q.mul_mem_right _ hpQ)
  have h3 : algebraMap (𝓞 K) (Localization.AtPrime Q) y ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q y).2 hyQ
  rw [← h2, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at h3
  obtain ⟨w, hw⟩ := h3
  obtain ⟨⟨z, t⟩, hzt⟩ := IsLocalization.surj Q.primeCompl w
  have htz : (t : 𝓞 K) * y = p * z := by
    apply IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors
    simp only at hzt
    rw [map_mul, map_mul, ← hw, ← hzt]
    simp only [map_natCast, eq_intCast, Int.cast_natCast]
    ring
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4 : (t : 𝓞 K) ^ 2 * u = p * z ^ 2 := by
    apply mul_left_cancel₀ hp0
    calc (p : 𝓞 K) * ((t : 𝓞 K) ^ 2 * u) = (t : 𝓞 K) ^ 2 * y ^ 2 := by rw [hyu]; ring
      _ = ((t : 𝓞 K) * y) ^ 2 := by ring
      _ = p * (p * z ^ 2) := by rw [htz]; ring
  have h5 : (t : 𝓞 K) ^ 2 * u ∈ Q := by rw [h4]; exact Q.mul_mem_right _ hpQ
  rcases hQp.mem_or_mem h5 with h6 | h6
  · exact t.2 (hQp.mem_of_pow_mem 2 h6)
  · exact hu h6

end GlobalTheory.UnramSquare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmQuadraticAdjoinSqrtNegNat
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmQuadraticAdjoinSqrtNegNat
open NumberField

open scoped IntermediateField

namespace GlobalTheory.CMSqrtNeg

theorem finrank_adjoin_sq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (c : E) (t : Ω)
    (ht : t ^ 2 = algebraMap E Ω c) (hn : t ∉ Set.range (algebraMap E Ω)) :
    IsIntegral E t ∧ Module.finrank E E⟮t⟯ = 2 := by
  have hm : (Polynomial.X ^ 2 - Polynomial.C c).Monic := Polynomial.monic_X_pow_sub_C c two_ne_zero
  have h0 : Polynomial.aeval t (Polynomial.X ^ 2 - Polynomial.C c) = 0 := by simp [ht]
  have hi : IsIntegral E t := ⟨_, hm, by simpa [Polynomial.aeval_def] using h0⟩
  refine ⟨hi, ?_⟩
  rw [IntermediateField.adjoin.finrank hi]
  have h1 : (minpoly E t).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd E t h0) hm.ne_zero
    rwa [Polynomial.natDegree_X_pow_sub_C _] at this
  have h2 : 2 ≤ (minpoly E t).natDegree := (minpoly.two_le_natDegree_iff hi).2 (by simpa using hn)
  omega

theorem exists_qcm_adjoin_sqrt_neg : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (p : ℕ), 0 < p → ∀ δ : Ω, δ ^ 2 = -(p : Ω) → δ ∉ Set.range (algebraMap E Ω) →
    ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} := by
  intro E Ω _ _ _ _ _ _ p hp δ hδ hδn
  have hδ' : δ ^ 2 = algebraMap E Ω (-(p : E)) := by simp [hδ]
  obtain ⟨hint, htwo⟩ := finrank_adjoin_sq (-(p : E)) δ hδ' hδn
  haveI : FiniteDimensional E E⟮δ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI nf : NumberField E⟮δ⟯ := NumberField.of_module_finite E _
  obtain ⟨d, s, hs, hsn, hneg⟩ := GlobalTheory.CMGen.exists_sqrt_totallyNegative E
  have hs0 : s ≠ 0 := fun h => hsn (h ▸ zero_mem _)
  let t : E⟮δ⟯ := ⟨δ * algebraMap E Ω s,
    mul_mem (IntermediateField.subset_adjoin E {δ} rfl) (IntermediateField.algebraMap_mem _ s)⟩
  let d' : maximalRealSubfield E := -(p : maximalRealSubfield E) * (d : maximalRealSubfield E)
  have ht : t ^ 2 = algebraMap E E⟮δ⟯ (algebraMap (maximalRealSubfield E) E d') := by
    apply Subtype.ext
    show (δ * algebraMap E Ω s) ^ 2 = algebraMap E Ω (algebraMap (maximalRealSubfield E) E d')
    rw [mul_pow, hδ, ← map_pow, hs]
    simp [d']
  have htn : t ∉ Set.range (algebraMap E E⟮δ⟯) := by
    rintro ⟨e, he⟩
    apply hδn
    refine ⟨e * s⁻¹, ?_⟩
    have h1 : algebraMap E Ω e = δ * algebraMap E Ω s := congrArg Subtype.val he
    have h2 : algebraMap E Ω s ≠ 0 := (map_ne_zero _).2 hs0
    rw [map_mul, h1, map_inv₀, mul_assoc, mul_inv_cancel₀ h2, mul_one]
  have hpos : ∀ φ : maximalRealSubfield E →+* ℝ, 0 < φ d' := fun φ => by
    have := hneg φ
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    simp only [d', map_mul, map_neg, map_natCast]
    nlinarith
  have hcm := (GlobalTheory.isCMField_of_sq_eq_totallyPositive E E⟮δ⟯ htwo d' t ht htn hpos).1
  exact ⟨⟨E⟮δ⟯, nf, hcm, htwo⟩, rfl⟩

end GlobalTheory.CMSqrtNeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmQuadraticAdjoinSqrtNegNatStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmQuadratic_adjoin_sqrt_neg_nat : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (p : ℕ), 0 < p → ∀ δ : Ω, δ ^ 2 = -(p : Ω) → δ ∉ Set.range (algebraMap E Ω) → ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} := by
  first | exact @GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg | exact GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg | (intros; apply GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankMaximalRealEven
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankMaximalRealEven
open NumberField

namespace GlobalTheory.RealGal

theorem QCM.even_finrank_maximalRealSubfield (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    (Q : GlobalTheory.RealGal.QCM E Ω) : Even (Module.finrank ℚ (maximalRealSubfield Q.K)) := by
  have h1 := (letI : Module.Free (maximalRealSubfield Q.K) Q.K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield Q.K) Q.K)
  have h2 := Module.finrank_mul_finrank ℚ E Q.K
  have h3 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield Q.K) Q.K] at h1
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h3
  rw [Q.two] at h2
  exact ⟨Module.finrank ℚ (maximalRealSubfield E), by omega⟩

end GlobalTheory.RealGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankMaximalRealEvenStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_maximal_real_even : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] (Q : GlobalTheory.RealGal.QCM E Ω), Even (Module.finrank ℚ (maximalRealSubfield Q.K)) := by
  first | exact @GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield | exact GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield | (intros; apply GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceBelowCMFieldOfSqrtNegPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceBelowCMFieldOfSqrtNegPrime
open NumberField IsDedekindDomain

namespace GlobalTheory.SplitOfNegPrime

theorem sqrt_neg_not_mem_maximalRealSubfield (L : Type) [Field L] [NumberField L] [IsCMField L]
    (p : ℕ) (δ : L) (hp : 0 < p) (hδ : δ ^ 2 = -(p : L)) : δ ∉ maximalRealSubfield L := by
  intro hmem
  let x : maximalRealSubfield L := ⟨δ, hmem⟩
  have hx : x ^ 2 = -(p : maximalRealSubfield L) := Subtype.ext (by simpa [x] using hδ)
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield L)) := inferInstance
  have hv : v.IsReal := IsTotallyReal.isReal v
  have h := congrArg (InfinitePlace.embedding_of_isReal hv) hx
  rw [map_pow, map_neg, map_natCast] at h
  have h1 : (0 : ℝ) < p := by exact_mod_cast hp
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]

theorem isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L), 0 < p → δ ^ 2 = -(p : L) → ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 → ∀ w : HeightOneSpectrum (𝓞 L), (q : 𝓞 L) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
  intro L _ _ _ p q δ hp hδ hdvd w hw
  set Lp := maximalRealSubfield L
  set u := w.under (𝓞 Lp)
  obtain ⟨k, hk⟩ := hdvd
  set z : 𝓞 Lp := -(2 * (q : 𝓞 Lp) * (k : 𝓞 Lp)) with hz
  have hq : (q : 𝓞 Lp) ∈ u.asIdeal := by
    change _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  have hzu : z ∈ u.asIdeal := by
    rw [hz]
    exact u.asIdeal.neg_mem_iff.2 (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq))
  have hk' : ((p : ℤ) : 𝓞 Lp) + 1 = (((8 * q : ℕ) : ℤ) : 𝓞 Lp) * (k : 𝓞 Lp) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 Lp) hk
  have hsq : (1 + 4 * z : 𝓞 Lp) = -(p : 𝓞 Lp) := by
    rw [hz]
    push_cast at hk'
    linear_combination hk'
  have h1 := GlobalTheory.HenselSquare.isSquare_one_add_four_mul Lp u z hzu
  rw [hsq] at h1
  refine GlobalTheory.SplitOfSquare.isSplitAt_of_isSquare L (-(p : Lp)) δ (by rw [hδ]; push_cast; rfl)
    (sqrt_neg_not_mem_maximalRealSubfield L p δ hp hδ) w ?_
  simpa using h1

end GlobalTheory.SplitOfNegPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceBelowCMFieldOfSqrtNegPrimeStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplitPlaceBelowCMField_of_sqrt_neg_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L), 0 < p → δ ^ 2 = -(p : L) → ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 → ∀ w : HeightOneSpectrum (𝓞 L), (q : 𝓞 L) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
  first | exact @GlobalTheory.SplitOfNegPrime.isSplitAt | exact GlobalTheory.SplitOfNegPrime.isSplitAt | (intros; apply GlobalTheory.SplitOfNegPrime.isSplitAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsUnramifiedAtOfSqEqNegPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsUnramifiedAtOfSqEqNegPrime
open NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegRam

theorem not_isUnramifiedAt_of_sq_eq_neg :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime →
      ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K),
        (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  intro E K _ _ _ _ _ p hp hd δ hδ w hpw hunr
  have hmax := w.isMaximal
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hv : Algebra.IsUnramifiedAt ℤ (w.asIdeal.under (𝓞 E)) := by
    refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd _ inferInstance ?_
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hpw
  have h1 : w.asIdeal.ramificationIdx (𝓞 E) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hunr
  have h2 : (w.asIdeal.under (𝓞 E)).ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hv
  have h3 : w.asIdeal.ramificationIdx ℤ = 1 := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) (w.asIdeal.under (𝓞 E)) w.asIdeal, h1, h2]
  have hZ : Algebra.IsUnramifiedAt ℤ w.asIdeal := Ideal.ramificationIdx_eq_one_iff.1 h3
  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    have : (-(p : K)) = algebraMap ℤ K (-(p : ℤ)) := by simp
    rw [this]
    exact isIntegral_algebraMap
  set y : 𝓞 K := ⟨δ, hint⟩ with hy
  have hy2 : y ^ 2 = (p : 𝓞 K) * (-1) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 K) K (y ^ 2) = algebraMap (𝓞 K) K ((p : 𝓞 K) * (-1))
    rw [map_pow, map_mul, map_neg, map_one, map_natCast]
    change δ ^ 2 = _
    rw [hδ]; ring
  have hu : (-1 : 𝓞 K) ∉ w.asIdeal := by
    intro h
    exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w.asIdeal.neg_mem h))
  exact GlobalTheory.UnramSquare.not_sq_mul_unit K w.asIdeal hZ p hp hpw y (-1) hu hy2

end GlobalTheory.SqrtNegRam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsUnramifiedAtOfSqEqNegPrimeStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isUnramifiedAt_of_sq_eq_neg_prime : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  first | exact @GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg | exact GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg | (intros; apply GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CMFam

open IntermediateField

theorem exists_qcm_adjoin (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (p : ℕ) (hp : 0 < p) (δ : Ω) (hδ : δ ^ 2 = -(p : Ω))
    (hn : δ ∉ Set.range (algebraMap E Ω)) :
    ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} :=
  GlobalTheory.T.exists_cmQuadratic_adjoin_sqrt_neg_nat E Ω p hp δ hδ hn

theorem isSplitAt_of_dvd (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L) (hp : 0 < p)
    (hδ : δ ^ 2 = -(p : L)) (hq : ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1) (w : HeightOneSpectrum (𝓞 L))
    (hw : (q : 𝓞 L) ∈ w.asIdeal) : GlobalTheory.UnitaryBC.IsSplitAt w :=
  GlobalTheory.T.isSplitPlaceBelowCMField_of_sqrt_neg_prime L p q δ hp hδ hq w hw

theorem not_isUnramifiedAt (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (p : ℕ) (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (δ : K) (hδ : δ ^ 2 = -(p : K))
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal :=
  GlobalTheory.T.not_isUnramifiedAt_of_sq_eq_neg_prime E K p hp hd δ hδ w hw

theorem exists_unram (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K]
      (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal :=
  GlobalTheory.T.exists_nat_unramified_over_maximalRealSubfield E

theorem even_finrank (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    (Q : GlobalTheory.RealGal.QCM E Ω) : Even (Module.finrank ℚ (maximalRealSubfield Q.K)) :=
  GlobalTheory.T.finrank_maximal_real_even E Ω Q

end GlobalTheory.CMFam

namespace GlobalTheory.CMFam

theorem dvd_of_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q n : ℕ} (hq : q.Prime)
    (hqw : (q : 𝓞 K) ∈ w.asIdeal) (hn : (n : 𝓞 K) ∈ w.asIdeal) : q ∣ n := by
  by_contra h
  have hc : Nat.gcd q n = 1 := (Nat.Prime.coprime_iff_not_dvd hq).2 h
  have hm : (((Nat.gcd q n : ℕ) : ℤ) : 𝓞 K) ∈ w.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab q n]
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_right _ hqw) (w.asIdeal.mul_mem_right _ hn)
  rw [hc] at hm
  simp only [Nat.cast_one, Int.cast_one] at hm
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem natCast_mem_under {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : (n : 𝓞 E) ∈ (w.under (𝓞 E)).asIdeal ↔ (n : 𝓞 K) ∈ w.asIdeal := by
  change _ ∈ Ideal.comap _ _ ↔ _
  rw [Ideal.mem_comap, map_natCast]

end GlobalTheory.CMFam


open GlobalTheory.CMFam GlobalTheory.ExSplitCM in
theorem GlobalTheory.GalCut.infinite_qcm_split_good : AutomorphicFormsFiniteGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)), {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P}.Infinite := by
  intro hAF E Ω _ _ _ _ _ _ l _ a π w₀
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have halg : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q₀, hq₀, hq₀w⟩ := exists_prime_mem w₀
  haveI : Fact q₀.Prime := ⟨hq₀⟩
  obtain ⟨N, hN0, hN⟩ := exists_unram E
  set S : Set (HeightOneSpectrum (𝓞 E)) := {v | ¬ ∃ B, (CG.mk π).HasSat v B} with hSdef
  have hS : S.Finite := Filter.eventually_cofinite.1 (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hAF E a π)
  set T : Finset ℕ := ({2, l, q₀} : Finset ℕ) ∪ N.primeFactors ∪ (discr E).natAbs.primeFactors ∪
    (finite_primes_of_finite hS).toFinset with hTdef
  set M : ℕ := 8 * ∏ q ∈ T, q with hM
  have hT2 : 2 ∈ T := by simp [hTdef]
  have hTl : l ∈ T := by simp [hTdef]
  have hTq₀ : q₀ ∈ T := by simp [hTdef]
  have hTN : ∀ r : ℕ, r.Prime → r ∣ N → r ∈ T := fun r hr hd => by
    simp [hTdef, Nat.mem_primeFactors, hr, hd, hN0]
  have hTd : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ T := fun r hr hd => by
    have : r ∈ (discr E).natAbs.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hr, Int.natCast_dvd.1 hd, Int.natAbs_ne_zero.2 (discr_ne_zero E)⟩
    simp [hTdef, this]
  have hTS : ∀ r : ℕ, r.Prime → ∀ v ∈ S, (r : 𝓞 E) ∈ v.asIdeal → r ∈ T := fun r hr v hv h => by
    have : r ∈ (finite_primes_of_finite hS).toFinset := by simpa using ⟨hr, v, hv, h⟩
    simp [hTdef, this]
  have hM0 : M ≠ 0 := by
    rw [hM]
    refine mul_ne_zero (by norm_num) ?_
    rw [Finset.prod_ne_zero_iff]
    intro q hq h0
    subst h0
    simp [hTdef] at hq
    rcases hq with h | h | h
    · exact (Fact.out : l.Prime).ne_zero h.symm
    · exact hq₀.ne_zero h.symm
    · exact Nat.not_prime_zero h.1
  haveI : NeZero M := ⟨hM0⟩
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p =>
    IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) two_pos
  choose δ hδ using hsq
  set Gd : Set ℕ := {p | p.Prime ∧ p ∉ T ∧ (M : ℤ) ∣ (p : ℤ) + 1} with hGd
  have hGood : Gd.Infinite := by
    refine ((Nat.infinite_setOfPred_prime_and_eq_mod (q := M) isUnit_one.neg).diff T.finite_toSet).mono ?_
    rintro p ⟨⟨hp, hpe⟩, hpT⟩
    refine ⟨hp, hpT, ?_⟩
    have : (((p : ℤ) + 1 : ℤ) : ZMod M) = 0 := by push_cast; rw [hpe]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have h8 : ∀ p ∈ Gd, ∀ q ∈ T, ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 := fun p hp q hq => by
    refine dvd_trans ?_ hp.2.2
    rw [Int.natCast_dvd_natCast, hM]
    exact Nat.mul_dvd_mul_left 8 (Finset.dvd_prod_of_mem _ hq)
  have hodd : ∀ p ∈ Gd, p ≠ 2 := fun p hp h => hp.2.1 (h ▸ hT2)
  have hdisc : ∀ p ∈ Gd, ¬ (p : ℤ) ∣ discr E := fun p hp h => hp.2.1 (hTd p hp.1 h)
  have hmove : ∀ p ∈ Gd, ∀ (u : HeightOneSpectrum (𝓞 E)) (A' : ValuationSubring Ω), ((p : ℕ) : 𝓞 E) ∈ u.asIdeal →
      IsPlaceOver A' u → ∃ s ∈ Ine (F := E) A', s (δ p) ≠ δ p := fun p hp u A' hu hA' =>
    GlobalTheory.SqrtNegRam.sqrt_neg_moved_by_inertia E Ω p hp.1 (hodd p hp) (hdisc p hp) (δ p) (hδ p) u A' hu hA'
  have hnot : ∀ p ∈ Gd, δ p ∉ Set.range (algebraMap E Ω) := by
    rintro p hp ⟨x, hx⟩
    obtain ⟨u, hu⟩ := exists_mem_of_prime (F := E) hp.1
    obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
    obtain ⟨s, -, hs⟩ := hmove p hp u A' hu hA'
    exact hs (by rw [← hx]; exact s.commutes x)
  have hQ : ∀ p ∈ Gd, ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ p} := fun p hp =>
    exists_qcm_adjoin E Ω p hp.1.pos (δ p) (hδ p) (hnot p hp)
  have hmem : ∀ p ∈ Gd, ∀ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ p} →
      Q ∈ {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P} := by
    intro p hp Q hQK
    have hδK : δ p ∈ Q.K := by rw [hQK]; exact IntermediateField.mem_adjoin_simple_self E (δ p)
    set y : ↥Q.K := ⟨δ p, hδK⟩ with hy
    have hy2 : y ^ 2 = -(p : ↥Q.K) := Subtype.ext (by simpa using hδ p)
    have hsplit : ∀ q ∈ T, ∀ w : HeightOneSpectrum (𝓞 ↥Q.K), (q : 𝓞 ↥Q.K) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w :=
      fun q hq w hw => isSplitAt_of_dvd _ p q y hp.1.pos hy2 (h8 p hp q hq) w hw
    refine ⟨fun A hA s hs => ?_, fun w hw => ?_, ?_, fun P hP => ?_⟩
    · rw [mem_range_res_iff, hQK]
      refine fix_adjoin (halg.isAlgebraic (δ p)).isIntegral s ?_
      exact GlobalTheory.SqFix.sqrt_fixed_of_isSquare_padic E Ω w₀ A hA q₀ hq₀w (-(p : ℤ)) (δ p)
        (by push_cast; exact hδ p)
        (by push_cast; exact GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q₀ p (h8 p hp q₀ hTq₀)) s hs
    · refine hsplit q₀ hTq₀ w ?_
      rw [← natCast_mem_under (E := E), hw]
      exact hq₀w
    · obtain ⟨w, hw⟩ := exists_mem_of_prime (F := ↥Q.K) hp.1
      refine ⟨w, not_isUnramifiedAt E ↥Q.K p hp.1 (hdisc p hp) y hy2 w hw, ?_⟩
      by_contra hB
      exact hp.2.1 (hTS p hp.1 _ hB ((natCast_mem_under w p).2 hw))
    · refine ⟨⟨y, p, hp.1.pos, by rw [hy2]⟩, even_finrank E Ω Q, fun w hw => ?_⟩
      obtain ⟨q, hq, hqw⟩ := exists_prime_mem w
      have hqT : q ∉ T := fun h => hw (hsplit q h w hqw)
      refine ⟨fun hl => hqT (prime_eq_of_mem w (Fact.out : l.Prime) hq hl hqw ▸ hTl), ?_, ?_⟩
      · refine hN ↥Q.K w fun h => hqT (hTN q hq (dvd_of_mem w hq hqw h))
      · have hB : ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B := by
          by_contra hB
          exact hqT (hTS q hq _ hB ((natCast_mem_under w q).2 hqw))
        obtain ⟨B, hB⟩ := hB
        exact ⟨_, hP.sat w _ B (GlobalTheory.RealGal.AttRes.normV_eq_pow w) hB⟩
  intro hfin
  apply hGood
  refine (hfin.biUnion (t := fun Q : GlobalTheory.RealGal.QCM E Ω => {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 E) |
      ¬ ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Ine (F := E) A' ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range},
      ((p : ℕ) : 𝓞 E) ∈ u.asIdeal})
    fun Q _ => finite_primes_of_finite (Filter.eventually_cofinite.1 (UpperTheory.cm_inertia_restriction_holds E ↥Q.K Ω))).subset ?_
  intro p hp
  obtain ⟨Q, hQK⟩ := hQ p hp
  refine Set.mem_biUnion (hmem p hp Q hQK) ⟨hp.1, ?_⟩
  obtain ⟨u, hu⟩ := exists_mem_of_prime (F := E) hp.1
  obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  refine ⟨u, fun hall => ?_, hu⟩
  obtain ⟨s, hs, hne⟩ := hmove p hp u A' hu hA'
  refine hne ((mem_range_res_iff Q.K s).1 (hall A' hA' hs) (δ p) ?_)
  rw [hQK]
  exact IntermediateField.mem_adjoin_simple_self E (δ p)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplitStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_quadraticCM_goodBaseChange_split : AutomorphicFormsFiniteGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)), {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P}.Infinite := by
  first | exact @GlobalTheory.GalCut.infinite_qcm_split_good | exact GlobalTheory.GalCut.infinite_qcm_split_good | (intros; apply GlobalTheory.GalCut.infinite_qcm_split_good <;> assumption)
end
