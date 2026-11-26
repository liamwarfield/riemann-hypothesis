module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsUnitValueSkewHermitian
public import Development.WeilBound.CoreStatements.SesquilinearFractions.NIdeal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIntegralIffDenominator
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIntegralIffDenominator
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
private theorem norm_intCast_padicAlgCl_lt_one_iff_dvd (p : ℕ) [Fact p.Prime] (k : ℤ) :
    ‖(k : PadicAlgCl p)‖ < 1 ↔ (p : ℤ) ∣ k := by
  rw [← map_intCast (algebraMap ℚ_[p] (PadicAlgCl p)) k, PadicAlgCl.norm_extends]
  exact Padic.norm_intCast_lt_one_iff

private theorem norm_intCast_cp_lt_one_iff_dvd (p : ℕ) [Fact p.Prime] (k : ℤ) :
    ‖(k : ℂ_[p])‖ < 1 ↔ (p : ℤ) ∣ k := by
  rw [← map_intCast (algebraMap (PadicAlgCl p) ℂ_[p]) k, ← PadicComplex.coe_eq,
    PadicComplex.norm_extends]
  exact norm_intCast_padicAlgCl_lt_one_iff_dvd p k

private theorem not_dvd_den_of_norm_le_one_padicAlgCl (p : ℕ) [Fact p.Prime] (q : ℚ) (hq : ‖(q : PadicAlgCl p)‖ ≤ 1) :
    ¬ p ∣ q.den := by
  intro hd
  have hp : p.Prime := Fact.out
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have h2 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 hd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hnum1 : ‖(q.num : PadicAlgCl p)‖ = 1 :=
    le_antisymm (IsUltrametricDist.norm_intCast_le_one _ _)
      (not_lt.mp fun h => hnum ((norm_intCast_padicAlgCl_lt_one_iff_dvd p _).mp h))
  have hden : ‖(q.den : PadicAlgCl p)‖ < 1 := by
    rw [← Int.cast_natCast, norm_intCast_padicAlgCl_lt_one_iff_dvd]
    exact Int.natCast_dvd_natCast.mpr hd
  have hden0 : 0 < ‖(q.den : PadicAlgCl p)‖ := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
    exact norm_pos_iff.mpr (Nat.cast_ne_zero.mpr q.den_nz)
  rw [Rat.cast_def, norm_div, hnum1, div_le_iff₀ hden0, one_mul] at hq
  linarith

private theorem norm_multiset_prod_le_one_of_forall_norm_le_one {K : Type*} [NormedField K] (s : Multiset K) :
    (∀ y ∈ s, ‖y‖ ≤ 1) → ‖s.prod‖ ≤ 1 := by
  refine Multiset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ih h
    rw [Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (h a (by simp)) (norm_nonneg _) (ih fun y hy => h y (by simp [hy]))

private theorem norm_multiset_sum_le_one_of_ultrametric {K : Type*} [NormedField K] [IsUltrametricDist K] (s : Multiset K) :
    (∀ y ∈ s, ‖y‖ ≤ 1) → ‖s.sum‖ ≤ 1 := by
  refine Multiset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ih h
    rw [Multiset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (by simp)) (ih fun y hy => h y (by simp [hy])))

private theorem norm_esymm_le_one_of_forall_norm_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] (s : Multiset K)
    (h : ∀ y ∈ s, ‖y‖ ≤ 1) (k : ℕ) : ‖s.esymm k‖ ≤ 1 := by
  rw [Multiset.esymm]
  apply norm_multiset_sum_le_one_of_ultrametric
  intro y hy
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hy
  apply norm_multiset_prod_le_one_of_forall_norm_le_one
  intro z hz
  exact h z (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hz)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (x : E), ((∀ j : E →+* ℂ_[p], ‖j x‖ ≤ 1) ↔ ∃ (n : ℕ) (a : 𝓞 E), ¬ (p : ℕ) ∣ n ∧ (n : E) * x = a) := by
  intro E _ _ p x
  constructor
  · intro h
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hmon : (minpoly ℚ x).Monic := minpoly.monic hint
    have hroot : ∀ r ∈ ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).roots,
        ‖r‖ ≤ 1 := by
      intro r hr
      have hr' : r ∈ (minpoly ℚ x).rootSet (PadicAlgCl (p : ℕ)) := by
        refine Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero hint, ?_⟩
        rw [Polynomial.aeval_def, ← Polynomial.eval_map]
        exact (Polynomial.mem_roots'.mp hr).2
      rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly (PadicAlgCl (p : ℕ)) x] at hr'
      obtain ⟨ψ, rfl⟩ := hr'
      have h1 := h ((algebraMap (PadicAlgCl (p : ℕ)) ℂ_[p]).comp (ψ : E →+* PadicAlgCl (p : ℕ)))
      rw [RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends] at h1
      exact h1
    have hcard : ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).roots.card =
        ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).natDegree :=
      IsAlgClosed.card_roots_eq_natDegree
    have hmon' : ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).Monic := hmon.map _
    have hcoeff : ∀ k, ‖(((minpoly ℚ x).coeff k : ℚ) : PadicAlgCl (p : ℕ))‖ ≤ 1 := by
      intro k
      have e1 : (((minpoly ℚ x).coeff k : ℚ) : PadicAlgCl (p : ℕ)) =
          ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).coeff k := by
        rw [Polynomial.coeff_map]
        exact (eq_ratCast _ _).symm
      rw [e1]
      by_cases hk : k ≤ ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).natDegree
      · rw [Polynomial.coeff_eq_esymm_roots_of_card hcard hk, hmon'.leadingCoeff, one_mul,
          norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact norm_esymm_le_one_of_forall_norm_le_one _ hroot _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hk), norm_zero]
        exact zero_le_one
    obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ∏ k ∈ Finset.range ((minpoly ℚ x).natDegree + 1),
        ((minpoly ℚ x).coeff k).den := ⟨_, rfl⟩
    have hm : ¬ (p : ℕ) ∣ m := by
      rw [hmdef, Prime.dvd_finsetProd_iff p.2.prime]
      rintro ⟨k, -, hk⟩
      exact not_dvd_den_of_norm_le_one_padicAlgCl _ _ (hcoeff k) hk
    have hlift : Polynomial.C (m : ℚ) * minpoly ℚ x ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro k
      rw [Polynomial.coeff_C_mul]
      by_cases hk : k ≤ (minpoly ℚ x).natDegree
      · have hd : ((minpoly ℚ x).coeff k).den ∣ m := by
          rw [hmdef]
          exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
        obtain ⟨t, ht⟩ := hd
        refine ⟨(t : ℤ) * ((minpoly ℚ x).coeff k).num, ?_⟩
        simp only [eq_intCast]
        rw [ht]
        push_cast
        rw [← Rat.den_mul_eq_num]
        ring
      · exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hk), mul_zero,
          map_zero]⟩
    obtain ⟨g, hg⟩ := (Polynomial.mem_lifts _).mp hlift
    have hlc : g.leadingCoeff = (m : ℤ) := by
      have h1 := Polynomial.leadingCoeff_map_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)) g
      rw [hg, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hmon.leadingCoeff, mul_one,
        eq_intCast] at h1
      exact_mod_cast h1.symm
    have hg0 : Polynomial.aeval x g = 0 := by
      rw [← Polynomial.aeval_map_algebraMap ℚ x g, hg, map_mul, Polynomial.aeval_C, minpoly.aeval,
        mul_zero]
    have hI := isIntegral_leadingCoeff_smul g x hg0
    rw [hlc] at hI
    have hI' : IsIntegral ℤ ((m : E) * x) := by
      simpa [zsmul_eq_mul, nsmul_eq_mul] using hI
    exact ⟨m, ⟨(m : E) * x, hI'⟩, hm, rfl⟩
  · rintro ⟨n, a, hpn, hna⟩ j
    have hn : ‖((n : ℕ) : ℂ_[p])‖ = 1 := by
      have h1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n
      have h2 : ¬ ‖((n : ℕ) : ℂ_[p])‖ < 1 := by
        rw [← Int.cast_natCast, norm_intCast_cp_lt_one_iff_dvd]
        exact fun h => hpn (Int.natCast_dvd_natCast.mp h)
      linarith [not_lt.mp h2]
    have ha : ‖j (a : E)‖ ≤ 1 := by
      have h1 := GlobalTheory.CompanionTheory.Ar.HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) j a
      rw [NormedField.valuation_apply] at h1
      exact_mod_cast h1
    have hj : j ((n : E) * x) = (n : ℂ_[p]) * j x := by
      rw [map_mul, map_natCast]
    rw [hna] at hj
    calc ‖j x‖ = ‖(n : ℂ_[p])‖ * ‖j x‖ := by rw [hn, one_mul]
      _ = ‖(n : ℂ_[p]) * j x‖ := (norm_mul _ _).symm
      _ = ‖j (a : E)‖ := by rw [hj]
      _ ≤ 1 := ha
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIntegralIffDenominatorStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_integral_iff_denominator : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (x : E), ((∀ j : E →+* ℂ_[p], ‖j x‖ ≤ 1) ↔ ∃ (n : ℕ) (a : 𝓞 E), ¬ (p : ℕ) ∣ n ∧ (n : E) * x = a) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator | exact GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator | (intros; apply GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealPadicGeneratorLogNorm
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealPadicGeneratorLogNorm
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem ideal_local_generator : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (p : Nat.Primes), I ≠ ⊥ → ∃ δ ∈ I, δ ≠ 0 ∧ (∃ n : ℕ, ¬ (p : ℕ) ∣ n ∧ ∀ a ∈ I, (n : 𝓞 F) * a ∈ Ideal.span {δ}) ∧ ∀ j : F →+* ℂ_[p], Real.log ‖j (δ : F)‖ = logIdeal (j.comp (algebraMap (𝓞 F) F)) I :=
  @PositivityTheory.Xgf.ideal_padic_generator_log_norm

end GlobalTheory.CompanionTheory.Ar.Fl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealPadicGeneratorLogNormStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_padic_generator_log_norm : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (p : Nat.Primes), I ≠ ⊥ → ∃ δ ∈ I, δ ≠ 0 ∧ (∃ n : ℕ, ¬ (p : ℕ) ∣ n ∧ ∀ a ∈ I, (n : 𝓞 F) * a ∈ Ideal.span {δ}) ∧ ∀ j : F →+* ℂ_[p], Real.log ‖j (δ : F)‖ = logIdeal (j.comp (algebraMap (𝓞 F) F)) I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.ideal_local_generator | exact GlobalTheory.CompanionTheory.Ar.Fl.ideal_local_generator | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.ideal_local_generator <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsRealDifferentGenerator
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.DifferentIdealEqTopOfUnramified
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

theorem differentIdeal_eq_top_of_unramified (E : Type) [Field E] [NumberField E] [IsCMField E]
    [h : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] :
    differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hdvd : P ∣ differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) := Ideal.dvd_iff_le.mpr hle
  haveI : P.IsPrime := hP.isPrime
  have hU : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P := by
    unfold Algebra.IsUnramifiedAt
    haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := inferInstance
    exact Algebra.FormallyUnramified.comp (𝓞 (maximalRealSubfield E)) (𝓞 E) (Localization.AtPrime P)
  exact (not_dvd_differentIdeal_iff.mpr hU) hdvd

theorem exists_real_different_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : Nat.Primes, ∃ δ ∈ differentIdeal ℤ (𝓞 E), δ ≠ 0 ∧ IsCMField.complexConj E (δ : E) = δ ∧ ∀ j : E →+* ℂ_[p], Real.log ‖j (δ : E)‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  intro E _ _ _ hU p
  set F := maximalRealSubfield E
  have hD : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E), differentIdeal_eq_top_of_unramified E, Ideal.top_mul]
  have hD0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨δ, hδI, hδ0, ⟨n, hn, hnI⟩, -⟩ := ideal_padic_generator_log_norm F (differentIdeal ℤ (𝓞 F)) p hD0
  set δ' : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) δ
  have hδ'I : δ' ∈ differentIdeal ℤ (𝓞 E) := by rw [hD]; exact Ideal.mem_map_of_mem _ hδI
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  refine ⟨δ', hδ'I, fun h => hδ0 (hinj (h.trans (map_zero _).symm)), ?_, fun j => ?_⟩
  · have : ((δ' : 𝓞 E) : E) = ((δ : F) : E) := rfl
    rw [this]
    exact IsCMField.complexConj_apply_eq_self E (δ : F)
  ·
    set j' : 𝓞 E →+* ℂ_[p] := j.comp (algebraMap (𝓞 E) E) with hj'
    have hmax : ∀ b ∈ differentIdeal ℤ (𝓞 E), ‖j' b‖ ≤ ‖j' δ'‖ := by
      intro b hb
      rw [hD] at hb
      induction hb using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hnI a ha)
        have e := congrArg (fun z : 𝓞 F => j' (algebraMap (𝓞 F) (𝓞 E) z)) hy
        simp only [map_mul, map_natCast] at e
        have h1 := congrArg norm e
        simp only [norm_mul] at h1
        rw [LocGen.norm_natCast_cp p n hn, one_mul] at h1
        rw [← h1]
        have : ‖j' (algebraMap (𝓞 F) (𝓞 E) y)‖ ≤ 1 := NI.norm_int_le j' _
        calc ‖j' (algebraMap (𝓞 F) (𝓞 E) y)‖ * ‖j' δ'‖ ≤ 1 * ‖j' δ'‖ :=
              mul_le_mul_of_nonneg_right this (norm_nonneg _)
          _ = ‖j' δ'‖ := one_mul _
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      | smul c x _ hx =>
        rw [smul_eq_mul, map_mul, norm_mul]
        have : ‖j' c‖ ≤ 1 := NI.norm_int_le j' c
        calc ‖j' c‖ * ‖j' x‖ ≤ 1 * ‖j' δ'‖ := mul_le_mul this hx (norm_nonneg _) zero_le_one
          _ = ‖j' δ'‖ := one_mul _
    exact (NI.logIdeal_eq (j.comp (algebraMap (𝓞 E) E)) _ hδ'I hmax).symm

end PositivityTheory.Xgf

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsRealDifferentGenerator
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_real_different_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : Nat.Primes, ∃ δ ∈ differentIdeal ℤ (𝓞 E), δ ≠ 0 ∧ IsCMField.complexConj E (δ : E) = δ ∧ ∀ j : E →+* ℂ_[p], Real.log ‖j (δ : E)‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @PositivityTheory.Xgf.exists_real_different_generator | exact PositivityTheory.Xgf.exists_real_different_generator
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsRealDifferentGeneratorStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_different_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : Nat.Primes, ∃ δ ∈ differentIdeal ℤ (𝓞 E), δ ≠ 0 ∧ IsCMField.complexConj E (δ : E) = δ ∧ ∀ j : E →+* ℂ_[p], Real.log ‖j (δ : E)‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_real_different_generator | exact GlobalTheory.CompanionTheory.Relay.exists_real_different_generator | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_real_different_generator <;> assumption)
end
end
