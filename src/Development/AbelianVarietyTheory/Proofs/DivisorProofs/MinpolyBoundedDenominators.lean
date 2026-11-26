module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderEqTopOfEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFiniteAdelesAwayPBoundedDenominators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFiniteAdelesAwayPBoundedDenominators
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DenAwayCpt

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlobalTheory.DenAway

theorem exists_nat_mul_integral_of_isCompact : ∀ (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)), IsCompact Q →
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ := by
  intro p _ Q hQ
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' intAfP p)
    (fun a => (isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun x hx v => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hxa' : (m a : AfP p) * x ∈ intAfP p := hxa
  have e : ((∏ a ∈ t, m a : ℕ) : AfP p) * x = (k : AfP p) * ((m a : AfP p) * x) := by
    rw [hk, Nat.cast_mul]; ring
  rw [e, eval_natCast_mul]
  exact mul_mem (natCast_mem v.1 k) (hxa' v)

end GlobalTheory.DenAwayCpt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFiniteAdelesAwayPBoundedDenominatorsStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_finiteAdelesAwayP_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)), IsCompact Q → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ := by
  first | (exact @GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact) | (exact GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact) | (intros; apply GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulRatEqIntOfIntegralAway
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulRatEqIntOfIntegralAway
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

open IsDedekindDomain

theorem ratint_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ),
    (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) →
    ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  intro p hp q h
  have hp' : p.Prime := hp.out
  have key : ∀ {l : ℕ}, l.Prime → l ∣ q.den → l = p := by
    intro l hl hld
    by_contra hne
    have hlI : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
    let v : HeightOneSpectrum ℤ :=
      ⟨Ideal.span {(l : ℤ)}, (Ideal.span_singleton_prime hlI.ne_zero).2 hlI, by simpa using hl.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro e
      have h1 : (l : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (by
        have : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
        rw [← e] at this
        exact Ideal.mem_span_singleton.1 this |>.elim (fun c hc => by
          exact Ideal.mem_span_singleton.2 ⟨c, hc⟩))
      have h2 : l ∣ p := Int.natCast_dvd_natCast.1 h1
      exact hne ((Nat.prime_dvd_prime_iff_eq hl hp').1 h2)
    have hq := h ⟨v, hv⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hq
    have hq2 : v.valuation ℚ q ≤ 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hq
    have hb : ((q.den : ℤ)) ≠ 0 := by exact_mod_cast q.den_nz
    have hcop : ((q.den : ℤ)) ∈ v.asIdeal → q.num ∉ v.asIdeal := by
      intro hd hn
      have hd' : (l : ℤ) ∣ (q.den : ℤ) := Ideal.mem_span_singleton.1 hd
      have hn' : (l : ℤ) ∣ q.num := Ideal.mem_span_singleton.1 hn
      have hc : IsCoprime q.num (q.den : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        exact_mod_cast q.reduced
      exact hlI.not_unit (hc.isUnit_of_dvd' hn' hd')
    have e : q = ((algebraMap ℤ ℚ q.num) / (algebraMap ℤ ℚ (q.den : ℤ))) := by
      simp [Rat.num_div_den]
    rw [e, v.valuation_div_le_one_iff ℚ q.num hb hcop] at hq2
    exact hq2 (Ideal.mem_span_singleton.2 (Int.natCast_dvd_natCast.2 hld))
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hld => key hl hld)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  have : ((p : ℚ) ^ q.den.primeFactorsList.length) = (q.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.den_mul_eq_num]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulRatEqIntOfIntegralAwayStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_mul_rat_eq_int_of_integral_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) → ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  first | (exact @GlobalTheory.ratint_away) | (exact GlobalTheory.ratint_away) | (intros; apply GlobalTheory.ratint_away  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharpolyCoeffMulLeftFiniteAdelesAwayP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharpolyCoeffMulLeftFiniteAdelesAwayP
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CharpolyCont

theorem continuous_eval₂_of {X R : Type*} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {σ : Type*} (f : ℤ →+* R) (P : MvPolynomial σ ℤ) (x : X → σ → R)
    (hx : ∀ i, Continuous fun t => x t i) : Continuous fun t => MvPolynomial.eval₂ f (x t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂_C]; exact continuous_const
  | add P Q hP hQ => simp only [MvPolynomial.eval₂_add]; exact hP.add hQ
  | mul_X P i hP => simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]; exact hP.mul (hx i)

theorem continuous_charpoly_coeff_mulLeft {R A : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] [TopologicalSpace A] [IsModuleTopology R A]
    (k : ℕ) : Continuous fun a : A => (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k := by
  let b := Module.Free.chooseBasis R A
  have e : ∀ a : A, (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k =
      MvPolynomial.eval₂Hom (Int.castRingHom R)
        (fun ij : Module.Free.ChooseBasisIndex R A × Module.Free.ChooseBasisIndex R A =>
          LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2)
        ((Matrix.charpoly.univ ℤ (Module.Free.ChooseBasisIndex R A)).coeff k) := by
    intro a
    rw [Matrix.charpoly.univ_coeff_eval₂Hom, ← LinearMap.charpoly_toMatrix _ b]
    rfl
  simp_rw [e]
  refine continuous_eval₂_of _ _ _ fun ij => ?_
  have h : ∀ a : A, LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2 =
      (b.coord ij.1).comp (LinearMap.mulRight R (b ij.2)) a := by
    intro a
    simp [LinearMap.toMatrix_apply]
  simp_rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

end GlobalTheory.CharpolyCont

open GlobalTheory.CharpolyCont in
theorem GlobalTheory.charpoly_coeff_continuous_GAf : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ), Continuous fun g : G.GAf =>
    (LinearMap.charpoly (LinearMap.mulLeft (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C))).coeff k := by
  intro p _ G k
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (continuous_charpoly_coeff_mulLeft (R := AfP p) (A := AfP p ⊗[ℚ] G.C) k).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharpolyCoeffMulLeftFiniteAdelesAwayPStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_charpoly_coeff_mulLeft_finiteAdeles_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ), Continuous fun g : G.GAf => (LinearMap.charpoly (LinearMap.mulLeft (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k := by
  first | (exact @GlobalTheory.charpoly_coeff_continuous_GAf) | (exact GlobalTheory.charpoly_coeff_continuous_GAf) | (intros; apply GlobalTheory.charpoly_coeff_continuous_GAf  <;> assumption)
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinPtsAway

theorem supp_compact (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) :
    ∃ Q : Set G.GAf, IsCompact Q ∧ ∀ g, f g ≠ 0 → g ∈ Q := by
  obtain ⟨-, -, -, S, hS⟩ := hf
  refine ⟨⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)), ?_, ?_⟩
  · exact S.isCompact_biUnion fun s _ => (L.compact.prod L.compact).image (by fun_prop)
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_iUnion₂.2 ⟨s, hs, (k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

theorem coeff_continuous (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ) :
    Continuous fun g : G.GAf => (LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k :=
  GlobalTheory.T.continuous_charpoly_coeff_mulLeft_finiteAdeles_awayP p G k

theorem bdd_at_places (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)) (hQ : IsCompact Q) :
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ :=
  GlobalTheory.T.compact_finiteAdelesAwayP_bounded_denominators p Q hQ

theorem rat_of_integral_away (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : ∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) :
    ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z :=
  GlobalTheory.T.exists_prime_pow_mul_rat_eq_int_of_integral_away p q hq

theorem bdd_denom (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)) (hQ : IsCompact Q) :
    ∃ D : ℕ, 0 < D ∧ ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Q → ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D * q = z := by
  obtain ⟨D, hD, hQD⟩ := bdd_at_places p Q hQ
  refine ⟨D, hD, fun q hq => ?_⟩
  obtain ⟨m, z, hz⟩ := rat_of_integral_away p (D * q) fun v => by
    have := hQD _ hq v
    rwa [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, (AfP.eval v).commutes] at this
  exact ⟨m, z, by rw [← hz, mul_assoc]⟩

theorem charpoly_conj_tmul (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (A : Type) [CommRing A]
    [Algebra ℚ A] (y : C) (u : (A ⊗[ℚ] C)ˣ) :
    LinearMap.charpoly (LinearMap.mulLeft A ((u : A ⊗[ℚ] C) * ((1 : A) ⊗ₜ[ℚ] y) * ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C))) =
      (LinearMap.charpoly (LinearMap.mulLeft ℚ y)).map (algebraMap ℚ A) := by
  let e : (A ⊗[ℚ] C) ≃ₗ[A] (A ⊗[ℚ] C) :=
    { LinearMap.mulLeft A (u : A ⊗[ℚ] C) with
      invFun := fun z => ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C) * z
      left_inv := fun z => by simp [← mul_assoc]
      right_inv := fun z => by simp [← mul_assoc] }
  have h1 : LinearMap.mulLeft A ((u : A ⊗[ℚ] C) * ((1 : A) ⊗ₜ[ℚ] y) * ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C)) =
      e.conj (LinearMap.mulLeft A ((1 : A) ⊗ₜ[ℚ] y)) := by
    ext z
    simp [e, LinearEquiv.conj_apply, mul_assoc]
  have h2 : LinearMap.mulLeft A ((1 : A) ⊗ₜ[ℚ] y) = (LinearMap.mulLeft ℚ y).baseChange A := by
    ext c
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h1, LinearEquiv.charpoly_conj, h2, LinearMap.charpoly_baseChange]

theorem integral_of_charpoly (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (y : C) (p D : ℕ)
    (h : ∀ i, ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D * (LinearMap.charpoly (LinearMap.mulLeft ℚ y)).coeff i = z) :
    ∃ m : ℕ, IsIntegral ℤ ((p : C) ^ m * D * y) := by
  choose m z hz using h
  set χ := LinearMap.charpoly (LinearMap.mulLeft ℚ y) with hχ
  set N := χ.natDegree
  set M := ∑ i ∈ Finset.range N, m i
  refine ⟨M, ?_⟩
  set s : ℚ := (p : ℚ) ^ M * D with hs
  have hχy : Polynomial.aeval y χ = 0 := by
    have e := LinearMap.aeval_self_charpoly (LinearMap.mulLeft ℚ y)
    have e2 : Polynomial.aeval (LinearMap.mulLeft ℚ y) χ = Algebra.lmul ℚ C (Polynomial.aeval y χ) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    rw [e2] at e
    have := congrArg (fun f : Module.End ℚ C => f 1) e
    simpa using this
  have hlift : χ.scaleRoots s ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i N with hi | hi | hi
    · have hmi : m i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_range.2 hi)
      refine ⟨(p : ℤ) ^ (M - m i) * z i * ((p : ℤ) ^ M * D) ^ (N - i - 1), ?_⟩
      have e1 : s ^ (N - i) = s * s ^ (N - i - 1) := by
        rw [← pow_succ']; congr 1; omega
      have e2 : s * χ.coeff i = (p : ℚ) ^ (M - m i) * z i := by
        rw [← hz i, hs, ← mul_assoc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hmi]
      simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [e1, ← mul_assoc, mul_comm (χ.coeff i) s, e2, hs]
    · subst hi
      refine ⟨1, ?_⟩
      rw [Nat.sub_self, pow_zero, mul_one, ← Polynomial.leadingCoeff, LinearMap.charpoly_monic]; simp
    · refine ⟨0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi]; simp
  obtain ⟨P, hP, hPdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
    ((Polynomial.monic_scaleRoots_iff s).2 (LinearMap.charpoly_monic _))
  refine ⟨P, hPm, ?_⟩
  have e3 : Polynomial.eval₂ (algebraMap ℤ C) ((p : C) ^ M * D * y) P =
      Polynomial.aeval ((p : C) ^ M * D * y) (χ.scaleRoots s) := by
    rw [← hP, Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]
  rw [e3, Polynomial.aeval_def]
  have e4 : (p : C) ^ M * D * y = algebraMap ℚ C s * y := by
    rw [hs]; simp
  rw [e4, Polynomial.scaleRoots_eval₂_mul_of_commute _ _ _ (Algebra.commutes _ _) (fun a b => Algebra.commutes _ _),
    ← Polynomial.aeval_def, hχy, mul_zero]

theorem minpoly_coeff_integral (F : Type) [Field F] (S : Type) [Ring S] [Algebra F S] (y : S) (c : F)
    (hc : IsIntegral ℤ (algebraMap F S c * y)) (hy : IsIntegral F y) (k : ℕ) :
    IsIntegral ℤ (c ^ ((minpoly F y).natDegree - k) * (minpoly F y).coeff k) := by
  by_cases hc0 : c = 0
  · subst hc0
    rcases lt_trichotomy k (minpoly F y).natDegree with hk | hk | hk
    · rw [zero_pow (by omega), zero_mul]; exact isIntegral_zero
    · rw [hk, Nat.sub_self, pow_zero, one_mul, ← Polynomial.leadingCoeff, minpoly.monic hy, ]; exact isIntegral_one
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk, mul_zero]; exact isIntegral_zero
  obtain ⟨P, hPm, hP⟩ := hc
  set Pm := P.map (algebraMap ℤ F)
  have hPz : Polynomial.eval₂ (algebraMap F S) (algebraMap F S c * y) Pm = 0 := by
    rw [Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]; exact hP
  have h1 : Polynomial.aeval y (Pm.scaleRoots c⁻¹) = 0 := by
    have e := Polynomial.scaleRoots_eval₂_mul_of_commute (p := Pm) (algebraMap F S) (algebraMap F S c * y) c⁻¹
      (Algebra.commutes _ _) (fun a b => Algebra.commutes _ _)
    rw [hPz, mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul] at e
    rw [Polynomial.aeval_def]; exact e
  have h2 : minpoly F y ∣ Pm.scaleRoots c⁻¹ := minpoly.dvd F y h1
  have h3 : (minpoly F y).scaleRoots c ∣ Pm := by
    have := Polynomial.scaleRoots_dvd _ _ (r := c) h2
    rwa [← Polynomial.scaleRoots_mul, inv_mul_cancel₀ hc0, Polynomial.scaleRoots_one] at this
  have h4 := Polynomial.isIntegral_coeff_of_dvd P _ hPm ((Polynomial.monic_scaleRoots_iff c).2 (minpoly.monic hy)) h3 k
  rw [Polynomial.coeff_scaleRoots, mul_comm] at h4
  exact h4

theorem exists_den_minpoly_coeff : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ D : ℕ, 0 < D ∧ ∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → ∀ k : ℕ, ∃ m : ℕ, IsIntegral ℤ ((p : G.F) ^ m * D * (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k) := by
  intro p _ G L f hf β x t hx
  obtain ⟨Q, hQc, hQ⟩ := supp_compact p G L f hf
  set N := Module.finrank ℚ G.C
  let cf : ℕ → G.GAf → AfP p := fun k g => (LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k
  have hQ'c : IsCompact (⋃ k ∈ Finset.range (N + 1), cf k '' Q) :=
    (Finset.range (N + 1)).isCompact_biUnion fun k _ => hQc.image (coeff_continuous p G k)
  obtain ⟨D', hD'0, hD'⟩ := bdd_denom p _ hQ'c
  refine ⟨D' ^ Module.finrank G.F G.C, pow_pos hD'0 _, ?_⟩
  intro y h hfy k
  set yc : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hyc
  have hg := hQ _ hfy

  set u : (AfP p ⊗[ℚ] G.C)ˣ := ((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * x with hu
  have hrep : ((((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) =
      (u : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] yc) * ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
    have e : (((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
        u * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * u⁻¹ := by
      have e0 : (((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
          ((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * x⁻¹) *
            (h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 := rfl
      rw [e0, hu]; group
    rw [e]; simp only [Units.val_mul]; rfl
  have hchar : LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      ((((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℚ yc)).map (algebraMap ℚ (AfP p)) := by
    rw [hrep]; exact charpoly_conj_tmul G.C (AfP p) yc u
  have hcoef : ∀ i, ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D' * (LinearMap.charpoly (LinearMap.mulLeft ℚ yc)).coeff i = z := by
    intro i
    by_cases hi : i ≤ N
    · apply hD'
      refine Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), _, hg, ?_⟩
      simp only [cf]
      rw [hchar, Polynomial.coeff_map]
    · refine ⟨0, 0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
      simp
  obtain ⟨M, hM⟩ := integral_of_charpoly G.C yc p D' hcoef
  have hint : IsIntegral ℤ (algebraMap G.F G.C ((p : G.F) ^ M * D') * yc) := by
    convert hM using 2
    simp [map_mul, map_pow, map_natCast]
  have hI := minpoly_coeff_integral G.F G.C yc _ hint (Algebra.IsIntegral.isIntegral _) k
  set d := (minpoly G.F yc).natDegree
  have hd : d ≤ Module.finrank G.F G.C := minpoly.natDegree_le yc
  by_cases hk : k ≤ d
  · refine ⟨M * (d - k), ?_⟩
    have e : (p : G.F) ^ (M * (d - k)) * ((D' ^ Module.finrank G.F G.C : ℕ) : G.F) * (minpoly G.F yc).coeff k =
        (D' : G.F) ^ (Module.finrank G.F G.C - (d - k)) *
          (((p : G.F) ^ M * D') ^ (d - k) * (minpoly G.F yc).coeff k) := by
      rw [mul_pow, ← pow_mul, Nat.cast_pow]
      have : Module.finrank G.F G.C = (Module.finrank G.F G.C - (d - k)) + (d - k) := by omega
      conv_lhs => rw [this, pow_add]
      ring
    rw [e]
    have hD : IsIntegral ℤ (D' : G.F) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ G.F (D' : ℤ)))
    exact (hD.pow _).mul hI
  · refine ⟨0, ?_⟩
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
    exact isIntegral_zero

end GlobalTheory.FinPtsAway
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ D : ℕ, 0 < D ∧ ∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → ∀ k : ℕ, ∃ m : ℕ, IsIntegral ℤ ((p : G.F) ^ m * D * (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k) := by
  first | (exact @GlobalTheory.FinPtsAway.exists_den_minpoly_coeff) | (exact GlobalTheory.FinPtsAway.exists_den_minpoly_coeff) | (intros; apply GlobalTheory.FinPtsAway.exists_den_minpoly_coeff  <;> assumption)
