module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassesFixedUnitsModRatNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalNormApproxOfLocalPadicNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulIsIntegralOfPadicIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMinpolyMemAdicCompletionIntegers
open scoped TensorProduct Classical
open Polynomial

namespace GlobalTheory.DescCoeff

theorem natDegree_minpoly_le_one_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := _root_.GlobalTheory.CentSep.natDegree_minpoly_le_baseChange (F := F) (A := A) K g hK

theorem minpoly_one_tmul_eq {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (K : Type) [Field K] [Algebra F K] (y : B) :
    minpoly K ((1 : K) ⊗ₜ[F] y) = (minpoly F y).map (algebraMap F K) := by
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := natDegree_minpoly_le_one_tmul K y hzi
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
    (by rw [natDegree_map]; exact hge)
  rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]

end GlobalTheory.DescCoeff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulIsIntegralOfPadicIntegral
open scoped TensorProduct Classical
open Polynomial

namespace GlobalTheory.IntegralDescent

theorem not_dvd_den_coeff_minpoly (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (w : E) (hw : IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w)) (i : ℕ) :
    ¬ ℓ ∣ ((minpoly ℚ w).coeff i).den := by
  obtain ⟨p, hpm, hp⟩ := hw
  have hzi : IsIntegral ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) := IsIntegral.of_finite _ _
  have hdvd : minpoly ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) ∣ p.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
    apply minpoly.dvd
    rw [aeval_def, eval₂_map]
    exact hp
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ_[ℓ] hpm hdvd
  rw [(minpoly.monic hzi).leadingCoeff, C_1, mul_one, GlobalTheory.DescCoeff.minpoly_one_tmul_eq] at hg
  have hc := congrArg (fun q => q.coeff i) hg
  simp only [coeff_map] at hc
  have hn : ‖(((minpoly ℚ w).coeff i : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
    rw [← eq_ratCast (algebraMap ℚ ℚ_[ℓ]), ← hc]
    exact (g.coeff i).2
  intro hd
  have hu := PadicInt.isUnit_den _ hn
  exact PadicInt.irreducible_p.not_isUnit
    (isUnit_of_dvd_unit (Nat.cast_dvd_cast (α := ℤ_[ℓ]) hd) hu)

theorem exists_not_dvd_isIntegral_mul : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (w : E), IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) → ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * w) := by
  intro E _ _ _ ℓ hℓ w hw
  set f := minpoly ℚ w with hf
  have hfm : f.Monic := minpoly.monic (IsIntegral.of_finite ℚ w)
  set d : ℕ := ∏ i ∈ Finset.range f.natDegree, (f.coeff i).den with hd
  refine ⟨d, ?_, ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (hℓ.out.prime.dvd_finsetProd_iff _).mp h
    exact not_dvd_den_coeff_minpoly E ℓ w hw i hi
  · have hroot : aeval ((d : E) * w) (f.scaleRoots (d : ℚ)) = 0 := by
      have := scaleRoots_aeval_eq_zero (r := (d : ℚ)) (minpoly.aeval ℚ w)
      rwa [map_natCast] at this
    have hlift : f.scaleRoots (d : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
      rw [lifts_iff_coeff_lifts]
      intro i
      rw [coeff_scaleRoots]
      rcases lt_trichotomy i f.natDegree with hi | hi | hi
      · obtain ⟨c, hc⟩ : (f.coeff i).den ∣ d :=
          Finset.dvd_prod_of_mem (fun j => (f.coeff j).den) (Finset.mem_range.mpr hi)
        obtain ⟨k, hk⟩ : ∃ k, f.natDegree - i = k + 1 := ⟨f.natDegree - i - 1, by omega⟩
        refine ⟨(f.coeff i).num * c * (d : ℤ) ^ k, ?_⟩
        rw [hk, pow_succ]
        have h1 : (d : ℚ) = ((f.coeff i).den : ℚ) * c := by exact_mod_cast hc
        have h2 : f.coeff i * ((f.coeff i).den : ℚ) = (f.coeff i).num := Rat.mul_den_eq_num _
        simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
        rw [← h2]
        linear_combination (-(f.coeff i) * (d : ℚ) ^ k) * h1
      · subst hi
        exact ⟨1, by simp [hfm.coeff_natDegree]⟩
      · exact ⟨0, by simp [coeff_eq_zero_of_natDegree_lt hi]⟩
    obtain ⟨q, hq, -, hqm⟩ :=
      lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff _).mpr hfm)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ, hq]
    exact hroot

end GlobalTheory.IntegralDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulIsIntegralOfPadicIntegralStatement
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (w : E), IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) → ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * w) := by
  first | (exact @GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul) | (exact GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul) | (intros; apply GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxUnitPadicTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxUnitPadicTensor
open scoped TensorProduct Classical

namespace GlobalTheory.PadicTensorApprox

variable {E : Type} [CommRing E] [Algebra ℚ E] {ℓ : ℕ} [Fact ℓ.Prime]

theorem isIntegral_tmul (u : ℚ_[ℓ]) (hu : ‖u‖ ≤ 1) (c : E) (hc : IsIntegral ℤ c) :
    IsIntegral ℤ_[ℓ] (u ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) := by
  have h1 : IsIntegral ℤ ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) :=
    map_isIntegral_int (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := E)) hc
  have h2 : IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) := by
    obtain ⟨P, hP, hP'⟩ := h1
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hP']
    congr 1
  let v : ℤ_[ℓ] := ⟨u, hu⟩
  have h3 := h2.smul v
  have e : v • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) = u ⊗ₜ[ℚ] c := by
    rw [TensorProduct.smul_tmul']
    congr 1
    change u * 1 = u
    exact mul_one u
  rwa [e] at h3

theorem exists_tmul_integral [FiniteDimensional ℚ E] (a : ℚ_[ℓ]) (c : E) :
    ∃ (a' : ℚ_[ℓ]) (c' : E), IsIntegral ℤ c' ∧ (a ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) = a' ⊗ₜ[ℚ] c' := by
  have hq : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hz : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hq
  obtain ⟨m, hm, hi⟩ := hz.exists_integral_multiple
  refine ⟨((m : ℚ)⁻¹) • a, m • c, hi, ?_⟩
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hm', one_smul]

theorem pow_mul_tmul (N : ℕ) (a : ℚ_[ℓ]) (c : E) :
    (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * (a ⊗ₜ[ℚ] c) = ((ℓ : ℚ_[ℓ]) ^ N * a) ⊗ₜ[ℚ] c := by
  have : (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N = ((ℓ : ℚ_[ℓ]) ^ N) ⊗ₜ[ℚ] (1 : E) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Algebra.TensorProduct.natCast_def]
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem exists_pow_mul_isIntegral [FiniteDimensional ℚ E] (x : ℚ_[ℓ] ⊗[ℚ] E) :
    ∃ N : ℕ, IsIntegral ℤ_[ℓ] ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * x) := by
  have hl : IsIntegral ℤ_[ℓ] (ℓ : ℚ_[ℓ] ⊗[ℚ] E) := by
    have := isIntegral_algebraMap (R := ℤ_[ℓ]) (A := ℚ_[ℓ] ⊗[ℚ] E) (x := (ℓ : ℤ_[ℓ]))
    rwa [map_natCast] at this
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [mul_zero]; exact isIntegral_zero⟩
  | add x y hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨N, hN⟩ := hy
    refine ⟨M + N, ?_⟩
    have := ((hl.pow N).mul hM).add ((hl.pow M).mul hN)
    have e : (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ (M + N) * (x + y) = (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ M * x) +
        (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ M * ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * y) := by ring
    rwa [e]
  | tmul a c =>
    obtain ⟨a', c', hc, e⟩ := exists_tmul_integral a c
    have hp : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖a'‖ hp
    refine ⟨N, ?_⟩
    rw [e, pow_mul_tmul]
    refine isIntegral_tmul _ ?_ _ hc
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
    exact hN.le

theorem exists_sub_eq_pow_mul [FiniteDimensional ℚ E] (N : ℕ) (x : ℚ_[ℓ] ⊗[ℚ] E) :
    ∃ (b : E) (t : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] t ∧
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = x + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * t := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, isIntegral_zero, by simp⟩
  | add x y hx hy =>
    obtain ⟨b, t, ht, e⟩ := hx
    obtain ⟨b', t', ht', e'⟩ := hy
    refine ⟨b + b', t + t', ht.add ht', ?_⟩
    rw [TensorProduct.tmul_add, e, e']
    ring
  | tmul a c =>
    obtain ⟨a', c', hc, e⟩ := exists_tmul_integral a c
    have hp : (0 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    have hl : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    obtain ⟨q, hq⟩ := Padic.rat_dense ℓ a' (ε := ((ℓ : ℝ) ^ N)⁻¹) (by positivity)
    refine ⟨q • c', (((q : ℚ_[ℓ]) - a') / (ℓ : ℚ_[ℓ]) ^ N) ⊗ₜ[ℚ] c', isIntegral_tmul _ ?_ _ hc, ?_⟩
    · rw [norm_div, norm_pow, Padic.norm_p, inv_pow, div_le_one (by positivity), norm_sub_rev]
      exact hq.le
    · rw [e, pow_mul_tmul, ← TensorProduct.add_tmul, ← TensorProduct.smul_tmul]
      congr 1
      rw [Rat.smul_one_eq_cast]
      field_simp
      ring

theorem exists_approx_unit (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ) :
    ∃ (b : E) (s : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] s ∧
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = (z : ℚ_[ℓ] ⊗[ℚ] E) * (1 + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) * s) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_isIntegral ((z⁻¹ : (ℚ_[ℓ] ⊗[ℚ] E)ˣ) : ℚ_[ℓ] ⊗[ℚ] E)
  obtain ⟨b, t, ht, e⟩ := exists_sub_eq_pow_mul (N + 1) (z : ℚ_[ℓ] ⊗[ℚ] E)
  refine ⟨b, _, hN.mul ht, ?_⟩
  have h := z.mul_inv
  rw [e]
  linear_combination (-((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ (N + 1) * t)) * h

end GlobalTheory.PadicTensorApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxUnitPadicTensorStatement
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_unit_padic_tensor : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), ∃ (b : E) (s : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] s ∧ (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = (z : ℚ_[ℓ] ⊗[ℚ] E) * (1 + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) * s) := by
  first | (exact @GlobalTheory.PadicTensorApprox.exists_approx_unit) | (exact GlobalTheory.PadicTensorApprox.exists_approx_unit) | (intros; apply GlobalTheory.PadicTensorApprox.exists_approx_unit  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvOneAddPrimeMulPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvOneAddPrimeMulPadic
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_integral_inv_one_add_prime_mul :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S] (s : S),
      IsIntegral ℤ_[ℓ] s → ∃ r : S, (1 + (ℓ : S) * s) * r = 1 ∧ IsIntegral ℤ_[ℓ] r := by
  intro ℓ _ S _ _ s hs
  let B := integralClosure ℤ_[ℓ] S
  let b : B := ⟨s, hs⟩
  have hu : IsUnit (1 + (ℓ : B) * b) := by
    by_contra hn
    obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hn)
    have hmax : (M.comap (algebraMap ℤ_[ℓ] B)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[ℓ]) M
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have hl : (ℓ : ℤ_[ℓ]) ∈ M.comap (algebraMap ℤ_[ℓ] B) := by
      rw [heq, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at hl
    have h1 : (1 : B) ∈ M := by
      have := M.sub_mem hmem (M.mul_mem_right b hl)
      simpa using this
    exact hM.ne_top ((Ideal.eq_top_iff_one M).mpr h1)
  obtain ⟨r, hr⟩ := hu.exists_right_inv
  refine ⟨(r : S), ?_, r.2⟩
  have := congrArg (fun x : B => (x : S)) hr
  simpa [b] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvOneAddPrimeMulPadicStatement
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_inv_one_add_prime_mul_padic : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S] (s : S), IsIntegral ℤ_[ℓ] s → ∃ r : S, (1 + (ℓ : S) * s) * r = 1 ∧ IsIntegral ℤ_[ℓ] r := by
  first | (exact @GlobalTheory.exists_integral_inv_one_add_prime_mul) | (exact GlobalTheory.exists_integral_inv_one_add_prime_mul) | (intros; apply GlobalTheory.exists_integral_inv_one_add_prime_mul  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalNormApproxOfLocalPadicNorm
open scoped TensorProduct Classical

namespace GlobalTheory.LocalApprox

theorem isUnit_of_isUnit_one_tmul (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (b : E) (hb : IsUnit ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b)) : IsUnit b := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ ℚ_[ℓ]).injective
  have h1 : Function.Injective (LinearMap.mulLeft ℚ b) := by
    intro x y hxy
    apply hinj
    have h := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) hxy
    simp only [LinearMap.mulLeft_apply, map_mul] at h
    exact hb.mul_left_cancel h
  obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.1 h1 1
  have hw' : b * w = 1 := hw
  exact ⟨⟨b, w, hw', by rw [mul_comm]; exact hw'⟩, rfl⟩

theorem exists_rat_mul_unit (ℓ : ℕ) [Fact ℓ.Prime] (u : ℚ_[ℓ]ˣ) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ r : ℤ_[ℓ]ˣ, (u : ℚ_[ℓ]) = algebraMap ℚ ℚ_[ℓ] c * ((r : ℤ_[ℓ]) : ℚ_[ℓ]) := by
  have hu : 0 < ‖(u : ℚ_[ℓ])‖ := norm_pos_iff.2 u.ne_zero
  obtain ⟨c, hc⟩ := Padic.rat_dense ℓ (u : ℚ_[ℓ]) hu
  have hn : ‖(c : ℚ_[ℓ])‖ = ‖(u : ℚ_[ℓ])‖ := by
    have h : (c : ℚ_[ℓ]) = (u : ℚ_[ℓ]) + -((u : ℚ_[ℓ]) - c) := by ring
    have hlt : ‖-((u : ℚ_[ℓ]) - c)‖ < ‖(u : ℚ_[ℓ])‖ := by rwa [norm_neg]
    rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]
  have hc0 : (c : ℚ_[ℓ]) ≠ 0 := norm_pos_iff.1 (hn ▸ hu)
  have h1 : ‖(u : ℚ_[ℓ]) / c‖ = 1 := by rw [norm_div, hn, div_self hu.ne']
  refine ⟨c, fun h => hc0 (by simp [h]), PadicInt.mkUnits h1, ?_⟩
  rw [PadicInt.mkUnits_eq, eq_ratCast, mul_div_cancel₀ _ hc0]

theorem main : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E →ₐ[ℚ] E) (ℓ : ℕ) [Fact ℓ.Prime]
    (a : E) (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), IsUnit a →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] E) (u : ℚ_[ℓ]) *
      ((z : ℚ_[ℓ] ⊗[ℚ] E) * Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ (z : ℚ_[ℓ] ⊗[ℚ] E)) →
    ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y) := by
  intro E _ _ _ τ ℓ _ a u z ha hau
  set S := ℚ_[ℓ] ⊗[ℚ] E
  set τℓ : S →ₐ[ℚ_[ℓ]] S := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ with hτℓ
  set ι : E →ₐ[ℚ] S := Algebra.TensorProduct.includeRight with hι
  have hιapp : ∀ w : E, ι w = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w := fun w => rfl
  have hτι : ∀ w : E, τℓ (ι w) = ι (τ w) := fun w => by
    show Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] τ w
    rw [Algebra.TensorProduct.map_tmul]; rfl
  have hιq : ∀ q : ℚ, ι (algebraMap ℚ E q) = algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] q) := fun q => by
    rw [ι.commutes, IsScalarTower.algebraMap_apply ℚ ℚ_[ℓ] S]
  have hint : ∀ t : ℤ_[ℓ], IsIntegral ℤ_[ℓ] (algebraMap ℚ_[ℓ] S (t : ℚ_[ℓ])) := fun t => by
    rw [show (t : ℚ_[ℓ]) = algebraMap ℤ_[ℓ] ℚ_[ℓ] t from rfl, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  have hτint : ∀ w : S, IsIntegral ℤ_[ℓ] w → IsIntegral ℤ_[ℓ] (τℓ w) := fun w hw =>
    hw.map (τℓ.restrictScalars ℤ_[ℓ])
  obtain ⟨c, hc0, r, hur⟩ := exists_rat_mul_unit ℓ u
  obtain ⟨b, s, hs, hb⟩ := GlobalTheory.T.exists_approx_unit_padic_tensor E ℓ z
  obtain ⟨ρ, hρ, hρint⟩ := GlobalTheory.T.exists_integral_inv_one_add_prime_mul_padic ℓ S s hs
  set v : S := 1 + (ℓ : S) * s with hv
  have hvint : IsIntegral ℤ_[ℓ] v := by
    refine isIntegral_one.add (IsIntegral.mul ?_ hs)
    rw [show (ℓ : S) = algebraMap ℤ_[ℓ] S ℓ by simp]
    exact isIntegral_algebraMap
  have hbU : IsUnit b := isUnit_of_isUnit_one_tmul E ℓ b (by
    rw [hb]; exact z.isUnit.mul ⟨⟨_, ρ, hρ, by rw [mul_comm]; exact hρ⟩, rfl⟩)
  set m : E := algebraMap ℚ E c * (b * τ b) with hm
  have hmU : IsUnit m := ((isUnit_iff_ne_zero.2 hc0).map (algebraMap ℚ E)).mul (hbU.mul (hbU.map τ))
  obtain ⟨mi, hmi⟩ : ∃ mi : E, m * mi = 1 := ⟨_, hmU.mul_val_inv⟩
  obtain ⟨ai, hai⟩ : ∃ ai : E, a * ai = 1 := ⟨_, ha.mul_val_inv⟩

  set R : S := algebraMap ℚ_[ℓ] S ((r : ℤ_[ℓ]) : ℚ_[ℓ]) with hR
  set Ri : S := algebraMap ℚ_[ℓ] S (((r⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) with hRi
  set C : S := algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] c) with hC
  set U : S := algebraMap ℚ_[ℓ] S (u : ℚ_[ℓ]) with hU
  have hUCR : U = C * R := by rw [hU, hur, map_mul]
  have hRRi : R * Ri = 1 := by
    rw [hR, hRi, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      PadicInt.coe_one, map_one]
  have h1 : ι a = U * ((z : S) * τℓ z) := hau
  have h2 : ι m = C * (((z : S) * v) * (τℓ z * τℓ v)) := by
    rw [hm, map_mul, map_mul, hιq, hτι b |>.symm, hιapp b, hb, map_mul]
  have h4 : v * ρ = 1 := hρ
  have h5 : τℓ v * τℓ ρ = 1 := by rw [← map_mul, h4, map_one]
  have h3 : ι m * ι mi = 1 := by rw [← map_mul, hmi, map_one]
  have h3' : ι a * ι ai = 1 := by rw [← map_mul, hai, map_one]
  have hx : ι (a * mi) = R * ρ * τℓ ρ := by
    have hK : R * ρ * τℓ ρ * ι m = ι a := by
      rw [h2, h1, hUCR]
      linear_combination (C * R * (z : S) * τℓ z * τℓ v * τℓ ρ) * h4 + (C * R * (z : S) * τℓ z) * h5
    rw [map_mul]
    linear_combination (-ι mi) * hK + (R * ρ * τℓ ρ) * h3
  have hy : ι (m * ai) = Ri * v * τℓ v := by
    have hK : Ri * v * τℓ v * ι a = ι m := by
      rw [h2, h1, hUCR]
      linear_combination (C * (z : S) * v * τℓ z * τℓ v) * hRRi
    rw [map_mul]
    linear_combination (-ι ai) * hK + (Ri * v * τℓ v) * h3'
  obtain ⟨d1, hd1, hx1⟩ := GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (a * mi) (by
    rw [← hιapp, hx]
    exact ((hint _).mul hρint).mul (hτint _ hρint))
  obtain ⟨d2, hd2, hy2⟩ := GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (m * ai) (by
    rw [← hιapp, hy]
    exact ((hint _).mul hvint).mul (hτint _ hvint))
  refine ⟨c, b, a * mi, m * ai, hc0, hbU, ?_, ?_, d1 * d2, ?_, ?_, ?_⟩
  · linear_combination (-a) * hmi
  · linear_combination (-m) * hai
  · intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : ℓ.Prime)).1 h with h | h
    · exact hd1 h
    · exact hd2 h
  · have : ((d1 * d2 : ℕ) : E) * (a * mi) = (d2 : E) * ((d1 : E) * (a * mi)) := by push_cast; ring
    rw [this]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d2 : ℤ))).mul hx1
  · have : ((d1 * d2 : ℕ) : E) * (m * ai) = (d1 : E) * ((d2 : E) * (m * ai)) := by push_cast; ring
    rw [this]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d1 : ℤ))).mul hy2

end GlobalTheory.LocalApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalNormApproxOfLocalPadicNormStatement
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_norm_approx_of_local_padic_norm : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E →ₐ[ℚ] E) (ℓ : ℕ) [Fact ℓ.Prime]
    (a : E) (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), IsUnit a →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] E) (u : ℚ_[ℓ]) *
      ((z : ℚ_[ℓ] ⊗[ℚ] E) * Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ (z : ℚ_[ℓ] ⊗[ℚ] E)) →
    ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y) := by
  first | (exact @GlobalTheory.LocalApprox.main) | (exact GlobalTheory.LocalApprox.main) | (intros; apply GlobalTheory.LocalApprox.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFixedUnitClassesCentralizerRegular
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β →
    ∀ (y₀ : G.Cˣ) (s : ℚ), (y₀ : G.C) * β * sh G (y₀ : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (y₀ : G.C)).Separable → (minpoly G.F (y₀ : G.C)).natDegree = G.n → ∀ S : Finset ℕ,
    ∃ A : Finset G.C, ∀ a : G.C, IsUnit a → Commute a y₀ → (β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C) = a →
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (y₀ : G.C)) ∧
      inC G ℚ_[ℓ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C))) →
      ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : G.Cˣ), Commute (e : G.C) y₀ ∧
        a = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a₀ * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  intro p _ G β hβ y₀ s hy hsep hdeg S
  classical
  set Ec : Subalgebra ℚ G.C := Subalgebra.centralizer ℚ ({(y₀ : G.C)} : Set G.C) with hEc
  have memE : ∀ x : G.C, x ∈ Ec ↔ Commute x (y₀ : G.C) := by
    intro x
    rw [hEc, Subalgebra.mem_centralizer_iff]
    constructor
    · intro h; exact (h (y₀ : G.C) (Set.mem_singleton _)).symm
    · intro h g hg; rw [Set.mem_singleton_iff.1 hg]; exact h.eq.symm
  have hcomm : ∀ a b : Ec, a * b = b * a := fun a b => Subtype.ext
    (GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G y₀ hsep hdeg a b ((memE a).1 a.2) ((memE b).1 b.2)).eq
  letI : CommRing Ec := { (inferInstance : Ring Ec) with mul_comm := hcomm }
  haveI : FiniteDimensional ℚ G.C := Module.Finite.trans G.F G.C
  haveI : FiniteDimensional ℚ Ec := inferInstance
  haveI : IsReduced Ec := ⟨fun x ⟨k, hk⟩ => Subtype.ext (GlobalTheory.T.eq_zero_of_nilpotent_commute_separable_minpoly p G y₀ hsep hdeg x ((memE x).1 x.2) k
    (by simpa using congrArg Subtype.val hk))⟩

  have sh_add : ∀ x y : G.C, sh G (x + y) = sh G x + sh G y := fun x y => by simp [sh]
  have sh_mul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := fun x y => by simp [sh]
  have sh_one : sh G 1 = 1 := by simp [sh]
  have sh_zero : sh G 0 = 0 := by simp [sh]
  have sh_alg : ∀ q : ℚ, sh G (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := fun q => by
    simp only [sh, RingHom.map_rat_algebraMap G.star q, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
  have sh_sh : ∀ x, sh G (sh G x) = x := fun x => G.star_star x
  have sh_binv : sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
    have h1 : sh G ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by
      rw [← hβ, ← sh_mul, Units.mul_inv, sh_one]
    calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h0 : sh G (y₀ : G.C) = 0 := by
      have := congrArg (fun t => ((β⁻¹ : G.Cˣ) : G.C) * (((y₀⁻¹ : G.Cˣ) : G.C) * t)) hy
      simpa [← mul_assoc] using this
    have : (y₀ : G.C) = 0 := by rw [← sh_sh (y₀ : G.C), h0, sh_zero]
    exact y₀.ne_zero this
  have tC_y : (β : G.C) * sh G (y₀ : G.C) * ((β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C s * ((y₀⁻¹ : G.Cˣ) : G.C) := by
    have := congrArg (fun t => ((y₀⁻¹ : G.Cˣ) : G.C) * t * ((β⁻¹ : G.Cˣ) : G.C)) hy
    simp only [← mul_assoc, Units.inv_mul, one_mul] at this
    rw [this, mul_assoc, Units.mul_inv, mul_one, Algebra.commutes]
  have tC_mul : ∀ x y : G.C, (β : G.C) * sh G (x * y) * ((β⁻¹ : G.Cˣ) : G.C) =
      ((β : G.C) * sh G y * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro x y
    rw [sh_mul]; simp only [mul_assoc, Units.inv_mul_cancel_left]
  have tC_mem : ∀ x : G.C, Commute x (y₀ : G.C) →
      Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) (y₀ : G.C) := by
    intro x hx
    have h1 : Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) (algebraMap ℚ G.C s * ((y₀⁻¹ : G.Cˣ) : G.C)) := by
      rw [← tC_y]
      show _ * _ = _ * _
      rw [← tC_mul, ← tC_mul, hx.eq]
    have h2 : Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) ((y₀⁻¹ : G.Cˣ) : G.C) := by
      have h3 := h1.smul_right (s⁻¹)
      rwa [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_mul] at h3
    simpa using h2.units_inv_right

  let τf : Ec → Ec := fun x => ⟨(β : G.C) * sh G (x : G.C) * ((β⁻¹ : G.Cˣ) : G.C), (memE _).2 (tC_mem x ((memE x).1 x.2))⟩
  have τf_val : ∀ x : Ec, ((τf x : Ec) : G.C) = (β : G.C) * sh G (x : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := fun x => rfl
  have τf_inv : ∀ x, τf (τf x) = x := by
    intro x; apply Subtype.ext
    rw [τf_val, τf_val, sh_mul, sh_mul, sh_sh, hβ, sh_binv]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
    rw [Units.mul_inv, mul_one]
  let τa : Ec →ₐ[ℚ] Ec :=
    { toFun := τf
      map_one' := by apply Subtype.ext; rw [τf_val]; simp [sh_one]
      map_mul' := by
        intro x y; apply Subtype.ext
        rw [τf_val, Subalgebra.coe_mul, tC_mul, ← τf_val, ← τf_val, ← Subalgebra.coe_mul, hcomm]
      map_zero' := by apply Subtype.ext; rw [τf_val]; simp [sh_zero]
      map_add' := by
        intro x y; apply Subtype.ext
        rw [τf_val, Subalgebra.coe_add, sh_add, mul_add, add_mul]; rfl
      commutes' := by
        intro q; apply Subtype.ext
        rw [τf_val]
        change (β : G.C) * sh G (algebraMap ℚ G.C q) * ((β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C q
        rw [sh_alg, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one] }
  have τa_apply : ∀ x, τa x = τf x := fun x => rfl
  let τe : Ec ≃ₐ[ℚ] Ec := AlgEquiv.ofAlgHom τa τa (AlgHom.ext fun x => τf_inv x) (AlgHom.ext fun x => τf_inv x)
  have τe_apply : ∀ x, τe x = τf x := fun x => rfl
  have τe_inv : ∀ x, τe (τe x) = x := fun x => τf_inv x

  obtain ⟨x₁, hx₁⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one G.F)
  set jF : G.F := x₁ - IsCMField.complexConj G.F x₁ with hjF
  have hjF0 : jF ≠ 0 := by
    rw [hjF, sub_ne_zero]; intro h; exact hx₁ (by rw [← h]; rfl)
  have hjFc : IsCMField.complexConj G.F jF = -jF := by
    rw [hjF, map_sub, IsCMField.complexConj_apply_apply]; ring
  have cen : ∀ z : G.F, algebraMap G.F G.C z ∈ Ec := fun z => (memE _).2 (Algebra.commutes z (y₀ : G.C))
  let jE : Ec := ⟨algebraMap G.F G.C jF, cen jF⟩
  have hjE : IsUnit jE := by
    have h : jE * ⟨algebraMap G.F G.C jF⁻¹, cen _⟩ = 1 := by
      apply Subtype.ext
      change algebraMap G.F G.C jF * algebraMap G.F G.C jF⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hjF0, map_one]
    exact ⟨⟨jE, _, h, by rw [hcomm]; exact h⟩, rfl⟩
  have hjτ : τe jE = -jE := by
    apply Subtype.ext
    rw [τe_apply, τf_val]
    change (β : G.C) * (G.star (algebraMap G.F G.C jF)).unop * ((β⁻¹ : G.Cˣ) : G.C) = -algebraMap G.F G.C jF
    rw [G.star_F, hjFc, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one, map_neg]
  obtain ⟨A', hA'⟩ := GlobalTheory.T.finite_classes_fixedUnits_mod_rat_norms Ec τe τe_inv jE hjE hjτ S
  refine ⟨A'.image Subtype.val, ?_⟩
  intro a ha hac hafix hloc

  obtain ⟨ua, rfl⟩ := ha
  have ha' : (ua : G.C) ∈ Ec := (memE _).2 hac
  set a' : Ec := ⟨ua, ha'⟩ with ha'def
  have hinvE : ((ua⁻¹ : G.Cˣ) : G.C) ∈ Ec := (memE _).2 hac.units_inv_left
  have ha'u : IsUnit a' := by
    have h : a' * ⟨_, hinvE⟩ = 1 := Subtype.ext ua.mul_inv
    exact ⟨⟨a', _, h, by rw [hcomm]; exact h⟩, rfl⟩
  have ha'fix : τe a' = a' := Subtype.ext hafix
  have hloc' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : Ec), c ≠ 0 ∧ IsUnit b ∧
      a' = x * (algebraMap ℚ Ec c * (b * τe b)) ∧
      algebraMap ℚ Ec c * (b * τe b) = y * a' ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : Ec) * x) ∧
        IsIntegral ℤ ((d : Ec) * y) := by
    intro ℓ hℓ hℓS
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨u, z, hzc, hz⟩ := hloc ℓ hℓS
    obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.tensor_centralizer_injective_commutant_eq ℚ_[ℓ] G.C (y₀ : G.C)
    set ι := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) Ec.val with hι
    have hinCy : inC G ℚ_[ℓ] (y₀ : G.C) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (y₀ : G.C) := rfl
    obtain ⟨w, hw⟩ := hsurj z (hinCy ▸ hzc)
    obtain ⟨w2, hw2⟩ := hsurj ((z⁻¹ : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ) : ℚ_[ℓ] ⊗[ℚ] G.C) (hinCy ▸ hzc.units_inv_left)
    have hww : w * w2 = 1 := hinj (by rw [map_mul, hw, hw2, Units.mul_inv, map_one])
    let Z : (ℚ_[ℓ] ⊗[ℚ] Ec)ˣ := ⟨w, w2, hww, by rw [mul_comm]; exact hww⟩
    set τℓ := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τe.toAlgHom with hτℓ
    have hkey : ∀ t : ℚ_[ℓ] ⊗[ℚ] Ec, ι (τℓ t) = inC G ℚ_[ℓ] (β : G.C) * (starT G.star ℚ_[ℓ] (ι t)).unop *
        inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul r e =>
        rw [hτℓ, hι, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          starT_tmul]
        simp only [inC, AlgHom.id_apply, Subalgebra.coe_val, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rfl
      | add t1 t2 h1 h2 => rw [map_add (f := _), map_add (f := _), h1, h2, map_add (f := _), map_add (f := _), MulOpposite.unop_add, mul_add, add_mul]
    have heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a' = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] Ec) (u : ℚ_[ℓ]) *
        ((Z : ℚ_[ℓ] ⊗[ℚ] Ec) * τℓ (Z : ℚ_[ℓ] ⊗[ℚ] Ec)) := by
      apply hinj
      rw [map_mul, map_mul, AlgHom.commutes, hkey]
      have hZ : ι (Z : ℚ_[ℓ] ⊗[ℚ] Ec) = z := hw
      rw [hZ, hι, Algebra.TensorProduct.map_tmul]
      change inC G ℚ_[ℓ] (ua : G.C) = _
      rw [hz]
      simp only [mul_assoc]
    obtain ⟨c, b, x, y, hc, hb, h1, h2, d, hd, hx, hy⟩ := GlobalTheory.T.exists_global_norm_approx_of_local_padic_norm Ec τe.toAlgHom ℓ a' u Z ha'u heq
    exact ⟨c, b, x, y, hc, hb, h1, h2, d, hd, hx, hy⟩
  obtain ⟨a₀, ha₀, r, e, hre⟩ := hA' a' ha'u ha'fix hloc'
  refine ⟨(a₀ : G.C), Finset.mem_image_of_mem _ ha₀, r, Units.map (Ec.val : Ec →* G.C) e, (memE _).1 (e : Ec).2, ?_⟩
  rw [τe_apply] at hre
  have := congrArg Subtype.val hre
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, τf_val] at this
  simpa using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFixedUnitClassesCentralizerRegularStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β →
    ∀ (y₀ : G.Cˣ) (s : ℚ), (y₀ : G.C) * β * sh G (y₀ : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (y₀ : G.C)).Separable → (minpoly G.F (y₀ : G.C)).natDegree = G.n → ∀ S : Finset ℕ,
    ∃ A : Finset G.C, ∀ a : G.C, IsUnit a → Commute a y₀ → (β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C) = a →
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (y₀ : G.C)) ∧
      inC G ℚ_[ℓ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C))) →
      ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : G.Cˣ), Commute (e : G.C) y₀ ∧
        a = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a₀ * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  first | (exact @GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular) | (exact GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular) | (intros; apply GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular  <;> assumption)
end
