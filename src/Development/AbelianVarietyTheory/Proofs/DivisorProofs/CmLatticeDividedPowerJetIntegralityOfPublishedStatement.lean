module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZeta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeSumDerivativesEqEisensteinJets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPassScaled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalScalarNormalisedStandardFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzJetConj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CMLatticeDividedPowerJetIntegralityOfHyp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestLast
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorBoundWeierstrassCmTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFormulaWeierstrassPIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFormulaWeierstrassPIntegral
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.IsogFormula

theorem main : ∀ (L : PeriodPair) (α β Ω P : ℂ) (M n : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → MulStable L α → Complex.normSq α = n → 0 < n → 0 < M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (((M * n : ℕ) : ℂ) ^ 2 * ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2))) := by
  intro L α β Ω P M n hβ hβim hΩ hα hnorm hn hM hP hMP
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [map_zero] at hnorm
    have h0 : n = 0 := by exact_mod_cast hnorm.symm
    omega
  obtain ⟨S, hS⟩ := kernel_reps_exist L α hα0 hα
  have hcard := kernel_reps_card L α S hα0 hα hS
  have hs2 := quasiPeriodConstIsogeny_thm L α S hα0 hα hS
  obtain ⟨t, m, ht, hm, -⟩ := mul_stable_integral L α hα
  have hcardn : S.card + 1 = n := by
    rw [hnorm] at hcard
    exact_mod_cast hcard
  have hVL := (GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L β Ω (M * n) hβ hβim hΩ (Nat.mul_pos hM hn)).2
  have hnat : ∀ (k : ℕ) (x : ℂ), x ∈ L.lattice → (k : ℂ) * x ∈ L.lattice := by
    intro k x hx
    have := L.lattice.nsmul_mem hx k
    simpa [nsmul_eq_mul] using this
  have hconj : ∀ ω ∈ L.lattice, conj α * ω ∈ L.lattice := by
    intro ω hω
    have hc : conj α = (t : ℂ) - α := by rw [← ht]; ring
    rw [hc, sub_mul]
    refine L.lattice.sub_mem ?_ (hα ω hω)
    have := L.lattice.smul_mem t hω
    simpa [zsmul_eq_mul] using this
  have hnT : ∀ T ∈ S, (n : ℂ) * T ∈ L.lattice := by
    intro T hT
    have h1 := hconj _ (hS.1 T hT).1
    have hn' : (n : ℂ) = conj α * α := by
      rw [mul_comm, Complex.mul_conj, hnorm]
      simp
    rw [hn', mul_assoc]
    exact h1
  have hs2' : (α ^ 2 - (n : ℂ)) * s2 L = ∑ T ∈ S, L.weierstrassP T := by
    rw [← hs2, hnorm]
    simp
  have hnc : (n : ℂ) = (S.card : ℂ) + 1 := by exact_mod_cast hcardn.symm
  have key : ((M * n : ℕ) : ℂ) ^ 2 * ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2)
      - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2))
      = ∑ T ∈ S, ((M * n : ℕ) : ℂ) ^ 2 * (L.weierstrassP T - L.weierstrassP P) / Ω ^ 2 := by
    have e1 : ∑ T ∈ S, ((M * n : ℕ) : ℂ) ^ 2 * (L.weierstrassP T - L.weierstrassP P) / Ω ^ 2
        = ((M * n : ℕ) : ℂ) ^ 2 * (∑ T ∈ S, L.weierstrassP T - (S.card : ℂ) * L.weierstrassP P) / Ω ^ 2 := by
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [e1, ← hs2']
    rw [show (α ^ 2 - (n : ℂ)) * ((s2 L + L.weierstrassP P) / Ω ^ 2) - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2)
        = ((α ^ 2 - (n : ℂ)) * s2 L + (1 - (n : ℂ)) * L.weierstrassP P) / Ω ^ 2 by ring]
    rw [hnc]
    ring
  rw [key]
  refine IsIntegral.sum _ (fun T hT => ?_)
  refine hVL T P (hS.1 T hT).2 hP ?_ ?_
  · have h := hnat M _ (hnT T hT)
    rw [show ((M * n : ℕ) : ℂ) * T = (M : ℂ) * ((n : ℂ) * T) by push_cast; ring]
    exact h
  · have h := hnat n _ hMP
    rw [show ((M * n : ℕ) : ℂ) * P = (n : ℂ) * ((M : ℂ) * P) by push_cast; ring]
    exact h

end GlobalTheory.IsogFormula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFormulaWeierstrassPIntegralStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_formula_weierstrassP_integral : ∀ (L : PeriodPair) (α β Ω P : ℂ) (M n : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → MulStable L α → Complex.normSq α = n → 0 < n → 0 < M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (((M * n : ℕ) : ℂ) ^ 2 * ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2))) := by
  first | exact @GlobalTheory.IsogFormula.main | exact GlobalTheory.IsogFormula.main | (intros; apply GlobalTheory.IsogFormula.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundMultiplierSqrtNegD
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundMultiplierSqrtNegD
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzMult

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (σ p : ℂ), d.Prime → 4 < d → l ≠ d → Sz l lam 0 (12 * p) → Sz l lam 0 (-2 * (d : ℂ) * σ + ((d : ℂ) + 1) * p) → (l = 3 → d % 3 = 2) → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else 0) σ := by
  intro l _ lam d σ p hd hd4 hld hA hB h3
  have hlp : l.Prime := Fact.out
  obtain ⟨hint, -, hmul, hmono, -, hl, -⟩ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam
  obtain ⟨-, hadd2, -, -, hZ, -⟩ := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hne : ∀ n : ℕ, ¬ l ∣ n → (n : ℂ) ≠ 0 := by
    intro n hn h
    apply hn
    rw [Nat.cast_eq_zero.mp h]
    exact dvd_zero l
  have hinv : ∀ n : ℕ, ¬ l ∣ n → Sz l lam 0 ((n : ℂ)⁻¹) := by
    intro n hn
    apply hint n _ hn
    rw [mul_inv_cancel₀ (hne n hn)]
    exact isIntegral_one
  have hnat : ∀ n : ℕ, Sz l lam 0 (n : ℂ) := fun n => by exact_mod_cast hZ n
  have hm0 : ∀ (r : ℝ) (x y : ℂ), Sz l lam 0 x → Sz l lam r y → Sz l lam r (x * y) := by
    intro r x y hx hy
    simpa using hmul 0 r x y hx hy
  have hcancel : ∀ (r : ℝ) (n : ℕ) (x : ℂ), ¬ l ∣ n → Sz l lam r ((n : ℂ) * x) → Sz l lam r x := by
    intro r n x hn h
    have := hm0 r _ _ (hinv n hn) h
    rwa [← mul_assoc, inv_mul_cancel₀ (hne n hn), one_mul] at this
  have hkey : ∀ r : ℝ, 0 ≤ r → Sz l lam r (((d : ℂ) + 1) * p) → Sz l lam r (((2 * d : ℕ) : ℂ) * σ) := by
    intro r hr h
    have hB' := hmono 0 r _ hr hB
    have := (hadd2 r _ _ h hB').2
    convert this using 1
    push_cast
    ring
  have hmulk : ∀ (r : ℝ) (m k : ℕ), d + 1 = m * k → Sz l lam r ((m : ℂ) * p) → Sz l lam r (((d : ℂ) + 1) * p) := by
    intro r m k hk h
    have := hm0 r (k : ℂ) _ (hnat k) h
    have e : ((d : ℂ) + 1) = (m : ℂ) * k := by exact_mod_cast hk
    rw [e]
    convert this using 1
    ring
  by_cases h2 : l = 2
  · subst h2
    have hd2 : ¬ 2 ∣ d := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hd).mp h
      omega
    have h4p : Sz 2 lam 0 (((4 : ℕ) : ℂ) * p) := by
      apply hcancel 0 3 _ (by norm_num)
      convert hA using 1
      push_cast
      ring
    rw [if_pos rfl]
    split_ifs with h43
    · obtain ⟨k, hk⟩ : 4 ∣ d + 1 := by omega
      have h1 := hkey 0 le_rfl (hmulk 0 4 k hk h4p)
      have h2s : Sz 2 lam 0 (((2 : ℕ) : ℂ) * σ) := by
        apply hcancel 0 d _ hd2
        convert h1 using 1
        push_cast
        ring
      have := (hl 0 σ).mp h2s
      norm_num at this
      exact this
    · have h2p : Sz 2 lam 1 (((2 : ℕ) : ℂ) * p) := by
        have := (hl 0 (((2 : ℕ) : ℂ) * p)).mp (by convert h4p using 1; push_cast; ring)
        norm_num at this ⊢
        exact this
      obtain ⟨k, hk⟩ : 2 ∣ d + 1 := by omega
      have h1 := hkey 1 zero_le_one (hmulk 1 2 k hk h2p)
      have h2s : Sz 2 lam 1 (((2 : ℕ) : ℂ) * σ) := by
        apply hcancel 1 d _ hd2
        convert h1 using 1
        push_cast
        ring
      have := (hl 1 σ).mp h2s
      norm_num at this
      exact this
  · rw [if_neg h2]
    by_cases h3' : l = 3
    · subst h3'
      have hd3 := h3 rfl
      have h3p : Sz 3 lam 0 (((3 : ℕ) : ℂ) * p) := by
        apply hcancel 0 4 _ (by norm_num)
        convert hA using 1
        push_cast
        ring
      obtain ⟨k, hk⟩ : 3 ∣ d + 1 := by omega
      have h1 := hkey 0 le_rfl (hmulk 0 3 k hk h3p)
      exact hcancel 0 (2 * d) σ (by omega) h1
    · have hl2 : ∀ n : ℕ, n.Prime → l ∣ n → l = n := fun n hn h =>
        (Nat.prime_dvd_prime_iff_eq hlp hn).mp h
      have h12 : ¬ l ∣ 12 := by
        intro h
        rcases (Nat.Prime.dvd_mul hlp).mp (show l ∣ 2 * 2 * 3 from h) with h' | h'
        · rcases (Nat.Prime.dvd_mul hlp).mp h' with h'' | h'' <;>
            exact h2 (hl2 2 Nat.prime_two h'')
        · exact h3' (hl2 3 Nat.prime_three h')
      have h2d : ¬ l ∣ 2 * d := by
        intro h
        rcases (Nat.Prime.dvd_mul hlp).mp h with h' | h'
        · exact h2 (hl2 2 Nat.prime_two h')
        · exact hld (hl2 d hd h')
      have hp : Sz l lam 0 p := by
        apply hcancel 0 12 p h12
        exact_mod_cast hA
      have h1 := hkey 0 le_rfl (hmulk 0 1 (d + 1) (by ring) (by simpa using hp))
      exact hcancel 0 (2 * d) σ h2d h1

end GlobalTheory.SzMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundMultiplierSqrtNegDStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_bound_multiplier_sqrt_neg_d : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (σ p : ℂ), d.Prime → 4 < d → l ≠ d → Sz l lam 0 (12 * p) → Sz l lam 0 (-2 * (d : ℂ) * σ + ((d : ℂ) + 1) * p) → (l = 3 → d % 3 = 2) → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else 0) σ := by
  first | exact @GlobalTheory.SzMult.main | exact GlobalTheory.SzMult.main | (intros; apply GlobalTheory.SzMult.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundThreeInert
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundThreeInert
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.ArithThreeInert

theorem main : ∀ [Fact (Nat.Prime 3)] (lam : algebraicClosure ℚ ℂ →+* ℂ_[3]) (d : ℕ) (w σ p : ℂ), d % 3 = 1 → w ^ 2 = -(d : ℂ) → Sz 3 lam 0 (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz 3 lam 0 (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p) → Sz 3 lam 0 σ := by
  intro _ lam d w σ p hd hw h1 h2
  obtain ⟨hint, hadd, hmul, -, hneg, -, -⟩ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties 3 lam
  have hsub : ∀ x y : ℂ, Sz 3 lam 0 x → Sz 3 lam 0 y → Sz 3 lam 0 (x - y) := by
    intro x y hx hy
    rw [sub_eq_add_neg]; exact hadd 0 x (-y) hx (hneg 0 y hy)
  have hI : ∀ x : ℂ, IsIntegral ℤ x → Sz 3 lam 0 x := by
    intro x hx
    exact hint 1 x (by norm_num) (by simpa using hx)
  have hw_int : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.Monic.def.mpr (by
        rw [Polynomial.leadingCoeff_X_pow_add_C (by norm_num)])
    · simp [hw]
  have hA : Sz 3 lam 0 ((1 + w) ^ 2 - 1) :=
    hI _ (((isIntegral_one.add hw_int).pow 2).sub isIntegral_one)
  have hB : Sz 3 lam 0 ((1 - w) ^ 2 - 1) :=
    hI _ (((isIntegral_one.sub hw_int).pow 2).sub isIntegral_one)
  have hW : Sz 3 lam 0 w := hI _ hw_int
  have hcomb : Sz 3 lam 0 (((((1 - w) ^ 2 - 1) *
      (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p)) -
      (((1 + w) ^ 2 - 1) * (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p))) * w) := by
    have := hmul 0 0 _ _ (hsub _ _ (by simpa using hmul 0 0 _ _ hB h1) (by simpa using hmul 0 0 _ _ hA h2)) hW
    simpa using this
  have heq : ((((1 - w) ^ 2 - 1) *
      (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p)) -
      (((1 + w) ^ 2 - 1) * (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p))) * w
      = ((4 * d ^ 2 : ℕ) : ℂ) * (-σ) := by
    push_cast
    linear_combination (4 * (d : ℂ) * σ) * hw
  rw [heq] at hcomb
  have hd0 : ((4 * d ^ 2 : ℕ) : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; simp at hd
    exact_mod_cast (by positivity : 0 < 4 * d ^ 2).ne'
  have h3 : ¬ 3 ∣ 4 * d ^ 2 := by
    intro h
    have h0 : (4 * d ^ 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.mul_mod, Nat.pow_mod, hd] at h0
    norm_num at h0
  have hinv : Sz 3 lam 0 (((4 * d ^ 2 : ℕ) : ℂ))⁻¹ :=
    hint (4 * d ^ 2) _ h3 (by rw [mul_inv_cancel₀ hd0]; exact isIntegral_one)
  have hm := hmul 0 0 _ _ hinv hcomb
  rw [zero_add] at hm
  have hfin := hneg 0 _ hm
  rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul, neg_neg] at hfin
  exact hfin

end GlobalTheory.ArithThreeInert
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundThreeInertStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_bound_three_inert : ∀ [Fact (Nat.Prime 3)] (lam : algebraicClosure ℚ ℂ →+* ℂ_[3]) (d : ℕ) (w σ p : ℂ), d % 3 = 1 → w ^ 2 = -(d : ℂ) → Sz 3 lam 0 (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz 3 lam 0 (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p) → Sz 3 lam 0 σ := by
  first | exact @GlobalTheory.ArithThreeInert.main | exact GlobalTheory.ArithThreeInert.main | (intros; apply GlobalTheory.ArithThreeInert.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundAtRamifiedPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundAtRamifiedPrime
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzRamified

theorem norm_int_eq_one {l : ℕ} [Fact l.Prime] {z : ℤ} (h : ¬ (l : ℤ) ∣ z) : ‖(z : ℂ_[l])‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] ℂ_[l]) z, norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one z) (not_lt.mp fun h' => h (Padic.norm_intCast_lt_one_iff.mp h'))

theorem norm_bound {l : ℕ} [Fact l.Prime] (W S P : ℂ_[l]) (hl : 4 < l) (hW : W ^ 2 = -(l : ℂ_[l]))
    (hP : ‖12 * P‖ ≤ 1) (hS : ‖((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P‖ ≤ 1) :
    ‖S‖ ≤ (l : ℝ) ^ (1 / 2 : ℝ) := by
  have hpr : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hpr.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]
  have h12 : ‖(12 : ℂ_[l])‖ = 1 := by
    have hd : ¬ (l : ℤ) ∣ 12 := by
      intro h
      have h' : l ∣ 12 := by exact_mod_cast h
      have h4 : l ∣ 2 ^ 2 * 3 := h'
      rcases (Nat.Prime.dvd_mul hpr).1 h4 with h5 | h5
      · have := Nat.le_of_dvd (by norm_num) (hpr.dvd_of_dvd_pow h5); omega
      · have := Nat.le_of_dvd (by norm_num) h5; omega
    simpa using norm_int_eq_one (l := l) hd
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hd : ¬ (l : ℤ) ∣ 2 := by
      intro h
      have := Int.le_of_dvd (by norm_num) h
      omega
    simpa using norm_int_eq_one (l := l) hd
  have hW2 : ‖W‖ ^ 2 = (l : ℝ)⁻¹ := by rw [← norm_pow, hW, norm_neg, hn]
  have hW1 : ‖W‖ < 1 := by
    have : ‖W‖ ^ 2 < 1 := by rw [hW2]; exact inv_lt_one_of_one_lt₀ hl1
    nlinarith [norm_nonneg W]
  have h1W : ‖1 + W‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hW1.ne'), norm_one,
      max_eq_left hW1.le]
  have hP1 : ‖P‖ ≤ 1 := by rwa [norm_mul, h12, one_mul] at hP
  have hB : ‖((1 + W) ^ 2 - 1) * P‖ ≤ 1 := by
    have e : ((1 + W) ^ 2 - 1) * P = W * (2 + W) * P := by ring
    have h2W : ‖2 + W‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2.le hW1.le)
    rw [e, norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ hW1.le (norm_nonneg _) h2W) (norm_nonneg _) hP1
  have hA : ‖W‖ * ‖S‖ ≤ 1 := by
    have e : 2 * W * (1 + W) * S =
        (((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P) + ((1 + W) ^ 2 - 1) * P := by
      linear_combination S * hW
    have := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hS hB)
    rwa [← e, norm_mul, norm_mul, norm_mul, h2, h1W, one_mul, mul_one] at this
  have hsq : ‖S‖ ^ 2 ≤ l := by
    have h3 : (‖W‖ * ‖S‖) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hA
    rw [mul_pow, hW2, inv_mul_le_iff₀ hl0, mul_one] at h3
    exact h3
  rw [← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le hsq

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (w σ p : ℂ), 4 < l → w ^ 2 = -(l : ℂ) → Sz l lam 0 (12 * p) → Sz l lam 0 (((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz l lam (1 / 2) σ := by
  intro l _ lam w σ p hl hw hp hs
  obtain ⟨hp, hp'⟩ := hp
  obtain ⟨hs, hs'⟩ := hs
  rw [Real.rpow_zero] at hp' hs'
  have hlK : (l : ℂ) ∈ algebraicClosure ℚ ℂ := natCast_mem _ l
  have hwK : w ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [← mem_algebraicClosure_iff, hw]
    exact neg_mem hlK
  have hpK : p ∈ algebraicClosure ℚ ℂ := by
    have e : p = (12 * p) / ((12 : ℕ) : ℂ) := by push_cast; ring
    rw [e]
    exact div_mem hp (natCast_mem _ 12)
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hw0 : w ≠ 0 := by
    rintro rfl
    have : (l : ℂ) = 0 := by linear_combination hw
    have h' : l = 0 := by exact_mod_cast this
    omega
  have hw1 : 1 + w ≠ 0 := by
    intro h
    have : ((l + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination hw + (1 - w) * h
    exact Nat.succ_ne_zero l (by exact_mod_cast this)
  have hσK : σ ∈ algebraicClosure ℚ ℂ := by
    have e : σ = ((((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) + ((1 + w) ^ 2 - 1) * p) /
        (((2 : ℕ) : ℂ) * w * (1 + w)) := by
      rw [eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hw0) hw1)]
      push_cast
      linear_combination σ * hw
    have h1 : 1 + w ∈ algebraicClosure ℚ ℂ := add_mem (one_mem _) hwK
    rw [e]
    exact div_mem (add_mem hs (mul_mem (sub_mem (pow_mem h1 2) (one_mem _)) hpK))
      (mul_mem (mul_mem (natCast_mem _ 2) hwK) h1)
  refine ⟨hσK, norm_bound (lam ⟨w, hwK⟩) _ (lam ⟨p, hpK⟩) hl ?_ ?_ ?_⟩
  · have e : (⟨w, hwK⟩ : algebraicClosure ℚ ℂ) ^ 2 = -(l : algebraicClosure ℚ ℂ) := Subtype.ext (by simpa using hw)
    rw [← map_pow, e, map_neg, map_natCast]
  · have e : (⟨12 * p, hp⟩ : algebraicClosure ℚ ℂ) = ((12 : ℕ) : algebraicClosure ℚ ℂ) * ⟨p, hpK⟩ :=
      Subtype.ext (by
        show 12 * p = ((12 : ℕ) : ℂ) * p
        norm_num)
    rw [e, map_mul, map_natCast] at hp'
    exact_mod_cast hp'
  · have e : (⟨_, hs⟩ : algebraicClosure ℚ ℂ) =
        ((1 + ⟨w, hwK⟩) ^ 2 - (1 + (l : algebraicClosure ℚ ℂ))) * ⟨σ, hσK⟩ - ((1 + ⟨w, hwK⟩) ^ 2 - 1) * ⟨p, hpK⟩ :=
      Subtype.ext (by simp)
    rw [e] at hs'
    simpa only [map_sub, map_mul, map_pow, map_add (f := _), map_one, map_natCast] using hs'

end GlobalTheory.SzRamified
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundAtRamifiedPrimeStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicValuation_bound_at_ramified_prime : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (w σ p : ℂ), 4 < l → w ^ 2 = -(l : ℂ) → Sz l lam 0 (12 * p) → Sz l lam 0 (((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz l lam (1 / 2) σ := by
  first | exact @GlobalTheory.SzRamified.main | exact GlobalTheory.SzRamified.main | (intros; apply GlobalTheory.SzRamified.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorBoundWeierstrassCmTorsion
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.CMSize

theorem mulStable_one_add {L : PeriodPair} {w : ℂ} (h : MulStable L w) : MulStable L (1 + w) := by
  intro x hx
  rw [add_mul, one_mul]
  exact add_mem hx (h x hx)

theorem mulStable_one_sub {L : PeriodPair} {w : ℂ} (h : MulStable L w) : MulStable L (1 - w) := by
  intro x hx
  rw [sub_mul, one_mul]
  exact sub_mem hx (h x hx)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (L : PeriodPair) (Ω P : ℂ) (M : ℕ), d.Prime → 4 < d → MulStable L (Complex.I * (Real.sqrt d : ℝ)) → Ω ^ 12 = latDisc L → ¬ l ∣ M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((s2 L + L.weierstrassP P) / Ω ^ 2) := by
  intro l hl lam d L Ω P M hd hd4 hw hΩ hM hP hMP
  have hlp : l.Prime := hl.out
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hM (dvd_zero _))
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hs0 : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.pos
    exact (Real.sqrt_pos.mpr this).ne'
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hwdef
  have hre : w.re = 0 := by simp [hwdef]
  have him : w.im = Real.sqrt d := by simp [hwdef]
  have him0 : w.im ≠ 0 := by rw [him]; exact hs0
  have hw2 : w ^ 2 = -(d : ℂ) := by
    have h1 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
      rw [← Complex.ofReal_mul, hs]; simp
    rw [hwdef, mul_pow, Complex.I_sq, sq, h1]; ring
  have hn0 : Complex.normSq w = (d : ℕ) := by
    rw [Complex.normSq_apply, hre, him, hs]; simp
  have hn1 : Complex.normSq (1 + w) = ((1 + d : ℕ) : ℝ) := by
    rw [Complex.normSq_apply]; simp [hre, him, hs]
  have hn2 : Complex.normSq (1 - w) = ((1 + d : ℕ) : ℝ) := by
    rw [Complex.normSq_apply]; simp [hre, him, hs]
  have hsz := (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1
  have hp : Sz l lam 0 (12 * (L.weierstrassP P / Ω ^ 2)) := by
    refine hsz (M ^ 2) _ (fun h => hM (hlp.dvd_of_dvd_pow h)) ?_
    have := ((GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L w Ω M hw him0 hΩ hM0).1 P hMP).1
    convert this using 1
    push_cast; ring
  have key : ∀ (α : ℂ) (n : ℕ), MulStable L α → Complex.normSq α = n → ¬ l ∣ n →
      Sz l lam 0 ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) -
        (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2)) := by
    intro α n hα hn hln
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hln (dvd_zero _))
    refine hsz ((M * n) ^ 2) _ (fun h => ?_) ?_
    · rcases (Nat.Prime.dvd_mul hlp).1 (hlp.dvd_of_dvd_pow h) with h | h
      · exact hM h
      · exact hln h
    · have := GlobalTheory.T.isogeny_formula_weierstrassP_integral L α w Ω P M n hw him0 hΩ hα hn hn0 hM0 hP hMP
      rwa [Nat.cast_pow]
  by_cases hld : l = d
  · subst hld
    rw [if_neg (by omega), if_pos rfl]
    have hnd : ¬ l ∣ 1 + l := by
      intro h
      have : l ∣ 1 := (Nat.dvd_add_left (dvd_refl l)).1 h
      exact hlp.one_lt.ne' (Nat.dvd_one.1 this)
    have h1 := key (1 + w) (1 + l) (mulStable_one_add hw) hn1 hnd
    refine GlobalTheory.T.algebraicValuation_bound_at_ramified_prime l lam w _ _ hd4 hw2 hp ?_
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  · rw [if_neg hld]
    by_cases h3 : l = 3 ∧ d % 3 = 1
    · obtain ⟨rfl, h3⟩ := h3
      rw [if_neg (by omega)]
      have hnd : ¬ 3 ∣ 1 + d := by omega
      have h1 := key (1 + w) (1 + d) (mulStable_one_add hw) hn1 hnd
      have h2 := key (1 - w) (1 + d) (mulStable_one_sub hw) hn2 hnd
      refine GlobalTheory.T.valuation_bound_three_inert lam d w _ (L.weierstrassP P / Ω ^ 2) h3 hw2 ?_ ?_
      · simpa only [Nat.cast_add, Nat.cast_one] using h1
      · simpa only [Nat.cast_add, Nat.cast_one] using h2
    · have hnd : ¬ l ∣ d := fun h => hld ((Nat.prime_dvd_prime_iff_eq hlp hd).1 h)
      have h1 := key w d hw hn0 hnd
      refine GlobalTheory.T.valuation_bound_multiplier_sqrt_neg_d l lam d _ _ hd hd4 hld hp ?_ ?_
      · convert h1 using 1
        rw [hw2]; ring
      · rintro rfl
        have : ¬ d % 3 = 1 := fun h => h3 ⟨rfl, h⟩
        omega

end GlobalTheory.CMSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorBoundWeierstrassCmTorsionStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_bound_weierstrass_cm_torsion : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (L : PeriodPair) (Ω P : ℂ) (M : ℕ), d.Prime → 4 < d → MulStable L (Complex.I * (Real.sqrt d : ℝ)) → Ω ^ 12 = latDisc L → ¬ l ∣ M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((s2 L + L.weierstrassP P) / Ω ^ 2) := by
  first | exact @GlobalTheory.CMSize.main | exact GlobalTheory.CMSize.main | (intros; apply GlobalTheory.CMSize.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImagQuadIntegerLatticeMulStableISqrt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImagQuadIntegerLatticeMulStableISqrt
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.IntLatMul

theorem main : ∀ (d : ℕ) (Λ : PeriodPair), 0 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    MulStable Λ (Complex.I * (Real.sqrt d : ℝ)) ∧ (Complex.I * (Real.sqrt d : ℝ)).im ≠ 0 := by
  intro d Λ hd hΛ
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hw2 : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hwi : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      algebraMap_int_eq, eq_intCast, Int.cast_natCast, hw2]
    ring
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxi, a, b, hab⟩ := (hΛ x).1 hx
    refine (hΛ _).2 ⟨hwi.mul hxi, -(b * d), a, ?_⟩
    rw [hab]
    push_cast
    linear_combination (b : ℂ) * hw2
  · have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    simp [hw, hs.ne']

end GlobalTheory.IntLatMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImagQuadIntegerLatticeMulStableISqrtStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imagQuadIntegerLattice_mulStable_I_sqrt : ∀ (d : ℕ) (Λ : PeriodPair), 0 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → MulStable Λ (Complex.I * (Real.sqrt d : ℝ)) ∧ (Complex.I * (Real.sqrt d : ℝ)).im ≠ 0 := by
  first | exact @GlobalTheory.IntLatMul.main | exact GlobalTheory.IntLatMul.main | (intros; apply GlobalTheory.IntLatMul.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMulTorsMemLatticeIff
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem nsmul_zmod_eq_zero_iff_dvd (N : ℕ) [NeZero N] (M : ℕ) (a : ZMod N) :
    M • a = 0 ↔ N ∣ M * a.val := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]

theorem natCast_mul_tors_mem_lattice_iff :
    ∀ (N : ℕ) [NeZero N] (τ : ℍ) (M : ℕ) (x : Fin 2 → ZMod N),
      (M : ℂ) * tors N τ x ∈ (tauPair τ).lattice ↔ M • x = 0 := by
  intro N _ τ M x
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hx : M • x = 0 ↔ N ∣ M * (x 0).val ∧ N ∣ M * (x 1).val := by
    rw [← nsmul_zmod_eq_zero_iff_dvd, ← nsmul_zmod_eq_zero_iff_dvd, funext_iff, Fin.forall_fin_two]
    rfl
  have hm : ∀ z : ℂ, z ∈ (tauPair τ).lattice ↔ ∃ m n : ℤ, m * (τ : ℂ) + n = z := by
    intro z
    rw [PeriodPair.mem_lattice]; simp [tauPair]
  rw [hx, hm]
  constructor
  · rintro ⟨m, n, h⟩
    have h1 : ((N * m - M * (x 0).val : ℤ) : ℂ) * (τ : ℂ) + ((N * n - M * (x 1).val : ℤ) : ℂ) = 0 := by
      unfold tors at h
      field_simp at h
      push_cast
      linear_combination h
    have him := congrArg Complex.im h1
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
      Complex.zero_im, UpperHalfPlane.coe_im, mul_eq_zero, τ.im_pos.ne', or_false, Int.cast_eq_zero] at him
    rw [him, Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h1
    constructor
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨m, by push_cast at him ⊢; linear_combination -him⟩
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨n, by push_cast at h1 ⊢; linear_combination -h1⟩
  · rintro ⟨⟨m, hm0⟩, ⟨n, hn0⟩⟩
    refine ⟨m, n, ?_⟩
    have a : (M : ℂ) * ((x 0).val : ℂ) = N * m := by exact_mod_cast hm0
    have b : (M : ℂ) * ((x 1).val : ℂ) = N * n := by exact_mod_cast hn0
    unfold tors
    field_simp
    push_cast
    linear_combination -(τ : ℂ) * a - b

end GlobalTheory.WpFam
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzTau

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), d.Prime → 4 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ Sz l lam 0 (jT τ) ∧ ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N x τ) / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro l hl lam d Λ c Ω τ hd h4 hΛ hτ hΩ
  obtain ⟨hst, him⟩ := GlobalTheory.T.imagQuadIntegerLattice_mulStable_I_sqrt d Λ hd.pos hΛ
  refine ⟨GlobalTheory.QFam.pow_twelve_eq_DD Λ c τ hτ Ω hΩ, ?_, ?_⟩
  · refine (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1 1 (jT τ) hl.out.not_dvd_one ?_
    rw [Nat.cast_one, one_mul]
    exact GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication Λ c τ _ hτ hst him
  · intro N _ M x hM hx hx0
    obtain ⟨h1, h2⟩ := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ c Ω τ hτ
    rw [add_div, h1, (h2 N x).1, ← add_div]
    have hh := (GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ hτ).1
    refine GlobalTheory.T.denominator_bound_weierstrass_cm_torsion l lam d Λ Ω _ M hd h4 hst hΩ hM ?_ ?_
    · rw [hh, (GlobalTheory.WpFam.TorsMem.main N τ).2.2.1 x]
      exact hx0
    · rw [mul_left_comm, hh]
      exact (GlobalTheory.WpFam.natCast_mul_tors_mem_lattice_iff N τ M x).2 hx

end GlobalTheory.SzTau
end

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatValRam GlobalTheory.HilbFam GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsFieldData IsIntLattice c_vp cE_vp a0 delta_vp)
open ReciprocityTheory.ChartRestriction.L1 (IsTauOf DD jT)
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb)
open scoped UpperHalfPlane Classical

namespace GlobalTheory.JetIntElliptic

theorem sz_l (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) :
    Sz l lam (-1) (l : ℂ) ∧ Sz l lam 1 (l : ℂ)⁻¹ := by
  have h : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h1 : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
    rw [h1, norm_algebraMap', Padic.norm_p]
  refine ⟨⟨natCast_mem _ l, ?_⟩, ⟨inv_mem (natCast_mem _ l), ?_⟩⟩
  · have : (⟨(l : ℂ), natCast_mem _ l⟩ : algebraicClosure ℚ ℂ) = (l : algebraicClosure ℚ ℂ) := rfl
    rw [this, map_natCast, h, Real.rpow_neg_one]
  · have : (⟨(l : ℂ)⁻¹, inv_mem (natCast_mem _ l)⟩ : algebraicClosure ℚ ℂ) = (l : algebraicClosure ℚ ℂ)⁻¹ := rfl
    rw [this, map_inv₀, map_natCast, norm_inv, h, inv_inv, Real.rpow_one]

theorem sz_val (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D : ℕ) :
    Sz l lam (-(padicValNat l D : ℝ)) (D : ℂ) := by
  obtain ⟨m, hm⟩ : l ^ padicValNat l D ∣ D := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have h := sz_mul (sz_pow (sz_l l lam).1 (padicValNat l D)) (sz_nat (l := l) (lam := lam) m)
  have h2 : (D : ℂ) = (l : ℂ) ^ padicValNat l D * m := by exact_mod_cast hm
  rw [← h2] at h
  convert h using 1
  ring

theorem c_facts {E : Type} [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (l : ℕ) (hl : l.Prime) :
    delta_vp E l ≤ c_vp 𝔣 l ∧ 0 ≤ c_vp 𝔣 l ∧ ∃ q : ℚ, (q : ℝ) = c_vp 𝔣 l := by
  have h0 : 0 ≤ delta_vp E l := by unfold delta_vp; positivity
  unfold c_vp
  split_ifs with h
  · refine ⟨?_, by positivity, ⟨a0 𝔣 l, by simp⟩⟩
    obtain ⟨v, hv, hvd⟩ := h
    obtain ⟨-, -, l', hl', -, hm, hnd, -⟩ := h𝔣.2.2 v hvd
    have hll : l' = l := by
      by_contra hne
      have hc : IsCoprime (l' : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hl' hl).2 hne)
      obtain ⟨a, b, hab⟩ := hc
      have h1 : (1 : OF E) = (a : OF E) * (l' : OF E) + (b : OF E) * (l : OF E) := by exact_mod_cast hab.symm
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (h1 ▸ add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hv)))
    subst hll
    have : delta_vp E l' = 0 := by
      unfold delta_vp
      rw [padicValInt.eq_zero_of_not_dvd hnd]; simp
    rw [this]; positivity
  · exact ⟨le_rfl, h0, ⟨(padicValInt l (discr E) : ℚ) / (Module.finrank ℚ E : ℚ), by unfold delta_vp; push_cast; rfl⟩⟩

theorem theta_facts {E : Type} [Field E] [NumberField E] [IsCMField E] (ψ : E →+* ℂ) (d : ℕ) (w θ : E) (hw : w ^ 2 = -(d : E))
    (hψ : ψ w = Complex.I * (Real.sqrt d : ℝ)) (hθ : θ = (if d % 4 = 3 then (-1 + w) / 2 else w)) :
    IsIntegral ℤ θ ∧ (θ - IsCMField.complexConj E θ) ^ 2 = -(((if d % 4 = 3 then d else 4 * d : ℕ) : ℕ) : E) := by
  have hc : IsCMField.complexConj E w = -w := by
    apply ψ.injective
    rw [IsCMField.complexEmbedding_complexConj, map_neg, hψ]
    simp
  split_ifs at hθ ⊢ with h
  · subst hθ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
    have hm' : (d : E) + 1 = 4 * m := by exact_mod_cast hm
    refine ⟨⟨Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (m : ℤ), by monicity!, ?_⟩, ?_⟩
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      simp only [eq_intCast, Int.cast_natCast, algebraMap_int_eq]
      linear_combination (1 / 4 : E) * hw - (1 / 4 : E) * hm'
    · rw [map_div₀, map_add (f := _), map_neg, map_one, hc, map_ofNat]
      linear_combination hw
  · subst hθ
    refine ⟨⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩, ?_⟩
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      simp only [eq_intCast, Int.cast_natCast, algebraMap_int_eq]
      linear_combination hw
    · rw [hc]; push_cast
      linear_combination 4 * hw

theorem tors_ex (N M₀ : ℕ) (hN : 0 < N) (h1 : 1 < M₀) (hd : M₀ ∣ N) : ∃ y : Fin 2 → ZMod N, M₀ • y = 0 ∧ y ≠ 0 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 0 < k := Nat.pos_of_mul_pos_left hN
  refine ⟨fun _ => (k : ZMod (M₀ * k)), funext fun i => ?_, fun h => ?_⟩
  · simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
    rw [← Nat.cast_mul, ZMod.natCast_self]
  · have h0 : ((k : ℕ) : ZMod (M₀ * k)) = 0 := congrFun h 0
    have := Nat.le_of_dvd hk ((ZMod.natCast_eq_zero_iff _ _).1 h0)
    nlinarith

theorem val_facts (l d : ℕ) (hl : l.Prime) (hd : d.Prime) (h4 : 4 < d) :
    (padicValNat l (if d % 4 = 3 then d else 4 * d) : ℝ) / 2 =
      (if l = d then 1 / 2 else 0) + (if l = 2 ∧ ¬ d % 4 = 3 then 1 else 0) := by
  haveI := Fact.mk hl
  haveI := Fact.mk hd
  have h1 : padicValNat l d = if l = d then 1 else 0 := by
    rw [Nat.padicValNat_def]
    split_ifs with h
    · subst h; exact Nat.Prime.multiplicity_self
    · exact multiplicity_primes h
  have h2 : padicValNat l 4 = if l = 2 then 2 else 0 := by
    rw [Nat.padicValNat_def]
    split_ifs with h
    · subst h; exact Nat.multiplicity_prime_pow 2
    · refine multiplicity_eq_zero_of_not_dvd fun hh => h ?_
      exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow (n := 2) hh)
  by_cases h3 : d % 4 = 3
  · simp only [h3, if_true, h1, not_true, and_false, if_false]
    split_ifs <;> norm_num
  · simp only [h3, if_false, not_false_iff, and_true]
    rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by norm_num) hd.ne_zero, h1, h2]
    split_ifs <;> norm_num

theorem fin_id (jt Ω p n lp γ pi im r : ℂ) (t f K : ℕ) (hΩ : Ω ≠ 0) (hp : p ≠ 0) (hlp : lp ≠ 0) (hpi : pi ≠ 0) (him : im ≠ 0)
    (hr : r ≠ 0) :
    n ^ (t * f) * jt * ((2 * pi / r * γ / (Ω / lp) / (Ω / lp)) ^ K / ((Ω / lp) ^ t) ^ f) =
      jt * (pi / im) ^ K / p ^ (t * f + 2 * K) / (Ω * 1 / p) ^ (t * f + 2 * K) * (n * lp) ^ (t * f) *
        (2 * im / r * γ * lp ^ 2) ^ K := by
  have h1 : 2 * pi / r * γ / (Ω / lp) / (Ω / lp) = (pi / im) * (2 * im / r * γ * lp ^ 2) / Ω ^ 2 := by field_simp
  have h2 : ∀ x : ℂ, x / p ^ (t * f + 2 * K) / (Ω * 1 / p) ^ (t * f + 2 * K) = x / Ω ^ (t * f + 2 * K) := fun x => by
    rw [div_div, ← mul_pow]; congr 2; field_simp
  rw [h1, h2, ← pow_mul, div_pow, div_pow Ω, mul_pow (pi / im), mul_pow n, pow_add, pow_mul Ω 2]
  field_simp

theorem core (hjsz : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → ω ≠ 0 → Sz l lam ρ ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2) → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ / ω ^ wt (2 * s) κ)) : EisExp → JetInt := by
  intro hEis E _ _ _ _ I _ d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ lam Ω hΩ
  obtain ⟨w, θ, τ, hw, hφw, hθ, hφθ, htau, him⟩ := GlobalTheory.QuadGenerator.exists_generator E I d φ Λ hF hΛ
  have hδ2 := GlobalTheory.RootDiscrExp.half_le_delta_two_vp E I d φ hF
  obtain ⟨hd, h4, hUn, -, -, hI2, hCM, -⟩ := hF
  have hcard := card_eq_finrank hCM
  have hf2 : 2 ≤ Module.finrank ℚ (FR E) := hcard ▸ hI2
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨hint, hsq⟩ := theta_facts (φ i₀) d w θ hw (hφw i₀) hθ
  have hvD := val_facts l d hl hd h4
  set D : ℕ := if d % 4 = 3 then d else 4 * d with hDdef
  have hD0 : 0 < D := by rw [hDdef]; split_ifs <;> omega
  obtain ⟨M₀, hM₀1, hM₀⟩ : ∃ M₀ : ℕ, 1 < M₀ ∧ ¬ l ∣ M₀ :=
    ⟨l + 1, by have := hl.pos; omega, fun h => hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right dvd_rfl).1 h))⟩
  obtain ⟨M, M', L, hM, hM', hMM, hL, hLm, hLs, hNs⟩ :=
    GlobalTheory.RoadE.passl E l lam 𝔣 Q y θ D M₀ h𝔣 hQl hy hD0 hint hsq hM₀
  have hMpos : 0 < M := Nat.pos_of_ne_zero fun h => hM (h ▸ dvd_zero l)
  have hM'pos : 0 < M' := Nat.pos_of_ne_zero fun h => hM' (h ▸ dvd_zero l)
  have hNpos : 0 < M' * l ^ (padicValNat l D + a0 𝔣 l) := Nat.mul_pos hM'pos (pow_pos hl.pos _)
  haveI : NeZero (M' * l ^ (padicValNat l D + a0 𝔣 l)) := ⟨hNpos.ne'⟩
  obtain ⟨t, ht, ht0⟩ := tors_ex _ M₀ hNpos hM₀1 (hMM.mul_right _)
  obtain ⟨hδc, hc0, q, hq⟩ := c_facts 𝔣 h𝔣 l hl
  have hdF := (GlobalTheory.DiscrTower.padicValInt_discr_div_le_delta_vp E l hl).trans hδc
  obtain ⟨γ, hγ0, hγ, hγ'⟩ := GlobalTheory.QFam.exists_sz_scale l lam (q + if l = d then 1 / 2 else 0)
  have hqh : ((q + if l = d then 1 / 2 else 0 : ℚ) : ℝ) = c_vp 𝔣 l + if l = d then 1 / 2 else 0 := by
    rw [← hq]; split_ifs <;> push_cast <;> ring
  rw [hqh] at hγ hγ'
  have hΩ0 : Ω ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ (by rw [← hΩ]; simp)
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd.pos)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have him0 : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hlp : (l : ℂ) ^ a0 𝔣 l ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  refine ⟨fun _ => Ω / (l : ℂ) ^ a0 𝔣 l, fun _ => 2 * Real.pi / (Real.sqrt d : ℝ) * γ / (Ω / (l : ℂ) ^ a0 𝔣 l), fun i => ?_,
    fun g κ u hg hu => ?_⟩
  · refine ⟨div_ne_zero hΩ0 hlp, div_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero hpi) hsd) hγ0)
      (div_ne_zero hΩ0 hlp), ?_, ?_⟩
    · have h1 : Ω / (l : ℂ) ^ a0 𝔣 l / Ω = ((l : ℂ)⁻¹) ^ a0 𝔣 l := by rw [inv_pow]; field_simp
      rw [h1]
      simpa using sz_pow (sz_l l lam).2 (a0 𝔣 l)
    · have h1 : Ω / (l : ℂ) ^ a0 𝔣 l * (2 * Real.pi / (Real.sqrt d : ℝ) * γ / (Ω / (l : ℂ) ^ a0 𝔣 l)) * (Real.sqrt d : ℝ) /
          (2 * Real.pi) = γ := by field_simp
      beta_reduce
      rw [h1]
      exact hγ'
  · obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_cmType_realEmbeddings E I φ hCM
    have hD := GlobalTheory.HilbFam.iterD_defSum_eq_jet hEis E I φ e θ τ _ L (M * D) s _ g κ u hf2 hs hNpos hL he hφθ
      (Nat.mul_pos hMpos hD0) hLm hg hu
    obtain ⟨hω, hj, hst⟩ := GlobalTheory.SzTau.main l lam d Λ 1 Ω τ hd h4 hΛ htau hΩ
    haveI : IsGalois ℚ (FR E) := (IsAbelianGalois.tower_bot ℚ (FR E) E).toIsGalois
    have hfpos : (0 : ℝ) < Module.finrank ℚ (FR E) := by exact_mod_cast (by omega : 0 < Module.finrank ℚ (FR E))
    have ha0 : (0 : ℝ) ≤ a0 𝔣 l := Nat.cast_nonneg _
    have hv0 : (0 : ℝ) ≤ padicValNat l D := Nat.cast_nonneg _
    have hJ := hjsz hEis (FR E) hf2 s _ L hs hL z hz l lam (fun j => κ (e.symm j)) t M' M₀ (padicValNat l D + a0 𝔣 l)
      (cE_vp l z) (-(padicValNat l D : ℝ) / 2) (2 * c_vp 𝔣 l + 2 * a0 𝔣 l + (padicValNat l D : ℝ) / 2) (Nat.cast_nonneg _)
      (fun C => by
        have h1 : (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat ≤ cE_vp l z :=
          Finset.le_sup (f := fun C => (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat)
            (Finset.mem_univ C)
        have h2 := (Int.self_le_toNat (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)))).trans
          (Int.ofNat_le.2 h1)
        exact_mod_cast h2)
      hM' hL.1 hLs hNs (by push_cast; linarith) (by positivity) hM₀ ht ht0 τ _ hj hω
      (div_ne_zero (by simpa using hΩ0) hp)
      (sz_mono (hst _ M₀ t hM₀ ht ht0) (by
        rw [hvD]
        by_cases h2 : l = 2
        · have hc2 : (1 / 2 : ℝ) ≤ c_vp 𝔣 l := by subst h2; exact hδ2.trans hδc
          have hld : ¬ l = d := by omega
          simp only [h2, if_true, true_and] at hld ⊢
          rw [← h2]
          split_ifs <;> linarith
        · simp only [h2, if_false, false_and]
          split_ifs <;> linarith))
    have hsum : ∑ j, κ (e.symm j) = ∑ i, κ i := Equiv.sum_comp e.symm κ
    have hr : Sz l lam (-(if l = 2 ∧ ¬ d % 4 = 3 then 1 else 0)) (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) := by
      rcases him with ⟨h3, h⟩ | ⟨h3, h⟩
      · have : (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) = 1 := by rw [h]; push_cast; field_simp
        rw [this]; simpa [h3] using sz_one (l := l) (lam := lam)
      · have : (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) = ((2 : ℕ) : ℂ) := by rw [h]; push_cast; field_simp
        rw [this]
        split_ifs with h5
        · obtain ⟨rfl, -⟩ := h5; exact (sz_l 2 lam).1
        · simpa using sz_nat (l := l) (lam := lam) 2
    have hn : Sz l lam (0 + -(padicValNat l D : ℝ)) ((M * D : ℕ) : ℂ) := by
      rw [Nat.cast_mul]; exact sz_mul (sz_nat M) (sz_val l lam D)
    have hlps := sz_pow (sz_l l lam).1 (a0 𝔣 l)
    have hall := sz_mul (sz_mul hJ (sz_pow (sz_mul hn hlps) (2 * s * Module.finrank ℚ (FR E))))
      (sz_pow (sz_mul (sz_mul hr hγ) (sz_pow hlps 2)) (∑ i, κ i))
    beta_reduce
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, hcard]
    have hD' : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 = _ := hD
    rw [hD', fin_id _ Ω (2 * Real.pi * Complex.I) _ _ γ _ (τ.im : ℝ) _ (2 * s) _ _ hΩ0 hp hlp hpi him0 hsd]
    rw [wt, hsum, Complex.ofReal_div] at hall
    refine sz_mono hall ?_
    have hdF' : (padicValInt l (discr (FR E)) : ℝ) ≤ c_vp 𝔣 l * Module.finrank ℚ (FR E) := (div_le_iff₀ hfpos).1 hdF
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have h6 := mul_le_mul_of_nonneg_left hdF' hs0
    have h7 : 0 ≤ (s : ℝ) * (c_vp 𝔣 l * Module.finrank ℚ (FR E)) := by positivity
    have h8 : (if l = 2 ∧ ¬ d % 4 = 3 then (1 : ℝ) else 0) = (padicValNat l D : ℝ) / 2 - (if l = d then 1 / 2 else 0) := by
      rw [hvD]; ring
    rw [h8]
    push_cast
    nlinarith

theorem jetInt : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatJet.JetInt := fun _ hPZ _ _ =>
  core GlobalTheory.HilbFam.sz_jet_conj (GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson (GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ) hPZ)

end GlobalTheory.JetIntElliptic
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLatticeDividedPowerJetIntegrality_of_ellipticCM : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatJet.JetInt := by
  first | exact @GlobalTheory.JetIntElliptic.jetInt | exact GlobalTheory.JetIntElliptic.jetInt | (intros; apply GlobalTheory.JetIntElliptic.jetInt <;> assumption)
