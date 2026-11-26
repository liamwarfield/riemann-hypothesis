module

public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBound
public import Development.WeilBound.CoreStatements.FlagImmersions.DegLApply
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RemainderTermSummable
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.RestTermBoundConvergent
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem rest_bound (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (k : ℕ) (Q : RP Ψ N) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (p : ℕ) (fr : ℕ → Ψ ⊕ Ψ), 2 ≤ p →
      |restTerm j p fr k Q| ≤ c * Real.log p / (p : ℝ) ^ 2 := by
  set M : ℝ := ∑ σ : Ψ ⊕ Ψ, |degFl (pLie j (k - 1) σ * Q)| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hMle : ∀ σ, |degFl (pLie j (k - 1) σ * Q)| ≤ M := fun σ =>
    Finset.single_le_sum (f := fun σ => |degFl (pLie j (k - 1) σ * Q)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ)
  refine ⟨2 * k * M, by positivity, fun p fr hp => ?_⟩
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  unfold restTerm
  split_ifs with hk
  · set r : ℝ := ((p : ℝ) ^ k)⁻¹ with hr
    have hr0 : 0 ≤ r := by positivity
    have hpk : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hk
    have hp4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have hr1 : r ≤ ((p : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hpk
    have hr2 : r ≤ 1 / 2 := by
      refine hr1.trans ?_
      rw [one_div]
      exact inv_anti₀ (by norm_num) (by linarith)
    have hs : HasSum (fun n : ℕ => (r * M) * (1 / 2 : ℝ) ^ n) ((r * M) * 2) :=
      hasSum_geometric_two.mul_left _
    have hb : ‖∑' n : ℕ, r ^ (n + 1) * degFl (pLie j (k - 1) (fr n) * Q)‖ ≤ (r * M) * 2 := by
      refine tsum_of_norm_bounded hs fun n => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ (n + 1)), pow_succ]
      have h1 : r ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ hr0 hr2 n
      calc r ^ n * r * |degFl (pLie j (k - 1) (fr n) * Q)| ≤ (1 / 2 : ℝ) ^ n * r * M := by
            gcongr
            exact hMle _
        _ = _ := by ring
    rw [Real.norm_eq_abs] at hb
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.log p * (k : ℝ))]
    calc Real.log p * (k : ℝ) * |∑' n : ℕ, r ^ (n + 1) * degFl (pLie j (k - 1) (fr n) * Q)|
        ≤ Real.log p * (k : ℝ) * ((((p : ℝ) ^ 2)⁻¹ * M) * 2) := by
          gcongr
          refine hb.trans ?_
          gcongr
      _ = _ := by ring
  · rw [abs_zero]
    positivity

theorem summable_log_div_sq : Summable fun p : ℕ => Real.log p / (p : ℝ) ^ 2 := by
  have h : Summable fun p : ℕ => 2 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun p => div_nonneg (Real.log_natCast_nonneg p) (by positivity))
    (fun p => ?_) h
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 := Real.log_le_rpow_div hp'.le (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : (p : ℝ) ^ 2 = (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hp']
    norm_num
  have h3 : 0 < (p : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have h4 : 0 < (p : ℝ) ^ (3 / 2 : ℝ) := by positivity
  rw [h2, div_le_iff₀ (by positivity)]
  refine h1.trans (le_of_eq ?_)
  field_simp

theorem rest_term_bound_convergent : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), (∃ c : ℝ, ∀ p : ℕ, 2 ≤ p → |restTerm j p (frob p τ) k Q| ≤ c * Real.log p / (p : ℝ) ^ 2) ∧ ∀ B₀ : ℕ, Tendsto (fun B : ℕ => ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ bad), restTerm j p (frob p τ) k Q) atTop (𝓝 (restSum j bad frob B₀ τ k Q)) := by
  intro Ψ _ _ N j bad frob τ k Q
  obtain ⟨c, hc0, hc⟩ := rest_bound Ψ N j k Q
  refine ⟨⟨c, fun p hp => hc p _ hp⟩, fun B₀ => ?_⟩
  have hs : Summable fun p : ℕ =>
      if p.Prime ∧ B₀ < p ∧ p ∉ bad then restTerm j p (frob p τ) k Q else 0 := by
    refine Summable.of_norm_bounded (summable_log_div_sq.mul_left c) fun p => ?_
    split_ifs with h
    · rw [Real.norm_eq_abs, ← mul_div_assoc]
      exact hc p _ h.1.two_le
    · rw [norm_zero]
      exact mul_nonneg hc0 (div_nonneg (Real.log_natCast_nonneg p) (by positivity))
  have ht := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine ht.congr fun B => ?_
  simp only [Function.comp_apply]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h3, by omega⟩, h2, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by omega, h3, h1, h4⟩

end RootFieldNumerics
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RemainderTermSummable
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem restTerm_bound_and_tendsto : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), (∃ c : ℝ, ∀ p : ℕ, 2 ≤ p → |restTerm j p (frob p τ) k Q| ≤ c * Real.log p / (p : ℝ) ^ 2) ∧ ∀ B₀ : ℕ, Tendsto (fun B : ℕ => ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ bad), restTerm j p (frob p τ) k Q) atTop (𝓝 (restSum j bad frob B₀ τ k Q)) :=
  @RootFieldNumerics.rest_term_bound_convergent

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RemainderTermSummableStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.remainder_term_summable : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), (∃ c : ℝ, ∀ p : ℕ, 2 ≤ p → |restTerm j p (frob p τ) k Q| ≤ c * Real.log p / (p : ℝ) ^ 2) ∧ ∀ B₀ : ℕ, Tendsto (fun B : ℕ => ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ bad), restTerm j p (frob p τ) k Q) atTop (𝓝 (restSum j bad frob B₀ τ k Q)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.restTerm_bound_and_tendsto | exact GlobalTheory.CompanionTheory.Ar.Top.restTerm_bound_and_tendsto | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.restTerm_bound_and_tendsto <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ConstantsMonomialApproximation
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ConstantsMonomialApproximation
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section ChartForms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem isMultiHomog_chartMonomial (d : ∀ k, ι k) :
    IsMultiHomog (∏ k, X ⟨k, d k⟩ : MRing ι ℤ) (fun _ => 1) := by
  have h := IsWeightedHomogeneous.prod (R := ℤ) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, d k⟩ : MRing ι ℤ)) (fun k => blockWeight ι ⟨k, d k⟩)
    (fun k _ => isWeightedHomogeneous_X ℤ _ _)
  have e : (∑ k, blockWeight ι ⟨k, d k⟩) = fun _ : K => 1 := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h

theorem isMultiHomog_mul_const {f g : MRing ι ℤ} {a b : ℕ}
    (hf : IsMultiHomog f (fun _ => a)) (hg : IsMultiHomog g (fun _ => b)) :
    IsMultiHomog (f * g) (fun _ => a + b) :=
  IsWeightedHomogeneous.mul hf hg

theorem isMultiHomog_pow_const {f : MRing ι ℤ} (hf : IsMultiHomog f (fun _ => 1)) (n : ℕ) :
    IsMultiHomog (f ^ n) (fun _ => n) := by
  induction n with
  | zero => rw [pow_zero]; exact isWeightedHomogeneous_one ℤ (blockWeight ι)
  | succ n ih => rw [pow_succ]; exact isMultiHomog_mul_const ih hf

theorem pointConeMap_chartMonomial (y : (Σ k, ι k) → Ω) (d : ∀ k, ι k) :
    pointConeMap ℤ y (∏ k, X ⟨k, d k⟩ : MRing ι ℤ) =
      C (segreVec y d) * ∏ k : K, (X k : MvPolynomial K Ω) := by
  simp [pointConeMap, segreVec, Finset.prod_mul_distrib, map_prod]

theorem exists_form_of_mem_chart (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hs : segreVec y c ≠ 0)
    {r : Ω} (hr : r ∈ chartRing ℤ (segreVec y) c) :
    ∃ (n : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => n) ∧
      pointConeMap ℤ y G = C (r * segreVec y c ^ n) * (∏ k : K, (X k : MvPolynomial K Ω)) ^ n := by
  set T : MvPolynomial K Ω := ∏ k : K, (X k : MvPolynomial K Ω) with hT
  set s : Ω := segreVec y c with hsdef
  set M : MRing ι ℤ := ∏ k, X ⟨k, c k⟩ with hM
  have hMh : IsMultiHomog M (fun _ => 1) := isMultiHomog_chartMonomial c
  have hMc : pointConeMap ℤ y M = C s * T := pointConeMap_chartMonomial y c
  unfold chartRing at hr
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    refine ⟨1, ∏ k, X ⟨k, d k⟩, isMultiHomog_chartMonomial d, ?_⟩
    rw [pointConeMap_chartMonomial, pow_one, pow_one, div_mul_cancel₀ _ hs]
  | algebraMap z =>
    refine ⟨0, C z, ?_, ?_⟩
    · exact isWeightedHomogeneous_C (blockWeight ι) z
    · have h1 : (C z : MRing ι ℤ) = algebraMap ℤ (MRing ι ℤ) z := rfl
      rw [h1, AlgHom.commutes]
      simp [MvPolynomial.algebraMap_eq]
  | add u v _ _ hu hv =>
    obtain ⟨a, F, hF, hFc⟩ := hu
    obtain ⟨b, G, hG, hGc⟩ := hv
    refine ⟨a + b, F * M ^ b + G * M ^ a, ?_, ?_⟩
    · have h1 := isMultiHomog_mul_const hF (isMultiHomog_pow_const hMh b)
      have h2 := isMultiHomog_mul_const hG (isMultiHomog_pow_const hMh a)
      rw [add_comm b a] at h2
      exact IsWeightedHomogeneous.add h1 h2
    · simp only [map_add (f := _), map_mul, map_pow, hFc, hGc, hMc]
      ring
  | mul u v _ _ hu hv =>
    obtain ⟨a, F, hF, hFc⟩ := hu
    obtain ⟨b, G, hG, hGc⟩ := hv
    refine ⟨a + b, F * G, isMultiHomog_mul_const hF hG, ?_⟩
    simp only [map_mul, map_pow, hFc, hGc]
    ring

theorem pointConeMap_map_int (A : Type) [CommRing A] [Algebra A Ω] (y : (Σ k, ι k) → Ω) (G : MRing ι ℤ) :
    pointConeMap A y (MvPolynomial.map (Int.castRingHom A) G) = pointConeMap ℤ y G := by
  induction G using MvPolynomial.induction_on with
  | C z => simp [pointConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.map_X]; simp [pointConeMap]

end ChartForms

theorem const_mul_chartMonomial_pow_form : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (c : ∀ k, ι k) (a : A), ∃ (n : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - (MvPolynomial.map (Int.castRingHom A) G) ∈ pointIdeal A y := by
  intro K _ _ ι _ Ω _ y A _ _ hA c a
  by_cases hs : segreVec y c = 0
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hs
    refine ⟨1, 0, isWeightedHomogeneous_zero ℤ _ _, ?_⟩
    have hX : (X ⟨k, c k⟩ : MRing ι A) ∈ pointIdeal A y := by
      simp [pointIdeal, RingHom.mem_ker, pointConeMap, hk]
    rw [map_zero, sub_zero, pow_one]
    exact Ideal.mul_mem_left _ _
      (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem (fun k => (X ⟨k, c k⟩ : MRing ι A)) (Finset.mem_univ k)) hX)
  · obtain ⟨n, G, hG, hGc⟩ := exists_form_of_mem_chart y c hs (hA c hs a)
    refine ⟨n, G, hG, ?_⟩
    rw [pointIdeal, RingHom.mem_ker, map_sub, pointConeMap_map_int, hGc, map_mul, map_pow]
    have hM : pointConeMap A y (∏ k, X ⟨k, c k⟩ : MRing ι A) =
        C (segreVec y c) * ∏ k : K, (X k : MvPolynomial K Ω) := by
      simp [pointConeMap, segreVec, Finset.prod_mul_distrib, map_prod]
    have hC : pointConeMap A y (C a : MRing ι A) = C (algebraMap A Ω a) := by
      simp [pointConeMap, MvPolynomial.algebraMap_eq]
    rw [hM, hC, mul_pow, ← C_pow, C_mul]
    ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ConstantsMonomialApproximationStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constants_monomial_approximation : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (c : ∀ k, ι k) (a : A), ∃ (n : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - (MvPolynomial.map (Int.castRingHom A) G) ∈ pointIdeal A y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.const_mul_chartMonomial_pow_form | exact GlobalTheory.CompanionTheory.Ar.Num.const_mul_chartMonomial_pow_form | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.const_mul_chartMonomial_pow_form <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AntisymmetricPerturbationBound
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AntisymmetricPerturbationBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
open RootFieldNumerics

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem inv_linear_eval (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (l : MvPolynomial (Ψ × Fin N) ℝ)
    (hl : l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j) :
    ∃ a b : Ψ → ℝ, ∀ x : Ψ × Fin N → ℝ, eval x l =
      ∑ τ, (a τ - b τ) * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), x (τ, i) +
        ∑ τ, b τ * ∑ i, x (τ, i) := by
  obtain ⟨h1, h2⟩ := hl
  rw [homogeneousSubmodule_one_eq_span_X] at h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 h1
  have hcoef : ∀ p, l.coeff (Finsupp.single p 1) = c p := by
    intro p
    rw [← hc, coeff_sum, Finset.sum_eq_single p]
    · simp
    · intro q _ hq
      rw [coeff_smul, coeff_X, if_neg, smul_zero]
      intro h
      exact hq (Finsupp.single_left_injective one_ne_zero h)
    · simp
  have hinv : ∀ τ (i k : Fin N), ((i : ℕ) < j ↔ (k : ℕ) < j) → c (τ, i) = c (τ, k) := by
    intro τ i k hik
    have hmem : Equiv.swap (τ, i) (τ, k) ∈ GroundTheory.Heights₂.Heights.antisymWeyl Ψ N j := by
      intro p
      rw [Equiv.swap_apply_def]
      split_ifs with e1 e2
      · subst e1
        exact ⟨rfl, hik.symm⟩
      · subst e2
        exact ⟨rfl, hik⟩
      · exact ⟨rfl, Iff.rfl⟩
    have h3 := coeff_rename_mapDomain _ (Equiv.swap (τ, i) (τ, k)).injective l (Finsupp.single (τ, i) 1)
    rw [h2 _ hmem, Finsupp.mapDomain_single, Equiv.swap_apply_left, hcoef, hcoef] at h3
    exact h3.symm
  have ha : ∀ τ, ∃ a : ℝ, ∀ i : Fin N, (i : ℕ) < j → c (τ, i) = a := by
    intro τ
    by_cases h : ∃ i : Fin N, (i : ℕ) < j
    · obtain ⟨i, hi⟩ := h
      exact ⟨c (τ, i), fun k hk => hinv τ k i (by simp [hi, hk])⟩
    · exact ⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩
  have hb : ∀ τ, ∃ b : ℝ, ∀ i : Fin N, ¬ (i : ℕ) < j → c (τ, i) = b := by
    intro τ
    by_cases h : ∃ i : Fin N, ¬ (i : ℕ) < j
    · obtain ⟨i, hi⟩ := h
      exact ⟨c (τ, i), fun k hk => hinv τ k i (iff_of_false hk hi)⟩
    · exact ⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩
  choose a ha using ha
  choose b hb using hb
  refine ⟨a, b, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hc, map_sum, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eval, eval_X]
  split_ifs with hi
  · rw [ha τ i hi]
    ring
  · rw [hb τ i hi]
    ring

theorem flagDeg_eq_delta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Ψ × Fin N → ℝ,
      flagDeg (fun τ i => x (τ, i) : Wt Ψ N) = c * eval x (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) := by
  refine ⟨((dimFl Ψ N).factorial : ℝ) * ∏ _τ : Ψ, ∏ i : Fin N, ∏ k ∈ Finset.Ioi i, ((k : ℝ) - (i : ℝ))⁻¹, ?_, ?_⟩
  · refine mul_pos (by positivity) (Finset.prod_pos fun _ _ => Finset.prod_pos fun i _ =>
      Finset.prod_pos fun k hk => inv_pos.2 (sub_pos.2 ?_))
    exact_mod_cast (Finset.mem_Ioi.1 hk)
  · intro x
    rw [(GlobalTheory.T.flag_degree_weight_formula Ψ N _).1, mul_assoc]
    congr 1
    unfold GroundTheory.Heights₂.Heights.antisymDelta
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_filter]
    refine Finset.prod_congr (by ext k; simp) fun k _ => ?_
    rw [map_sub, eval_X, eval_X, div_eq_inv_mul]

theorem cor_b_poly_functional : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (R : RP Ψ N →ₗ[ℝ] ℝ) (v ε : ℝ) (Pl l : MvPolynomial (Ψ × Fin N) ℝ), 0 < v → (∀ lam : Wt Ψ N, eval (fun x => lam x.1 x.2) Pl = R (linRoot lam ^ (dimFl Ψ N + 1))) → Pl.IsHomogeneous (dimFl Ψ N + 1) → l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j → (∀ m, |(Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l).coeff m| ≤ ε) → ∃ α β : Ψ → ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 → |R (monomial m 1) + v * (∑ τ, (α τ - β τ) * Sh j τ (monomial m 1) + ∑ τ, β τ * Tot τ (monomial m 1))| ≤ ε := by
  intro Ψ _ _ N j R v ε Pl l hv hP _ hl hε
  obtain ⟨a, b, hab⟩ := inv_linear_eval Ψ N j l hl
  obtain ⟨c, hc0, hc⟩ := flagDeg_eq_delta Ψ N
  set K : ℝ := v * ((dimFl Ψ N : ℝ) + 1) * c with hK
  have hK0 : K ≠ 0 := by positivity
  refine ⟨fun τ => a τ / K, fun τ => b τ / K, fun m hm => ?_⟩
  let Φ : RP Ψ N →ₗ[ℝ] ℝ :=
    R + v • (∑ τ, (a τ / K - b τ / K) • Lin.shL j τ + ∑ τ, (b τ / K) • Lin.totL τ)
  have hΦ : ∀ F, Φ F = R F + v * (∑ τ, (a τ / K - b τ / K) * Sh j τ F + ∑ τ, b τ / K * Tot τ F) := by
    intro F
    simp only [Φ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Lin.shL_apply,
      Lin.totL_apply, smul_eq_mul]
  obtain ⟨P', -, hP', -, hle⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) Φ
  have heq : P' = Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l := by
    refine MvPolynomial.funext fun x => ?_
    have e1 : (-∑ y, C (x y) * X y : RP Ψ N) = linRoot (fun τ i => x (τ, i) : Wt Ψ N) := rfl
    have e2 := hP (fun τ i => x (τ, i))
    rw [hP', e1, hΦ, map_sub, map_mul, hab, ← e2]
    simp only [(GlobalTheory.T.flag_shift_total_lin_root_power Ψ N j _ _).1, (GlobalTheory.T.flag_shift_total_lin_root_power Ψ N j _ _).2, hc]
    rw [sub_eq_add_neg (eval x Pl)]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hK' : v * ((dimFl Ψ N : ℝ) + 1) * c / K = 1 := div_self hK0
    generalize (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), x (τ, i)) = s
    generalize (∑ i, x (τ, i)) = t
    generalize eval x (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) = d
    linear_combination (-(d * ((a τ - b τ) * s + b τ * t))) * hK'
  have h := hle m hm
  rw [hΦ, heq] at h
  exact h.trans (hε m)

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AntisymmetricPerturbationBoundStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antisymmetric_perturbation_bound :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (R : RP Ψ N →ₗ[ℝ] ℝ)
      (v ε : ℝ) (Pl l : MvPolynomial (Ψ × Fin N) ℝ),
      0 < v →
      (∀ lam : Wt Ψ N, eval (fun x => lam x.1 x.2) Pl = R (linRoot lam ^ (dimFl Ψ N + 1))) →
      Pl.IsHomogeneous (dimFl Ψ N + 1) →
      l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j →
      (∀ m, |AddMonoidAlgebra.coeff (Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l) m| ≤ ε) →
      ∃ α β : Ψ → ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 →
        |R (monomial m 1) + v * (∑ τ, (α τ - β τ) * Sh j τ (monomial m 1) +
          ∑ τ, β τ * Tot τ (monomial m 1))| ≤ ε :=
  @GlobalTheory.CompanionTheory.Ar.Top.cor_b_poly_functional
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalNumberPermutationInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalNumberPermutationInvariant
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num.RootPerm

theorem classList_mapDomain {K σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (μ : σ →₀ ℕ) :
    classList cls (Finsupp.mapDomain e μ) = classList (cls ∘ e) μ := by
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_rename {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (he : Function.Injective e)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he, classList_mapDomain]

theorem rename_psumExpansion {r : ℕ} (e : Equiv.Perm (Fin r)) (k : ℕ) (i : Fin r) :
    rename (Sum.map e e) (psumExpansion r k i) = psumExpansion r k (e i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [psumExpansion, map_sum, rename_X]

theorem root_perm : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (r : ℕ) (e : Equiv.Perm (Fin r)) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)), (∀ (a : O) (x : Fin r → K → ℤ), laNum P a (x ∘ e) k Q = laNum P a x k Q) ∧ ∀ T : LocPair ι O (Fin r), (T.comp e).ck P k Q = T.ck P k Q := by
  intro O _ _ _ K _ _ ι _ r e P k Q
  refine ⟨fun a x => ?_, fun T => ?_⟩
  · have h : ∀ W : Ideal (MRing ι O), classNum (x ∘ e) (psum (Fin r) ℤ (k - 1)) Q W =
        classNum x (psum (Fin r) ℤ (k - 1)) Q W := fun W => by
      rw [← classNum_rename x e e.injective, rename_psum]
    simp only [laNum, h]
  · have h : ∀ (i : Fin r) (W : Ideal (MRing ι O)),
        classNum (Sum.elim (T.x ∘ e) (T.x' ∘ e)) (psumExpansion r k i) Q W =
          classNum (Sum.elim T.x T.x') (psumExpansion r k (e i)) Q W := fun i W => by
      have hc : Sum.elim T.x T.x' ∘ Sum.map e e = Sum.elim (T.x ∘ e) (T.x' ∘ e) := by
        funext s
        rcases s with s | s <;> rfl
      rw [← rename_psumExpansion, classNum_rename _ _ (Sum.map_injective.mpr ⟨e.injective, e.injective⟩), hc]
    simp only [LocPair.ck, pairNum, LocPair.comp, Function.comp_apply, h]
    exact Equiv.sum_comp e fun j => cycEval (fun W => classNum (Sum.elim T.x T.x') (psumExpansion r k j) Q W)
      (ratDiv P (T.f j) (T.g j))

end GlobalTheory.CompanionTheory.Ar.Num.RootPerm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalNumberPermutationInvariantStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_number_permutation_invariant : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (r : ℕ) (e : Equiv.Perm (Fin r)) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)), (∀ (a : O) (x : Fin r → K → ℤ), laNum P a (x ∘ e) k Q = laNum P a x k Q) ∧ ∀ T : LocPair ι O (Fin r), (T.comp e).ck P k Q = T.ck P k Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.RootPerm.root_perm | exact GlobalTheory.CompanionTheory.Ar.Num.RootPerm.root_perm | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.RootPerm.root_perm <;> assumption)
end
end
