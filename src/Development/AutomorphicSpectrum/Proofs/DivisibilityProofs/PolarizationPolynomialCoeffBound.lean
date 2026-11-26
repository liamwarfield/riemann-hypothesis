module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBound
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.PolarizationCoefficientsBound
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem pa_neg_lin_pow {J : Type} [Fintype J] [DecidableEq J] (d : ℕ) (c : J → ℝ) :
    ((-∑ x, C (c x) * X x : MvPolynomial J ℝ)) ^ d =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset J) d,
        ((-1) ^ d * (m.multinomial : ℝ) * m.prod (fun r e => c r ^ e)) • monomial m (1 : ℝ) := by
  rw [neg_pow, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
  refine Finset.sum_nbij' (fun g => Finsupp.equivFunOnFinite.symm g) (fun m => ⇑m) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_piAntidiag] at hg
    simp only [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    simpa using hg.1
  · intro m hm
    simp only [Finset.mem_finsuppAntidiag] at hm
    simp only [Finset.mem_piAntidiag]
    exact ⟨hm.1, fun i _ => Finset.mem_univ i⟩
  · intro g _
    simp
  · intro m _
    simp
  · intro g _
    set m : J →₀ ℕ := Finsupp.equivFunOnFinite.symm g with hm
    have hg : g = ⇑m := by simp [hm]
    rw [hg, Finsupp.multinomial_of_support_subset (Finset.subset_univ _),
      Finsupp.prod_fintype _ _ (by simp), monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp only [mul_pow, Finset.prod_mul_distrib, smul_eq_C_mul, map_mul, map_prod, map_pow, map_natCast,
      map_neg, map_one]
    ring

theorem polarization_coefficients_bound : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ), ∃ Pl : MvPolynomial J ℝ, Pl.IsHomogeneous d ∧ (∀ c : J → ℝ, eval c Pl = Φ ((-∑ x, C (c x) * X x) ^ d)) ∧ (∀ m : J →₀ ℕ, m.degree = d → AddMonoidAlgebra.coeff Pl m = (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1)) ∧ ∀ m : J →₀ ℕ, m.degree = d → |Φ (monomial m 1)| ≤ |Pl.coeff m| := by
  intro J _ _ d Φ
  set S := Finset.finsuppAntidiag (Finset.univ : Finset J) d with hSdef
  have hS : ∀ m : J →₀ ℕ, m ∈ S ↔ m.degree = d := by
    intro m
    simp [hSdef, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  set a : (J →₀ ℕ) → ℝ := fun m => (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1) with ha
  set Pl : MvPolynomial J ℝ := ∑ m ∈ S, monomial m (a m) with hPl
  have hcoeff : ∀ m : J →₀ ℕ, m.degree = d → AddMonoidAlgebra.coeff Pl m = a m := by
    intro m hm
    rw [hPl, coeff_sum, Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      rw [coeff_monomial, ite_eq_right hb]
    · intro hm'
      exact absurd ((hS m).2 hm) hm'
  refine ⟨Pl, ?_, ?_, hcoeff, ?_⟩
  · apply IsHomogeneous.sum
    intro m hm
    exact isHomogeneous_monomial _ ((hS m).1 hm)
  · intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pa_neg_lin_pow, hPl, map_sum (eval c), map_sum Φ]
    refine Finset.sum_congr hSdef fun m _ => ?_
    rw [eval_monomial, map_smul, smul_eq_mul, ha]
    ring
  · intro m hm
    rw [hcoeff m hm, ha]
    have hpos : (1 : ℝ) ≤ (m.multinomial : ℝ) := by
      have : 0 < m.multinomial := by
        rw [Finsupp.multinomial_eq]
        exact Nat.multinomial_pos _ _
      exact_mod_cast this
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    nlinarith [abs_nonneg (Φ (monomial m 1))]

end RootFieldNumerics
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBound
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem polarisation_functional : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ), ∃ Pl : MvPolynomial J ℝ, Pl.IsHomogeneous d ∧ (∀ c : J → ℝ, eval c Pl = Φ ((-∑ x, C (c x) * X x) ^ d)) ∧ (∀ m : J →₀ ℕ, m.degree = d → AddMonoidAlgebra.coeff Pl m = (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1)) ∧ ∀ m : J →₀ ℕ, m.degree = d → |Φ (monomial m 1)| ≤ |Pl.coeff m| :=
  @RootFieldNumerics.polarization_coefficients_bound

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBoundStatement
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_polynomial_coeff_bound : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ), ∃ Pl : MvPolynomial J ℝ, Pl.IsHomogeneous d ∧ (∀ c : J → ℝ, eval c Pl = Φ ((-∑ x, C (c x) * X x) ^ d)) ∧ (∀ m : J →₀ ℕ, m.degree = d → AddMonoidAlgebra.coeff Pl m = (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1)) ∧ ∀ m : J →₀ ℕ, m.degree = d → |Φ (monomial m 1)| ≤ |Pl.coeff m| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional | exact GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalLinRootPower
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalLinRootPower
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.LinPow

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_C_mul (c : ℝ) (F : RP Ψ N) : degFl (C c * F) = c * degFl F := by
  unfold degFl
  simp_rw [coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem pderiv_linRoot (u : Wt Ψ N) (τ : Ψ) (i : Fin N) :
    pderiv (τ, i) (linRoot u) = -C (u τ i) := by
  simp [linRoot, pderiv_X, Pi.single_apply]

theorem pderiv_linRoot_pow (u : Wt Ψ N) (τ : Ψ) (i : Fin N) (D : ℕ) :
    pderiv (τ, i) (linRoot u ^ (D + 1)) =
      C (-(((D : ℝ) + 1) * u τ i)) * linRoot u ^ D := by
  rw [Derivation.leibniz_pow, pderiv_linRoot]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
  simp only [map_neg, map_mul, map_add (f := _), map_natCast, map_one]
  push_cast
  ring

private lemma degFl_sum' {ι : Type*} (s : Finset ι) (f : ι → RP Ψ N) :
    degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  unfold degFl
  simp_rw [coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem degFl_sum_pderiv (u : Wt Ψ N) (τ : Ψ) (s : Finset (Fin N)) :
    degFl (∑ i ∈ s, pderiv (τ, i) (linRoot u ^ (dimFl Ψ N + 1))) =
      -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ s, u τ i) := by
  rw [degFl_sum']
  simp_rw [pderiv_linRoot_pow, degFl_C_mul]
  simp only [flagDeg]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.CompanionTheory.Ar.Top.LinPow

theorem GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ) (u : Wt Ψ N), Sh j τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u τ i) ∧ Tot τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i, u τ i) := by
  intro Ψ _ _ N j τ u
  exact ⟨GlobalTheory.CompanionTheory.Ar.Top.LinPow.degFl_sum_pderiv u τ _,
    GlobalTheory.CompanionTheory.Ar.Top.LinPow.degFl_sum_pderiv u τ Finset.univ⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalLinRootPowerStatement
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_shift_total_lin_root_power : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ) (u : Wt Ψ N), Sh j τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u τ i) ∧ Tot τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i, u τ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow | exact GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsFlagDegreeOnePolys
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.ExistsDegreeOneClass
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.L3

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem permExp_apply (σ : Ψ → Equiv.Perm (Fin N)) (x : Ψ × Fin N) :
    permExp σ x = N - 1 - ((σ x.1 x.2 : Fin N) : ℕ) := by
  simp [permExp]

theorem permExp_injective :
    Function.Injective (permExp : (Ψ → Equiv.Perm (Fin N)) → (Ψ × Fin N) →₀ ℕ) := by
  intro σ σ' h
  funext τ
  ext i
  have h1 := DFunLike.congr_fun h (τ, i)
  rw [permExp_apply, permExp_apply] at h1
  have h2 := (σ τ i).2
  have h3 := (σ' τ i).2
  dsimp only at h1
  omega

theorem degree_permExp_one :
    (permExp (1 : Ψ → Equiv.Perm (Fin N))).degree = dimFl Ψ N := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [permExp_apply, Pi.one_apply, Equiv.Perm.one_apply]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, dimFl,
    Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
    Finset.sum_range_id]

theorem degFl_monomial_one [DecidableEq Ψ] :
    degFl (monomial (permExp (1 : Ψ → Equiv.Perm (Fin N))) ((-1 : ℝ) ^ dimFl Ψ N)) = 1 := by
  unfold degFl
  rw [Finset.sum_eq_single (1 : Ψ → Equiv.Perm (Fin N))]
  · simp [← mul_pow]
  · intro σ _ hσ
    rw [coeff_monomial, if_neg (fun h => hσ (permExp_injective h).symm), mul_zero]
  · simp

end RootFieldNumerics.L3

theorem RootFieldNumerics.exists_degree_one_class : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ), 1 ≤ j → j < N → (∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N) ∧ degFl Q = 1) ∧ ∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N - 1) ∧ degFl (pkLow j τ 1 * Q) = 1 := by
  intro Ψ _ _ N j τ h1 hj
  refine ⟨⟨_, isHomogeneous_monomial _ RootFieldNumerics.L3.degree_permExp_one, RootFieldNumerics.L3.degFl_monomial_one⟩, ?_⟩
  let i0 : Fin N := ⟨j - 1, by omega⟩
  let i1 : Fin N := ⟨j, hj⟩
  let m : (Ψ × Fin N) →₀ ℕ := permExp (1 : Ψ → Equiv.Perm (Fin N)) - Finsupp.single (τ, i0) 1
  have hm : Finsupp.single (τ, i0) 1 + m = permExp (1 : Ψ → Equiv.Perm (Fin N)) := by
    apply add_tsub_cancel_of_le
    rw [Finsupp.single_le_iff, RootFieldNumerics.L3.permExp_apply]
    simp only [Pi.one_apply, Equiv.Perm.one_apply, i0]
    omega
  have hdeg : m.degree = dimFl Ψ N - 1 := by
    rw [← RootFieldNumerics.L3.degree_permExp_one, ← hm, map_add (f := _), Finsupp.degree_single]
    omega
  have h01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp only [i0, i1] at this
    omega
  have hm0 : m (τ, i0) = N - 1 - j := by
    simp only [m, Finsupp.tsub_apply, RootFieldNumerics.L3.permExp_apply, Finsupp.single_eq_same, Pi.one_apply,
      Equiv.Perm.one_apply, i0]
    omega
  have hm1 : m (τ, i1) = N - 1 - j := by
    have : (Finsupp.single (τ, i0) 1 : (Ψ × Fin N) →₀ ℕ) (τ, i1) = 0 :=
      Finsupp.single_eq_of_ne' (by simpa using h01)
    simp only [m, Finsupp.tsub_apply, RootFieldNumerics.L3.permExp_apply, this, Pi.one_apply,
      Equiv.Perm.one_apply, i1]
    omega
  refine ⟨monomial m ((-1 : ℝ) ^ dimFl Ψ N), isHomogeneous_monomial _ hdeg, ?_⟩
  refine Eq.trans ?_ (RootFieldNumerics.L3.degFl_monomial_one (Ψ := Ψ) (N := N))
  unfold degFl
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [pkLow, Finset.sum_mul, coeff_sum, Finset.sum_eq_single i0]
  · rw [X_pow_eq_monomial, monomial_mul, one_mul, hm]
  · intro i hi hi0
    rw [X_pow_eq_monomial, monomial_mul, coeff_monomial, if_neg]
    intro h
    have hi1 : i ≠ i1 := by
      intro h'
      rw [Finset.mem_filter, h'] at hi
      simp [i1] at hi
    have e0 := DFunLike.congr_fun h (τ, i0)
    have e1 := DFunLike.congr_fun h (τ, i1)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by simpa using hi0), hm0,
      RootFieldNumerics.L3.permExp_apply] at e0
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by simpa using hi1), hm1,
      RootFieldNumerics.L3.permExp_apply] at e1
    dsimp only at e0 e1
    have h2 := (σ τ i0).2
    have h3 := (σ τ i1).2
    exact h01 ((σ τ).injective (Fin.ext (by omega)))
  · intro h
    exact absurd (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, i0]; omega) h
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsFlagDegreeOnePolys
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem testForms_sh_tot : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ), 1 ≤ j → j < N → (∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N) ∧ degFl Q = 1) ∧ ∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N - 1) ∧ degFl (pkLow j τ 1 * Q) = 1 :=
  RootFieldNumerics.exists_degree_one_class

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsFlagDegreeOnePolysStatement
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_degree_one_polys : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ), 1 ≤ j → j < N → (∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N) ∧ degFl Q = 1) ∧ ∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N - 1) ∧ degFl (pkLow j τ 1 * Q) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot | exact GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot <;> assumption)
end
end
