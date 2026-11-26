module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegral
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecomposition
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PZeroSetNull

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantOneRowExpansion
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantOneRowExpansion
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem pderiv_fin_prod {σ : Type*} (k : σ) : ∀ (d : ℕ) (f : Fin (d + 1) → MvPolynomial σ ℝ),
    pderiv k (∏ r, f r) = ∑ r, pderiv k (f r) * ∏ s, f (r.succAbove s) := by
  intro d
  induction d with
  | zero => intro f; simp
  | succ d ih =>
    intro f
    rw [Fin.prod_univ_succ, Derivation.leibniz, ih (fun i => f i.succ),
      Fin.sum_univ_succ (fun r => pderiv k (f r) * ∏ s, f (r.succAbove s))]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · simp only [Fin.succAbove_zero]
      ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [Fin.prod_univ_succ (fun s => f (r.succ.succAbove s))]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
      ring

theorem pderiv_row_weight (c v : ℝ) : pderiv (some 0 : Option (Fin 2)) (rowW ![c, 0] v) = C c := by
  simp [rowW, pderiv_X, Pi.single_apply]

theorem eval_row_weight (n : Fin 3 → ℝ) (c v : ℝ) :
    evalW n n (rowW ![c, 0] v) = lin4 (fun i => c * n i) + C v * X none := by
  have h : lin4 (fun i => c * n i) = C c * lin4 n := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [lin4, lin3, map_sum, map_mul, rename_C, rename_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  simp [rowW, evalW, aeval_def, algebraMap_eq]

theorem extract_one : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (c : Fin (d + 1) → ℝ) (v : Fin (d + 1) → ℝ) (n : Fin 3 → ℝ) (e : ℂ),
      ((d + 1).factorial : ℂ) * mdisc (fun r => blk ((c r : ℂ) * e)
        ((∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H)) =
      e * L (evalW n n (pderiv (some 0) (∏ r, rowW ![c r, 0] (v r)))) := by
  intro d T H L hL c v n e
  have h1 := ((GlobalTheory.T.mixed_discriminant_cofactor_expansion d).1 (fun r => (c r : ℂ) * e)
    (fun r => (∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))
  refine h1.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pderiv_fin_prod, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h3 := hL (fun s i => c (r.succAbove s) * n i) (fun s => v (r.succAbove s))
  rw [h3, pderiv_row_weight, map_mul (evalW n n), map_prod (evalW n n)]
  simp only [eval_row_weight]
  have h4 : evalW n n (C (c r)) = C (c r) := by simp [evalW, aeval_def, algebraMap_eq]
  rw [h4, C_mul', map_smul, Complex.real_smul]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantOneRowExpansionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_discriminant_one_row_expansion : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (c : Fin (d + 1) → ℝ) (v : Fin (d + 1) → ℝ) (n : Fin 3 → ℝ) (e : ℂ),
      ((d + 1).factorial : ℂ) * mdisc (fun r => blk ((c r : ℂ) * e)
        ((∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H)) =
      e * L (evalW n n (pderiv (some 0) (∏ r, rowW ![c r, 0] (v r)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.extract_one | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.extract_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.extract_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WordCoefficientSecondDerivative
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WordCoefficientSecondDerivative
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd

theorem pderiv_comm {σ : Type*} (a b : σ) (P : MvPolynomial σ ℝ) :
    pderiv a (pderiv b P) = pderiv b (pderiv a P) := by
  have h : ⁅(pderiv a : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)),
      (pderiv b : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    classical
    have hc : ∀ c : σ, pderiv (R := ℝ) c (X i) = if i = c then 1 else 0 := fun c => by
      rw [pderiv_X, Pi.single_apply]
    simp only [Derivation.commutator_apply, hc, Derivation.coe_zero, Pi.zero_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using h2

theorem pderiv_some_rename_mul (j : Fin 2) (P : MvPolynomial (Fin 2) ℝ) (m : ℕ) :
    pderiv (some j) (rename some P * (X none : MvPolynomial (Option (Fin 2)) ℝ) ^ m) =
      rename some (pderiv j P) * X none ^ m := by
  have h0 : pderiv (some j) ((X none : MvPolynomial (Option (Fin 2)) ℝ) ^ m) = 0 := by
    simp [Derivation.leibniz_pow, pderiv_X, Pi.single_apply]
  rw [Derivation.leibniz, h0, pderiv_rename (Option.some_injective _)]
  simp [mul_comm]

theorem evalW_rename (n₀ n₁ : Fin 3 → ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    evalW n₀ n₁ (rename some P) = rename some (aeval ![lin3 n₀, lin3 n₁] P) := by
  have h : ((evalW n₀ n₁).comp (rename some) : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] _) =
      (rename some).comp (aeval ![lin3 n₀, lin3 n₁]) := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;> simp [evalW, lin4]
  exact DFunLike.congr_fun h P

theorem prod_rows_word (d k i : ℕ) (hk : 2 * k ≤ d + 2) :
    (∏ r : Fin (d + 2),
      rowW (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0)
        (if (r : ℕ) < 2 * k then 0 else 1)) =
    rename some (wwLinProd k (DiagonalFibreFubini.wordCoef i)) * X none ^ (d + 2 - 2 * k) := by
  rw [Fin.prod_univ_eq_prod_range (fun r : ℕ =>
    rowW (if r < 2 * k then DiagonalFibreFubini.wordCoef i r else 0) (if r < 2 * k then 0 else 1)) (d + 2)]
  obtain ⟨m, hm⟩ : ∃ m, d + 2 = 2 * k + m := ⟨d + 2 - 2 * k, by omega⟩
  rw [hm, Finset.prod_range_add, show 2 * k + m - 2 * k = m by omega]
  congr 1
  · rw [wwLinProd, map_prod]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hn' : n < 2 * k := Finset.mem_range.mp hn
    simp [rowW, hn']
  · rw [Finset.prod_congr rfl (g := fun _ => (X none : MvPolynomial (Option (Fin 2)) ℝ))]
    · simp
    · intro x _
      simp [rowW]

theorem evalW_pderiv_prod_rows_word : ∀ (d k i : ℕ), i < k → 2 * k ≤ d + 2 → ∀ n₀ n₁ : Fin 3 → ℝ,
    evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r : Fin (d + 2),
      rowW (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0)
        (if (r : ℕ) < 2 * k then 0 else 1)))) =
    rename some (aeval ![lin3 n₀, lin3 n₁]
      (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))) * X none ^ (d + 2 - 2 * k) := by
  intro d k i _ hk n₀ n₁
  rw [prod_rows_word d k i hk, pderiv_some_rename_mul, pderiv_some_rename_mul, map_mul, evalW_rename,
    pderiv_comm 1 0, map_pow]
  congr 1
  simp [evalW]

end GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WordCoefficientSecondDerivativeStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_coefficient_second_derivative : ∀ (d k i : ℕ), i < k → 2 * k ≤ d + 2 → ∀ n₀ n₁ : Fin 3 → ℝ,
    evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r : Fin (d + 2),
      rowW (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0)
        (if (r : ℕ) < 2 * k then 0 else 1)))) =
    rename some (aeval ![lin3 n₀, lin3 n₁]
      (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))) * X none ^ (d + 2 - 2 * k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd.evalW_pderiv_prod_rows_word | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd.evalW_pderiv_prod_rows_word | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd.evalW_pderiv_prod_rows_word <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantLinearFunctional
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantLinearFunctional
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly

noncomputable section

lemma exists_perm_of_sum_single {d : ℕ} {τ τ' : Fin d → Option (Fin 3)}
    (h : ∑ t, Finsupp.single (τ t) (1 : ℕ) = ∑ t, Finsupp.single (τ' t) (1 : ℕ)) :
    ∃ π : Equiv.Perm (Fin d), ∀ t, τ' (π t) = τ t := by
  classical
  have hc : ∀ o : Option (Fin 3), Fintype.card {t // τ t = o} = Fintype.card {t // τ' t = o} := by
    intro o
    have h1 := congrArg (fun f => f o) h
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_boole, Nat.cast_id] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h1
  exact ⟨Equiv.ofFiberEquiv (fun o => Fintype.equivOfCardEq (hc o)), fun t => Equiv.ofFiberEquiv_map _ t⟩

lemma prod_X_eq_monomial {d : ℕ} (τ : Fin d → Option (Fin 3)) :
    (∏ t, (X (τ t) : MvPolynomial (Option (Fin 3)) ℝ)) =
      monomial (∑ t, Finsupp.single (τ t) (1 : ℕ)) 1 := by
  exact (monomial_sum_one (R := ℝ) Finset.univ fun t => Finsupp.single (τ t) 1).symm

lemma linear_form_add_eq_sum (n : Fin 3 → ℝ) (v : ℝ) :
    lin4 n + C v * X none =
      ∑ j : Option (Fin 3), C (Option.elim j v n) * (X j : MvPolynomial (Option (Fin 3)) ℝ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin4, lin3, map_sum, map_mul, rename_X, rename_C, Fintype.sum_option, Option.elim_none,
    Option.elim_some]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_functional : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
    ∃ L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ, ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)) := by
  classical
  intro d T H
  obtain ⟨Λ, hΛ, hsym⟩ := (PositivityTheory.Xgp.t_fib_mdisc d).2
  obtain ⟨M, hM⟩ : ∃ M : Option (Fin 3) → Matrix (Fin d) (Fin d) ℂ, M none = H ∧ ∀ i, M (some i) = T i :=
    ⟨fun j => Option.elim j H T, rfl, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (Option (Fin 3) →₀ ℕ) → ℂ, ∀ τ : Fin d → Option (Fin 3),
      g (∑ t, Finsupp.single (τ t) (1 : ℕ)) = (d.factorial : ℂ) * Λ (fun t => M (τ t)) := by
    refine ⟨fun m => if h : ∃ τ : Fin d → Option (Fin 3), ∑ t, Finsupp.single (τ t) (1 : ℕ) = m then
      (d.factorial : ℂ) * Λ (fun t => M (h.choose t)) else 0, fun τ => ?_⟩
    have h : ∃ τ' : Fin d → Option (Fin 3),
        ∑ t, Finsupp.single (τ' t) (1 : ℕ) = ∑ t, Finsupp.single (τ t) (1 : ℕ) := ⟨τ, rfl⟩
    simp only [dif_pos h]
    obtain ⟨π, hπ⟩ := exists_perm_of_sum_single h.choose_spec
    have e : (fun t => M (h.choose t)) = (fun t => M (τ t)) ∘ π :=
      funext fun t => by simp only [Function.comp_apply, hπ]
    rw [e, hsym]
  refine ⟨(basisMonomials (Option (Fin 3)) ℝ).constr ℝ g, fun c v => ?_⟩
  have hL : ∀ (m : Option (Fin 3) →₀ ℕ) (x : ℝ),
      (basisMonomials (Option (Fin 3)) ℝ).constr ℝ g (monomial m x) = (x : ℂ) * g m := by
    intro m x
    have hx : (monomial m x : MvPolynomial (Option (Fin 3)) ℝ) = x • basisMonomials (Option (Fin 3)) ℝ m := by
      simp only [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    rw [hx, map_smul, Module.Basis.constr_basis, Complex.real_smul]
  have hrow : ∀ t, (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H =
      ∑ j : Option (Fin 3), ((Option.elim j (v t) (c t) : ℝ) : ℂ) • M j := by
    intro t
    rw [Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some, hM.1, hM.2]
    exact add_comm _ _
  have hprod : (∏ t, (lin4 (c t) + C (v t) * X none) : MvPolynomial (Option (Fin 3)) ℝ) =
      ∑ r : Fin d → Option (Fin 3),
        monomial (∑ t, Finsupp.single (r t) (1 : ℕ)) (∏ t, Option.elim (r t) (v t) (c t)) := by
    simp only [linear_form_add_eq_sum]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod (C : ℝ →+* MvPolynomial (Option (Fin 3)) ℝ), prod_X_eq_monomial,
      C_mul_monomial, mul_one]
  simp only [hrow]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hΛ, MultilinearMap.map_sum, hprod, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, hL, hg, smul_eq_mul, Complex.ofReal_prod]
  simp only [RingHom.id_apply]
  ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantLinearFunctionalStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_discriminant_linear_functional : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
    ∃ L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ, ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValuationRingExtensionSpecialization
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValuationRingExtensionSpecialization
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.ComplexPlace

theorem exists_ringHom_of_finiteType {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (v : A →+* ℂ) (hv : (RingHom.ker v).IsMaximal) (M : Ideal B)
    (hMm : M.IsMaximal) (hM : ∀ a, v a = 0 → algebraMap A B a ∈ M) :
    ∃ ψ : B →+* ℂ, ∀ a, ψ (algebraMap A B a) = v a := by
  letI κF : Field (A ⧸ RingHom.ker v) := Ideal.Quotient.field _
  letI KF : Field (B ⧸ M) := Ideal.Quotient.field _
  let φ : A ⧸ RingHom.ker v →+* B ⧸ M :=
    Ideal.quotientMap M (algebraMap A B) (fun a ha => hM a (RingHom.mem_ker.mp ha))
  letI : Algebra (A ⧸ RingHom.ker v) (B ⧸ M) := φ.toAlgebra
  haveI : IsScalarTower A (A ⧸ RingHom.ker v) (B ⧸ M) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.FiniteType A (B ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A M) (Ideal.Quotient.mkₐ_surjective A M)
  haveI : Algebra.FiniteType (A ⧸ RingHom.ker v) (B ⧸ M) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ RingHom.ker v) (B ⧸ M)
  haveI : Module.Finite (A ⧸ RingHom.ker v) (B ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  letI : Algebra (A ⧸ RingHom.ker v) ℂ := (RingHom.kerLift v).toAlgebra
  let g : (B ⧸ M) →ₐ[A ⧸ RingHom.ker v] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨g.toRingHom.comp (Ideal.Quotient.mk M), fun a => ?_⟩
  exact g.commutes (Ideal.Quotient.mk (RingHom.ker v) a)

theorem isLocalRing_and_ker {L : Type} [Field L] (O : Subring L) (v : O →+* ℂ)
    (hv : ∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) :
    ∃ _ : IsLocalRing O, RingHom.ker v = IsLocalRing.maximalIdeal O := by
  have hunit : ∀ s : O, IsUnit s ↔ v s ≠ 0 := by
    intro s
    constructor
    · intro h
      exact (h.map v).ne_zero
    · intro h
      have hs : (s : L) ≠ 0 := by
        intro h0
        apply h
        have : s = 0 := Subtype.ext h0
        simp [this]
      refine IsUnit.of_mul_eq_one (⟨(s : L)⁻¹, hv s h⟩ : O) ?_
      exact Subtype.ext (mul_inv_cancel₀ hs)
  have hloc : IsLocalRing O := by
    refine IsLocalRing.of_nonunits_add ?_
    intro a b ha hb
    have ha' : v a = 0 := by
      by_contra h
      exact ha ((hunit a).2 h)
    have hb' : v b = 0 := by
      by_contra h
      exact hb ((hunit b).2 h)
    intro hab
    exact (hunit _).1 hab (by simp [ha', hb'])
  refine ⟨hloc, ?_⟩
  ext s
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
  simp

theorem exists_valuationSubring_place (L : Type) [Field L] (O : Subring L) (v : O →+* ℂ)
    (hv : ∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) :
    ∃ V : ValuationSubring L, (∀ s ∈ O, s ∈ V) ∧ ∀ T : Finset L, (∀ t ∈ T, t ∈ V) →
      ∃ (R : Subring L) (hO : O ≤ R) (ψ : R →+* ℂ), (∀ t ∈ T, t ∈ R) ∧
        (∀ s : O, ψ (Subring.inclusion hO s) = v s) ∧ ∀ t ∈ T, t ≠ 0 → t⁻¹ ∈ V → t⁻¹ ∈ R := by
  obtain ⟨hloc, hker⟩ := isLocalRing_and_ker O v hv
  obtain ⟨V, hV, hlocal⟩ := IsLocalRing.exists_factor_valuationRing O.subtype
  refine ⟨V, fun s hs => hV ⟨s, hs⟩, fun T hT => ?_⟩
  let S : Finset L := T ∪ (T.filter (fun t => t⁻¹ ∈ V)).image (fun t => t⁻¹)
  have hSV : ∀ x ∈ S, x ∈ V := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hT x h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ht).2
  let B : Subalgebra O L := Algebra.adjoin O (S : Set L)
  let VA : Subalgebra O L :=
    { V.toSubring with algebraMap_mem' := fun s => hV s }
  have hBV : B ≤ VA := Algebra.adjoin_le (fun x hx => hSV x hx)
  haveI : Algebra.FiniteType O B :=
    (Subalgebra.fg_iff_finiteType B).1 (Subalgebra.fg_adjoin_finset S)
  let f : B →+* V :=
    { toFun := fun x => ⟨x.1, hBV x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let n : Ideal B := (IsLocalRing.maximalIdeal V).comap f
  have hn : n ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ n := h ▸ Submodule.mem_top
    have h2 : f 1 ∈ IsLocalRing.maximalIdeal V := h1
    rw [map_one] at h2
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal V).ne_top h2
  obtain ⟨M, hMm, hnM⟩ := Ideal.exists_le_maximal n hn
  have hM : ∀ a : O, v a = 0 → algebraMap O B a ∈ M := by
    intro a ha
    apply hnM
    have ha' : a ∈ IsLocalRing.maximalIdeal O := hker ▸ RingHom.mem_ker.mpr ha
    show f (algebraMap O B a) ∈ IsLocalRing.maximalIdeal V
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha' ⊢
    intro hu
    apply ha'
    exact hlocal.map_nonunit a hu
  have hvm : (RingHom.ker v).IsMaximal := by
    rw [hker]
    exact IsLocalRing.maximalIdeal.isMaximal O
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_finiteType v hvm M hMm hM
  have hO : O ≤ B.toSubring := fun s hs => B.algebraMap_mem (⟨s, hs⟩ : O)
  refine ⟨B.toSubring, hO, ψ, ?_, ?_, ?_⟩
  · intro t ht
    exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _ ht))
  · intro s
    exact hψ s
  · intro t ht _ hi
    exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨t, Finset.mem_filter.2 ⟨ht, hi⟩, rfl⟩)))

end GlobalTheory.CompanionTheory.Ar.ComplexPlace
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValuationRingExtensionSpecializationStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_ring_extension_specialization : ∀ (L : Type) [Field L] (O : Subring L) (v : O →+* ℂ), (∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) → ∃ V : ValuationSubring L, (∀ s ∈ O, s ∈ V) ∧ ∀ T : Finset L, (∀ t ∈ T, t ∈ V) → ∃ (R : Subring L) (hO : O ≤ R) (ψ : R →+* ℂ), (∀ t ∈ T, t ∈ R) ∧ (∀ s : O, ψ (Subring.inclusion hO s) = v s) ∧ ∀ t ∈ T, t ≠ 0 → t⁻¹ ∈ V → t⁻¹ ∈ R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place | exact GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place | (intros; apply GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultAtTwistQuadEq
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultAtTwistQuadEq
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Abstract

variable {R R' : Type*} [CommRing R] [CommRing R']

theorem length_cut_of_flat (φ : R →+* R') (q : R') (J W : Ideal R) [W.IsPrime]
    (W' : Ideal R') [W'.IsPrime] (hW' : W' = W.map φ ⊔ Ideal.span {q}) (hc : W'.comap φ = W)
    (hflat : ((Ideal.Quotient.mk (Ideal.span {q})).comp φ).Flat) :
    Module.length (Localization.AtPrime W')
        (LocalizedModule W'.primeCompl (R' ⧸ (J.map φ ⊔ Ideal.span {q}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) := by
  let I : Ideal R' := Ideal.span {q}
  let π : R' →+* R' ⧸ I := Ideal.Quotient.mk I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  let ψ : R →+* R' ⧸ I := π.comp φ
  have hker : RingHom.ker π = I := Ideal.mk_ker
  have hIW : I ≤ W' := hW' ▸ le_sup_right
  let P : Ideal (R' ⧸ I) := W'.map π
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective hπ (by rw [hker]; exact hIW)
  have hPc : W' = P.comap π := by
    show W' = (W'.map π).comap π
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hIW]
  have hPψ : W = P.comap ψ := by
    have h : P.comap ψ = (P.comap π).comap φ := (Ideal.comap_comap φ π).symm
    rw [h, ← hPc, hc]
  have hPmap : W.map ψ = P := by
    show W.map (π.comp φ) = W'.map π
    rw [hW', Ideal.map_sup, ← Ideal.map_map]
    have : (Ideal.span {q} : Ideal R').map π = ⊥ := Ideal.map_quotient_self I
    rw [this, sup_bot_eq]
  let L := Localization.localRingHom W P ψ hPψ
  have hLflat : L.Flat := RingHom.Flat.localRingHom hflat P W hPψ
  have hcomp : L.comp (algebraMap R (Localization.AtPrime W)) =
      (algebraMap (R' ⧸ I) (Localization.AtPrime P)).comp ψ :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hPψ z
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map L =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), Ideal.map_map, hcomp,
      ← Ideal.map_map, hPmap, IsLocalization.AtPrime.map_eq_maximalIdeal P]
  have hJ : (J.map (algebraMap R (Localization.AtPrime W))).map L =
      (J.map ψ).map (algebraMap (R' ⧸ I) (Localization.AtPrime P)) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
  have hkerE : RingHom.ker ((Ideal.Quotient.mk (J.map ψ)).comp π) = J.map φ ⊔ I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    show ((J.map (π.comp φ))).comap π = _
    rw [← Ideal.map_map, Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker]
  let e : (R' ⧸ (J.map φ ⊔ I)) ≃+* ((R' ⧸ I) ⧸ J.map ψ) :=
    (Ideal.quotEquivOfEq hkerE.symm).trans (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (J.map ψ)).comp π) (Ideal.Quotient.mk_surjective.comp hπ))
  have he : ∀ (s : R') (x : R' ⧸ (J.map φ ⊔ I)), e.toAddEquiv (s • x) = π s • e.toAddEquiv x := by
    intro s x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (J.map ψ) (π (s * y)) =
      Ideal.Quotient.mk (J.map ψ) (π s) * Ideal.Quotient.mk (J.map ψ) (π y)
    rw [map_mul, map_mul]
  rw [GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedModule_eq_of_surjective π hπ P W' hPc _ _
      e.toAddEquiv he,
    GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    ← hJ]
  exact GroundTheory.Heights₂.Heights.Inter.BCMultProof.length_quot_map_of_flat L hLflat hmax _

end Abstract

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def toPoly : MRing (Tb ι) →+* Polynomial (Polynomial (MRing ι)) :=
  (aeval (fun q : Σ o, Tb ι o => match q with
    | ⟨none, j⟩ => (![Polynomial.X, Polynomial.C Polynomial.X] : Fin 2 → _) j
    | ⟨some k, i⟩ => Polynomial.C (Polynomial.C (X ⟨k, i⟩))) :
      MRing (Tb ι) →ₐ[ℤ] Polynomial (Polynomial (MRing ι))).toRingHom

def ofPoly : Polynomial (Polynomial (MRing ι)) →+* MRing (Tb ι) :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom inc yN) xN

theorem toPoly_xN : toPoly (xN : MRing (Tb ι)) = Polynomial.X := by
  simp only [toPoly, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toPoly_yN : toPoly (yN : MRing (Tb ι)) = Polynomial.C Polynomial.X := by
  simp only [toPoly, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toPoly_comp_inc : (toPoly.comp inc : MRing ι →+* _) = Polynomial.C.comp Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [toPoly, inc]
  · intro i; simp [toPoly, inc, oldIdx]

theorem toPoly_inc (f : MRing ι) : toPoly (inc f) = Polynomial.C (Polynomial.C f) :=
  congrArg (fun g => g f) (toPoly_comp_inc (ι := ι))

theorem ofPoly_comp_toPoly : (ofPoly.comp toPoly : MRing (Tb ι) →+* _) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [toPoly, ofPoly]
  · rintro ⟨o, i⟩
    cases o with
    | none =>
      change Fin 2 at i
      fin_cases i
      · have : (X ⟨none, (0 : Fin 2)⟩ : MRing (Tb ι)) = xN := rfl
        simp [this, toPoly_xN, ofPoly]
      · have : (X ⟨none, (1 : Fin 2)⟩ : MRing (Tb ι)) = yN := rfl
        simp [this, toPoly_yN, ofPoly]
    | some k =>
      simp [toPoly, ofPoly, inc, oldIdx]

theorem toPoly_comp_ofPoly :
    (toPoly.comp ofPoly : Polynomial (Polynomial (MRing ι)) →+* _) = RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · refine RingHom.ext fun f => ?_
      simp [ofPoly, toPoly_inc]
    · simp [ofPoly, toPoly_yN]
  · simp [ofPoly, toPoly_xN]

def polyEquiv : MRing (Tb ι) ≃+* Polynomial (Polynomial (MRing ι)) :=
  RingEquiv.ofRingHom toPoly ofPoly toPoly_comp_ofPoly ofPoly_comp_toPoly

theorem toPoly_quad (p : ℕ) : ∃ s : Polynomial (MRing ι),
    toPoly (quad p : MRing (Tb ι)) = Polynomial.X ^ 2 + Polynomial.C s := by
  refine ⟨Polynomial.C (C (p : ℤ)) * Polynomial.X ^ 2, ?_⟩
  have h : toPoly (C (p : ℤ) : MRing (Tb ι)) =
      Polynomial.C (Polynomial.C (C (p : ℤ) : MRing ι)) := by
    simpa [inc] using toPoly_inc (ι := ι) (C (p : ℤ) : MRing ι)
  simp [quad, toPoly_xN, toPoly_yN, h]

theorem flat_quad (p : ℕ) :
    ((Ideal.Quotient.mk (Ideal.span {quad p})).comp inc :
      MRing ι →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat := by
  obtain ⟨s, hs⟩ := toPoly_quad (ι := ι) p
  let g : Polynomial (Polynomial (MRing ι)) := Polynomial.X ^ 2 + Polynomial.C s
  have hg : g.Monic := Polynomial.monic_X_pow_add
    (lt_of_le_of_lt Polynomial.degree_C_le (by norm_num))
  have : Module.Free (Polynomial (MRing ι)) (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  have h1 : (Polynomial.C : MRing ι →+* Polynomial (MRing ι)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (MRing ι) (Polynomial (MRing ι)))
  have h2 : (AdjoinRoot.of g).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (inferInstance : Module.Flat (Polynomial (MRing ι)) (AdjoinRoot g))
  let E : (MRing (Tb ι) ⧸ Ideal.span {quad p}) ≃+* AdjoinRoot g :=
    Ideal.quotientEquiv _ _ (polyEquiv (ι := ι)) (by
      rw [Ideal.map_span, Set.image_singleton]
      show Ideal.span {g} = Ideal.span {toPoly (quad p)}
      rw [hs])
  have h3 : (E.symm : AdjoinRoot g →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat :=
    RingHom.Flat.of_bijective E.symm.bijective
  have hcomp : (Ideal.Quotient.mk (Ideal.span {quad p})).comp inc =
      (E.symm : AdjoinRoot g →+* _).comp ((AdjoinRoot.of g).comp Polynomial.C) := by
    refine RingHom.ext fun f => ?_
    show Ideal.Quotient.mk _ (inc f) = E.symm (AdjoinRoot.of g (Polynomial.C f))
    rw [RingEquiv.eq_symm_apply]
    show Ideal.Quotient.mk _ (toPoly (inc f)) = _
    rw [toPoly_inc]
    rfl
  rw [hcomp]
  exact (h1.comp h2).comp h3

theorem multAt_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (J W : Ideal (MRing ι)) (hW : W ∈ J.minimalPrimes) (hT : (twist p W).IsPrime) :
    multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  have hWp : W.IsPrime := hW.1.1
  unfold multAt
  rw [dite_eq_left hT, dite_eq_left hWp]
  exact congrArg ENat.toNat (length_cut_of_flat inc (quad p) J W (twist p W) rfl
    (comap_inc_twist p W) (flat_quad p))

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultAtTwistQuadEqStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multAt_twist_quad_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (J W : Ideal (MRing ι)), W ∈ J.minimalPrimes → (twist p W).IsPrime → multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SpherePairLogSineMoment
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SpherePairLogSineMoment
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo

noncomputable section

def crd (m : S2) : Fin 3 → ℝ := fun i => (m : E3) i

def dens (a : ℂ) : ℝ := Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2

def stereoMeasure : Measure ℂ := volume.withDensity fun a => ENNReal.ofReal (dens a)

theorem continuous_crd : Continuous crd :=
  continuous_pi fun i => (EuclideanSpace.proj i).continuous.comp continuous_subtype_val

theorem measurable_dens : Measurable dens := by
  have : Continuous dens := by
    unfold dens
    refine continuous_const.div₀ (by fun_prop) fun a => ?_
    positivity
  exact this.measurable

theorem dens_nonneg (a : ℂ) : 0 ≤ dens a := by
  unfold dens
  have := Real.pi_pos
  positivity

theorem measurable_nS : Measurable nS := by
  have : Continuous nS := by
    refine continuous_pi fun i => ?_
    unfold nS
    refine Continuous.div ?_ (by fun_prop) fun a => by positivity
    fin_cases i <;> simp <;> fun_prop
  exact this.measurable

theorem stereo_hyp (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f) :
    (Integrable (fun a : ℂ => f (nS a) * dens a) ↔ Integrable (fun m : S2 => f (crd m)) sphereMeasure) ∧
      ∫ a : ℂ, f (nS a) * dens a = ∫ m : S2, f (crd m) ∂sphereMeasure :=
  (GlobalTheory.T.sphere_measure_stereographic_integral).1 f hf

theorem map_stereo : stereoMeasure.map nS = sphereMeasure.map crd := by
  have := FibreLocal.isProbabilityMeasure_sphere
  ext s hs
  rw [Measure.map_apply measurable_nS hs, Measure.map_apply continuous_crd.measurable hs]
  have hpre := continuous_crd.measurable hs
  have hpre' := measurable_nS hs
  have hf : Measurable (s.indicator (1 : (Fin 3 → ℝ) → ℝ)) := measurable_one.indicator hs
  have hfI : Integrable (fun m : S2 => s.indicator (1 : (Fin 3 → ℝ) → ℝ) (crd m)) sphereMeasure :=
    (integrable_const (1 : ℝ)).indicator hpre
  obtain ⟨h1, h2⟩ := stereo_hyp _ hf
  have hI := h1.2 hfI
  have hnn : 0 ≤ᵐ[volume] fun a => s.indicator (1 : (Fin 3 → ℝ) → ℝ) (nS a) * dens a :=
    Eventually.of_forall fun a => mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (dens_nonneg a)
  calc stereoMeasure (nS ⁻¹' s) = ∫⁻ a in nS ⁻¹' s, ENNReal.ofReal (dens a) := withDensity_apply _ hpre'
    _ = ∫⁻ a, ENNReal.ofReal (s.indicator (1 : (Fin 3 → ℝ) → ℝ) (nS a) * dens a) := by
        rw [← lintegral_indicator hpre']
        refine lintegral_congr fun a => ?_
        by_cases ha : nS a ∈ s
        · simp [Set.indicator, ha]
        · simp [Set.indicator, ha]
    _ = ENNReal.ofReal (∫ a, s.indicator (1 : (Fin 3 → ℝ) → ℝ) (nS a) * dens a) :=
        (ofReal_integral_eq_lintegral_ofReal hI hnn).symm
    _ = ENNReal.ofReal (∫ m, s.indicator (1 : (Fin 3 → ℝ) → ℝ) (crd m) ∂sphereMeasure) := by rw [h2]
    _ = sphereMeasure (crd ⁻¹' s) := by
        have h3 : ∫ m, s.indicator (1 : (Fin 3 → ℝ) → ℝ) (crd m) ∂sphereMeasure =
            sphereMeasure.real (crd ⁻¹' s) := integral_indicator_one hpre
        rw [h3]
        exact ofReal_measureReal

instance : IsFiniteMeasure stereoMeasure := by
  have := FibreLocal.isProbabilityMeasure_sphere
  constructor
  have h := congrArg (fun μ => μ Set.univ) map_stereo
  simp only [Measure.map_apply measurable_nS MeasurableSet.univ,
    Measure.map_apply continuous_crd.measurable MeasurableSet.univ, Set.preimage_univ] at h
  rw [h]
  simp

theorem integral_pair (Φ : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ) (hΦ : Measurable Φ) :
    ∫ p : ℂ × ℂ, dens p.1 * dens p.2 * Φ (nS p.1, nS p.2) =
      ∫ p : S2 × S2, Φ (crd p.1, crd p.2) ∂(sphereMeasure.prod sphereMeasure) := by
  have := FibreLocal.isProbabilityMeasure_sphere
  have hc := continuous_crd.measurable
  have hn := measurable_nS
  have hmap : (stereoMeasure.prod stereoMeasure).map (Prod.map nS nS) =
      (sphereMeasure.prod sphereMeasure).map (Prod.map crd crd) := by
    rw [← Measure.map_prod_map _ _ hn hn, ← Measure.map_prod_map _ _ hc hc, map_stereo]
  have hd : Measurable fun a => ENNReal.ofReal (dens a) := ENNReal.measurable_ofReal.comp measurable_dens
  have hprod : stereoMeasure.prod stereoMeasure =
      (volume : Measure (ℂ × ℂ)).withDensity
        (fun p => ENNReal.ofReal (dens p.1) * ENNReal.ofReal (dens p.2)) := by
    rw [stereoMeasure, prod_withDensity hd hd]
    rfl
  have hL : ∫ p : ℂ × ℂ, dens p.1 * dens p.2 * Φ (nS p.1, nS p.2) =
      ∫ p, Φ (Prod.map nS nS p) ∂(stereoMeasure.prod stereoMeasure) := by
    rw [hprod, integral_withDensity_eq_integral_toReal_smul₀
      (by exact ((hd.comp measurable_fst).mul (hd.comp measurable_snd)).aemeasurable)
      (Eventually.of_forall fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (dens_nonneg _),
      ENNReal.toReal_ofReal (dens_nonneg _)]
    rfl
  rw [hL, ← integral_map (hn.prodMap hn).aemeasurable hΦ.aestronglyMeasurable, hmap,
    integral_map (hc.prodMap hc).aemeasurable hΦ.aestronglyMeasurable]
  rfl

def dp {Ω : Type*} (u : Ω → Fin 3 → ℝ) : MvPolynomial (Fin 3) (Ω → ℝ) :=
  ∑ i, X i * C (fun q => u q i)

def pp {Ω : Type*} (u v : Ω → Fin 3 → ℝ) (Q : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) (Ω → ℝ) :=
  aeval ![dp u, dp v] Q

theorem map_pp {Ω : Type*} (u v : Ω → Fin 3 → ℝ) (Q : MvPolynomial (Fin 2) ℝ) (p : Ω) :
    map (Pi.evalRingHom (fun _ : Ω => ℝ) p) (pp u v Q) = aeval ![lin3 (u p), lin3 (v p)] Q := by
  have h : map (Pi.evalRingHom (fun _ : Ω => ℝ) p) (pp u v Q) =
      mapAlgHom (Pi.evalAlgHom ℝ (fun _ : Ω => ℝ) p) (pp u v Q) := rfl
  rw [h, pp, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext r
  fin_cases r
  · simp [dp, lin3, mapAlgHom_apply]
  · simp [dp, lin3, mapAlgHom_apply]

theorem ell_eq (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (R : MvPolynomial (Fin 3) ℝ)
    (S : Finset (Fin 3 →₀ ℕ)) (hS : R.support ⊆ S) :
    ℓ R = ∑ m ∈ S, AddMonoidAlgebra.coeff R m * ℓ (monomial m 1) := by
  conv_lhs => rw [R.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rw [← Finset.sum_subset hS fun m _ hm => by simp [notMem_support_iff.1 hm]]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_one (AddMonoidAlgebra.coeff R m), ← smul_eq_mul, ← smul_monomial, map_smul, smul_eq_mul, smul_eq_mul, mul_one]

theorem ell_pp {Ω : Type*} (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (u v : Ω → Fin 3 → ℝ)
    (Q : MvPolynomial (Fin 2) ℝ) (p : Ω) :
    ℓ (aeval ![lin3 (u p), lin3 (v p)] Q) =
      ∑ m ∈ (pp u v Q).support, AddMonoidAlgebra.coeff (pp u v Q) m p * ℓ (monomial m 1) := by
  rw [← map_pp, ell_eq ℓ _ _ (support_map_subset _ _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map]
  rfl

theorem continuous_coeff_pp {Ω : Type*} [TopologicalSpace Ω] (u v : Ω → Fin 3 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (Q : MvPolynomial (Fin 2) ℝ) (m : Fin 3 →₀ ℕ) :
    Continuous (AddMonoidAlgebra.coeff (pp u v Q) m) := by
  set φ : C(Ω, ℝ) →ₐ[ℝ] (Ω → ℝ) := ContinuousMap.coeFnAlgHom (α := Ω) (A := ℝ) ℝ
  set w : Fin 2 → MvPolynomial (Fin 3) C(Ω, ℝ) :=
    ![∑ i, X i * C ⟨fun q => u q i, (continuous_apply i).comp hu⟩,
      ∑ i, X i * C ⟨fun q => v q i, (continuous_apply i).comp hv⟩]
  have hw : ![dp u, dp v] = fun r => mapAlgHom φ (w r) := by
    funext r
    set_option synthInstance.maxHeartbeats 100000 in
      fin_cases r <;> simp [w, dp, mapAlgHom_apply] <;>
        apply Finset.sum_congr rfl <;> intro i hi <;> congr 2 <;> funext q <;> rfl
  rw [pp, hw, ← comp_aeval, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]
  exact (AddMonoidAlgebra.coeff (aeval w Q) m).continuous

theorem continuous_ell (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (Q : MvPolynomial (Fin 2) ℝ) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => ℓ (aeval ![lin3 p.1, lin3 p.2] Q) := by
  have h := ell_pp ℓ (Prod.fst : (Fin 3 → ℝ) × (Fin 3 → ℝ) → _) Prod.snd Q
  simp only [h]
  exact continuous_finsetSum _ fun m _ =>
    (continuous_coeff_pp _ _ continuous_fst continuous_snd Q m).mul continuous_const

def ker (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ := (1 / 2) * Real.log ((1 - ∑ i, p.1 i * p.2 i) / 2)

theorem measurable_ker : Measurable ker := by
  have hc : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (1 - ∑ i, p.1 i * p.2 i) / 2 := by fun_prop
  exact (Real.measurable_log.comp hc.measurable).const_mul (1 / 2)

theorem ker_crd (p : S2 × S2) : ker (crd p.1, crd p.2) = wwLogWeight p := by
  have h : ∑ i, crd p.1 i * crd p.2 i = inner ℝ (p.1 : E3) (p.2 : E3) := by
    simp [crd, PiLp.inner_apply, mul_comm]
  simp only [ker, wwLogWeight, h]

theorem pp_eq (Q : MvPolynomial (Fin 2) ℝ) :
    pp (fun p : S2 × S2 => crd p.1) (fun p => crd p.2) Q =
      aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q := rfl

theorem ell_moment (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (Q : MvPolynomial (Fin 2) ℝ) :
    ℓ (momentPoly (sphereMeasure.prod sphereMeasure) wwLogWeight
        (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) =
      ∫ p : S2 × S2, wwLogWeight p * ℓ (aeval ![lin3 (crd p.1), lin3 (crd p.2)] Q)
        ∂(sphereMeasure.prod sphereMeasure) := by
  have hI : ∀ m, Integrable (fun p => wwLogWeight p *
      AddMonoidAlgebra.coeff (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q) m p)
      (sphereMeasure.prod sphereMeasure) := fun m =>
    FibreLocal.integrable_mul _ (DiagFibreMoment.continuous_coeff_aeval Q m)
  have h := fun p : S2 × S2 => ell_pp ℓ (fun p : S2 × S2 => crd p.1) (fun p => crd p.2) Q p
  simp only [pp_eq] at h
  simp only [h, Finset.mul_sum]
  rw [integral_finsetSum _ fun m _ => by
    simpa only [mul_assoc] using (hI m).mul_const (ℓ (monomial m 1))]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [momentPoly, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [← mul_assoc]
  rw [integral_mul_const, ← mul_one (∫ p, _ ∂_), ← smul_eq_mul, ← smul_monomial, map_smul, smul_eq_mul,
    smul_eq_mul, mul_one]

theorem integral_eq_moment : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (Q : MvPolynomial (Fin 2) ℝ),
    ∫ p : ℂ × ℂ, logSin 1 p.1 p.2 * (wS p.1 * wS p.2 * ℓ (aeval ![lin3 (nS p.1), lin3 (nS p.2)] Q)) =
      Real.pi ^ 2 * ℓ (momentPoly (sphereMeasure.prod sphereMeasure) wwLogWeight
        (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) := by
  intro ℓ Q
  have hΦ : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ker p * ℓ (aeval ![lin3 p.1, lin3 p.2] Q) := measurable_ker.mul (continuous_ell ℓ Q).measurable
  have h := integral_pair _ hΦ
  rw [ell_moment]
  simp only [ker_crd] at h
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have hk : logSin 1 p.1 p.2 = ker (nS p.1, nS p.2) := (GlobalTheory.T.sphere_measure_stereographic_integral).2 p.1 p.2
  have hw : ∀ a, wS a = Real.pi * dens a := fun a => by
    have := Real.pi_ne_zero
    simp only [wS, dens]
    field_simp
  simp only [hk, hw]
  ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SpherePairLogSineMomentStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphere_pair_log_sine_moment : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (Q : MvPolynomial (Fin 2) ℝ),
    ∫ p : ℂ × ℂ, logSin 1 p.1 p.2 * (wS p.1 * wS p.2 * ℓ (aeval ![lin3 (nS p.1), lin3 (nS p.2)] Q)) =
      Real.pi ^ 2 * ℓ (momentPoly (sphereMeasure.prod sphereMeasure) wwLogWeight
        (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment <;> assumption)
end
end
