module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import Development.WeilBound.CoreStatements.FlagImmersions.MapProdLinear
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.WeilBound.CoreStatements.FlagImmersions.DegLApply
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
public import Development.WeilBound.CoreStatements.FlagImmersions.ShiftPowerSumMul
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConj
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConj
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem combLine_smooth_conj :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  intro K _ ι _ J _ ℓ n
  refine ⟨fun hs => ?_, fun hc => ?_, ?_⟩
  · refine contDiffOn_prod fun j _ => ?_
    intro z hz
    have h0 : (ℓ j).h z ≠ 0 := ((ℓ j).pos z hz).ne'
    have hf := hs j z hz
    have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (ℓ j).h z ^ m)
        {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
      intro m
      cases m with
      | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
      | negSucc k =>
        simp only [zpow_negSucc]
        exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
    exact key _
  · intro z
    show (∏ j, (ℓ j).h _ ^ n j) = ∏ j, (ℓ j).h z ^ n j
    simp only [hc _ z]
  · exact contDiffOn_const

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConjStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_combination_smooth_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj | exact GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CurveDegreeLinearNefCone
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.RootCoefWeightedSumSplit
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem root_coef_add {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' : ℝ)
    (j : Option (Ψ × Fin N)) : M.coef (lam + mu) (s + s') j = M.coef lam s j + M.coef mu s' j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.add_apply]; ring

theorem root_coef_smul {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam : Wt Ψ N) (a s : ℝ)
    (j : Option (Ψ × Fin N)) : M.coef (a • lam) (a * s) j = a * M.coef lam s j := by
  cases j with
  | none => simp only [RootModel.coef, mul_div_assoc]
  | some r => simp only [RootModel.coef, Pi.smul_apply, smul_eq_mul]; ring

theorem root_coef_split {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ)
    (j : Option (Ψ × Fin N)) : M.coef lam s j = M.coef lam 0 j + s * M.coef 0 1 j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.zero_apply]; ring

theorem root_coef_weighted_sum_split {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ)
    (g : Option (Ψ × Fin N) → ℝ) :
    ∑ j, M.coef lam s j * g j = ∑ j, M.coef lam 0 j * g j + s * ∑ j, M.coef 0 1 j * g j := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [root_coef_split M lam s j]
  ring

end RootFieldNumerics

theorem RootFieldNumerics.curveDeg_linear_and_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' a : ℝ), (∀ W, M.curveDeg (lam + mu) (s + s') W = M.curveDeg lam s W + M.curveDeg mu s' W) ∧ (∀ W, M.curveDeg (a • lam) (a * s) W = a * M.curveDeg lam s W) ∧ (∀ p, 0 ≤ s → M.NefAt p lam 0 → M.NefAt p 0 1 → M.NefAt p lam s) ∧ (0 ≤ s → M.NefGen lam 0 → M.NefGen 0 1 → M.NefGen lam s) := by
  intro Ψ _ N M lam mu s s' a
  refine ⟨fun W => ?_, fun W => ?_, fun p hs h1 h2 W hW => ?_, fun hs h1 h2 W hW hP => ?_⟩
  · simp only [RootModel.curveDeg]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [RootFieldNumerics.root_coef_add]; ring
  · simp only [RootModel.curveDeg]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [RootFieldNumerics.root_coef_smul]; ring
  · have e : M.curveDeg lam s W = M.curveDeg lam 0 W + s * M.curveDeg 0 1 W :=
      RootFieldNumerics.root_coef_weighted_sum_split M lam s _
    rw [e]
    exact add_nonneg (h1 W hW) (mul_nonneg hs (h2 W hW))
  · have e : ∑ j, M.coef lam s j * geomDeg W (M.line 1 j) 1
        = ∑ j, M.coef lam 0 j * geomDeg W (M.line 1 j) 1
          + s * ∑ j, M.coef 0 1 j * geomDeg W (M.line 1 j) 1 :=
      RootFieldNumerics.root_coef_weighted_sum_split M lam s _
    rw [e]
    exact add_nonneg (h1 W hW hP) (mul_nonneg hs (h2 W hW hP))
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CurveDegreeLinearNefCone
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem curveDeg_linear_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' a : ℝ), (∀ W, M.curveDeg (lam + mu) (s + s') W = M.curveDeg lam s W + M.curveDeg mu s' W) ∧ (∀ W, M.curveDeg (a • lam) (a * s) W = a * M.curveDeg lam s W) ∧ (∀ p, 0 ≤ s → M.NefAt p lam 0 → M.NefAt p 0 1 → M.NefAt p lam s) ∧ (0 ≤ s → M.NefGen lam 0 → M.NefGen 0 1 → M.NefGen lam s) :=
  @RootFieldNumerics.curveDeg_linear_and_nef

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CurveDegreeLinearNefConeStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_degree_linear_nef_cone : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' a : ℝ), (∀ W, M.curveDeg (lam + mu) (s + s') W = M.curveDeg lam s W + M.curveDeg mu s' W) ∧ (∀ W, M.curveDeg (a • lam) (a * s) W = a * M.curveDeg lam s W) ∧ (∀ p, 0 ≤ s → M.NefAt p lam 0 → M.NefAt p 0 1 → M.NefAt p lam s) ∧ (0 ≤ s → M.NefGen lam 0 → M.NefGen 0 1 → M.NefGen lam s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.curveDeg_linear_nef | exact GlobalTheory.CompanionTheory.Ar.Top.curveDeg_linear_nef | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.curveDeg_linear_nef <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MassFormulaConjugationAction
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardCount
namespace ListOfFnPermExistsEquivPerm

open Finset in
private theorem card_count {α : Type} [DecidableEq α] :
    ∀ {n : ℕ} (v : Fin n → α) (a : α), #{i | v i = a} = (List.ofFn v).count a
  | 0, v, a => by simp
  | n + 1, v, a => by
    have ih := card_count (fun i : Fin n => v i.succ) a
    rw [Fin.card_filter_univ_succ', List.ofFn_succ, List.count_cons, ih]
    by_cases h : v 0 = a <;> simp [h, add_comm]

end ListOfFnPermExistsEquivPerm

theorem UpperTheory.Reformulated.B.Yde7.main :
    ∀ {α : Type} {n : ℕ} (v w : Fin n → α),
      (List.ofFn v).Perm (List.ofFn w) → ∃ (s : Equiv.Perm (Fin n)), v = w ∘ (⇑s : Fin n → Fin n) := by
  intro α n v w h
  classical
  have hc : ∀ c, Fintype.card {i // v i = c} = Fintype.card {i // w i = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert (ListOfFnPermExistsEquivPerm.card_count v c).trans ((h.count_eq c).trans (ListOfFnPermExistsEquivPerm.card_count w c).symm)
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm
end

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section Lin

variable {K : Type} [Fintype K] {ι : K → Type} {σ : Type}
  (I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
  (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (A : σ → HermLine ι)

theorem arNum_eq_sum_of_subset (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)) (hs : H.support ⊆ s) :
    arNum I P A H = ∑ μ ∈ s, H.coeff μ * arList I P (μ.toMultiset.map A).toList := by
  unfold arNum
  refine Finset.sum_subset hs fun μ _ hμ => ?_
  rw [MvPolynomial.notMem_support_iff.1 hμ, zero_mul]

theorem arNum_add' (H H' : MvPolynomial σ ℝ) :
    arNum I P A (H + H') = arNum I P A H + arNum I P A H' := by
  classical
  rw [arNum_eq_sum_of_subset I P A (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
    arNum_eq_sum_of_subset I P A H (H.support ∪ H'.support) Finset.subset_union_left,
    arNum_eq_sum_of_subset I P A H' (H.support ∪ H'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem arNum_C_mul' (c : ℝ) (H : MvPolynomial σ ℝ) :
    arNum I P A (C c * H) = c * arNum I P A H := by
  have hs : (C c * H).support ⊆ H.support := by
    intro μ hμ
    rw [MvPolynomial.mem_support_iff] at hμ ⊢
    intro h0
    exact hμ (by rw [MvPolynomial.coeff_C_mul, h0, mul_zero])
  rw [arNum_eq_sum_of_subset I P A (C c * H) H.support hs, arNum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_C_mul, mul_assoc]

theorem arNum_zero' : arNum I P A (0 : MvPolynomial σ ℝ) = 0 := by
  simp [arNum]

theorem arNum_sum' {α : Type} (s : Finset α) (H : α → MvPolynomial σ ℝ) :
    arNum I P A (∑ a ∈ s, H a) = ∑ a ∈ s, arNum I P A (H a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using arNum_zero' I P A
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, arNum_add', ih]

theorem arNum_monomial' (μ : σ →₀ ℕ) (c : ℝ) :
    arNum I P A (monomial μ c) = c * arList I P (μ.toMultiset.map A).toList := by
  classical
  rw [arNum_eq_sum_of_subset I P A (monomial μ c) {μ} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem arNum_rename' {σ' : Type} (e : σ' → σ) (H : MvPolynomial σ' ℝ) :
    arNum I P A (rename e H) = arNum I P (A ∘ e) H := by
  classical
  induction H using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [MvPolynomial.rename_monomial, arNum_monomial', arNum_monomial',
      show Finsupp.toMultiset (Finsupp.mapDomain e μ) = (Finsupp.toMultiset μ).map e from
        (Finsupp.toMultiset_map _ _).symm, Multiset.map_map]
  | add p q hp hq => rw [map_add (f := _), arNum_add', arNum_add', hp, hq]

end Lin

theorem exists_perm_of_ofFn_perm' {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : (List.ofFn v).Perm (List.ofFn w)) : ∃ s : Equiv.Perm (Fin n), v = w ∘ s :=
  _root_.UpperTheory.Reformulated.B.Yde7.main v w h

theorem arList_eq_of_perm {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1))
    {I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    (l : List (HermLine ι)) (L : Fin (D + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j))
    (hp : l.Perm (List.ofFn L)) : arList I P l = I P (D + 1) L := by
  have key : ∀ (m : ℕ) (v : Fin m → HermLine ι), (List.ofFn v).Perm (List.ofFn L) →
      I P m v = I P (D + 1) L := by
    intro m v h
    have hm : m = D + 1 := by simpa using h.length_eq
    subst hm
    obtain ⟨s, rfl⟩ := exists_perm_of_ofFn_perm' v L h
    exact hI.1 P _ L s hP hL
  refine key l.length l.get ?_
  rwa [List.ofFn_get]

theorem arNum_linear_arList_symm : (∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι ℤ)) (σ : Type) (A : σ → HermLine ι), (∀ H H' : MvPolynomial σ ℝ, arNum I P A (H + H') = arNum I P A H + arNum I P A H') ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), arNum I P A (C c * H) = c * arNum I P A H) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), arNum I P A (∑ a ∈ s, H a) = ∑ a ∈ s, arNum I P A (H a)) ∧ (∀ (μ : σ →₀ ℕ) (c : ℝ), arNum I P A (monomial μ c) = c * arList I P (μ.toMultiset.map A).toList) ∧ ∀ (σ' : Type) (e : σ' → σ) (H : MvPolynomial σ' ℝ), arNum I P A (rename e H) = arNum I P (A ∘ e) H) ∧ (∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (l : List (HermLine ι)) (L : Fin (D + 1) → HermLine ι), (∀ j, IsSmoothHerm (L j)) → l.Perm (List.ofFn L) → arList I P l = I P (D + 1) L) := by
  refine ⟨?_, ?_⟩
  · intro K _ _ ι _ I P σ A
    exact ⟨arNum_add' I P A, arNum_C_mul' I P A, fun α s H => arNum_sum' I P A s H,
      arNum_monomial' I P A, fun σ' e H => arNum_rename' I P A e H⟩
  · intro K _ _ ι _ P D hP I hI l L hL hp
    exact arList_eq_of_perm hP hI l L hL hp

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FunctionalProductLinearForms
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.LinearFunctionalProductExpansion
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.linear_functional_product_expansion : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (c : Fin d → J → ℝ), Φ (∏ k, ∑ j, C (c k j) * X j) = ∑ w : Fin d → J, (∏ k, c k (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  intro J _ _ d Φ c
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.monomial_sum_one, C_mul', map_smul, smul_eq_mul]
  rfl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FunctionalProductLinearForms
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem linearFunctional_prod_linearForms : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (c : Fin d → J → ℝ), Φ (∏ k, ∑ j, C (c k j) * X j) = ∑ w : Fin d → J, (∏ k, c k (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  exact @RootFieldNumerics.linear_functional_product_expansion

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FunctionalProductLinearFormsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_product_linear_forms : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (c : Fin d → J → ℝ), Φ (∏ k, ∑ j, C (c k j) * X j) = ∑ w : Fin d → J, (∏ k, c k (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.linearFunctional_prod_linearForms | exact GlobalTheory.CompanionTheory.Ar.Top.linearFunctional_prod_linearForms | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.linearFunctional_prod_linearForms <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralCongrSmul
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralCongrSmul
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ptsIntegral_congr_and_homog :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (e : ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ), (∀ g g' : ((Σ k, ι k) → ℂ) → ℝ, (∀ z ∈ mcPts P, g z = g' z) → ptsIntegral P φ g = ptsIntegral P φ g') ∧ ∀ (c : ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ), ptsIntegral P φ (fun z => c * g z) = c * ptsIntegral P φ g := by
  classical
  intro K _ _ ι _ P e φ
  refine ⟨fun g g' hg => ?_, fun c g => ?_⟩
  · exact (ReciprocityTheory.ChartRestriction.G.Geo.ptsLocal K ι P e 0 φ φ g g' (fun _ _ _ => rfl) hg).2
  · unfold ptsIntegral
    split_ifs with h
    · unfold ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegralAt
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      funext y
      have : ∀ w, ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity P h.choose φ (fun z => c * g z) y w =
          c * ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity P h.choose φ g y w := by
        intro w
        unfold ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity
        split_ifs <;> ring
      simp only [this]
      rw [← mul_finsum_mem]
    · simp

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralCongrSmulStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_integral_congr_smul : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (e : ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ), (∀ g g' : ((Σ k, ι k) → ℂ) → ℝ, (∀ z ∈ mcPts P, g z = g' z) → ptsIntegral P φ g = ptsIntegral P φ g') ∧ ∀ (c : ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ), ptsIntegral P φ (fun z => c * g z) = c * ptsIntegral P φ g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_congr_and_homog | exact GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_congr_and_homog | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_congr_and_homog <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivCycleMapLocalisation
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxSynthPendingDepth 1


attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem GlobalTheory.CompanionTheory.Ar.Num.divCycle_map_localisation :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (Mo : Submonoid R) [IsLocalization Mo R'] (P : Ideal (MRing ι R)) (f : MRing ι R) (W' : Ideal (MRing ι R')), W'.IsPrime → divCycle (P.map (MvPolynomial.map (algebraMap R R'))) (MvPolynomial.map (algebraMap R R') f) W' = divCycle P f (W'.comap (MvPolynomial.map (algebraMap R R'))) := by
  intro K _ _ ι _ R R' _ _ _ Mo _ P f W' hW'
  classical
  let φ : MRing ι R →+* MRing ι R' := MvPolynomial.map (algebraMap R R')
  let M : Submonoid (MRing ι R) := Mo.map (C (σ := (Σ k, ι k)) (R := R))
  have : IsLocalization M (MRing ι R') := MvPolynomial.isLocalization Mo R'
  have hφ : algebraMap (MRing ι R) (MRing ι R') = φ := rfl
  set J := P ⊔ Ideal.span {f} with hJdef
  have hJ : P.map φ ⊔ Ideal.span {φ f} = J.map (algebraMap (MRing ι R) (MRing ι R')) := by
    rw [hφ, hJdef, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hdisj : Disjoint (M : Set (MRing ι R)) (W'.comap (algebraMap (MRing ι R) (MRing ι R'))) :=
    (IsLocalization.isPrime_iff_isPrime_disjoint M (MRing ι R') W').mp hW' |>.2
  have hWp : (W'.comap (algebraMap (MRing ι R) (MRing ι R'))).IsPrime := Ideal.comap_isPrime _ _
  have hmap : (W'.comap (algebraMap (MRing ι R) (MRing ι R'))).map
      (algebraMap (MRing ι R) (MRing ι R')) = W' := IsLocalization.map_under M _ W'
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = W'.comap (algebraMap (MRing ι R) (MRing ι R')) := ⟨_, rfl⟩
  rw [← hQ] at hdisj hWp hmap
  subst hmap
  have hmin : Q.map (algebraMap (MRing ι R) (MRing ι R')) ∈ (P.map φ ⊔ Ideal.span {φ f}).minimalPrimes ↔
      Q ∈ J.minimalPrimes := by
    rw [hJ, IsLocalization.minimalPrimes_map M]
    show (Q.map (algebraMap (MRing ι R) (MRing ι R'))).comap
      (algebraMap (MRing ι R) (MRing ι R')) ∈ J.minimalPrimes ↔ _
    rw [← hQ]
  have hrel : IsRelevant (Q.map (algebraMap (MRing ι R) (MRing ι R'))) ↔ IsRelevant Q := by
    refine forall_congr' fun k => exists_congr fun i => not_congr ?_
    have hX : (X ⟨k, i⟩ : MRing ι R') =
        algebraMap (MRing ι R) (MRing ι R') (X ⟨k, i⟩) := (MvPolynomial.map_X _ _).symm
    rw [hX, ← Ideal.mem_comap, ← hQ]
  have hl : ∀ (h₁ : Q.IsPrime) (h₂ : (Q.map (algebraMap (MRing ι R) (MRing ι R'))).IsPrime),
      @multAt _ _ _ _ J Q h₁ =
        @multAt _ _ _ _ (P.map φ ⊔ Ideal.span {φ f})
          (Q.map (algebraMap (MRing ι R) (MRing ι R'))) h₂ := by
    intro h₁ h₂
    unfold multAt
    rw [hJ]
    exact GenericCycleCorresp.length_eq M J Q hdisj
  have hQ' : Ideal.comap (MvPolynomial.map (algebraMap R R') : MRing ι R →+* MRing ι R')
      (Q.map (algebraMap (MRing ι R) (MRing ι R'))) = Q := hQ.symm
  rw [hQ']
  change divCycle (P.map φ) (φ f) _ = divCycle P f Q
  unfold divCycle
  by_cases hc : Q ∈ J.minimalPrimes ∧ IsRelevant Q
  · rw [dite_eq_left ⟨hmin.mpr hc.1, hrel.mpr hc.2⟩, dite_eq_left hc, hl]
  · rw [dite_eq_right (fun h => hc ⟨hmin.mp h.1, hrel.mp h.2⟩), dite_eq_right hc]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffs
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.ExistsIntegerCoefficientsRational
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem exists_clear_denominators_bis {J : Type} [Fintype J] (c : J → ℚ) :
    ∃ (q : ℕ) (n : J → ℤ), 0 < q ∧ ∀ j, (n j : ℚ) = q * c j := by
  classical
  refine ⟨∏ i, (c i).den, fun j => (c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ), ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => (c i).den_pos)
  · intro j
    obtain ⟨k, hk⟩ : (c j).den ∣ ∏ i, (c i).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    show (((c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ) : ℤ) : ℚ) = ((∏ i, (c i).den : ℕ) : ℚ) * c j
    rw [hk, Nat.mul_div_cancel_left _ (c j).den_pos]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

end RootFieldNumerics

theorem RootFieldNumerics.exists_integer_coefficients_rational : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j := by
  intro Ψ _ N M lam s hlam
  classical
  choose f hf using hlam
  let c : Option (Ψ × Fin N) → ℚ := fun j => match j with
    | some r => -f r.1 r.2
    | none => s / M.kA
  obtain ⟨q, n, hq, hn⟩ := RootFieldNumerics.exists_clear_denominators_bis c
  refine ⟨q, n, hq, fun j => ?_⟩
  have h : ((n j : ℚ) : ℝ) = ((q * c j : ℚ) : ℝ) := by rw [hn j]
  push_cast at h
  rw [h]
  congr 1
  cases j with
  | none => simp [c, RootModel.coef]
  | some r => simp [c, RootModel.coef, hf]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffs
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem clear_rat_weight_coef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j :=
  @RootFieldNumerics.exists_integer_coefficients_rational

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_weight_integral_coeffs : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.clear_rat_weight_coef | exact GlobalTheory.CompanionTheory.Ar.Top.clear_rat_weight_coef | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.clear_rat_weight_coef <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoSeriesThreeStep
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem co_series_three_step : (∀ (Sg : Type) [Fintype Sg] [DecidableEq Sg] (φ : Equiv.Perm Sg) (p k : ℕ), 2 ≤ p → 1 ≤ k → ∀ (La : Sg → ℝ) (τ : Sg), ∑ σ, co φ p k τ σ * La σ = (∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * La ((φ ^ (n + 1)) τ)) - La τ / ((p : ℝ) - 1)) ∧ (∀ (Sg : Type) (φ : Equiv.Perm Sg) (p k : ℕ), 2 ≤ p → ∀ (La : Sg → ℝ) (q : ℕ → Sg → ℝ), (∀ r τ, q r τ = ((p : ℝ) ^ ((r + 1) * k))⁻¹ * La ((φ ^ (r + 1)) τ) + q (r + 1) τ) → (∀ r τ, q (r + 1) τ = ((p : ℝ) ^ k)⁻¹ * q r (φ τ)) → ∀ τ, (p : ℝ) ^ k * q 0 τ = q 0 (φ τ) + La (φ τ)) := by
  refine ⟨?_, ?_⟩
  · intro Sg _ _ φ p k hp hk La τ
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hpk1 : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
    have hpk0 : (0 : ℝ) < (p : ℝ) ^ k := by linarith
    set r : ℝ := ((p : ℝ) ^ k)⁻¹ with hr
    have hr0 : 0 ≤ r := (inv_pos.mpr hpk0).le
    have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hpk1
    have hgeo : Summable (fun n : ℕ => r ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
    have hterm : ∀ σ n, returnTerm φ p k τ σ n = if (φ ^ (n + 1)) τ = σ then r ^ (n + 1) else 0 := by
      intro σ n
      simp only [returnTerm, one_div, hr]
    have hsum : ∀ σ, Summable (returnTerm φ p k τ σ) := by
      intro σ
      refine Summable.of_norm_bounded hgeo ?_
      intro n
      rw [hterm]
      split_ifs
      · rw [Real.norm_of_nonneg (pow_nonneg hr0 _)]
      · simpa using pow_nonneg hr0 (n + 1)
    have hsum' : ∀ σ, Summable (fun n => returnTerm φ p k τ σ n * La σ) :=
      fun σ => (hsum σ).mul_right _
    have hinner : ∀ n : ℕ, ∑ σ, returnTerm φ p k τ σ n * La σ = r ^ (n + 1) * La ((φ ^ (n + 1)) τ) := by
      intro n
      rw [Finset.sum_eq_single ((φ ^ (n + 1)) τ)]
      · rw [hterm, if_pos rfl]
      · intro b _ hb
        rw [hterm, if_neg (Ne.symm hb), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hswap : ∑ σ, (∑' n, returnTerm φ p k τ σ n) * La σ =
        ∑' n : ℕ, r ^ (n + 1) * La ((φ ^ (n + 1)) τ) := by
      simp_rw [← tsum_mul_right]
      rw [← Summable.tsum_finsetSum (fun σ _ => hsum' σ)]
      exact tsum_congr hinner
    have hlast : ∑ σ, (if σ = τ then 1 / ((p : ℝ) - 1) else 0) * La σ = La τ / ((p : ℝ) - 1) := by
      rw [Finset.sum_eq_single τ]
      · rw [if_pos rfl]; ring
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    simp only [co, sub_mul]
    rw [Finset.sum_sub_distrib, hswap, hlast]
  · intro Sg φ p k hp La q h1 h2 τ
    have hp0 : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : p ≠ 0))
    have a := h1 0 τ
    have b := h2 0 τ
    simp only [zero_add, one_mul, pow_one] at a b
    rw [a, b]
    field_simp
    ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerHeightIdentityExpansion
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.TowerPointCountIdentity
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem degFl_sum' {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {ι : Type} (s : Finset ι)
    (f : ι → RP Ψ N) : degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  unfold degFl
  simp only [MvPolynomial.coeff_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
private theorem Sh_sum {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {ι : Type} (j : ℕ) (τ : Ψ)
    (s : Finset ι) (f : ι → RP Ψ N) : Sh j τ (∑ i ∈ s, f i) = ∑ i ∈ s, Sh j τ (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Sh, map_sum]
  rw [Finset.sum_comm, degFl_sum']
private theorem Tot_sum {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {ι : Type} (τ : Ψ)
    (s : Finset ι) (f : ι → RP Ψ N) : Tot τ (∑ i ∈ s, f i) = ∑ i ∈ s, Tot τ (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Tot, map_sum]
  rw [Finset.sum_comm, degFl_sum']
private theorem PPt_sum {Ψ : Type} [Fintype Ψ] {N : ℕ} {ι : Type} (T : RootTower Ψ N)
    (II : IntersectionSystem) (B : ℕ) (s : Finset ι) (f : ι → RP Ψ N) :
    T.PPt II B (∑ i ∈ s, f i) = ∑ i ∈ s, T.PPt II B (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RootTower.PPt, RootTower.PPc, toA, map_sum]
  rw [Finset.sum_comm]

theorem tower_point_count_identity : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (A₀ b₀ : ℝ) (F : RP Ψ N) (Q : Ψ → ℕ → RP Ψ N), T.IdentAt II hh frob B₀ A₀ b₀ → IsDecomp F Q → T.PPt II B₀ F = T.volT * (hh F - A₀ * ∑ σ, Sh T.j σ F - b₀ * ∑ σ, Tot σ F + ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B₀ τ k (Q τ k)) := by
  intro II Ψ _ _ N T hh frob B₀ A₀ b₀ F Q hI hD
  obtain ⟨hQ, rfl⟩ := hD
  have key : ∀ τ, ∀ k ∈ Finset.Icc 1 N, T.PPt II B₀ (pk τ k * Q τ k) = T.volT * (hh (pk τ k * Q τ k)
      - A₀ * ∑ σ, Sh T.j σ (pk τ k * Q τ k) - b₀ * ∑ σ, Tot σ (pk τ k * Q τ k)
      + restSum T.j T.bad frob B₀ τ k (Q τ k)) := by
    intro τ k hk
    have hk' := Finset.mem_Icc.1 hk
    exact hI τ k hk'.1 hk'.2 _ (hQ τ k hk'.1 hk'.2)
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [PPt_sum, map_sum, Sh_sum, Tot_sum]
  rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (key τ))]
  have e1 : ∑ σ, ∑ τ, ∑ k ∈ Finset.Icc 1 N, Sh T.j σ (pk τ k * Q τ k)
      = ∑ τ, ∑ k ∈ Finset.Icc 1 N, ∑ σ, Sh T.j σ (pk τ k * Q τ k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have e2 : ∑ σ, ∑ τ, ∑ k ∈ Finset.Icc 1 N, Tot σ (pk τ k * Q τ k)
      = ∑ τ, ∑ k ∈ Finset.Icc 1 N, ∑ σ, Tot σ (pk τ k * Q τ k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [e1, e2]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]

end RootFieldNumerics
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerHeightIdentityExpansion
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem identOnDecomposedForm : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (A₀ b₀ : ℝ) (F : RP Ψ N) (Q : Ψ → ℕ → RP Ψ N), T.IdentAt II hh frob B₀ A₀ b₀ → IsDecomp F Q → T.PPt II B₀ F = T.volT * (hh F - A₀ * ∑ σ, Sh T.j σ F - b₀ * ∑ σ, Tot σ F + ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B₀ τ k (Q τ k)) :=
  @RootFieldNumerics.tower_point_count_identity

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerHeightIdentityExpansionStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_height_identity_expansion : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (A₀ b₀ : ℝ) (F : RP Ψ N) (Q : Ψ → ℕ → RP Ψ N), T.IdentAt II hh frob B₀ A₀ b₀ → IsDecomp F Q → T.PPt II B₀ F = T.volT * (hh F - A₀ * ∑ σ, Sh T.j σ F - b₀ * ∑ σ, Tot σ F + ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B₀ τ k (Q τ k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.identOnDecomposedForm | exact GlobalTheory.CompanionTheory.Ar.Top.identOnDecomposedForm | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.identOnDecomposedForm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartRingLocalizationMembership
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartRingLocalizationMembership
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

theorem GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, ι k), segreVec y c ≠ 0 → ∀ t : Ω, t ∈ chartRing O (segreVec y) c ↔ ∃ s : A, s ∉ m ∧ algebraMap A Ω s * t ∈ chartRing ℤ (segreVec y) c := by
  intro K _ _ ι _ Ω _ y A _ _ hA m _ O _ _ _ _ _ _ _ c hc t
  have hconst : ∀ a : A, algebraMap A Ω a ∈ chartRing ℤ (segreVec y) c := hA c hc
  have hmul : ∀ {a b : A}, a ∉ m → b ∉ m → a * b ∉ m := fun ha hb h =>
    (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha hb
  constructor
  · intro ht
    induction ht using Algebra.adjoin_induction with
    | mem a ha =>
      refine ⟨1, fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one m).2 h), ?_⟩
      rw [map_one, one_mul]
      exact Algebra.subset_adjoin ha
    | algebraMap o =>
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl o
      refine ⟨s, s.2, ?_⟩
      have h' : algebraMap A Ω (s : A) * algebraMap O Ω o = algebraMap A Ω a := by
        rw [IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω a, ← map_mul,
          mul_comm, h]
      rw [h']
      exact hconst a
    | add a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨r, hr, hb⟩ := hb
      refine ⟨s * r, hmul hs hr, ?_⟩
      have : algebraMap A Ω (s * r) * (a + b) =
          algebraMap A Ω r * (algebraMap A Ω s * a) + algebraMap A Ω s * (algebraMap A Ω r * b) := by
        rw [map_mul]; ring
      rw [this]
      exact add_mem (mul_mem (hconst r) ha) (mul_mem (hconst s) hb)
    | mul a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨r, hr, hb⟩ := hb
      refine ⟨s * r, hmul hs hr, ?_⟩
      have : algebraMap A Ω (s * r) * (a * b) = (algebraMap A Ω s * a) * (algebraMap A Ω r * b) := by
        rw [map_mul]; ring
      rw [this]
      exact mul_mem ha hb
  · rintro ⟨s, hs, ht⟩
    have hle : ∀ {a : Ω}, a ∈ chartRing ℤ (segreVec y) c → a ∈ chartRing O (segreVec y) c := by
      intro a ha
      induction ha using Algebra.adjoin_induction with
      | mem a ha => exact Algebra.subset_adjoin ha
      | algebraMap n =>
        have : algebraMap ℤ Ω n = algebraMap O Ω (n : O) := by simp
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      | add a b _ _ ha hb => exact add_mem ha hb
      | mul a b _ _ ha hb => exact mul_mem ha hb
    obtain ⟨u, hu⟩ := IsLocalization.map_units O (⟨s, hs⟩ : m.primeCompl)
    have hu' : (u : O) = algebraMap A O s := hu
    have hinv : algebraMap O Ω ((u⁻¹ : Oˣ) : O) * algebraMap A Ω s = 1 := by
      rw [IsScalarTower.algebraMap_apply A O Ω, ← hu', ← map_mul, Units.inv_mul, map_one]
    have : t = algebraMap O Ω ((u⁻¹ : Oˣ) : O) * (algebraMap A Ω s * t) := by
      rw [← mul_assoc, hinv, one_mul]
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) (hle ht)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartRingLocalizationMembershipStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ring_localization_membership : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, ι k), segreVec y c ≠ 0 → ∀ t : Ω, t ∈ chartRing O (segreVec y) c ↔ ∃ s : A, s ∉ m ∧ algebraMap A Ω s * t ∈ chartRing ℤ (segreVec y) c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff | exact GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CutoffCoefficientsBound
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CutoffCoefficientsBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

private theorem card_lt_lemma {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter fun i : Fin N => (i : ℕ) < j).card = j := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (show {i : Fin N // (i : ℕ) < j} ≃ Fin j from
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, lt_of_lt_of_le y.2 hj⟩, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl })]
  exact Fintype.card_fin j

theorem flag_degree_low_zero {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (hj : j ≤ N) (τ : Ψ) (Q : RP Ψ N) :
    degFl (pkLow j τ 0 * Q) = j * degFl Q := by
  have hp : (pkLow j τ 0 : RP Ψ N) = C (j : ℝ) := by
    unfold pkLow
    simp only [pow_zero, Finset.sum_const, card_lt_lemma hj, nsmul_eq_mul, mul_one]
    exact (map_natCast C j).symm
  rw [hp]
  unfold degFl
  simp only [coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem flat_85_bound : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C rd Lval : ℝ) (B₀ : ℕ) (A₀ b₀ : ℝ), T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C rd Lval → 128 ≤ B₀ → T.bad.card ≤ B₀ → T.IdentAt II hh frob B₀ A₀ b₀ → |T.j * A₀ + N * b₀| ≤ C * N * bigLam B₀ rd Lval := by
  intro II Ψ _ _ N T _ hh frob C rd Lval B₀ A₀ b₀ hP hI9 hF hB hbad hId
  unfold RootTower.Proportional at hP
  unfold I9 at hI9
  obtain ⟨τ⟩ := ‹Nonempty Ψ›
  obtain ⟨⟨Q, hQ, hdeg⟩, -⟩ := testForms_sh_tot Ψ N T.j τ T.j_pos T.j_lt
  obtain ⟨h, hPP, hbd⟩ := hF
  have hN : 1 ≤ N := le_trans T.j_pos T.j_lt.le
  have hQ' : Q.IsHomogeneous (dimFl Ψ N + 1 - 1) := by simpa using hQ
  have hid := hId τ 1 le_rfl hN Q hQ'
  have hhh : hh (pk τ 1 * Q) = 0 := hI9.2.2 τ Q hQ
  have hSh : ∀ σ, Sh T.j σ (pk τ 1 * Q) = if σ = τ then (T.j : ℝ) else 0 := by
    intro σ
    rw [(RootFieldNumerics.shift_power_sum_mul Ψ N T.j τ σ 1 Q le_rfl).1]
    simp [flag_degree_low_zero T.j T.j_lt.le τ Q, hdeg]
  have hTot : ∀ σ, Tot σ (pk τ 1 * Q) = if σ = τ then (N : ℝ) else 0 := by
    intro σ
    rw [(RootFieldNumerics.shift_power_sum_mul Ψ N T.j τ σ 1 Q le_rfl).2]
    simp [hdeg]
  have hrest : restSum T.j T.bad frob B₀ τ 1 Q = 0 := by
    simp [restSum, restTerm]
  have hL : T.PPt II B₀ (pk τ 1 * Q) = ∑ c, h B₀ c τ * T.vol c := by
    unfold RootTower.PPt
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hPP B₀ (by omega) c τ Q hQ, hdeg, mul_one]
  rw [hL, hhh, hrest] at hid
  simp only [hSh, hTot, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at hid
  have hvol : 0 < T.volT := Finset.sum_pos (fun c _ => hP.1 c) Finset.univ_nonempty
  have hv0 : T.volT ≠ 0 := hvol.ne'
  have key : (T.j : ℝ) * A₀ + N * b₀ = -(∑ c, h B₀ c τ * T.vol c) / T.volT := by
    rw [hid]
    field_simp
    ring
  rw [key, abs_div, abs_neg, abs_of_pos hvol, div_le_iff₀ hvol]
  calc |∑ c, h B₀ c τ * T.vol c| ≤ ∑ c, |h B₀ c τ * T.vol c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, |h B₀ c τ| * T.vol c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [abs_mul, abs_of_pos (hP.1 c)]
    _ ≤ ∑ c, C * N * bigLam B₀ rd Lval * T.vol c := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact mul_le_mul_of_nonneg_right (hbd B₀ hB hbad c τ) (hP.1 c).le
    _ = C * N * bigLam B₀ rd Lval * T.volT := by
        rw [← Finset.mul_sum]
        rfl

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CutoffCoefficientsBoundStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_coefficients_bound : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C rd Lval : ℝ) (B₀ : ℕ) (A₀ b₀ : ℝ), T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C rd Lval → 128 ≤ B₀ → T.bad.card ≤ B₀ → T.IdentAt II hh frob B₀ A₀ b₀ → |T.j * A₀ + N * b₀| ≤ C * N * bigLam B₀ rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flat_85_bound | exact GlobalTheory.CompanionTheory.Ar.Top.flat_85_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flat_85_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelCurveDegreeNef
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.RootModelCurveDegreeNef
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem geoNum_one_linear_in_degree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) :
    ∃ c : K → ℤ, ∀ a : K → ℤ, geoNum 1 W (fun _ => a) = ∑ k, a k * c k := by
  classical
  refine ⟨fun k => geoNum 1 W (fun _ => Pi.single k 1), fun a => ?_⟩
  have hs : ∀ b : K → ℤ, (Fin.init (fun _ : Fin 1 => b) : Fin 0 → K → ℤ) = fun i => i.elim0 :=
    fun b => Subsingleton.elim _ _
  rw [geoNum.eq_2 (n := 0)]
  simp only [geoNum.eq_2 (n := 0), hs]
  split_ifs with h
  · simp [Pi.single_apply]
  · simp

theorem geoNum_linear_combination {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    {J : Type} [Fintype J] (n : J → ℤ) (b : J → K → ℤ) :
    geoNum 1 W (fun _ => ∑ j, n j • b j) = ∑ j, n j * geoNum 1 W (fun _ => b j) := by
  obtain ⟨c, hc⟩ := geoNum_one_linear_in_degree (K := K) W
  rw [hc]
  simp only [hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem char_prime_of_prime_ideal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (hW : W.IsPrime) (h : charOf W ≠ 0) : (charOf W).Prime := by
  classical
  set I : Ideal ℤ := Ideal.comap (C : ℤ →+* MRing ι) W with hI
  have hp : I.IsPrime := Ideal.IsPrime.comap _
  have hne : I ≠ ⊥ := by
    intro hb
    apply h
    have : Submodule.IsPrincipal.generator I = 0 :=
      (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mp hb
    simp [charOf, ← hI, this]
  have hg := Submodule.IsPrincipal.prime_generator_of_isPrime I hne
  have : charOf W = (Submodule.IsPrincipal.generator I).natAbs := by
    simp [charOf, ← hI]
  rw [this]
  exact Int.prime_iff_natAbs_prime.mp hg

theorem root_line_a_independent {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    (M.line t j).a = (M.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp only [RootModel.line, M.x_deg]

end RootFieldNumerics

theorem RootFieldNumerics.curveDeg_eq_and_nefOnFibres_of_coef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → (∀ W : Ideal (MRing M.ι), (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W) ∧ (M.NefFib lam s → NefOnFibres M.P (combLine (M.line t) n).a) := by
  intro Ψ _ N M t lam s q n hn
  have key : ∀ W : Ideal (MRing M.ι),
      (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W := by
    intro W
    rw [show (combLine (M.line t) n).a = ∑ j, n j • (M.line t j).a from rfl,
      geoNum_linear_combination W n (fun j => (M.line t j).a)]
    push_cast
    rw [RootModel.curveDeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [root_line_a_independent M t j, hn j]
    ring
  refine ⟨key, fun hN W hWp hPW hc hd => ?_⟩
  have hpr := char_prime_of_prime_ideal W hWp.1 hc
  have h0 := hN _ hpr W ⟨hWp, hPW, rfl, hd⟩
  have h1 : (0:ℝ) ≤ geoNum 1 W (fun _ => (combLine (M.line t) n).a) := by
    rw [key]
    exact mul_nonneg (Nat.cast_nonneg _) h0
  exact_mod_cast h1
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelCurveDegreeNef
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem nefFib_integral_multiple : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → (∀ W : Ideal (MRing M.ι), (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W) ∧ (M.NefFib lam s → NefOnFibres M.P (combLine (M.line t) n).a) :=
  RootFieldNumerics.curveDeg_eq_and_nefOnFibres_of_coef

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelCurveDegreeNefStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_curve_degree_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → (∀ W : Ideal (MRing M.ι), (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W) ∧ (M.NefFib lam s → NefOnFibres M.P (combLine (M.line t) n).a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.nefFib_integral_multiple | exact GlobalTheory.CompanionTheory.Ar.Top.nefFib_integral_multiple | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.nefFib_integral_multiple <;> assumption)
end
end
