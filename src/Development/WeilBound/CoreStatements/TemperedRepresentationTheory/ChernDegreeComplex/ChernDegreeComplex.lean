module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeft
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableLocalZeroCount
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AeZeroCountEqIntersection

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPolynomialGrowth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPolynomialGrowth
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.ChernTwist

section Multi

variable {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem mInt_update_add_rsmul (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (a : Fin e) (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q) (t : ℝ) (g : X → ℝ)
    (hg : Continuous g) :
    mInt A (Function.update Φ a (P + Q.rsmul t)) g =
      mInt A (Function.update Φ a P) g + t * mInt A (Function.update Φ a Q) g := by
  cases e with
  | zero => exact a.elim0
  | succ e =>
    let s : Equiv.Perm (Fin (e + 1)) := Equiv.swap 0 a
    let τ : Fin e → LocPot X := Fin.tail (Φ ∘ s)
    have hτ : ∀ i, IsPotential A (τ i) := fun i => hΦ _
    have key : ∀ T : LocPot X, mInt A (Function.update Φ a T) g = mInt A (Fin.cons T τ) g := by
      intro T
      rw [← mIntSymm A (Function.update Φ a T) s g]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [s]
      · have hne : s i.succ ≠ a := by
          intro h
          have : i.succ = s a := by rw [← h]; simp [s]
          simp [s] at this
        simp [Function.update_of_ne hne, τ, Fin.tail]
    have hc : ∀ T : LocPot X, IsPotential A T → ∀ i, IsPotential A ((Fin.cons T τ : Fin (e + 1) → LocPot X) i) :=
      fun T hT i => Fin.cases hT hτ i
    have hQt := isPotentialRsmul A t Q hQ
    rw [key, key, key, mIntAdd A P (Q.rsmul t) τ hP hQt hτ g (mIntegrableCont A _ (hc P hP) g hg)
      (mIntegrableCont A _ (hc _ hQt) g hg), mIntRsmul A t Q τ hQ hτ g]

theorem exists_poly_mInt (A : FinHolAtlas e X) (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q)
    (g : X → ℝ) (hg : Continuous g) (S : Finset (Fin e)) :
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∃ R : Polynomial ℝ, R.natDegree ≤ S.card ∧
      ∀ t : ℝ, mInt A (fun i => if i ∈ S then P + Q.rsmul t else Φ i) g = R.eval t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro Φ _
    exact ⟨Polynomial.C (mInt A Φ g), by simp, fun t => by simp⟩
  | insert a S ha ih =>
    intro Φ hΦ
    have hup : ∀ T : LocPot X, IsPotential A T → ∀ i, IsPotential A (Function.update Φ a T i) := by
      intro T hT i
      by_cases e' : i = a
      · subst e'; simpa using hT
      · simpa [Function.update_of_ne e'] using hΦ i
    obtain ⟨R₁, d₁, h₁⟩ := ih _ (hup P hP)
    obtain ⟨R₂, d₂, h₂⟩ := ih _ (hup Q hQ)
    refine ⟨R₁ + Polynomial.X * R₂, ?_, fun t => ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      refine Polynomial.natDegree_add_le_of_degree_le (d₁.trans (Nat.le_succ _)) ?_
      refine Polynomial.natDegree_mul_le.trans ?_
      have := Polynomial.natDegree_X_le (R := ℝ)
      omega
    · set Ψ : Fin e → LocPot X := fun i => if i ∈ S then P + Q.rsmul t else Φ i with hΨ
      have hΨp : ∀ i, IsPotential A (Ψ i) := by
        intro i
        simp only [hΨ]
        split_ifs
        · exact isPotentialAdd A _ _ hP (isPotentialRsmul A t Q hQ)
        · exact hΦ i
      have e₀ : (fun i => if i ∈ insert a S then P + Q.rsmul t else Φ i) =
          Function.update Ψ a (P + Q.rsmul t) := by
        funext i
        by_cases e' : i = a
        · subst e'; simp
        · simp [Function.update_of_ne e', hΨ, e']
      have e₁ : ∀ T : LocPot X, Function.update Ψ a T =
          fun i => if i ∈ S then P + Q.rsmul t else Function.update Φ a T i := by
        intro T
        funext i
        by_cases e' : i = a
        · subst e'; simp [ha]
        · simp [Function.update_of_ne e', hΨ]
      rw [e₀, mInt_update_add_rsmul A Ψ hΨp a P Q hP hQ t g hg, e₁, e₁, h₁, h₂]
      simp

end Multi

theorem chernInt_twist_polynomial :
    ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv) (L L₀ : LB Y.X) (r : L.ι → Y.Fnˣ) (r₀ : L₀.ι → Y.Fnˣ), Presents Δ L r →
      Presents Δ₀ L₀ r₀ → ∀ (φ : Weight Y.str (RingHom.id ℂ) L) (φ₀ : Weight Y.str (RingHom.id ℂ) L₀), φ.IsCInf →
      φ₀.IsCInf → ∃ P : Polynomial ℝ, P.natDegree ≤ Y.dim ∧ ∀ m : ℕ, ∃ (L' : LB Y.X) (r' : L'.ι → Y.Fnˣ)
        (ψ : Weight Y.str (RingHom.id ℂ) L'), Presents (Δ + m • Δ₀) L' r' ∧ ψ.IsCInf ∧
          ψ.chernInt Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  intro Y Δ Δ₀ L L₀ r r₀ h h₀ φ φ₀ hφ hφ₀
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  obtain ⟨R⟩ := genSmooth_of_smooth Y.str Y.dim (RingHom.id ℂ)
  have hA := R.isAlgAtlas_finAtlas
  have hP : IsPotential R.finAtlas φ.locPot := Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 hφ)
  have hQ : IsPotential R.finAtlas φ₀.locPot := Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 hφ₀)
  obtain ⟨Pol, hdeg, hev⟩ := exists_poly_mInt R.finAtlas φ.locPot φ₀.locPot hP hQ (fun _ => 1) continuous_const
    Finset.univ (fun _ => φ.locPot) (fun _ => hP)
  refine ⟨Pol, by simpa using hdeg, fun m => ?_⟩
  have hpr := h.tens (GlobalTheory.CombChern.presents_zpow h₀ (m : ℤ))
  rw [natCast_zsmul] at hpr
  have hψ : (φ.tens (φ₀.zpow (m : ℤ))).IsCInf := hφ.tens (hφ₀.zpow _)
  refine ⟨_, _, φ.tens (φ₀.zpow (m : ℤ)), hpr, hψ, ?_⟩
  have hT := isPotentialAdd R.finAtlas _ _ hP (isPotentialRsmul R.finAtlas (m : ℝ) _ hQ)
  have hsf : SameForm R.finAtlas (φ.tens (φ₀.zpow (m : ℤ))).locPot (φ.locPot + φ₀.locPot.rsmul (m : ℝ)) := by
    refine Weight.sameForm_of_eq _ hA hT fun x => ?_
    refine ⟨(pick φ.isLB x, fun _ => pick φ₀.isLB x), mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick φ₀.isLB x)⟩,
      fun z => ?_⟩
    have e := φ₀.zpow_φ (m : ℤ) (fun _ => pick φ₀.isLB x) z
    change (φ.φ (pick φ.isLB x) z + (φ₀.zpow (m : ℤ)).φ (fun _ => pick φ₀.isLB x) z) / 2 =
      φ.φ (pick φ.isLB x) z / 2 + (m : ℝ) * (φ₀.φ (pick φ₀.isLB x) z / 2)
    rw [e]
    push_cast
    ring
  rw [((Weight.chernInt_eq_mInt R hψ measurable_const).2
    (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y _ hψ)), SameForm.mInt_eq (fun _ => hsf)]
  simpa using hev (m : ℝ)

end GlobalTheory.CompanionTheory.ChernTwist
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPolynomialGrowthStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_polynomial_growth : ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv) (L L₀ : LB Y.X) (r : L.ι → Y.Fnˣ) (r₀ : L₀.ι → Y.Fnˣ), Presents Δ L r → Presents Δ₀ L₀ r₀ → ∀ (φ : Weight Y.str (RingHom.id ℂ) L) (φ₀ : Weight Y.str (RingHom.id ℂ) L₀), φ.IsCInf → φ₀.IsCInf → ∃ P : Polynomial ℝ, P.natDegree ≤ Y.dim ∧ ∀ m : ℕ, ∃ (L' : LB Y.X) (r' : L'.ι → Y.Fnˣ) (ψ : Weight Y.str (RingHom.id ℂ) L'), Presents (Δ + m • Δ₀) L' r' ∧ ψ.IsCInf ∧ ψ.chernInt Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ChernTwist.chernInt_twist_polynomial | exact GlobalTheory.CompanionTheory.ChernTwist.chernInt_twist_polynomial | (intros; apply GlobalTheory.CompanionTheory.ChernTwist.chernInt_twist_polynomial <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralEqIntersection
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralRandomSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianWeightTotalMass
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianWeightTotalMass
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem integral_exp_neg_norm_sq : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := 1) one_pos
  have hd : (Module.finrank ℝ ℂ : ℝ) / 2 = 1 := by simp [Complex.finrank_real_complex]
  simp only [one_mul, div_one, hd, Real.rpow_one, neg_mul] at h
  exact h

theorem lintegral_exp_neg_norm_sq :
    ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) = ENNReal.ofReal Real.pi := by
  have hi : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
    by_contra hn
    have h0 := integral_undef hn
    rw [integral_exp_neg_norm_sq] at h0
    exact Real.pi_ne_zero h0
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le), integral_exp_neg_norm_sq]

theorem lintegral_gW (d : ℕ) (α : Type) [Fintype α] :
    ∫⁻ C : Fin d → α → ℂ, gW d α C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) := by
  have hw : ∀ C : Fin d → α → ℂ, gW d α C =
      ∏ k, ∏ j, ENNReal.ofReal (Real.exp (-‖C k j‖ ^ 2)) := by
    intro C
    unfold gW
    simp only [← Finset.sum_neg_distrib, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le]
    exact Finset.prod_congr rfl fun k _ =>
      ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le
  have hm : Measurable fun z : ℂ => ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) := by fun_prop
  have hrow : ∫⁻ r : α → ℂ, ∏ j, ENNReal.ofReal (Real.exp (-‖r j‖ ^ 2)) =
      ENNReal.ofReal Real.pi ^ Fintype.card α := by
    rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (fun _ => hm.aemeasurable)]
    simp [lintegral_exp_neg_norm_sq]
  have hmr : Measurable fun r : α → ℂ => ∏ j, ENNReal.ofReal (Real.exp (-‖r j‖ ^ 2)) :=
    Finset.measurable_prod _ fun j _ => hm.comp (measurable_pi_apply j)
  simp only [hw]
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (fun _ => hmr.aemeasurable)]
  simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm, ENNReal.ofReal_pow Real.pi_pos.le, mul_comm]

end GlobalTheory.CompanionTheory.FSCrofton
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianWeightTotalMassStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_weight_total_mass : ∀ (d : ℕ) (α : Type) [Fintype α], ∫⁻ C : Fin d → α → ℂ, gW d α C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW | exact GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaCompactDisjointRefinement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaCompactDisjointRefinement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.CroftonPartition

theorem isSigmaCompact_of_isOpen_compact {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] {U : Set X} (hU : IsOpen U) : IsSigmaCompact U := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance

theorem isSigmaCompact_inter_isClosed {X : Type} [TopologicalSpace X] {s C : Set X}
    (hs : IsSigmaCompact s) (hC : IsClosed C) : IsSigmaCompact (s ∩ C) := by
  obtain ⟨K, hK, hKs⟩ := hs
  refine ⟨fun n => K n ∩ C, fun n => (hK n).inter_right hC, ?_⟩
  rw [← hKs, Set.iUnion_inter]

theorem exists_sigmaCompact_partition : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] (ι : Type) (S : ι → Set X), (∀ i, IsOpen (S i)) →
    (⋃ i, S i) = Set.univ → ∃ (m : ℕ) (l : Fin m → ι) (A : Fin m → Set X),
      Pairwise (Function.onFun Disjoint A) ∧ (⋃ t, A t) = Set.univ ∧ (∀ t, A t ⊆ S (l t)) ∧
      ∀ t, IsSigmaCompact (A t) := by
  intro X _ _ _ _ ι S hS hcov
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover S hS hcov.ge
  let e := t.equivFin
  let l : Fin t.card → ι := fun j => (e.symm j : ι)
  let A : Fin t.card → Set X := fun j => S (l j) \ ⋃ (i : Fin t.card) (_ : i < j), S (l i)
  refine ⟨t.card, l, A, ?_, ?_, ?_, ?_⟩
  · intro j j' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Set.disjoint_left.2 fun x hx hx' => hx'.2 (Set.mem_iUnion₂.2 ⟨j, h, hx.1⟩)
    · exact Set.disjoint_left.2 fun x hx hx' => hx.2 (Set.mem_iUnion₂.2 ⟨j', h, hx'.1⟩)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    have hl : l (e ⟨i, hit⟩) = i := by simp [l]
    obtain ⟨j, hj, hmin⟩ := wellFounded_lt.has_min {j : Fin t.card | x ∈ S (l j)}
      ⟨e ⟨i, hit⟩, by simpa [hl] using hxi⟩
    refine Set.mem_iUnion.2 ⟨j, hj, fun hx => ?_⟩
    obtain ⟨i', hi', hxi'⟩ := Set.mem_iUnion₂.1 hx
    exact hmin i' hxi' hi'
  · intro j
    exact Set.sdiff_subset
  · intro j
    show IsSigmaCompact (S (l j) \ ⋃ (i : Fin t.card) (_ : i < j), S (l i))
    rw [Set.sdiff_eq]
    exact isSigmaCompact_inter_isClosed (isSigmaCompact_of_isOpen_compact (hS _))
      (isClosed_compl_iff.2 (isOpen_iUnion fun i => isOpen_iUnion fun _ => hS _))

end GlobalTheory.CompanionTheory.CroftonPartition
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaCompactDisjointRefinementStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigma_compact_disjoint_refinement : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X] (ι : Type) (S : ι → Set X), (∀ i, IsOpen (S i)) → (⋃ i, S i) = Set.univ → ∃ (m : ℕ) (l : Fin m → ι) (A : Fin m → Set X), Pairwise (Function.onFun Disjoint A) ∧ (⋃ t, A t) = Set.univ ∧ (∀ t, A t ⊆ S (l t)) ∧ ∀ t, IsSigmaCompact (A t) := by
  first | exact @GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition | exact GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition | (intros; apply GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralRandomSections
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem measurable_gW (d : ℕ) (α : Type) [Fintype α] : Measurable (gW d α) := by
  unfold gW
  fun_prop

theorem encard_iUnion_fin {X : Type} {m : ℕ} (B : Fin m → Set X)
    (h : Pairwise (Function.onFun Disjoint B)) :
    (((⋃ t, B t).encard : ℕ∞) : ℝ≥0∞) = ∑ t, (((B t).encard : ℕ∞) : ℝ≥0∞) := by
  classical
  have key : ∀ s : Finset (Fin m), (((⋃ t ∈ s, B t).encard : ℕ∞) : ℝ≥0∞) =
      ∑ t ∈ s, (((B t).encard : ℕ∞) : ℝ≥0∞) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq, ENat.toENNReal_add,
        ih]
      exact Set.disjoint_iUnion₂_right.2 fun t ht => h (fun e => ha (e ▸ ht))
  simpa using key Finset.univ

theorem crofton : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∃ μ : Measure (Fin Y.dim → Fin n → ℂ), IsProbabilityMeasure μ ∧ μ ≪ volume ∧ (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ∫ C, (({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℝ) ∂μ := by
  intro Y Δ L r hL n b hb _
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  set φ := Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp) with hφdef
  have hφ : φ.IsCInf := Weight.isCInf_fsBasis hL b hb _ _
  have hneg : φ.chernPart Y.dim (-1) = 0 :=
    Weight.chernPart_neg_eq_zero hφ (Weight.semiPosReg_fsBasis hL b hb _ _)
  have hint := GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ
  have hfin : φ.chernPart Y.dim 1 Set.univ ≠ ⊤ := by
    have h1 := hint.1
    rw [IntegrableOn, Measure.restrict_univ, integrable_const_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 one_ne_zero
    · exact ((isFiniteMeasure_iff _).1 (by simpa using h1)).ne

  let ι := AlgChart Y.str (RingHom.id ℂ) Y.dim × L.ι × Fin n
  let S : ι → Set (CxPts Y.str (RingHom.id ℂ)) := fun t => t.1.e.source ∩
    (ptsIn Y.str (RingHom.id ℂ) (L.U t.2.1) ∩ ptsIn Y.str (RingHom.id ℂ) (nonzeroLocus (b t.2.2)))
  have hSo : ∀ t, IsOpen (S t) := fun t =>
    t.1.e.open_source.inter ((isOpen_ptsIn _).inter (isOpen_ptsIn _))
  have hSc : (⋃ t, S t) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := RingHom.id ℂ) y
    obtain ⟨j, hj⟩ := exists_mem_ptsIn hb y
    exact Set.mem_iUnion.2 ⟨⟨c, pick hL y, j⟩, hc, mem_pick hL y, hj⟩
  obtain ⟨m, l, A, hdis, hun, hsub, hσ⟩ := GlobalTheory.T.sigma_compact_disjoint_refinement _ ι S hSo hSc
  set G : ℝ≥0∞ := ENNReal.ofReal (Real.pi ^ (Y.dim * n)) with hG
  have hGpos : G ≠ 0 := by
    rw [hG, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hGtop : G ≠ ⊤ := ENNReal.ofReal_ne_top
  let Z : (Fin Y.dim → Fin n → ℂ) → Set (CxPts Y.str (RingHom.id ℂ)) := fun C =>
    {y | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
      ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}
  let P : Fin m → (Fin Y.dim → Fin n → ℂ) → Set (CxPts Y.str (RingHom.id ℂ)) := fun t C =>
    {y | y ∈ A t ∧ ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
      ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}
  have hpiece : ∀ t, Measurable (fun C => (((P t C).encard : ℕ∞) : ℝ≥0∞)) ∧
      ∫⁻ C, gW Y.dim (Fin n) C * (((P t C).encard : ℕ∞) : ℝ≥0∞) =
        G * φ.chernPart Y.dim 1 (A t) := fun t =>
    GlobalTheory.T.measurable_local_zero_count Y L hL n b hb (l t).1 (l t).2.1 (l t).2.2 (A t)
      (fun y hy => (hsub t hy).1) (fun y hy => (hsub t hy).2.1)
      (fun y hy => (secVal_ne_zero_iff _ (hsub t hy).2.1).2 (hsub t hy).2.2) (hσ t)
  have hZ : ∀ C, (((Z C).encard : ℕ∞) : ℝ≥0∞) = ∑ t, (((P t C).encard : ℕ∞) : ℝ≥0∞) := by
    intro C
    rw [← encard_iUnion_fin]
    · congr 2
      ext y
      simp only [Set.mem_iUnion, P, Z, Set.mem_ofPred_eq]
      constructor
      · intro h
        obtain ⟨t, ht⟩ := Set.mem_iUnion.1 (hun ▸ Set.mem_univ y)
        exact ⟨t, ht, h⟩
      · rintro ⟨t, -, h⟩
        exact h
    · intro s t hst
      exact (hdis hst).mono (fun y hy => hy.1) (fun y hy => hy.1)
  have hNm : Measurable fun C => (((Z C).encard : ℕ∞) : ℝ≥0∞) := by
    simp only [hZ]
    exact Finset.measurable_fun_sum _ fun t _ => (hpiece t).1
  have hAm : ∀ t, MeasurableSet (A t) := fun t => by
    obtain ⟨K, hK, e⟩ := hσ t
    rw [← e]
    exact MeasurableSet.iUnion fun i => (hK i).measurableSet
  have hmass : φ.chernPart Y.dim 1 Set.univ = ∑ t, φ.chernPart Y.dim 1 (A t) := by
    rw [← hun, measure_iUnion hdis hAm, tsum_fintype]
  have hgm := measurable_gW Y.dim (Fin n)
  have hsum : ∫⁻ C, gW Y.dim (Fin n) C * (((Z C).encard : ℕ∞) : ℝ≥0∞) =
      G * φ.chernPart Y.dim 1 Set.univ := by
    simp only [hZ, Finset.mul_sum]
    rw [lintegral_finsetSum Finset.univ (f := fun t C => gW Y.dim (Fin n) C *
      (((P t C).encard : ℕ∞) : ℝ≥0∞)) fun t _ => hgm.mul (hpiece t).1, hmass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => (hpiece t).2
  let μ : Measure (Fin Y.dim → Fin n → ℂ) := G⁻¹ • volume.withDensity (gW Y.dim (Fin n))
  have hlin : ∀ f : (Fin Y.dim → Fin n → ℂ) → ℝ≥0∞, Measurable f →
      ∫⁻ C, f C ∂μ = G⁻¹ * ∫⁻ C, gW Y.dim (Fin n) C * f C := by
    intro f hf
    rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hgm hf]
    rfl
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have h1 := hlin (fun _ => 1) measurable_const
    simp only [lintegral_one, mul_one] at h1
    rw [h1, GlobalTheory.T.gaussian_weight_total_mass, Fintype.card_fin]
    exact ENNReal.inv_mul_cancel hGpos hGtop
  have hN : ∫⁻ C, (((Z C).encard : ℕ∞) : ℝ≥0∞) ∂μ = φ.chernPart Y.dim 1 Set.univ := by
    rw [hlin _ hNm, hsum, ← mul_assoc, ENNReal.inv_mul_cancel hGpos hGtop, one_mul]
  refine ⟨μ, hprob, ?_, ?_⟩
  · exact (withDensity_absolutelyContinuous _ _).smul_left _
  · have hcast : ∀ C, ((Z C).ncard : ℝ) = ((((Z C).encard : ℕ∞) : ℝ≥0∞)).toReal := by
      intro C
      rw [Set.ncard]
      cases h : (Z C).encard with
      | top => simp
      | coe a => simp
    have hae : ∀ᵐ C ∂μ, (((Z C).encard : ℕ∞) : ℝ≥0∞) < ⊤ :=
      ae_lt_top hNm (by rw [hN]; exact hfin)
    have e := integral_toReal hNm.aemeasurable hae
    rw [hN] at e
    simp only [Z] at hcast e
    simp only [hcast]
    rw [e, Weight.chernInt, hneg]
    simp [Measure.real]
end GlobalTheory.CompanionTheory.FSCrofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralRandomSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_random_sections : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∃ μ : Measure (Fin Y.dim → Fin n → ℂ), IsProbabilityMeasure μ ∧ μ ≪ volume ∧ (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ∫ C, (({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℝ) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.crofton | exact GlobalTheory.CompanionTheory.FSCrofton.crofton | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.crofton <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralEqIntersection
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.ChernDegree

theorem chernInt_fsBasis_eq_inter : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ((Y.inter fun _ => Δ : ℤ) : ℝ) := by
  intro Y Δ L r hL n b hb hP
  obtain ⟨μ, hμ, hac, heq⟩ := GlobalTheory.T.chern_integral_random_sections Y Δ L r hL n b hb hP
  rw [heq, integral_congr_ae (g := fun _ => (((Y.inter fun _ => Δ : ℤ)) : ℝ)) ?_]
  · simp
  · filter_upwards [hac.ae_le (GlobalTheory.T.ae_zero_count_eq_intersection Y Δ L r hL n b hb hP)] with C hC
    exact_mod_cast hC

end GlobalTheory.CompanionTheory.ChernDegree
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralEqIntersectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_eq_intersection : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ((Y.inter fun _ => Δ : ℤ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ChernDegree.chernInt_fsBasis_eq_inter | exact GlobalTheory.CompanionTheory.ChernDegree.chernInt_fsBasis_eq_inter | (intros; apply GlobalTheory.CompanionTheory.ChernDegree.chernInt_fsBasis_eq_inter <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntersectionNumberPolynomial
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntersectionNumberPolynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.ChernPoly

theorem inter_add_nsmul_polynomial :
    ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv), ∃ Q : Polynomial ℝ, ∀ m : ℕ,
      ((Y.inter fun _ => Δ + m • Δ₀ : ℤ) : ℝ) = Q.eval (m : ℝ) := by
  intro Y Δ Δ₀
  classical
  refine ⟨∑ s : Finset (Fin Y.dim),
    Polynomial.C ((Y.interForm (s.piecewise (fun _ => Δ₀) (fun _ => Δ)) : ℤ) : ℝ) * Polynomial.X ^ s.card,
    fun m => ?_⟩
  have h1 : (fun _ : Fin Y.dim => Δ + m • Δ₀) = (fun _ => (m : ℤ) • Δ₀) + (fun _ => Δ) := by
    funext i
    rw [Pi.add_apply, natCast_zsmul, add_comm]
  rw [← Y.interForm_apply, h1, MultilinearMap.map_add_univ]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : (s.piecewise (fun i => (m : ℤ) • s.piecewise (fun _ => Δ₀) (fun _ => Δ) i)
      (s.piecewise (fun _ => Δ₀) (fun _ => Δ))) = s.piecewise (fun _ => (m : ℤ) • Δ₀) (fun _ => Δ) := by
    funext i
    by_cases hi : i ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ hi,
        Finset.piecewise_eq_of_mem _ _ _ hi]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi,
        Finset.piecewise_eq_of_notMem _ _ _ hi]
  have key := Y.interForm.map_piecewise_smul (fun _ => (m : ℤ)) (s.piecewise (fun _ => Δ₀) (fun _ => Δ)) s
  rw [hpw, Finset.prod_const, smul_eq_mul] at key
  rw [key]
  push_cast
  simp only [id_eq]
  push_cast
  ring

end GlobalTheory.CompanionTheory.ChernPoly
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntersectionNumberPolynomialStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_polynomial : ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv), ∃ Q : Polynomial ℝ, ∀ m : ℕ, ((Y.inter fun _ => Δ + m • Δ₀ : ℤ) : ℝ) = Q.eval (m : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ChernPoly.inter_add_nsmul_polynomial | exact GlobalTheory.CompanionTheory.ChernPoly.inter_add_nsmul_polynomial | (intros; apply GlobalTheory.CompanionTheory.ChernPoly.inter_add_nsmul_polynomial <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationIndep
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralWeightIndep
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralWeightIndep
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
open ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.ChernMass

theorem chernInt_eq_of_isCInf : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L),
    φ.IsCInf → ψ.IsCInf →
      φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  intro Y L φ ψ hφ hψ
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  obtain ⟨R⟩ := genSmooth_of_smooth Y.str Y.dim (RingHom.id ℂ)
  have hA := R.isAlgAtlas_finAtlas
  set v : CxPts Y.str (RingHom.id ℂ) → ℝ :=
    fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2 with hv
  have hdiff : ∀ i y, y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (ψ.φ i y - φ.φ i y) / 2 = v y := by
    intro i y hy
    have hp := mem_pick φ.isLB y
    simp only [hv]
    rw [ψ.trans i _ y hy hp, φ.trans i _ y hy hp]
    ring
  have hvC : ∀ y, CInfAt v y := by
    intro y
    have hp := mem_pick φ.isLB y
    refine (((hψ _ y hp).add (hφ _ y hp).neg).const_mul (1 / 2)).congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hp] with z hz
    rw [← hdiff _ z hz]
    ring
  have hvs : (R.finAtlas).Smooth v :=
    (hA.smooth_iff R).2 ((cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hvC y)
  have sφ := (Weight.isCInf_iff_isSmooth R).1 hφ
  have sψ := (Weight.isCInf_iff_isSmooth R).1 hψ
  have hQ : IsPotential R.finAtlas (φ.locPot + LocPot.ofFun v) :=
    isPotentialAdd _ _ _ (Weight.isPotential_locPot sφ) (isPotential_ofFun _ _ hvs)
  have hS : SameForm R.finAtlas ψ.locPot (φ.locPot + LocPot.ofFun v) :=
    ψ.sameForm_of_re (R := R) hA hQ fun x => by
      refine ⟨pick φ.isLB x, mem_pick φ.isLB x, _, isOpen_ptsIn _, mem_pick φ.isLB x, fun _ => 0,
        fun _ => differentiableOn_const (0 : ℂ), fun z hz => ?_⟩
      have := hdiff _ z hz
      show ψ.φ _ z / 2 = (φ.φ _ z / 2 + v z) + _
      rw [← this]
      simp
      ring
  rw [(Weight.chernInt_eq_mInt R hφ measurable_const).2
      (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ),
    (Weight.chernInt_eq_mInt R hψ measurable_const).2
      (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y ψ hψ),
    SameForm.mInt_eq (fun _ => hS) _]
  exact (massIndep R.finAtlas (fun _ => φ.locPot) (fun _ => v)
    (fun _ => Weight.isPotential_locPot sφ) (fun _ => hvs)).symm

end GlobalTheory.CompanionTheory.ChernMass
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralWeightIndepStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_weight_indep : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ψ.IsCInf → φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_isCInf | exact GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_isCInf | (intros; apply GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_isCInf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationTransfer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationTransfer
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory GlobalTheory.Points GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.ProjVar.Var

namespace GlobalTheory.CompanionTheory.ChernTransport

section Chart

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {B B' : LB X} {φ : Weight p σ B} {ψ : Weight p σ B'}

theorem hess_eq_of_unit (c : AlgChart p σ D) (h : φ.IsCInf) {y : CxPts p σ} (hy : y ∈ c.e.source)
    {i : B.ι} {j : B'.ι} (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B'.U j))
    (a : Γ(X, B.U i ⊓ B'.U j)ˣ)
    (ha : ∀ z ∈ ptsIn p σ (B.U i ⊓ B'.U j),
      ψ.φ j z = φ.φ i z + Real.log (‖ev p σ _ a.val z‖ ^ 2)) :
    c.hess ψ j y = c.hess φ i y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ B'.U j))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨hi, hj⟩)
  have hg := c.holo _ a.val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ B'.U j),
      (ev p σ _ a.val ∘ c.e.symm) v ≠ 0 := fun v hv => ev_ne_zero hv.2 a.isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h i) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun w => ((Real.log (‖(ev p σ _ a.val ∘ c.e.symm) w‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext s t
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 s t
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ha _ hv.2, one_mul]
  rfl

theorem chartMeas_congr_source {n : ℕ} {T : Type} [TopologicalSpace T] [MeasurableSpace T]
    (e : OpenPartialHomeomorph T (V n)) {ρ ρ' : T → ENNReal} (h : ∀ y ∈ e.source, ρ y = ρ' y) :
    chartMeas e ρ = chartMeas e ρ' := by
  have hae : (ρ ∘ e.symm) =ᵐ[volume.restrict e.target] (ρ' ∘ e.symm) :=
    (ae_restrict_iff' e.open_target.measurableSet).2
      (Filter.Eventually.of_forall fun v hv => h _ (e.map_target hv))
  show Measure.map e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm)) =
    Measure.map e.symm ((volume.restrict e.target).withDensity (ρ' ∘ e.symm))
  rw [withDensity_congr_ae hae]

theorem chernPart_eq_of_chernDens (h : ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source,
    c.chernDens ψ y = c.chernDens φ y) (ε : ℤˣ) : ψ.chernPart D ε = φ.chernPart D ε := by
  show (⨆ c : AlgChart p σ D, chartMeas c.e fun y => ENNReal.ofReal (↑↑ε * c.chernDens ψ y)) =
    ⨆ c : AlgChart p σ D, chartMeas c.e fun y => ENNReal.ofReal (↑↑ε * c.chernDens φ y)
  exact iSup_congr fun c => chartMeas_congr_source _ fun y hy => by rw [h c y hy]

end Chart

variable {Y : Var ℂ} {Δ : Y.Dv} {L L' : LB Y.X} {r : L.ι → Y.Fnˣ} {r' : L'.ι → Y.Fnˣ}

theorem exists_unit_tv (hp : Presents Δ L r) (hp' : Presents Δ L' r') (i : L.ι) (j : L'.ι) :
    ∃ a : Γ(Y.X, L.U i ⊓ L'.U j)ˣ, ∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
      tv (σ := RingHom.id ℂ) (r i) (r' j) z = ev Y.str (RingHom.id ℂ) _ a.val z := by
  obtain ⟨a, ha⟩ := exists_unit_fnOf_eq (U := L.U i ⊓ L'.U j)
    (f := (r' j : Y.Fn) / (r i : Y.Fn))
    fun x hx => (hp.isEqn i x hx.1).iff_unitAt.1 (hp'.isEqn j x hx.2)
  refine ⟨a, fun z hz => ?_⟩
  have hb := mem_ptsIn_iff.1 hz
  rw [tv, ← ha (gen_mem hb), val_cx_fnOf hb]

theorem exists_transport (hp : Presents Δ L r) (hp' : Presents Δ L' r')
    (φ : Weight Y.str (RingHom.id ℂ) L) (hφ : φ.IsCInf) :
    ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧
      ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  have hs : mSmooth Y (RingHom.id ℂ) Δ (ofWeight Y (RingHom.id ℂ) Δ L r hp φ) :=
    (mSmooth_ofWeight_iff hp φ).2 ((Weight.isCInf_iff_isSmooth (Y.an _)).1 hφ)
  set m := ofWeight Y (RingHom.id ℂ) Δ L r hp φ with hm
  let ψ : Weight Y.str (RingHom.id ℂ) L' := m.toWeight hs.posSet_eq hp'
  have hψ : ψ.IsCInf := (Weight.isCInf_iff_isSmooth (Y.an _)).2 (hs.isSmooth_toWeight hp')
  have key : ∀ (i : L.ι) (j : L'.ι) (a : Γ(Y.X, L.U i ⊓ L'.U j)ˣ),
      (∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
        tv (σ := RingHom.id ℂ) (r i) (r' j) z = ev Y.str (RingHom.id ℂ) _ a.val z) →
      ∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
        ψ.φ j z = φ.φ i z + Real.log (‖ev Y.str (RingHom.id ℂ) _ a.val z‖ ^ 2) := by
    intro i j a ha z hz
    obtain ⟨hi, hj⟩ := mem_ptsIn_inf.1 hz
    have hw : m.wt (r i) z = φ.φ i z := by
      rw [Met.wt, hm, ofWeight_h hp φ hi, Real.log_exp, neg_neg]
    have := Met.wt_trans (hs.posSet_eq ▸ mem_univ z) (ptsIn_subset_eqnSet hp i hi)
      (ptsIn_subset_eqnSet hp' j hj)
    rw [hw, ha z hz] at this
    exact this
  have hd : ∀ (c : AlgChart Y.str (RingHom.id ℂ) Y.dim), ∀ y ∈ c.e.source,
      c.chernDens ψ y = c.chernDens φ y := by
    intro c y hy
    have hi := mem_pick φ.isLB y
    have hj := mem_pick ψ.isLB y
    obtain ⟨a, ha⟩ := exists_unit_tv hp hp' _ _
    rw [c.chernDens_eq hψ hy hj, c.chernDens_eq hφ hy hi,
      hess_eq_of_unit c hφ hy hi hj a (key _ _ a ha)]
  refine ⟨ψ, hψ, ?_⟩
  rw [Weight.chernInt, Weight.chernInt, chernPart_eq_of_chernDens hd, chernPart_eq_of_chernDens hd]

theorem transport : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ) (r' : L'.ι → Y.Fnˣ),
    Presents Δ L r → Presents Δ L' r' → ∀ φ : Weight Y.str (RingHom.id ℂ) L, φ.IsCInf →
      ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧
        ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  intro Y Δ L L' r r' hp hp' φ hφ
  exact exists_transport hp hp' φ hφ

end GlobalTheory.CompanionTheory.ChernTransport
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationTransferStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_presentation_transfer : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ) (r' : L'.ι → Y.Fnˣ), Presents Δ L r → Presents Δ L' r' → ∀ φ : Weight Y.str (RingHom.id ℂ) L, φ.IsCInf → ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧ ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.ChernTransport.transport | exact GlobalTheory.CompanionTheory.ChernTransport.transport | (intros; apply GlobalTheory.CompanionTheory.ChernTransport.transport <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationIndep
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.ChernMass

theorem chernInt_eq_of_presents (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ)
    (r' : L'.ι → Y.Fnˣ) (hL : Presents Δ L r) (hL' : Presents Δ L' r')
    (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) L')
    (hφ : φ.IsCInf) (hψ : ψ.IsCInf) :
    φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  obtain ⟨ψ₀, hψ₀, hmass⟩ := GlobalTheory.T.chern_integral_presentation_transfer Y Δ L L' r r' hL hL' φ hφ
  rw [← hmass]
  exact GlobalTheory.T.chern_integral_weight_indep Y L' ψ₀ ψ hψ₀ hψ

end GlobalTheory.CompanionTheory.ChernMass
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationIndepStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_presentation_indep : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ) (r' : L'.ι → Y.Fnˣ), Presents Δ L r → Presents Δ L' r' → ∀ (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) L'), φ.IsCInf → ψ.IsCInf → φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_presents | exact GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_presents | (intros; apply GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_presents <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneTwistGloballyGenerated
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneTwistGloballyGenerated
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.SerreBpf


open GlobalTheory.QCoh GlobalTheory.Twist CechPic GlobalTheory.LB in
theorem eventually_basePointFree (Y : Var ℂ) (i : Fin (Y.N + 1))
    (hi : Y.ι (genericPoint Y.X) ∈ ProjSpace.chart ℂ Y.N i) (Δ : Y.Dv) :
    ∀ᶠ m : ℕ in Filter.atTop, ∃ (L : LB Y.X) (r : L.ι → Y.Fnˣ) (n : ℕ) (b : Fin n → L.Sec),
      L.IsLB ∧ Presents (Δ + m • Y.hyp hi) L r ∧ ⨆ j, nonzeroLocus (b j) = ⊤ := by
  have hA : GlobalTheory.IsAmpleLB Y.O1 := Y.isAmple_projective_O_one
  have hK : (GlobalTheory.Cartier.toLB (-Δ)).IsLB := GlobalTheory.Cartier.isLB_toLB _
  have hL0 : (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))).IsLB := GlobalTheory.CechPic.isLB_dual hK
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL0
  haveI := GlobalTheory.LB.isFiniteType_toMod hL0
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))) :=
    GlobalTheory.QCoh.IsFiniteQC.of_isFiniteType
  filter_upwards [hA.eventually_isGloballyGenerated_twist
    (GlobalTheory.LB.toMod (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))))] with m hm
  have hM : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m).IsLB :=
    ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb Y.isLineBundle_twistingSheafOne _ _
  have hN : (GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi)).IsLB := GlobalTheory.Cartier.isLB_toLB _
  have h1 : GlobalTheory.QCoh.IsGloballyGenerated
      (GlobalTheory.twist (GlobalTheory.twist (GlobalTheory.LB.unitMod Y.X) (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)) := by
    haveI : Epi (GlobalTheory.Twist.map (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
        (GlobalTheory.Twist.unitTwistIso (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))).inv) :=
      (GlobalTheory.Twist.epi_map_iff hM _).2 inferInstance
    exact hm.of_epi (GlobalTheory.Twist.map (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
      (GlobalTheory.Twist.unitTwistIso (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))).inv)
  have hiso : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
      ((GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi)).div (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))) := by
    rw [← GlobalTheory.CechPic.tens_eq_div, ← GlobalTheory.CechPic.cls_eq_iff hM (GlobalTheory.CechPic.isLB_tens hN hK),
      GlobalTheory.CechPic.cls_tens hN hK, GlobalTheory.CechPic.cls_lbPow Y.isLineBundle_twistingSheafOne, ← GlobalTheory.Cartier.toPic_apply,
      ← GlobalTheory.Cartier.toPic_apply, ← (Y.presents_hyp hi).toPic_eq, map_add, map_neg, map_nsmul]
    abel
  obtain ⟨e⟩ := GlobalTheory.Twist.nonempty_twistTwistIso (F := GlobalTheory.LB.unitMod Y.X) hL0 hM hN hiso
  have h2 : GlobalTheory.QCoh.IsGloballyGenerated (GlobalTheory.LB.toMod (GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi))) :=
    (GlobalTheory.QCoh.isGloballyGenerated_iff_of_iso (e ≪≫ GlobalTheory.Twist.unitTwistIso _)).1 h1
  obtain ⟨n, s, hs⟩ := ((GlobalTheory.isGloballyGenerated_toMod_iff hN).1 h2).exists_fin_succ
  exact ⟨_, _, n + 1, s, hN, GlobalTheory.Cartier.presents_toLB _, hs⟩

end GlobalTheory.CompanionTheory.SerreBpf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneTwistGloballyGeneratedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperplane_twist_globally_generated : ∀ (Y : Var ℂ) (i : Fin (Y.N + 1)) (hi : Y.ι (genericPoint Y.X) ∈ ProjSpace.chart ℂ Y.N i) (Δ : Y.Dv), ∀ᶠ m : ℕ in Filter.atTop, ∃ (L : LB Y.X) (r : L.ι → Y.Fnˣ) (n : ℕ) (b : Fin n → L.Sec), L.IsLB ∧ Presents (Δ + m • Y.hyp hi) L r ∧ ⨆ j, nonzeroLocus (b j) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SerreBpf.eventually_basePointFree | exact GlobalTheory.CompanionTheory.SerreBpf.eventually_basePointFree | (intros; apply GlobalTheory.CompanionTheory.SerreBpf.eventually_basePointFree <;> assumption)
end
end

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace PositivityTheory.Tls2.Chern2

theorem chernDegreeComplex : GlobalTheory.Published.ChernDegreeComplex := by
  intro Y Δ L r hr φ hφ
  refine ⟨GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ, ?_⟩
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart ℂ Y.N (Y.ι (genericPoint ↥Y.X))
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (GlobalTheory.T.hyperplane_twist_globally_generated Y i hi 0)
  obtain ⟨L₀, r₀, n₀, b₀, hL₀, hp₀, hb₀⟩ := hM₀ (M₀ + 1) (by omega)
  have hφ₀ := Weight.isCInf_fsBasis (p := Y.str) (σ := RingHom.id ℂ) hL₀ b₀ hb₀ 1 (by simp)
  obtain ⟨P, -, hP⟩ := GlobalTheory.T.chern_integral_polynomial_growth Y Δ _ L L₀ r r₀ hr hp₀ φ _ hφ hφ₀
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.intersection_number_polynomial Y Δ (0 + (M₀ + 1) • Y.hyp hi)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (GlobalTheory.T.hyperplane_twist_globally_generated Y i hi Δ)
  have key : ∀ m : ℕ, M ≤ m → P.eval (m : ℝ) = Q.eval (m : ℝ) := by
    intro m hm
    obtain ⟨L', r', ψ, hp', hψ, hψeq⟩ := hP m
    have hmm : M ≤ m * (M₀ + 1) := le_trans hm (Nat.le_mul_of_pos_right m (Nat.succ_pos M₀))
    obtain ⟨L₁, r₁, n₁, b₁, hL₁, hp₁, hb₁⟩ := hM (m * (M₀ + 1)) hmm
    have hΔ : Δ + (m * (M₀ + 1)) • Y.hyp hi = Δ + m • (0 + (M₀ + 1) • Y.hyp hi) := by
      rw [zero_add, mul_smul]
    rw [hΔ] at hp₁
    rw [← hψeq, ← hQ m, ← GlobalTheory.T.chern_integral_eq_intersection Y _ L₁ r₁ hL₁ n₁ b₁ hb₁ hp₁]
    exact GlobalTheory.T.chern_integral_presentation_indep Y _ L' L₁ r' r₁ hp' hp₁ ψ _ hψ
      (Weight.isCInf_fsBasis _ _ _ _ _)
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite M).image Nat.cast_injective.injOn)
    rintro x ⟨m, hm, rfl⟩
    exact key m hm
  obtain ⟨L', r', ψ, hp', hψ, hψeq⟩ := hP 0
  have h0 : Δ + (0 : ℕ) • (0 + (M₀ + 1) • Y.hyp hi) = Δ := by simp
  rw [h0] at hp'
  have hQ0 := hQ 0
  rw [h0] at hQ0
  rw [hQ0, ← hPQ, ← hψeq]
  exact GlobalTheory.T.chern_integral_presentation_indep Y Δ L L' r r' hr hp' φ ψ hφ hψ

end PositivityTheory.Tls2.Chern2
