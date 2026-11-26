module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAB
public import Lemmata.GeneralBFactTerForm.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem mvPolynomialInt_dimFormula {σ : Type*} [Finite σ] (P Q : Ideal (MvPolynomial σ ℤ))
    [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ Q) + ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) =
      ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by

  haveI : IsJacobsonRing ℤ := int_isJacobsonRing
  haveI := DimF.finiteRingKrullDim_mvPolynomialInt_quot P
  haveI : (Q.map (Ideal.Quotient.mk P)).IsPrime := DimF.isPrime_map_mk h
  have key := DimF.dim_quot_add_height (A := MvPolynomial σ ℤ ⧸ P)
    (DimF.height_eq_of_isMaximal_int P) (Q.map (Ideal.Quotient.mk P))

  rw [← key, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE h)]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section Dim

variable {σ : Type*} [Finite σ]

theorem dim_quot_minimal_add_one (P W : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (s : MvPolynomial σ ℤ) (hs : s ∉ P) (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ W) + 1 = ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hq : W.map (Ideal.Quotient.mk P) ∈
      (Ideal.span {Ideal.Quotient.mk P s}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk P s} = (Ideal.span {s}).map (Ideal.Quotient.mk P) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk P)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk P s}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk P)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk P s ∈ W.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hsW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hs this
  have key := mvPolynomialInt_dimFormula P W hPW
  rw [hh] at key
  exact_mod_cast key

theorem withBot_eq_of_add_one {x : WithBot ℕ∞} {m : ℕ} (h : x + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    x = (m : WithBot ℕ∞) := by
  first | exact Bl.general_b_fact_ter_form.goal1 .. | (apply Bl.general_b_fact_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_ter_form.goal1 <;> assumption)

end Dim

section Blocks

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def blockWeight [DecidableEq K] (k : K) : (Σ k, ι k) → ℕ := fun p => if p.1 = k then 1 else 0

theorem weight_blockWeight [DecidableEq K] (k : K) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight (ι := ι) k) m = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [blockWeight]
  · intro b _ hb
    simp [blockWeight, hb]
  · simp

theorem isWeightedHomogeneous_of_isMultiHomog [DecidableEq K] {s : MRing ι} {a : K → ℕ}
    (h : IsMultiHomog s a) (k : K) : IsWeightedHomogeneous (blockWeight (ι := ι) k) s (a k) := by
  intro d hd
  rw [weight_blockWeight]
  exact h d (mem_support_iff.mpr hd) k

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous_of_isMultiHomogIdeal [DecidableEq K] {P : Ideal (MRing ι)}
    (h : IsMultiHomogIdeal P) (k : K) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx => ?_
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_of_isMultiHomog ha k)⟩

theorem isHomogeneous_of_mem_minimalPrimes {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A)
    [GradedRing 𝒜] {I W : Ideal A} (hI : I.IsHomogeneous 𝒜) (hW : W ∈ I.minimalPrimes) :
    W.IsHomogeneous 𝒜 := by
  have hWp : W.IsPrime := hW.1.1
  have h1 : (W.homogeneousCore 𝒜).toIdeal.IsPrime := hWp.homogeneousCore
  have h2 : I ≤ (W.homogeneousCore 𝒜).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  have h3 := hW.2 ⟨h1, h2⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
  have e : (W.homogeneousCore 𝒜).toIdeal = W :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) h3
  exact e ▸ (W.homogeneousCore 𝒜).isHomogeneous

theorem exists_blockComponent [DecidableEq K] {W : Ideal (MRing ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k)))
    (a : K → ℕ) (T : Finset K) {f : MRing ι} (hf : f ∈ W) :
    ∃ g ∈ W, ∀ m, AddMonoidAlgebra.coeff g m = if (∀ k ∈ T, ∑ i, m ⟨k, i⟩ = a k) then AddMonoidAlgebra.coeff f m else 0 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨f, hf, fun m => by simp⟩
  | @insert k T hk ih =>
    obtain ⟨g, hgW, hg⟩ := ih
    refine ⟨weightedHomogeneousComponent (blockWeight k) (a k) g,
      weightedHomogeneousComponent_mem_of_mem ℤ (blockWeight k) (hW k) hgW (a k), fun m => ?_⟩
    rw [coeff_weightedHomogeneousComponent, weight_blockWeight, hg]
    by_cases h1 : ∑ i, m ⟨k, i⟩ = a k <;> by_cases h2 : ∀ k' ∈ T, ∑ i, m ⟨k', i⟩ = a k' <;>
      simp [h1, h2]

theorem isMultiHomogIdeal_of_isHomogeneous [DecidableEq K] {W : Ideal (MRing ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k))) :
    IsMultiHomogIdeal W := by
  refine ⟨{f | f ∈ W ∧ ∃ a, IsMultiHomog f a}, fun f hf => hf.2, le_antisymm (fun f hf => ?_)
    (Ideal.span_le.mpr fun f hf => hf.1)⟩
  choose g hgW hg using fun a : K → ℕ => exists_blockComponent hW a Finset.univ hf
  have hsum : f = ∑ a ∈ f.support.image (fun m k => ∑ i, m ⟨k, i⟩), g a := by
    ext m
    rw [coeff_sum]
    have e : ∀ a : K → ℕ,
        AddMonoidAlgebra.coeff (g a) m = if (fun k => ∑ i, m ⟨k, i⟩) = a then AddMonoidAlgebra.coeff f m else 0 := by
      intro a
      rw [hg a]
      by_cases h : (fun k => ∑ i, m ⟨k, i⟩) = a
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        exact h (funext fun k => h' k (Finset.mem_univ k))
    simp_rw [e]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · by_contra hne
      exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
  rw [hsum]
  refine Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨hgW a, a, fun m hm k => ?_⟩
  rw [mem_support_iff, hg a] at hm
  by_contra hk
  exact hm (if_neg fun h => hk (h k (Finset.mem_univ k)))

theorem isMultiHomogIdeal_of_mem_minimalPrimes {P W : Ideal (MRing ι)} {s : MRing ι} {a : K → ℕ}
    (hP : IsMultiHomogIdeal P) (hs : IsMultiHomog s a)
    (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) : IsMultiHomogIdeal W := by
  classical
  refine isMultiHomogIdeal_of_isHomogeneous fun k => isHomogeneous_of_mem_minimalPrimes _
    ((isHomogeneous_of_isMultiHomogIdeal hP k).sup (Ideal.homogeneous_span _ _ ?_)) hW
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_of_isMultiHomog hs k)⟩

theorem charOf_prime {W : Ideal (MRing ι)} (hW : W.IsPrime) (hv : ¬ IsHorizontal W) :
    (charOf W).Prime := by
  have := hW
  have hJ : (W.comap (C : ℤ →+* MRing ι)).IsPrime := inferInstance
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ≠ 0 := fun h0 =>
    hv ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mpr h0)
  unfold charOf
  rw [← Int.prime_iff_natAbs_prime, ← Ideal.span_singleton_prime hg,
    Ideal.span_singleton_generator]
  exact hJ

end Blocks

theorem divSuppArith : DivSuppArithStatement := by
  intro K _ ι _ P n A s W hP hs hW
  obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  obtain ⟨a, -, hsa, hsP⟩ := hs
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hsa hWmin
  have := hPp
  have h1 := dim_quot_minimal_add_one P W s hsP hWmin
  rw [hPdim] at h1
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
  exact ⟨fun hh => ⟨hK, ⟨hWp, hWmh, hWrel⟩, hh, hdim⟩,
    fun hv => ⟨⟨hWp, hWmh, hWrel⟩, charOf_prime hWp hv, hdim⟩⟩

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

theorem isMultiHomog_X {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (q : Σ k, ι k) :
    IsMultiHomog (X q : MRing ι) (fun k => ∑ i, (Finsupp.single q 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩) := by
  intro m hm k
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  rfl

theorem isMultiHomogIdeal_span_X {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (q : Σ k, ι k) : IsMultiHomogIdeal (Ideal.span {(X q : MRing ι)}) := by
  refine ⟨{X q}, ?_, rfl⟩
  rintro f rfl
  exact ⟨_, isMultiHomog_X q⟩

theorem exists_anLogRes (hE : ResExistsStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} (hP : IsArithVar P (e + 1)) :
    ∃ J : Ideal (MRing ι), Nonempty (AnLogRes P J e) := by
  obtain ⟨⟨k⟩, ⟨-, -, hrel⟩, -, -⟩ := id hP
  obtain ⟨i, hi⟩ := hrel k
  obtain ⟨J', -, -, -, hR⟩ := hE K ι P (Ideal.span {(X ⟨k, i⟩ : MRing ι)}) e hP
    (isMultiHomogIdeal_span_X _) (fun h => hi (h (Ideal.mem_span_singleton_self _)))
  exact ⟨J', hR⟩

theorem ptsIndep_of (hE : ResExistsStatement) (hB : ResBridgeStatement) : PtsIndepStatement := by
  intro K _ ι _ P e Ψ Ψ' L A s hP hΨ hΨ' hL hA hs
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  rw [hB K ι P J e R Ψ L A s hP hΨ hL hA hs, hB K ι P J e R Ψ' L A s hP hΨ' hL hA hs]

theorem ptsIntegral_eq_at (hE : ResExistsStatement) (hB : ResBridgeStatement) {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ptsIntegral P (pot L) (logNorm A s) = ptsIntegralAt P Ψ (pot L) (logNorm A s) := by
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ := ⟨Ψ, hΨ⟩
  unfold ptsIntegral
  rw [dite_eq_left hex]
  exact ptsIndep_of hE hB K ι P e _ _ L A s hP hex.choose_spec hΨ hL hA hs

theorem ptsIntegral_eq_mInt (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hG : GoodProjExistsStatement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {L : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ptsIntegral P (pot L) (logNorm A s) =
      mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  obtain ⟨Ψ, hΨ⟩ := hG K ι P e hP
  rw [ptsIntegral_eq_at hE hB hP hΨ hL hA hs]
  exact hB K ι P J e R Ψ L A s hP hΨ hL hA hs

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeL
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e)

theorem brFib_finite' (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} ∩ {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0}).Finite := by
  have hK : Nonempty K := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1

  refine Set.Finite.of_finite_image (f := brW R Ψ) ?_ ((brW_injOn R Ψ).mono Set.inter_subset_right)
  refine (fibreFinite K ι P e Ψ hP hΨ y).subset ?_
  rintro _ ⟨x, ⟨hxy, hx⟩, rfl⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hxy
  have h := brW_mem_fibre R Ψ hK hPh hx.2
  rwa [hxy] at h

theorem lift_mem_iff {x z : R.X} (hz : z ∈ R.U x) :
    R.lift z z ∈ mcPts J ↔ R.lift x z ∈ mcPts J := by
  have h1 : SameOrbit (R.lift z z) (R.lift x z) := R.compat z x z ⟨R.mem_U z, hz⟩
  have h2 : SameOrbit (R.lift x z) (R.lift z z) := R.compat x z z ⟨hz, R.mem_U z⟩
  exact ⟨mem_mcPts_of_sameOrbit R.homog h2, mem_mcPts_of_sameOrbit R.homog h1⟩

theorem psi_lift_eq {x z : R.X} (hz : z ∈ R.U x)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Ψ (segre (R.lift z z)) = μ • Ψ (segre (R.lift x z)) := by
  obtain ⟨c, hc, heq⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.2 fun k _ => hc k, ?_⟩
  rw [heq, segre_smul, map_smul]

theorem isOpen_chart_notB (j : Fin R.A.n) :
    IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J}) := by
  have hS : IsOpen {x : R.X | R.lift x x ∉ mcPts J} := by
    rw [isOpen_iff_forall_mem_open]
    intro x0 hx0
    have hP0 : R.lift x0 x0 ∈ mcPts P := R.mem x0 x0 (R.mem_U x0)

    have hex : ∃ f ∈ J, eval (R.lift x0 x0) (map (Int.castRingHom ℂ) f) ≠ 0 := by
      by_contra hcon
      exact hx0 ⟨hP0.1, fun f hf => not_not.1 fun h => hcon ⟨f, hf, h⟩⟩
    obtain ⟨f, hfJ, hf⟩ := hex
    have hcont : ContinuousOn (fun z => eval (R.lift x0 z) (map (Int.castRingHom ℂ) f)) (R.U x0) := by
      have hl : ContinuousOn (fun z => R.lift x0 z) (R.U x0) :=
        continuousOn_pi.2 fun p => continuousOn_lift R x0 p
      exact (MvPolynomial.continuous_eval _).comp_continuousOn hl
    refine ⟨R.U x0 ∩ (fun z => eval (R.lift x0 z) (map (Int.castRingHom ℂ) f)) ⁻¹' {w | w ≠ 0},
      ?_, hcont.isOpen_inter_preimage (R.isOpen_U x0) isOpen_ne, ⟨R.mem_U x0, hf⟩⟩
    rintro z ⟨hz, hzf⟩
    show R.lift z z ∉ mcPts J
    rw [lift_mem_iff R hz]
    exact fun h => hzf (h.2 f hfJ)
  exact (R.A.chart j).isOpen_inter_preimage_symm hS

theorem not_flat (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) {O : Set (Fin e → ℂ)}
    (hO : IsOpen O) (hOt : O ⊆ (R.A.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (brQ R Ψ ∘ (R.A.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by

  set O' := O ∩ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J})
  have hO' : IsOpen O' := hO.inter (isOpen_chart_notB R j)
  have hO'ne : O'.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : O ⊆ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J} := by
      intro u hu
      refine ⟨hOt hu, ?_⟩
      by_contra hb
      have hu' : u ∈ O' := ⟨hu, hOt hu, hb⟩
      rw [hcon] at hu'
      exact hu'
    exact (hO.measure_pos volume hne).ne' (measure_mono_null hsub (R.null j))

  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hO'ne (han.mono Set.inter_subset_left)
    (fun u hu => hdet u hu.1)
  apply hy
  refine Set.Finite.of_finite_image (f := (R.A.chart j).symm) ?_
    ((R.A.chart j).symm.injOn.mono fun u hu => hu.1.2.1)
  refine (brFib_finite' R Ψ hP hΨ y).subset ?_
  rintro _ ⟨u, ⟨huO', huy⟩, rfl⟩
  exact ⟨huy, huO'.2.2, h0 u huO'.1⟩

theorem analyticAt_det_fderiv {Q : (Fin e → ℂ) → (Fin e → ℂ)} {u : Fin e → ℂ}
    (hQ : AnalyticAt ℂ Q u) :
    AnalyticAt ℂ (fun v => LinearMap.det (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) u := by
  have hF : AnalyticAt ℂ (fderiv ℂ Q) u := hQ.fderiv

  have hentry : ∀ i j : Fin e, AnalyticAt ℂ
      (fun v => LinearMap.toMatrix' (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) i j) u := by
    intro i j
    have hL : AnalyticAt ℂ (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L (Pi.single j 1) i)
        (fderiv ℂ Q u) := by
      have h := ContinuousLinearMap.analyticAt
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).comp
          (ContinuousLinearMap.apply ℂ (Fin e → ℂ) (Pi.single j (1 : ℂ)))) (fderiv ℂ Q u)
      exact h
    have heq : (fun v => LinearMap.toMatrix' (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) i j) =
        fun v => fderiv ℂ Q v (Pi.single j 1) i := by
      funext v
      rw [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
    rw [heq]
    exact hL.comp hF

  have hdet : (fun v => LinearMap.det (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) =
      fun v => (LinearMap.toMatrix' (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))).det := by
    funext v
    rw [LinearMap.det_toMatrix']
  rw [hdet]
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hentry _ _)

theorem det_eq_zero_of_coord {L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)} (m : Fin e)
    (h : ∀ v, L v m = 0) : LinearMap.det (L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
  by_contra hd

  have hu : IsUnit (L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hd)
  obtain ⟨v, hv⟩ := ((Module.End.isUnit_iff _).1 hu).2 (Pi.single m 1)
  rw [ContinuousLinearMap.coe_coe] at hv
  have hvm := congrFun hv m
  rw [h v, Pi.single_eq_same] at hvm
  exact zero_ne_one hvm

theorem det_brQ_chart (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.X}
    {j k : Fin R.A.n} (hj : x ∈ (R.A.chart j).source) (hk : x ∈ (R.A.chart k).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  have hxj : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmem : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source :=
    ⟨(R.A.chart j).map_source hj, show (R.A.chart j).symm (R.A.chart j x) ∈ (R.A.chart k).source by
      rw [hxj]; exact hk⟩
  have hT : AnalyticAt ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) := R.A.holo j k _ hmem
  have hQk : AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :=
    analyticAt_brQ R Ψ x k hk h0

  have hev : (brQ R Ψ ∘ (R.A.chart j).symm) =ᶠ[𝓝 (R.A.chart j x)]
      (brQ R Ψ ∘ (R.A.chart k).symm) ∘ (R.A.chart k ∘ (R.A.chart j).symm) := by
    have hn : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source ∈
        𝓝 (R.A.chart j x) :=
      ((R.A.chart j).isOpen_inter_preimage_symm (R.A.chart k).open_source).mem_nhds hmem
    filter_upwards [hn] with v hv
    simp only [Function.comp_apply]
    rw [(R.A.chart k).left_inv hv.2]
  have hfx : (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) = R.A.chart k x := by
    simp only [Function.comp_apply]
    rw [hxj]
  have hg : DifferentiableAt ℂ (brQ R Ψ ∘ (R.A.chart k).symm)
      ((R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x)) := by
    rw [hfx]
    exact hQk.differentiableAt
  rw [hev.fderiv_eq, fderiv_comp _ hg hT.differentiableAt, hfx]
  exact LinearMap.det_comp _ _

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeF
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem maDensity_eq_maDens {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    maDensity φ z = ReciprocityTheory.AnForm.maDens φ z := rfl

theorem prod_norm_update_zpow [DecidableEq K] (k0 : K) (v : ℂ) (a : K → ℤ) :
    ∏ k, ‖Function.update (fun _ => (1 : ℂ)) k0 v k‖ ^ a k = ‖v‖ ^ a k0 := by
  rw [Finset.prod_eq_single k0]
  · simp
  · intro k _ hk
    simp [Function.update_apply, hk]
  · intro h
    exact absurd (Finset.mem_univ k0) h

theorem exists_sheet_brW (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hs : IsSectionOn P A s)
    (x : R.X) (hx : x ∉ brBad R Ψ) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ, IsSheet P Ψ (brQ R Ψ x) (brW R Ψ x) γ ∧
      logNorm A s (γ (brQ R Ψ x)) * maDensity (fun j y' => pot L j (γ y')) (brQ R Ψ x) =
        logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  set j := chartIdx R.A x with hjdef
  have hj : x ∈ (R.A.chart j).source := Classical.choose_spec (R.A.cover x)
  set u := R.A.chart j x with hudef
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have huU : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  obtain ⟨hQa, hQd⟩ := brGood R Ψ x hx j hj
  set Q := brQ R Ψ ∘ (R.A.chart j).symm with hQdef
  set Df := fderiv ℂ Q u with hDf
  have hdet : Df.det ≠ 0 := hQd
  set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe
  have hCe' : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = Df :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet
  have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
    rw [hCe']; exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph Q with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
  have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyt : Q u ∈ F.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hσu : F.symm (Q u) = u := by
    have := F.left_inv hus
    rwa [hFc] at this
  have hy0 : Q u = brQ R Ψ x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  set γ₀ : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' => R.lift x ((R.A.chart j).symm (F.symm y')) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := (analyticAt_lift_chart R x j huU).comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = R.lift x x := by simp only [hγ₀, hσu, hsu]
  set ψ0 : (Fin e → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp ((analyticAt_segre_lift R Ψ x j huU).comp_of_eq hσa hσu) 0
  have hψ0u : ψ0 (Q u) ≠ 0 := by
    simp only [hψ0, hγ₀u]; exact projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx
  set c : (Fin e → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹
    with hcdef
  have hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0 := by
    intro y' h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp only [hcdef, Function.update_self]; exact hψ0a.inv hψ0u
    · simp only [hcdef, Function.update_of_ne hk]; exact analyticAt_const
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef
  have hγa : AnalyticAt ℂ γ (Q u) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)
  have hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y') := fun y' => by
    rw [← hprod y']; exact segre_smul (c y') (γ₀ y')
  refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
  · rw [← hy0, hseg]
    simp only [hψ0, hγ₀u]
    rfl
  · rw [← hy0]
    have hU : ∀ᶠ y' in 𝓝 (Q u),
        F.symm y' ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]; exact ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt, mcPts_smul hPh (c y') (hc_ne y' h0) (R.mem x _ hUy.2), ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, brQ_eq_local R Ψ hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    obtain ⟨a, ha, hsa, -⟩ := hs
    have hlog : logNorm A s (γ (Q u)) = logNorm A s (R.lift x x) := by
      show logNorm A s (bsmul (c (Q u)) (γ₀ (Q u))) = _
      rw [logNorm_bsmul A ha hsa (hc_ne _ hψ0u), hγ₀u]
    rw [hlog]
    congr 1
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact (R.mem x x (R.mem_U x)).1
    have hH : ∀ i, cxHessian (fun y' => pot L i (γ y')) (Q u) =
        cxHessian (fun y' => pot L i (γ₀ y')) (Q u) := by
      intro i
      set G : (Fin e → ℂ) → ℂ :=
        fun y' => ((-((L i).a k0 : ℝ) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(((L i).a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u]
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => pot L i (γ y')) =ᶠ[𝓝 (Q u)]
          fun y' => pot L i (γ₀ y') + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u,
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < (L i).h (γ₀ y') := (L i).pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ (L i).a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [pot, hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl, (L i).smul _ _ (hc_ne y' h0), prod_norm_update_zpow, Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => pot L i (γ₀ y')) C
        (pot_contDiffAt (hL i) hγ₀a hblk) hGa]
    have hmd : maDensity (fun i y' => pot L i (γ y')) (Q u) =
        maDensity (fun i y' => pot L i (γ₀ y')) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd, maDensity_eq_maDens]
    have hcd : ∀ i, ContDiffAt ℝ 2 (fun v => pot L i (R.lift x ((R.A.chart j).symm v)))
        (F.symm (Q u)) := by
      intro i
      rw [hσu]
      exact pot_contDiffAt (hL i) (analyticAt_lift_chart R x j huU)
        (by rw [hsu]; exact (R.mem x x (R.mem_U x)).1)
    have hcomp : ReciprocityTheory.AnForm.maDens (fun i y' => pot L i (γ₀ y')) (Q u) =
        ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.lift x ((R.A.chart j).symm v)))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun i v => pot L i (R.lift x ((R.A.chart j).symm v)))
        F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    have hloc : ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.lift x ((R.A.chart j).symm v))) u =
        locDens R.A (fun i => potOf R (L i)) j u := by
      unfold locDens
      rw [hsu]
      rfl
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    unfold pushDens
    rw [div_eq_mul_inv]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeJ
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

def LogAbsLocIntStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (f : (Fin D → ℂ) → ℂ), IsOpen U → AnalyticOnNhd ℂ f U →
    LocallyIntegrableOn (fun z => Real.log ‖f z‖) U volume

theorem analyticAt_eval_poly {D : ℕ} {σ : Type*} (p : MvPolynomial σ ℂ)
    {γ : (Fin D → ℂ) → σ → ℂ} {u : Fin D → ℂ} (hγ : ∀ i, AnalyticAt ℂ (fun v => γ v i) u) :
    AnalyticAt ℂ (fun v => eval (γ v) p) u := by
  induction p using MvPolynomial.induction_on
  · simpa using analyticAt_const
  · rename_i p q hp hq
    have h := hp.add hq
    simp only [map_add (f := _)]
    exact h
  · rename_i p i hp
    have h := hp.mul (hγ i)
    simp only [map_mul, MvPolynomial.eval_X]
    exact h

theorem abs_log_div_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.log (a / b)| ≤ |Real.log a| + |Real.log b| := by
  rcases ha.eq_or_lt with h | h
  · subst h
    simp
  · rw [Real.log_div h.ne' hb.ne', abs_le]
    constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
      le_abs_self (Real.log b), neg_abs_le (Real.log b)]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem brIntegrable_of (hLA : LogAbsLocIntStatement) (R : AnLogRes P J e)
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  classical
  obtain ⟨a, hAa, hsa, -⟩ := hs
  have hpot : ∀ i, IsPotential R.A (potOf R (L i)) := fun i => isPotential_potOf R (hL i)
  intro j Kc hKt hKc
  have hdens := locDensCont R.A (fun i => potOf R (L i)) hpot j
  have hloc : LocallyIntegrableOn
      (fun y => logNorm A s (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)))
      (R.A.chart j).target volume := by
    intro y0 hy0
    let x0 := (R.A.chart j).symm y0
    let V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0
    have hVo : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
    have hy0V : y0 ∈ V := ⟨hy0, R.mem_U x0⟩
    let γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun v => R.lift x0 ((R.A.chart j).symm v)
    let F : (Fin e → ℂ) → ℂ := fun v => eval (γ v) (map (Int.castRingHom ℂ) s)
    let H : (Fin e → ℂ) → ℝ := fun v => A.h (γ v)
    have hγa : ∀ y ∈ V, ∀ p, AnalyticAt ℂ (fun v => γ v p) y := fun y hy p => R.holo x0 p j y hy
    have hFan : AnalyticOnNhd ℂ F V := fun y hy => analyticAt_eval_poly _ (hγa y hy)
    have hγc : ContinuousOn γ V := continuousOn_pi.mpr (fun p => (R.holo x0 p j).continuousOn)
    have hnz : ∀ y ∈ V, ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := fun y hy => (R.mem x0 _ hy.2).1
    have hHpos : ∀ y ∈ V, 0 < H y := fun y hy => A.pos _ (hnz y hy)
    have hHc : ContinuousOn H V := hA.continuousOn.comp hγc (fun y hy => hnz y hy)
    have hlogH : ContinuousOn (fun y => Real.log (H y)) V := hHc.log (fun y hy => (hHpos y hy).ne')
    have hlogF : LocallyIntegrableOn (fun y => Real.log ‖F y‖) V volume := hLA e V F hVo hFan
    have hinv : ∀ y ∈ V, logNorm A s (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) =
        Real.log (‖F y‖ / H y) := by
      intro y hy
      obtain ⟨c, hc, hcz⟩ := R.compat ((R.A.chart j).symm y) x0 ((R.A.chart j).symm y)
        ⟨R.mem_U _, hy.2⟩
      rw [hcz]
      have h1 := logNorm_bsmul A hAa hsa hc (R.lift x0 ((R.A.chart j).symm y))
      exact h1
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVo y0 hy0V
    have hBV : Metric.closedBall y0 (δ / 2) ⊆ V :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hBc : IsCompact (Metric.closedBall y0 (δ / 2)) := isCompact_closedBall y0 (δ / 2)
    have hBm : MeasurableSet (Metric.closedBall y0 (δ / 2)) :=
      Metric.isClosed_closedBall.measurableSet
    refine ⟨Metric.closedBall y0 (δ / 2),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y0 (by linarith)), ?_⟩
    have hmeas : AEStronglyMeasurable (fun y => Real.log (‖F y‖ / H y))
        (volume.restrict (Metric.closedBall y0 (δ / 2))) := by
      have hF' : AEMeasurable (fun y => ‖F y‖) (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        ((hFan.continuousOn.mono hBV).aestronglyMeasurable hBm).norm.aemeasurable
      have hH' : AEMeasurable H (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        ((hHc.mono hBV).aestronglyMeasurable hBm).aemeasurable
      exact (Real.measurable_log.comp_aemeasurable (hF'.div hH')).aestronglyMeasurable
    have hint : IntegrableOn (fun y => Real.log (‖F y‖ / H y)) (Metric.closedBall y0 (δ / 2))
        volume := by
      have hb : Integrable (fun y => |Real.log ‖F y‖| + |Real.log (H y)|)
          (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        (Integrable.abs (hlogF.integrableOn_compact_subset hBV hBc)).add
          (Integrable.abs ((hlogH.mono hBV).integrableOn_compact hBc))
      refine hb.mono' hmeas ?_
      refine (ae_restrict_iff' hBm).mpr (Filter.Eventually.of_forall (fun y hy => ?_))
      rw [Real.norm_eq_abs]
      exact abs_log_div_le (norm_nonneg _) (hHpos y (hBV hy))
    exact hint.congr_fun (fun y hy => (hinv y (hBV hy)).symm) hBm
  exact (hloc.integrableOn_compact_subset hKt hKc).mul_continuousOn (hdens.mono hKt) hKc

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
