module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumNormSqOrbit
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsAlgebraicIndependentRatiosOfGenericZero
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoordsNoHomogeneousRelationGenericHyperpla
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoordsNoHomogeneousRelationGenericHyperpla
namespace GlobalTheory


open MvPolynomial in
theorem aeval_mul_of_isHomogeneous_cone {K L ι : Type} [CommRing K] [CommRing L] [Algebra K L]
    {Q : MvPolynomial ι K} {d : ℕ} (hQ : Q.IsHomogeneous d) (c : L) (x : ι → L) :
    aeval (fun a => c * x a) Q = c ^ d * aeval x Q := by
  classical
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hQ.degree_eq_sum_deg_support hs
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hd]
  ring


open MvPolynomial in
theorem aeval_eq_pow_mul_aeval_dehomogenise {K L : Type} [CommRing K] [Field L] [Algebra K L]
    {m : ℕ} {Q : MvPolynomial (Fin (m + 1)) K} {d : ℕ} (hQ : Q.IsHomogeneous d)
    (x : Fin (m + 1) → L) (hx : x 0 ≠ 0) :
    aeval x Q = x 0 ^ d * aeval (fun a : Fin m => x a.succ / x 0)
      (aeval (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) Q) := by
  set y : Fin m → L := fun a => x a.succ / x 0 with hy
  have hx' : x = fun a => x 0 * (Fin.cons 1 y : Fin (m + 1) → L) a := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · simp
    · simp only [Fin.cons_succ, hy]
      field_simp
  have key : (fun i => aeval y ((Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) i)) =
      (Fin.cons 1 y : Fin (m + 1) → L) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  conv_lhs => rw [hx']
  rw [aeval_mul_of_isHomogeneous_cone hQ,
    aeval_eq_bind₁ (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K), aeval_bind₁, key]


open MvPolynomial in
theorem dehomogenise_ne_zero_of_isHomogeneous {K : Type} [Field K]
    {m : ℕ} {Q : MvPolynomial (Fin (m + 1)) K} {d : ℕ} (hQ : Q.IsHomogeneous d) (h0 : Q ≠ 0) :
    aeval (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) Q ≠ 0 := by
  intro h
  have hinj := IsFractionRing.injective (MvPolynomial (Fin (m + 1)) K)
    (FractionRing (MvPolynomial (Fin (m + 1)) K))
  have hx0 : (algebraMap (MvPolynomial (Fin (m + 1)) K) (FractionRing (MvPolynomial (Fin (m + 1)) K)) ∘
      X) 0 ≠ 0 := by
    simp only [Function.comp_apply]
    exact (map_ne_zero_iff _ hinj).mpr (X_ne_zero 0)
  have e := aeval_eq_pow_mul_aeval_dehomogenise (L := FractionRing (MvPolynomial (Fin (m + 1)) K)) hQ
    (algebraMap (MvPolynomial (Fin (m + 1)) K) (FractionRing (MvPolynomial (Fin (m + 1)) K)) ∘ X) hx0
  rw [h, map_zero, mul_zero, aeval_algebraMap_apply, aeval_X_left_apply] at e
  exact h0 (hinj (by rw [e, map_zero]))

theorem exists_coordinates_no_homogeneous_relation_of_generic_zero :
    ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ),
    (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 →
    (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N,
      ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d →
        MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by
  intro K _ σ m N t ζ ht hζ hrel
  let _ : Algebra K ℂ := σ.toAlgebra
  obtain _ | N := N
  · exact absurd (funext fun j => j.elim0) hζ
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hζ
  have hj0' : ζ j0 ≠ 0 := hj0
  have hind : AlgebraicIndependent K t := by
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra hne
    exact ht p hne hp
  obtain ⟨J, hJ⟩ := exists_algebraicIndependent_ratios_of_generic_zero K ℂ m N t ζ j0 hind hj0' hrel
  refine ⟨Fin.cons j0 J, fun Q d hQ0 hQ => ?_⟩
  have e := aeval_eq_pow_mul_aeval_dehomogenise (L := ℂ) hQ
    (fun a => ζ ((Fin.cons j0 J : Fin (m + 1) → Fin (N + 1)) a)) (by simpa using hj0')
  change MvPolynomial.aeval _ Q ≠ 0
  rw [e]
  simp only [Fin.cons_zero, Fin.cons_succ]
  refine mul_ne_zero (pow_ne_zero _ hj0') ?_
  intro h
  exact dehomogenise_ne_zero_of_isHomogeneous hQ hQ0 ((algebraicIndependent_iff.mp hJ) _ h)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoordsNoHomogeneousRelationGenericHyperplaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ), (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 → (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N, ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d → MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by
  first | exact @GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero | exact GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero | (intros; apply GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeTranscendentalPointNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeTranscendentalPointNonvanishing
open MeasureTheory

namespace GlobalTheory

theorem ae_eval₂_ne_zero_of_countable (K : Type) [Field K] [Countable K] (σ : K →+* ℂ)
    (ι : Type) [Fintype ι] :
    ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by
  have : Countable (MvPolynomial ι K) :=
    (MvPolynomial.basisMonomials ι K).repr.injective.countable
  rw [ae_all_iff]
  intro Q
  by_cases hQ : Q = 0
  · exact Filter.Eventually.of_forall fun t h => absurd hQ h
  · have hm : MvPolynomial.map σ Q ≠ 0 := by
      intro h
      exact hQ (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero]))
    have h := ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (ι → ℂ))
      (LinearEquiv.refl ℂ (ι → ℂ)) _ hm
    filter_upwards [h] with t ht _
    rw [MvPolynomial.eval₂_eq_eval_map]
    exact ht

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeTranscendentalPointNonvanishingStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_transcendental_point_nonvanishing : ∀ (K : Type) [Field K] [Countable K] (σ : K →+* ℂ) (ι : Type) [Fintype ι], ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by
  first | exact @GlobalTheory.ae_eval₂_ne_zero_of_countable | exact GlobalTheory.ae_eval₂_ne_zero_of_countable | (intros; apply GlobalTheory.ae_eval₂_ne_zero_of_countable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeExistsFlatDatumLinearCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsBoundedByGenericCombinations
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsBoundedByGenericCombinations
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem cone_sum_sq_le {m N : ℕ} (t : Fin m × Fin N → ℂ) (Z : Set (Fin N → ℂ)) (hZ : IsClosed Z)
    (hc : ∀ (c : ℂ), ∀ ζ ∈ Z, c • ζ ∈ Z) (h0 : ∀ ζ ∈ Z, (∀ i, ∑ j, t (i, j) * ζ j = 0) → ζ = 0) :
    ∃ C : ℝ, ∀ ζ ∈ Z, ∑ k, ‖ζ k‖ ^ 2 ≤ C * ∑ i, ‖∑ j, t (i, j) * ζ j‖ ^ 2 := by
  set f : (Fin N → ℂ) → ℝ := fun ζ => ∑ i, ‖∑ j, t (i, j) * ζ j‖ ^ 2 with hf
  set g : (Fin N → ℂ) → ℝ := fun ζ => ∑ k, ‖ζ k‖ ^ 2 with hg
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hS : IsCompact (Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z) := (isCompact_sphere _ _).inter_right hZ
  have hfnn : ∀ ζ, 0 ≤ f ζ := fun ζ => Finset.sum_nonneg fun i _ => by positivity
  have hpos : ∀ ζ ∈ Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z, 0 < f ζ := by
    rintro ζ ⟨h1, h2⟩
    refine lt_of_le_of_ne (hfnn ζ) fun h => ?_
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h.symm
    have h4 : ζ = 0 := h0 ζ h2 fun i => by simpa using h3 i (Finset.mem_univ i)
    simp [h4] at h1
  obtain ⟨C, hC⟩ := hS.bddAbove_image (f := fun ζ => g ζ / f ζ)
    (hgc.continuousOn.div hfc.continuousOn fun ζ hζ => (hpos ζ hζ).ne')
  refine ⟨C, fun ζ hζ => ?_⟩
  by_cases hz : ζ = 0
  · simp [hz]
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hz
  set c : ℂ := ((‖ζ‖⁻¹ : ℝ) : ℂ) with hcdef
  have hcn : ‖c‖ = ‖ζ‖⁻¹ := by simp [hcdef]
  have hmem : c • ζ ∈ Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z :=
    ⟨by rw [mem_sphere_zero_iff_norm, norm_smul, hcn, inv_mul_cancel₀ hn.ne'], hc c ζ hζ⟩
  have h1 : g (c • ζ) ≤ C * f (c • ζ) := (div_le_iff₀ (hpos _ hmem)).1 (hC ⟨_, hmem, rfl⟩)
  have h2 : g (c • ζ) = ‖c‖ ^ 2 * g ζ := by
    simp only [hg, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  have h3 : f (c • ζ) = ‖c‖ ^ 2 * f ζ := by
    simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_pow, ← norm_mul, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun j _ => by ring
  have h4 : 0 < ‖c‖ ^ 2 := by rw [hcn]; positivity
  rw [h2, h3, mul_left_comm] at h1
  exact le_of_mul_le_mul_left h1 h4

theorem eval₂_smul_of_isHomogeneous {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} {Q : MvPolynomial (Fin n) K}
    (hQ : Q.IsHomogeneous d) (c : ℂ) (z : Fin n → ℂ) :
    MvPolynomial.eval₂ σ (fun a => c * z a) Q = c ^ d * MvPolynomial.eval₂ σ z Q := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h := hQ (MvPolynomial.mem_support_iff.1 hs)
  have h' : ∑ a, s a = d := by
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h']
  ring

theorem forms_le_generic_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖sf i x‖ ^ 2 := by
  intro E _ _ _ r X Xa K _ σ t ht hrel sf
  choose Q d hQ0 hQd hQ using hrel.1
  let Z : Set (Fin Xa.N → ℂ) := {ζ | ∀ jj, MvPolynomial.eval₂ σ (fun a => ζ (jj a)) (Q jj) = 0}
  have hZ : IsClosed Z := by
    simp only [Z, Set.setOf_forall]
    refine isClosed_iInter fun jj => isClosed_eq ?_ continuous_const
    simp only [MvPolynomial.eval₂_eq']
    fun_prop
  obtain ⟨C, hC⟩ := cone_sum_sq_le t Z hZ
    (fun c ζ hζ jj => by
      have := eval₂_smul_of_isHomogeneous σ (hQd jj) c fun a => ζ (jj a)
      rw [hζ jj, mul_zero] at this
      exact this)
    (fun ζ hζ h => by
      by_contra hz
      obtain ⟨jj, hjj⟩ := GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes K σ _ _ t ζ ht hz h
      exact hjj _ _ (hQ0 jj) (hQd jj) (hζ jj))
  exact ⟨C, fun x hx => hC (fun k => Xa.w k x) fun jj => hQ jj x hx⟩

end GlobalTheory.Shares
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsBoundedByGenericCombinationsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_forms_bounded_by_generic_combinations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖sf i x‖ ^ 2 := by
  first | exact @GlobalTheory.Shares.forms_le_generic_comb | exact GlobalTheory.Shares.forms_le_generic_comb | (intros; apply GlobalTheory.Shares.forms_le_generic_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsNotSmallWhereCombinationsVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsNotSmallWhereCombinationsVanish
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares.Low

open MvPolynomial Filter

section Alg

variable {K : Type} [Field K] (σ : K →+* ℂ)

theorem eval₂_smul_of_isHomogeneous {ι : Type} {F : MvPolynomial ι K} {e : ℕ} (hF : F.IsHomogeneous e)
    (x : ι → ℂ) (c : ℂ) : eval₂ σ (fun j => c * x j) F = c ^ e * eval₂ σ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = e := by
    have := hF (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem eval₂_cons_zero {n : ℕ} (y : Fin n → ℂ) (Q : MvPolynomial (Fin (n + 1)) K) :
    eval₂ σ (Fin.cons 0 y : Fin (n + 1) → ℂ) Q = eval₂ σ y ((finSuccEquiv K n Q).coeff 0) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have : finSuccEquiv K n (C a) = Polynomial.C (C a) := by simp [finSuccEquiv_apply]
    simp [this]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, eval₂_mul, eval₂_mul, hp]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [finSuccEquiv_X_zero]
    · simp [finSuccEquiv_X_succ]

theorem exists_rel_coeff_zero_ne {Y : Type} {n : ℕ} (S : Set Y) (u : Fin (n + 1) → Y → ℂ)
    (hu : ∀ x ∈ S, u 0 x ≠ 0) (d : ℕ) : ∀ Q : MvPolynomial (Fin (n + 1)) K, Q ≠ 0 → Q.IsHomogeneous d →
      (∀ x ∈ S, eval₂ σ (fun i => u i x) Q = 0) →
      ∃ (Q' : MvPolynomial (Fin (n + 1)) K) (d' : ℕ), (finSuccEquiv K n Q').coeff 0 ≠ 0 ∧ Q'.IsHomogeneous d' ∧
        ∀ x ∈ S, eval₂ σ (fun i => u i x) Q' = 0 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro Q hQ hh hv
    by_cases h0 : (finSuccEquiv K n Q).coeff 0 = 0
    · obtain ⟨p, hp⟩ := Polynomial.X_dvd_iff.mpr h0
      set Q1 := (finSuccEquiv K n).symm p with hQ1
      have hQQ : Q = MvPolynomial.X 0 * Q1 := by
        apply (finSuccEquiv K n).injective
        rw [map_mul, finSuccEquiv_X_zero, hQ1, AlgEquiv.apply_symm_apply, hp]
      have hQ1ne : Q1 ≠ 0 := by
        rintro h
        rw [h, mul_zero] at hQQ
        exact hQ hQQ
      have key : ∀ m, Q1.coeff m ≠ 0 → Finsupp.weight (1 : Fin (n + 1) → ℕ) m + 1 = d := by
        intro m hm
        have h1 : Q.coeff (Finsupp.single 0 1 + m) ≠ 0 := by
          rw [hQQ, coeff_X_mul]; exact hm
        have := hh h1
        rw [map_add (f := _), Finsupp.weight_single] at this
        simp at this
        omega
      obtain ⟨m, hm⟩ := ne_zero_iff.mp hQ1ne
      have hd := key m hm
      refine ih (d - 1) (by omega) Q1 hQ1ne (fun m' hm' => ?_) (fun x hx => ?_)
      · have := key m' hm'
        omega
      · have := hv x hx
        rw [hQQ, eval₂_mul, eval₂_X] at this
        exact (mul_eq_zero.mp this).resolve_left (hu x hx)
    · exact ⟨Q, d, h0, hh, hv⟩

theorem continuous_eval₂ {ι : Type} (Q : MvPolynomial ι K) : Continuous fun y : ι → ℂ => eval₂ σ y Q := by
  have := MvPolynomial.continuous_eval (MvPolynomial.map σ Q)
  simpa only [eval_map] using this

theorem isHomogeneous_expand {ι : Type} {F : MvPolynomial ι K} {e : ℕ} (hF : F.IsHomogeneous e) (k : ℕ) :
    (expand k F).IsHomogeneous (k * e) := by
  have := hF.aeval (fun i => (MvPolynomial.X i : MvPolynomial ι K) ^ k) (n := k) (fun i => by
    simpa using (isHomogeneous_X K i).pow k)
  exact this

theorem eval₂_expand' {ι : Type} (F : MvPolynomial ι K) (k : ℕ) (y : ι → ℂ) :
    eval₂ σ y (expand k F) = eval₂ σ (fun i => y i ^ k) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end Alg

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (Xa : ArchInM X)

theorem decay_le : ∃ C : ℝ, ∀ x ∈ X.dom, ‖Xa.et x * Xa.th1 x ^ (Xa.i * (Xa.g0 / 2))‖ ^ 2 ≤
    C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) * (‖fun j => Xa.w j x‖ ^ (2 * (Xa.i * (Xa.g0 / 2)))) ^ 2 := by
  obtain ⟨K3, h3⟩ := Xa.p3
  obtain ⟨K4, h4⟩ := Xa.p4
  obtain ⟨B, hB⟩ := Xa.firstTheta_vanishes.1.1.2
  set n1 := Xa.i * (Xa.g0 / 2) with hn1
  refine ⟨|K4| * (B ^ 2) ^ n1 * |K3| ^ (2 * n1 + 1) * (Xa.N : ℝ) ^ (2 * n1), fun x hx => ?_⟩
  set W := ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hW
  set ρ := ‖fun j => Xa.w j x‖ with hρ
  set e := Real.exp (-phla X Xa.L x) with he
  have he0 : 0 < e := Real.exp_pos _
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hWle : W ≤ Xa.N * ρ ^ 2 * e := by
    rw [hW, OW.sum_pnorm_sq X _ _ hx]
    refine mul_le_mul_of_nonneg_right ?_ he0.le
    calc ∑ k, Complex.normSq (Xa.w k x) ≤ ∑ _k : Fin Xa.N, ρ ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← Complex.sq_norm]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (fun j => Xa.w j x) k) 2
      _ = Xa.N * ρ ^ 2 := by simp
  have hph : phla X (n1 • Xa.de) x + n1 * phla X (2 • Xa.L - Xa.de) x = ((2 * n1 : ℕ) : ℝ) * phla X Xa.L x := by
    have h0 : phla X 0 x = 0 := by rw [IW.phla_eq X hx]; simp
    rw [← OW.phla_add_nsmul X hx]
    have : n1 • Xa.de + n1 • (2 • Xa.L - Xa.de) = 0 + (2 * n1) • Xa.L := by
      rw [smul_sub, ← mul_smul, mul_comm]; abel
    rw [this, OW.phla_add_nsmul X hx, h0, zero_add]
  have hid : ‖Xa.et x * Xa.th1 x ^ n1‖ ^ 2 * e ^ (2 * n1) =
      X.pnorm (n1 • Xa.de) Xa.et x ^ 2 * (X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2) ^ n1 := by
    rw [OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, he, ← Real.exp_nat_mul, mul_neg, ← hph, neg_add, Real.exp_add,
      ← mul_neg, Real.exp_nat_mul, ← Complex.sq_norm, ← Complex.sq_norm, norm_mul, norm_pow]
    ring
  have hpt : X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hB x hx) 2
  have hk : ((2 * n1 : ℕ) : ℝ) = Xa.i * Xa.g0 := by
    obtain ⟨m, hm⟩ := Xa.genus_even
    have : 2 * n1 = Xa.i * Xa.g0 := by
      rw [hn1, hm, ← two_mul, Nat.mul_div_cancel_left _ two_pos]; ring
    rw [this]; push_cast; rfl
  have hexp : Real.exp (-(2 * Xa.i * Xa.ph x)) ≤ Real.exp (-(2 * Xa.c * Xa.ph x)) ^ (2 * n1 + 1) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp, Nat.cast_add, hk]
    have hT : (2 : ℝ) ≤ Xa.T := by
      have h1 := Xa.T_ge
      have h2 := Xa.n_ge
      have : 2 ≤ Xa.T := by nlinarith
      exact_mod_cast this
    have hi : (1 : ℝ) ≤ Xa.i := by exact_mod_cast Xa.i_pos
    have hg : (1 : ℝ) ≤ Xa.g0 := by exact_mod_cast Xa.genus_pos
    have hc := Xa.c_pos
    have hT' := Xa.Tcg0
    have hφ := Xa.ph_nonneg x hx
    have a1 : Xa.c * Xa.g0 ≤ 1 / 2 := by nlinarith [mul_pos hc (lt_of_lt_of_le one_pos hg)]
    have a2 : Xa.c ≤ 1 / 2 := by nlinarith
    have a3 : (Xa.i * Xa.g0 + 1) * Xa.c ≤ Xa.i := by nlinarith
    have := mul_le_mul_of_nonneg_right a3 hφ
    push_cast
    nlinarith
  have hg : Real.exp (-(2 * Xa.c * Xa.ph x)) ≤ |K3| * W :=
    (h3 x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hW0)
  have hpe : X.pnorm (n1 • Xa.de) Xa.et x ^ 2 ≤ |K4| * (|K3| * W) ^ (2 * n1 + 1) :=
    (h4 x hx).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (hexp.trans (pow_le_pow_left₀ (Real.exp_pos _).le hg _)) (abs_nonneg _)))
  refine le_of_mul_le_mul_right ?_ (pow_pos he0 (2 * n1))
  rw [hid]
  calc _ ≤ (|K4| * (|K3| * W) ^ (2 * n1 + 1)) * (B ^ 2) ^ n1 :=
        mul_le_mul hpe (pow_le_pow_left₀ (sq_nonneg _) hpt _) (by positivity) (by positivity)
    _ = |K4| * (B ^ 2) ^ n1 * |K3| ^ (2 * n1 + 1) * W * W ^ (2 * n1) := by ring
    _ ≤ |K4| * (B ^ 2) ^ n1 * |K3| ^ (2 * n1 + 1) * W * (Xa.N * ρ ^ 2 * e) ^ (2 * n1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hWle _) (by positivity)
    _ = _ := by ring

theorem exists_rel {K : Type} [Field K] (σ : K →+* ℂ) (hR : RelIn σ X Xa) (jj : Fin (nd X + 1) → Fin Xa.N) :
    ∃ (Q : MvPolynomial (Fin (nd X + 2)) K) (d : ℕ), (finSuccEquiv K (nd X + 1) Q).coeff 0 ≠ 0 ∧ Q.IsHomogeneous d ∧
      ∀ x ∈ X.dom, eval₂ σ (Fin.cons (Xa.et x * Xa.th1 x ^ (Xa.i * (Xa.g0 / 2)))
        (fun a => Xa.w (jj a) x ^ (2 * (Xa.i * (Xa.g0 / 2)))) : Fin (nd X + 2) → ℂ) Q = 0 := by
  obtain ⟨Q, d, hQ, hh, hv⟩ := hR.2 jj
  have hdense := GlobalTheory.GenFrame.subset_closure_forall_ne_zero (FourierCoefficientDomain.isOpen_dom X)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected (J := Bool) (fun b => cond b Xa.et Xa.th1)
    (fun b => by
      cases b
      · exact Xa.firstTheta_vanishes.1.1.1.1
      · exact Xa.et_sec.1)
    (fun b => by
      cases b
      · exact Xa.firstTheta_ne_zero
      · exact Xa.et_ne)
  obtain ⟨Q', d', h0, hh', hv'⟩ := exists_rel_coeff_zero_ne σ {x | x ∈ X.dom ∧ ∀ b : Bool, cond b Xa.et Xa.th1 x ≠ 0} _
    (fun x hx => mul_ne_zero (hx.2 true) (pow_ne_zero _ (hx.2 false))) d Q hQ hh (fun x hx => hv x hx.1)
  refine ⟨Q', d', h0, hh', fun x hx => ?_⟩
  set u : Fin (nd X + 2) → Frame X.Ψ r → ℂ := Fin.cons (fun x => Xa.et x * Xa.th1 x ^ (Xa.i * (Xa.g0 / 2)))
    fun a x => Xa.w (jj a) x ^ (2 * (Xa.i * (Xa.g0 / 2))) with hu
  have hcont : ContinuousOn (fun x => eval₂ σ (fun i => u i x) Q') X.dom := by
    refine (continuous_eval₂ σ Q').comp_continuousOn (continuousOn_pi.mpr fun i => ?_)
    refine Fin.cases ?_ (fun a => ?_) i
    · exact Xa.et_sec.1.continuousOn.mul (Xa.firstTheta_vanishes.1.1.1.1.continuousOn.pow _)
    · exact (Xa.w_van (jj a)).1.1.1.1.continuousOn.pow _
  have hz : eval₂ σ (fun i => u i x) Q' = 0 := by
    have h1 := ((hcont x hx).mono (fun y hy => hy.1 :
      {x | x ∈ X.dom ∧ ∀ b : Bool, cond b Xa.et Xa.th1 x ≠ 0} ⊆ X.dom)).mem_closure (t := {0}) (hdense hx)
      (fun y hy => hv' y hy)
    simpa using h1
  convert hz using 2
  funext i
  refine Fin.cases rfl (fun a => rfl) i

end Model

theorem forms_not_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom, ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 < ε * ‖sf 0 x‖ ^ 2 → c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  intro E _ _ _ r X Xa K _ σ t ht hR sf
  by_contra hcon
  have hseq : ∀ n : ℕ, ∃ x ∈ X.dom, ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 < (1 / ((n : ℝ) + 1)) * ‖sf 0 x‖ ^ 2 ∧
      ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 < 1 / ((n : ℝ) + 1) := by
    intro n
    by_contra h
    push Not at h
    exact hcon ⟨_, _, Nat.one_div_pos_of_nat (n := n), Nat.one_div_pos_of_nat (n := n), h⟩
  choose xs hxs hs hw using hseq
  set k := 2 * (Xa.i * (Xa.g0 / 2)) with hk
  have hk0 : 0 < k := by
    have h1 := Xa.i_pos
    have h2 := Xa.genus_pos
    obtain ⟨m, hm⟩ := Xa.genus_even
    have : 0 < Xa.g0 / 2 := by omega
    positivity
  set ρ : ℕ → ℝ := fun n => ‖fun j => Xa.w j (xs n)‖ with hρ
  have hρ0 : ∀ n, 0 < ρ n := fun n => by
    obtain ⟨j, hj⟩ := Xa.w_nz _ (hxs n)
    exact norm_pos_iff.mpr fun h => hj (congrFun h j)
  set u : ℕ → Fin Xa.N → ℂ := fun n j => ((ρ n : ℂ))⁻¹ * Xa.w j (xs n) with hu
  have hnρ : ∀ n, ‖((ρ n : ℂ))⁻¹‖ = (ρ n)⁻¹ := fun n => by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hρ0 n).le]
  have hu1 : ∀ n, u n ∈ Metric.sphere (0 : Fin Xa.N → ℂ) 1 := fun n => by
    have : u n = ((ρ n : ℂ))⁻¹ • fun j => Xa.w j (xs n) := rfl
    rw [mem_sphere_zero_iff_norm, this, norm_smul, hnρ]
    exact inv_mul_cancel₀ (hρ0 n).ne'
  obtain ⟨ζ, hζ, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin Xa.N → ℂ) 1).tendsto_subseq hu1
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  have hε : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hlin : ∀ i, Tendsto (fun n => ‖∑ j, t (i, j) * u (φ n) j‖ ^ 2) atTop (𝓝 (‖∑ j, t (i, j) * ζ j‖ ^ 2)) := fun i =>
    ((tendsto_finsetSum _ fun j _ => ((continuous_apply j).continuousAt.tendsto.comp hlim).const_mul _).norm).pow 2
  have hsu : ∀ i n, ‖∑ j, t (i, j) * u n j‖ ^ 2 = (ρ n)⁻¹ ^ 2 * ‖sf i (xs n)‖ ^ 2 := fun i n => by
    have : ∑ j, t (i, j) * u n j = ((ρ n : ℂ))⁻¹ * sf i (xs n) := by
      simp only [hu, sf, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, norm_mul, hnρ, mul_pow]
  have hzero : ∀ i : Fin (nd X), ∑ j, t (i.succ, j) * ζ j = 0 := fun i => by
    have h1 := le_of_tendsto_of_tendsto' (hlin i.succ) (hε.mul (hlin 0)) (fun n => by
      rw [hsu, hsu, mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (Finset.single_le_sum (f := fun i : Fin (nd X) => ‖sf i.succ (xs (φ n))‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ i)).trans (hs (φ n)).le)
    rw [zero_mul] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h1 (by positivity)))
  obtain ⟨jj, hjj⟩ := GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero K σ (nd X) Xa.N (fun p => t (p.1.succ, p.2)) ζ (fun Q hQ => by
    have hinj : Function.Injective (fun p : Fin (nd X) × Fin Xa.N => ((p.1.succ, p.2) : Fin (nd X + 1) × Fin Xa.N)) :=
      (Fin.succ_injective _).prodMap Function.injective_id
    have := ht (rename _ Q) (fun h => hQ (rename_injective _ hinj (by rw [h, map_zero])))
    rwa [eval₂_rename] at this) hζ0 hzero
  obtain ⟨Q, d, h0, hh, hv⟩ := exists_rel X Xa σ hR jj
  refine hjj (expand k ((finSuccEquiv K (nd X + 1) Q).coeff 0)) (k * d) ((expand_ne_zero hk0).mpr h0)
    (isHomogeneous_expand (hh.finSuccEquiv_coeff_isHomogeneous 0 d (zero_add d)) k) ?_
  rw [eval₂_expand', ← eval₂_cons_zero]
  obtain ⟨C, hC⟩ := decay_le X Xa
  set b : ℕ → ℂ := fun n => ((ρ n : ℂ))⁻¹ ^ k * (Xa.et (xs n) * Xa.th1 (xs n) ^ (Xa.i * (Xa.g0 / 2))) with hb
  have hb0 : Tendsto (fun n => b (φ n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ‖b (φ n)‖ ^ 2) atTop (𝓝 0) := by
      have h2 := hε.const_mul |C|
      rw [mul_zero] at h2
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) h2
      have h3 := hC _ (hxs (φ n))
      have h4 : C * (∑ k, X.pnorm Xa.L (Xa.w k) (xs (φ n)) ^ 2) ≤ |C| * (1 / ((φ n : ℝ) + 1)) :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (hw (φ n)).le (abs_nonneg _))
      have h5 : 0 < (ρ (φ n) ^ k) ^ 2 := pow_pos (pow_pos (hρ0 _) _) _
      simp only [hb]
      rw [norm_mul, norm_pow, hnρ, mul_pow, inv_pow, inv_pow, inv_mul_le_iff₀' h5]
      exact h3.trans (mul_le_mul_of_nonneg_right h4 h5.le)
    have h2 := h1.sqrt
    simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h2
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h2
  have hval : ∀ n, eval₂ σ (Fin.cons (b n) (fun a => u n (jj a) ^ k) : Fin (nd X + 2) → ℂ) Q = 0 := fun n => by
    have h1 := eval₂_smul_of_isHomogeneous σ hh (Fin.cons (Xa.et (xs n) * Xa.th1 (xs n) ^ (Xa.i * (Xa.g0 / 2)))
        (fun a => Xa.w (jj a) (xs n) ^ k) : Fin (nd X + 2) → ℂ) (((ρ n : ℂ))⁻¹ ^ k)
    rw [hv _ (hxs n), mul_zero] at h1
    convert h1 using 2
    funext i
    refine Fin.cases rfl (fun a => ?_) i
    simp only [Fin.cons_succ, hu, mul_pow]
  have hT : Tendsto (fun n => (Fin.cons (b (φ n)) (fun a => u (φ n) (jj a) ^ k) : Fin (nd X + 2) → ℂ)) atTop
      (𝓝 (Fin.cons 0 (fun a => ζ (jj a) ^ k) : Fin (nd X + 2) → ℂ)) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    refine Fin.cases hb0 (fun a => ?_) i
    exact ((continuous_apply (jj a)).continuousAt.tendsto.comp hlim).pow k
  have hfin := (continuous_eval₂ σ Q).continuousAt.tendsto.comp hT
  exact tendsto_nhds_unique hfin (tendsto_const_nhds.congr fun n => (hval (φ n)).symm)

end GlobalTheory.Shares.Low
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsNotSmallWhereCombinationsVanishStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_forms_not_small_where_combinations_vanish : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom, ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 < ε * ‖sf 0 x‖ ^ 2 → c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  first | exact @GlobalTheory.Shares.Low.forms_not_small | exact GlobalTheory.Shares.Low.forms_not_small | (intros; apply GlobalTheory.Shares.Low.forms_not_small <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeCoefficientsCommonZerosSimple
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeCoefficientsCommonZerosSimple
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ParamSard

noncomputable def colProj {n N : ℕ} (j0 : Fin N) :
    (Fin (n + 1) × Fin N → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => WithLp.toLp 2 fun k => p (k.succ, j0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

noncomputable def colInc {n N : ℕ} (j0 : Fin N) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin (n + 1) × Fin N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v q => if q.2 = j0 then (Fin.cons 0 (fun k => v k) : Fin (n + 1) → ℂ) q.1 else 0
      map_add' := fun v w => by
        funext ⟨i, j⟩
        by_cases h : j = j0
        · refine Fin.cases ?_ (fun k => ?_) i <;> simp [h]
        · simp [h]
      map_smul' := fun c v => by
        funext ⟨i, j⟩
        by_cases h : j = j0
        · refine Fin.cases ?_ (fun k => ?_) i <;> simp [h]
        · simp [h] }

theorem colInc_apply {n N : ℕ} (j0 : Fin N) (v : EuclideanSpace ℂ (Fin n)) (k : Fin n) (j : Fin N) :
    colInc j0 v (k.succ, j) = if j = j0 then v k else 0 := by
  simp [colInc]

theorem colProj_colInc {n N : ℕ} (j0 : Fin N) (v : EuclideanSpace ℂ (Fin n)) :
    colProj j0 (colInc j0 v) = v := by
  ext k
  show colInc j0 v (k.succ, j0) = _
  simp [colInc_apply]

theorem ae_simple_col {n N : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (w : Fin N → EuclideanSpace ℂ (Fin n) → ℂ) (hw : ∀ j, DifferentiableOn ℂ (w j) U) (j0 : Fin N) :
    ∀ᵐ t : Fin (n + 1) × Fin N → ℂ, ∀ z ∈ U, w j0 z ≠ 0 → ∑ j, t (0, j) * w j z ≠ 0 →
      (∀ k : Fin n, ∑ j, t (k.succ, j) * w j z = 0) →
      (fderiv ℂ (fun y => (WithLp.toLp 2 fun k : Fin n =>
        (∑ j, t (k.succ, j) * w j y) / ∑ j, t (0, j) * w j y : EuclideanSpace ℂ (Fin n))) z).det ≠ 0 := by
  set S : (Fin (n + 1) × Fin N → ℂ) → EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
    fun p y => WithLp.toLp 2 fun k => (∑ j, p (k.succ, j) * w j y) / w j0 y with hS
  set G : (Fin (n + 1) × Fin N → ℂ) → (Fin (n + 1) × Fin N → ℂ) :=
    fun p => p - colInc j0 (S p (colProj j0 p)) with hG
  have hnull : volume (G '' {p | DifferentiableAt ℝ G p ∧ (fderiv ℝ G p).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := fun p => fderiv ℝ G p)
      (fun p hp => hp.1.hasFDerivAt.hasFDerivWithinAt) (fun p hp => hp.2)
  rw [← compl_mem_ae_iff] at hnull
  filter_upwards [hnull] with t ht z hz hw0 hs0 hsk hdet
  apply ht
  set F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun y => WithLp.toLp 2 fun k : Fin n =>
        (∑ j, t (k.succ, j) * w j y) / ∑ j, t (0, j) * w j y with hF
  have hwz : ∀ j, DifferentiableAt ℂ (w j) z := fun j => (hw j).differentiableAt (hU.mem_nhds hz)
  set A : EuclideanSpace ℂ (Fin n) → (Fin (n + 1) × Fin N → ℂ) :=
    fun y => t + colInc j0 (y - colProj j0 t) with hA
  have hπA : ∀ y, colProj j0 (A y) = y := fun y => by simp [hA, colProj_colInc]
  have hGA : ∀ y, w j0 y ≠ 0 → G (A y) = t - colInc j0 (S t y) := by
    intro y hy
    have : S (A y) y = S t y + (y - colProj j0 t) := by
      ext k
      simp only [hS, hA, Pi.add_apply, colInc_apply, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, PiLp.add_apply]
      field_simp
    simp only [hG, hπA, this]
    simp only [hA, map_add (f := _)]
    abel
  have hSz : S t z = 0 := by
    ext k
    simp [hS, hsk]
  have hFz : F z = 0 := by
    ext k
    simp [hF, hsk]
  have hsum : ∀ i, DifferentiableAt ℂ (fun y => ∑ j, t (i, j) * w j y) z := fun i =>
    DifferentiableAt.fun_sum fun j _ => (hwz j).const_mul _
  have hFd : DifferentiableAt ℂ F z := by
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have := (hsum k.succ).mul ((hsum 0).inv hs0)
    simp only [hF, div_eq_mul_inv]
    exact this
  have hGd : DifferentiableAt ℂ G (A z) := by
    refine differentiableAt_id.sub ((colInc j0).differentiableAt.comp _ ?_)
    have hwp : ∀ j, DifferentiableAt ℂ (fun p => w j (colProj j0 p)) (A z) := fun j =>
      DifferentiableAt.comp _ (by rw [hπA]; exact hwz j) (colProj j0).differentiableAt
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have h1 : DifferentiableAt ℂ (fun p : Fin (n + 1) × Fin N → ℂ =>
        ∑ j, p (k.succ, j) * w j (colProj j0 p)) (A z) :=
      DifferentiableAt.fun_sum fun j _ => (differentiableAt_apply _ _).mul (hwp j)
    have := h1.mul ((hwp j0).inv (by rw [hπA]; exact hw0))
    simp only [hS, div_eq_mul_inv]
    exact this
  refine ⟨A z, ⟨hGd.restrictScalars ℝ, ?_⟩, by rw [hGA z hw0, hSz, map_zero, sub_zero]⟩
  obtain ⟨v, hv, hv0⟩ : ∃ v, fderiv ℂ F z v = 0 ∧ v ≠ 0 := by
    have := LinearMap.det_eq_zero_iff_ker_ne_bot.1 hdet
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 this
    exact ⟨v, hv, hv0⟩
  set c : EuclideanSpace ℂ (Fin n) → ℂ := fun y => (∑ j, t (0, j) * w j y) * (w j0 y)⁻¹ with hc
  have hcd : DifferentiableAt ℂ c z := (hsum 0).mul ((hwz j0).inv hw0)
  have hev : G ∘ A =ᶠ[𝓝 z] fun y => t - colInc j0 (c y • F y) := by
    filter_upwards [(hwz j0).continuousAt.eventually_ne hw0, (hsum 0).continuousAt.eventually_ne hs0]
      with y h1 h2
    have : S t y = c y • F y := by
      ext k
      simp only [hS, hc, hF, PiLp.smul_apply, smul_eq_mul]
      field_simp
    rw [← this]
    exact hGA y h1
  have hAd : HasFDerivAt A (colInc j0) z := by
    have := (((colInc j0).hasFDerivAt (x := z - colProj j0 t)).comp z
      ((hasFDerivAt_id z).sub_const (colProj j0 t))).const_add t
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have e1 := hGd.hasFDerivAt.comp z hAd
  have e2 := (((colInc j0).hasFDerivAt).comp z (hcd.hasFDerivAt.smul hFd.hasFDerivAt)).const_sub t
  have e3 := e1.unique (e2.congr_of_eventuallyEq hev)
  have e4 : fderiv ℂ G (A z) (colInc j0 v) = 0 := by
    have := congrArg (fun L => L v) e3
    simpa [hv, hFz] using this
  have e5 : fderiv ℝ G (A z) (colInc j0 v) = 0 := by
    rw [(hGd.hasFDerivAt.restrictScalars ℝ).fderiv]
    exact e4
  refine LinearMap.det_eq_zero_iff_ker_ne_bot.2 ((Submodule.ne_bot_iff _).2 ⟨colInc j0 v, e5, fun h => hv0 ?_⟩)
  rw [← colProj_colInc j0 v, h, map_zero]

theorem ae_simple {n N : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (w : Fin N → EuclideanSpace ℂ (Fin n) → ℂ) (hw : ∀ j, DifferentiableOn ℂ (w j) U) :
    ∀ᵐ t : Fin (n + 1) × Fin N → ℂ, ∀ z ∈ U, ∑ j, t (0, j) * w j z ≠ 0 →
      (∀ k : Fin n, ∑ j, t (k.succ, j) * w j z = 0) →
      (fderiv ℂ (fun y => (WithLp.toLp 2 fun k : Fin n =>
        (∑ j, t (k.succ, j) * w j y) / ∑ j, t (0, j) * w j y : EuclideanSpace ℂ (Fin n))) z).det ≠ 0 := by
  filter_upwards [ae_all_iff.2 (ae_simple_col U hU w hw)] with t ht z hz h0 hk
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
  exact ht j z hz (right_ne_zero_of_mul hj) h0 hk

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_cell {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    ∃ O : Set (Frame X.Ψ r), IsOpen O ∧ (∀ b ∈ Bor X.Ψ r, rmul x0 b ∈ O) ∧
      ∀ y ∈ O, ∃ z ∈ OmF X x0, ∃ b ∈ Bor X.Ψ r, y = rmul (cpt X x0 z) b ∧
      ∀ (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ), IsBEq X L w0 →
        (∀ k, IsBEq X L (s k)) → w0 (cpt X x0 z) ≠ 0 →
        (fderiv ℂ (fun u : V (nd X) => (WithLp.toLp 2 fun k =>
          s k (cpt X x0 u) / w0 (cpt X x0 u) : V (nd X))) z).det ≠ 0 →
        (fderiv ℂ (fun u : V (nd X) => (WithLp.toLp 2 fun k =>
          s k (cpt X y u) / w0 (cpt X y u) : V (nd X))) 0).det ≠ 0 := by
  have hod : x0 ∈ X.dom := IW.orth_mem_dom X _ ho
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X x0 ho
  have hO : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  refine ⟨{x | x ∈ X.dom ∧ Δ x ≠ 0}, hO, fun b hb => ?_, fun y hy => ?_⟩
  · have h0 := huniq 0 (IW.zero_mem_OmF X _ ho) b hb
    rw [IW.cpt_zero] at h0
    exact ⟨OntoS.dom_rmul X hod hb, h0.1⟩
  obtain ⟨h1, h2, h3⟩ := hsplit y hy.1 hy.2
  refine ⟨zOf y, h1, bOf y, h2, h3, fun L w0 s hw0 hs hwx hdet => ?_⟩
  have hcd := OntoB.cd_cpt X y
  set U : Set (V (nd X)) := cpt X y ⁻¹' {x | x ∈ X.dom ∧ Δ x ≠ 0} with hUd
  have hU : IsOpen U := hO.preimage hcd.continuous
  have h0U : (0 : V (nd X)) ∈ U := by
    show cpt X y 0 ∈ {x | x ∈ X.dom ∧ Δ x ≠ 0}
    rwa [IW.cpt_zero]
  set Φ : V (nd X) → V (nd X) := fun u => zOf (cpt X y u) with hΦdef
  have hΦ : DifferentiableOn ℂ Φ U :=
    hz.comp (hcd.differentiable (by simp)).differentiableOn fun _ h => h
  have hΦ0 : Φ 0 = zOf y := by
    show zOf (cpt X y 0) = _
    rw [IW.cpt_zero]
  have hJ : (fderiv ℂ Φ 0).det = bchar (kapW X) (bOf (cpt X y 0)) :=
    KapPf.kappa_statement_holds r X y x0 1 U Φ (fun u => bOf (cpt X y u)) hU hΦ
      (fun u hu => ⟨hu.1, (hsplit _ hu.1 hu.2).2.1, by
        rw [FundSetPf.lact_one]; exact (hsplit _ hu.1 hu.2).2.2⟩) 0 h0U
  have hJ0 : (fderiv ℂ Φ 0).det ≠ 0 := hJ ▸ OntoE.bchar_ne X _ (hsplit _ h0U.1 h0U.2).2.1
  have hΦd : DifferentiableAt ℂ Φ 0 := hΦ.differentiableAt (hU.mem_nhds h0U)
  have hnx : OmF X x0 ∈ 𝓝 (zOf y) := (OntoB.isOpen_OmF X x0).mem_nhds h1
  set F : V (nd X) → V (nd X) := fun u : V (nd X) =>
    (WithLp.toLp 2 fun k => s k (cpt X x0 u) / w0 (cpt X x0 u) : V (nd X)) with hF
  have hFd : DifferentiableAt ℂ F (zOf y) := by
    have hw : DifferentiableAt ℂ (fun u => w0 (cpt X x0 u)) (zOf y) :=
      (OntoB.hol_comp X x0 hw0.1).differentiableAt hnx
    have hsk : ∀ k, DifferentiableAt ℂ (fun u => s k (cpt X x0 u)) (zOf y) := fun k =>
      (OntoB.hol_comp X x0 (hs k).1).differentiableAt hnx
    rw [hF]
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have := (hsk k).mul (hw.inv hwx)
    simp only [div_eq_mul_inv]
    exact this
  have hev : (fun u : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X y u) / w0 (cpt X y u) : V (nd X))) =ᶠ[𝓝 0] F ∘ Φ := by
    filter_upwards [hU.mem_nhds h0U] with u hu
    obtain ⟨g1, g2, g3⟩ := hsplit _ hu.1 hu.2
    have g1' : cpt X x0 (zOf (cpt X y u)) ∈ X.dom := g1
    show _ = F (Φ u)
    rw [hF]
    show (WithLp.toLp 2 _ : V (nd X)) = WithLp.toLp 2 _
    congr 1
    funext k
    have a1 := (hs k).2 _ g1' _ g2
    have a2 := hw0.2 _ g1' _ g2
    rw [← g3] at a1 a2
    rw [a1, a2, mul_div_mul_left _ _ (OntoE.bchar_ne X L g2)]
  rw [hev.fderiv_eq, fderiv_comp 0 (by rwa [hΦ0]) hΦd, hΦ0]
  have : ((fderiv ℂ F (zOf y)).comp (fderiv ℂ Φ 0)).det =
      (fderiv ℂ F (zOf y)).det * (fderiv ℂ Φ 0).det := by
    unfold ContinuousLinearMap.det
    rw [← LinearMap.det_comp]
    rfl
  rw [this]
  exact mul_ne_zero hdet hJ0

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) , ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∀ x ∈ X.dom, sf 0 x ≠ 0 → (∀ k : Fin (nd X), sf k.succ x = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => sf k.succ (cpt X x z) / sf 0 (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
  intro E _ _ _ r X Xa
  have hsec : ∀ j, X.IsSec Xa.L (Xa.w j) := fun j => (Xa.w_van j).1.1.1
  choose O hO hOb hOc using fun x0 : {x0 // IsOrth X x0} => exists_cell X x0.2
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  have hae := (ae_ball_iff hT).2 fun (x0 : {x0 // IsOrth X x0}) (_ : x0 ∈ T) =>
    ae_simple (OmF X x0.1) (OntoB.isOpen_OmF X x0.1) (fun j u => Xa.w j (cpt X x0.1 u))
      fun j => OntoB.hol_comp X x0.1 (hsec j).1
  filter_upwards [hae] with t ht sf x hx h0 hk
  have hsf : ∀ i, IsBEq X Xa.L (sf i) := fun i =>
    ⟨DifferentiableOn.fun_sum fun j _ => (hsec j).1.const_mul _, fun y hy b hb => by
      simp only [sf, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [(hsec j).2.1 y hy b hb]; ring⟩
  have hxU : x ∈ ⋃ i ∈ T, O i := by
    rw [hTU]
    obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
    exact Set.mem_iUnion.2 ⟨⟨x1, h1⟩, hOb _ b hb⟩
  obtain ⟨x0, hx0, hxO⟩ := Set.mem_iUnion₂.1 hxU
  obtain ⟨z, hz, b, hb, hxe, hmain⟩ := hOc x0 x hxO
  have hz' : cpt X x0.1 z ∈ X.dom := hz
  have hval : ∀ i, sf i x = bchar Xa.L b * sf i (cpt X x0.1 z) := fun i => by
    rw [← (hsf i).2 _ hz' b hb, ← hxe]
  have h0' : sf 0 (cpt X x0.1 z) ≠ 0 := right_ne_zero_of_mul (hval 0 ▸ h0)
  have hk' : ∀ k : Fin (nd X), sf k.succ (cpt X x0.1 z) = 0 := fun k =>
    (mul_eq_zero.1 (hval k.succ ▸ hk k)).resolve_left (OntoE.bchar_ne X _ hb)
  exact hmain Xa.L (sf 0) (fun k => sf k.succ) (hsf 0) (fun k => hsf k.succ) h0'
    (ht x0 hx0 z hz h0' hk')

end GlobalTheory.ParamSard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeCoefficientsCommonZerosSimpleStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_coefficients_common_zeros_simple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) , ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∀ x ∈ X.dom, sf 0 x ≠ 0 → (∀ k : Fin (nd X), sf k.succ x = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => sf k.succ (cpt X x z) / sf 0 (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
  first | exact @GlobalTheory.ParamSard.main | exact GlobalTheory.ParamSard.main | (intros; apply GlobalTheory.ParamSard.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeExistsFlatDatumLinearCombination
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GenericFlat

theorem ae_exists_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] [Countable K] (σ : K →+* ℂ), RelIn σ X Xa → ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, ∃ Fl : FlatM X Xa, (∀ x, Fl.w0 x = ∑ j, t (0, j) * Xa.w j x) ∧ ∀ k x, Fl.s k x = ∑ j, t (k.succ, j) * Xa.w j x := by
  intro E _ _ _ r X Xa K _ _ σ hR
  filter_upwards [GlobalTheory.T.ae_transcendental_point_nonvanishing K σ (Fin (nd X + 1) × Fin Xa.N), GlobalTheory.T.ae_coefficients_common_zeros_simple E r X Xa] with t hgen hsimple

  have hdom : ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖∑ j, t (i, j) * Xa.w j x‖ ^ 2 :=
    GlobalTheory.T.theta_forms_bounded_by_generic_combinations E r X Xa K σ t hgen hR
  have hlow : ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom,
      ∑ i : Fin (nd X), ‖∑ j, t (i.succ, j) * Xa.w j x‖ ^ 2 < ε * ‖∑ j, t (0, j) * Xa.w j x‖ ^ 2 →
        c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
    GlobalTheory.T.theta_forms_not_small_where_combinations_vanish E r X Xa K σ t hgen hR
  have hsim : ∀ x ∈ X.dom, ∑ j, t (0, j) * Xa.w j x ≠ 0 →
      (∀ k : Fin (nd X), ∑ j, t (k.succ, j) * Xa.w j x = 0) →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        (∑ j, t (k.succ, j) * Xa.w j (cpt X x z)) / ∑ j, t (0, j) * Xa.w j (cpt X x z) : V (nd X))) 0).det ≠ 0 :=
    hsimple
  obtain ⟨C, hC⟩ := hdom

  have hzero : ∀ x ∈ X.dom, (∀ k : Fin (nd X), ∑ j, t (k.succ, j) * Xa.w j x = 0) →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        (∑ j, t (k.succ, j) * Xa.w j (cpt X x z)) / ∑ j, t (0, j) * Xa.w j (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
    intro x hx hs
    have hs0 : ∑ j, t (0, j) * Xa.w j x ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Xa.w_nz x hx
      have hsum : ∑ i, ‖∑ j, t (i, j) * Xa.w j x‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
        · simp [h0]
        · simp [hs m]
      have hle := hC x hx
      rw [hsum, mul_zero] at hle
      have hk' : ‖Xa.w k x‖ ^ 2 ≤ ∑ k, ‖Xa.w k x‖ ^ 2 :=
        Finset.single_le_sum (f := fun k => ‖Xa.w k x‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
      have h2 : ‖Xa.w k x‖ ^ 2 = 0 := le_antisymm (hk'.trans hle) (by positivity)
      exact hk (by simpa using h2)
    exact hsim x hx hs0 hs
  obtain ⟨Fl, h0, hs⟩ := GlobalTheory.FlatPoints.exists_flat GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames
    GlobalTheory.FlagMahler.mahler_compactness r X Xa (fun i j => t (i, j)) ⟨C, hC⟩ hlow hzero
  exact ⟨Fl, fun x => congrFun h0 x, fun k x => congrFun (congrFun hs k) x⟩

end GlobalTheory.GenericFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeExistsFlatDatumLinearCombinationStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_exists_flat_datum_linearCombination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] [Countable K] (σ : K →+* ℂ), RelIn σ X Xa → ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, ∃ Fl : FlatM X Xa, (∀ x, Fl.w0 x = ∑ j, t (0, j) * Xa.w j x) ∧ ∀ k x, Fl.s k x = ∑ j, t (k.succ, j) * Xa.w j x := by
  first | exact @GlobalTheory.GenericFlat.ae_exists_flat | exact GlobalTheory.GenericFlat.ae_exists_flat | (intros; apply GlobalTheory.GenericFlat.ae_exists_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAlgIndependentCoeffsFlatDatum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
open MeasureTheory

namespace GlobalTheory.GenericFlat

theorem ae_cast {a b n m : ℕ} (hab : a = b) (hnm : n = m) (P : (Fin (a + 1) × Fin n → ℂ) → Prop)
    (hP : ∀ᵐ t : Fin (a + 1) × Fin n → ℂ, P t) :
    ∀ᵐ t : Fin (b + 1) × Fin m → ℂ,
      P fun p => t (Fin.cast (congrArg (· + 1) hab) p.1, Fin.cast hnm p.2) := by
  subst hab hnm
  simpa using hP

theorem exists_generic_flatAt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1), ∃ t : Idx D j N → ℂ, (∀ Q : MvPolynomial (Idx D j N) T.Q.c.F, Q ≠ 0 → MvPolynomial.eval₂ T.σ₀ t Q ≠ 0) ∧ Nonempty (FlatAt h j A t) := by
  intro D T h j _hj N wL wF w Tn c1 A
  have hC : Countable T.Q.c.F := (Module.finBasis ℚ T.Q.c.F).equivFun.injective.countable

  have hk : ∀ k : (T.U j T.σ₀).Comp, ∀ᵐ t : Fin (WeightFamilies.dimY D j + 1) × Fin N → ℂ,
      ∃ Fl : FlatM ((T.U j T.σ₀).X k) (A.Xa k),
        (∀ x, Fl.w0 x = ∑ i, t (0, i) * rdR h j (w i) k x) ∧
        ∀ a x, Fl.s a x = ∑ i, t ((Fin.cast (A.dim k) a).succ, i) * rdR h j (w i) k x := by
    intro k
    have H := GlobalTheory.T.ae_exists_flat_datum_linearCombination _ _ ((T.U j T.σ₀).X k) (A.Xa k) T.Q.c.F T.σ₀ (A.rel k)
    refine (ae_cast (A.dim k) (A.hN k) _ H).mono ?_
    rintro t ⟨Fl, h0, hs⟩
    refine ⟨Fl, fun x => ?_, fun a x => ?_⟩
    · rw [h0]
      refine Fintype.sum_equiv (finCongr (A.hN k)) _ _ fun i => ?_
      simp only [A.hw k i, finCongr_apply]
      congr 2
    · rw [hs]
      refine Fintype.sum_equiv (finCongr (A.hN k)) _ _ fun i => ?_
      simp only [A.hw k i, finCongr_apply]
      congr 2

  have hall := (ae_all_iff.2 hk).and
    (GlobalTheory.ae_eval₂_ne_zero_of_countable T.Q.c.F T.σ₀ (Fin (WeightFamilies.dimY D j + 1) × Fin N))
  obtain ⟨t, ht, hg⟩ := hall.exists
  choose Fl h0 hs using ht
  exact ⟨t, hg, ⟨⟨Fl, h0, hs⟩⟩⟩

end GlobalTheory.GenericFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAlgIndependentCoeffsFlatDatumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algIndependent_coeffs_flatDatum : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1), ∃ t : Idx D j N → ℂ, (∀ Q : MvPolynomial (Idx D j N) T.Q.c.F, Q ≠ 0 → MvPolynomial.eval₂ T.σ₀ t Q ≠ 0) ∧ Nonempty (FlatAt h j A t) := by
  first | exact @GlobalTheory.GenericFlat.exists_generic_flatAt | exact GlobalTheory.GenericFlat.exists_generic_flatAt | (intros; apply GlobalTheory.GenericFlat.exists_generic_flatAt <;> assumption)
end
