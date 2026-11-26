module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GradientAtPoint

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalRiemannExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def NormalRiemannExtension.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (U : Set (σ → ℂ))
    (f : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → IsOpen U →
    HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0})) →
    ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ U) ∧
      Set.EqOn g f ((zeroSetIn I ∩ U) \ {z | eval z h = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalGermIntegrallyClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalGermIntegrallyClosed.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (F G : (σ → ℂ) → ℂ) (d : ℕ) (a : Fin d → (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ F N → DifferentiableOn ℂ G N → (∀ j, DifferentiableOn ℂ (a j) N) →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    (∀ z ∈ (zeroSetIn I ∩ N) \ {z | G z = 0},
      F z ^ d + ∑ j, a j z * F z ^ (j : ℕ) * G z ^ (d - (j : ℕ)) = 0) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ ∃ H : (σ → ℂ) → ℂ, DifferentiableOn ℂ H V ∧
      ∀ z ∈ zeroSetIn I ∩ V, F z = G z * H z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveElementFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def PrimitiveElementFibres.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ (c : Fin n → ℂ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Δ : MvPolynomial (Fin d) ℂ)
        (Q : Fin n → Polynomial (MvPolynomial (Fin d) ℂ)),
        m.Monic ∧ m.natDegree = projDegree J A ∧ Δ ≠ 0 ∧
          ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
            (m.map (eval y)).Separable ∧
            (∀ x ∈ fibre J A y, (m.map (eval y)).IsRoot (∑ j, c j * x j) ∧
              ∀ j, eval y Δ * x j = ((Q j).map (eval y)).eval (∑ j, c j * x j)) ∧
            ∀ τ : ℂ, (m.map (eval y)).IsRoot τ → ∃ x ∈ fibre J A y, ∑ j, c j * x j = τ

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalBranchedCovering
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def LocalBranchedCovering.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ)),
    I.IsPrime → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    ∃ (k : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (W : Set (σ → ℂ)) (D : Set (Fin k → ℂ)) (m : ℕ)
      (δ : (Fin k → ℂ) → ℂ),
      IsOpen W ∧ w ∈ W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ IsOpen D ∧ A w ∈ D ∧
      (∀ z ∈ zeroSetIn I ∩ W, A z = A w → z = w) ∧
      (∀ z ∈ zeroSetIn I ∩ closure W, A z ∈ D → z ∈ W) ∧
      DifferentiableOn ℂ δ D ∧
      (∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, δ t ≠ 0) ∧
      (∀ y ∈ D, δ y ≠ 0 → ∃ (O : Set (Fin k → ℂ)) (s : Fin m → (Fin k → ℂ) → σ → ℂ),
        IsOpen O ∧ y ∈ O ∧ (∀ j, DifferentiableOn ℂ (s j) O) ∧
        ∀ y' ∈ O, (∀ j, s j y' ∈ zeroSetIn I ∩ W ∧ A (s j y') = y') ∧
          Function.Injective (fun j => s j y') ∧
          ∀ z ∈ zeroSetIn I ∩ W, A z = y' → z ∈ Set.range (fun j => s j y')) ∧
      ∀ z ∈ zeroSetIn I ∩ W, ∀ ε > 0, A '' (zeroSetIn I ∩ Metric.ball z ε) ∈ 𝓝 (A z)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPowerSumsEsymmAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Finset

theorem multiset_mul_esymm_eq_sum (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map fun x => x ^ a.2).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun x : s => (x : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum s ℂ k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe, MvPolynomial.psum,
    MvPolynomial.aeval_X] at h
  convert h using 4 with a _
  rw [Finset.sum_eq_multiset_sum]
  conv_lhs => rw [← Multiset.map_univ_coe s]
  rw [Multiset.map_map]
  rfl

theorem PowerSumsEsymmAnalytic.proof : PowerSumsEsymmAnalytic.Statement := by
  intro σ _ V d Z hV hcard hp k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa [Multiset.esymm, Multiset.powersetCard_zero_left] using
      (analyticOnNhd_const (𝕜 := ℂ) (v := (1 : ℂ)) (s := V))
  by_cases hkd : d < k
  · refine (analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ))).congr hV fun z hz => ?_
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard z hz]; exact hkd)]
  push Not at hkd
  have hsum : AnalyticOnNhd ℂ (fun z => ((k : ℂ))⁻¹ * ((-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (Z z).esymm a.1 * ((Z z).map fun x => x ^ a.2).sum)) V := by
    refine analyticOnNhd_const.mul (analyticOnNhd_const.mul ?_)
    refine Finset.analyticOnNhd_fun_sum _ fun a ha => ?_
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    refine (analyticOnNhd_const.mul (ih a.1 ha.2)).mul (hp a.2 (by omega) (by omega))
  refine hsum.congr hV fun z _ => ?_
  rw [← multiset_mul_esymm_eq_sum, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), one_mul]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalizationAtPrimeQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem LocalizationAtPrimeQuotient.proof : LocalizationAtPrimeQuotient.Statement.{u} := by
  intro A _ I T P _ W _ hP
  let Q := A ⧸ I
  let B := Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))

  have hsub : (P.comap (algebraMap Q (Localization T))).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    have hmem : ∀ r : A, Ideal.Quotient.mk I r ∈ P.comap (algebraMap Q (Localization T)) ↔ r ∈ W := by
      intro r; rw [← hP]; exact Iff.rfl
    have hIW : I ≤ W := fun r hr => by
      rw [← hmem, Ideal.Quotient.eq_zero_iff_mem.2 hr]; exact Ideal.zero_mem _
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : Ideal.Quotient.mk I r ∈ (P.comap (algebraMap Q (Localization T))).primeCompl ↔ r ∉ W :=
      not_congr (hmem r)
    rw [h1]
    constructor
    · intro hr; exact ⟨r, hr, rfl⟩
    · rintro ⟨r', hr', he⟩ hr
      apply hr'
      have : r' - r ∈ I := Ideal.Quotient.eq.1 he
      simpa using W.add_mem (hIW this) hr
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl) (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T
      (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) B
  refine ⟨e.toRingEquiv, fun a => ?_⟩
  have h2 : algebraMap (Localization T) (Localization.AtPrime P)
      (algebraMap Q (Localization T) (Ideal.Quotient.mk I a)) =
      algebraMap Q (Localization.AtPrime P) (Ideal.Quotient.mk I a) :=
    (IsScalarTower.algebraMap_apply Q (Localization T) (Localization.AtPrime P) _).symm
  rw [h2]
  exact e.commutes (Ideal.Quotient.mk I a)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraphPartition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal
open Set Metric

noncomputable section

theorem AreaGraphPartition.proof : AreaGraphPartition.Statement := by
  intro k m U F hU hF r hr

  have hcont : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ F x := fun x hx =>
    (hF.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)

  have hball : ∀ x : U, ∃ ε > 0, ball (x : EuclideanSpace ℝ (Fin k)) ε ⊆ U ∧
      ∀ y ∈ ball (x : EuclideanSpace ℝ (Fin k)) ε, ‖fderiv ℝ F y - fderiv ℝ F x‖ ≤ r (fderiv ℝ F x) := by
    intro x
    have hpos : (0 : ℝ) < r (fderiv ℝ F x) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hr _))
    have hca : ContinuousAt (fderiv ℝ F) x := hcont.continuousAt (hU.mem_nhds x.2)
    obtain ⟨δ, δpos, hδ⟩ := Metric.continuousAt_iff.1 hca _ hpos
    obtain ⟨η, ηpos, hη⟩ := Metric.isOpen_iff.1 hU x x.2
    refine ⟨min δ η, lt_min δpos ηpos, (ball_subset_ball (min_le_right _ _)).trans hη, ?_⟩
    intro y hy
    have := hδ (lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _))
    rw [dist_eq_norm] at this
    exact this.le
  choose ε εpos hεU hεD using hball

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => ball (x : EuclideanSpace ℝ (Fin k)) (ε x)) (fun _ => isOpen_ball)
  have hcover : (⋃ x : U, ball (x : EuclideanSpace ℝ (Fin k)) (ε x)) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun x => hεU x
    · intro x hx
      exact mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (εpos _)⟩
  rcases U.eq_empty_or_nonempty with hUe | hUne
  ·
    refine ⟨fun _ => ∅, fun _ => 0, fun _ _ _ => disjoint_empty _, fun _ => MeasurableSet.empty,
      fun _ => empty_subset _, by simp [hUe], fun _ => fun x hx => absurd hx (notMem_empty x),
      fun _ x hx => absurd hx (notMem_empty x)⟩
  have hTne : T.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hUne
    have : x ∈ ⋃ i ∈ T, ball ((i : U) : EuclideanSpace ℝ (Fin k)) (ε i) := by rw [hTU, hcover]; exact hx
    simp [h] at this
  obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
  set B : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => ball ((c n : U) : EuclideanSpace ℝ (Fin k)) (ε (c n)) with hB
  have hBU : ⋃ n, B n = U := by
    rw [← hcover, ← hTU, hc, biUnion_range]
  refine ⟨disjointed B, fun n => fderiv ℝ F (c n), disjoint_disjointed B,
    MeasurableSet.disjointed (fun n => measurableSet_ball), fun n => (disjointed_subset B n).trans
    (hεU (c n)), by rw [iUnion_disjointed, hBU], ?_, ?_⟩
  · intro n x hx y hy
    have hx' := disjointed_subset B n hx
    have hy' := disjointed_subset B n hy
    exact (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le'
      (fun z hz => hdiff z (hεU (c n) hz)) (fun z hz => hεD (c n) z hz) hy' hx'
  · intro n x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hεD (c n) x (disjointed_subset B n hx)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGraphJacContinuous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open scoped InnerProductSpace

theorem det_one_add_adjoint_comp_self_pos {k m : ℕ}
    (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < LinearMap.det ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
      LinearMap.adjoint B ∘ₗ B) := by
  set S : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) := 1 + LinearMap.adjoint B ∘ₗ B
    with hSdef
  have hBB : (LinearMap.adjoint B ∘ₗ B).IsPositive := LinearMap.isPositive_adjoint_comp_self B
  have hS : S.IsPositive := LinearMap.isPositive_one.add hBB
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  rw [hS.isSymmetric.det_eq_prod_eigenvalues hn]
  refine Finset.prod_pos fun i _ => ?_
  set v := hS.isSymmetric.eigenvectorBasis hn i
  have hv : ‖v‖ = 1 := (hS.isSymmetric.eigenvectorBasis hn).orthonormal.1 i
  have h1 : ⟪S v, v⟫_ℝ = hS.isSymmetric.eigenvalues hn i := by
    rw [hS.isSymmetric.apply_eigenvectorBasis hn i]
    simp [real_inner_smul_left, hv, v]
  have h2 : ⟪S v, v⟫_ℝ = ‖v‖ ^ 2 + ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ := by
    rw [hSdef, LinearMap.add_apply, inner_add_left, Module.End.one_apply, real_inner_self_eq_norm_sq]
  have h3 : 0 ≤ ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ := by
    simpa using hBB.re_inner_nonneg_left v
  have : 0 < (hS.isSymmetric.eigenvalues hn i : ℝ) := by
    rw [← h1, h2, hv]; linarith
  simpa using this

theorem graphJac_pos {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < graphJac B :=
  Real.sqrt_pos.mpr (det_one_add_adjoint_comp_self_pos B)

theorem continuous_graphJac (k m : ℕ) :
    Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  have hc : Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      (1 + (ContinuousLinearMap.adjoint B).comp B :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
    continuous_const.add ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)
  have heq : (fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) =
      fun B => √((1 + (ContinuousLinearMap.adjoint B).comp B :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)).det) := by
    funext B
    rfl
  rw [heq]
  exact (ContinuousLinearMap.continuous_det.comp hc).sqrt

theorem GraphJacContinuous.proof : GraphJacContinuous.Statement := by
  intro k m A ε hε
  set g := fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
    graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) with hg
  have hgA : 0 < g A := graphJac_pos _
  set η := ε * g A / (1 + ε) with hη
  have hη0 : 0 < η := by positivity
  have hηe : (1 + ε) * η = ε * g A := by rw [hη]; field_simp
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuous_iff.mp (continuous_graphJac k m) A η hη0
  refine ⟨δ / 2, half_pos hδ, fun B hB => ?_⟩
  have hd : dist B A < δ := by rw [dist_eq_norm]; linarith
  have h := hδη B hd
  rw [Real.dist_eq, abs_lt] at h
  change g B ≤ (1 + ε) * g A ∧ g A ≤ (1 + ε) * g B
  constructor
  · nlinarith
  · nlinarith

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCircleArgumentPrinciple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

theorem CircleArgumentPrinciple.differentiable_prod_sub (Z : Multiset ℂ) :
    Differentiable ℂ fun s : ℂ => (Z.map fun a => s - a).prod := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (differentiable_id.sub_const a).mul ih

theorem CircleArgumentPrinciple.integral_prod_mul {O : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hO : IsOpen O)
    (hball : closedBall c r ⊆ O) {u φ : ℂ → ℂ} (hu : DifferentiableOn ℂ u O)
    (hu0 : ∀ s ∈ closedBall c r, u s ≠ 0) (hφ : DifferentiableOn ℂ φ O) (Z : Multiset ℂ)
    (hZ : ∀ a ∈ Z, a ∈ ball c r) :
    (2 * π * I)⁻¹ * (∮ s in C(c, r), φ s * deriv (fun s => (Z.map fun a => s - a).prod * u s) s /
      ((Z.map fun a => s - a).prod * u s)) = (Z.map φ).sum := by
  induction Z using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, one_mul, Multiset.sum_zero]
    have hd : ∀ z ∈ closedBall c r, DifferentiableAt ℂ (fun s => φ s * deriv u s / u s) z := by
      intro z hz
      have hzO : O ∈ 𝓝 z := hO.mem_nhds (hball hz)
      exact ((hφ.differentiableAt hzO).mul ((hu.deriv hO).differentiableAt hzO)).div
        (hu.differentiableAt hzO) (hu0 z hz)
    rw [circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz => hd z (ball_subset_closedBall hz.1)), mul_zero]
  | cons a Z ih =>
    have hZ' : ∀ b ∈ Z, b ∈ ball c r := fun b hb => hZ b (Multiset.mem_cons_of_mem hb)
    have ha : a ∈ ball c r := hZ a (Multiset.mem_cons_self a Z)
    set F : ℂ → ℂ := fun s => (Z.map fun b => s - b).prod * u s with hFdef
    have hF : DifferentiableOn ℂ F O :=
      ((CircleArgumentPrinciple.differentiable_prod_sub Z).differentiableOn).mul hu

    have hne : ∀ s ∈ sphere c r, ∀ b ∈ a ::ₘ Z, s - b ≠ 0 := by
      intro s hs b hb h0
      have hb' := hZ b hb
      obtain rfl := sub_eq_zero.1 h0
      rw [mem_ball] at hb'
      rw [mem_sphere] at hs
      linarith
    have hFne : ∀ s ∈ sphere c r, F s ≠ 0 := by
      intro s hs
      refine mul_ne_zero (Multiset.prod_ne_zero ?_) (hu0 s (sphere_subset_closedBall hs))
      simp only [Multiset.mem_map, not_exists, not_and]
      exact fun b hb h0 => hne s hs b (Multiset.mem_cons_of_mem hb) h0
    have hsplit : Set.EqOn
        (fun s => φ s * deriv (fun s => ((a ::ₘ Z).map fun b => s - b).prod * u s) s /
          (((a ::ₘ Z).map fun b => s - b).prod * u s))
        (fun s => (s - a)⁻¹ • φ s + φ s * deriv F s / F s) (sphere c r) := by
      intro s hs
      have hsO : O ∈ 𝓝 s := hO.mem_nhds (hball (sphere_subset_closedBall hs))
      have hfun : (fun s => ((a ::ₘ Z).map fun b => s - b).prod * u s) = fun s => (s - a) * F s := by
        funext w
        simp only [Multiset.map_cons, Multiset.prod_cons, hFdef, mul_assoc]
      have hval : ((a ::ₘ Z).map fun b => s - b).prod * u s = (s - a) * F s := by
        simp only [Multiset.map_cons, Multiset.prod_cons, hFdef, mul_assoc]
      have hder : deriv (fun s => (s - a) * F s) s = 1 * F s + (s - a) * deriv F s :=
        (((hasDerivAt_id' s).sub_const a).mul (hF.differentiableAt hsO).hasDerivAt).deriv
      have hsa : s - a ≠ 0 := hne s hs a (Multiset.mem_cons_self a Z)
      have hFs := hFne s hs
      show φ s * deriv (fun s => ((a ::ₘ Z).map fun b => s - b).prod * u s) s /
          (((a ::ₘ Z).map fun b => s - b).prod * u s) = (s - a)⁻¹ • φ s + φ s * deriv F s / F s
      rw [hfun, hder, hval, smul_eq_mul]
      field_simp
    have hint1 : CircleIntegrable (fun s => (s - a)⁻¹ • φ s) c r := by
      refine ContinuousOn.circleIntegrable hr.le ?_
      simp only [smul_eq_mul]
      refine ContinuousOn.mul ?_ (hφ.continuousOn.mono (sphere_subset_closedBall.trans hball))
      exact (continuousOn_id.sub continuousOn_const).inv₀
        (fun s hs => hne s hs a (Multiset.mem_cons_self a Z))
    have hint2 : CircleIntegrable (fun s => φ s * deriv F s / F s) c r := by
      refine ContinuousOn.circleIntegrable hr.le ?_
      intro s hs
      have hsO : O ∈ 𝓝 s := hO.mem_nhds (hball (sphere_subset_closedBall hs))
      exact (((hφ.differentiableAt hsO).mul ((hF.deriv hO).differentiableAt hsO)).div
        (hF.differentiableAt hsO) (hFne s hs)).continuousAt.continuousWithinAt
    have hcauchy : (2 * π * I : ℂ)⁻¹ • (∮ s in C(c, r), (s - a)⁻¹ • φ s) = φ a :=
      two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        Set.countable_empty ha (hφ.continuousOn.mono hball)
        (fun z hz => hφ.differentiableAt (hO.mem_nhds (hball (ball_subset_closedBall hz.1))))
    rw [circleIntegral.integral_congr hr.le hsplit, circleIntegral.integral_add hint1 hint2, mul_add,
      ← smul_eq_mul, hcauchy, ih hZ', Multiset.map_cons, Multiset.sum_cons]

theorem CircleArgumentPrinciple.factorisation {h : ℂ → ℂ} {O : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hO : IsOpen O) (hball : closedBall c r ⊆ O) (hh : DifferentiableOn ℂ h O)
    (hsph : ∀ s ∈ sphere c r, h s ≠ 0) :
    ∃ (Z : Multiset ℂ) (u : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ ball c r) ∧ DifferentiableOn ℂ u O ∧ (∀ s ∈ closedBall c r, u s ≠ 0) ∧
      (∀ s ∈ O, h s = (Z.map fun a => s - a).prod * u s) := by
  have han : AnalyticOnNhd ℂ h O := hh.analyticOnNhd hO

  have hord : ∀ z ∈ closedBall c r, analyticOrderAt h z ≠ ⊤ := by
    intro z hz htop
    have h0 := (han.mono hball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall c r).isPreconnected hz (analyticOrderAt_eq_top.1 htop)
    have hs : c + (r : ℂ) ∈ sphere c r := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact hsph _ hs (h0 (sphere_subset_closedBall hs))

  set S0 : Set ℂ := {z | z ∈ closedBall c r ∧ h z = 0} with hS0def
  have hS0fin : S0.Finite := by
    apply IsCompact.finite
    · refine (isCompact_closedBall c r).of_isClosed_subset ?_ (fun z hz => hz.1)
      exact (hh.continuousOn.mono hball).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
    · rw [isDiscrete_iff_nhdsNE]
      intro z hz
      rcases (han z (hball hz.1)).eventually_eq_zero_or_eventually_ne_zero with h1 | h1
      · exact absurd (analyticOrderAt_eq_top.2 h1) (hord z hz.1)
      · rw [Filter.inf_principal_eq_bot]
        filter_upwards [h1] with w hw hwS
        exact hw hwS.2
  set S : Finset ℂ := hS0fin.toFinset with hSdef
  have hmemS : ∀ a, a ∈ S ↔ a ∈ closedBall c r ∧ h a = 0 := fun a => hS0fin.mem_toFinset
  set m : ℂ → ℕ := fun a => analyticOrderNatAt h a with hmdef
  have hmcast : ∀ a ∈ S, analyticOrderAt h a = (m a : ℕ∞) := fun a ha =>
    (Nat.cast_analyticOrderNatAt (hord a ((hmemS a).1 ha).1)).symm
  have hmpos : ∀ a ∈ S, m a ≠ 0 := by
    intro a ha h0
    have h1 := hmcast a ha
    rw [h0, Nat.cast_zero, analyticOrderAt_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact h1 (han a (hball ((hmemS a).1 ha).1))
    · exact h1 ((hmemS a).1 ha).2
  set P : ℂ → ℂ := fun s => ∏ a ∈ S, (s - a) ^ m a with hPdef
  set Z : Multiset ℂ := ∑ a ∈ S, Multiset.replicate (m a) a with hZdef
  have hPZ : ∀ s, (Z.map fun a => s - a).prod = P s := by
    intro s
    simp only [hZdef, hPdef]
    induction S using Finset.induction_on with
    | empty => simp
    | insert b T hb ih =>
      rw [Finset.sum_insert hb, Finset.prod_insert hb, Multiset.map_add (f := _), Multiset.prod_add, ih,
        Multiset.map_replicate, Multiset.prod_replicate]
  have hPdiff : Differentiable ℂ P := by
    simp only [hPdef]
    fun_prop
  have hP0 : ∀ s, P s = 0 ↔ s ∈ S := by
    intro s
    simp only [hPdef, Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨a, ha, h0⟩
      rw [sub_eq_zero.1 ((pow_eq_zero_iff (hmpos a ha)).1 h0)]
      exact ha
    · intro hs
      exact ⟨s, hs, by rw [sub_self]; exact zero_pow (hmpos s hs)⟩

  have hloc : ∀ a ∈ S, ∃ G : ℂ → ℂ, AnalyticAt ℂ G a ∧ G a ≠ 0 ∧
      ∀ᶠ w in 𝓝[≠] a, P w ≠ 0 ∧ h w / P w = G w := by
    intro a ha
    obtain ⟨g, hg, hga, hev⟩ :=
      (han a (hball ((hmemS a).1 ha).1)).analyticOrderAt_eq_natCast.1 (hmcast a ha)
    set Q : ℂ → ℂ := fun w => ∏ b ∈ S.erase a, (w - b) ^ m b with hQdef
    have hPQ : ∀ w, P w = (w - a) ^ m a * Q w := fun w =>
      (Finset.mul_prod_erase S (fun b => (w - b) ^ m b) ha).symm
    have hQa : Q a ≠ 0 := by
      simp only [hQdef]
      rw [Finset.prod_ne_zero_iff]
      intro b hb
      exact pow_ne_zero _ (sub_ne_zero.2 (Finset.ne_of_mem_erase hb).symm)
    have hQan : AnalyticAt ℂ Q a := by
      simp only [hQdef]
      fun_prop
    refine ⟨fun w => g w / Q w, hg.div hQan hQa, div_ne_zero hga hQa, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds (hQan.continuousAt.eventually_ne hQa),
      self_mem_nhdsWithin] with w hw hQw hwa
    have hpow : (w - a) ^ m a ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hwa)
    refine ⟨by rw [hPQ]; exact mul_ne_zero hpow hQw, ?_⟩
    rw [hw, hPQ, smul_eq_mul, mul_div_mul_left _ _ hpow]
  set u : ℂ → ℂ := fun s => if P s = 0 then limUnder (𝓝[≠] s) (fun w => h w / P w) else h s / P s
    with hudef
  have hu_near : ∀ a ∈ S, ∃ G : ℂ → ℂ, AnalyticAt ℂ G a ∧ G a ≠ 0 ∧ u =ᶠ[𝓝 a] G := by
    intro a ha
    obtain ⟨G, hG, hGa, hev⟩ := hloc a ha
    refine ⟨G, hG, hGa, ?_⟩
    have hlim : limUnder (𝓝[≠] a) (fun w => h w / P w) = G a :=
      Tendsto.limUnder_eq ((hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
        (hev.mono fun w hw => hw.2.symm))
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with w hw
    by_cases hwa : w = a
    · subst hwa
      simp only [hudef, (hP0 w).2 ha, if_true, hlim]
    · obtain ⟨hPw, hq⟩ := hw hwa
      simp only [hudef, hPw, if_false, hq]
  have hu_off : ∀ s, P s ≠ 0 → u =ᶠ[𝓝 s] fun w => h w / P w := by
    intro s hs
    filter_upwards [(hPdiff s).continuousAt.eventually_ne hs] with w hw
    simp only [hudef, hw, if_false]
  refine ⟨Z, u, ?_, ?_, ?_, ?_⟩
  ·
    intro a haZ
    obtain ⟨b, hb, hab⟩ := Multiset.mem_sum.1 haZ
    rw [Multiset.eq_of_mem_replicate hab]
    obtain ⟨hbc, hb0⟩ := (hmemS b).1 hb
    rw [mem_ball]
    refine lt_of_le_of_ne (mem_closedBall.1 hbc) fun hbr => hsph b ?_ hb0
    exact mem_sphere.2 hbr
  ·
    intro s hs
    by_cases hPs : P s = 0
    · obtain ⟨G, hG, -, hEq⟩ := hu_near s ((hP0 s).1 hPs)
      exact (hG.differentiableAt.congr_of_eventuallyEq hEq).differentiableWithinAt
    · exact (((hh.differentiableAt (hO.mem_nhds hs)).div (hPdiff s) hPs).congr_of_eventuallyEq
        (hu_off s hPs)).differentiableWithinAt
  ·
    intro s hs
    by_cases hPs : P s = 0
    · obtain ⟨G, -, hGs, hEq⟩ := hu_near s ((hP0 s).1 hPs)
      rw [hEq.eq_of_nhds]
      exact hGs
    · have hhs : h s ≠ 0 := fun h0 => hPs ((hP0 s).2 ((hmemS s).2 ⟨hs, h0⟩))
      simp only [hudef, hPs, if_false]
      exact div_ne_zero hhs hPs
  ·
    intro s hs
    rw [hPZ]
    by_cases hPs : P s = 0
    · rw [hPs, zero_mul]
      exact ((hmemS s).1 ((hP0 s).1 hPs)).2
    · simp only [hudef, hPs, if_false]
      field_simp

theorem CircleArgumentPrinciple.proof : CircleArgumentPrinciple.Statement := by
  intro h O c r hr hO hball hh hsph
  obtain ⟨Z, u, hZ, hu, hu0, hfac⟩ := CircleArgumentPrinciple.factorisation hr hO hball hh hsph
  refine ⟨Z, u, hZ, hu, hu0, hfac, fun φ hφ => ?_⟩
  rw [← CircleArgumentPrinciple.integral_prod_mul hr hO hball hu hu0 hφ Z hZ]
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro s hs
  have hsO : s ∈ O := hball (sphere_subset_closedBall hs)
  have heq : h =ᶠ[𝓝 s] fun w => (Z.map fun a => w - a).prod * u w :=
    Filter.eventually_of_mem (hO.mem_nhds hsO) hfac
  simp only [heq.deriv_eq, hfac s hsO]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicJacobianNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InjectiveHolomorphicJacobianNeZero.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U →
      ∀ x ∈ U, LinearMap.det (fderiv ℂ f x : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalGermIrreducible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalGermIrreducible.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I →
      GermIrreducibleAt (zeroSetIn I) w

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalComplementConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I →
    ∀ U ∈ 𝓝 w, ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧
      IsPreconnected ((zeroSetIn I ∩ B) \ {z | eval z h = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IrreducibleGermComplementConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (h : (σ → ℂ) → ℂ),
    IsAnalyticNear X w → GermIrreducibleAt X w → AnalyticAt ℂ h w →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ X → h z = 0) →
    ∀ U ∈ 𝓝 w, ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧ IsPreconnected ((X ∩ B) \ {z | h z = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

def IrreducibleGermCurve.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ),
    IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) X

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalMaximumPrinciple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalMaximumPrinciple.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ))
    (g : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset g (zeroSetIn I ∩ U) → (∀ z ∈ zeroSetIn I ∩ U, ‖g z‖ ≤ ‖g w‖) →
    ∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → g z = g w

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermMeetOverHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IrreducibleGermMeetOverHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y Z : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W ∈ 𝓝 w, ∀ x ∈ Y ∩ W, A x = A w → x = w) →
    IsAnalyticNear Z w → (¬ ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z) →
    ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
      ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z → e (A z) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusIdentity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def RegularLocusIdentity.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)), I.IsPrime →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧ ∀ z ∈ zeroSetIn I, eval z h ≠ 0 → ∀ W ∈ 𝓝 z,
      ∃ V : Set (σ → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
        ∀ F : (σ → ℂ) → ℂ, AnalyticOnNhd ℂ F V →
          (∃ y ∈ zeroSetIn I ∩ V, ∀ᶠ u in 𝓝 y, u ∈ zeroSetIn I → F u = 0) →
            ∀ u ∈ zeroSetIn I ∩ V, F u = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalZerosNowhereDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalZerosNowhereDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (G : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ G N → ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    ∃ U : Set (σ → ℂ), IsOpen U ∧ w ∈ U ∧ U ⊆ N ∧
      ∀ z ∈ zeroSetIn I ∩ U, ∀ V ∈ 𝓝 z, ∃ x ∈ zeroSetIn I ∩ V, G x ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionProperBall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteProjectionProperBall.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ U ∈ 𝓝 w, ∃ ρ : ℝ, 0 < ρ ∧ ∃ r : ℝ, 0 < r ∧ Metric.ball w ρ ⊆ U ∧
      ∀ K ⊆ Metric.ball (A w) r, IsCompact K →
        IsCompact {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionOpenNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermProjectionOpenNear.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N₀ ∈ 𝓝 w, ∀ x ∈ X ∩ N₀, ∀ V ∈ 𝓝 x, A '' (X ∩ V) ∈ 𝓝 (A x)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreCentredEquation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def FiniteFibreCentredEquation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ T : ℂ, T ^ n + ∑ j, b j (A w) * T ^ (j : ℕ) = (T - g w) ^ n) ∧
        ∀ᶠ z in 𝓝 w, z ∈ X → g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatLocalRegularElement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def FlatLocalRegularElement.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M],
      Module.Finite B M → Module.Flat A M →
      ∀ y ∈ maximalIdeal B,
        IsSMulRegular (M ⧸ ((maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))) y →
        IsSMulRegular M y ∧ Module.Flat A (QuotSMulTop y M)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatLocalRegularSequence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

def FlatLocalRegularSequence.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) → Module.Flat A B →
      ∀ (rs : List A) (ys : List B), (∀ r ∈ rs, r ∈ maximalIdeal A) → IsWeaklyRegular A rs →
        (∀ y ∈ ys, y ∈ maximalIdeal B) →
        IsWeaklyRegular (B ⧸ (maximalIdeal A).map (algebraMap A B))
          (ys.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))) →
        IsWeaklyRegular B (rs.map (algebraMap A B) ++ ys)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
