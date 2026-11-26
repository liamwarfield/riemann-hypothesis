module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSemiPosMassFinite
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralDensityIndependentProjection
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableChartAbsDensity

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ZeroSetChartIdealEqChartSet
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ZeroSetChartIdealEqChartSet
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

theorem zeroSet_chartIdeal_conePts : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal Q →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i := by
  intro K _ _ ι _ Q m σ i hQ
  exact segChart_zeroSet (isMultiHomogIdeal_toR hQ) σ i

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ZeroSetChartIdealEqChartSetStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeroSet_chartIdeal_eq_chartSet : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal Q →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothMetricsNonnegDensity
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothMetricsNonnegDensity
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxTwist

theorem isSheet_bot_of_isSetSheet {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {S : Set ((Σ k, ι k) → ℂ)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hS : ∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (hγ : IsSetSheet S Ψ y w γ) : IsSheet ⊥ Ψ y w γ := by
  refine ⟨hγ.1, hγ.2.mono fun y' hy' => ⟨hy'.1, ⟨hS _ hy'.2.1, fun f hf => ?_⟩, hy'.2.2⟩⟩
  rw [Ideal.mem_bot.1 hf]
  simp

theorem exists_dominating_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
    ∃ N : Fin e → HermLine ι, (∀ j, IsSmoothHerm (N j)) ∧
      ∀ (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
        (∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) →
        (∀ (g : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z, 0 ≤ g z) → 0 ≤ setSheetDensity S Ψ (pot N) g y w) ∧
        ∀ (g g' : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z ∈ S, |g z| ≤ g' z) →
          |setSheetDensity S Ψ (pot L) g y w| ≤ 3 ^ e * setSheetDensity S Ψ (pot N) g' y w := by
  intro K _ ι _ e L hL
  classical
  choose T hTs hTp hLTp using fun j =>
    GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.proof GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.proof K ι (L j) (hL j)
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j => isSmoothHerm_tensor (hL j) (hTs j)
  refine ⟨fun j => ((L j).tensor (T j)).tensor (T j), fun j => isSmoothHerm_tensor (hLT j) (hTs j), ?_⟩
  intro S Ψ hS
  have hab : ∀ {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ},
      IsSetSheet S Ψ y w γ → |maDensity (fun j y' => pot L j (γ y')) y| ≤
        3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y :=
    fun hγ => GroundTheory.Heights₂.Heights.Inter.PointsAbsIntegrable.abs_maDensity_le hL hTs hTp hLTp
      (isSheet_bot_of_isSetSheet hS hγ)
  have hnn : ∀ {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ},
      IsSetSheet S Ψ y w γ →
        0 ≤ maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y :=
    fun hγ => nonneg_of_mul_nonneg_right ((abs_nonneg _).trans (hab hγ)) (by positivity)
  refine ⟨fun g y w hg => ?_, fun g g' y w hgg => ?_⟩
  · unfold setSheetDensity
    split_ifs with hγ
    · exact mul_nonneg (hg _) (hnn hγ.choose_spec)
    · exact le_rfl
  · unfold setSheetDensity
    by_cases hγ : ∃ γ, IsSetSheet S Ψ y w γ
    · rw [dite_eq_left hγ, dite_eq_left hγ]
      have hs := hγ.choose_spec
      have hmem : hγ.choose y ∈ S := hs.2.self_of_nhds.2.1
      have hg := hgg _ hmem
      rw [abs_mul]
      calc |g (hγ.choose y)| * |maDensity (fun j y' => pot L j (hγ.choose y')) y|
          ≤ g' (hγ.choose y) * (3 ^ e * maDensity
              (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (hγ.choose y')) y) :=
            mul_le_mul hg (hab hs) (abs_nonneg _) ((abs_nonneg _).trans hg)
        _ = 3 ^ e * (g' (hγ.choose y) * maDensity
              (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (hγ.choose y')) y) := by ring
    · rw [dite_eq_right hγ, dite_eq_right hγ]
      simp

end GlobalTheory.CompanionTheory.Ar.Pub.CxTwist
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothMetricsNonnegDensityStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_metrics_nonneg_density : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
    ∃ N : Fin e → HermLine ι, (∀ j, IsSmoothHerm (N j)) ∧
      ∀ (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
        (∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) →
        (∀ (g : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z, 0 ≤ g z) → 0 ≤ setSheetDensity S Ψ (pot N) g y w) ∧
        ∀ (g g' : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z ∈ S, |g z| ≤ g' z) →
          |setSheetDensity S Ψ (pot L) g y w| ≤ 3 ^ e * setSheetDensity S Ψ (pot N) g' y w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxTwist.exists_dominating_twist | exact GlobalTheory.CompanionTheory.Ar.Pub.CxTwist.exists_dominating_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxTwist.exists_dominating_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGoodProjFirstCoordinate
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGoodProjFirstCoordinate
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem card_le_ringKrullDim {σ : Type} [Finite σ] (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime] {n : ℕ}
    (x : Fin n → MvPolynomial σ ℂ ⧸ Q) (hx : AlgebraicIndependent ℂ x) :
    ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ Q) := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ (MvPolynomial σ ℂ ⧸ Q)
  have hns : n ≤ s := by
    set S := Algebra.adjoin ℂ (Set.range (g ∘ X))
    have hmem : ∀ y, g y ∈ S := by
      intro y
      show g y ∈ Algebra.adjoin ℂ (Set.range (g ∘ X))
      rw [Algebra.adjoin_range_eq_range_aeval]
      refine ⟨y, ?_⟩
      show aeval (g ∘ X) y = g y
      rw [← MvPolynomial.aeval_unique g]
    let g' : MvPolynomial (Fin s) ℂ →+* S := g.toRingHom.codRestrict S.toSubsemiring hmem
    have hg' : (algebraMap S (MvPolynomial σ ℂ ⧸ Q)).comp g' = g.toRingHom := by
      ext y <;> rfl
    have halg : Algebra.IsAlgebraic S (MvPolynomial σ ℂ ⧸ Q) := by
      refine ⟨fun b => ?_⟩
      obtain ⟨p, hpm, hp⟩ := hint b
      refine IsIntegral.isAlgebraic ⟨p.map g', hpm.map g', ?_⟩
      rw [Polynomial.eval₂_map, hg']
      exact hp
    have h1 := hx.cardinalMk_le_trdeg
    have h2 := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℂ (Set.range (g ∘ X))
    have h3 := Cardinal.mk_range_le (f := g ∘ X)
    have := h1.trans (h2.trans h3)
    simpa using this
  have hdim : (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ Q) := by
    refine le_ringKrullDim_of_isIntegral g.toRingHom hint hinj s ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  exact le_trans (by exact_mod_cast hns) hdim

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isWeightedHomogeneous_of_isMultiHomog (f : MRingOver ℂ ι) (a : K → ℕ) (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (blkWt (ι := ι)) f (Finsupp.equivFunOnFinite.symm a) := by
  intro m hm
  have hms : m ∈ f.support := mem_support_iff.mpr hm
  ext k
  rw [weight_blkWt_apply, hf m hms k]
  simp

theorem ideal_isHomogeneous (Q : Ideal (MRingOver ℂ ι)) (hQ : IsMultiHomogIdeal Q) :
    Q.IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkWt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨_, (mem_weightedHomogeneousSubmodule ℂ _ _ _).mpr (isWeightedHomogeneous_of_isMultiHomog f a ha)⟩

def segMonC (i : (k : K) → ι k) : MRingOver ℂ ι := ∏ k, X ⟨k, i k⟩

theorem segMonC_isWeightedHomogeneous (i : (k : K) → ι k) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (segMonC i) oneK := by
  unfold segMonC
  have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRingOver ℂ ι))
    (fun k => Finsupp.single k 1) (w := blkWt (ι := ι))
    (fun k _ => isWeightedHomogeneous_X ℂ _ _)
  convert this using 1
  ext k
  rw [Finsupp.finsetSum_apply]
  simp [oneK, Finsupp.single_apply]

theorem component_aeval_cx {E : Type*} (w' : E → (K →₀ ℕ))
    (yt : E → MRingOver ℂ ι)
    (hy : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (w' e)) (H : MvPolynomial E ℂ)
    (δ : K →₀ ℕ) :
    weightedHomogeneousComponent (blkWt (ι := ι)) δ (aeval yt H) =
      aeval yt (weightedHomogeneousComponent w' δ H) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H.as_sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hmon : IsWeightedHomogeneous (blkWt (ι := ι)) (aeval yt (monomial m (AddMonoidAlgebra.coeff H m)))
      (Finsupp.weight w' m) := by
    rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
    refine IsWeightedHomogeneous.C_mul ?_ _
    have := IsWeightedHomogeneous.prod m.support (fun e => yt e ^ m e) (fun e => m e • w' e)
      (fun e _ => (hy e).pow (m e))
    rwa [Finsupp.weight_apply]
  by_cases h : Finsupp.weight w' m = δ
  · subst h
    rw [hmon.weightedHomogeneousComponent_same,
      (isWeightedHomogeneous_monomial w' m (AddMonoidAlgebra.coeff H m) rfl).weightedHomogeneousComponent_same]
  · rw [hmon.weightedHomogeneousComponent_ne δ (Ne.symm h),
      (isWeightedHomogeneous_monomial w' m (AddMonoidAlgebra.coeff H m) rfl).weightedHomogeneousComponent_ne δ
        (Ne.symm h), map_zero]

theorem aeval_sumElim_factor_cx (k0 : K) {S : Type*} [CommRing S] [Algebra ℂ S] {r : ℕ}
    {H : MvPolynomial (Fin r ⊕ {k // k ≠ k0}) ℂ} {δ : K →₀ ℕ}
    (hH : IsWeightedHomogeneous (sWt k0 r) H δ) {n0 : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ}
    (hn0 : n0 ∈ H.support) (a : Fin r → S) (b : {k // k ≠ k0} → S) :
    aeval (Sum.elim a b) H = (∏ k', b k' ^ n0 (Sum.inr k')) * aeval (Sum.elim a 1) H := by
  conv_lhs => rw [H.as_sum]
  conv_rhs => rw [H.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hw : Finsupp.weight (sWt k0 r) n = Finsupp.weight (sWt k0 r) n0 :=
    (hH (mem_support_iff.mp hn)).trans (hH (mem_support_iff.mp hn0)).symm
  simp only [aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_pow, Finset.prod_const_one, mul_one,
    inr_eq_of_weight_eq k0 hw]
  ring

def segC (Q : Ideal (MRingOver ℂ ι)) (i : (k : K) → ι k) : MRingOver ℂ ι ⧸ Q :=
  Ideal.Quotient.mk _ (segMonC i)

theorem algebraicIndependent_sumElim_cx (Q : Ideal (MRingOver ℂ ι)) [Q.IsPrime]
    (hhom : IsMultiHomogIdeal Q) (k0 : K) (i0 : (k : K) → ι k)
    (hi0 : ∀ k, (X ⟨k, i0 k⟩ : MRingOver ℂ ι) ∉ Q) {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℂ)
    (hind : AlgebraicIndependent ℂ (forms (segC Q) L)) :
    AlgebraicIndependent ℂ (Sum.elim (forms (segC Q) L)
      (fun k' : {k // k ≠ k0} => Ideal.Quotient.mk Q (X ⟨k'.1, i0 k'.1⟩))) := by
  set xs : {k // k ≠ k0} → MRingOver ℂ ι ⧸ Q :=
    fun k' => Ideal.Quotient.mk Q (X ⟨k'.1, i0 k'.1⟩) with hxs
  let π := Ideal.Quotient.mkₐ ℂ Q
  let yt : Fin r ⊕ {k // k ≠ k0} → MRingOver ℂ ι :=
    Sum.elim (fun j => ∑ i, L j i • segMonC i) (fun k' => X ⟨k'.1, i0 k'.1⟩)
  have hyt : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (sWt k0 r e) := by
    rintro (j | k')
    · refine IsWeightedHomogeneous.sum _ _ _ fun i _ => ?_
      rw [smul_eq_C_mul]
      exact (segMonC_isWeightedHomogeneous i).C_mul _
    · exact isWeightedHomogeneous_X ℂ _ _
  have hπy : (fun e => π (yt e)) = Sum.elim (forms (segC Q) L) xs := by
    funext e
    rcases e with j | k'
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [yt, π, forms, segC, map_sum]
    · rfl
  have hcomp : ∀ G : MvPolynomial (Fin r ⊕ {k // k ≠ k0}) ℂ,
      Ideal.Quotient.mk Q (aeval yt G) = aeval (Sum.elim (forms (segC Q) L) xs) G := by
    intro G
    rw [← hπy, ← MvPolynomial.comp_aeval]
    rfl
  have hx0 : ∀ k', xs k' ≠ 0 := by
    intro k' h
    rw [hxs, Ideal.Quotient.eq_zero_iff_mem] at h
    exact hi0 k'.1 h
  rw [algebraicIndependent_iff]
  intro H hH0
  by_contra hne
  obtain ⟨n0, hn0⟩ := support_nonempty.mpr hne
  set δ := Finsupp.weight (sWt k0 r) n0
  set H' := weightedHomogeneousComponent (sWt k0 r) δ H
  have hH'hom : IsWeightedHomogeneous (sWt k0 r) H' δ :=
    weightedHomogeneousComponent_isWeightedHomogeneous δ H
  have hn0' : n0 ∈ H'.support := by
    rw [mem_support_iff, coeff_weightedHomogeneousComponent, if_pos rfl]
    exact mem_support_iff.mp hn0
  have hmem : aeval yt H ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hcomp]
    exact hH0
  have hmem' : aeval yt H' ∈ Q := by
    rw [← component_aeval_cx (sWt k0 r) yt hyt H δ]
    exact weightedHomogeneousComponent_mem_of_mem ℂ blkWt (ideal_isHomogeneous Q hhom) hmem δ
  have hzero : aeval (Sum.elim (forms (segC Q) L) xs) H' = 0 := by
    rw [← hcomp]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem'
  rw [aeval_sumElim_factor_cx k0 hH'hom hn0'] at hzero
  have hprod : (∏ k', xs k' ^ n0 (Sum.inr k')) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hx0 k')
  have h1 : aeval (Sum.elim (forms (segC Q) L) 1) H' = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hprod
  let G : MvPolynomial (Fin r) ℂ := aeval (Sum.elim X 1) H'
  have hG : ∀ {S : Type} [CommRing S] [Algebra ℂ S] (a : Fin r → S),
      aeval a G = aeval (Sum.elim a 1) H' := by
    intro S _ _ a
    simp only [G]
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    exact congrArg (fun f => aeval f H') (funext fun e => by rcases e with j | k' <;> simp)
  have hG0 : G = 0 := (algebraicIndependent_iff.mp hind) G (by rw [hG]; exact h1)
  have hH'0 : H' * ∏ k', X (Sum.inr k') = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_mul, map_zero, map_prod]
    by_cases hz : ∀ k', z (Sum.inr k') ≠ 0
    · have := aeval_sumElim_factor_cx k0 hH'hom hn0' (S := ℂ) (z ∘ Sum.inl) (z ∘ Sum.inr)
      have hzz : Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) = z := by
        funext e; rcases e with j | k' <;> rfl
      rw [hzz, ← hG, hG0, map_zero, mul_zero] at this
      rw [← coe_aeval_eq_eval]
      simp only [AlgHom.coe_toRingHom] at this ⊢
      rw [this, zero_mul]
    · push Not at hz
      obtain ⟨k', hk'⟩ := hz
      rw [Finset.prod_eq_zero (Finset.mem_univ k') (by simp [hk']), mul_zero]
  have hH'z : H' = 0 := by
    rcases mul_eq_zero.mp hH'0 with h | h
    · exact h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k' _ => X_ne_zero _)
  rw [hH'z] at hn0'
  simp at hn0'

theorem forms_not_algebraicIndependent_cx (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (hQ : IsCxVar Q e)
    {r : ℕ} (hr : e + 1 < r) (L : Fin r → ((k : K) → ι k) → ℂ) :
    ¬ AlgebraicIndependent ℂ (forms (segC Q) L) := by
  intro hind
  obtain ⟨⟨k0⟩, ⟨hprime, hhom, hrel⟩, hdim⟩ := hQ
  haveI := hprime
  choose i0 hi0 using hrel
  have hs := algebraicIndependent_sumElim_cx Q hhom k0 i0 hi0 L hind
  let eqv : Fin (r + Fintype.card {k // k ≠ k0}) ≃ Fin r ⊕ {k // k ≠ k0} :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _).symm)
  have h := card_le_ringKrullDim Q _ (hs.comp eqv eqv.injective)
  rw [hdim] at h
  have hc : Fintype.card {k // k ≠ k0} + 1 = Fintype.card K := by
    have h1 := Fintype.card_subtype_compl (fun k => k = k0)
    rw [Fintype.card_subtype_eq] at h1
    have := Fintype.card_pos_iff.mpr ⟨k0⟩
    simp only [ne_eq]
    omega
  have h' : r + Fintype.card {k // k ≠ k0} ≤ e + Fintype.card K := by exact_mod_cast h
  omega

def evC (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q) :
    (MRingOver ℂ ι ⧸ Q) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ Q (aeval z) fun a ha => by
    have h := hz.2 a ha
    rw [← coe_aeval_eq_eval] at h
    exact h

theorem evC_mk (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q)
    (q : MRingOver ℂ ι) : evC Q z hz (Ideal.Quotient.mk _ q) = aeval z q := rfl

theorem evC_segC (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q)
    (t : (k : K) → ι k) : evC Q z hz (segC Q t) = segre z t := by
  rw [segC, evC_mk, segMonC, map_prod]
  simp [segre]

theorem evC_forms (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q) {r : ℕ}
    (L : Fin r → ((k : K) → ι k) → ℂ) (j : Fin r) :
    evC Q z hz (forms (segC Q) L j) = ∑ t, L j t * segre z t := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [forms, map_sum, map_smul, evC_segC, smul_eq_mul]

theorem mem_conePts (Q : Ideal (MRingOver ℂ ι)) (hQ : IsMultiHomogIdeal Q) (k0 : K) {c : ℂ}
    (hc : c ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : scaleBlock k0 c z ∈ conePts Q := by
  refine ⟨fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, mul_ne_zero ?_ hi⟩
    split_ifs <;> simp [hc]
  · exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ (fun k => if k = k0 then c else 1) z hz.2

theorem false_of_forms_vanish_cx (Q : Ideal (MRingOver ℂ ι)) (hhom : IsMultiHomogIdeal Q) (k0 : K)
    {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℂ) (hL : ∀ t, IntOver ℂ (forms (segC Q) L) (segC Q t))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) (hV : ∀ j, ∑ t, L j t * segre z t = 0) : False := by
  choose i1 hi1 using hz.1
  have hs : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi1 k
  obtain ⟨p, hpm, hp⟩ := hL i1
  let g0 : MvPolynomial (Fin r) ℂ →+* ℂ := eval₂Hom (RingHom.id ℂ) 0
  have key : ∀ c : ℂ, c ≠ 0 → Polynomial.eval (c * segre z i1) (p.map g0) = 0 := by
    intro c hc
    have hzc := mem_conePts Q hhom k0 hc hz
    have hcomp : ((evC Q _ hzc : (MRingOver ℂ ι ⧸ Q) →+* ℂ)).comp
        ((aeval (forms (segC Q) L) : MvPolynomial (Fin r) ℂ →ₐ[ℂ] _) : MvPolynomial (Fin r) ℂ →+* _) =
        g0 := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [g0]
      · intro j
        have h1 : ∑ t, L j t * (c * segre z t) = c * ∑ t, L j t * segre z t := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
        simp [g0, evC_forms, GroundTheory.Heights₂.Heights.SegreCoordGoodProj.segre_scaleBlock, h1, hV j]
    have := congrArg (evC Q _ hzc : (MRingOver ℂ ι ⧸ Q) →+* ℂ) hp
    rw [Polynomial.hom_eval₂, hcomp] at this
    simp only [RingHom.coe_coe, evC_segC, GroundTheory.Heights₂.Heights.SegreCoordGoodProj.segre_scaleBlock,
      map_zero] at this
    rw [Polynomial.eval_map]
    exact this
  have hinf : {x : ℂ | (p.map g0).IsRoot x}.Infinite := by
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    have hx0 : x ≠ 0 := hx
    have := key (x / segre z i1) (div_ne_zero hx0 hs)
    rw [div_mul_cancel₀ x hs] at this
    exact this
  exact (hpm.map g0).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ hinf)

theorem evC_aeval (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q) {r : ℕ}
    (ℓ : Fin r → MRingOver ℂ ι ⧸ Q) (F : MvPolynomial (Fin r) ℂ) :
    evC Q z hz (aeval ℓ F) = aeval (fun j => evC Q z hz (ℓ j)) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp]

theorem exists_goodProj_coord (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (i : (k : K) → ι k) :
    IsCxVar Q e → (∃ z ∈ conePts Q, segre z i ≠ 0) →
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ),
      IsSetGoodProj (conePts Q) Ψ ∧ ∀ w, Ψ w 0 = w i := by
  intro hQ ⟨z0, hz0, hz0i⟩
  classical
  obtain ⟨r, hr, L, hL⟩ := exists_linear_normalization (k := ℂ) (segC Q) (e + 1)
    (fun r L hr => forms_not_algebraicIndependent_cx Q e hQ hr L)
  obtain ⟨⟨k0⟩, ⟨hprime, hhom, -⟩, -⟩ := hQ
  haveI := hprime
  cases r with
  | zero => exact (false_of_forms_vanish_cx Q hhom k0 L hL hz0 fun j => j.elim0).elim
  | succ r' =>
  have hw : segC Q i ≠ 0 := fun h =>
    hz0i (by rw [← evC_segC Q z0 hz0, h, map_zero])
  obtain ⟨p, hpm, hp, hc0⟩ :=
    GroundTheory.Heights₂.Heights.SegreCoordGoodProj.exists_monic_coeff_zero_ne _ hw (hL i)
  set c0 := p.coeff 0 with hc0def
  have hsupp : ∀ m ∈ (homogeneousComponent c0.totalDegree c0).support,
      Finsupp.degree m = c0.totalDegree := by
    intro m hm
    rw [mem_support_iff, coeff_homogeneousComponent] at hm
    by_contra hne
    exact hm (if_neg hne)
  obtain ⟨lam, hlam⟩ := exists_eval_cons_one_ne_zero _ _ hsupp
    (homogeneousComponent_totalDegree_ne_zero hc0)
  let Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
    { toFun := fun w j => Fin.cases (w i) (fun j' : Fin e => if h : (j' : ℕ) < r' then
          ∑ t, (L (Fin.succ ⟨j', h⟩) t - lam ⟨j', h⟩ * L 0 t) * w t else 0) j
      map_add' := by
        intro w w'
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp
        · simp only [Fin.cases_succ, Pi.add_apply]
          split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp
        · simp only [Fin.cases_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> simp [Finset.mul_sum, mul_left_comm] }
  refine ⟨Ψ, fun z hz hΨ => ?_, fun w => rfl⟩
  set V : Fin (r' + 1) → ℂ := fun j => ∑ t, L j t * segre z t with hVdef
  have hzi : segre z i = 0 := congrFun hΨ 0
  have hVs : ∀ j : Fin r', V j.succ = lam j * V 0 := by
    intro j
    have h := congrFun hΨ (Fin.succ ⟨j, by omega⟩)
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Fin.cases_succ, dif_pos j.2, Fin.eta,
      Pi.zero_apply] at h
    simp only [hVdef]
    rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib, ← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  by_cases hs : V 0 = 0
  · refine false_of_forms_vanish_cx Q hhom k0 L hL hz fun j => ?_
    refine Fin.cases hs (fun j => ?_) j
    exact (hVs j).trans (by rw [hs, mul_zero])
  let g : Polynomial ℂ := (ReciprocityTheory.ChartRestriction.G.Geo.subst lam c0).map
    ((aeval (0 : Fin r' → ℂ) : MvPolynomial (Fin r') ℂ →ₐ[ℂ] ℂ) : MvPolynomial (Fin r') ℂ →+* ℂ)
  have hgD : g.coeff c0.totalDegree ≠ 0 := by
    simp only [g, Polynomial.coeff_map, subst_coeff_totalDegree]
    simpa using hlam
  have hroot : ∀ x : ℂ, x ≠ 0 → g.eval x = 0 := by
    intro x hx
    have hc : x / V 0 ≠ 0 := div_ne_zero hx hs
    have hzc := mem_conePts Q hhom k0 hc hz
    set u : Fin (r' + 1) → ℂ := fun j => x / V 0 * V j with hudef
    have hu0 : u 0 = x := div_mul_cancel₀ x hs
    have hu' : (fun j : Fin r' => u j.succ - lam j • u 0) = 0 := by
      funext j
      simp only [hudef, hVs j, smul_eq_mul, Pi.zero_apply]
      ring
    have h1 : aeval u c0 = 0 := by
      have := congrArg (evC Q _ hzc : (MRingOver ℂ ι ⧸ Q) →+* ℂ) hp
      rw [Polynomial.hom_eval₂] at this
      simp only [RingHom.coe_coe, evC_segC, GroundTheory.Heights₂.Heights.SegreCoordGoodProj.segre_scaleBlock,
        hzi, mul_zero, Polynomial.eval₂_at_zero, map_zero, RingHom.comp_apply] at this
      rw [← this]
      simp only [AlgHom.coe_toRingHom, RingHom.coe_coe, evC_aeval]
      refine congrArg (fun v => aeval v c0) (funext fun j => ?_)
      rw [evC_forms]
      simp only [GroundTheory.Heights₂.Heights.SegreCoordGoodProj.segre_scaleBlock, hudef, hVdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    have h2 := eval₂_subst lam u c0
    rw [hu', hu0, h1] at h2
    rw [Polynomial.eval_map]
    exact h2
  have hg0 : g = 0 := Polynomial.eq_zero_of_infinite_isRoot g
    (Set.Infinite.mono (fun x hx => hroot x hx) (Set.finite_singleton (0 : ℂ)).infinite_compl)
  exact hgD (by rw [hg0, Polynomial.coeff_zero])

end GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGoodProjFirstCoordinateStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodProj_first_coordinate : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (i : (k : K) → ι k),
    IsCxVar Q e → (∃ z ∈ conePts Q, segre z i ≠ 0) →
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ),
      IsSetGoodProj (conePts Q) Ψ ∧ ∀ w, Ψ w 0 = w i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.exists_goodProj_coord | exact GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.exists_goodProj_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.exists_goodProj_coord <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableDomCellLogNormChart
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableDomCellLogNormChart
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open GroundTheory.Heights₂.Heights (chartLift chartLiftDom contDiff_chartLift chartLift_blockNonzero segre_chartLift
  chartWeight_of_coord)

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {m : ℕ}

theorem eval_chartSection (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (s : MRingOver ℂ ι)
    (x : Fin m → ℂ) : MvPolynomial.eval x (chartSection σ i s) = MvPolynomial.eval (chartLift σ i x) s := by
  induction s using MvPolynomial.induction_on with
  | C c => simp [chartSection]
  | add p q hp hq =>
    have : chartSection σ i (p + q) = chartSection σ i p + chartSection σ i q := by
      simp [chartSection]
    rw [this, map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p q hp =>
    have : chartSection σ i (p * X q) =
        chartSection σ i p * X (σ.symm (Function.update i q.1 q.2)) := by
      simp [chartSection]
    rw [this, map_mul, map_mul, hp]
    simp [chartLift]

theorem mem_closedBall_of_lift_mem_domCell {S : Set ((Σ k, ι k) → ℂ)} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {x : Fin m → ℂ} (hx : x ∈ chartSet S σ i) (hd : chartLift σ i x ∈ domCell i) :
    x ∈ Metric.closedBall (0 : Fin m → ℂ) 1 := by
  obtain ⟨z, -, hzi, rfl⟩ := hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro a
  have h := hd (σ a)
  rw [segre_chartLift σ i z hzi, hzi, norm_one] at h
  exact h

theorem abs_log_div_le {t h c : ℝ} (ht : 0 ≤ t) (hh : 0 < h) (hc : |Real.log h| ≤ c) (hc0 : 0 ≤ c) :
    |Real.log (t / h)| ≤ |Real.log t| + c := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using hc0
  · rw [Real.log_div ht.ne' hh.ne']
    exact (abs_sub _ _).trans (by gcongr)

end

theorem integrable_chartAbsDens_cellWeight : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ)
    (J : Ideal (MvPolynomial (Fin m) ℂ)),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    J ∈ chartComponents (conePts Q) σ i →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) →
    (∀ R C : ℝ, Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + C)
      (chartPot σ i N))) →
    Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) := by
  intro K _ _ ι _ Q e m σ i Ψ N A s a J hA _ _ hmeas hzero hJ hproj hint
  classical
  set T : Set (Fin m → ℂ) := Metric.closedBall 0 1 ∩ {x | x (σ.symm i) = 1} with hT
  have hTc : IsCompact T :=
    (isCompact_closedBall (0 : Fin m → ℂ) 1).inter_right
      (isClosed_eq (continuous_apply _) continuous_const)
  have hcont : ContinuousOn (fun x => Real.log (A.h (chartLift σ i x))) T := by
    have h1 : ContinuousOn (fun x => A.h (chartLift σ i x)) T :=
      hA.continuousOn.comp (contDiff_chartLift σ i (n := 0)).continuous.continuousOn
        fun x hx => chartLift_blockNonzero σ i hx.2
    exact h1.log fun x hx => (A.pos _ (chartLift_blockNonzero σ i hx.2)).ne'
  obtain ⟨C, hC⟩ := hTc.exists_bound_of_continuousOn hcont
  have hchart : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J, x ∈ chartSet (conePts Q) σ i := by
    intro x hx
    rw [← hzero]
    intro q hq
    exact hx q ((mem_chartComponents.1 hJ).1.2 hq)
  have hcoord : ∀ x ∈ chartSet (conePts Q) σ i, x (σ.symm i) = 1 := by
    rintro _ ⟨z, -, hzi, rfl⟩
    simpa using hzi
  have hmeasW : Measurable (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) := by
    unfold chartWeight
    exact (hmeas.comp (contDiff_chartLift σ i (n := 0)).continuous.measurable).piecewise
      (GroundTheory.Heights₂.Heights.isOpen_chartLiftDom σ i).measurableSet measurable_const
  have hmeasD : Measurable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) :=
    GroundTheory.Heights₂.Heights.SheetSumMeasurable.measurable_sheetSum hproj (fun a b => |a * b|)
      ((continuous_mul.comp continuous_id).abs.measurable) hmeasW _
  refine (hint 1 (max C 0)).mono' hmeasD.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (GroundTheory.Heights₂.Heights.chartAbsDens_nonneg _ _ _ _ _)]
  have key : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J,
      |chartWeight σ i ((domCell i).indicator (absLogNorm A s)) x| ≤
        |(Metric.closedBall (0 : Fin m → ℂ) 1).indicator
          (fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + max C 0) x| := by
    intro x hx
    have hxc := hchart x hx
    have h1 := hcoord x hxc
    rw [chartWeight_of_coord _ h1]
    by_cases hd : chartLift σ i x ∈ domCell i
    · have hb := mem_closedBall_of_lift_mem_domCell hxc hd
      have hC' : |Real.log (A.h (chartLift σ i x))| ≤ max C 0 :=
        (hC x ⟨hb, h1⟩).trans (le_max_left _ _)
      have hnz := chartLift_blockNonzero σ i h1
      have habs : absLogNorm A s (chartLift σ i x) = |logNormC A s (chartLift σ i x)| := by
        simp only [absLogNorm]
        rw [if_pos hnz]
      rw [Set.indicator_of_mem hd, Set.indicator_of_mem hb, habs, abs_abs, logNormC,
        ← eval_chartSection]
      exact (abs_log_div_le (norm_nonneg _) (A.pos _ hnz) hC' (le_max_right _ _)).trans
        (le_abs_self _)
    · rw [Set.indicator_of_notMem hd, abs_zero]
      exact abs_nonneg _
  have h := GroundTheory.Heights₂.Heights.sheetSum_le_mul (J := J) (A := chartProjMatrix σ Ψ) (y := y)
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hproj y) 1
    (fun x t => |chartWeight σ i ((domCell i).indicator (absLogNorm A s)) x *
      ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i N k ∘ t) y|)
    (fun x t => |(Metric.closedBall (0 : Fin m → ℂ) 1).indicator
      (fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + max C 0) x *
      ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i N k ∘ t) y|)
    (fun x hx t _ => by
      rw [one_mul, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (key x hx.1) (abs_nonneg _))
  exact h.trans_eq (one_mul _)

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableDomCellLogNormChartStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_domCell_logNorm_chart : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ)
    (J : Ideal (MvPolynomial (Fin m) ℂ)),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    J ∈ chartComponents (conePts Q) σ i →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) →
    (∀ R C : ℝ, Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + C)
      (chartPot σ i N))) →
    Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.integrable_chartAbsDens_cellWeight | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.integrable_chartAbsDens_cellWeight | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.integrable_chartAbsDens_cellWeight <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LintegralFibreLogNormFinite
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

section Assembly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem setSheetDensity_eq_zero {e : ℕ} {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ S, g z = 0) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : setSheetDensity S Ψ φ g y w = 0 := by
  unfold setSheetDensity
  split_ifs with hγ
  · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
  · rfl

theorem setSheetDensity_sum {e : ℕ} {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {τ : Type*} (t : Finset τ) (G : τ → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    setSheetDensity S Ψ φ (fun z => ∑ i ∈ t, G i z) y w = ∑ i ∈ t, setSheetDensity S Ψ φ (G i) y w := by
  unfold setSheetDensity
  split_ifs with hγ
  · rw [Finset.sum_mul]
  · simp

theorem exists_mem_domCell [DecidableEq K] {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) :
    ∃ i, z ∈ domCell i := by
  choose i1 _ using hz
  have : Nonempty ((k : K) → ι k) := ⟨i1⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun i' : (k : K) → ι k => ‖segre z i'‖
  exact ⟨i, hi⟩

theorem segre_ne_zero_of_mem_domCell {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0)
    {i : (k : K) → ι k} (hi : z ∈ domCell i) : segre z i ≠ 0 := by
  choose i1 hi1 using hz
  have h1 : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hi1 k
  intro h0
  have := hi i1
  rw [h0, norm_zero] at this
  exact h1 (norm_le_zero_iff.1 this)

end Assembly

theorem cell_mass_lt_top {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {N : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRingOver ℂ ι} {a : K → ℕ}
    (hQ : IsCxVar Q e) (hΨ : IsSetGoodProj (conePts Q) Ψ) (hΨ0 : ∀ w, Ψ w 0 = w i)
    (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hAa : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) (hsQ : s ∉ Q)
    (hnn : ∀ y w, 0 ≤ setSheetDensity (conePts Q) Ψ (pot N) ((domCell i).indicator (absLogNorm A s)) y w) :
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) ((domCell i).indicator (absLogNorm A s)) y) < ⊤ := by
  classical
  set σ : Fin (Fintype.card ((k : K) → ι k)) ≃ ((k : K) → ι k) := (Fintype.equivFin _).symm with hσ
  set G := (domCell i).indicator (absLogNorm A s) with hG
  obtain ⟨hGm, hGi⟩ := GlobalTheory.T.domCell_logNorm_measurable_invariant K ι A s a i hA hAa hs
  have hzero := GlobalTheory.T.zeroSet_chartIdeal_eq_chartSet K ι Q _ σ i hQ.2.1.2.1
  have hdim := GlobalTheory.T.ringKrullDim_chartComponents K ι Q e _ σ i hQ
  have hfin := GlobalTheory.T.chartComponents_finite_projection K ι Q e _ σ i Ψ hQ hΨ hΨ0 hdim
  have hfs := GlobalTheory.T.chart_density_integrable K ι Q e _ σ i N G Ψ hQ hN hGi hΨ0 (GlobalTheory.T.setFibre_finite_of_goodProj K ι Q e Ψ hQ hΨ) hzero hdim hfin
  have hsm : ∀ j, ∀ J ∈ chartComponents (conePts Q) σ i, GroundTheory.Heights₂.Heights.SmoothNear
      (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (chartPot σ i N j) := fun j J hJ =>
    GroundTheory.Heights₂.Heights.smoothNear_chartPot σ i hN (fun x hx => by
      have hx' : x ∈ chartSet (conePts Q) σ i := by
        rw [← hzero]
        exact fun q hq => hx q ((mem_chartComponents.1 hJ).1.2 hq)
      obtain ⟨z, -, hzi, rfl⟩ := hx'
      simpa using hzi) j
  have hint : Integrable (fun y => ∑ J ∈ chartComponents (conePts Q) σ i,
      chartAbsDens J (chartProjMatrix σ Ψ) (chartWeight σ i G) (chartPot σ i N) y) :=
    integrable_finsetSum _ fun J hJ =>
      GlobalTheory.T.integrable_domCell_logNorm_chart K ι Q e _ σ i Ψ N A s a J hA hAa hs hGm hzero hJ (hfin J hJ) fun R C =>
        GlobalTheory.T.integrable_chartAbsDensity _ e J _ _ _ R C (mem_chartComponents.1 hJ).1.1 (hdim J hJ) (hfin J hJ)
          (GlobalTheory.T.chartSection_not_mem_components K ι Q e _ σ i s a hQ hs hsQ J hJ) fun j => hsm j J hJ
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
  filter_upwards [hfs] with y hy
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : cxPosDens (conePts Q) Ψ (pot N) G y =
      ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot N) G y w := by
    unfold cxPosDens
    exact finsum_congr fun w => finsum_congr fun _ => max_eq_left (hnn y w)
  rw [hpos, hy]
  exact Finset.sum_le_sum fun J _ =>
    GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.chartDens_le_chartAbsDens _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart


open GlobalTheory.CompanionTheory.Ar.Pub.CxChart in
theorem GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) < ⊤ := by
  intro K _ ι _ Q e Ψ L A s a hQ hΨ hL hA hAa hs hsQ
  classical
  obtain ⟨N, hN, hTw⟩ := GlobalTheory.T.exists_smooth_metrics_nonneg_density K ι e L hL
  obtain ⟨hnn, hbd⟩ := hTw (conePts Q) Ψ fun z hz => hz.1
  set G : ((k : K) → ι k) → ((Σ k, ι k) → ℂ) → ℝ := fun i => (domCell i).indicator (absLogNorm A s) with hG
  have hG0 : ∀ i z, 0 ≤ G i z := fun i z => Set.indicator_nonneg (fun z _ => by
    unfold absLogNorm
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl) z
  have hWm := fun i => GlobalTheory.T.domCell_logNorm_measurable_invariant K ι A s a i hA hAa hs
  have hcell : ∀ i, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) < ⊤ := by
    intro i
    by_cases hi : ∃ z ∈ conePts Q, segre z i ≠ 0
    · obtain ⟨Ψ', hΨ', hΨ0⟩ := GlobalTheory.T.exists_goodProj_first_coordinate K ι Q e i hQ hi
      rw [GlobalTheory.T.integral_density_independent_projection K ι Q e Ψ Ψ' N (G i) hQ hΨ hΨ' hN (hWm i).1 (hWm i).2]
      exact cell_mass_lt_top hQ hΨ' hΨ0 hN hA hAa hs hsQ fun y w => (hTw (conePts Q) Ψ' fun z hz => hz.1).1 _ y w (hG0 i)
    · have h0 : ∀ z ∈ conePts Q, G i z = 0 := fun z hz => Set.indicator_of_notMem (fun hzi =>
        hi ⟨z, hz, segre_ne_zero_of_mem_domCell hz.1 hzi⟩) _
      have : ∀ y, cxPosDens (conePts Q) Ψ (pot N) (G i) y = 0 := fun y => by
        unfold cxPosDens
        simp [setSheetDensity_eq_zero (pot N) h0]
      simp [this]
  have hfib := GlobalTheory.T.setFibre_finite_of_goodProj K ι Q e Ψ hQ hΨ
  have hcov : ∀ z ∈ conePts Q, |logNormC A s z| ≤ ∑ i, G i z := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_mem_domCell hz.1
    have : |logNormC A s z| = G i z := by
      simp only [hG, Set.indicator_of_mem hi, absLogNorm, if_pos hz.1]
    rw [this]
    exact Finset.single_le_sum (f := fun i => G i z) (fun i _ => hG0 i z) (Finset.mem_univ i)
  have hpt : ∀ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) ≤
      ENNReal.ofReal (3 ^ e) * ∑ i, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) := by
    intro y
    have hnnd : ∀ i, 0 ≤ cxPosDens (conePts Q) Ψ (pot N) (G i) y := fun i =>
      finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnnd i, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold cxPosDens
    simp only [finsum_mem_eq_finite_toFinset_sum _ (hfib y)]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    refine (hbd _ (fun z => ∑ i, G i z) y w hcov).trans ?_
    rw [setSheetDensity_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => le_max_left _ _) (by positivity)
  calc ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
        |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|)
      ≤ ∫⁻ y, ENNReal.ofReal (3 ^ e) * ∑ i, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (3 ^ e) * ∑ i, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum' _ fun i _ =>
          (GlobalTheory.T.aemeasurable_cxPosDensity K ι Q e Ψ N (G i) hQ hΨ hN (hWm i).1 (hWm i).2).ennreal_ofReal]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.sum_lt_top.2 fun i _ => hcell i)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LintegralFibreLogNormFiniteStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fibre_logNorm_finite : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top <;> assumption)
end
