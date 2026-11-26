module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisor
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberMetricChange
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousMetricRatio
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousMetricRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.Descent

open ReciprocityTheory.AnForm.M

section General
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem holoOn_continuousOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X}
    {f : X → ℂ} (hU : IsOpen U) (h : A.HoloOn U f) : ContinuousOn f U := by
  intro t ht
  obtain ⟨j, hj⟩ := A.cover t
  have h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) (A.chart j t) :=
    h j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using ht⟩
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) t :=
    ContinuousAt.comp h1.continuousAt ((A.chart j).continuousAt hj)
  have h3 : ((f ∘ (A.chart j).symm) ∘ A.chart j) =ᶠ[𝓝 t] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
    simp [(A.chart j).left_inv hu]
  exact (h2.congr h3).continuousWithinAt

theorem exists_continuous_descent {P : Ideal (MRing J)} {d : ℕ} (M : CxModel P d)
    (F : ((Σ k, J k) → ℂ) → ℝ) (hF : ContinuousOn F {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ), (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, F (torusSmul c z) = F z) :
    ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts P, κ (M.proj z) = F z := by
  choose r hr hpr using M.surj
  have key : ∀ z ∈ mcPts P, F (r (M.proj z)) = F z := by
    intro z hz
    obtain ⟨c, hc, e⟩ := (M.fibre _ (hr _) z hz).1 (hpr _)
    calc F (r (M.proj z)) = F (torusSmul c (r (M.proj z))) := (hinv c hc _ (hr _)).symm
      _ = F z := by rw [← e]
  refine ⟨fun x => F (r x), ?_, key⟩
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections x
  have hsc : ContinuousOn s U := continuousOn_pi.2 fun p => holoOn_continuousOn hU (hh p)
  have hcomp : ContinuousOn (F ∘ s) U := hF.comp hsc fun y hy => (hs y hy).1.1
  refine (hcomp.continuousAt (hU.mem_nhds hx)).congr ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  have h := key (s y) (hs y hy).1
  rw [(hs y hy).2] at h
  exact h.symm

theorem log_h_torusSmul (A : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h (torusSmul c z)) = (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + Real.log (A.h z) := by
  have h1 : A.h (torusSmul c z) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have h2 : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [h1, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => h2 k) (A.pos z hz).ne',
    Real.log_prod (fun k _ => h2 k)]
  simp only [Real.log_zpow]

theorem log_h_continuousOn {A : HermLine J} (hA : IsSmoothHerm A) :
    ContinuousOn (fun z => Real.log (A.h z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  ContinuousOn.log hA.continuousOn fun z hz => (A.pos z hz).ne'

end General

theorem logDiff_descends : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb : HermLine J), IsSmoothHerm Nb → Nb.a = muTwDeg Hd B → ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), κ (M.proj z) = Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B Nb hNb hdeg
  have hA : ∀ p, ∃ A : HermLine J, p ∈ D.SB B → A.a = D.vdeg p ∧ IsSmoothHerm A ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z := by
    intro p
    by_cases hp : p ∈ D.SB B
    · obtain ⟨A, h1, h2, -, h3⟩ :=
        (GlobalTheory.T.vertical_factor_smooth_hermitian_metric K J II Ψ Ω W D p (Finset.mem_of_mem_filter p hp)).1
      exact ⟨A, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨S.ref, fun h => absurd h hp⟩
  choose A hA using hA
  have hdegk : ∀ k, (Nb.a k : ℝ) = (S.ref.a k : ℝ) + ∑ p ∈ D.SB B, ((A p).a k : ℝ) := by
    intro k
    have href : S.ref.a = Hd.aMu := S.ref_deg
    have hs : ∑ p ∈ D.SB B, (A p).a k = ∑ p ∈ D.SB B, D.vdeg p k :=
      Finset.sum_congr rfl fun p hp => by rw [(hA p hp).1]
    have : Nb.a k = S.ref.a k + ∑ p ∈ D.SB B, (A p).a k := by
      rw [hdeg, href, hs]
      simp [muTwDeg, Finset.sum_apply]
    rw [this]
    push_cast
    rfl
  obtain ⟨κ, hκ, hκe⟩ := exists_continuous_descent M
    (fun z => Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log ((A p).h z))
    (((log_h_continuousOn hNb).sub (log_h_continuousOn S.ref_smooth)).sub
      (continuousOn_finsetSum _ fun p hp => log_h_continuousOn (hA p hp).2.1))
    (by
      intro c hc z hz
      have hb := hz.1
      simp only [log_h_torusSmul _ hc hb, Finset.sum_add_distrib]
      rw [Finset.sum_comm (s := D.SB B)]
      simp only [hdegk, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      ring)
  refine ⟨κ, hκ, fun z hz => ?_⟩
  rw [hκe z hz]
  congr 1
  exact Finset.sum_congr rfl fun p hp => by rw [(hA p hp).2.2 z hz]

end GlobalTheory.CompanionTheory.Ar.Cusp.Descent
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousMetricRatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_metric_ratio : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb : HermLine J), IsSmoothHerm Nb → Nb.a = muTwDeg Hd B → ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), κ (M.proj z) = Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Descent.logDiff_descends | exact GlobalTheory.CompanionTheory.Ar.Cusp.Descent.logDiff_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Descent.logDiff_descends <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeHeightLimit
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeHeightLimit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Local

variable {e : ℕ} {X : Type} [TopologicalSpace X] {I : Type} [Fintype I]

theorem holoOn_mono (A : FinHolAtlas e X) {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hs : V ⊆ U) :
    A.HoloOn V g :=
  fun j w hw => h j w ⟨hw.1, hs hw.2⟩

theorem continuousOn_of_holoOn (A : FinHolAtlas e X) {U : Set X} {s : X → I → ℂ}
    (hU : IsOpen U) (hs : ∀ p, A.HoloOn U fun y => s y p) : ContinuousOn s U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  refine ContinuousAt.continuousWithinAt (continuousAt_pi.2 fun p => ?_)
  have hw : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j y) ∈ U
      rw [(A.chart j).left_inv hj]; exact hy⟩
  have h1 : ContinuousAt ((fun y => s y p) ∘ (A.chart j).symm) (A.chart j y) :=
    (hs p j _ hw).continuousAt
  have h2 : ContinuousAt (A.chart j) y := (A.chart j).continuousAt hj
  have h3 : ContinuousAt (((fun y => s y p) ∘ (A.chart j).symm) ∘ A.chart j) y :=
    ContinuousAt.comp h1 h2
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(A.chart j).left_inv hy']

theorem log_norm_section_local (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {s : X → I → ℂ}
    (hs : ∀ p, A.HoloOn U fun y => s y p) {y₀ : X} (hy₀ : y₀ ∈ U) {T : (I → ℂ) → ℂ}
    (hT : AnalyticAt ℂ T (s y₀)) (hT0 : T (s y₀) ≠ 0) {Q : (I → ℂ) → Prop}
    (hQ : ∀ᶠ z in 𝓝 (s y₀), Q z) :
    ∃ U' : Set X, IsOpen U' ∧ y₀ ∈ U' ∧ U' ⊆ U ∧ (∀ y ∈ U', Q (s y)) ∧ ∃ G : X → ℂ, A.HoloOn U' G ∧
      ∀ y ∈ U', Real.log ‖T (s y)‖ = (G y).re := by
  set L : (I → ℂ) → ℂ := fun z => Complex.log (T z / T (s y₀)) with hL
  have hLa : AnalyticAt ℂ L (s y₀) := by
    refine (hT.div analyticAt_const hT0).clog ?_
    simp [hT0]
  have hev : ∀ᶠ z in 𝓝 (s y₀), AnalyticAt ℂ L z ∧ T z ≠ 0 ∧ Q z :=
    hLa.eventually_analyticAt.and ((hT.continuousAt.eventually_ne hT0).and hQ)
  obtain ⟨N, hNsub, hNo, hzN⟩ := mem_nhds_iff.1 hev
  have hc := continuousOn_of_holoOn A hU hs
  refine ⟨U ∩ s ⁻¹' N, hc.isOpen_inter_preimage hU hNo, ⟨hy₀, hzN⟩, Set.inter_subset_left,
    fun y hy => (hNsub hy.2).2.2, fun y => L (s y) + (Real.log ‖T (s y₀)‖ : ℂ), ?_, ?_⟩
  · intro j w hw
    have hsw : AnalyticAt ℂ (fun w => s ((A.chart j).symm w)) w :=
      analyticAt_pi_iff.2 fun p => hs p j w ⟨hw.1, hw.2.1⟩
    have hcomp : AnalyticAt ℂ (fun w => L (s ((A.chart j).symm w))) w :=
      AnalyticAt.comp (f := fun w => s ((A.chart j).symm w)) (hNsub hw.2.2).1 hsw
    exact hcomp.add analyticAt_const
  · intro y hy
    have hTy := (hNsub hy.2).2.1
    simp only [hL, Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hTy) (norm_ne_zero_iff.2 hT0)]
    ring

end Local

section Slots

variable {X : Type} [TopologicalSpace X] {e : ℕ}

theorem positionPot_lt (th Pn : LocPot X) (f : X → ℝ) {i : ℕ} {j : Fin e} (hj : (j : ℕ) < i) :
    positionPot th Pn f i j = th + LocPot.ofFun f := by
  simp [positionPot, hj]

theorem positionPot_ge (th Pn : LocPot X) (f : X → ℝ) {i : ℕ} {j : Fin e} (hj : ¬ (j : ℕ) < i) :
    positionPot th Pn f i j = Pn + LocPot.ofFun fun _ => 0 := by
  simp [positionPot, hj]

theorem add_ofFun_U (P : LocPot X) (u : X → ℝ) (x : X) :
    (P + LocPot.ofFun u).U x = P.U x ∩ Set.univ := rfl

theorem add_ofFun_φ (P : LocPot X) (u : X → ℝ) (x y : X) :
    (P + LocPot.ofFun u).φ x y = P.φ x y + u y := rfl

end Slots

section Vertical

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

theorem sum_log_vertFactor_local (D : ComponentData II Ψ K J Ω W) (M : XModel D) (F : Finset ℕ)
    (hF : ∀ p ∈ F, p ∈ D.S) {U : Set M.Xc} (hU : IsOpen U) {s : M.Xc → (Σ k, J k) → ℂ}
    (hs : ∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) (hh : ∀ p, M.atlas.HoloOn U fun y => s y p)
    {y₀ : M.Xc} (hy₀ : y₀ ∈ U) :
    ∃ U' : Set M.Xc, IsOpen U' ∧ y₀ ∈ U' ∧ U' ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U' G ∧
      ∀ y ∈ U', ∑ p ∈ F, Real.log (D.vertFactor p (s y)) = (G y).re := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨U, hU, hy₀, subset_rfl, fun _ => 0, fun j w _ => analyticAt_const, fun y _ => by simp⟩
  | insert p F hp ih =>
    obtain ⟨U₁, hU₁, hy₁, hs₁, G₁, hG₁, hre₁⟩ := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
    obtain ⟨T, hT, hT0, hev⟩ := GroundTheory.Heights₂.Heights.NineStatements.NbarLeviChartReg.vertFactor_local D
      (hF p (Finset.mem_insert_self p F)) (hs y₀ hy₀)
    obtain ⟨U₂, hU₂, hy₂, hs₂, hQ, G₂, hG₂, hre₂⟩ := log_norm_section_local M.atlas hU hh hy₀ hT hT0 hev
    refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hy₁, hy₂⟩, fun y hy => hs₁ hy.1, fun y => G₂ y + G₁ y, ?_, ?_⟩
    · intro j w hw
      exact (hG₂ j w ⟨hw.1, hw.2.2⟩).add (hG₁ j w ⟨hw.1, hw.2.1⟩)
    · intro y hy
      rw [Finset.sum_insert hp, hQ y hy.2 (hs y (hs₂ hy.2)), hre₂ y hy.2, hre₁ y hy.1, Complex.add_re]

end Vertical

theorem ptsIntegral_word_eq_mInt : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb Bm : HermLine J) (Pn : ReciprocityTheory.AnForm.M.LocPot M.Xc) (i : ℕ) (f G₀ : M.Xc → ℝ) (g : ((Σ k, J k) → ℂ) → ℝ), ReciprocityTheory.AnForm.M.IsPotential M.atlas Pn → (∀ x, ∀ y₀ ∈ (Pn).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pn).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, J k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Pn).φ x y' - (fun z => Real.log (Nb.h z)) (s y') = (G y').re) → M.atlas.SmoothOn S.R.Yo f → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → Real.log (Bm.h z) = Real.log (S.ref.h z) + f (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z)) → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → g z = G₀ (M.proj z)) → (∀ j, MeasureTheory.AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (MeasureTheory.volume.restrict (M.atlas.chart j).target)) → ReciprocityTheory.AnForm.M.MIntegrable M.atlas (positionPot S.R.th Pn f i) G₀ → ptsIntegral (mCoordIdeal D.y) (pot fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb) g = ReciprocityTheory.AnForm.M.mInt M.atlas (positionPot S.R.th Pn f i) G₀ := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B Nb Bm Pn i f G₀ g hPot hPn hf hBm hg hG₀ hInt
  obtain ⟨hYo, hnull, -, -⟩ := GlobalTheory.T.regular_chart_data_properties D.n M.Xc M.atlas S.R
  have hex : ∃ Q : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ), IsGoodProj (mCoordIdeal D.y) Q :=
    goodProjExists K J _ D.n D.arith
  have hnull' : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (S.R.Yoᶜ ∪ ∅)) = 0 := by
    intro j
    rw [Set.union_empty]
    exact hnull j
  have hN : IsPtsNull (mCoordIdeal D.y) D.n (∅ : Set ((Σ k, J k) → ℂ)) := fun _ _ => by simp
  have hsm : ∀ (j : Fin D.n) x, M.atlas.SmoothOn ((positionPot S.R.th Pn f i j).U x ∩ S.R.Yo)
      ((positionPot (e := D.n) S.R.th Pn f i j).φ x) := by
    intro j x a
    by_cases hj : (j : ℕ) < i
    · rw [positionPot_lt _ _ _ hj, add_ofFun_U]
      have s1 : (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' ((S.R.th.U x ∩ Set.univ) ∩ S.R.Yo) ⊆
          (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' S.R.th.U x := fun w hw => ⟨hw.1, hw.2.1.1⟩
      have s2 : (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' ((S.R.th.U x ∩ Set.univ) ∩ S.R.Yo) ⊆
          (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' S.R.Yo := fun w hw => ⟨hw.1, hw.2.2⟩
      exact ((S.R.th_pot.1 x a).mono s1).add ((hf a).mono s2)
    · rw [positionPot_ge _ _ _ hj, add_ofFun_U]
      have s1 : (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' ((Pn.U x ∩ Set.univ) ∩ S.R.Yo) ⊆
          (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' Pn.U x := fun w hw => ⟨hw.1, hw.2.1.1⟩
      exact ((hPot.1 x a).mono s1).add contDiffOn_const
  have hloc : ∀ (j : Fin D.n), ∀ x, ∀ y₀ ∈ (positionPot (e := D.n) S.R.th Pn f i j).U x ∩ S.R.Yo,
      ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (positionPot (e := D.n) S.R.th Pn f i j).U x ∩ S.R.Yo ∧
        ∃ s : M.Xc → (Σ k, J k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧
          (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
            ∀ y' ∈ U, (positionPot (e := D.n) S.R.th Pn f i j).φ x y' -
              (fun z => (1 : ℝ) * Real.log ((if (j : ℕ) < i then Bm else Nb).h z)) (s y') = (G y').re := by
    intro j x y₀ hy
    by_cases hj : (j : ℕ) < i
    · rw [positionPot_lt _ _ _ hj, add_ofFun_U] at hy
      rw [positionPot_lt _ _ _ hj, add_ofFun_U]
      simp only [if_pos hj, _root_.one_mul, add_ofFun_φ]
      obtain ⟨hyU, hyY⟩ := hy
      obtain ⟨U, hUo, hyU', hUs, s, hs, hh, G, hG, hre⟩ := S.th_ref x y₀ hyU.1
      obtain ⟨U₂, hU₂o, hy₂, hU₂s, G₂, hG₂, hre₂⟩ := sum_log_vertFactor_local D M (D.SB B)
        (fun p hp => (Finset.mem_filter.1 hp).1) (hUo.inter hYo) (s := s) (fun y hy => (hs y hy.1).1)
        (fun p => holoOn_mono _ (hh p) Set.inter_subset_left) ⟨hyU', hyY⟩
      refine ⟨U₂, hU₂o, hy₂, fun y hy => ⟨⟨hUs (hU₂s hy).1, trivial⟩, (hU₂s hy).2⟩, s,
        fun y hy => hs y (hU₂s hy).1, fun p => holoOn_mono _ (hh p) fun y hy => (hU₂s hy).1,
        fun y => G y - G₂ y, ?_, ?_⟩
      · intro a w hw
        exact (hG a w ⟨hw.1, (hU₂s hw.2).1⟩).sub (hG₂ a w hw)
      · intro y hy
        have hmem := hs y (hU₂s hy).1
        have hpY : M.proj (s y) ∈ S.R.Yo := by
          rw [hmem.2]
          exact (hU₂s hy).2
        have e1 := hBm (s y) hmem.1 hpY
        rw [hmem.2] at e1
        have e2 := hre y (hU₂s hy).1
        have e3 := hre₂ y hy
        rw [e1, Complex.sub_re]
        linarith
    · rw [positionPot_ge _ _ _ hj, add_ofFun_U] at hy
      rw [positionPot_ge _ _ _ hj, add_ofFun_U]
      simp only [if_neg hj, _root_.one_mul, add_ofFun_φ, add_zero]
      obtain ⟨hyU, hyY⟩ := hy
      obtain ⟨U, hUo, hyU', hUs, s, hs, hh, G, hG, hre⟩ := hPn x y₀ hyU
      exact ⟨U ∩ S.R.Yo, hUo.inter hYo, ⟨hyU', hyY⟩, fun y hy => ⟨hUs hy.1, hy.2⟩, s,
        fun y hy => hs y hy.1, fun p => holoOn_mono _ (hh p) Set.inter_subset_left, G,
        holoOn_mono _ hG Set.inter_subset_left, fun y hy => hre y hy.1⟩
  have hmain := GlobalTheory.T.mixed_integral_model_formula K J (mCoordIdeal D.y) D.n M hex.choose S.R.Yo ∅ ∅ (fun _ => 1)
    (fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb) (positionPot S.R.th Pn f i) g G₀ D.arith hex.choose_spec
    hYo hnull' hN hsm hloc (fun z hz _ hY _ => hg z hz hY) hG₀
  have h := (hmain.2.2 hInt).2
  have hfun : (fun (j : Fin D.n) z => (1 : ℝ) * Real.log ((if (j : ℕ) < i then Bm else Nb).h z)) =
      pot fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb := by
    funext j z
    simp [pot]
  unfold ptsIntegral
  rw [dite_eq_left hex, ← hfun]
  exact h

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeHeightLimitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_hodge_height_limit : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb Bm : HermLine J) (Pn : ReciprocityTheory.AnForm.M.LocPot M.Xc) (i : ℕ) (f G₀ : M.Xc → ℝ) (g : ((Σ k, J k) → ℂ) → ℝ), ReciprocityTheory.AnForm.M.IsPotential M.atlas Pn → (∀ x, ∀ y₀ ∈ (Pn).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pn).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, J k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Pn).φ x y' - (fun z => Real.log (Nb.h z)) (s y') = (G y').re) → M.atlas.SmoothOn S.R.Yo f → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → Real.log (Bm.h z) = Real.log (S.ref.h z) + f (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z)) → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → g z = G₀ (M.proj z)) → (∀ j, MeasureTheory.AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (MeasureTheory.volume.restrict (M.atlas.chart j).target)) → ReciprocityTheory.AnForm.M.MIntegrable M.atlas (positionPot S.R.th Pn f i) G₀ → ptsIntegral (mCoordIdeal D.y) (pot fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb) g = ReciprocityTheory.AnForm.M.mInt M.atlas (positionPot S.R.th Pn f i) G₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnAtlasContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnAtlasContinuous
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.AtlasSmooth

theorem continuous_of_atlas_smooth :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X) (f : X → ℝ),
      A.Smooth f → Continuous f :=
  fun _ _ _ A _ hf => ReciprocityTheory.AnForm.M.st_smooth_continuous A hf

end GlobalTheory.CompanionTheory.Ar.AtlasSmooth
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnAtlasContinuousStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_on_atlas_continuous : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X) (f : X → ℝ), A.Smooth f → Continuous f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth | exact GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoUniformly
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoUniformly
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem tendstoUniformlyOn_regWeight_of_isTied :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, J k) → ℂ)) (A : HermLine J) (S : LogLogRegularisationSetting M Xo A), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  intro K _ J _ P n M Xo A S hS K' hK'Y hK'
  refine hK'.induction_on (p := fun s => TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) s)
    ?_ ?_ ?_ ?_
  · intro u _
    simp
  · intro s t hst ht
    exact ht.mono hst
  · intro s t hs ht
    intro u hu
    filter_upwards [hs u hu, ht u hu] with a ha hb y hy
    exact hy.elim (ha y) (hb y)
  · intro x hx
    obtain ⟨j, hj⟩ := M.atlas.cover x
    have hopen : (M.atlas.chart j).source ∈ 𝓝 x := (M.atlas.chart j).open_source.mem_nhds hj
    obtain ⟨C, hCn, hCs, hCc⟩ := local_compact_nhds hopen
    refine ⟨C ∩ K', ?_, ?_⟩
    · exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hCn) self_mem_nhdsWithin
    · have hcpt : IsCompact (C ∩ K') := hCc.inter hK'
      have himg : IsCompact ((M.atlas.chart j) '' (C ∩ K')) :=
        hcpt.image_of_continuousOn
          ((M.atlas.chart j).continuousOn.mono fun y hy => hCs hy.1)
      have hsub : (M.atlas.chart j) '' (C ∩ K') ⊆
          (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo := by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨(M.atlas.chart j).map_source (hCs hy.1), ?_⟩
        show (M.atlas.chart j).symm ((M.atlas.chart j) y) ∈ S.R.Yo
        rw [(M.atlas.chart j).left_inv (hCs hy.1)]
        exact hK'Y hy.2
      have hu := (GlobalTheory.T.regularized_weight_tendsto_C2 K J P n M Xo A S hS j _ hsub himg).1
      rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
      intro ε hε
      filter_upwards [hu ε hε] with t ht y hy
      have h := ht _ (Set.mem_image_of_mem _ hy)
      simpa [Function.comp, (M.atlas.chart j).left_inv (hCs hy.1)] using h

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoUniformlyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_weight_tendsto_uniformly : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, J k) → ℂ)) (A : HermLine J) (S : LogLogRegularisationSetting M Xo A), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.tendstoUniformlyOn_regWeight_of_isTied | exact GlobalTheory.CompanionTheory.Ar.Cusp.tendstoUniformlyOn_regWeight_of_isTied | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.tendstoUniformlyOn_regWeight_of_isTied <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Main
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W}

theorem tuo_const {A₁ B₁ C₂ : Type*} [UniformSpace B₁] (l : Filter C₂) (f : A₁ → B₁) (s : Set A₁) :
    TendstoUniformlyOn (fun _ : C₂ => f) f l s :=
  fun _ hu => Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu

theorem mem_Xo_of_proj_mem {Hd : HodgeData D} {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine Hd))
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) (hY : M.proj z ∈ S.R.Yo) : z ∈ D.Xo := by
  obtain ⟨z', ⟨hz'X, hz'P⟩, hz'⟩ := S.Yo_sub _ hY
  obtain ⟨c, hc, hzc⟩ := (M.fibre z' hz'P z hz).1 hz'
  refine ⟨hz, fun hB => ?_⟩
  have hinv : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have h1 := D.bd_torus z hB (fun k => (c k)⁻¹) hinv
  have h2 : torusSmul (fun k => (c k)⁻¹) z = z' := by
    funext p
    rw [hzc]
    simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]
  rw [h2] at h1
  exact hz'X.2 h1

theorem tendsto_arLimFun (hLoc : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement) {Hd : HodgeData D} {M : XModel D}
    (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (hS : S.IsTied) (B : ℕ) (hII : IsFullIntersectionSystem II)
    (Nb : HermLine J) (hNb : IsSmoothHerm Nb) (hNa : Nb.a = muTwDeg Hd B) :
    Tendsto (arLimFun Hd S B) (𝓝[>] 0) (𝓝 (limTop Hd B Nb)) := by
  obtain ⟨Pn, hPn, hPnS⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K J (mCoordIdeal D.y) D.n M Nb hNb
  obtain ⟨Θ, hΘ, hΘp, hΘN⟩ := GlobalTheory.T.exists_positive_potential_dominating K J II Ψ Ω W D M Pn hPn
  obtain ⟨-, ⟨C₁, hC₁⟩, hpsh⟩ := GlobalTheory.T.regularized_weight_psh_and_bounds K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S Θ hS hΘ hΘp
  obtain ⟨κ, hκc, hκ⟩ := GlobalTheory.T.exists_continuous_metric_ratio K J II Ψ Ω W D Hd M S B Nb hNb hNa
  obtain ⟨Bκ, hBκ⟩ : ∃ b : ℝ, ∀ x, |κ x| ≤ b := by
    obtain ⟨b, hb⟩ := (isCompact_univ.image hκc).isBounded.exists_norm_le
    exact ⟨b, fun x => hb _ ⟨x, Set.mem_univ _, rfl⟩⟩
  obtain ⟨hYo, hYnull, -, -⟩ := GlobalTheory.T.regular_chart_data_properties D.n M.Xc M.atlas S.R
  have hph := S.R.ph_smooth

  set Cc : ℝ := |C₁| + |S.R.Clog| + |Bκ| + 1 with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  have hlogr : ∀ x ∈ S.R.Yo, 0 ≤ Real.log (S.R.r x) := fun x hx => Real.log_nonneg (S.R.one_le_r x hx)

  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧
      ∀ x ∈ S.R.Yo, |S.regWeight t x| ≤ |C₁| + |S.R.Clog| * Real.log (S.R.r x) ∧ S.regWeight t x ≤ |C₁| := by
    filter_upwards [hC₁] with t ht
    refine ⟨ht.1, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := ht.2 x hx
    have h3 := S.R.ph_ge x hx
    have h4 : -(|S.R.Clog| * Real.log (S.R.r x)) ≤ -S.R.Clog * Real.log (S.R.r x) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self S.R.Clog) (hlogr x hx)
      linarith
    have h5 : C₁ ≤ |C₁| := le_abs_self _
    have h6 : 0 ≤ |S.R.Clog| * Real.log (S.R.r x) := mul_nonneg (abs_nonneg _) (hlogr x hx)
    have h7 : 0 ≤ |C₁| := abs_nonneg _
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, by linarith⟩
  set G : M.Xc → ℝ := S.R.Yo.indicator fun x => κ x - S.R.ph x with hG
  set GT : ℝ → M.Xc → ℝ := fun t x => κ x - S.regWeight t x with hGT
  have hconv : ∀ i : ℕ, MIntegrable M.atlas (positionPot S.R.th Pn S.R.ph i) G ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t)) ∧
      Tendsto (fun t => mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t)) (𝓝[>] 0)
        (𝓝 (mInt M.atlas (positionPot S.R.th Pn S.R.ph i) G)) := by
    intro i
    refine GlobalTheory.T.mixed_integral_tendsto_off_divisor D.n M.Xc M.atlas S.R Θ hΘ hΘp
      (fun j : Fin D.n => if (j : ℕ) < i then S.R.th else Pn)
      (fun j : Fin D.n => if (j : ℕ) < i then S.R.ph else fun _ => 0)
      (fun (j : Fin D.n) t => if (j : ℕ) < i then S.regWeight t else fun _ => 0) G GT Cc
      ?_ ?_ ?_ ?_ ?_ ?_
    · intro j
      by_cases h : (j : ℕ) < i
      · simpa [h] using S.R.th_pot
      · simpa [h] using hPn
    · intro j
      by_cases h : (j : ℕ) < i
      · simpa [h] using hph
      · simp only [h, if_false]
        intro j'
        exact contDiffOn_const
    · have h1 := hpsh 1 one_pos
      filter_upwards [hbd, h1] with t ht ht1 j
      by_cases h : (j : ℕ) < i
      · simp only [h, if_true]
        refine ⟨ht.1, ?_, fun x hx => ?_⟩
        · have : Θ.rsmul 1 = Θ := by
            cases Θ
            simp [LocPot.rsmul]
          rwa [this] at ht1
        · obtain ⟨h2, h3⟩ := ht.2 x hx
          have hL := hlogr x hx
          have h4 : |S.R.Clog| * Real.log (S.R.r x) ≤ Cc * Real.log (S.R.r x) :=
            mul_le_mul_of_nonneg_right (by rw [hCc]; linarith [abs_nonneg C₁, abs_nonneg Bκ]) hL
          have h5 : |C₁| ≤ Cc := by rw [hCc]; linarith [abs_nonneg S.R.Clog, abs_nonneg Bκ]
          exact ⟨by linarith, by linarith⟩
      · simp only [h, if_false]
        refine ⟨fun j' => contDiffOn_const, hΘN, fun x hx => ?_⟩
        have hL := hlogr x hx
        have := mul_nonneg hCc0 hL
        simp only [abs_zero]
        exact ⟨by linarith, hCc0⟩
    · intro j k K' hK' hK'c
      by_cases h : (j : ℕ) < i
      · simp only [h, if_true]
        exact GlobalTheory.T.regularized_weight_tendsto_C2 K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S hS k K' hK' hK'c
      · simp only [h, if_false]
        exact ⟨tuo_const _ _ _, tuo_const _ _ _, tuo_const _ _ _⟩
    · filter_upwards [hbd] with t ht
      refine ⟨?_, fun x hx => ?_⟩
      · letI : MeasurableSpace M.Xc := borel M.Xc
        haveI : BorelSpace M.Xc := ⟨rfl⟩
        have hc : Continuous (GT t) := hκc.sub (GlobalTheory.T.smooth_on_atlas_continuous D.n M.Xc M.atlas _ ht.1)
        exact hc.measurable.indicator hYo.measurableSet
      · obtain ⟨h2, -⟩ := ht.2 x hx
        have hL := hlogr x hx
        have h4 : |S.R.Clog| * Real.log (S.R.r x) ≤ Cc * Real.log (S.R.r x) :=
          mul_le_mul_of_nonneg_right (by rw [hCc]; linarith [abs_nonneg C₁, abs_nonneg Bκ]) hL
        have h5 : |C₁| + |κ x| ≤ Cc := by
          have := hBκ x
          have h6 := le_abs_self Bκ
          rw [hCc]; linarith [abs_nonneg S.R.Clog]
        have h7 : |GT t x| ≤ |κ x| + |S.regWeight t x| := abs_sub _ _
        linarith
    · intro K' hK' hK'c
      have hu := GlobalTheory.T.regularized_weight_tendsto_uniformly K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S hS K' hK' hK'c
      have hu2 : TendstoUniformlyOn GT (fun x => κ x - S.R.ph x) (𝓝[>] 0) K' := by
        rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
        intro ε hε
        filter_upwards [hu ε hε] with t ht x hx
        have := ht x hx
        simp only [hGT, Real.dist_eq] at this ⊢
        rwa [show κ x - S.R.ph x - (κ x - S.regWeight t x) = -(S.R.ph x - S.regWeight t x) by ring, abs_neg]
      exact hu2.congr_right fun x hx => by simp [hG, Set.indicator_of_mem (hK' hx)]

  have hmeasT : ∀ t, M.atlas.Smooth (S.regWeight t) → ∀ j, AEStronglyMeasurable (GT t ∘ (M.atlas.chart j).symm)
      (volume.restrict (M.atlas.chart j).target) := by
    intro t ht j
    have hc : Continuous (GT t) := hκc.sub (GlobalTheory.T.smooth_on_atlas_continuous D.n M.Xc M.atlas _ ht)
    exact (hc.comp_continuousOn (M.atlas.chart j).continuousOn_symm).aestronglyMeasurable
      (M.atlas.chart j).open_target.measurableSet
  have hmeasG : ∀ j, AEStronglyMeasurable (G ∘ (M.atlas.chart j).symm)
      (volume.restrict (M.atlas.chart j).target) := by
    intro j
    set V : Set (Fin D.n → ℂ) := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo with hV
    have hVo : IsOpen V := (M.atlas.chart j).continuousOn_symm.isOpen_inter_preimage
      (M.atlas.chart j).open_target hYo
    have hF : ContinuousOn (fun y => κ ((M.atlas.chart j).symm y) - S.R.ph ((M.atlas.chart j).symm y)) V := by
      refine ContinuousOn.sub ?_ (hph j).continuousOn
      exact hκc.comp_continuousOn ((M.atlas.chart j).continuousOn_symm.mono Set.inter_subset_left)
    have h1 : AEStronglyMeasurable (V.indicator fun y => κ ((M.atlas.chart j).symm y) -
        S.R.ph ((M.atlas.chart j).symm y)) volume :=
      (aestronglyMeasurable_indicator_iff hVo.measurableSet).2 (hF.aestronglyMeasurable hVo.measurableSet)
    refine (h1.mono_measure Measure.restrict_le_self).congr ?_
    refine (ae_restrict_iff' (M.atlas.chart j).open_target.measurableSet).2 (Filter.Eventually.of_forall fun y hy => ?_)
    by_cases hyY : (M.atlas.chart j).symm y ∈ S.R.Yo
    · have hyV : y ∈ V := ⟨hy, hyY⟩
      simp [hG, Set.indicator_of_mem hyY, Set.indicator_of_mem hyV]
    · have hyV : y ∉ V := fun h => hyY h.2
      simp [hG, Set.indicator_of_notMem hyY, Set.indicator_of_notMem hyV]

  have hwl : ∀ i, ptsIntegral (mCoordIdeal D.y)
      (pot fun j : Fin D.n => if (j : ℕ) < i then muVert Hd B else Nb)
      (fun z => Real.log (Nb.h z) - Real.log ((muVert Hd B).h z)) =
      mInt M.atlas (positionPot S.R.th Pn S.R.ph i) G := by
    intro i
    refine GlobalTheory.T.regularized_hodge_height_limit K J II Ψ Ω W D Hd M S B Nb (muVert Hd B) Pn i S.R.ph G _ hPn hPnS hph ?_ ?_ hmeasG (hconv i).1
    · intro z hz hY
      have h1 := S.ph_eq z ⟨mem_Xo_of_proj_mem S hz hY, hz⟩ hY
      rw [GlobalTheory.T.vertical_hodge_metric_log_formula K J II Ψ Ω W D Hd B z hz, h1]
      ring
    · intro z hz hY
      have h1 := S.ph_eq z ⟨mem_Xo_of_proj_mem S hz hY, hz⟩ hY
      have h2 := GlobalTheory.T.vertical_hodge_metric_log_formula K J II Ψ Ω W D Hd B z hz
      have h3 := hκ z hz
      simp only [hG, Set.indicator_of_mem hY]
      rw [h1, h2, h3]
      ring
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) - ∑ i ∈ Finset.range (D.n + 1),
        mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t) = arLimFun Hd S B t := by
    have hint : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range (D.n + 1),
        MIntegrable M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t) :=
      (Filter.eventually_all_finset _).2 fun i _ => (hconv i).2.1
    filter_upwards [GlobalTheory.T.regularized_hodge_metric_smooth K J II Ψ Ω W D Hd M S B hS, hbd, hint] with t hsp hb hi
    obtain ⟨hsm, hdeg, hlog⟩ := hsp
    have hT := GlobalTheory.T.intersection_number_metric_change hLoc K J II (mCoordIdeal D.y) D.n Nb (muReg Hd S B t) hII D.arith hNb hsm
      (hdeg.trans hNa.symm)
    rw [arLimFun, hT]
    congr 1
    refine Finset.sum_congr rfl fun i hi' => ?_
    refine (GlobalTheory.T.regularized_hodge_height_limit K J II Ψ Ω W D Hd M S B Nb (muReg Hd S B t) Pn i (S.regWeight t) (GT t) _ hPn hPnS
      (fun j => (hb.1 j).mono fun y hy => ⟨hy.1, Set.mem_univ _⟩) ?_ ?_ (hmeasT t hb.1) (hi i hi')).symm
    · intro z hz _
      exact hlog z hz
    · intro z hz _
      simp only [hGT]
      rw [hlog z hz, hκ z hz]
      ring
  have hlim : Tendsto (fun t => II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) -
      ∑ i ∈ Finset.range (D.n + 1), mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t))
      (𝓝[>] 0) (𝓝 (limTop Hd B Nb)) := by
    rw [limTop]
    simp only [hwl]
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun i _ => (hconv i).2.2)
  exact hlim.congr' hev

end Main
end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_comparison_between_models : Top.Given → PtsIntegrableStatement →
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem)
      (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
      (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
      (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M M' : XModel D)
      (S : LogLogRegularisationSetting M D.Xo (muLine Hd))
      (S₁ : LogLogRegularisationSetting M' D.Xo (muLine Hd)) (B : ℕ),
      IsFullIntersectionSystem II → S.IsTied → S₁.IsTied →
      ArLimExists Hd S B ∧ arLim Hd S B = arLim Hd S₁ B := by
  intro hG _ K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M M' S S₁ B hII hS hS₁
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hNb : IsSmoothHerm (fsHerm J (muTwDeg Hd B)) := PB.StepW.fsHerm_isSmoothHerm K J _
  have h₁ := tendsto_arLimFun hIn.metricLocal S hS B hII _ hNb rfl
  have h₂ := tendsto_arLimFun hIn.metricLocal S₁ hS₁ B hII _ hNb rfl
  exact ⟨⟨_, h₁⟩, by rw [arLim, arLim, h₁.limUnder_eq, h₂.limUnder_eq]⟩
end
