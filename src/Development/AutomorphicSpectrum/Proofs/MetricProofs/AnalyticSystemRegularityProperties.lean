module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
public import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
public import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open scoped ContDiff

theorem GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics : ∀ (e : ℕ) (σ : Type) (S : AnSys e σ), IsOpen S.open' ∧ IsNull S.A S.open'ᶜ ∧ (∀ a, ∀ x ∈ S.open', IsTwiceDifferentiableAt S.A (S.potH a) x) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → IsPotential S.A (S.potT a t)) ∧ ∀ y ∈ S.open', Real.exp 1 ≤ rW S.L S.s y := by
  intro e σ S
  have hcl : IsClosed (bdry S.s) := LeviFormBoundaryTopology.isClosed_bdry S.sec
  refine ⟨hcl.isOpen_compl, ?_, ?_, ?_, fun y _ => rW_ge S.L S.s S.norm_le y⟩
  · have hAn : S.A.IsAnalyticSubset (bdry S.s) := by
      intro x
      refine ⟨S.L.U x, S.L.isOpen_U x, S.L.mem_U x, 1, fun _ => S.s x, fun _ => S.sec.1 x, ?_⟩
      ext z
      constructor
      · rintro ⟨hz, hzU⟩
        exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff S.sec hzU).1 hz⟩
      · rintro ⟨hzU, hz⟩
        exact ⟨(LeviFormBoundaryTopology.bdry_iff S.sec hzU).2 (hz 0), hzU⟩
    have hInt := LeviFormBoundaryTopology.interior_bdry_eq_empty S.sec S.snc
    intro j
    have h := analyticNull S.A (bdry S.s) hAn hInt j
    have hc : S.open'ᶜ = bdry S.s := compl_compl _
    rw [hc]
    rw [Set.inter_comm, (S.A.chart j).image_source_inter_eq'] at h
    exact h
  · intro a x hx j hj
    obtain ⟨hth, hph, -, -⟩ := S.sing a
    have h1 := hth.1 x j
    have h2 := hph j
    have hO1 : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U x) :=
      (S.A.chart j).isOpen_inter_preimage_symm ((S.th a).isOpen_U x)
    have hO2 : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ) :=
      (S.A.chart j).isOpen_inter_preimage_symm hcl.isOpen_compl
    have hm1 : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U x :=
      ⟨(S.A.chart j).map_source hj, by
        simpa [(S.A.chart j).left_inv hj] using (S.th a).mem_U x⟩
    have hm2 : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ :=
      ⟨(S.A.chart j).map_source hj, by
        have hx' : x ∈ (bdry S.s)ᶜ := hx
        simpa [(S.A.chart j).left_inv hj] using hx'⟩
    have hle : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
    have hA := (h1.contDiffAt (hO1.mem_nhds hm1)).of_le hle
    have hB := (h2.contDiffAt (hO2.mem_nhds hm2)).of_le hle
    exact hA.add hB
  · intro a t ht ht'
    exact isPotentialAdd S.A _ _ (S.sing a).1 (isPotential_ofFun S.A _ ((S.reg a).2.2 t ht ht').1)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.C2TendstoPullbackThroughChart
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.ChartPullBack

theorem comp_symm_eventuallyEq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : ((f ∘ c) ∘ c.symm) =ᶠ[𝓝 z] f := by
  filter_upwards [c.open_target.mem_nhds hz] with y hy
  simp [Function.comp, c.right_inv hy]

theorem fderiv_comp_symm_eq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : fderiv ℝ ((f ∘ c) ∘ c.symm) z = fderiv ℝ f z :=
  (comp_symm_eventuallyEq c f hz).fderiv_eq

theorem fderiv_comp_symm_eventuallyEq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : fderiv ℝ ((f ∘ c) ∘ c.symm) =ᶠ[𝓝 z] fderiv ℝ f := by
  filter_upwards [c.open_target.mem_nhds hz] with y hy
  exact fderiv_comp_symm_eq c f hy

theorem fderiv_fderiv_comp_symm_eq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) :
    fderiv ℝ (fderiv ℝ ((f ∘ c) ∘ c.symm)) z = fderiv ℝ (fderiv ℝ f) z :=
  (fderiv_comp_symm_eventuallyEq c f hz).fderiv_eq

theorem C2_tendsto_chart_pullback : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (c : OpenPartialHomeomorph X (Fin e → ℂ)) (g : ℝ → (Fin e → ℂ) → ℝ) (p : (Fin e → ℂ) → ℝ) (K' : Set (Fin e → ℂ)), K' ⊆ c.target → (TendstoUniformlyOn g p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (g t)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (g t))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (g t) z - fderiv ℝ p z‖ ≤ M * t) → (TendstoUniformlyOn (fun t => (g t ∘ c) ∘ c.symm) p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ ((g t ∘ c) ∘ c.symm)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ ((g t ∘ c) ∘ c.symm))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ ((g t ∘ c) ∘ c.symm) z - fderiv ℝ p z‖ ≤ M * t) := by
  intro e X _ c g p K' hK h
  obtain ⟨h0, h1, h2, M, hM⟩ := h
  refine ⟨h0.congr (Eventually.of_forall fun t z hz => ?_),
    h1.congr (Eventually.of_forall fun t z hz => ?_),
    h2.congr (Eventually.of_forall fun t z hz => ?_),
    M, hM.mono fun t ht z hz => ?_⟩
  · exact ((comp_symm_eventuallyEq c (g t) (hK hz)).eq_of_nhds).symm
  · exact (fderiv_comp_symm_eq c (g t) (hK hz)).symm
  · exact (fderiv_fderiv_comp_symm_eq c (g t) (hK hz)).symm
  · rw [fderiv_comp_symm_eq c (g t) (hK hz)]
    exact ht z hz

end GlobalTheory.CompanionTheory.Metric.ChartPullBack
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereSingularTotalMassDegree
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem AnSys.eventually_mInt_potT {e : ℕ} {σ : Type} (S : AnSys e σ) (w : Fin e → σ) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      mInt S.A (fun i => S.potT (w i) t) (fun _ => 1) = S.degNum w := by
  have hsm : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i, S.A.Smooth (S.phT (w i) t) := by
    refine Filter.eventually_all.2 fun i => ?_
    obtain ⟨h0, -, hreg⟩ := S.reg (w i)
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht
    exact (hreg t ht.1 ht.2).1
  filter_upwards [hsm] with t ht
  exact massIndep S.A (fun i => S.th (w i)) (fun i => S.phT (w i) t)
    (fun i => (S.sing (w i)).1) ht

theorem AnSys.abs_one_le_log_rW {e : ℕ} {σ : Type} (S : AnSys e σ) (y : S.X) :
    |(1 : ℝ)| ≤ 1 * Real.log (rW S.L S.s y) := by
  have h : Real.exp 1 ≤ rW S.L S.s y := by
    have := S.norm_le y
    unfold rW
    linarith
  have h1 : (1 : ℝ) ≤ Real.log (rW S.L S.s y) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) h)).2 h
  simpa using h1

theorem AnSys.mIntegrable_potH_and_mInt_eq_degNum :
    ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e σ) (w : Fin e → σ),
      MIntegrable S.A (fun i => S.potH (w i)) (fun _ => 1) ∧
        mInt S.A (fun i => S.potH (w i)) (fun _ => 1) = S.degNum w := by
  intro hC e σ S w
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  have hlim := hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun i => S.th (w i)) (fun i => S.ph (w i)) (fun i => S.phT (w i)) S.C₅ S.C S.t₀
    (fun i => S.sing (w i)) (fun i => S.reg (w i)) (fun i => S.c2 (w i))
    (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
    (fun _ y _ => S.abs_one_le_log_rW y)
    (TendstoUniformlyOn.tendstoLocallyUniformlyOn (by
      refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
      exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε))
  refine ⟨hlim.1, ?_⟩
  have hT : Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun _ => 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (mInt S.A (fun i => S.potH (w i)) (fun _ => 1))) :=
    hlim.2
  have hc : Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun _ => 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (S.degNum w)) :=
    tendsto_const_nhds.congr' ((S.eventually_mInt_potT w).mono fun _ h => h.symm)
  exact tendsto_nhds_unique hT hc

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EpsilonScheduleProperties
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem log_div_self_anti (a b : ℝ) (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    Real.log b / b ≤ Real.log a / a :=
  Real.log_div_self_antitoneOn ha (show Real.exp 1 ≤ b from ha.trans hab) hab

theorem epsT_mono (C t t' : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (htt : t ≤ t')
    (ht' : t' ≤ Real.exp (-Real.exp 1)) : epsT C t ≤ epsT C t' := by
  have ht'0 : 0 < t' := ht.trans_le htt
  have h1 := (GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht'0 ht').1
  have h2 : Real.log (1 / t') ≤ Real.log (1 / t) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv]
    linarith [Real.log_le_log ht htt]
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  exact mul_le_mul_of_nonneg_left (log_div_self_anti _ _ h1 h2) hC

theorem le_epsT (C t : ℝ) (hC : 1 ≤ C) (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    t ≤ epsT C t := by
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  set ℓ := Real.log (1 / t) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hle : ℓ ≤ 1 / t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / t by positivity)
    linarith
  have htl : t * ℓ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hle ht.le
    rwa [mul_one_div_cancel ht.ne'] at this
  have hA : t ≤ 1 / ℓ := by rw [le_div_iff₀ hℓ0]; exact htl
  have hB : 1 / ℓ ≤ Real.log ℓ / ℓ := div_le_div_of_nonneg_right h2 hℓ0.le
  have hq : 0 ≤ Real.log ℓ / ℓ := div_nonneg (by linarith) hℓ0.le
  have hC' : Real.log ℓ / ℓ ≤ C * (Real.log ℓ / ℓ) := le_mul_of_one_le_left hq hC
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  linarith

theorem epsT_tendsto (C : ℝ) : Tendsto (epsT C) (𝓝[>] 0) (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have hL : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    simpa [Function.comp_def, one_div] using this
  have h := (hl.comp hL).const_mul C
  rw [mul_zero] at h
  have e : epsT C = fun t => C * ((fun x : ℝ => Real.log x / x) ∘ (fun t : ℝ => Real.log (1 / t))) t := by
    funext t
    rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
    rfl
  rw [e]
  exact h

theorem epsT_le_one (C : ℝ) : ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → epsT C t ≤ 1 := by
  have hev : {t : ℝ | epsT C t < 1} ∈ 𝓝[>] (0 : ℝ) :=
    (epsT_tendsto C) (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨u / 2, by linarith, fun t ht hta => ?_⟩
  exact (hsub ⟨ht, by linarith⟩ : epsT C t < 1).le

theorem fin_pos_lower (n : ℕ) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    ∃ b : ℝ, 0 < b ∧ ∀ j, b ≤ a j := by
  by_cases h : Nonempty (Fin n)
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty a,
      (Finset.lt_inf'_iff _).2 (fun j _ => ha j), fun j => Finset.inf'_le _ (Finset.mem_univ j)⟩
  · exact ⟨1, one_pos, fun j => (h ⟨j⟩).elim⟩

theorem epsT_numerics :
    (∀ a b : ℝ, Real.exp 1 ≤ a → a ≤ b → Real.log b / b ≤ Real.log a / a) ∧
    (∀ C t t' : ℝ, 0 ≤ C → 0 < t → t ≤ t' → t' ≤ Real.exp (-Real.exp 1) → epsT C t ≤ epsT C t') ∧
    (∀ C t : ℝ, 1 ≤ C → 0 < t → t ≤ Real.exp (-Real.exp 1) → t ≤ epsT C t) ∧
    (∀ C : ℝ, Tendsto (epsT C) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ C : ℝ, ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → epsT C t ≤ 1) ∧
    (∀ (n : ℕ) (a : Fin n → ℝ), (∀ j, 0 < a j) → ∃ b : ℝ, 0 < b ∧ ∀ j, b ≤ a j) :=
  ⟨log_div_self_anti, epsT_mono, le_epsT, epsT_tendsto, epsT_le_one, fin_pos_lower⟩

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizationGlueBounds
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.RegFin

theorem isPsh_of_posPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw; rw [levi_zero]
  · exact (h x j y hy w hw).le

theorem quot_mem_unit {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) ∧
      Real.log (Real.log (1 / t)) / Real.log (1 / t) ≤ 1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  have hl : 0 < Real.log (1 / t) := lt_of_lt_of_le (Real.exp_pos 1) h1
  refine ⟨div_nonneg (by linarith) hl.le, ?_⟩
  rw [div_le_one hl]
  have := Real.log_le_sub_one_of_pos hl
  linarith

theorem quot_mono {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') (hte : t' ≤ Real.exp (-Real.exp 1)) :
    Real.log (Real.log (1 / t)) / Real.log (1 / t) ≤
      Real.log (Real.log (1 / t')) / Real.log (1 / t') := by
  have ht' := ht.trans_le htt
  have h1 := (GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht' hte).1
  have hle : Real.log (1 / t') ≤ Real.log (1 / t) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le ht htt)
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 h1) (Set.mem_Ici.2 (h1.trans hle)) hle

theorem isRegFamily_of_glue : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (Θ L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ K Cl t₀ : ℝ) (f : ℝ → Fin B.n → X → ℝ) (F : ℝ → X → ℝ), IsPotential A Θ → IsPosPot A Θ → IsPotential A th → (∀ y, logNormSec L s y ≤ 0) → (∀ y, ∃ j, y ∈ chartBall B j 1) → (∀ y ∉ bdry s, -C₅ * Real.log (rW L s y) ≤ ph y) → 0 < K → 1 ≤ Cl → 0 < t₀ → t₀ ≤ Real.exp (-Real.exp 1) → (∀ t, 0 < t → t ≤ t₀ → A.Smooth (F t) ∧ IsPsh A (th + LocPot.ofFun (F t) + Θ.rsmul (K * epsT Cl t)) ∧ ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ F t y ∧ F t y ≤ f t j y + K * epsT Cl t) → (∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ Cl ∧ -Cl * Real.log (Real.log (1 / t)) ≤ f t j y ∧ (y ∉ bdry s → ph y ≤ f t j y ∧ (rW L s y ≤ Real.log (1 / t) → f t j y ≤ ph y + t ^ ((1 : ℝ) / 3)))) → (∀ t t', 0 < t → t ≤ t' → t' ≤ t₀ → ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ f t' j y + epsT Cl t') → ∃ C : ℝ, IsRegFamily A Θ L s th ph F C t₀ := by
  intro e X _ A B Θ L th s ph C₅ K Cl t₀ f F hΘ hΘp hth hs hcov hph hK hCl ht₀ ht₀e hF hf hmono
  have hΘpsh := isPsh_of_posPot A Θ hΘp
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Cl * (1 + K) + |C₅| + 1 := ⟨_, rfl⟩
  have hC5 := abs_nonneg C₅
  have hClK : 0 ≤ Cl * K := by positivity
  have hC1 : 1 ≤ C := by nlinarith
  have hCK : Cl * (1 + K) ≤ C := by linarith
  have hCl' : Cl ≤ C := by nlinarith
  have hKCl : K * Cl ≤ C := by nlinarith
  have hr : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hs
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpt : ∀ y, ∃ j, y ∈ chartBall B j (5 / 4) := fun y => by
    obtain ⟨j, hj⟩ := hcov y
    exact ⟨j, chartBall_mono B j (by norm_num) hj⟩
  have ht₀1 : t₀ < 1 :=
    lt_of_le_of_lt ht₀e (by
      have := Real.exp_lt_exp.2 (show -Real.exp 1 < 0 by linarith [Real.exp_pos 1])
      rwa [Real.exp_zero] at this)
  refine ⟨C, ht₀, ht₀1, fun t ht htt => ?_⟩
  have hte := htt.trans ht₀e
  obtain ⟨hl1, hll⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  obtain ⟨hg0, hg1⟩ := quot_mem_unit ht hte
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = Real.log (Real.log (1 / t)) / Real.log (1 / t) := ⟨_, rfl⟩
  rw [← hgdef] at hg0 hg1
  have hεC : epsT C t = C * g := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef]
  have hεl : epsT Cl t = Cl * g := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef]
  obtain ⟨hsm, hpsh, hFf⟩ := hF t ht htt
  have hKg : K * (Cl * g) ≤ K * Cl := by
    have := mul_le_mul_of_nonneg_left hg1 (by linarith : (0 : ℝ) ≤ Cl)
    nlinarith
  have hKg0 : 0 ≤ K * (Cl * g) := by positivity
  have hFC : ∀ y, F t y ≤ Cl * (1 + K) := fun y => by
    obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := (hf t ht htt j y hj).1
    rw [hεl] at h1
    nlinarith
  refine ⟨hsm, fun y => (hFC y).trans hCK, fun y hy => ?_, fun y => ?_, ?_,
    fun y hy hyr => ?_, fun y hy => ?_, fun t' htt' ht' y => ?_⟩
  · obtain ⟨j, hj⟩ := hpt y
    exact ((hf t ht htt j y hj).2.2 hy).1.trans (hFf j y hj).1
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).1
    have h2 := (hf t ht htt j y hj).2.1
    have : Cl * Real.log (Real.log (1 / t)) ≤ C * Real.log (Real.log (1 / t)) :=
      mul_le_mul_of_nonneg_right hCl' (by linarith)
    linarith
  · refine GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (F t) hΘ hΘpsh hth hsm ?_ hpsh
    rw [hεl, hεC]
    have := mul_le_mul_of_nonneg_right hKCl hg0
    nlinarith
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := ((hf t ht htt j y hj).2.2 hy).2 hyr
    rw [hεl] at h1
    rw [hεC]
    have := mul_le_mul_of_nonneg_right hKCl hg0
    nlinarith
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have hfj := hf t ht htt j y hj
    rw [hεl] at h1
    rw [hεC]
    have hry := hr y
    have hrpos : 0 < rW L s y := by linarith
    have ht3 : 0 ≤ t ^ ((1 : ℝ) / 3) := by positivity
    have hCg0 : 0 ≤ C * g := by positivity
    by_cases hyr : rW L s y ≤ Real.log (1 / t)
    · have h2 := (hfj.2.2 hy).2 hyr
      have h3 : C * g ≤ C * g * rW L s y := le_mul_of_one_le_right hCg0 (by linarith)
      have := mul_le_mul_of_nonneg_right hKCl hg0
      nlinarith
    · push_neg at hyr
      have hlog : Real.log (rW L s y) / rW L s y ≤ g := by
        rw [hgdef]
        exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 hl1) (Set.mem_Ici.2 hry) hyr.le
      have hlog' : Real.log (rW L s y) ≤ g * rW L s y := by
        rw [div_le_iff₀ hrpos] at hlog
        linarith
      have hlpos : 0 < Real.log (1 / t) := by linarith [Real.exp_pos 1]
      have hgr : 1 ≤ g * rW L s y := by
        have e1 : g * rW L s y = Real.log (Real.log (1 / t)) * (rW L s y / Real.log (1 / t)) := by
          rw [hgdef]; ring
        have e2 : 1 ≤ rW L s y / Real.log (1 / t) := by
          rw [le_div_iff₀ hlpos]; linarith
        rw [e1]
        nlinarith
      have hlr0 : 0 ≤ Real.log (rW L s y) := Real.log_nonneg (by linarith)
      have hph1 := hph y hy
      have hph2 : -|C₅| * Real.log (rW L s y) ≤ -C₅ * Real.log (rW L s y) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₅]) hlr0
      have h4 : |C₅| * Real.log (rW L s y) ≤ |C₅| * (g * rW L s y) :=
        mul_le_mul_of_nonneg_left hlog' hC5
      have h5 : Cl * (1 + K) ≤ Cl * (1 + K) * (g * rW L s y) :=
        le_mul_of_one_le_right (by positivity) hgr
      have hCg : C * g * rW L s y = (Cl * (1 + K) + |C₅| + 1) * (g * rW L s y) := by
        rw [hCdef]; ring
      have := hFC y
      nlinarith
  · have ht'0 : 0 < t' := ht.trans_le htt'
    have hte' := ht'.trans ht₀e
    obtain ⟨hg0', hg1'⟩ := quot_mem_unit ht'0 hte'
    have hgm := quot_mono ht htt' hte'
    obtain ⟨g', hgdef'⟩ : ∃ g' : ℝ, g' = Real.log (Real.log (1 / t')) / Real.log (1 / t') :=
      ⟨_, rfl⟩
    rw [← hgdef'] at hg0' hg1'
    rw [← hgdef, ← hgdef'] at hgm
    have hεC' : epsT C t' = C * g' := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef']
    have hεl' : epsT Cl t' = Cl * g' := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef']
    obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := hmono t t' ht htt' ht' j y hj
    have h3 := ((hF t' ht'0 ht').2.2 j y hj).1
    rw [hεl] at h1
    rw [hεl'] at h2
    rw [hεC']
    have h4 : K * (Cl * g) ≤ K * (Cl * g') :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgm (by linarith)) hK.le
    have h5 : Cl * (1 + K) * g' ≤ C * g' := mul_le_mul_of_nonneg_right hCK hg0'
    have h6 : C * g' ≤ C * (C * g') := le_mul_of_one_le_left (by positivity) hC1
    linarith

end GlobalTheory.CompanionTheory.Ar.RegFin
end
