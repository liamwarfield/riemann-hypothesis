module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.RootOfRealisationTelescoping
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.PointsIntegralSmallLimit
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB

namespace PositivityTheory.Xgn.SmallPotentialLimit

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P

theorem pts_congr {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) {e : ℕ}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g g' : ((Σ k, ι k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  have key : ∀ Ψ y w, sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ g' y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · rw [h _ hγ.choose_spec.2.self_of_nhds.2.1]
    · rfl
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    simp only [key]
  · rfl

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (Q.isOpen_U x)
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ Q.U x
      rw [(A.chart j).left_inv hj]
      exact Q.mem_U x⟩
  exact ((h.1 x j).contDiffAt (hopen.mem_nhds hmem)).of_le (by
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    exact h2)

section Sys

variable {e : ℕ} {σ : Type} (S : AnSys e σ)

theorem one_le_log (y : S.X) : 1 ≤ Real.log (rW S.L S.s y) := by
  have h : Real.exp 1 ≤ rW S.L S.s y := rW_ge S.L S.s S.norm_le y
  exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) h)).2 h

theorem defect_bound (a : σ) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀) {y : S.X} (hy : y ∉ bdry S.s) :
    |S.ph a y - S.phT a t y| ≤ (|S.C| + |S.C₅|) * Real.log (rW S.L S.s y) := by
  obtain ⟨-, hC, hle, -⟩ := (S.reg a).2.2 t h0 h1
  have h2 := hC y
  have h3 := hle y hy
  have h4 := ((S.sing a).2.2.2 y hy).1
  have h5 := one_le_log S y
  rw [abs_of_nonpos (by linarith)]
  have h6 : S.C ≤ |S.C| * Real.log (rW S.L S.s y) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) h5)
  have h7 : S.C₅ * Real.log (rW S.L S.s y) ≤ |S.C₅| * Real.log (rW S.L S.s y) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  linarith

theorem defect_cont (a : σ) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    ContinuousOn (fun y => S.ph a y - S.phT a t y) (bdry S.s)ᶜ := by
  have hcl : IsClosed (bdry S.s) := LeviFormBoundaryTopology.isClosed_bdry S.sec
  intro y hy
  exact ((LeviFormBoundaryTopology.continuousAt_of_smoothOn S.A hcl.isOpen_compl (S.sing a).2.1 hy).sub
    (LeviFormBoundaryTopology.continuousAt_of_smoothOn S.A isOpen_univ ((S.reg a).2.2 t h0 h1).1
      (Set.mem_univ y))).continuousWithinAt

theorem defect_integrable (a : σ) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀) (Φ : Fin e → LocPot S.X)
    (hΦ : ∀ i, IsPotential S.A (Φ i)) : MIntegrable S.A Φ (fun y => S.ph a y - S.phT a t y) := by
  intro j Kc hK hKc
  have hcl : IsClosed (bdry S.s) := LeviFormBoundaryTopology.isClosed_bdry S.sec
  have hO : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ) :=
    (S.A.chart j).isOpen_inter_preimage_symm hcl.isOpen_compl
  set O := (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ with hOdef
  have hnull := (anSys_open_basics e σ S).2.1 j
  have hae : (Kc : Set (Fin e → ℂ)) =ᵐ[volume] (Kc ∩ O : Set (Fin e → ℂ)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    refine ⟨fun h => ⟨h, hK h, ?_⟩, fun h => h.1⟩
    by_contra hcon
    exact hy ⟨hK h, hcon⟩
  refine IntegrableOn.congr_set_ae ?_ hae
  have hm : MeasurableSet (Kc ∩ O) := hKc.measurableSet.inter hO.measurableSet
  have i1 := (mIntegrableCont S.A Φ hΦ (fun _ => (1 : ℝ)) continuous_const j Kc hK hKc).mono_set
    (Set.inter_subset_left (t := O))
  have i2 := (logNormIntegrable S.A S.L S.s S.m S.W S.potL S.sec S.snc Φ hΦ j Kc hK hKc).mono_set
    (Set.inter_subset_left (t := O))
  have i3 := ((i1.norm.const_mul (Real.exp 1)).add (i2.norm.const_mul 2)).const_mul (|S.C| + |S.C₅|)
  refine Integrable.mono' i3 ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ hm
    refine ContinuousOn.mul ?_ ((locDensCont S.A Φ hΦ j).mono fun y hy => hy.2.1)
    exact (defect_cont S a h0 h1).comp ((S.A.chart j).continuousOn_symm.mono fun y hy => hy.2.1)
      fun y hy => hy.2.2
  · filter_upwards [ae_restrict_mem hm] with y hy
    have hb := defect_bound S a h0 h1 (y := (S.A.chart j).symm y) hy.2.2
    have hr : Real.exp 1 ≤ rW S.L S.s ((S.A.chart j).symm y) := rW_ge S.L S.s S.norm_le _
    have hl : Real.log (rW S.L S.s ((S.A.chart j).symm y)) ≤
        Real.exp 1 + 2 * |logNormSec S.L S.s ((S.A.chart j).symm y)| := by
      have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le (Real.exp_pos 1) hr)
      have h2 := neg_abs_le (logNormSec S.L S.s ((S.A.chart j).symm y))
      unfold rW at this ⊢
      linarith
    have hc : 0 ≤ |S.C| + |S.C₅| := by positivity
    have hb2 := hb.trans (mul_le_mul_of_nonneg_left hl hc)
    have := mul_le_mul_of_nonneg_right hb2 (abs_nonneg (locDens S.A Φ j y))
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, one_mul]
    linarith

theorem tendsto_base (hC : ConvergenceSignedStatement) (a : σ) (w : Fin e → σ) :
    Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun y => S.ph a y - S.phT a t y))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  have hcl : IsClosed (bdry S.s) := LeviFormBoundaryTopology.isClosed_bdry S.sec
  have ht0 : 0 < S.t₀ := (S.reg a).1
  have hlim := hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun i => S.th (w i)) (fun i => S.ph (w i)) (fun i => S.phT (w i)) S.C₅ S.C S.t₀
    (fun i => S.sing (w i)) (fun i => S.reg (w i)) (fun i => S.c2 (w i))
    (fun _ => 0) (fun t y => if 0 < t ∧ t ≤ S.t₀ then S.ph a y - S.phT a t y else 0) (|S.C| + |S.C₅|)
    (fun t => by
      by_cases h : 0 < t ∧ t ≤ S.t₀
      · simp only [if_pos h]
        exact defect_cont S a h.1 h.2
      · simp only [if_neg h]
        exact continuousOn_const)
    (fun t y hy => by
      by_cases h : 0 < t ∧ t ≤ S.t₀
      · simp only [if_pos h]
        exact defect_bound S a h.1 h.2 hy
      · simp only [if_neg h, abs_zero]
        exact mul_nonneg (by positivity) (zero_le_one.trans (one_le_log S y)))
    (by
      refine Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε x hx => ?_
      obtain ⟨j, hj⟩ := S.A.cover x
      have hO : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ) :=
        (S.A.chart j).isOpen_inter_preimage_symm hcl.isOpen_compl
      have hm : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ :=
        ⟨(S.A.chart j).map_source hj, by
          show (S.A.chart j).symm (S.A.chart j x) ∈ (bdry S.s)ᶜ
          rw [(S.A.chart j).left_inv hj]
          exact hx⟩
      obtain ⟨Kc, hKc, hxK, hK⟩ := exists_compact_subset hO hm
      have hu := Metric.tendstoUniformlyOn_iff.1 (S.c2 a j Kc hK hKc).1 ε hε
      refine ⟨(S.A.chart j).source ∩ S.A.chart j ⁻¹' Kc, mem_nhdsWithin_of_mem_nhds
        (inter_mem ((S.A.chart j).open_source.mem_nhds hj)
          (((S.A.chart j).continuousAt hj).preimage_mem_nhds (mem_interior_iff_mem_nhds.1 hxK))), ?_⟩
      filter_upwards [hu, Ioc_mem_nhdsGT ht0] with t ht ht' y hy
      have h1 := ht _ hy.2
      simp only [Function.comp_apply, (S.A.chart j).left_inv hy.1] at h1
      rw [if_pos ⟨ht'.1, ht'.2⟩, Real.dist_eq, zero_sub, abs_neg]
      rwa [Real.dist_eq] at h1)
  have h0 : mInt S.A (fun i => S.th (w i) + LocPot.ofFun (S.ph (w i))) (fun _ => (0 : ℝ)) = 0 := by
    unfold mInt
    split_ifs
    · simp [integralWith]
    · rfl
  have h2 := hlim.2
  rw [h0] at h2
  refine h2.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT ht0] with t ht
  simp only [if_pos (show 0 < t ∧ t ≤ S.t₀ from ⟨ht.1, ht.2⟩)]
  rfl

end Sys

section Real

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type} {S : AnSys D σ}
  {P : Ideal (MRing ι)} (Re : Realis S P)

theorem log_sub_orbit {A B : HermLine ι} (hab : A.a = B.a) {z z' : (Σ k, ι k) → ℂ}
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : SameOrbit z z') :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h z') - Real.log (B.h z') := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [A.smul c z' hc, B.smul c z' hc, hab]
  have h0 : (∏ k, ‖c k‖ ^ B.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [Real.log_mul h0 (A.pos z' hz').ne', Real.log_mul h0 (B.pos z' hz').ne']
  ring

theorem line_samePot (a : σ) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    SamePot Re.R.A Set.univ (potOf Re.R (Re.line a t)) ((S.potT a t).pullback Re.π Re.holo.1) := by
  intro x hx
  obtain ⟨V, hV, hxV, G, hG, hGe⟩ := Re.ref_pot a x hx
  refine ⟨V ∩ Re.R.U x, hV.inter (Re.R.isOpen_U x), ⟨hxV, Re.R.mem_U x⟩, G,
    fun j => (hG j).mono fun y hy => ⟨hy.1, hy.2.1⟩, fun y hy => ?_⟩
  have e1 := hGe y hy.1
  have e2 := log_sub_orbit (Re.line_deg a t) (Re.R.mem y y (Re.R.mem_U y)).1
    (Re.R.compat x y y ⟨hy.2, Re.R.mem_U y⟩)
  have e3 := Re.line_eq a t h0 h1 y
  change Real.log ((Re.ref a).h (Re.R.lift x y)) - (S.th a).φ (Re.π x) (Re.π y) = _ at e1
  change Real.log ((Re.line a t).h (Re.R.lift x y)) -
    ((S.th a).φ (Re.π x) (Re.π y) + S.phT a t (Re.π y)) = _
  linarith

theorem holoOn_comp {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {A : FinHolAtlas e X}
    {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) :
    B.HoloOn (h ⁻¹' U) (fun y => g (h y)) := by
  intro j y hy
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm y))
  have a1 := hh.2 j k y ⟨hy.1, hk⟩
  have a2 := hg k (A.chart k (h ((B.chart j).symm y))) ⟨(A.chart k).map_source hk, by
    show (A.chart k).symm (A.chart k (h ((B.chart j).symm y))) ∈ U
    rw [(A.chart k).left_inv hk]
    exact hy.2⟩
  have a3 : AnalyticAt ℂ ((g ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (B.chart j).symm)) y :=
    AnalyticAt.comp a2 a1
  refine a3.congr ?_
  have hc : ContinuousAt (h ∘ (B.chart j).symm) y :=
    hh.1.continuousAt.comp ((B.chart j).continuousAt_symm hy.1)
  filter_upwards [hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with z hz
  simp only [Function.comp_apply]
  rw [(A.chart k).left_inv (show h ((B.chart j).symm z) ∈ (A.chart k).source from hz)]

theorem preimage_null : IsNull Re.R.A (Re.π ⁻¹' S.open')ᶜ := by
  have hAn : Re.R.A.IsAnalyticSubset (Re.π ⁻¹' bdry S.s) := by
    intro x
    refine ⟨Re.π ⁻¹' S.L.U (Re.π x), (S.L.isOpen_U _).preimage Re.holo.1, S.L.mem_U _, 1,
      fun _ y => S.s (Re.π x) (Re.π y), fun _ => holoOn_comp Re.holo (S.sec.1 (Re.π x)), ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff S.sec hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(LeviFormBoundaryTopology.bdry_iff S.sec hzU).2 (hz 0), hzU⟩
  have hInt := LeviFormBoundaryTopology.interior_bdry_eq_empty S.sec S.snc
  have hInt' : interior (Re.π ⁻¹' bdry S.s) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hns : ¬ interior (Re.π ⁻¹' bdry S.s) ⊆ Re.π ⁻¹' Re.br := fun hs => by
      have := interior_maximal hs isOpen_interior hx
      rw [Re.degree.2.2.2.1] at this
      exact this
    obtain ⟨y, hy, hyb⟩ := Set.not_subset.1 hns
    obtain ⟨E, hyE, hE, -⟩ := exists_localHomeomorph_of_isDegreeOff Re.holo Re.degree y hyb
    have hn : E '' (E.source ∩ interior (Re.π ⁻¹' bdry S.s)) ∈ 𝓝 (E y) :=
      E.image_mem_nhds hyE (inter_mem (E.open_source.mem_nhds hyE) (isOpen_interior.mem_nhds hy))
    have hsub : E '' (E.source ∩ interior (Re.π ⁻¹' bdry S.s)) ⊆ bdry S.s := by
      rintro _ ⟨z, hz, rfl⟩
      rw [← hE hz.1]
      exact (interior_subset hz.2 : z ∈ Re.π ⁻¹' bdry S.s)
    have := mem_interior_iff_mem_nhds.2 (mem_of_superset hn hsub)
    rw [hInt] at this
    exact this
  intro j
  have h := analyticNull Re.R.A _ hAn hInt' j
  have hc : (Re.π ⁻¹' S.open')ᶜ = Re.π ⁻¹' bdry S.s := by
    ext z
    simp [AnSys.open']
  rw [hc]
  rw [Set.inter_comm, (Re.R.A.chart j).image_source_inter_eq'] at h
  exact h

theorem pts_eq (hE : ResExistsStatement) (a₀ : σ) (A : HermLine ι) (w : Fin D → σ) (hA : IsSmoothHerm A)
    (ha : A.a = (Re.ref a₀).a)
    (hph : ∀ x, Re.π x ∈ S.open' → Real.log (A.h (Re.R.lift x x)) =
      Real.log ((Re.ref a₀).h (Re.R.lift x x)) + S.ph a₀ (Re.π x))
    {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    ptsIntegral P (pot fun j => Re.line (w j) t)
        (fun z => Real.log (A.h z) - Real.log ((Re.line a₀ t).h z)) =
      Re.deg * mInt S.A (fun i => S.potT (w i) t) (fun y => S.ph a₀ y - S.phT a₀ t y) := by
  have hlog : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      logNorm (A.tensor (Re.line a₀ t).inv).inv 1 z = Real.log (A.h z) - Real.log ((Re.line a₀ t).h z) := by
    intro z hz
    rw [logNorm_inv_one]
    change Real.log (A.h z * ((Re.line a₀ t).h z)⁻¹) = _
    rw [Real.log_mul (A.pos z hz).ne' (inv_ne_zero ((Re.line a₀ t).pos z hz).ne'), Real.log_inv]
    ring
  have hdeg : (A.tensor (Re.line a₀ t).inv).a = 0 := by
    change A.a + -(Re.line a₀ t).a = 0
    rw [ha, Re.line_deg, add_neg_cancel]
  have hΦ : ∀ i, IsPotential S.A (S.potT (w i) t) := fun i =>
    (anSys_open_basics D σ S).2.2.2.1 (w i) t h0 h1
  rw [pts_congr P _ fun z hz => (hlog z hz.1).symm,
    ptsIntegral_eq_mInt' hE resBridge Re.R Re.arith (fun j => Re.line_smooth (w j) t h0 h1)
      (isSmoothHerm_inv (isSmoothHerm_tensor hA (isSmoothHerm_inv (Re.line_smooth a₀ t h0 h1))))
      (isSectionOn_inv_one Re.arith.2.1.1 hdeg),
    ← (degreeFormulaInt S.A Re.R.A Re.π Re.holo Re.deg Re.br Re.degree (fun i => S.potT (w i) t) hΦ (fun y => S.ph a₀ y - S.phT a₀ t y)
      (defect_integrable S a₀ h0 h1 _ hΦ)).2]
  refine (mInt_congr_samePot D Re.R.X Re.R.A (Re.π ⁻¹' S.open') _ _ _ _ (preimage_null Re)
    (fun i x _ => line_samePot Re (w i) h0 h1 x (Set.mem_univ x))
    (fun i x _ => isC2At_of_isPotential _ (isPotentialPullback S.A Re.R.A Re.π Re.holo _ (hΦ i)) x)
    fun x hx => ?_).1
  rw [hlog _ (Re.R.mem x x (Re.R.mem_U x)).1, hph x hx, Re.line_eq a₀ t h0 h1 x]
  simp only [Function.comp_apply]
  ring

end Real

end PositivityTheory.Xgn.SmallPotentialLimit

theorem PositivityTheory.Xgn.points_integral_small_limit : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (a₀ : σ) (A : HermLine ι) (w : Fin D → σ), IsSmoothHerm A → A.a = (Re.ref a₀).a → (∀ x, Re.π x ∈ S.open' → Real.log (A.h (Re.R.lift x x)) = Real.log ((Re.ref a₀).h (Re.R.lift x x)) + S.ph a₀ (Re.π x)) → Tendsto (fun t => ptsIntegral P (pot fun j => Re.line (w j) t) (fun z => Real.log (A.h z) - Real.log ((Re.line a₀ t).h z))) (𝓝[>] 0) (𝓝 0) := by
  intro hI K _ ι _ D σ S P Re a₀ A w hA ha hph
  have h := (PositivityTheory.Xgn.SmallPotentialLimit.tendsto_base S hI.convergenceSigned a₀ w).const_mul (Re.deg : ℝ)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (S.reg a₀).1] with t ht
  exact (PositivityTheory.Xgn.SmallPotentialLimit.pts_eq Re hI.resExists a₀ A w hA ha hph ht.1 ht.2).symm
end

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.RealisationRoots

open ReciprocityTheory.AnForm.M

section Gen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

theorem pts_neg_congr (P : Ideal (MRing ι)) {e : ℕ}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g g' : ((Σ k, ι k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = -g' z) :
    ptsIntegral P φ g = -ptsIntegral P φ g' := by
  have key : ∀ Ψ y w, sheetDensity P Ψ φ g y w = -sheetDensity P Ψ φ g' y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · rw [h _ hγ.choose_spec.2.self_of_nhds.2.1, neg_mul]
    · exact neg_zero.symm
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    simp only [key, finsum_neg_distrib, MeasureTheory.integral_neg]
  · exact neg_zero.symm

theorem h_inv_of_deg {G : HermLine ι} (hG : G.a = 0) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    G.h (fun p => c p.1 * z p) = G.h z := by
  rw [G.smul c z hc, hG]
  simp

theorem smooth_log {G : HermLine ι} (hG : IsSmoothHerm G) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.log (G.h z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  ContDiffOn.log hG fun z hz => (G.pos z hz).ne'

theorem continuous_log_lift {e : ℕ} (R : AnLogRes P J e) {G : HermLine ι} (hG : IsSmoothHerm G) (h0 : G.a = 0) :
    Continuous fun x => Real.log (G.h (R.lift x x)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h1 : ContinuousOn (fun y => Real.log (G.h (R.lift x y))) (R.U x) :=
    (smooth_log hG).continuousOn.comp (continuousOn_pi.2 fun p => continuousOn_lift R x p)
      fun y hy => (R.mem x y hy).1
  have hn : R.U x ∈ 𝓝 x := (R.isOpen_U x).mem_nhds (R.mem_U x)
  refine (h1.continuousAt hn).congr ?_
  filter_upwards [hn] with y hy
  obtain ⟨c, hc, hcz⟩ := R.compat x y y ⟨hy, R.mem_U y⟩
  rw [hcz, h_inv_of_deg h0 c _ hc]

theorem add_update (hE : ResExistsStatement) {e : ℕ} (R : AnLogRes P J e) (hP : IsArithVar P (e + 1))
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (j : Fin e) {A B C G : HermLine ι}
    (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (hC : IsSmoothHerm C) (hG : IsSmoothHerm G) (h0 : G.a = 0)
    (h : ∀ z ∈ mcPts P, A.h z * B.h z = C.h z) :
    ptsIntegral P (pot (Function.update L j C)) (fun z => Real.log (G.h z)) =
      ptsIntegral P (pot (Function.update L j A)) (fun z => Real.log (G.h z)) +
        ptsIntegral P (pot (Function.update L j B)) (fun z => Real.log (G.h z)) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by have := j.2; omega⟩
  have hg : (fun z => Real.log (G.h z)) = logNorm G.inv 1 := funext fun z => (logNorm_inv_one G z).symm
  have hL' : ∀ i, IsSmoothHerm (j.removeNth L i) := fun i => hL _
  have key : ∀ E : HermLine ι, IsSmoothHerm E →
      ptsIntegral P (pot (Function.update L j E)) (fun z => Real.log (G.h z)) =
        mInt R.A (Fin.cons (potOf R E) fun i => potOf R (j.removeNth L i))
          (fun x => Real.log (G.h (R.lift x x))) := by
    intro E hEs
    have hU : ∀ i, IsSmoothHerm (Function.update L j E i) := by
      intro i
      by_cases hi : i = j
      · subst hi
        rwa [Function.update_self]
      · rw [Function.update_of_ne hi]
        exact hL i
    rw [hg, ptsIntegral_eq_mInt' hE resBridge R hP hU (isSmoothHerm_inv hG) (isSectionOn_inv_one hP.2.1.1 h0),
      ← potOf_cons, ← mIntSymm R.A
        (fun i => potOf R ((Fin.cons E (j.removeNth L) : Fin (n + 1) → HermLine ι) i)) j.cycleRange]
    have hu : Function.update L j E =
        (Fin.cons E (j.removeNth L) : Fin (n + 1) → HermLine ι) ∘ j.cycleRange := by
      rw [Fin.cons_comp_cycleRange, Fin.insertNth_removeNth]
    rw [hu]
    exact mInt_congr _ (fun _ _ _ => rfl) fun x => logNorm_inv_one _ _
  rw [key C hC, key A hA, key B hB]
  have hΦ : ∀ i, IsPotential R.A (potOf R (j.removeNth L i)) := fun i => isPotential_potOf R (hL' i)
  have hPA := isPotential_potOf R hA
  have hPB := isPotential_potOf R hB
  have hc := continuous_log_lift R hG h0
  rw [← mIntAdd R.A _ _ _ hPA hPB hΦ _ (mIntegrableCont _ _ (fun i => Fin.cases hPA hΦ i) _ hc)
    (mIntegrableCont _ _ (fun i => Fin.cases hPB hΦ i) _ hc)]
  refine mInt_congr _ (locDens_cons_congr _ _ fun j y hy => germ_of_eqOn R (fun x z hz => ?_) j y hy)
    fun _ => rfl
  have hm := R.mem x z hz
  show Real.log (C.h (R.lift x z)) = Real.log (A.h (R.lift x z)) + Real.log (B.h (R.lift x z))
  rw [← h _ hm]
  exact Real.log_mul (A.pos _ hm.1).ne' (B.pos _ hm.1).ne'

theorem triv_update (hE : ResExistsStatement) {e : ℕ} (R : AnLogRes P J e) (hP : IsArithVar P (e + 1))
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (j : Fin e) {G : HermLine ι}
    (hG : IsSmoothHerm G) (h0 : G.a = 0) :
    ptsIntegral P (pot (Function.update L j (GlobalTheory.CompanionTheory.Ar.Top.trivLine ι))) (fun z => Real.log (G.h z)) = 0 := by
  have hs : IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.Top.trivLine ι) := contDiffOn_const
  have := add_update hE R hP hL j hs hs hs hG h0 fun z _ => mul_one _
  linarith

theorem tendsto_words (hE : ResExistsStatement) {e : ℕ} (R : AnLogRes P J e) (hP : IsArithVar P (e + 1))
    {σ ρ : Type} {t₀ : ℝ} (ht₀ : 0 < t₀) (ℓ : σ → ℝ → HermLine ι) (x : ℝ → ρ → HermLine ι) (G : ℝ → HermLine ι)
    (hℓ : ∀ a t, 0 < t → t ≤ t₀ → IsSmoothHerm (ℓ a t)) (hx : ∀ t r, IsSmoothHerm (x t r))
    (hG : ∀ t, IsSmoothHerm (G t)) (h0 : ∀ t, (G t).a = 0)
    (hrel : ∀ r, ∃ a, (∃ b, ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ mcPts P, (x t r).h z * (ℓ a t).h z = (ℓ b t).h z) ∨
      ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ mcPts P, (x t r).h z * (ℓ a t).h z = 1)
    (hw : ∀ w : Fin e → σ, Tendsto (fun t => ptsIntegral P (pot fun j => ℓ (w j) t)
      (fun z => Real.log ((G t).h z))) (𝓝[>] 0) (𝓝 0))
    (s : Finset (Fin e)) : ∀ L : ℝ → Fin e → HermLine ι, (∀ j ∈ s, ∃ r, ∀ t, L t j = x t r) →
      (∀ j ∉ s, ∃ a, ∀ t, L t j = ℓ a t) →
      Tendsto (fun t => ptsIntegral P (pot (L t)) (fun z => Real.log ((G t).h z))) (𝓝[>] 0) (𝓝 0) := by
  induction s using Finset.induction_on with
  | empty =>
    intro L _ h2
    choose w hw' using fun j => h2 j (Finset.notMem_empty j)
    have : L = fun t j => ℓ (w j) t := funext fun t => funext fun j => hw' j t
    subst this
    exact hw w
  | insert j s hj ih =>
    intro L h1 h2
    obtain ⟨r, hr⟩ := h1 j (Finset.mem_insert_self j s)
    have hup : ∀ a, Tendsto (fun t => ptsIntegral P (pot (Function.update (L t) j (ℓ a t)))
        (fun z => Real.log ((G t).h z))) (𝓝[>] 0) (𝓝 0) := by
      intro a
      refine ih (fun t => Function.update (L t) j (ℓ a t)) (fun i hi => ?_) fun i hi => ?_
      · have hij : i ≠ j := fun h => hj (h ▸ hi)
        simp only [Function.update_of_ne hij]
        exact h1 i (Finset.mem_insert_of_mem hi)
      · by_cases hij : i = j
        · subst hij
          exact ⟨a, fun t => Function.update_self _ _ _⟩
        · simp only [Function.update_of_ne hij]
          exact h2 i fun h => (Finset.mem_insert.1 h).elim hij hi
    have hLs : ∀ t, 0 < t → t ≤ t₀ → ∀ i, IsSmoothHerm (L t i) := by
      intro t a b i
      by_cases hi : i ∈ insert j s
      · obtain ⟨r, hr⟩ := h1 i hi
        rw [hr]
        exact hx t r
      · obtain ⟨c, hc⟩ := h2 i hi
        rw [hc]
        exact hℓ c t a b
    have hself : ∀ t, Function.update (L t) j (x t r) = L t := fun t => by
      rw [← hr t, Function.update_eq_self]
    obtain ⟨a, ⟨b, hb⟩ | hb⟩ := hrel r
    · have h3 := (hup b).sub (hup a)
      rw [sub_zero] at h3
      refine h3.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht
      rw [add_update hE R hP (hLs t ht.1 ht.2) j (hx t r) (hℓ a t ht.1 ht.2) (hℓ b t ht.1 ht.2) (hG t) (h0 t)
        (hb t ht.1 ht.2), hself, add_sub_cancel_right]
    · have h3 := (hup a).neg
      rw [neg_zero] at h3
      refine h3.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht
      have h4 := add_update hE R hP (hLs t ht.1 ht.2) j (C := GlobalTheory.CompanionTheory.Ar.Top.trivLine ι) (hx t r)
        (hℓ a t ht.1 ht.2) contDiffOn_const (hG t) (h0 t) (hb t ht.1 ht.2)
      rw [triv_update hE R hP (hLs t ht.1 ht.2) j (hG t) (h0 t), hself] at h4
      linarith

theorem tendsto_congr_pts (P : Ideal (MRing ι)) {e : ℕ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (φ : ℝ → Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g g' : ℝ → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ mcPts P, g t z = -g' t z)
    (h' : Tendsto (fun t => ptsIntegral P (φ t) (g' t)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t => ptsIntegral P (φ t) (g t)) (𝓝[>] 0) (𝓝 0) := by
  have h3 := h'.neg
  rw [neg_zero] at h3
  refine h3.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht
  exact (pts_neg_congr P _ (h t ht.1 ht.2)).symm

end Gen

theorem telescope {G : Type} [CommMonoid G] {N : ℕ} (x y : Fin N → G)
    (h : ∀ i : Fin N, x i * y i = if h : 0 < (i : ℕ) then y ⟨i - 1, by omega⟩ else 1)
    (i₀ : Fin N) (hi : (i₀ : ℕ) + 1 = N) : (∏ i, x i) * y i₀ = 1 := by
  induction N with
  | zero => exact i₀.elim0
  | succ n ih =>
    obtain rfl : i₀ = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [Fin.prod_univ_castSucc, mul_assoc, h]
    split_ifs with hn
    · simp only [Fin.val_last] at hn
      exact ih (fun i => x i.castSucc) (fun i => y i.castSucc) (fun i => h i.castSucc) ⟨n - 1, by omega⟩
        (by simp only []; omega)
    · simp only [Fin.val_last] at hn
      obtain rfl : n = 0 := by omega
      simp

theorem telescope_add {G : Type} [AddCommMonoid G] {N : ℕ} (x y : Fin N → G)
    (h : ∀ i : Fin N, x i + y i = if h : 0 < (i : ℕ) then y ⟨i - 1, by omega⟩ else 0)
    (i₀ : Fin N) (hi : (i₀ : ℕ) + 1 = N) : (∑ i, x i) + y i₀ = 0 := by
  induction N with
  | zero => exact i₀.elim0
  | succ n ih =>
    obtain rfl : i₀ = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [Fin.sum_univ_castSucc, add_assoc, h]
    split_ifs with hn
    · simp only [Fin.val_last] at hn
      exact ih (fun i => x i.castSucc) (fun i => y i.castSucc) (fun i => h i.castSucc) ⟨n - 1, by omega⟩
        (by simp only []; omega)
    · simp only [Fin.val_last] at hn
      obtain rfl : n = 0 := by omega
      simp

theorem mono_roots {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (m : Ψ × Fin N →₀ ℕ)
    (d : ℕ) (hm : m.degree = d) (j : Fin d) :
    ∃ r, ∀ t, GlobalTheory.CompanionTheory.Ar.Top.monoLines (M.line t) (m.mapDomain some) d j = M.x t r := by
  have hl : (j : ℕ) < (Finsupp.toMultiset (m.mapDomain (some : _ → Option (Ψ × Fin N)))).toList.length := by
    rw [Multiset.length_toList, ← Finsupp.toMultiset_map, Multiset.card_map, Finsupp.card_toMultiset]
    exact lt_of_lt_of_eq j.2 hm.symm
  have hall : ∀ o ∈ (Finsupp.toMultiset (m.mapDomain (some : _ → Option (Ψ × Fin N)))).toList,
      ∃ r, some r = o := by
    intro o ho
    rw [Multiset.mem_toList, ← Finsupp.toMultiset_map] at ho
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.1 ho
    exact ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hall _ (List.get_mem _ ⟨j, hl⟩)
  refine ⟨r, fun t => ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Top.monoLines
  rw [dite_eq_left hl, ← hr]
  rfl

end PositivityTheory.Xgn.RealisationRoots

open PositivityTheory.Xgn.RealisationRoots in
theorem PositivityTheory.Xgn.root_of_realisation_telescoping : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (S : GlobalTheory.CompanionTheory.Ar.PB.AnSys (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) (Option (Ψ × Fin N))) (Re : GlobalTheory.CompanionTheory.Ar.PB.Realis S M.P) (τ : Ψ) (i₀ : Fin N) (F : Type) [Field F] [NumberField F] (φ : F →+* M.Ω) (A : HermLine M.ι) (Sf : FlatHerm M.y φ A), OverInt M.y φ → IsSmoothHerm A → (i₀ : ℕ) + 1 = N → 0 < S.t₀ → A.a = ∑ i, M.xdeg (τ, i) → (∀ (σ : Ψ) (i : Fin N), M.xdeg (σ, i) + (Re.ref (some (σ, i))).a = if h : 0 < (i : ℕ) then (Re.ref (some (σ, ⟨i - 1, by omega⟩))).a else 0) → (∀ t, 0 < t → t ≤ S.t₀ → ∀ (σ : Ψ) (i : Fin N), ∀ z ∈ mcPts M.P, (M.x t (σ, i)).h z * (Re.line (some (σ, i)) t).h z = if h : 0 < (i : ℕ) then (Re.line (some (σ, ⟨i - 1, by omega⟩)) t).h z else 1) → (∀ x, Re.π x ∈ S.open' → -Real.log (A.h (Re.R.lift x x)) = Real.log ((Re.ref (some (τ, i₀))).h (Re.R.lift x x)) + S.ph (some (τ, i₀)) (Re.π x)) → ∃ R : RootFlat M τ, R.ht = Sf.ht := by
  intro hI Ψ _ _ N M S Re τ i₀ F _ _ φ A Sf hO hA hi ht₀ hdeg hxd hxh hph
  let T : ℝ → HermLine M.ι := fun t => GlobalTheory.CompanionTheory.Ar.PB.combLine (fun i : Fin N => M.x t (τ, i)) fun _ => 1
  have hTh : ∀ t z, (T t).h z = ∏ i, (M.x t (τ, i)).h z := fun t z => by
    simp only [T, GlobalTheory.CompanionTheory.Ar.PB.combLine_h, zpow_one]
  have hTs : ∀ t, IsSmoothHerm (T t) := fun t => by
    unfold IsSmoothHerm
    rw [show (T t).h = fun z => ∏ i, (M.x t (τ, i)).h z from funext (hTh t)]
    exact contDiffOn_prod fun i _ => M.x_smooth t (τ, i)
  have hTa : ∀ t, (T t).a = A.a := fun t => by
    funext k
    simp only [T, GlobalTheory.CompanionTheory.Ar.PB.combLine_a, one_mul, hdeg, Finset.sum_apply, M.x_deg]
  let G : ℝ → HermLine M.ι := fun t => A.tensor (T t).inv
  have hGh : ∀ t z, (G t).h z = A.h z * ((T t).h z)⁻¹ := fun t z => rfl
  have hGs : ∀ t, IsSmoothHerm (G t) := fun t => isSmoothHerm_tensor hA (isSmoothHerm_inv (hTs t))
  have hG0 : ∀ t, (G t).a = 0 := fun t => by
    change A.a + -(T t).a = 0
    rw [hTa, add_neg_cancel]
  have hinv : A.inv.a = (Re.ref (some (τ, i₀))).a := by
    have := telescope_add (fun i => M.xdeg (τ, i)) (fun i => (Re.ref (some (τ, i))).a) (hxd τ) i₀ hi
    change -A.a = _
    rw [hdeg]
    exact neg_eq_of_add_eq_zero_right this
  have hw : ∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) → Option (Ψ × Fin N),
      Tendsto (fun t => ptsIntegral M.P (pot fun j => Re.line (w j) t)
      (fun z => Real.log ((G t).h z))) (𝓝[>] 0) (𝓝 0) := by
    intro w
    refine tendsto_congr_pts M.P ht₀ _ (fun t h0 h1 z hz => ?_)
      (PositivityTheory.Xgn.points_integral_small_limit hI M.K M.ι _ _ S M.P Re (some (τ, i₀)) A.inv w (isSmoothHerm_inv hA) hinv fun x hx => by
        rw [← hph x hx]
        exact Real.log_inv _)
    have h2 := telescope (fun i => (M.x t (τ, i)).h z) (fun i => (Re.line (some (τ, i)) t).h z)
      (fun i => hxh t h0 h1 τ i z hz) i₀ hi
    rw [← hTh] at h2
    rw [hGh, inv_eq_of_mul_eq_one_right h2,
      Real.log_mul (A.pos z hz.1).ne' ((Re.line (some (τ, i₀)) t).pos z hz.1).ne']
    change _ = -(Real.log (A.h z)⁻¹ - _)
    rw [Real.log_inv]
    ring
  refine ⟨{ F := F, φ := φ, overInt := hO, A := A, A_smooth := hA, S := Sf, deg := hdeg.symm
            v := fun t z => Real.log ((G t).h z)
            v_inv := fun t c z hc => by rw [h_inv_of_deg (hG0 t) c z hc]
            v_smooth := fun t => smooth_log (hGs t)
            prod := fun t _ z hz => ?_
            small := fun m hm => ?_ }, rfl⟩
  · rw [Real.exp_neg, Real.exp_log ((G t).pos z hz.1), hGh, ← hTh, mul_inv, inv_inv,
      mul_inv_cancel_left₀ (A.pos z hz.1).ne']
  · refine tendsto_words hI.resExists Re.R Re.arith ht₀ Re.line M.x G Re.line_smooth M.x_smooth hGs hG0
      (fun r => ⟨some r, ?_⟩) hw Finset.univ _ (fun j _ => mono_roots M m _ hm j)
      fun j hj => (hj (Finset.mem_univ j)).elim
    by_cases h : 0 < (r.2 : ℕ)
    · exact Or.inl ⟨_, fun t h0 h1 z hz => by
        have := hxh t h0 h1 r.1 r.2 z hz
        rwa [dite_eq_left h] at this⟩
    · exact Or.inr fun t h0 h1 z hz => by
        have := hxh t h0 h1 r.1 r.2 z hz
        rwa [dite_eq_right h] at this
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermRootLineDegree
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_rootFlat_of_realis : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (S : GlobalTheory.CompanionTheory.Ar.PB.AnSys (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) (Option (Ψ × Fin N))) (Re : GlobalTheory.CompanionTheory.Ar.PB.Realis S M.P) (τ : Ψ) (i₀ : Fin N) (F : Type) [Field F] [NumberField F] (φ : F →+* M.Ω) (A : HermLine M.ι) (Sf : FlatHerm M.y φ A), OverInt M.y φ → IsSmoothHerm A → (i₀ : ℕ) + 1 = N → 0 < S.t₀ → A.a = ∑ i, M.xdeg (τ, i) → (∀ (σ : Ψ) (i : Fin N), M.xdeg (σ, i) + (Re.ref (some (σ, i))).a = if h : 0 < (i : ℕ) then (Re.ref (some (σ, ⟨i - 1, by omega⟩))).a else 0) → (∀ t, 0 < t → t ≤ S.t₀ → ∀ (σ : Ψ) (i : Fin N), ∀ z ∈ mcPts M.P, (M.x t (σ, i)).h z * (Re.line (some (σ, i)) t).h z = if h : 0 < (i : ℕ) then (Re.line (some (σ, ⟨i - 1, by omega⟩)) t).h z else 1) → (∀ x, Re.π x ∈ S.open' → -Real.log (A.h (Re.R.lift x x)) = Real.log ((Re.ref (some (τ, i₀))).h (Re.R.lift x x)) + S.ph (some (τ, i₀)) (Re.π x)) → ∃ R : RootFlat M τ, R.ht = Sf.ht :=
  PositivityTheory.Xgn.root_of_realisation_telescoping

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermRootLineDegreeStatement
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_herm_root_line_degree : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (S : GlobalTheory.CompanionTheory.Ar.PB.AnSys (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) (Option (Ψ × Fin N))) (Re : GlobalTheory.CompanionTheory.Ar.PB.Realis S M.P) (τ : Ψ) (i₀ : Fin N) (F : Type) [Field F] [NumberField F] (φ : F →+* M.Ω) (A : HermLine M.ι) (Sf : FlatHerm M.y φ A), OverInt M.y φ → IsSmoothHerm A → (i₀ : ℕ) + 1 = N → 0 < S.t₀ → A.a = ∑ i, M.xdeg (τ, i) → (∀ (σ : Ψ) (i : Fin N), M.xdeg (σ, i) + (Re.ref (some (σ, i))).a = if h : 0 < (i : ℕ) then (Re.ref (some (σ, ⟨i - 1, by omega⟩))).a else 0) → (∀ t, 0 < t → t ≤ S.t₀ → ∀ (σ : Ψ) (i : Fin N), ∀ z ∈ mcPts M.P, (M.x t (σ, i)).h z * (Re.line (some (σ, i)) t).h z = if h : 0 < (i : ℕ) then (Re.line (some (σ, ⟨i - 1, by omega⟩)) t).h z else 1) → (∀ x, Re.π x ∈ S.open' → -Real.log (A.h (Re.R.lift x x)) = Real.log ((Re.ref (some (τ, i₀))).h (Re.R.lift x x)) + S.ph (some (τ, i₀)) (Re.π x)) → ∃ R : RootFlat M τ, R.ht = Sf.ht := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_rootFlat_of_realis | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_rootFlat_of_realis | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_rootFlat_of_realis <;> assumption)
end
