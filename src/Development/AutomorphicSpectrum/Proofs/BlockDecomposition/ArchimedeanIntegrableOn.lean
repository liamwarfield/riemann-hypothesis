module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicLiftGivesHolomorphicSection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypersurfaceComplexPointsMeasurableNull

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureZeroSetAvoidedByHolomorphicMap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureZeroSetAvoidedByHolomorphicMap
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

section Abstract
open Set
open scoped ENNReal
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.FinChart

namespace GlobalTheory.CompanionTheory.ArchDom

theorem measurableSet_inter_preimage {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {f : α → β} {s : Set α}
    {t : Set β} (hf : ContinuousOn f s) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∩ f ⁻¹' t) := by
  have hm : Measurable (s.restrict f) := (continuousOn_iff_continuous_restrict.1 hf).measurable
  have := hs.subtype_image (hm ht)
  convert this using 1
  ext v
  exact ⟨fun hv => ⟨⟨v, hv.1⟩, hv.2, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩⟩

theorem chartMeas_le_sum {D n : ℕ} {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (e : OpenPartialHomeomorph Y (V D)) (ρ : Y → ℝ≥0∞) {Z : Set Y}
    (hZ : MeasurableSet Z) (hnull : volume (e.target ∩ e.symm ⁻¹' Z) = 0)
    (P : Fin n → (Fin D → ℂ) → Y) (K : Fin n → Set (Fin D → ℂ)) (hK : ∀ j, MeasurableSet (K j))
    (hP : ∀ j, ContinuousOn (P j) (K j)) (w : Fin n → (Fin D → ℂ) → ℝ≥0∞)
    (hcov : ∀ y ∈ e.source, y ∉ Z → ∃ j, ∃ u ∈ K j, P j u = y)
    (hinj : ∀ j, ∀ u ∈ K j, ∀ u' ∈ K j, P j u ∉ Z → P j u = P j u' → u = u')
    (hdet : ∀ j, ∀ u ∈ K j, P j u ∈ e.source → P j u ∉ Z →
      DifferentiableAt ℝ ((toV D).symm ∘ e ∘ P j) u ∧
      ENNReal.ofReal |(fderiv ℝ ((toV D).symm ∘ e ∘ P j) u).det| * ρ (P j u) ≤ w j u) :
    GlobalTheory.ChartGlue.chartMeas e ρ ≤
      ∑ j, Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) := by
  refine Measure.le_iff.2 fun S hS => ?_
  have hsrc := e.open_source.measurableSet
  let T : Fin n → Set (Fin D → ℂ) := fun j => K j ∩ P j ⁻¹' ((e.source ∩ S) \ Z)
  let G : Fin n → (Fin D → ℂ) → (Fin D → ℂ) := fun j => (toV D).symm ∘ e ∘ P j
  have hT : ∀ j, MeasurableSet (T j) := fun j =>
    measurableSet_inter_preimage (hP j) (hK j) ((hsrc.inter hS).diff hZ)
  have hM : ∀ j, MeasurableSet (K j \ P j ⁻¹' Z) := fun j =>
    measurableSet_inter_preimage (hP j) (hK j) hZ.compl
  have hcover : e '' (e.source ∩ S) ⊆
      (e.target ∩ e.symm ⁻¹' Z) ∪ ⋃ j, toV D '' (G j '' T j) := by
    rintro _ ⟨y, ⟨hy, hyS⟩, rfl⟩
    by_cases hyZ : y ∈ Z
    · exact Or.inl (GlobalTheory.ChartGlue.mem_over e hy hyZ)
    · obtain ⟨j, u, hu, rfl⟩ := hcov y hy hyZ
      refine Or.inr (mem_iUnion.2 ⟨j, _, ⟨u, ⟨hu, ⟨⟨hy, hyS⟩, hyZ⟩⟩, rfl⟩, ?_⟩)
      simp [G]
  have hterm : ∀ j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) ≤
      Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) S := by
    intro j
    have hinjG : InjOn (G j) (T j) := by
      rintro u ⟨hu, hR⟩ u' ⟨hu', hR'⟩ h
      have h1 : e (P j u) = e (P j u') := (toV D).symm.injective h
      exact hinj j u hu u' hu' hR.2 (e.injOn hR.1.1 hR'.1.1 h1)
    have hder : ∀ u ∈ T j, HasFDerivWithinAt (G j) (fderiv ℝ (G j) u) (T j) u := fun u hu =>
      (hdet j u hu.1 hu.2.1.1 hu.2.2).1.hasFDerivAt.hasFDerivWithinAt
    have hae : AEMeasurable (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) :=
      (((hP j).mono diff_subset).aemeasurable (hM j)).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [← measurePreserving_toV.setLIntegral_comp_emb (toV D).toHomeomorph.measurableEmbedding,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hT j) hder hinjG,
      Measure.map_apply_of_aemeasurable hae hS, withDensity_apply',
      Measure.restrict_restrict' (hM j)]
    refine (setLIntegral_mono' (hT j) fun u hu => ?_).trans (lintegral_mono_set ?_)
    · have hv : toV D (G j u) = e (P j u) := (toV D).apply_symm_apply _
      have := (hdet j u hu.1 hu.2.1.1 hu.2.2).2
      rw [hv, e.left_inv hu.2.1.1]
      exact this
    · rintro u ⟨hu, hR⟩
      exact ⟨hR.1.2, hu, hR.2⟩
  calc GlobalTheory.ChartGlue.chartMeas e ρ S = ∫⁻ v in e '' (e.source ∩ S), ρ (e.symm v) :=
        GlobalTheory.ChartGlue.chartMeas_apply e ρ hS
    _ ≤ ∫⁻ v in (e.target ∩ e.symm ⁻¹' Z) ∪ ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ v in e.target ∩ e.symm ⁻¹' Z, ρ (e.symm v)) +
          ∫⁻ v in ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) := lintegral_union_le _ _ _
    _ = ∫⁻ v in ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) := by
        rw [setLIntegral_measure_zero _ _ hnull, zero_add]
    _ ≤ ∑' j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) := lintegral_iUnion_le _ _
    _ = ∑ j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) := tsum_fintype _
    _ ≤ ∑ j, Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) S :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by rw [Measure.finsetSum_apply]

theorem ofReal_abs_norm_mul_le (d : ℂ) (x : ℝ) (ε : ℤˣ) :
    ENNReal.ofReal |Algebra.norm ℝ d| * ENNReal.ofReal ((ε : ℤ) * x) ≤
      ENNReal.ofReal |‖d‖ ^ 2 * x| := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity), abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖d‖ ^ 2)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using le_abs_self x
  · simpa using neg_le_abs x

end GlobalTheory.CompanionTheory.ArchDom
end Abstract


open GlobalTheory.FinChart in
theorem GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) →
    (∀ y, y ∉ Z → ∃ x, F x = y) → (∀ x x', F x ∉ Z → F x = F x' → x = x') →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (ε : ℤˣ) (K : Fin A.n → Set (Fin D → ℂ)),
    (∀ j, IsCompact (K j)) → (∀ j, K j ⊆ (A.chart j).target) →
    (∀ x, ∃ j, ∃ u ∈ K j, (A.chart j).symm u = x) →
    φ.chernPart D ε ≤ ∑ j, Measure.map (F ∘ (A.chart j).symm)
      ((volume.restrict (K j \ (F ∘ (A.chart j).symm) ⁻¹' Z)).withDensity fun u =>
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|) := by
  intro k _ X q σ D T _ A F hF hol Z hZ hnull hsurj hinj B φ hφ ε K hK hKt hKc
  refine iSup_le fun c => ?_
  refine GlobalTheory.CompanionTheory.ArchDom.chartMeas_le_sum c.e _ hZ (hnull c) (fun j => F ∘ (A.chart j).symm) K
    (fun j => (hK j).measurableSet)
    (fun j => hF.comp_continuousOn ((A.chart j).continuousOn_symm.mono (hKt j))) _ ?_ ?_ ?_
  · intro y _ hyZ
    obtain ⟨x, rfl⟩ := hsurj y hyZ
    obtain ⟨j, u, hu, rfl⟩ := hKc x
    exact ⟨j, u, hu, rfl⟩
  · intro j u hu u' hu' hZu h
    exact (A.chart j).symm.injOn (hKt j hu) (hKt j hu') (hinj _ _ hZu h)
  · intro j u hu hsrc _
    obtain ⟨han, hd⟩ := GlobalTheory.T.smooth_weight_pullback_chart_formula A F hF hol φ hφ c j u (hKt j hu) hsrc
    have hG : (toV D).symm ∘ c.e ∘ (F ∘ (A.chart j).symm) =
        c.finChart ∘ F ∘ (A.chart j).symm := rfl
    rw [hG]
    have hdiff := han.differentiableAt
    refine ⟨hdiff.restrictScalars ℝ, ?_⟩
    have hdet : (fderiv ℝ (c.finChart ∘ F ∘ (A.chart j).symm) u).det = Algebra.norm ℝ
        (LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) := by
      rw [hdiff.fderiv_restrictScalars ℝ]
      exact LinearMap.det_restrictScalars
        (f := (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))
    rw [hdet, hd]
    exact GlobalTheory.CompanionTheory.ArchDom.ofReal_abs_norm_mul_le _ _ ε
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureZeroSetAvoidedByHolomorphicMapStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_zero_set_avoided_by_holomorphic_map : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) →
    (∀ y, y ∉ Z → ∃ x, F x = y) → (∀ x x', F x ∉ Z → F x = F x' → x = x') →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (ε : ℤˣ) (K : Fin A.n → Set (Fin D → ℂ)),
    (∀ j, IsCompact (K j)) → (∀ j, K j ⊆ (A.chart j).target) →
    (∀ x, ∃ j, ∃ u ∈ K j, (A.chart j).symm u = x) →
    φ.chernPart D ε ≤ ∑ j, Measure.map (F ∘ (A.chart j).symm)
      ((volume.restrict (K j \ (F ∘ (A.chart j).symm) ⁻¹' Z)).withDensity fun u =>
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|) := by
  first | exact @GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map | exact GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map | (intros; apply GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightsIntegralPullbackFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightsIntegralPullbackFormula
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
open Set Filter Topology

namespace GlobalTheory.CompanionTheory.MixZ

theorem lintegral_logNorm_locDens_lt_top : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B C : LB X} (φ : GlobalTheory.Weight q σ B) (_ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (_ : ψ.IsCInf)
      (g : GlobalTheory.CxPts q σ → ℝ) (S Z : Set (GlobalTheory.CxPts q σ)) {N : ℕ} (W : Fin N → X.Opens) (b : Fin N → C.ι)
      (a d : ∀ l, Γ(X, W l)),
    (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) → (∀ l, W l ≤ C.U (b l)) →
    (∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ S → y ∉ Z →
      g y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2) →
    IsOpen S → ContinuousOn g S → MeasurableSet Z →
    ∀ (j : Fin A.n) (K : Set (Fin D → ℂ)), K ⊆ (A.chart j).target → IsCompact K →
      ∫⁻ u in K \ (F ∘ (A.chart j).symm) ⁻¹' Z, S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤ := by
  intro k _ X q σ D T _ A F hF hol B C φ hφ ψ hψ g S Z N W b a d hcov hWb hg hSo hgc hZ j K hKt hKc
  have hGc : ContinuousOn (F ∘ (A.chart j).symm) (A.chart j).target :=
    hF.comp_continuousOn (A.chart j).continuousOn_symm
  have hdc : ContinuousOn (locDens A (fun _ => φ.locPot.pullback F hF) j) (A.chart j).target :=
    locDensCont A _ (fun _ => isPotential_pullback_locPot A F hF hol φ hφ) j
  refine hKc.induction_on (p := fun s => ∫⁻ u in s \ (F ∘ (A.chart j).symm) ⁻¹' Z,
      S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤) ?_ ?_ ?_ ?_
  · simp
  · intro s t hst ht
    exact (lintegral_mono_set (diff_subset_diff_left hst)).trans_lt ht
  · intro s t hs ht
    rw [union_diff_distrib]
    exact (lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)
  intro u0 hu0
  obtain ⟨l, hl⟩ := hcov (F ((A.chart j).symm u0))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ (W l))) :=
    (A.chart j).isOpen_inter_preimage_symm ((isOpen_ptsIn _).preimage hF)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 ⟨hKt hu0, hl⟩
  set V := (A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ (W l)) with hV
  set Bl := Metric.closedBall u0 (r / 2) with hBl
  have hBV : Bl ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact Bl := isCompact_closedBall _ _
  have hBm : MeasurableSet Bl := Metric.isClosed_closedBall.measurableSet
  have hBt : Bl ⊆ (A.chart j).target := hBV.trans inter_subset_left
  refine ⟨Bl, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  have hla : IntegrableOn (fun u => Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖) Bl :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt D V (fun u => ev q σ (W l) (a l) (F ((A.chart j).symm u))) hO
      (fun u hu => hol (W l) (a l) j u hu)).integrableOn_compact_subset hBV hBc
  have hld : IntegrableOn (fun u => Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖) Bl :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt D V (fun u => ev q σ (W l) (d l) (F ((A.chart j).symm u))) hO
      (fun u hu => hol (W l) (d l) j u hu)).integrableOn_compact_subset hBV hBc
  have hψc : ContinuousOn (fun u => ψ.φ (b l) (F ((A.chart j).symm u))) Bl := by
    intro u hu
    have hc : ContinuousAt (ψ.φ (b l)) (F ((A.chart j).symm u)) :=
      (hψ (b l) _ (ptsIn_mono (hWb l) (hBV hu).2)).continuousAt
    exact ContinuousAt.comp_continuousWithinAt (f := F ∘ (A.chart j).symm) hc
      ((hGc u (hBt hu)).mono hBt)
  have hlψ : IntegrableOn (fun u => |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) Bl :=
    (hψc.abs.div_const 2).integrableOn_compact hBc
  have hh : IntegrableOn (fun u => |Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
      |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
      |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) Bl :=
    (hla.abs.add hld.abs).add hlψ
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn (hdc.mono hBt)
  have hYm : MeasurableSet (Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z) := by
    have hc : Continuous (fun u : Bl => (F ∘ (A.chart j).symm) u.1) :=
      continuousOn_iff_continuous_restrict.1 (hGc.mono hBt)
    have h1 : MeasurableSet (Subtype.val '' ((fun u : Bl => (F ∘ (A.chart j).symm) u.1) ⁻¹' Z)) :=
      hBm.subtype_image (hc.measurable hZ)
    have h2 : Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z =
        Bl \ (Subtype.val '' ((fun u : Bl => (F ∘ (A.chart j).symm) u.1) ⁻¹' Z)) := by
      ext u
      constructor
      · rintro ⟨hu, hn⟩
        refine ⟨hu, ?_⟩
        rintro ⟨v, hv, rfl⟩
        exact hn hv
      · rintro ⟨hu, hn⟩
        exact ⟨hu, fun hz => hn ⟨⟨u, hu⟩, hz, rfl⟩⟩
    rw [h2]
    exact hBm.diff h1
  have hpt : ∀ u ∈ Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
      S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| ≤
      ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
        |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
        |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M := by
    rintro u ⟨huB, huZ⟩
    by_cases hS : F ((A.chart j).symm u) ∈ S
    · rw [indicator_of_mem hS]
      refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal ?_)
      · rw [← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hg l _ (hBV huB).2 hS huZ, Real.norm_eq_abs]
        have h1 := abs_sub (Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖ -
          Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖)
          (ψ.φ (b l) (F ((A.chart j).symm u)) / 2)
        have h2 := abs_sub (Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖)
          (Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖)
        rw [abs_div, abs_two] at h1
        linarith
      · simpa using hM u huB
    · rw [indicator_of_notMem hS, zero_mul]
      exact zero_le
  calc ∫⁻ u in Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
        S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
          ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|
      ≤ ∫⁻ u in Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M :=
        setLIntegral_mono' hYm hpt
    _ ≤ ∫⁻ u in Bl,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M :=
        lintegral_mono_set diff_subset
    _ = (∫⁻ u in Bl,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2)) * ENNReal.ofReal M :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top hh.lintegral_lt_top ENNReal.ofReal_lt_top

end GlobalTheory.CompanionTheory.MixZ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightsIntegralPullbackFormulaStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_indicator_mul_locDens_pullback_lt_top : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B C : LB X} (φ : GlobalTheory.Weight q σ B) (_ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (_ : ψ.IsCInf)
      (g : GlobalTheory.CxPts q σ → ℝ) (S Z : Set (GlobalTheory.CxPts q σ)) {N : ℕ} (W : Fin N → X.Opens) (b : Fin N → C.ι)
      (a d : ∀ l, Γ(X, W l)),
    (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) → (∀ l, W l ≤ C.U (b l)) →
    (∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ S → y ∉ Z →
      g y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2) →
    IsOpen S → ContinuousOn g S → MeasurableSet Z →
    ∀ (j : Fin A.n) (K : Set (Fin D → ℂ)), K ⊆ (A.chart j).target → IsCompact K →
      ∫⁻ u in K \ (F ∘ (A.chart j).symm) ⁻¹' Z, S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.lintegral_logNorm_locDens_lt_top | exact GlobalTheory.CompanionTheory.MixZ.lintegral_logNorm_locDens_lt_top | (intros; apply GlobalTheory.CompanionTheory.MixZ.lintegral_logNorm_locDens_lt_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogNormContinuousOffDivisor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogNormContinuousOffDivisor
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchInt

theorem continuousOn_logNorm_offSupp {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {q : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X} (ψ : GlobalTheory.Weight q σ L) (hψ : ψ.IsCInf)
    {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ContinuousOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) := by
  intro y hy
  obtain ⟨i, hi⟩ := GlobalTheory.CxPts.exists_mem_ptsIn (p := q) (σ := σ) ψ.isLB.cover y
  have hu : GlobalTheory.Cartier.UnitAt (GlobalTheory.Cartier.under y) ((r i : X.functionField)) :=
    GlobalTheory.Cartier.IsRatSec.unitAt ψ.isLB hr hy hi
  obtain ⟨V, hyV, hV⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hu
  have hgV : genericPoint X ∈ V := GlobalTheory.Cartier.gen_mem hyV
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hV
  have hyV' : y ∈ GlobalTheory.CxPts.ptsIn q σ V := GlobalTheory.CxPts.mem_ptsIn.2 hyV
  have hNo : IsOpen (GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr)) :=
    ((GlobalTheory.CxPts.isOpen_ptsIn V).inter (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
      (GlobalTheory.Cartier.isOpen_offSupp _)
  have hyN : y ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr) := ⟨⟨hyV', hi⟩, hy⟩
  have heq : ∀ z ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr),
      Real.log ‖GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2 =
        GlobalTheory.Cartier.logNorm ψ r z := by
    rintro z ⟨⟨hzV, hzi⟩, hz⟩
    rw [GlobalTheory.Cartier.logNorm_eq ψ hr hz hzi, ← ha hgV, GlobalTheory.Cartier.ratVal_fnOf hzV]
  have hne : GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) y ≠ 0 := by
    rw [← GlobalTheory.Cartier.ratVal_fnOf hyV' hgV, ha hgV]
    exact GlobalTheory.Cartier.ratVal_ne_zero hu
  have hev : ContinuousAt (GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V))) y :=
    (GlobalTheory.CxPts.continuousOn_ev _).continuousAt ((GlobalTheory.CxPts.isOpen_ptsIn V).mem_nhds hyV')
  have hφ : ContinuousAt (ψ.φ i) y := (hψ i y hi).continuousAt
  have hg : ContinuousAt (fun z => Real.log ‖GlobalTheory.CxPts.ev q σ V
      (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2) y :=
    (hev.norm.log (norm_ne_zero_iff.2 hne)).sub (hφ.div_const 2)
  exact (hg.congr (Filter.eventuallyEq_of_mem (hNo.mem_nhds hyN) heq)).continuousWithinAt

end GlobalTheory.CompanionTheory.MixZ.ArchInt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogNormContinuousOffDivisorStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_continuous_off_divisor : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L), ψ.IsCInf → ∀ {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r),
    ContinuousOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchInt.continuousOn_logNorm_offSupp | exact GlobalTheory.CompanionTheory.MixZ.ArchInt.continuousOn_logNorm_offSupp | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchInt.continuousOn_logNorm_offSupp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionFiniteOpenCover
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionFiniteOpenCover
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchRep

theorem exists_local_quot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L) (r : L.ι → X.functionFieldˣ) (y : GlobalTheory.CxPts q σ) :
    ∃ (W : X.Opens) (b : L.ι) (a d : Γ(X, W)) (h : genericPoint X ∈ W),
      y ∈ ptsIn q σ W ∧ W ≤ L.U b ∧ fnOf W h d ≠ 0 ∧
        (r b : X.functionField) * fnOf W h d = fnOf W h a := by
  have hb := mem_pick ψ.isLB y
  obtain ⟨W, hW, hyW, hWb⟩ := exists_isAffineOpen_mem_and_subset (mem_ptsIn.1 hb)
  have hg : genericPoint X ∈ W := gen_mem hyW
  haveI : Nonempty W := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  obtain ⟨a, d, hd, e⟩ := IsFractionRing.div_surjective (A := Γ(X, W)) (r (pick ψ.isLB y) : X.functionField)
  have hd0 : fnOf W hg d ≠ 0 := by
    have : algebraMap Γ(X, W) X.functionField d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    exact this
  refine ⟨W, pick ψ.isLB y, a, d, hg, mem_ptsIn.2 hyW, hWb, hd0, ?_⟩
  rw [← e]
  change algebraMap Γ(X, W) X.functionField a / algebraMap Γ(X, W) X.functionField d * fnOf W hg d = _
  have e' : algebraMap Γ(X, W) X.functionField d = fnOf W hg d := rfl
  have e'' : algebraMap Γ(X, W) X.functionField a = fnOf W hg a := rfl
  rw [e', e'', div_mul_cancel₀ _ hd0]

theorem logNorm_of_quot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    {W : X.Opens} {b : L.ι} {a d : Γ(X, W)} {h : genericPoint X ∈ W} (hWb : W ≤ L.U b)
    (e : (r b : X.functionField) * fnOf W h d = fnOf W h a) {y : GlobalTheory.CxPts q σ} (hy : y ∈ ptsIn q σ W)
    (ho : y ∈ offSupp q σ (divOfRatSec ψ.isLB hr)) (hd : ev q σ W d y ≠ 0) :
    GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ W a y‖ - Real.log ‖ev q σ W d y‖ - ψ.φ b y / 2 := by
  have hb : y ∈ ptsIn q σ (L.U b) := mem_ptsIn.2 (hWb (mem_ptsIn.1 hy))
  have hu := IsRatSec.unitAt ψ.isLB hr ho hb
  have hv : ratVal (r b : X.functionField) y ≠ 0 := ratVal_ne_zero hu
  have ev' : ratVal (r b : X.functionField) y * ev q σ W d y = ev q σ W a y := by
    rw [← ratVal_fnOf hy h d, ← ratVal_mul hu.regAt (regAt_fnOf (mem_ptsIn.1 hy) h d), e, ratVal_fnOf hy]
  rw [logNorm_eq ψ hr ho hb, ← ev', norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 hv) (norm_ne_zero_iff.2 hd)]
  ring

theorem logNorm_finite_rep {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ∃ (N : ℕ) (W : Fin N → X.Opens) (b : Fin N → L.ι) (a d : ∀ l, Γ(X, W l)),
      (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) ∧ (∀ l, W l ≤ L.U (b l)) ∧
      (∀ l, ∃ h : genericPoint X ∈ W l, fnOf (W l) h (d l) ≠ 0) ∧
      ∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ offSupp q σ (divOfRatSec ψ.isLB hr) → ev q σ (W l) (d l) y ≠ 0 →
        GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2 := by
  choose W₀ b₀ a₀ d₀ h₀ hy₀ hWb₀ hd₀ e₀ using exists_local_quot ψ r
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => ptsIn q σ (W₀ y))
    (fun y => isOpen_ptsIn _) fun y _ => Set.mem_iUnion.2 ⟨y, hy₀ y⟩
  let c : Fin t.card → GlobalTheory.CxPts q σ := fun l => (t.equivFin.symm l).1
  refine ⟨t.card, fun l => W₀ (c l), fun l => b₀ (c l), fun l => a₀ (c l), fun l => d₀ (c l), fun y => ?_,
    fun l => hWb₀ _, fun l => ⟨h₀ _, hd₀ _⟩, fun l y hy ho hd => logNorm_of_quot ψ hr (hWb₀ _) (e₀ _) hy ho hd⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨z, hz⟩, ?_⟩
  simpa [c] using hyz

end GlobalTheory.CompanionTheory.MixZ.ArchRep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionFiniteOpenCoverStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_finite_open_cover : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r),
    ∃ (N : ℕ) (W : Fin N → X.Opens) (b : Fin N → L.ι) (a d : ∀ l, Γ(X, W l)),
      (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) ∧ (∀ l, W l ≤ L.U (b l)) ∧
      (∀ l, ∃ h : genericPoint X ∈ W l, fnOf (W l) h (d l) ≠ 0) ∧
      ∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ offSupp q σ (divOfRatSec ψ.isLB hr) → ev q σ (W l) (d l) y ≠ 0 →
        GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchRep.logNorm_finite_rep | exact GlobalTheory.CompanionTheory.MixZ.ArchRep.logNorm_finite_rep | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchRep.logNorm_finite_rep <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegrableOn
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.ArchI

theorem exists_modif (hK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0})
    [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ) (hX : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D) :
    ∃ (T : Type) (_ : TopologicalSpace T) (_ : CompactSpace T) (_ : T2Space T) (A : FinHolAtlas D T)
      (F : T → GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Z : Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)),
      Continuous F ∧
      (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ F)) ∧
      MeasurableSet Z ∧ (∀ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) ∧
      (∀ y, y ∉ Z → ∃ x, F x = y) ∧ (∀ x x', F x ∉ Z → F x = F x' → x = x') := by
  have hC := hX.charZero
  obtain ⟨-, hp₃, hp₄, -⟩ := GlobalTheory.T.mixed_cycle_point_dictionary m n X i (D + 1) hX.dim_eq
  have hP := hp₄ (hp₃.2 hC)
  obtain ⟨J, ⟨R⟩⟩ := ReciprocityTheory.ChartRestriction.G.Geo.exists_anLogRes (GlobalTheory.T.resolution_exists_of_resolution_statement hK) hP
  obtain ⟨S, hS, hJ⟩ := R.homog
  obtain ⟨f, hfS, hfP⟩ : ∃ f ∈ S, f ∉ ptIdeal (i (genericPoint X)) := by
    by_contra h
    push_neg at h
    exact R.nondeg (hJ ▸ Ideal.span_le.2 h)
  obtain ⟨a, ha⟩ := hS f hfS
  have hfJ : f ∈ J := hJ ▸ Ideal.subset_span hfS
  have hJz : ∀ z ∈ mcPts J, eval z (map (Int.castRingHom ℂ) f) = 0 := fun z hz => hz.2 f hfJ
  choose F hF' using fun x => GlobalTheory.T.multicone_point_descends_to_subvariety m n X i (R.lift x x) (R.mem x x (R.mem_U x))
  have hU : ∀ x, ∀ y ∈ R.U x, IsUnder (PtsOver.map i rfl _ (F y)) (R.lift x y) := fun x y hy =>
    GlobalTheory.T.isUnder_of_same_orbit m n _ _ _ (hF' y) (R.compat x y y ⟨hy, R.mem_U y⟩)
  have key (x : R.X) (j : Fin R.A.n) := GlobalTheory.T.holomorphic_lift_gives_holomorphic_section m n X i D
    ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) (fun v => R.lift x ((R.A.chart j).symm v))
    (F ∘ (R.A.chart j).symm) ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x))
    (fun u hu => (ReciprocityTheory.ChartRestriction.G.Geo.analyticAt_lift_chart R x j hu).differentiableAt.differentiableWithinAt)
    (fun v hv => hU x _ hv.2)
  have hO (x : R.X) (j : Fin R.A.n) := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨j, hj⟩ := R.A.cover x
    have hm : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
      ⟨(R.A.chart j).map_source hj, by
        simpa only [Set.mem_preimage, (R.A.chart j).left_inv hj] using R.mem_U x⟩
    have h₁ := ((key x j).1.continuousAt ((hO x j).mem_nhds hm)).comp
      (f := R.A.chart j) (x := x) ((R.A.chart j).continuousAt hj)
    refine h₁.congr ?_
    filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with w hw
    simp only [Function.comp_apply, (R.A.chart j).left_inv hw]
  refine ⟨R.X, inferInstance, inferInstance, inferInstance, R.A, F,
    {y | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧ eval z (map (Int.castRingHom ℂ) f) = 0}, hFc, ?_,
    (GlobalTheory.T.hypersurface_complex_points_measurable_null m n X i D f a ha hfP).1, (GlobalTheory.T.hypersurface_complex_points_measurable_null m n X i D f a ha hfP).2, ?_, ?_⟩
  · intro W g j v hv
    set x := (R.A.chart j).symm v with hx
    have hvO : v ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x := ⟨hv.1, R.mem_U x⟩
    have hcont := (key x j).1
    have hO' : IsOpen (((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) ∩
        (F ∘ (R.A.chart j).symm) ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) :=
      hcont.isOpen_inter_preimage (hO x j) (isOpen_ptsIn W)
    have hd := (key x j).2 W g
    exact (SCV.analyticOnNhd_iff_differentiableOn hO').2 hd v ⟨hvO, hv.2⟩
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i y
    have hzJ : z ∉ mcPts J := fun h => hy ⟨z, hyz, hJz z h⟩
    obtain ⟨x, hx⟩ := R.surj z hz hzJ
    exact ⟨x, (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i _ _ _ _ (hF' x) hyz).2 hx⟩
  · intro x x' hx e
    refine R.inj x x' (fun h => hx ⟨_, hF' x, hJz _ h⟩) ?_
    exact (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i _ _ _ _ (hF' x) (hF' x')).1 e

theorem integrableOn_of_modif {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp ℤ} {σ : ℤ →+* ℂ} {D : ℕ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {T : Type} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F)
    (H : ∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F))
    (Z : Set (GlobalTheory.CxPts q σ)) (hZ : MeasurableSet Z)
    (hZ0 : ∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0)
    (hs : ∀ y, y ∉ Z → ∃ x, F x = y) (hi : ∀ x x', F x ∉ Z → F x = F x' → x = x')
    {B C : LB X} (φ : GlobalTheory.Weight q σ B) (hφ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (hψ : ψ.IsCInf)
    {r : C.ι → X.functionFieldˣ} (hr : IsRatSec C r) (ε : ℤˣ) :
    IntegrableOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) (φ.chernPart D ε) := by
  classical
  obtain ⟨N, W, b, a, d, hcov, hWb, hd, hf⟩ := GlobalTheory.T.rational_section_finite_open_cover ψ hr
  set S := offSupp q σ (divOfRatSec ψ.isLB hr) with hSdef
  have hSo : IsOpen S := isOpen_offSupp _
  have hgc := GlobalTheory.T.log_norm_continuous_off_divisor ψ hψ hr
  set g := GlobalTheory.Cartier.logNorm ψ r with hgdef
  set Z' : Set (GlobalTheory.CxPts q σ) := Z ∪ ⋃ l, {y | y ∈ ptsIn q σ (W l) ∧ ev q σ (W l) (d l) y = 0} with hZ'def
  have hpiece (l : Fin N) : MeasurableSet {y | y ∈ ptsIn q σ (W l) ∧ ev q σ (W l) (d l) y = 0} := by
    have ho : IsOpen (ptsIn q σ (W l) ∩ ev q σ (W l) (d l) ⁻¹' {0}ᶜ) :=
      (continuousOn_ev (d l)).isOpen_inter_preimage (isOpen_ptsIn _) isOpen_compl_singleton
    have e : {y | y ∈ ptsIn q σ (W l) ∧ ev q σ (W l) (d l) y = 0} =
        ptsIn q σ (W l) \ (ptsIn q σ (W l) ∩ ev q σ (W l) (d l) ⁻¹' {0}ᶜ) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff, not_and, not_not]
      exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
    rw [e]
    exact (isOpen_ptsIn _).measurableSet.diff ho.measurableSet
  have hZ'm : MeasurableSet Z' := hZ.union (MeasurableSet.iUnion hpiece)
  have hZ'0 : ∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z') = 0 := fun c => by
    rw [hZ'def, Set.preimage_union, Set.inter_union_distrib_left, Set.preimage_iUnion, Set.inter_iUnion]
    refine measure_union_null (hZ0 c) (measure_iUnion_null fun l => ?_)
    obtain ⟨h, hne⟩ := hd l
    exact GlobalTheory.T.zero_locus_regular_function_null X q σ D c (W l) h (d l) hne
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set Pt := hne.some
  have hKK (j : Fin A.n) := image_closed_compact (A.chart j) (isClosed_tsupport (Pt.χ j)) (Pt.tsupport_subset j)
  have hcovK : ∀ x, ∃ j, ∃ u ∈ (A.chart j) '' tsupport (Pt.χ j), (A.chart j).symm u = x := fun x => by
    obtain ⟨j, hj⟩ : ∃ j, Pt.χ j x ≠ 0 := by
      by_contra h
      push_neg at h
      have := Pt.sum_eq_one x
      simp [h] at this
    have hx : x ∈ tsupport (Pt.χ j) := subset_tsupport _ hj
    exact ⟨j, _, ⟨x, hx, rfl⟩, (A.chart j).left_inv (Pt.tsupport_subset j hx)⟩
  have hle := GlobalTheory.T.measure_zero_set_avoided_by_holomorphic_map A F hF H Z' hZ'm hZ'0 (fun y hy => hs y fun h => hy (Or.inl h))
    (fun x x' hx => hi x x' fun h => hx (Or.inl h)) φ hφ ε (fun j => (A.chart j) '' tsupport (Pt.χ j))
    (fun j => (hKK j).1) (fun j => (hKK j).2) hcovK
  have hfin (j : Fin A.n) := GlobalTheory.T.lintegral_indicator_mul_locDens_pullback_lt_top A F hF H φ hφ ψ hψ g S Z' W b a d hcov hWb
    (fun l y hy hyS hyZ => hf l y hy hyS fun h0 => hyZ (Or.inr (Set.mem_iUnion.2 ⟨l, hy, h0⟩))) hSo hgc hZ'm j
    _ (hKK j).2 (hKK j).1
  refine ⟨hgc.aestronglyMeasurable hSo.measurableSet, ?_⟩
  set h : GlobalTheory.CxPts q σ → ENNReal := S.indicator fun y => ‖g y‖ₑ with hh
  have hhm : Measurable h := by
    have := (hgc.enorm).measurable_piecewise (continuousOn_const (c := (0 : ENNReal)) (s := Sᶜ)) hSo.measurableSet
    rwa [show S.piecewise (fun y => ‖g y‖ₑ) (fun _ => (0 : ENNReal)) = h from Set.piecewise_eq_indicator] at this
  show ∫⁻ y, ‖g y‖ₑ ∂(φ.chernPart D ε).restrict S < ⊤
  rw [← lintegral_indicator hSo.measurableSet]
  refine (lintegral_mono' hle le_rfl).trans_lt ?_
  rw [lintegral_finsetSum_measure]
  refine ENNReal.sum_lt_top.2 fun j _ => ?_
  have hT := (A.chart j).open_target.measurableSet
  have hc : ContinuousOn (F ∘ (A.chart j).symm) (A.chart j).target :=
    hF.comp_continuousOn (A.chart j).continuousOn_symm
  have hsub : (A.chart j) '' tsupport (Pt.χ j) \ (F ∘ (A.chart j).symm) ⁻¹' Z' ⊆ (A.chart j).target :=
    Set.diff_subset.trans (hKK j).2
  have hm₀ : AEMeasurable (F ∘ (A.chart j).symm)
      (volume.restrict ((A.chart j) '' tsupport (Pt.χ j) \ (F ∘ (A.chart j).symm) ⁻¹' Z')) :=
    (hc.aemeasurable hT).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hdc := locDensCont A (fun _ => φ.locPot.pullback F hF)
    (fun _ => GlobalTheory.T.smooth_weight_pullback_is_potential A F hF H φ hφ) j
  have hρ : AEMeasurable (fun u => ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|)
      (volume.restrict ((A.chart j) '' tsupport (Pt.χ j) \ (F ∘ (A.chart j).symm) ⁻¹' Z')) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn hdc.abs).aemeasurable hT).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  rw [lintegral_map' hhm.aemeasurable (hm₀.mono_ac (withDensity_absolutelyContinuous _ _))]
  change ∫⁻ u, (h ∘ F ∘ (A.chart j).symm) u ∂_ < ⊤
  rw [lintegral_withDensity_eq_lintegral_mul₀ hρ (hhm.comp_aemeasurable hm₀)]
  refine lt_of_eq_of_lt (lintegral_congr fun u => ?_) (hfin j)
  simp only [Pi.mul_apply, Function.comp_apply, hh]
  exact mul_comm _ _

end GlobalTheory.CompanionTheory.ArchI

namespace GlobalTheory.CompanionTheory.MixZ


open GlobalTheory.CompanionTheory.ArchI in
theorem archIntegrableOn_of_resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ArchIntegrableOn := by
  intro hK m n N M X _ i _ D hX r hr σ
  obtain rfl : σ = σ₀ := Subsingleton.elim _ _
  obtain ⟨T, _, _, _, A, F, Z, hF, H, hZ, hZ0, hs, hi⟩ := exists_modif hK m n X i D hX
  have := hX.compactSpace σ₀
  exact ⟨integrableOn_of_modif A F hF H Z hZ hZ0 hs hi _ ((N.restr i).cInf σ₀) _ ((M.restr i).cInf σ₀) hr 1,
    integrableOn_of_modif A F hF H Z hZ hZ0 hs hi _ ((N.restr i).cInf σ₀) _ ((M.restr i).cInf σ₀) hr (-1)⟩

end GlobalTheory.CompanionTheory.MixZ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegrableOnStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_integrable_on : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.MixZ.ArchIntegrableOn := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.archIntegrableOn_of_resK | exact GlobalTheory.CompanionTheory.MixZ.archIntegrableOn_of_resK | (intros; apply GlobalTheory.CompanionTheory.MixZ.archIntegrableOn_of_resK <;> assumption)
end
