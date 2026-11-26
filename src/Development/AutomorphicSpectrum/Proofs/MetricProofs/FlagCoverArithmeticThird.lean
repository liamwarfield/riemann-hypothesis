module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricGrassmannChartLocal
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThird
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThird
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase

section Orbits

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_basePart {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem sameOrbit_comp {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)] {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (z ∘ v) (z' ∘ v) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext q
  simp only [Function.comp]
  rw [hb.2.2.1 q]

theorem mCoordIdeal_le {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : mCoordIdeal z' ≤ mCoordIdeal z := by
  obtain ⟨c, hc, rfl⟩ := h
  intro f hf
  let ψ : MvPolynomial K ℂ →ₐ[ℤ] MvPolynomial K ℂ :=
    (aeval fun k => C (c k) * X k : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ).restrictScalars ℤ
  have e : mConeMap (fun p : Σ k, ι k => c p.1 * z' p) = ψ.comp (mConeMap z') := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, ψ, mul_assoc, mul_left_comm]
  have hf' : mConeMap z' f = 0 := hf
  show mConeMap _ f = 0
  rw [e, AlgHom.comp_apply, hf', map_zero]

theorem mCoordIdeal_eq {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : mCoordIdeal z = mCoordIdeal z' :=
  le_antisymm (mCoordIdeal_le (Cj.sameOrbit_symm h)) (mCoordIdeal_le h)

theorem coord_ne {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 := fun e =>
  h (by
    show mConeMap z (X q) = 0
    rw [mConeMap, aeval_X, e, map_zero, zero_mul])

theorem comp_mem_mcPts {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)] {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (φ : Ω₁ →+* Ω)
    {x₁ : (Σ k, ι₁ k) → Ω₁} {x : (Σ k, ι k) → Ω} (hx : ∀ q, x (v q) = φ (x₁ q)) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) : z ∘ v ∈ mcPts (mCoordIdeal x₁) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (κ k)
    obtain ⟨⟨k', i'⟩, hp⟩ := hb.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    have hk : k' = k := hb.1 (by simpa [hp] using (hb.2.2.1 ⟨k', i'⟩).symm)
    subst hk
    exact ⟨i', by simpa [Function.comp, hp] using hi⟩
  · let ρ : MvPolynomial K₁ Ω₁ →+* MvPolynomial K Ω :=
      (MvPolynomial.map φ).comp (rename κ : MvPolynomial K₁ Ω₁ →ₐ[Ω₁] MvPolynomial K Ω₁).toRingHom
    have e : (mConeMap x).comp (rename v) = ρ.toIntAlgHom.comp (mConeMap x₁) := by
      apply MvPolynomial.algHom_ext
      intro p
      show mConeMap x (rename v (X p)) = ρ (mConeMap x₁ (X p))
      simp [mConeMap, ρ, hx, hb.2.2.1 p]
    have hf' : mConeMap x₁ f = 0 := hf
    have hr : rename v f ∈ mCoordIdeal x := by
      show mConeMap x (rename v f) = 0
      have e' : mConeMap x (rename v f) = ρ (mConeMap x₁ f) := DFunLike.congr_fun e f
      rw [e', hf', map_zero]
    have := hz.2 _ hr
    rwa [MvPolynomial.map_rename, MvPolynomial.eval_rename] at this

end Orbits

theorem img_lies_over : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w, CovMap.IsImg Cv z w → SameOrbit (basePart M.blk w) (basePart M'.blk z ∘ Cv.v) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ hA' z hz w hI
  have P' := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  have P := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨F', hF', hg'⟩ := P'.2.1 _ (P'.1 z hz)
  let c : K' → ℂ := fun k => if h : ∀ p, M'.blk p ≠ some k then (z ⟨k, F'.c ⟨k, h⟩⟩)⁻¹ else 1
  have hne : ∀ k : NonPluckerBlocks M'.blk, z ⟨k.1, F'.c k⟩ ≠ 0 := fun k => coord_ne (q := ⟨k, F'.c k⟩) (hg'.1 k)
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M'.blk p ≠ some k
    · simp only [c, dif_pos h]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z₁ : (Σ k, ι' k) → ℂ := fun p => c p.1 * z p
  have h1 : SameOrbit z₁ z := ⟨c, hc, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y') := mcPts_smul hA'.2.1.2.1 c hc hz
  have hn : ∀ k, basePart M'.blk z₁ ⟨k, F'.c k⟩ = 1 := fun k => by
    show c k.1 * z ⟨k.1, F'.c k⟩ = 1
    have hk : ∀ p, M'.blk p ≠ some k.1 := k.2
    simp only [c, dif_pos hk]
    exact inv_mul_cancel₀ (hne k)
  have hb₁ := P'.1 z₁ hz₁
  have ho := sameOrbit_basePart M'.blk h1
  have hgood : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by
    rw [mCoordIdeal_eq ho]
    exact hg'
  obtain ⟨h, hh⟩ := (P'.2.2 F' hF' z₁ hb₁ hgood hn).1 hz₁
  obtain ⟨F, hF, hg⟩ := P.2.1 _ (comp_mem_mcPts Cv.block Cv.φ Cv.x_eq hb₁)
  obtain ⟨z₀, a, b, -⟩ := hI z₁ h1 F' F hF' hF hgood hg h hh
  exact Cj.sameOrbit_trans (Cj.sameOrbit_symm (sameOrbit_basePart M.blk a))
    (Cj.sameOrbit_trans b (sameOrbit_comp Cv.block ho))

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThirdStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_arithmetic_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w, CovMap.IsImg Cv z w → SameOrbit (basePart M.blk w) (basePart M'.blk z ∘ Cv.v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.img_lies_over | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.img_lies_over | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.img_lies_over <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionVerticalFactor
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionVerticalFactor
noncomputable section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem log_vertFactor_eq_re_holo : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ) (M : XModel D) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ), p ∈ D.S → IsOpen U → (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) → (∀ q, M.atlas.HoloOn U fun y => s y q) → ∀ y₀ ∈ U, ∃ V : Set M.Xc, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn V G ∧ ∀ y ∈ V, Real.log (D.vertFactor p (s y)) = (G y).re := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D p M U s hp hU hs hhol y₀ hy₀
  obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp (hs y₀ hy₀)
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D p hp (s y₀) (hs y₀ hy₀)
  rw [VertFactorSmooth.vertFactor_eq D hp (hs y₀ hy₀) hG hH hdeg hrel hHz] at hpos
  have hGz : eval (s y₀) (map (Int.castRingHom ℂ) G) ≠ 0 := by
    intro h
    rw [h, zero_div, norm_zero] at hpos
    exact lt_irrefl _ hpos
  set A := M.atlas with hA
  have HG := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_eval A hhol G
  have HH := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_eval A hhol H
  set Gf : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) G) with hGf
  set Hf : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) H) with hHf
  set W₁ : Set M.Xc := U ∩ {y | Hf y ≠ 0} with hW₁
  have hW₁o : IsOpen W₁ := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.isOpen_inter_ne A hU HH
  have hsub : W₁ ⊆ U := Set.inter_subset_left
  have mono : ∀ {f : M.Xc → ℂ} {S T : Set M.Xc}, T ⊆ S → A.HoloOn S f → A.HoloOn T f := by
    intro f S T hTS hf j
    exact (hf j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hTS))
  set g : M.Xc → ℂ := fun y => Gf y / Hf y with hg
  have Hg : A.HoloOn W₁ g :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_div_congr A hW₁o (mono hsub HG) (mono hsub HH)
      (fun y hy => hy.2) fun y _ => rfl
  set c : ℂ := g y₀ with hc
  have hc0 : c ≠ 0 := div_ne_zero hGz hHz
  set V : Set M.Xc := W₁ ∩ {y | g y / c ∈ Complex.slitPlane} with hV
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hy, hsl⟩
    have hcont : ContinuousAt (fun y => g y / c) y :=
      (GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.continuousAt_of_holoOn A Hg hy).div_const c
    filter_upwards [hW₁o.mem_nhds hy, hcont (Complex.isOpen_slitPlane.mem_nhds hsl)] with u h1 h2
    exact ⟨h1, h2⟩
  have hy₀V : y₀ ∈ V := by
    refine ⟨⟨hy₀, hHz⟩, ?_⟩
    show g y₀ / c ∈ Complex.slitPlane
    rw [← hc, div_self hc0]
    exact Complex.one_mem_slitPlane
  refine ⟨V, hVo, hy₀V, fun y hy => hsub hy.1, fun y => Complex.log (g y / c) + (Real.log ‖c‖ : ℂ), ?_, ?_⟩
  · intro j u hu
    have hgu : AnalyticAt ℂ (g ∘ (A.chart j).symm) u :=
      Hg j u ⟨hu.1, hu.2.1⟩
    have hsl : (g ∘ (A.chart j).symm) u / c ∈ Complex.slitPlane := hu.2.2
    have h1 : AnalyticAt ℂ (fun v => (g ∘ (A.chart j).symm) v / c) u := hgu.div analyticAt_const hc0
    have h2 := (h1.clog hsl).add (analyticAt_const (v := ((Real.log ‖c‖ : ℝ) : ℂ)))
    exact h2
  · rintro y ⟨hy, hsl⟩
    have hsl' : g y / c ∈ Complex.slitPlane := hsl
    have hgy : g y ≠ 0 := by
      intro h
      rw [h, zero_div] at hsl'
      exact Complex.slitPlane_ne_zero hsl' rfl
    rw [VertFactorSmooth.vertFactor_eq D hp (hs y (hsub hy)) hG hH hdeg hrel hy.2]
    show Real.log ‖g y‖ = (Complex.log (g y / c) + ((Real.log ‖c‖ : ℝ) : ℂ)).re
    rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div (g y) c,
      Real.log_div (norm_ne_zero_iff.2 hgy) (norm_ne_zero_iff.2 hc0)]
    ring

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionVerticalFactorStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_vertical_factor : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ) (M : XModel D) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ), p ∈ D.S → IsOpen U → (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) → (∀ q, M.atlas.HoloOn U fun y => s y q) → ∀ y₀ ∈ U, ∃ V : Set M.Xc, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn V G ∧ ∀ y ∈ V, Real.log (D.vertFactor p (s y)) = (G y).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.log_vertFactor_eq_re_holo | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.log_vertFactor_eq_re_holo | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.log_vertFactor_eq_re_holo <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionMapLocallyAnalytic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionMapLocallyAnalytic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {D e : ℕ} (R : AnLogRes P ⊤ D) {Y : Type*} [TopologicalSpace Y]
  (B : FinHolAtlas e Y) {V : Y → Set Y} {μ : Y → Y → (Σ k, ι k) → ℂ} {h : Y → R.X}

theorem continuous_of_orbit_of_ne (hVo : ∀ y, IsOpen (V y)) (hVm : ∀ y, y ∈ V y)
    (hμ : ∀ y q, B.HoloOn (V y) fun u => μ y u q) (hne : ∀ y k, ∃ i, μ y y ⟨k, i⟩ ≠ 0)
    (hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u))
    (hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μ y y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt, tendsto_iff_ultrafilter]
  intro F hF
  obtain ⟨x, -, hx⟩ := isCompact_univ.ultrafilter_le_nhds (F.map h) (by simp)
  have hth : Tendsto h F (𝓝 x) := hx
  have hUx : ∀ᶠ y' in (F : Filter Y), h y' ∈ R.U x := hth ((R.isOpen_U x).mem_nhds (R.mem_U x))
  have hVy : ∀ᶠ y' in (F : Filter Y), y' ∈ V y := hF ((hVo y).mem_nhds (hVm y))
  have hcr : ∀ k (i i' : ι k), R.lift x x ⟨k, i⟩ * μ y y ⟨k, i'⟩ =
      R.lift x x ⟨k, i'⟩ * μ y y ⟨k, i⟩ := by
    intro k i i'
    have t1 : ∀ q, Tendsto (fun y' => R.lift x (h y') q) F (𝓝 (R.lift x x q)) := fun q =>
      (Proj.continuousAt_of_holoOn R.A (R.holo x q) (R.mem_U x)).tendsto.comp hth
    have t2 : ∀ q, Tendsto (fun y' => μ y y' q) F (𝓝 (μ y y q)) := fun q =>
      (Proj.continuousAt_of_holoOn B (hμ y q) (hVm y)).tendsto.mono_left hF
    refine tendsto_nhds_unique ((t1 ⟨k, i⟩).mul (t2 ⟨k, i'⟩))
      (((t1 ⟨k, i'⟩).mul (t2 ⟨k, i⟩)).congr' ?_)
    filter_upwards [hUx, hVy] with y' h1 h2
    exact Proj.orbit_cross (Proj.local_orbit R hVm hc hh h1 h2) k i' i
  have hxy : SameOrbit (R.lift x x) (μ y y) :=
    Proj.orbit_of_cross (R.mem x x (R.mem_U x)).1 (hne y) hcr
  have hxe : x = h y :=
    R.inj x (h y) (Proj.not_mem_mcPts_top _) (Proj.orbit_trans hxy (Proj.orbit_symm (hh y)))
  rw [← hxe]
  exact hx

end Orbit

theorem holoMap_of_local_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P J : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D D' : ℕ) (R : AnLogRes P J D) (R' : AnLogRes P' J' D') (g : R'.X → R.X), J = ⊤ → (∀ x, ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ R'.lift x x ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts P', ∀ x', SameOrbit z' (R'.lift x' x') → SameOrbit (f z') (R.lift (g x') (g x'))) → HoloMap R'.A R.A g := by
  intro K _ ι _ K' _ ι' _ P J P' J' D D' R R' g hJ hg
  subst hJ
  choose Vs f hVs hxV hf hcomp using hg
  have hcl : ∀ y, ContinuousOn (R'.lift y) (R'.U y) := fun y =>
    continuousOn_pi.2 fun p x hx =>
      (Proj.continuousAt_of_holoOn R'.A (R'.holo y p) hx).continuousWithinAt
  let V : R'.X → Set R'.X := fun y => R'.U y ∩ R'.lift y ⁻¹' Vs y
  let μ : R'.X → R'.X → (Σ k, ι k) → ℂ := fun y u => f y (R'.lift y u)
  have hVo : ∀ y, IsOpen (V y) := fun y =>
    (hcl y).isOpen_inter_preimage (R'.isOpen_U y) (hVs y)
  have hVm : ∀ y, y ∈ V y := fun y => ⟨R'.mem_U y, hxV y⟩
  have hμ : ∀ y q, R'.A.HoloOn (V y) fun u => μ y u q := by
    rintro y q j w ⟨hw, hwV⟩
    have h1 : AnalyticAt ℂ (fun w' => R'.lift y ((R'.A.chart j).symm w')) w :=
      AnalyticAt.pi fun p => R'.holo y p j w ⟨hw, hwV.1⟩
    have h2 : AnalyticAt ℂ (f y ∘ fun w' => R'.lift y ((R'.A.chart j).symm w')) w :=
      AnalyticAt.comp (hf y _ hwV.2) h1
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) q).analyticAt _ |>.comp h2
  have hor : ∀ y, ∀ u ∈ V y, SameOrbit (μ y u) (R.lift (g u) (g u)) := fun y u hu =>
    hcomp y _ ⟨hu.2, R'.mem y u hu.1⟩ u (R'.compat y u u ⟨hu.1, R'.mem_U u⟩)
  have hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u) := fun y y' u hu =>
    Proj.orbit_trans (hor y u hu.1) (Proj.orbit_symm (hor y' u hu.2))
  have hh : ∀ y, SameOrbit (R.lift (g y) (g y)) (μ y y) := fun y =>
    Proj.orbit_symm (hor y y (hVm y))
  have hne : ∀ y k, ∃ i, μ y y ⟨k, i⟩ ≠ 0 := fun y k => by
    obtain ⟨i, hi⟩ := (R.mem (g y) (g y) (R.mem_U _)).1 k
    exact ⟨i, Proj.orbit_ne (hh y) hi⟩
  have hcont : Continuous g := continuous_of_orbit_of_ne R R'.A hVo hVm hμ hne hc hh
  exact ⟨hcont, Proj.analytic_of_orbit R R'.A hVo hVm hμ hc hh hcont⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionMapLocallyAnalyticStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_map_locally_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P J : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D D' : ℕ) (R : AnLogRes P J D) (R' : AnLogRes P' J' D') (g : R'.X → R.X), J = ⊤ → (∀ x, ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ R'.lift x x ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts P', ∀ x', SameOrbit z' (R'.lift x' x') → SameOrbit (f z') (R.lift (g x') (g x'))) → HoloMap R'.A R.A g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_of_local_analytic | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_of_local_analytic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_of_local_analytic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalNormComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalNormComparison
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem upV_scale {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (z : (Σ k, ιk k) → ℂ) (c : Kk → ℂ)
    (k₀ : Kk) (m : ι (κ k₀)) :
    upV v (fun p => c p.1 * z p) ⟨κ k₀, m⟩ = c k₀ * upV v z ⟨κ k₀, m⟩ := by
  obtain ⟨q, hq⟩ := hb.2.2.2 ⟨κ k₀, m⟩ ⟨k₀, rfl⟩
  have hk : q.1 = k₀ := hb.1 (by rw [← hb.2.2.1 q, hq])
  rw [← hq, upV_apply hb.2.1, upV_apply hb.2.1, hk]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem pRead_scale (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ} (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) {u u' : (Σ k, ι k) → ℂ} (τ : Ψ) (a b : Fin N)
    (hu : ∀ k, M.blk (τ, pStep j keep τ b) = some k → ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, u' ⟨k, m⟩ = t * u ⟨k, m⟩) :
    pRead M F keep zb' h u' τ a b = pRead M F keep zb h u τ a b := by
  unfold pRead
  obtain hk | ⟨k, hk⟩ : M.blk (τ, pStep j keep τ b) = none ∨ ∃ k, M.blk (τ, pStep j keep τ b) = some k := by
    cases M.blk (τ, pStep j keep τ b) <;> simp
  · simp only [hk, Option.elim_none]
  · obtain ⟨t, ht, hu⟩ := hu k hk
    simp only [hk, Option.elim_some]
    rw [WMan.Orb.twMinor_scale M F hv _ k _ hu, WMan.Orb.twMinor_scale M F hv _ k _ hu,
      mul_left_comm (pSgn _ _ _) t, mul_div_mul_left _ _ ht]

end

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ z ∈ pO M Rb keep v F kb V r h, ∀ z' ∈ mcPts (mCoordIdeal (y ∘ v)), SameOrbit z' z → z' ∈ pO M Rb keep v F kb V r h ∧ pRho M Rb keep v F kb r h ε z' = pRho M Rb keep v F kb r h ε z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε ctx z hz z' hz' ho
  obtain ⟨hbm, hrange, -, -, hr, -, -⟩ := ctx
  obtain ⟨hzP, hs, hV, hm⟩ := hz
  have hI := GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange
  have hb := hI.1 z hzP
  have hb' := hI.1 z' hz'
  have hob : SameOrbit (pBase M v z') (pBase M v z) := hI.2 z' z ho
  have hnot : ∀ x : Rb.X, Rb.lift x x ∉ mcPts (⊤ : Ideal (MRing (baseIdx ι M.blk))) := fun x hx => by
    have := hx.2 1 Submodule.mem_top
    simp at this
  have hrr : r (pBase M v z') = r (pBase M v z) :=
    Rb.inj _ _ (hnot _) (orbit_trans (hr _ hb') (orbit_trans hob (orbit_symm (hr _ hb))))
  have hv : ∀ s, valAt M.x s (pBase M v z') = valAt M.x s (pBase M v z) := fun s => by
    obtain ⟨t, ht, et⟩ := hob
    have := StepW.TorusAct.valAt_torus (x := M.x) t ht hb (et ▸ hb') s
    rw [et]
    exact this
  obtain ⟨c, hc, rfl⟩ := ho

  have hkept : ∀ {p : Ψ × Fin N} {k : K}, keep p → M.blk p = some k →
      ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, upV v (fun p => c p.1 * z p) ⟨k, m⟩ = t * upV v z ⟨k, m⟩ := by
    intro p k hp hk
    obtain ⟨k₀, rfl⟩ := (hrange k).2 (Or.inr ⟨p, hp, hk⟩)
    exact ⟨c k₀, hc k₀, upV_scale hbm z c k₀⟩
  refine ⟨⟨hz', ?_, ?_, fun p k hp hk => ?_⟩, ?_⟩
  · rw [hrr]; exact hs
  · rw [hrr]; exact hV
  · obtain ⟨t, ht, hu⟩ := hkept hp hk
    rw [WMan.Orb.twMinor_scale M F hv _ k _ hu]
    exact mul_ne_zero ht (hm p k hp hk)
  · funext i
    unfold pRho
    rcases ε.symm i with l | q
    · show Rb.A.chart kb (r (pBase M v _)) l = Rb.A.chart kb (r (pBase M v z)) l
      rw [hrr]
    · exact pRead_scale M F keep hv h _ _ _ fun k hk =>
        hkept (SmallStep.pStep_reads Ψ N j keep q M.j_le).1 hk

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalNormComparisonStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_norm_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ z ∈ pO M Rb keep v F kb V r h, ∀ z' ∈ mcPts (mCoordIdeal (y ∘ v)), SameOrbit z' z → z' ∈ pO M Rb keep v F kb V r h ∧ pRho M Rb keep v F kb r h ε z' = pRho M Rb keep v F kb r h ε z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricExplicitMatrixForm
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricExplicitMatrixForm
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep

theorem prod_base_split {K : Type} [Fintype K] {σ : Type} (blk : σ → Option K) (p : σ) (k₀ : K)
    (hp : blk p = some k₀) (f : K → ℝ)
    (hf : ∀ k, (¬ ∀ p', blk p' ≠ some k) → k ≠ k₀ → f k = 1) :
    ∏ k, f k = (∏ k : NonPluckerBlocks blk, f k.1) * f k₀ := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ fun k => ∀ p', blk p' ≠ some k]
  congr 1
  · exact Finset.prod_subtype _ (by simp) f
  · refine Finset.prod_eq_single_of_mem k₀ ?_ ?_
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun e => e p hp⟩
    · intro k hk e
      exact hf k (Finset.mem_filter.1 hk).2 e

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ), M.blk p = some k₀ → IsGrChart N j p.2 I₀ C B → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → plk M (BM.F l) k₀ z I₀ ≠ 0 → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) (grMat C B I₀ (plk M (BM.F l) k₀ z)) + Real.log ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z I₀ C B hp hC hx hz hor hw
  obtain ⟨h, a, hb, hd, ha, hstep, hzk⟩ := GlobalTheory.T.block_metric_grassmann_chart_local K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hx.1 hz hor
  obtain ⟨hHb, hHd, hHm⟩ := hC h a _ hb hd ha hstep hw
  have hL : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)
  have hor' := hor
  obtain ⟨c0, hc0, e0⟩ := hor'
  have hbz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x) := by
    rw [e0]
    exact ((TorusAct.main _ _ _ M.x _ c0 hc0).2 hL).1
  have hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := by
    intro k h0
    have hl : BM.Rb.lift x₀ x₀ ⟨k, (BM.F l).c k⟩ = 0 := by
      have e1 := congrFun e0 ⟨k, (BM.F l).c k⟩
      rw [h0] at e1
      exact (mul_eq_zero.1 e1.symm).resolve_left (hc0 k)
    refine (BM.good l x₀ hx.1).1 k ?_
    show mConeMap (BM.Rb.lift x₀ x₀) (X ⟨k, (BM.F l).c k⟩) = 0
    rw [mConeMap, aeval_X, hl, map_zero, zero_mul]
  let c : K → ℂ := fun k => if hk : ∀ p', M.blk p' ≠ some k then
    (basePart M.blk z ⟨⟨k, hk⟩, (BM.F l).c ⟨k, hk⟩⟩)⁻¹ else if k = k₀ then (plk M (BM.F l) k₀ z I₀)⁻¹ else 1
  have hcb : ∀ k : NonPluckerBlocks M.blk, c k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹ := fun k => dif_pos k.2
  have hk₀ : ¬ ∀ p', M.blk p' ≠ some k₀ := fun e => e p hp
  have hck : c k₀ = (plk M (BM.F l) k₀ z I₀)⁻¹ := (dif_neg hk₀).trans (if_pos rfl)
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : ∀ p', M.blk p' ≠ some k
    · rw [hcb ⟨k, hk⟩]
      exact inv_ne_zero (hne ⟨k, hk⟩)
    · by_cases e : k = k₀
      · rw [e, hck]
        exact inv_ne_zero hw
      · rw [show c k = 1 from (dif_neg hk).trans (if_neg e)]
        exact one_ne_zero
  have hz₂ := ((TorusAct.main K ι Φ y z c hc).2 hz).1
  have hval := ((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc _)).2 hbz).2
  have hbp : basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) =
      fun q : Σ k, baseIdx ι M.blk k => c q.1.1 * basePart M.blk z q := rfl
  have hso : SameOrbit (basePart M.blk (fun q : Σ k, ι k => c q.1 * z q)) (BM.Rb.lift x₀ x₀) := by
    refine ⟨fun k => c k.1 * c0 k, fun k => mul_ne_zero (hc _) (hc0 k), ?_⟩
    rw [hbp, e0]
    funext q
    exact (mul_assoc _ _ _).symm
  have hnorm : ∀ k, basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hbp]
    show c k.1 * basePart M.blk z ⟨k, (BM.F l).c k⟩ = 1
    rw [hcb k, inv_mul_cancel₀ (hne k)]
  have hlog := (BM.induced l x₀ hx p _ hz₂ hso hnorm _ hHb hHd).1 k₀ hp (fun m => by
    rw [hbp, hzk m, hck]
    simp only [hval]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [mul_left_comm a, ← hHm I, mul_left_comm, ← mul_assoc _ _ (plk M (BM.F l) k₀ z I₀), mul_comm _ (plk M (BM.F l) k₀ z I₀),
      mul_inv_cancel_left₀ hw])
  have hs := (BM.hom p).smul c z hc
  rw [BM.hom_deg p] at hs
  have hdy : M.dy p k₀ = 1 := (dif_neg hk₀).trans (if_pos hp)
  have hdy0 : ∀ k, (¬ ∀ p', M.blk p' ≠ some k) → k ≠ k₀ → M.dy p k = 0 := fun k hk e =>
    (dif_neg hk).trans (if_neg fun e' => e (Option.some_injective _ (hp.symm.trans e')).symm)
  have hsplit := prod_base_split M.blk p k₀ hp (fun k => ‖c k‖ ^ M.dy p k)
    (fun k hk e => by simp only [hdy0 k hk e, zpow_zero])
  have hPQ : (∏ k, ‖c k‖ ^ M.dy p k) * ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ = 1 := by
    rw [hsplit, hdy, zpow_one, hck, norm_mul, baseMono, norm_prod, norm_inv]
    simp only [norm_zpow]
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw), mul_one]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hcb k, norm_inv, _root_.inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ (norm_ne_zero_iff.2 (hne k)))]
  have hpos := (BM.hom p).pos (fun q => c q.1 * z q) hz₂.1
  have hQ : ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ ≠ 0 := fun e => by
    rw [e, mul_zero] at hPQ
    exact zero_ne_one hPQ
  have hh : (BM.hom p).h z =
      ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ * (BM.hom p).h fun q => c q.1 * z q := by
    rw [hs, ← mul_assoc, mul_comm ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖, hPQ, one_mul]
  rw [hh, Real.log_mul hQ hpos.ne', hlog, add_comm]

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricExplicitMatrixFormStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_metric_explicit_matrix_form : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ), M.blk p = some k₀ → IsGrChart N j p.2 I₀ C B → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → plk M (BM.F l) k₀ z I₀ ≠ 0 → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) (grMat C B I₀ (plk M (BM.F l) k₀ z)) + Real.log ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFirst
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFirst
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_finTail {d : ℕ} (u : Fin (d + 1) → ℂ) :
    AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) u := by
  have h : (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) =
      ⇑(ContinuousLinearMap.pi fun i : Fin d =>
        (ContinuousLinearMap.proj i.succ : (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) := by
    funext u i
    rfl
  rw [h]
  exact ContinuousLinearMap.analyticAt _ _

theorem analyticAt_det_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : Type} [Fintype n]
    [DecidableEq n] (A : E → Matrix n n ℂ) (x : E) (h : ∀ r s, AnalyticAt ℂ (fun u => A u r s) x) :
    AnalyticAt ℂ (fun u => (A u).det) x := by
  simp only [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem analyticAt_minorIJ_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ}
    (A : E → Matrix (Fin N) (Fin N) ℂ) (x : E) (h : ∀ r s, AnalyticAt ℂ (fun u => A u r s) x)
    (I J : Finset (Fin N)) : AnalyticAt ℂ (fun u => minorIJ (A u) I J) x := by
  by_cases e : I.card = J.card
  · simp only [minorIJ, dif_pos e]
    exact analyticAt_det_of_entries _ x fun r s => h _ _
  · simp only [minorIJ, dif_neg e]
    exact analyticAt_const

theorem analyticAt_flagAt_entry {Ψ : Type} [DecidableEq Ψ] {N d : ℕ} (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (τ : Ψ) (ca cb : Fin N) (τ' : Ψ) (u₀ : Fin (d + 1) → ℂ)
    (hH : ∀ τ'' r s, AnalyticAt ℂ (fun w => H τ'' w r s) (Fin.tail u₀)) (r s : Fin N) :
    AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => flagAt H τ ca cb (u 0) (Fin.tail u) τ' r s) u₀ := by
  have hHt : ∀ τ'' r s, AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => H τ'' (Fin.tail u) r s) u₀ :=
    fun τ'' r s => (hH τ'' r s).comp (analyticAt_finTail u₀)
  have h0 : AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => u 0) u₀ :=
    (ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℂ) →L[ℂ] ℂ).analyticAt _
  unfold flagAt
  by_cases h : τ' = τ
  · simp only [if_pos h, Matrix.mul_apply, Matrix.add_apply]
    refine Finset.analyticAt_fun_sum _ fun t _ => (hHt _ _ _).mul (analyticAt_const.add ?_)
    by_cases e : cb = t ∧ ca = s
    · simpa only [Matrix.single_apply, if_pos e] using h0
    · simpa only [Matrix.single_apply, if_neg e] using analyticAt_const
  · simp only [if_neg h]
    exact hHt _ _ _

theorem sameOrbit_basePart {K : Type} {ι : K → Type} {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem coord_ne_zero_of_X_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 := fun h0 => h (by
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem exists_normalised_exact {M : FlagModel y Ψ N j} (F : FrameData ι Ψ N M.Ω M.blk) (z₀ : (Σ k, ι k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (hne : ∀ k : NonPluckerBlocks M.blk, z₀ ⟨k.1, F.c k⟩ ≠ 0)
    (hex : ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₀ (h τ')) :
    ∃ z : (Σ k, ι k) → ℂ, SameOrbit z₀ z ∧ (∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) ∧
      ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z (h τ') := by
  by_cases hp : Nonempty (Ψ × Fin N)
  · obtain ⟨⟨τ₀, i₀⟩⟩ := hp
    exact ⟨z₀, ⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩, (hex τ₀ i₀).1, hex⟩
  · have hb : ∀ (k : K) p, M.blk p ≠ some k := fun k p => (hp ⟨p⟩).elim
    refine ⟨fun q => z₀ q / z₀ ⟨q.1, F.c ⟨q.1, hb q.1⟩⟩,
      ⟨fun k => z₀ ⟨k, F.c ⟨k, hb k⟩⟩, fun k => hne ⟨k, hb k⟩, ?_⟩, ?_, fun τ' i => (hp ⟨(τ', i)⟩).elim⟩
    · funext q
      rw [mul_div_cancel₀ _ (hne ⟨q.1, hb q.1⟩)]
    · rintro ⟨k, hk⟩
      exact div_self (hne ⟨k, hb k⟩)

theorem exact_points_holomorphic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a ca cb : Fin N) (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∃ zex : (Fin (d + 1) → ℂ) → (Σ k, ι k) → ℂ, (∀ q', AnalyticOnNhd ℂ (fun u => zex u q') {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un}) ∧ ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → zex u ∈ mcPts (mCoordIdeal y) ∧ ∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) (zex u) ∧ SameOrbit (basePart M.blk (zex u)) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) (zex u) (flagAt H τ ca cb (u 0) (Fin.tail u) τ') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a ca cb X q Un Gn ΦYn ΦWn l H bp hUn hD
  obtain ⟨hH, hbc, hba, hbp, -, hex, -⟩ := hD
  have hbij := realis_bijective_of_degree_one K ι (d + 1) _ FA.S _ FA.Re FA.deg_one FA.br_empty
  have hyh : IsMultiHomogIdeal (mCoordIdeal y) :=
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y
  have key : ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → ∃ z : (Σ k, ι k) → ℂ,
      z ∈ mcPts (mCoordIdeal y) ∧ (∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) z) ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧
      (∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) z (flagAt H τ ca cb (u 0) (Fin.tail u) τ')) ∧
      ∀ k, basePart M.blk z ⟨k, (BM.F l).c k⟩ = 1 := by
    intro u hu
    obtain ⟨x₀, hx₀⟩ := hbij.2 (ΦYn u)
    obtain ⟨z₀, ho, hb, he⟩ := hex u hu x₀ hx₀
    have hgood := BM.good l _ (hbp _ hu).1.1
    have hne : ∀ k : NonPluckerBlocks M.blk, z₀ ⟨k.1, (BM.F l).c k⟩ ≠ 0 := by
      intro k
      obtain ⟨c, hc, hcz⟩ := hb
      have h1 := congrFun hcz ⟨k, (BM.F l).c k⟩
      have h2 : basePart M.blk z₀ ⟨k, (BM.F l).c k⟩ = z₀ ⟨k.1, (BM.F l).c k⟩ := rfl
      rw [← h2, h1]
      exact mul_ne_zero (hc k) (coord_ne_zero_of_X_notMem (hgood.1 k))
    obtain ⟨z, hz, hn, hz'⟩ := exists_normalised_exact (BM.F l) z₀ _ hne he
    refine ⟨z, ?_, ?_, ?_, hz', hn⟩
    · exact mem_mcPts_of_sameOrbit hyh (orbit_symm (orbit_trans ho hz))
        (FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀))
    · intro x₁ hx₁
      obtain rfl := hbij.1 (hx₁.trans hx₀.symm)
      exact orbit_trans ho hz
    · exact orbit_trans (orbit_symm (sameOrbit_basePart M.blk hz)) hb
  choose! zex hz using key
  refine ⟨zex, ?_, fun u hu => ⟨(hz u hu).1, fun x₀ hx =>
    ⟨(hz u hu).2.1 x₀ hx, (hz u hu).2.2.1, (hz u hu).2.2.2.1⟩⟩⟩
  rintro ⟨k, m⟩ u₀ hu₀
  have hu₀' : (Fin.tail u₀ : Fin d → ℂ) ∈ Un := hu₀
  have htail : Tendsto (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) (𝓝 u₀) (𝓝 (Fin.tail u₀)) :=
    (analyticAt_finTail u₀).continuousAt
  have hevU : ∀ᶠ u : Fin (d + 1) → ℂ in 𝓝 u₀, (Fin.tail u : Fin d → ℂ) ∈ Un := htail (hUn.mem_nhds hu₀')
  have hgood₀ := BM.good l _ (hbp _ hu₀').1.1
  by_cases hk : ∃ p, M.blk p = some k
  · obtain ⟨p, hp⟩ := hk
    have hval : ∀ s, RegAt M.x (mCoordIdeal (BM.Rb.lift (bp (Fin.tail u₀)) (bp (Fin.tail u₀)))) s →
        AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => valAt M.x s (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u)))) u₀ :=
      fun s hs => (analyticAt_valAt_lift_family (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x s d n BM.Rb Un bp (Fin.tail u₀)
        hUn hu₀' hbc hba hs).comp (analyticAt_finTail u₀)
    have hsum : AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => ∑ I,
        valAt M.x ((BM.F l).u ⟨k, m⟩ I) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) *
          minorIJ (flagAt H τ ca cb (u 0) (Fin.tail u) p.1) I (stepCols N j p.2)) u₀ :=
      Finset.analyticAt_fun_sum _ fun I _ => (hval _ ((hgood₀.2.1 _ I).1)).mul
        (analyticAt_minorIJ_of_entries _ _ (analyticAt_flagAt_entry H τ ca cb p.1 u₀
          (fun τ'' r s => hH τ'' r s _ hu₀')) _ _)
    refine hsum.congr ?_
    filter_upwards [hevU] with u hu
    obtain ⟨-, -, hb, he, -⟩ := hz u hu
    rw [(he p.1 p.2).2 k hp m]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [valAt_eq_of_sameOrbit (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x _ _ _ (BM.Rb.mem _ _ (BM.Rb.mem_U _))
      (orbit_symm hb)]
  · have hkb : ∀ p, M.blk p ≠ some k := fun p hp => hk ⟨p, hp⟩
    set kb : NonPluckerBlocks M.blk := ⟨k, hkb⟩ with hkb'
    set b₀ := bp (Fin.tail u₀) with hb₀
    have hlift : ∀ q : Σ k, baseIdx ι M.blk k,
        AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => BM.Rb.lift b₀ (bp (Fin.tail u)) q) u₀ :=
      fun q => (analyticAt_comp_of_holo_in_charts d n BM.Rb.X BM.Rb.A Un bp (Fin.tail u₀) (BM.Rb.U b₀)
        (fun x => BM.Rb.lift b₀ x q) hUn hu₀' hbc hba (BM.Rb.isOpen_U _) (BM.Rb.mem_U _)
        (BM.Rb.holo b₀ q)).comp (analyticAt_finTail u₀)
    have hden : BM.Rb.lift b₀ (bp (Fin.tail u₀)) ⟨kb, (BM.F l).c kb⟩ ≠ 0 :=
      coord_ne_zero_of_X_notMem (hgood₀.1 kb)
    refine ((hlift ⟨kb, m⟩).div (hlift ⟨kb, (BM.F l).c kb⟩) hden).congr ?_
    have hca : ContinuousAt bp (Fin.tail u₀) := hbc.continuousAt (hUn.mem_nhds hu₀')
    filter_upwards [hevU, htail (hca ((BM.Rb.isOpen_U b₀).mem_nhds (BM.Rb.mem_U b₀)))] with u hu hbu
    obtain ⟨-, -, hb, -, hn⟩ := hz u hu
    obtain ⟨c, hc, hcz⟩ := orbit_trans hb (BM.Rb.compat (bp (Fin.tail u)) b₀ (bp (Fin.tail u)) ⟨BM.Rb.mem_U _, hbu⟩)
    have h1 : c kb * BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ = 1 := by
      rw [← hn kb, hcz]
    have h2 : zex u ⟨k, m⟩ = c kb * BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩ := congrFun hcz ⟨kb, m⟩
    have h3 : BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ ≠ 0 := right_ne_zero_of_mul_eq_one h1
    show BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩ / BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ = zex u ⟨k, m⟩
    rw [h2, div_eq_iff h3]
    linear_combination (-(BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩)) * h1

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFirstStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a ca cb : Fin N) (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∃ zex : (Fin (d + 1) → ℂ) → (Σ k, ι k) → ℂ, (∀ q', AnalyticOnNhd ℂ (fun u => zex u q') {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un}) ∧ ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → zex u ∈ mcPts (mCoordIdeal y) ∧ ∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) (zex u) ∧ SameOrbit (basePart M.blk (zex u)) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) (zex u) (flagAt H τ ca cb (u 0) (Fin.tail u) τ') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IteratedDerivBoundGaussianGrowth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IteratedDerivBoundGaussianGrowth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem norm_iteratedDeriv_zero_le_of_gaussian_growth
    (f : ℂ → ℂ) (M lam : ℝ) (n n' i : ℕ) (hf : Differentiable ℂ f) (hlam : 0 < lam)
    (hn : 1 ≤ n) (hn' : 1 ≤ n') (hi : i ≤ n')
    (hb : ∀ τ, ‖f τ‖ ≤ M * Real.exp (n * ‖τ‖ ^ 2 * lam ^ 2 / 2)) :
    ‖iteratedDeriv i f 0‖ ≤ Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M := by
  have h0 : ‖f 0‖ ≤ M := by simpa using hb 0
  have hM : 0 ≤ M := (norm_nonneg _).trans h0
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simpa using h0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hi0' : (0 : ℝ) < i := by exact_mod_cast hi0
  have hlam2 : (0 : ℝ) < lam ^ 2 := pow_pos hlam 2
  have hq : (0 : ℝ) < i / (n * lam ^ 2) := div_pos hi0' (mul_pos hn0 hlam2)
  set R : ℝ := Real.sqrt (i / (n * lam ^ 2)) with hR
  have hR2 : R ^ 2 = i / (n * lam ^ 2) := Real.sq_sqrt hq.le
  have hRpos : 0 < R := Real.sqrt_pos.2 hq
  have hsph : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M * Real.exp (i / 2) := by
    intro z hz
    have hz' : ‖z‖ = R := mem_sphere_zero_iff_norm.1 hz
    have e : (n : ℝ) * ‖z‖ ^ 2 * lam ^ 2 / 2 = i / 2 := by
      rw [hz', hR2]
      field_simp
    calc ‖f z‖ ≤ M * Real.exp (n * ‖z‖ ^ 2 * lam ^ 2 / 2) := hb z
      _ = M * Real.exp (i / 2) := by rw [e]
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hRpos hf.diffContOnCl hsph
  refine hC.trans ?_
  have hA : 0 ≤ (i.factorial : ℝ) * (M * Real.exp (i / 2)) / R ^ i :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)) (pow_nonneg hRpos.le _)
  have hB : 0 ≤ Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M :=
    mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (pow_nonneg hlam.le _)) hM
  refine (pow_le_pow_iff_left₀ hA hB two_ne_zero).1 ?_
  have hs1 : (Real.sqrt (Real.exp 1 * n * n') ^ i) ^ 2 = (Real.exp 1 * n * n') ^ i := by
    rw [← pow_mul, mul_comm i 2, pow_mul, Real.sq_sqrt (by positivity)]
  have hs2 : (R ^ i) ^ 2 = (i / (n * lam ^ 2)) ^ i := by
    rw [← pow_mul, mul_comm i 2, pow_mul, hR2]
  have hs3 : Real.exp (i / 2) ^ 2 = Real.exp 1 ^ i := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have key : ((i.factorial : ℝ)) ^ 2 ≤ ((i : ℝ) * n') ^ i := by
    have h1 : (i.factorial : ℝ) ≤ (i : ℝ) ^ i := by exact_mod_cast Nat.factorial_le_pow i
    have h2 : ((i : ℝ) ^ i) ^ 2 ≤ ((i : ℝ) * n') ^ i := by
      rw [← pow_mul, mul_comm i 2, pow_mul, sq]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hi) hi0'.le) i
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2).trans h2
  have hin : (i : ℝ) ^ i ≠ 0 := pow_ne_zero _ hi0'.ne'
  have hnl : ((n : ℝ) * lam ^ 2) ^ i ≠ 0 := pow_ne_zero _ (mul_pos hn0 hlam2).ne'
  have lhs : ((i.factorial : ℝ) * (M * Real.exp (i / 2)) / R ^ i) ^ 2 =
      (M ^ 2 * Real.exp 1 ^ i * (n : ℝ) ^ i * (lam ^ 2) ^ i) * (i.factorial : ℝ) ^ 2 / (i : ℝ) ^ i := by
    rw [div_pow, mul_pow, mul_pow, hs3, hs2, div_pow]
    field_simp
    ring
  have rhs : (Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M) ^ 2 =
      (M ^ 2 * Real.exp 1 ^ i * (n : ℝ) ^ i * (lam ^ 2) ^ i) * ((i : ℝ) * n') ^ i / (i : ℝ) ^ i := by
    rw [mul_pow, mul_pow, hs1]
    field_simp
    ring
  rw [lhs, rhs]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left key (by positivity)) (pow_nonneg hi0'.le _)

end GlobalTheory.CompanionTheory.Ar.Sl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IteratedDerivBoundGaussianGrowthStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterated_deriv_bound_gaussian_growth : ∀ (f : ℂ → ℂ) (M lam : ℝ) (n n' i : ℕ), Differentiable ℂ f → 0 < lam → 1 ≤ n → 1 ≤ n' → i ≤ n' → (∀ τ, ‖f τ‖ ≤ M * Real.exp (n * ‖τ‖ ^ 2 * lam ^ 2 / 2)) → ‖iteratedDeriv i f 0‖ ≤ Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth | exact GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth <;> assumption)
end
end
