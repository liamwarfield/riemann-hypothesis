module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormTimesFibreClass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLineFirstChernFormsPullbackCell
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGramFlagCellFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGramFlagCellFrame
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pullGram_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ z : CxPts Y.str σ, InCell E E' φ f A u (under z) → pullGram E H φ f hf (upM u * A.map φ) z = fun τ => upM (fun j => ratVal (u j) z) τ * H A (ptMap σ f hf z) τ * (upM (fun j => ratVal (u j) z) τ)ᴴ := by
  intro F _ σ X Y ι _ m E E' φ f hf hR _c A u H hH z hz
  obtain ⟨hA, hB⟩ := hz
  funext τ
  rw [(GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH z).2 A hA _ hB τ]
  have hd : ∀ τ, ((A.map φ) τ).det ≠ 0 := fun τ => by
    change ((A τ).map φ).det ≠ 0
    have := RingHom.map_det (φ : X.Fn →+* Y.Fn) (A τ)
    rw [RingHom.mapMatrix_apply] at this
    change ((A τ).map (φ : X.Fn →+* Y.Fn)).det ≠ 0
    rw [← this]
    exact (map_ne_zero _).2 (Fr.det_ne hA τ)
  have e : upM u * A.map φ * (A.map φ)⁻¹ = upM u := by rw [mul_assoc, Mat.mul_inv hd, mul_one]
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) z
  have h0 : ratVal (0 : Y.Fn) z = 0 := by simpa using hψ 0
  have h1 : ratVal (1 : Y.Fn) z = 1 := by simpa using hψ 1
  have hv : (upM u).map (ratVal · z) τ = upM (fun j => ratVal (u j) z) τ := by
    ext a b
    simp only [Mat.map, upM, upU, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp [h0, h1]
  rw [e, hv]

end GlobalTheory.FlagCell2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGramFlagCellFrameStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullGram_flagCell_frame : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ z : CxPts Y.str σ, InCell E E' φ f A u (under z) → pullGram E H φ f hf (upM u * A.map φ) z = fun τ => upM (fun j => ratVal (u j) z) τ * H A (ptMap σ f hf z) τ * (upM (fun j => ratVal (u j) z) τ)ᴴ := by
  first | exact @GlobalTheory.FlagCell2.pullGram_cell | exact GlobalTheory.FlagCell2.pullGram_cell | (intros; apply GlobalTheory.FlagCell2.pullGram_cell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLineFirstChernFormsPullbackCell
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.GradedPull

theorem ratVal_zero' {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (y : CxPts X.str σ) :
    ratVal (0 : X.Fn) y = 0 := by
  have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial (0 : Γ(X.X, ⊤))
  rw [map_zero, ev_eq mem_ptsIn_top, map_zero] at e
  exact e

theorem ofValues_ddc_eq {n : ℕ} {p u : V n → ℝ} {Φ : V n → V n} {g : V n → ℂ} {z w : V n} (hw : Φ z = w)
    (hu : ContDiffAt ℝ 2 u w) (hΦ : ContDiffAt ℂ 2 Φ z) (hg : ∀ᶠ v in 𝓝 z, DifferentiableAt ℂ g v) (h0 : g z ≠ 0)
    (h : p =ᶠ[𝓝 z] fun v => u (Φ v) - Real.log (‖g v‖ ^ 2)) :
    (ofValues (ddc p z) : Alt n) = pull (fderiv ℂ Φ z) (ofValues (ddc u w) : Ev n) := by
  subst hw
  obtain ⟨U, hU, hUo, hz⟩ := eventually_nhds_iff.1 hg
  have hg2 : ContDiffAt ℂ 2 g z := ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hUo
    fun v hv => (hU v hv).differentiableWithinAt).contDiffAt (hUo.mem_nhds hz)).of_le (by norm_cast)
  have hs : IsSesq (ddc u (Φ z)) := by
    constructor <;> intros <;> simp [ddc] <;> ring
  rw [GlobalTheory.SecForm.pull_ofValues _ _ hs]
  congr 2
  funext ξ η
  have h1 : ContDiffAt ℝ 2 (fun v => u (Φ v)) z := hu.comp z (hΦ.restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ 2 (fun v => Real.log (‖g v‖ ^ 2)) z :=
    ((hg2.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  rw [ddc, ddc, leviForm_congr h, leviForm_sub h1 h2, leviForm_log_normSq_eq_zero hg2 h0, sub_zero,
    leviForm_comp_holo hu hΦ]

theorem grF_eq_pull : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (ε : Fin Y.dim ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ∀ r : Root m, (grF E' (pullGram E H φ f hf) r x : Alt Y.dim) = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (ofValues (ddc (cellPot ε (fun v => H A (c.e.symm v)) r) (cellMap ε f hf c u x.pt)) : Ev Y.dim) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u H hH ε x hx r
  have hM := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  set B₀ := (E'.nonempty (under x.pt)).choose with hB₀
  have hB₀m : B₀ ∈ E'.S (under x.pt) := (E'.nonempty (under x.pt)).choose_spec
  set B := upM u * A.map φ with hB
  have hT : ∀ w : CxPts Y.str σ, B ∈ E'.S (under w) → B₀ ∈ E'.S (under w) →
      HolUnitAt (atlas Y σ) (fun z => ((B₀ * B⁻¹) r.1).map (ratVal · z)) w ∧
      ∀ i j : Fin (m r.1), i < j → ((B₀ * B⁻¹) r.1).map (ratVal · w) i j = 0 := by
    intro w hAw hBw
    have hp := ((Fr.mem_iff hAw).1 hBw) r.1
    refine ⟨GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ Y (m r.1) ((B₀ * B⁻¹) r.1) w (fun i j => mem_O_ratOf.1 (hp.1 i j)) hp.2.1
      (mem_O_ratOf.1 hp.2.2.1), fun i j hij => ?_⟩
    rw [Matrix.map_apply, hp.2.2.2 i j i.2 hij]
    exact ratVal_zero' w
  have hne : ∀ w : CxPts Y.str σ, B ∈ E'.S (under w) → B₀ ∈ E'.S (under w) →
      ((B₀ * B⁻¹) r.1).map (ratVal · w) r.2 r.2 ≠ 0 := fun w h1 h2 => by
    obtain ⟨hol, tri⟩ := hT w h1 h2
    have := hol.1.ne_zero
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => tri i j hij)] at this
    exact Finset.prod_ne_zero_iff.1 this r.2 (Finset.mem_univ _)
  have hπ : Continuous (ptMap σ f hf) := by
    unfold ptMap
    apply GlobalTheory.Points.PtsOver.continuous_map
  have hAπ : A ∈ E.S (under (ptMap σ f hf x.pt)) := hx.1.1
  have hsm := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) _ A hAπ r.1).2 c hx.2).self_of_nhds
  have hb : bsL ε (cellMap ε f hf c u x.pt) = c.e (ptMap σ f hf x.pt) := bsL_pt _ _ _
  have hu := (GlobalTheory.T.contDiffAt_flagCellGradedLinePotential ι m Y.dim X.dim ε (fun v => H A (c.e.symm v)) (cellMap ε f hf c u x.pt) r
    (by rw [hb]; exact hsm.2) (by rw [hb]; exact fun i j => (hsm.1 i j).of_le (by norm_cast))).1
  have hl : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  have ht : Tendsto x.ch.symm (𝓝 x.crd) (𝓝 x.pt) := by
    have := x.ch.continuousAt_symm (x.ch.map_source x.2)
    rwa [ContinuousAt, x.ch.left_inv x.2] at this
  have e1 : ∀ᶠ z in 𝓝 x.pt, InCell E E' φ f A u (under z) :=
    (isOpen_ptsIn (p := Y.str) (σ := σ) ⟨_, (GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u).1⟩).mem_nhds (mem_ptsIn.2 hx.1)
      |> fun h => Filter.mem_of_superset h fun z hz => mem_ptsIn.1 hz
  have e2 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' x.pt B₀ hB₀m
  have e3 : ∀ᶠ z in 𝓝 x.pt, ptMap σ f hf z ∈ c.e.source := hπ.continuousAt.eventually (c.e.open_source.mem_nhds hx.2)
  refine ofValues_ddc_eq (g := fun v => ((B₀ * B⁻¹) r.1).map (ratVal · (x.ch.symm v)) r.2 r.2)
    (congrArg (cellMap ε f hf c u) hl) hu (GlobalTheory.T.flagCellCoordinates_contDiffAt_etaleChart F σ X Y ι m E E' φ f hf hR c A u _ ε x hx)
    ((hT _ hx.1.2 hB₀m).1.2 x.1.1 x.2 r.2 r.2) (by rw [hl]; exact hne _ hx.1.2 hB₀m) ?_
  filter_upwards [ht.eventually e1, ht.eventually e2, ht.eventually e3] with v h1 h2 h3
  obtain ⟨hol, tri⟩ := hT _ h1.2 h2
  have hpd := hM.posDef _ B h1.2 r.1
  have e := hM.trans _ B h1.2 B₀ h2 r.1
  have e' := (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ hpd tri hol.1).2 r.2
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hpd).2.1 r.2).1
  have eg := congrFun (GlobalTheory.T.pullGram_flagCell_frame F σ X Y ι m E E' φ f hf hR c A u H hH _ h1) r.1
  have ec : cellPot ε (fun v => H A (c.e.symm v)) r (cellMap ε f hf c u (x.ch.symm v)) =
      -Real.log (grD (pullGram E H φ f hf B (x.ch.symm v) r.1) r.2) := by
    rw [hB, eg, cellPot, cellMap, bsL_pt, fb_pt, c.e.left_inv h3]
  show -Real.log (grD (pullGram E H φ f hf B₀ (x.ch.symm v) r.1) r.2) =
    cellPot ε (fun v => H A (c.e.symm v)) r (cellMap ε f hf c u (x.ch.symm v)) - _
  rw [ec, e]
  erw [e']
  rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hne _ h1.2 h2))) hpos.ne']
  ring

end GlobalTheory.FlagCell2.GradedPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLineFirstChernFormsPullbackCellStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_line_first_chern_forms_pullback_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (ε : Fin Y.dim ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ∀ r : Root m, (grF E' (pullGram E H φ f hf) r x : Alt Y.dim) = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (ofValues (ddc (cellPot ε (fun v => H A (c.e.symm v)) r) (cellMap ε f hf c u x.pt)) : Ev Y.dim) := by
  first | exact @GlobalTheory.FlagCell2.GradedPull.grF_eq_pull | exact GlobalTheory.FlagCell2.GradedPull.grF_eq_pull | (intros; apply GlobalTheory.FlagCell2.GradedPull.grF_eq_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackBaseFormFlagCellCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompLinear
open GlobalTheory GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem pull_comp_linear : ∀ (n n' n'' : ℕ) (L : V n →L[ℂ] V n') (L' : V n' →L[ℂ] V n'') (α : Alt n''),
    pull (L'.comp L) α = pull L (pull L' α) :=
  fun n n' n'' L L' α => GlobalTheory.CxForm.pull_comp n'' n' n L L' α

end GlobalTheory.FlagCell2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompLinearStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackComplexFormsLinearMap_comp_linear : ∀ (n n' n'' : ℕ) (L : V n →L[ℂ] V n') (L' : V n' →L[ℂ] V n'') (α : Alt n''), pull (L'.comp L) α = pull L (pull L' α) := by
  first | exact @GlobalTheory.FlagCell2.pull_comp_linear | exact GlobalTheory.FlagCell2.pull_comp_linear | (intros; apply GlobalTheory.FlagCell2.pull_comp_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackBaseFormFlagCellCoordinates
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pullback_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (α : (atlas X σ).Fld), (atlas X σ).IsForm α → ∀ x : (atlas Y σ).Pt, x.pt ∈ cellSet E E' φ f hf c A u → (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α x = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (pull (bsL ε) ((atlas X σ).loc α c (bsL ε (cellMap ε f hf c u x.pt)))) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u n ε α hα x hx
  have hs : ptMap σ f hf x.pt ∈ ((atlas X σ).e c).source := hx.2
  rw [GlobalTheory.CxForm.pullback_eq_chart _ _ _ _ (atlas X σ) (atlas Y σ) (ptMap σ f hf) α (GlobalTheory.T.varietyComplexPointsMap_isHolomorphic F σ X Y f hf) hα x c hs]
  have hb : bsL ε (cellMap ε f hf c u x.pt) = c.e (ptMap σ f hf x.pt) := bsL_pt _ _ _
  have hloc : (atlas X σ).loc α c (c.e (ptMap σ f hf x.pt)) = α ⟨(c, ptMap σ f hf x.pt), hs⟩ :=
    (atlas X σ).loc_crd α ⟨(c, ptMap σ f hf x.pt), hs⟩
  rw [hb, hloc, ← GlobalTheory.T.pullbackComplexFormsLinearMap_comp_linear]
  congr 1
  have he : (atlas X σ).e c ∘ ptMap σ f hf ∘ x.ch.symm = bsL ε ∘ (cellMap ε f hf c u ∘ x.ch.symm) := by
    funext w
    simp only [Function.comp_apply, cellMap, bsL_pt]
    rfl
  have hd : DifferentiableAt ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd :=
    (GlobalTheory.T.flagCellCoordinates_contDiffAt_etaleChart F σ X Y ι m E E' φ f hf hR c A u n ε x hx).differentiableAt (by norm_num)
  rw [he, fderiv_comp x.crd (bsL ε).differentiableAt hd, ContinuousLinearMap.fderiv]

end GlobalTheory.FlagCell2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackBaseFormFlagCellCoordinatesStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_base_form_flag_cell_coordinates : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (α : (atlas X σ).Fld), (atlas X σ).IsForm α → ∀ x : (atlas Y σ).Pt, x.pt ∈ cellSet E E' φ f hf c A u → (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α x = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (pull (bsL ε) ((atlas X σ).loc α c (bsL ε (cellMap ε f hf c u x.pt)))) := by
  first | exact @GlobalTheory.FlagCell2.pullback_cell | exact GlobalTheory.FlagCell2.pullback_cell | (intros; apply GlobalTheory.FlagCell2.pullback_cell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralFlagCellFibreDensityEqBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingCurry
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section
namespace GlobalTheory.FibDensMass

section Curry
variable {ι : Type} [Fintype ι] {κ : ι → Type} [∀ i, Fintype (κ i)] {Y : (i : ι) → κ i → Type}
  [∀ i j, MeasurableSpace (Y i j)]

theorem measurePreserving_curry (μ : ∀ i j, Measure (Y i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry Y) (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2)
      (Measure.pi fun i => Measure.pi fun j => μ i j) := by
  refine ⟨(MeasurableEquiv.piCurry Y).measurable, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.univ.pi '' Set.univ.pi fun j => {s : Set (Y i j) | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun j => (μ i j).toFiniteSpanningSetsIn) fun s hs => ?_
  choose S hS hSs using hs
  have hpre : (MeasurableEquiv.piCurry Y) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun p : (i : ι) × κ i => S p.1 p.2 := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi, ← hSs, MeasurableEquiv.piCurry_apply, Sigma.forall]
    rfl
  rw [Measure.map_apply (MeasurableEquiv.piCurry Y).measurable (MeasurableSet.univ_pi fun i => by
      rw [← hSs i]; exact MeasurableSet.univ_pi fun j => hS i j (Set.mem_univ j)), hpre, Measure.pi_pi,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hSs i, Measure.pi_pi]

end Curry

theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]
    · refine lintegral_congr fun a => ?_
      rw [Fin.prod_univ_succ]
      rfl
    · exact Finset.aemeasurable_fun_prod _ fun i _ =>
        (hf _).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)

theorem lintegral_fintype_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod fun i => hf _

theorem block_mass (s : ℕ) (A : Matrix (Fin s) (Fin s) ℂ) (hA : A.PosDef) :
    ∫⁻ w : Low s → ℂ, ENNReal.ofReal (GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) *
      GlobalTheory.FlagFibre.dens Aᵀ w) = 1 := by
  have hAt : Aᵀ.PosDef := hA.transpose
  have hd : 0 < A.det.re := (GlobalTheory.FlagFibre.FlagInt.re_facts hA).1
  have hc := GlobalTheory.TrueCx.flagConst_pos s
  have hk : 0 ≤ GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) := by positivity
  simp_rw [ENNReal.ofReal_mul hk]
  rw [lintegral_const_mul _ (GlobalTheory.FlagFibre.measurable_dens _).ennreal_ofReal,
    GlobalTheory.FlagFibre.FlagInt.lintegral_dens s Aᵀ hAt, Matrix.det_transpose, ← ENNReal.ofReal_mul hk]
  rw [← ENNReal.ofReal_one]
  congr 1
  have : A.det.re ^ ((s : ℤ) - 1) * A.det.re ^ (1 - (s : ℤ)) = 1 := by
    rw [← zpow_add₀ hd.ne']; simp
  calc GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) * (A.det.re ^ (1 - (s : ℤ)) / GlobalTheory.TrueCx.flagConst s)
        = (A.det.re ^ ((s : ℤ) - 1) * A.det.re ^ (1 - (s : ℤ))) * (GlobalTheory.TrueCx.flagConst s / GlobalTheory.TrueCx.flagConst s) := by ring
    _ = 1 := by rw [this, div_self hc.ne', one_mul]

end GlobalTheory.FibDensMass

open GlobalTheory.FibDensMass in
theorem GlobalTheory.FlagCell2.fibDens_mass : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (G : Mat m ℂ), (∀ τ, (G τ).PosDef) → (∀ y, 0 ≤ fibDens G y) ∧ ∫⁻ y : Cell m → ℂ, ENNReal.ofReal (fibDens G y) = 1 := by
  intro ι _ m G hG
  have hnn : ∀ τ (w : Low (m τ) → ℂ), 0 ≤ GlobalTheory.TrueCx.flagConst (m τ) * (G τ).det.re ^ ((m τ : ℤ) - 1) *
      GlobalTheory.FlagFibre.dens (G τ)ᵀ w := fun τ w =>
    mul_nonneg (mul_nonneg (GlobalTheory.TrueCx.flagConst_pos _).le
      (zpow_nonneg (GlobalTheory.FlagFibre.FlagInt.re_facts (hG τ)).1.le _)) (GlobalTheory.FlagFibre.dens_nonneg _ _)
  refine ⟨fun y => Finset.prod_nonneg fun τ _ => hnn τ _, ?_⟩
  have hmp := measurePreserving_curry (Y := fun (τ : ι) (_ : Low (m τ)) => ℂ) (fun _ _ => (volume : Measure ℂ))
  let g : ∀ τ, (Low (m τ) → ℂ) → ℝ≥0∞ := fun τ w => ENNReal.ofReal (GlobalTheory.TrueCx.flagConst (m τ) *
    (G τ).det.re ^ ((m τ : ℤ) - 1) * GlobalTheory.FlagFibre.dens (G τ)ᵀ w)
  have hpt : ∀ y : Cell m → ℂ, ENNReal.ofReal (fibDens G y) = ∏ τ, g τ (MeasurableEquiv.piCurry (fun (τ : ι) (_ : Low (m τ)) => ℂ) y τ) := by
    intro y
    simp only [fibDens, g]
    rw [ENNReal.ofReal_prod_of_nonneg fun τ _ => hnn τ _]
    rfl
  simp_rw [hpt]
  rw [show (volume : Measure (Cell m → ℂ)) = Measure.pi fun p : Cell m => (volume : Measure ℂ) from rfl,
    hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (fun z => ∏ τ, g τ (z τ))]
  rw [lintegral_fintype_prod (μ := fun τ => Measure.pi fun _ : Low (m τ) => (volume : Measure ℂ))
    fun τ => ((GlobalTheory.FlagFibre.measurable_dens _).const_mul _).ennreal_ofReal.aemeasurable]
  exact Finset.prod_eq_one fun τ _ => block_mass (m τ) (G τ) (hG τ)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPtSplit
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

noncomputable def ptEquiv (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) : V d × (J → ℂ) ≃ᵐ V n :=
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm (MeasurableEquiv.refl (J → ℂ))).trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm).trans
    ((MeasurableEquiv.arrowCongr' ε.symm (MeasurableEquiv.refl ℂ)).trans (MeasurableEquiv.toLp 2 (Fin n → ℂ)))

theorem ptEquiv_apply (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (x : V d × (J → ℂ)) :
    ptEquiv n d J ε x = pt ε x.1 x.2 := by
  ext i
  change (Equiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm (x.1.ofLp, x.2) (ε i) = Sum.elim (fun a => x.1.ofLp a) x.2 (ε i)
  cases ε i <;> rfl

theorem measurePreserving_pt_split : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J),
    MeasurePreserving (fun x : V d × (J → ℂ) => pt ε x.1 x.2) volume volume ∧
      MeasurableEmbedding (fun x : V d × (J → ℂ) => pt ε x.1 x.2) := by
  intro n d J _ ε
  have e : (fun x : V d × (J → ℂ) => pt ε x.1 x.2) = ⇑(ptEquiv n d J ε) := by
    funext x; exact (ptEquiv_apply n d J ε x).symm
  rw [e]
  refine ⟨?_, (ptEquiv n d J ε).measurableEmbedding⟩
  have h1 : MeasurePreserving (fun z : V d => z.ofLp) volume volume := volume_preserving_ofLp_complex (Fin d)
  have h2 := h1.prod (MeasurePreserving.id (volume : Measure (J → ℂ)))
  have h3 := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin d ⊕ J => ℂ)).comp h2
  have h4 := (volume_preserving_arrowCongr' ε.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm (volume_preserving_ofLp_complex (Fin n))
  exact h5.comp h4

end GlobalTheory.FlagCell2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralFlagCellFibreDensityEqBase
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem aemeasurable_fibDens {ι : Type} [Fintype ι] {m : ι → ℕ} {d : ℕ} (G : V d → Mat m ℂ) (O : Set (V d))
    (hO : IsOpen O) (hG : ∀ τ i j, ContinuousOn (fun v => G v τ i j) O) :
    AEMeasurable (fun x : V d × (Cell m → ℂ) => fibDens (G x.1) x.2)
      (volume.restrict (O ×ˢ (Set.univ : Set (Cell m → ℂ)))) := by
  have hS : MeasurableSet (O ×ˢ (Set.univ : Set (Cell m → ℂ))) := hO.measurableSet.prod MeasurableSet.univ
  have hGτ : ∀ τ, ContinuousOn (fun x : V d × (Cell m → ℂ) => G x.1 τ) (O ×ˢ Set.univ) := by
    intro τ
    have h : ContinuousOn (fun v => G v τ) O :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hG τ i j
    exact h.comp continuous_fst.continuousOn fun x hx => hx.1
  unfold fibDens
  apply Finset.aemeasurable_fun_prod
  intro τ _
  refine AEMeasurable.mul (AEMeasurable.mul aemeasurable_const ?_) ?_
  · have h := ((continuous_id.matrix_det).comp_continuousOn (hGτ τ))
    exact ((Complex.continuous_re.comp_continuousOn h).aemeasurable hS).pow_const _
  · unfold GlobalTheory.FlagFibre.dens
    apply Finset.aemeasurable_fun_prod
    intro i _
    refine AEMeasurable.pow_const (AEMeasurable.norm ?_) _
    have hc : Continuous fun p : Matrix (Fin (m τ)) (Fin (m τ)) ℂ × (Low (m τ) → ℂ) =>
        ReciprocityTheory.ChartRestriction.G.FD.lminor ((GlobalTheory.FlagFibre.uni p.2)ᴴ * p.1ᵀ * GlobalTheory.FlagFibre.uni p.2) i.castSucc := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
      exact ((((GlobalTheory.FlagFibre.continuous_uni.comp continuous_snd).matrix_conjTranspose.matrix_mul
        continuous_fst.matrix_transpose).matrix_mul (GlobalTheory.FlagFibre.continuous_uni.comp continuous_snd)).matrix_submatrix
        _ _).matrix_det
    have h2 : ContinuousOn (fun x : V d × (Cell m → ℂ) => (G x.1 τ, fun s => x.2 ⟨τ, s⟩)) (O ×ˢ Set.univ) :=
      (hGτ τ).prodMk (by fun_prop : Continuous fun x : V d × (Cell m → ℂ) => fun s => x.2 ⟨τ, s⟩).continuousOn
    exact (hc.comp_continuousOn h2).aemeasurable hS

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem setLIntegral_fibDens : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (δ : V d → ℝ) (O K : Set (V d)), IsOpen O → MeasurableSet K → K ⊆ O → ContinuousOn δ O → (∀ τ i j, ContinuousOn (fun v => G v τ i j) O) → (∀ v ∈ O, ∀ τ, (G v τ).PosDef) → ∫⁻ w in bsL ε ⁻¹' K, ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)) = ∫⁻ v in K, ENNReal.ofReal (δ v) := by
  intro ι _ m n d ε G δ O K hO hK hKO hδ hG hpos
  have hmp := (GlobalTheory.FlagCell2.measurePreserving_pt_split n d (Cell m) ε).1
  have hb : Measurable (bsL ε) := (bsL ε).continuous.measurable
  have hm := hmp.restrict_preimage (hb hK)
  have hs : (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) ⁻¹' (bsL ε ⁻¹' K) = K ×ˢ Set.univ := by
    ext x
    simp [bsL_pt]
  rw [hs, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hm
  set F : V d × (Cell m → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal (δ x.1 * fibDens (G x.1) x.2) with hF
  have hS : MeasurableSet (O ×ˢ (Set.univ : Set (Cell m → ℂ))) := hO.measurableSet.prod MeasurableSet.univ
  have hFO : AEMeasurable F (volume.restrict (O ×ˢ (Set.univ : Set (Cell m → ℂ)))) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable (AEMeasurable.mul ?_ (aemeasurable_fibDens G O hO hG))
    exact (hδ.comp continuous_fst.continuousOn (fun x (hx : x ∈ O ×ˢ (Set.univ : Set (Cell m → ℂ))) => hx.1)).aemeasurable hS
  have hFK : AEMeasurable F ((volume.restrict K).prod volume) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Cell m → ℂ))), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
    exact hFO.mono_measure (Measure.restrict_mono (Set.prod_mono hKO subset_rfl) le_rfl)
  have e1 : (fun w => ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w))) ∘
      (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) = F := by
    funext x
    simp [hF, bsL_pt, fb_pt]
  have hH : AEMeasurable (fun w => ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)))
      (Measure.map (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) ((volume.restrict K).prod volume)) := by
    rw [(GlobalTheory.FlagCell2.measurePreserving_pt_split n d (Cell m) ε).2.aemeasurable_map_iff, e1]
    exact hFK
  rw [← hm.map_eq, lintegral_map' hH hm.measurable.aemeasurable]
  refine (lintegral_congr fun a => congrFun e1 a).trans ?_
  rw [lintegral_prod _ hFK]
  refine setLIntegral_congr_fun hK fun v hv => ?_
  obtain ⟨h0, h1⟩ := GlobalTheory.FlagCell2.fibDens_mass ι m (G v) (hpos v (hKO hv))
  simp only [hF]
  simp_rw [ENNReal.ofReal_mul' (h0 _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1, mul_one]

end GlobalTheory.FlagCell2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralFlagCellFibreDensityEqBaseStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setLIntegral_flagCellFibreDensity_eq_base : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (δ : V d → ℝ) (O K : Set (V d)), IsOpen O → MeasurableSet K → K ⊆ O → ContinuousOn δ O → (∀ τ i j, ContinuousOn (fun v => G v τ i j) O) → (∀ v ∈ O, ∀ τ, (G v τ).PosDef) → ∫⁻ w in bsL ε ⁻¹' K, ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)) = ∫⁻ v in K, ENNReal.ofReal (δ v) := by
  first | exact @GlobalTheory.FlagCell2.setLIntegral_fibDens | exact GlobalTheory.FlagCell2.setLIntegral_fibDens | (intros; apply GlobalTheory.FlagCell2.setLIntegral_fibDens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRefinementBundleDimEqBaseAddCardAboveDiagona
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRefinementBundleDimEqBaseAddCardAboveDiagona
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section

namespace GlobalTheory.FlagCell2.Dim

theorem card_low (s : ℕ) : Fintype.card (Low s) = s.choose 2 := by
  have h₁ : Fintype.card (Low s) = ∑ i : Fin s, (Finset.Ioi i).card := by
    rw [← Finset.card_sigma, ← Finset.card_univ]
    refine Finset.card_bij' (fun s _ => ⟨s.1.2, s.1.1⟩) (fun t ht => ⟨(t.2, t.1), by simpa using ht⟩) ?_ ?_ ?_ ?_ <;>
      simp
  rw [h₁, Nat.choose_two_right]
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => s - 1 - i), Finset.sum_range_reflect (fun i => i), Finset.sum_range_id]

theorem dim_eq_of_refines {F : Type} [Field F] [CharZero F] {X Y Y' : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {S : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X}
    {S' : Fr (ratOf Y') m m} {φ' : X.Fn →ₐ[F] Y'.Fn} {f' : Y'.X ⟶ X.X}
    (hR : Refines E S φ f) (hR' : Refines E S' φ' f') : Y.dim = Y'.dim := by
  have R₁ := hR.reps
  have R₂ := hR'.reps
  obtain ⟨ψ, hψ, hG⟩ := exists_fieldMap_coBear_generic F ι m X Y Y' E S φ f S' φ' f' R₁ R₂
  obtain ⟨h, hh⟩ := GlobalTheory.ZH.RatModel.exists_isHom_of_map_O F Y'.Fn (ratOf Y') Y.Fn (ratOf Y) ψ
    (dominates_O F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ ψ hψ hG)
  have hf : h ≫ f' = f := by
    have h1 := R₂.1.comp hh
    rw [hψ] at h1
    exact h1.unique R₁.1
  have hb := CoBear₂ F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ h hf
    (coBear_comp_of_isHom F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ ψ hψ hG h hh)
  change Y.X ⟶ Y'.X at h
  have : IsIso h := GlobalTheory.BijPointsIso.isIso_of_bijective_points F Y Y' h hh.inducedModelMorphism_comp_structureMap fun K _ _ => hb K
  have hd : topologicalKrullDim Y.X = topologicalKrullDim Y'.X :=
    IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso h)).isHomeomorph
  rw [Y.topologicalKrullDim_eq, Y'.topologicalKrullDim_eq] at hd
  exact_mod_cast hd

theorem main : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → Y.dim = X.dim + Fintype.card (Cell m) := by
  intro F _ σ X Y ι _ m E E' φ f _ hR
  have : CharZero F := σ.charZero
  obtain ⟨Y', φ', f', S', hd, hR'⟩ := tower _ (ratOf X) X.dim E (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  rw [dim_eq_of_refines hR hR', hd, Fintype.card_sigma]
  simp only [card_low, Pi.zero_apply, Nat.sub_zero]

end GlobalTheory.FlagCell2.Dim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRefinementBundleDimEqBaseAddCardAboveDiagonaStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRefinementBundle_dim_eq_base_add_card_aboveDiagonal : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → Y.dim = X.dim + Fintype.card (Cell m) := by
  first | exact @GlobalTheory.FlagCell2.Dim.main | exact GlobalTheory.FlagCell2.Dim.main | (intros; apply GlobalTheory.FlagCell2.Dim.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackAevalEvenComplexForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackAevalEvenComplexForms
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem GlobalTheory.FlagCell2.pull_aeval_even : ∀ (n n' : ℕ) (L : V n →L[ℂ] V n') (κ : Type) (w : κ → Ev n) (w' : κ → Ev n') (P : MvPolynomial κ ℂ), (∀ x, (w x : Alt n) = pull L (w' x : Alt n')) → ((aeval w P : Ev n) : Alt n) = pull L ((aeval w' P : Ev n') : Alt n') := by
  intro n n' L κ w w' P h
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C]
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, AlgHom.commutes]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), Subalgebra.coe_add, Subalgebra.coe_add, map_add (f := _), hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Subalgebra.coe_mul,
      Subalgebra.coe_mul, map_mul, hp, h i]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackAevalEvenComplexFormsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_aeval_evenComplexForms : ∀ (n n' : ℕ) (L : V n →L[ℂ] V n') (κ : Type) (w : κ → Ev n) (w' : κ → Ev n') (P : MvPolynomial κ ℂ), (∀ x, (w x : Alt n) = pull L (w' x : Alt n')) → ((aeval w P : Ev n) : Alt n) = pull L ((aeval w' P : Ev n') : Alt n') := by
  first | exact @GlobalTheory.FlagCell2.pull_aeval_even | exact GlobalTheory.FlagCell2.pull_aeval_even | (intros; apply GlobalTheory.FlagCell2.pull_aeval_even <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartSubsetChartEqLintegralImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartSubsetChartEqLintegralImage
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlagCell2

theorem part_subset_chart : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (s : ℤˣ) (i : A.ι) (T : Set M), MeasurableSet T → T ⊆ (A.e i).source → A.part β s T = ∫⁻ v in A.e i '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β i v)).re) := by
  intro M _ _ _ _ _ n A β hβ s i T hT hTi
  set ρ : A.ι → M → ENNReal := fun k y => ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β k (A.e k y))).re) with hρ
  have hp : A.part β s = ChartGlue.glueMeas A.e ρ := rfl
  have hρc : ∀ k l y, y ∈ (A.e k).source → y ∈ (A.e l).source →
      ρ k y = ENNReal.ofReal (‖ChartGlue.transDet (A.e k) (A.e l) y‖ ^ 2) * ρ l y := by
    intro k l y hk hl
    have h1 := A.loc_crd β (⟨(k, y), hk⟩ : A.Pt)
    have h2 := A.loc_crd β (⟨(l, y), hl⟩ : A.Pt)
    have h3 := hβ.compat (⟨(k, y), hk⟩ : A.Pt) ⟨(l, y), hl⟩ rfl
    simp only [hρ]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ChartGlue.transDet]
    ring
  rw [hp, ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hT hTi, ChartGlue.chartMeas_apply_of_subset _ _ hT hTi]
  refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hT hTi) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [hρ, (A.e i).left_inv (hTi hy)]

end GlobalTheory.FlagCell2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartSubsetChartEqLintegralImageStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formPart_subset_chart_eq_lintegral_image : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (s : ℤˣ) (i : A.ι) (T : Set M), MeasurableSet T → T ⊆ (A.e i).source → A.part β s T = ∫⁻ v in A.e i '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β i v)).re) := by
  first | exact @GlobalTheory.FlagCell2.part_subset_chart | exact GlobalTheory.FlagCell2.part_subset_chart | (intros; apply GlobalTheory.FlagCell2.part_subset_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartEqLintegralImageInjectiveHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartEqLintegralImageInjectiveHolomorphic
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

open Function

namespace GlobalTheory.FlagCell2.ChangeOfVariables

theorem part_eq_lintegral_image : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (Ω : Set M) (Φ : M → V n) (γ : V n → Alt n), IsOpen Ω → Set.InjOn Φ Ω → (∀ x : A.Pt, x.pt ∈ Ω → DifferentiableAt ℂ (Φ ∘ x.ch.symm) x.crd ∧ β x = pull (fderiv ℂ (Φ ∘ x.ch.symm) x.crd) (γ (Φ x.pt))) → ∀ (s : ℤˣ) (T : Set M), MeasurableSet T → T ⊆ Ω → A.part β s T = ∫⁻ v in Φ '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
  intro M _ _ _ _ _ n A β hβ Ω Φ γ hΩ hinj hloc s T hT hTΩ
  set ρ : A.ι → M → ℝ≥0∞ := fun k y => ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β k (A.e k y))).re) with hρ
  have hp : A.part β s = ChartGlue.glueMeas A.e ρ := rfl
  have hρc : ∀ k l y, y ∈ (A.e k).source → y ∈ (A.e l).source →
      ρ k y = ENNReal.ofReal (‖ChartGlue.transDet (A.e k) (A.e l) y‖ ^ 2) * ρ l y := by
    intro k l y hk hl
    have h1 := A.loc_crd β (⟨(k, y), hk⟩ : A.Pt)
    have h2 := A.loc_crd β (⟨(l, y), hl⟩ : A.Pt)
    have h3 := hβ.compat (⟨(k, y), hk⟩ : A.Pt) ⟨(l, y), hl⟩ rfl
    simp only [hρ]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ChartGlue.transDet]
    ring

  have chart : ∀ (i : A.ι) (P : Set M), MeasurableSet P → P ⊆ (A.e i).source → P ⊆ Ω →
      MeasurableSet (Φ '' P) ∧ A.part β s P =
        ∫⁻ v in Φ '' P, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
    intro i P hP hPs hPΩ
    set g : V n → V n := Φ ∘ (A.e i).symm with hg
    have hQ : MeasurableSet (A.e i '' P) := ChartGlue.measurableSet_image (A.e i) hP hPs
    have hder : ∀ v ∈ A.e i '' P, HasFDerivWithinAt g ((fderiv ℂ g v).restrictScalars ℝ) (A.e i '' P) v := by
      rintro _ ⟨y, hy, rfl⟩
      exact ((hloc ⟨(i, y), hPs hy⟩ (hPΩ hy)).1.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinjg : Set.InjOn g (A.e i '' P) := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyz
      simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy), (A.e i).left_inv (hPs hz)] at hyz
      rw [hinj (hPΩ hy) (hPΩ hz) hyz]
    have himg : Φ '' P = g '' (A.e i '' P) := by
      rw [Set.image_image]
      exact Set.image_congr fun y hy => by simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy)]
    refine ⟨himg ▸ measurable_image_of_fderivWithin hQ hder hinjg, ?_⟩
    rw [hp, ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hP hPs, ChartGlue.chartMeas_apply_of_subset _ _ hP hPs, himg,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hQ hder hinjg]
    refine setLIntegral_congr_fun hQ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hx := hloc ⟨(i, y), hPs hy⟩ (hPΩ hy)
    have hl := A.loc_crd β (⟨(i, y), hPs hy⟩ : A.Pt)
    have hdet : ((fderiv ℂ g (A.e i y)).restrictScalars ℝ).det = Algebra.norm ℝ (fderiv ℂ g (A.e i y)).det :=
      LinearMap.det_restrictScalars (f := (fderiv ℂ g (A.e i y) : V n →ₗ[ℂ] V n))
    have hx2 : β ⟨(i, y), hPs hy⟩ = pull (fderiv ℂ g (A.e i y)) (γ (Φ y)) := hx.2
    have hgy : g (A.e i y) = Φ y := by simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy)]
    beta_reduce
    rw [hdet, hgy]
    simp only [hρ, (A.e i).left_inv (hPs hy)]
    erw [hl, hx2, dens_pull]
    rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity),
      Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

  rcases Set.eq_empty_or_nonempty T with rfl | ⟨y₀, -⟩
  · simp
  obtain ⟨C, hCc, hCU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun j => (A.e j).source)
    (fun j => (A.e j).open_source)
  obtain ⟨f, hf⟩ := (hCc.insert (A.cover y₀).choose).exists_eq_range (Set.insert_nonempty _ _)
  set U : ℕ → Set M := fun k => (A.e (f k)).source with hU
  have hUo : ∀ k, IsOpen (U k) := fun k => (A.e (f k)).open_source
  set P : ℕ → Set M := fun k => T ∩ disjointed U k with hPdef
  have hPm : ∀ k, MeasurableSet (P k) := fun k =>
    hT.inter (MeasurableSet.disjointed (fun k => (hUo k).measurableSet) k)
  have hPU : ∀ k, P k ⊆ U k := fun k => Set.inter_subset_right.trans (disjointed_subset U k)
  have hPΩ : ∀ k, P k ⊆ Ω := fun k => Set.inter_subset_left.trans hTΩ
  have hPd : Pairwise (Disjoint on P) := (disjoint_disjointed U).mono fun k l h =>
    h.mono Set.inter_subset_right Set.inter_subset_right
  have hTP : T = ⋃ k, P k := by
    rw [← Set.inter_iUnion, iUnion_disjointed, eq_comm, Set.inter_eq_left]
    intro y _
    have hy : y ∈ ⋃ j, (A.e j).source := Set.mem_iUnion.2 (A.cover y)
    rw [← hCU] at hy
    obtain ⟨l, hl, hy⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨k, rfl⟩ := hf.le (Set.mem_insert_of_mem _ hl)
    exact Set.mem_iUnion.2 ⟨k, hy⟩
  have hIm : ∀ k, MeasurableSet (Φ '' P k) := fun k => (chart (f k) (P k) (hPm k) (hPU k) (hPΩ k)).1
  have hId : Pairwise (Disjoint on fun k => Φ '' P k) := by
    intro k l hkl
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have := hinj (hPΩ l hy) (hPΩ k hx) hxy
    subst this
    exact Set.disjoint_left.1 (hPd hkl) hx hy
  rw [hTP, Set.image_iUnion, measure_iUnion hPd hPm, lintegral_iUnion hIm hId]
  exact tsum_congr fun k => (chart (f k) (P k) (hPm k) (hPU k) (hPΩ k)).2

end GlobalTheory.FlagCell2.ChangeOfVariables
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartEqLintegralImageInjectiveHolomorphicStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formPart_eq_lintegral_image_injective_holomorphic : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (Ω : Set M) (Φ : M → V n) (γ : V n → Alt n), IsOpen Ω → Set.InjOn Φ Ω → (∀ x : A.Pt, x.pt ∈ Ω → DifferentiableAt ℂ (Φ ∘ x.ch.symm) x.crd ∧ β x = pull (fderiv ℂ (Φ ∘ x.ch.symm) x.crd) (γ (Φ x.pt))) → ∀ (s : ℤˣ) (T : Set M), MeasurableSet T → T ⊆ Ω → A.part β s T = ∫⁻ v in Φ '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
  first | exact @GlobalTheory.FlagCell2.ChangeOfVariables.part_eq_lintegral_image | exact GlobalTheory.FlagCell2.ChangeOfVariables.part_eq_lintegral_image | (intros; apply GlobalTheory.FlagCell2.ChangeOfVariables.part_eq_lintegral_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartComplComplexPointsInOpenEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartComplComplexPointsInOpenEqZero
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2Null

theorem part_compl_ptsIn : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : Var F) (β : (atlas Y σ).Fld) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ s : ℤˣ, (atlas Y σ).part β s (ptsIn Y.str σ W)ᶜ = 0 := by
  intro F _ σ Y β W hW s
  exact GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl fun c =>
    GlobalTheory.Mean4O.CoverInt.volume_image_compl_ptsIn F Y.X Y.str σ σ.injective
      (fun W hW => (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str W).injective) W hW _ c

end GlobalTheory.FlagCell2Null
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartComplComplexPointsInOpenEqZeroStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formPart_compl_complexPointsInOpen_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : Var F) (β : (atlas Y σ).Fld) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ s : ℤˣ, (atlas Y σ).part β s (ptsIn Y.str σ W)ᶜ = 0 := by
  first | exact @GlobalTheory.FlagCell2Null.part_compl_ptsIn | exact GlobalTheory.FlagCell2Null.part_compl_ptsIn | (intros; apply GlobalTheory.FlagCell2Null.part_compl_ptsIn <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.LocFib

theorem continuousOn_dens {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α)
    (i : A.ι) : ContinuousOn (fun v => (dens (A.loc α i v)).re) (A.e i).target :=
  Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)


set_option maxHeartbeats 800000 in
theorem part_preimage : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).IsForm ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) → ∀ (s : ℤˣ) (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (O : Set (CxPts X.str σ)), IsOpen O → O ⊆ c.e.source → (∀ x ∈ O, A ∈ E.S (under x)) → ∀ T, MeasurableSet T → T ⊆ O → (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s (ptMap σ f hf ⁻¹' T) = (atlas X σ).part α s T := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH α hα hβ s c A O hO hOc hOA T hT hTO
  rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  haveI : T2Space (CxPts X.str σ) := CxPts.t2Space _ _
  haveI : T2Space (CxPts Y.str σ) := CxPts.t2Space _ _
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_genericPoint_flag_in_cell_of_frame F X Y ι m E E' φ f hR _ A (hOA x₀ (hTO hx₀))
  have hdim := GlobalTheory.T.flagRefinementBundle_dim_eq_base_add_card_aboveDiagonal F σ X Y ι m E E' φ f hf hR
  let ε : Fin Y.dim ≃ Fin X.dim ⊕ Cell m := Fintype.equivOfCardEq (by simp [hdim])
  obtain ⟨hopen, hinj, himg⟩ := GlobalTheory.T.flagCell_coords_bijective_onto_chart_prod F σ X Y ι m E E' φ f hf hR c A u hu _ ε
  have hW := (GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u).1
  have hπ : Continuous (ptMap σ f hf) := GlobalTheory.Points.PtsOver.continuous_map f hf _
  have hTm : MeasurableSet (ptMap σ f hf ⁻¹' T) := hπ.measurable hT
  have hnull := GlobalTheory.T.formPart_compl_complexPointsInOpen_eq_zero F σ Y ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
    evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) ⟨_, hW⟩ hu s
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
    evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s := ⟨_, rfl⟩
  rw [← hμ] at hnull ⊢
  have h1 : μ (ptMap σ f hf ⁻¹' T) = μ (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) := by
    refine (measure_inter_add_diff (ptMap σ f hf ⁻¹' T) hopen.measurableSet).symm.trans ?_
    have h0 : μ (ptMap σ f hf ⁻¹' T \ cellSet E E' φ f hf c A u) = 0 :=
      by
      refine measure_mono_null (fun y hy => ?_) hnull
      intro hy'
      have h2 : under y ∈ (⟨_, hW⟩ : Y.X.Opens) := mem_ptsIn.1 hy'
      have h3 : InCell E E' φ f A u (under y) := h2
      exact hy.2 ⟨h3, hOc (hTO hy.1)⟩
    rw [h0, add_zero]
  have hmet := GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH)
  have hG : ∀ v ∈ c.e '' O, ∀ τ, MContDiffAt ∞ (fun w => H A (c.e.symm w) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
    rintro _ ⟨x, hx, rfl⟩ τ
    exact ((hmet x A (hOA x hx) τ).2 c (hOc hx)).self_of_nhds
  have hOo : IsOpen (c.e '' O) := c.e.isOpen_image_of_subset_source hO hOc
  have hTi : MeasurableSet (c.e '' T) := by
    have e : c.e '' T = Subtype.val '' (c.e.target.restrict c.e.symm ⁻¹' T) := by
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨_, c.e.map_source (hOc (hTO hx))⟩, by
          show c.e.symm (c.e x) ∈ T
          rwa [c.e.left_inv (hOc (hTO hx))], rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨_, hv, c.e.right_inv v.2⟩
    rw [e]
    exact (MeasurableEmbedding.subtype_coe c.e.open_target.measurableSet).measurableSet_image.2
      ((continuousOn_iff_continuous_restrict.1 c.e.continuousOn_symm).measurable hT)
  rw [h1, hμ, GlobalTheory.T.formPart_eq_lintegral_image_injective_holomorphic _ _ (atlas Y σ) _ hβ _ (cellMap ε f hf c u)
    (cellForm ε (fun v => H A (c.e.symm v)) ((atlas X σ).loc α c)) hopen hinj ?_ s _
    (hTm.inter hopen.measurableSet) Set.inter_subset_right, himg T (hTO.trans hOc) fun x hx => hOA x (hTO hx),
    show (atlas X σ).part α s T = ∫⁻ v in c.e '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens ((atlas X σ).loc α c v)).re)
      from GlobalTheory.T.formPart_subset_chart_eq_lintegral_image _ _ (atlas X σ) α hα s c T hT (hTO.trans hOc),
    ← GlobalTheory.T.setLIntegral_flagCellFibreDensity_eq_base ι m _ _ ε (fun v => H A (c.e.symm v))
      (fun v => ((s : ℤ) : ℝ) * (dens ((atlas X σ).loc α c v)).re) (c.e '' O) (c.e '' T) hOo hTi (Set.image_mono hTO)
      (continuousOn_const.mul ((continuousOn_dens _ hα c).mono ?_))
      (fun τ i j v hv => ((hG v hv τ).1 i j).continuousAt.continuousWithinAt) fun v hv τ => (hG v hv τ).2]
  · refine setLIntegral_congr_fun ((bsL ε).continuous.measurable hTi) fun w hw => ?_
    have hw' := Set.image_mono hTO hw
    beta_reduce
    rw [GlobalTheory.T.topDegreeDensity_base_form_times_fibre_class ι m _ _ ε _ _ w (fun τ => (hG _ hw' τ).2) fun τ => (hG _ hw' τ).1.of_le (by norm_cast),
      Complex.re_mul_ofReal, mul_assoc]
  · rintro _ ⟨x, hx, rfl⟩
    exact c.e.map_source (hOc hx)
  · intro x hx
    refine ⟨(GlobalTheory.T.flagCellCoordinates_contDiffAt_etaleChart F σ X Y ι m E E' φ f hf hR c A u _ ε x hx).differentiableAt two_ne_zero, ?_⟩
    rw [Pi.mul_apply, cellForm, map_mul, GlobalTheory.T.pullback_base_form_flag_cell_coordinates F σ X Y ι m E E' φ f hf hR c A u _ ε α hα x hx]
    congr 1
    exact GlobalTheory.T.pullback_aeval_evenComplexForms _ _ _ _ _ _ _ (GlobalTheory.T.graded_line_first_chern_forms_pullback_cell F σ X Y ι m E E' φ f hf hR c A u H hH ε x hx)

end GlobalTheory.FlagCell2.LocFib
