module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieFramesSmoothHermitianOffBoundary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityHodgeMetricBoundedDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPartHodgeMetricUniformisationImage
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityUniformisationChartChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityUniformisationChartChange
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open Filter Topology GlobalTheory.GoodMetric
open scoped ComplexOrder


set_option maxHeartbeats 800000 in
theorem GlobalTheory.UnifDens.chernTop_unif_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ (GlobalTheory.UnifDens.flatL h v) ∈ ch.e.source → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = Complex.normSq (LinearMap.det (fderiv ℂ (fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))) v : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) * chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)) (ch.e (ψ (GlobalTheory.UnifDens.flatL h v))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv ch hch A hA
  have hholo := GlobalTheory.T.componentUniformisation_continuousOn_analyticAt_charts E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hM := GlobalTheory.T.hodgeMetric_lie_frames_smooth_hermitian_off_boundary E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hL
  have hyO : ψ (GlobalTheory.UnifDens.flatL h v) ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) := by
    rw [← GlobalTheory.T.uniformisation_image_boundedDomain_eq_openPart E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ]
    exact ⟨_, hv, rfl⟩
  set y := ψ (GlobalTheory.UnifDens.flatL h v) with hydef
  let K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ := fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)
  let φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))
  have hφ : AnalyticAt ℂ φ v :=
    (hholo.2 _ hv ch hch).comp (show AnalyticAt ℂ (GlobalTheory.UnifDens.flatL h) v from (GlobalTheory.UnifDens.flatL h).toContinuousLinearMap.analyticAt v)
  have hy'' : ch.e.symm (ch.e y) = y := ch.e.left_inv hch
  have hK2 : ∀ τ, MContDiffAt 2 (fun u => K u τ) (φ v) := by
    intro τ a b
    have hsm := hM.smooth y hyO A hA τ a b
    have hre := GlobalTheory.ChernWeilLine.cInfAt_eventually hsm.1
    have him := GlobalTheory.ChernWeilLine.cInfAt_eventually hsm.2
    have hn : ∀ {g : CxPts X.str (σ.comp e.toRingHom) → ℝ}, (∀ᶠ z in 𝓝 y, CInfAt g z) →
        ContDiffAt ℝ 2 (g ∘ ch.e.symm) (ch.e y) := by
      intro g hg
      have hs : ch.e.target ∩ ch.e.symm ⁻¹' {z | CInfAt g z} ∈ 𝓝 (ch.e y) := by
        refine Filter.inter_mem (ch.e.open_target.mem_nhds (ch.e.map_source hch)) ?_
        exact (ch.e.continuousAt_symm (ch.e.map_source hch)).preimage_mem_nhds (hy''.symm ▸ hg)
      exact ((contDiffOn_chart (fun z hz => hz) ch).contDiffAt hs).of_le (by norm_cast)
    have h1 := (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn hre)).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn him)).mul (contDiffAt_const (c := Complex.I)))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, K]
    exact (Complex.re_add_im _).symm
  have hKu : ∀ τ, IsUnit (K (φ v) τ).det := by
    intro τ
    have hp := hM.posDef y hyO A hA τ
    show IsUnit (lieGram e U hj f₀ A₀ A (ch.e.symm (ch.e y)) τ).det
    rw [hy'']
    exact (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have key := GlobalTheory.ChernPull.chernTop_comp (pointPoly H Dw) K φ v hφ hK2 hKu
  have hcont : ContinuousAt (fun u => ψ (GlobalTheory.UnifDens.flatL h u)) v :=
    (hholo.1.continuousAt (GlobalTheory.PoincareLower.isOpen_domFlat.mem_nhds hv)).comp
      (GlobalTheory.UnifDens.flatL h).continuous.continuousAt
  have hg : (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) =ᶠ[𝓝 v] fun w => K (φ w) := by
    filter_upwards [hcont.preimage_mem_nhds (ch.e.open_source.mem_nhds hch)] with w hw
    simp only [K, φ, ch.e.left_inv hw]
  rw [GlobalTheory.ChernWeilLine.chernTop_congr _ hg, key]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityUniformisationChartChangeStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_class_density_uniformisation_chart_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ (GlobalTheory.UnifDens.flatL h v) ∈ ch.e.source → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = Complex.normSq (LinearMap.det (fderiv ℂ (fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))) v : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) * chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)) (ch.e (ψ (GlobalTheory.UnifDens.flatL h v))) := by
  first | exact @GlobalTheory.UnifDens.chernTop_unif_chart | exact GlobalTheory.UnifDens.chernTop_unif_chart | (intros; apply GlobalTheory.UnifDens.chernTop_unif_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPartHodgeMetricUniformisationImage
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifDens


open Filter Topology GlobalTheory.UnifDens in
theorem chernTopPart_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ A ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), MeasurableSet A → Set.InjOn ψ A → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' A) = ENNReal.ofReal (grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ) * muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) A := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ A hAD hAm hinj
  have hdim := GlobalTheory.T.flagSpaceComponent_base_dim_eq_cmType_card_mul_pq E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  obtain ⟨hcont, hana⟩ := GlobalTheory.T.componentUniformisation_continuousOn_analyticAt_charts E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have h3a := GlobalTheory.T.point_class_density_uniformisation_chart_change E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ hdim
  have h3b := GlobalTheory.T.pointClassDensity_hodgeMetric_boundedDomain E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ hdim
  set D := DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hDdef
  have hDo : IsOpen D := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set L := flatL hdim with hLdef
  set C : ℝ := grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef, grassConst]
    refine pow_nonneg (div_nonneg (Finset.prod_nonneg fun i _ => by positivity) (by positivity)) _
  set dens : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → ℝ := fun w =>
    ∏ i, ((hQ (unflat w i)).det.re) ^ (-((Dw.p + (Dw.p + Dw.q - Dw.p) : ℕ) : ℤ)) with hdens
  set μD := muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hμD
  set ρ : AlgChart X.str (σ.comp e.toRingHom) X.dim → CxPts X.str (σ.comp e.toRingHom) → ENNReal := fun ch y =>
    ENNReal.ofReal ((((1 : ℤˣ) : ℤ) : ℝ) * chernTop (pointPoly H Dw)
      (fun v => lieGram e U hj f₀ A₀ (Eb.nonempty (under y)).choose (ch.e.symm v)) (ch.e y)) with hρ
  have hμ : chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 =
      glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ := rfl
  have hpre : ∀ S : Set (CxPts X.str (σ.comp e.toRingHom)), MeasurableSet S → MeasurableSet (D ∩ ψ ⁻¹' S) := by
    intro S hS
    have hm : Measurable (D.restrict ψ) := (continuousOn_iff_continuous_restrict.1 hcont).measurable
    have := hDo.measurableSet.subtype_image (hm hS)
    convert this using 1
    ext w
    constructor
    · rintro ⟨hw, hwS⟩
      exact ⟨⟨w, hw⟩, hwS, rfl⟩
    · rintro ⟨⟨w, hw⟩, hwS, rfl⟩
      exact ⟨hw, hwS⟩
  have key : ∀ (ch : AlgChart X.str (σ.comp e.toRingHom) X.dim)
      (B : Set ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ)), MeasurableSet B → B ⊆ D → Set.InjOn ψ B →
      chartMeas ch.e (ρ ch) (ψ '' B) = ENNReal.ofReal C * μD (B ∩ ψ ⁻¹' ch.e.source) := by
    intro ch B hB hBD hBi
    set B' := B ∩ ψ ⁻¹' ch.e.source with hB'
    have hB'm : MeasurableSet B' := by
      have e0 : B' = B ∩ (D ∩ ψ ⁻¹' ch.e.source) := by
        ext w
        simp only [hB', Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, hBD h1, h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩
      rw [e0]
      exact hB.inter (hcont.isOpen_inter_preimage hDo ch.e.open_source).measurableSet
    have hψB : MeasurableSet (ψ '' B) := hB.image_of_continuousOn_injOn (hcont.mono hBD) hBi
    rw [chartMeas_apply ch.e (ρ ch) hψB]
    have e1 : ch.e.source ∩ ψ '' B = ψ '' B' := by
      rw [hB', Set.image_inter_preimage, Set.inter_comm]
    set φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun u => ch.e (ψ (L u)) with hφ
    set S := L ⁻¹' B' with hS
    have e2 : ch.e '' (ψ '' B') = φ '' S := by
      rw [hS, hφ, ← Set.image_image (fun w => ch.e (ψ w)) L, Set.image_preimage_eq _ L.surjective,
        Set.image_image]
    have hSm : MeasurableSet S := L.continuous.measurable hB'm
    have hdiff : ∀ u ∈ S, DifferentiableAt ℂ φ u := by
      intro u hu
      have hu' : L u ∈ B' := hu
      exact (hana (L u) (hBD hu'.1) ch hu'.2).differentiableAt.comp u L.differentiableAt
    have hder : ∀ u ∈ S, HasFDerivWithinAt φ ((fderiv ℂ φ u).restrictScalars ℝ) S u :=
      fun u hu => ((hdiff u hu).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinjφ : Set.InjOn φ S := by
      intro u1 h1 u2 h2 h12
      have h1' : L u1 ∈ B' := h1
      have h2' : L u2 ∈ B' := h2
      have h3 : ψ (L u1) = ψ (L u2) := ch.e.injOn h1'.2 h2'.2 h12
      exact L.injective (hBi h1'.1 h2'.1 h3)
    rw [e1, e2, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinjφ]
    have hint : ∀ u ∈ S, ENNReal.ofReal |((fderiv ℂ φ u).restrictScalars ℝ).det| * ρ ch (ch.e.symm (φ u)) =
        ENNReal.ofReal (C * dens (L u)) := by
      intro u hu
      have hu' : L u ∈ B' := hu
      have hsym : ch.e.symm (φ u) = ψ (L u) := ch.e.left_inv hu'.2
      rw [hsym]
      have hdet : ((fderiv ℂ φ u).restrictScalars ℝ).det =
          Complex.normSq (LinearMap.det (fderiv ℂ φ u : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) := by
        have := LinearMap.det_restrictScalars (R := ℝ)
          (f := (fderiv ℂ φ u : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim))
        rw [Algebra.norm_complex_apply] at this
        exact this
      have hA := (Eb.nonempty (under (ψ (L u)))).choose_spec
      have ha := h3a u (hBD hu'.1) ch hu'.2 _ hA
      have hb := h3b u (hBD hu'.1) _ hA
      rw [hdet, abs_of_nonneg (Complex.normSq_nonneg _), hρ, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
      congr 1
      simp only [Units.val_one, Int.cast_one, one_mul]
      rw [← ha, hb]
    rw [setLIntegral_congr_fun hSm hint]
    have hmp := (flatL_mp hdim).setLIntegral_comp_preimage_emb L.toHomeomorph.measurableEmbedding
      (fun w => ENNReal.ofReal (C * dens w)) B'
    rw [hS]
    refine hmp.trans ?_
    simp_rw [ENNReal.ofReal_mul hC]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hμD, muD, withDensity_apply _ hB'm,
      Measure.restrict_restrict hB'm, Set.inter_eq_left.2 (Set.inter_subset_left.trans hBD)]

  set ν : Measure (CxPts X.str (σ.comp e.toRingHom)) := ENNReal.ofReal C • Measure.map ψ (μD.restrict A) with hν
  have hae : AEMeasurable ψ (μD.restrict A) := (hcont.mono hAD).aemeasurable hAm
  have hνT : ∀ S, MeasurableSet S → ν S = ENNReal.ofReal C * μD (A ∩ ψ ⁻¹' S) := by
    intro S hS
    rw [hν, Measure.smul_apply, Measure.map_apply_of_aemeasurable hae hS, Measure.restrict_apply' hAm,
      Set.inter_comm, smul_eq_mul]
  have hAS : ∀ S : Set (CxPts X.str (σ.comp e.toRingHom)), MeasurableSet S → MeasurableSet (A ∩ ψ ⁻¹' S) := by
    intro S hS
    have e0 : A ∩ ψ ⁻¹' S = A ∩ (D ∩ ψ ⁻¹' S) := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨fun h => ⟨h.1, hAD h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [e0]
    exact hAm.inter (hpre S hS)
  have hψA : MeasurableSet (ψ '' A) := hAm.image_of_continuousOn_injOn (hcont.mono hAD) hinj
  have hle : (glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ).restrict (ψ '' A) ≤ ν := by
    rw [glueMeas, GlobalTheory.ChernScale.restrict_iSup_eq _ hψA]
    refine iSup_le fun ch => Measure.le_iff.2 fun S hS => ?_
    rw [Measure.restrict_apply hS, hνT S hS, Set.inter_comm, ← Set.image_inter_preimage,
      key ch _ (hAS S hS) (Set.inter_subset_left.trans hAD) (hinj.mono Set.inter_subset_left)]
    exact mul_le_mul' le_rfl (measure_mono Set.inter_subset_left)
  have heq : (glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ).restrict (ψ '' A) = ν := by
    refine ext_of_cover (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e.source)
      (fun ch => ch.e.open_source) (fun y => AlgChart.exists_mem_source y) fun ch S hS hSc =>
        le_antisymm (Measure.le_iff'.1 hle S) ?_
    rw [Measure.restrict_apply hS, hνT S hS]
    have e3 : A ∩ ψ ⁻¹' S = (A ∩ ψ ⁻¹' S) ∩ ψ ⁻¹' ch.e.source :=
      (Set.inter_eq_left.2 fun w (hw : w ∈ A ∩ ψ ⁻¹' S) => hSc hw.2).symm
    calc ENNReal.ofReal C * μD (A ∩ ψ ⁻¹' S)
        = chartMeas ch.e (ρ ch) (ψ '' (A ∩ ψ ⁻¹' S)) := by
          rw [key ch _ (hAS S hS) (Set.inter_subset_left.trans hAD) (hinj.mono Set.inter_subset_left), ← e3]
      _ = chartMeas ch.e (ρ ch) (S ∩ ψ '' A) := by rw [Set.image_inter_preimage, Set.inter_comm]
      _ ≤ glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ (S ∩ ψ '' A) :=
          Measure.le_iff'.1 (le_iSup (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => chartMeas ch.e (ρ ch)) ch) _
  rw [hμ, ← Measure.restrict_apply_self, heq, hνT _ hψA, Set.inter_eq_left.2 (Set.subset_preimage_image ψ A)]

end GlobalTheory.UnifDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPartHodgeMetricUniformisationImageStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTopPart_hodgeMetric_uniformisation_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ A ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), MeasurableSet A → Set.InjOn ψ A → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' A) = ENNReal.ofReal (grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ) * muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) A := by
  first | exact @GlobalTheory.UnifDens.chernTopPart_image | exact GlobalTheory.UnifDens.chernTopPart_image | (intros; apply GlobalTheory.UnifDens.chernTopPart_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedLevelEqParahoricWithTupleCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeAndTwistPlacesOverOtherThanSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeAndTwistPlacesOverOtherThanSplit
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OtherPlaces

theorem conj_mem_of_comap_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {w w' : HeightOneSpectrum (𝓞 E)}
    (h : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) =
      w'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))) (hne : w ≠ w') :
    ∀ c ∈ w.asIdeal, IsCMField.ringOfIntegersComplexConj E c ∈ w'.asIdeal := by
  have hsub : (w.asIdeal : Set (𝓞 E)) ⊆ w'.asIdeal ∪
      (w'.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E).toRingEquiv.toRingHom : Ideal (𝓞 E)) := by
    intro y hy
    obtain ⟨x, hx⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff E
      (y * IsCMField.ringOfIntegersComplexConj E y)).1 (by simp [mul_comm])
    have hx' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x = y * IsCMField.ringOfIntegersComplexConj E y :=
      RingOfIntegers.ext hx
    have h1 : x ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
      rw [Ideal.mem_comap, hx']; exact Ideal.mul_mem_right _ _ hy
    rw [h, Ideal.mem_comap, hx'] at h1
    exact w'.isPrime.mem_or_mem h1
  rcases Ideal.subset_union.1 hsub with h1 | h1
  · exact absurd (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h1)) hne
  · exact fun c hc => h1 hc

theorem over_ne : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) →
    ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.v ∉ gPl D → s.w ∈ L.Q t →
      (∀ PP ∈ L.Pg, ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) ∧ (∀ PP ∈ L.Q t, PP ≠ s.w → ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) := by
  intro D T L μ0 hL hPg t s hs hsQ
  refine ⟨fun PP hPP => ⟨PP.under (𝓞 (maximalRealSubfield D.host.E)), rfl, fun e => hs ?_⟩,
    fun PP hPP hne => ⟨PP.under (𝓞 (maximalRealSubfield D.host.E)), rfl, fun e => ?_⟩⟩
  · obtain ⟨k, v, rfl⟩ := (hPg PP).1 hPP
    exact ⟨D.naut.plGw k v, congrArg HeightOneSpectrum.asIdeal e, k, D.naut.plGw_over k v⟩
  · letI := D.host.isCMField_hostE
    refine (hL.Q_pl t s.w hsQ).2 PP hPP fun c hc => ⟨_, conj_mem_of_comap_eq
      (s.w_under.trans (congrArg HeightOneSpectrum.asIdeal e).symm) hne.symm c hc, rfl⟩

end GlobalTheory.OtherPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeAndTwistPlacesOverOtherThanSplitStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeAndTwistPlaces_over_other_than_split : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.v ∉ gPl D → s.w ∈ L.Q t → (∀ PP ∈ L.Pg, ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) ∧ (∀ PP ∈ L.Q t, PP ≠ s.w → ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) := by
  first | exact @GlobalTheory.OtherPlaces.over_ne | exact GlobalTheory.OtherPlaces.over_ne | (intros; apply GlobalTheory.OtherPlaces.over_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionCompletionBlockTriLowerBlockDet
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionCompletionBlockTriLowerBlockDet
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV

namespace GlobalTheory

theorem reduction_blockTri_detDD : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (φ : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* kP s.w) (n r : ℕ) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g : GL (Fin n) (kP s.w)), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1) → (∀ a b, ∃ hab : (h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = φ ⟨_, hab⟩) → (g ∈ blockTri (blk2 r) ↔ ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1) ∧ (g ∈ blockTri (blk2 r) → ∃ hd : NG.detDD s r h ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), ((dBlk (blk2 r) 1 g : (kP s.w)ˣ) : kP s.w) = φ ⟨_, hd⟩) := by
  intro L _ _ _ s φ n r h g hφ hg
  have key : ∀ a b, (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = 0 ↔
      Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
    intro a b
    obtain ⟨hab, e⟩ := hg a b
    rw [e, hφ]
  refine ⟨?_, ?_⟩
  · rw [mem_blockTri]
    constructor
    · intro H a b ha hb
      rw [← key]
      apply H
      simp [blk2, hb, Nat.not_lt.mpr ha]
    · intro H i j hij
      rw [key]
      unfold blk2 at hij
      by_cases hj : j.val < r
      · by_cases hi : i.val < r
        · simp [hj, hi] at hij
        · exact H i j (Nat.not_lt.mp hi) hj
      · by_cases hi : i.val < r <;> simp [hj, hi] at hij
  · intro hT
    let M : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s.v.adicCompletionIntegers (maximalRealSubfield L)) :=
      fun a b => ⟨(h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1, (hg a.1 b.1).1⟩
    have hdet : NG.detDD s r h = (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype M.det := by
      rw [RingHom.map_det]
      rfl
    refine ⟨hdet ▸ (M.det).2, ?_⟩
    have e1 : (⟨NG.detDD s r h, hdet ▸ (M.det).2⟩ : s.v.adicCompletionIntegers (maximalRealSubfield L)) = M.det :=
      Subtype.ext hdet
    rw [e1, RingHom.map_det, diag_block_det_val 1 hT]
    let e : {a : Fin n // blk2 r a = 1} ≃ {x : Fin n // r ≤ x.val} :=
      Equiv.subtypeEquivRight (fun a => by
        unfold blk2
        split_ifs with h'
        · exact ⟨fun h0 => absurd h0 (by decide), fun h0 => absurd h' (Nat.not_lt.mpr h0)⟩
        · exact ⟨fun _ => Nat.not_lt.mp h', fun _ => rfl⟩)
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.map_apply, M]
    exact (hg (e a).1 (e b).1).2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionCompletionBlockTriLowerBlockDetStatement
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (φ : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* kP s.w) (n r : ℕ) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g : GL (Fin n) (kP s.w)), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1) → (∀ a b, ∃ hab : (h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = φ ⟨_, hab⟩) → (g ∈ blockTri (blk2 r) ↔ ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1) ∧ (g ∈ blockTri (blk2 r) → ∃ hd : NG.detDD s r h ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), ((dBlk (blk2 r) 1 g : (kP s.w)ˣ) : kP s.w) = φ ⟨_, hd⟩) := by
  first | exact @GlobalTheory.reduction_blockTri_detDD | exact GlobalTheory.reduction_blockTri_detDD | (intros; apply GlobalTheory.reduction_blockTri_detDD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedLevelEqParahoricWithTupleCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtPara

theorem levelPara : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelPara (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ξ := by
  intro D T L μ0 hL hPg i t hr ψ v hv
  have loc_mul (a b : HChar D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E))
      (x : (w.adicCompletion D.host.E)ˣ) :
      (a * b).loc w x = a.loc w x * b.loc w x := rfl
  obtain ⟨s, hsv, hsQ⟩ := GlobalTheory.T.exists_splitTwistPlace_over_productCharacter_ramified D T L μ0 hL i t v hv
  have hvg : s.v ∉ gPl D := hsv ▸ hv.1
  obtain ⟨hPgo, hQo⟩ := GlobalTheory.T.typeAndTwistPlaces_over_other_than_split D T L μ0 hL hPg t s hvg hsQ

  have hunr : (L.C.mu0 i).UnrAt s.w := by
    refine (L.C.isMu0 i).unr s.w fun k hk => hvg ⟨s.w, s.w_under, k, hk⟩
  have htame : (L.C.mu0 i * L.xiH t).TameAt s.w := by
    intro x hx hx1
    rw [loc_mul, (L.C.isMu0 i).tame s.w x hx hx1, hL.xi_tame t s.w x hx hx1, one_mul]
  obtain ⟨ξ, hξc, hξr⟩ := GlobalTheory.T.tame_heckeCharacter_split_place_local_component D.host.E s _ htame
  obtain ⟨hUA, hSt, hred, hloc⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV
  obtain ⟨φ, -, hφ0, hφa, hφe⟩ := hloc s
  have hoff : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ PP,
      (PP ∈ L.Pg ∨ (PP ∈ L.Q t ∧ PP ≠ s.w)) → redFn 1 PP (km D D.R.nV κ) = 1 := by
    intro κ hκ htr PP hPP
    obtain ⟨v', hov, hne⟩ : ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v :=
      hPP.elim (hPgo PP) (fun h => hQo PP h.1 h.2)
    exact hred κ hκ {s.v} v' PP htr hov (by simpa using hne)
  refine ⟨s, ξ, hsv, hξc, ⟨?_, ?_⟩⟩
  · intro κ htr
    have hkey : ∀ hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV,
        (redFn 1 s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) ↔ ∀ a b : Fin D.R.nV, D.R.r ≤ a.val → b.val < D.R.r →
          Valued.v (((s.loc D.R.nV κ : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) := fun hκ =>
      (GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet D.host.E s φ D.R.nV D.R.r (s.loc D.R.nV κ) (redFn 1 s.w (km D D.R.nV κ)) hφ0 (hφe κ hκ)).1
    constructor
    · intro hJ
      have hJ' : km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 _ := hJ
      rw [mem_lev, mem_parLev] at hJ'
      obtain ⟨⟨-, hSt', -, hQ'⟩, -⟩ := hJ'
      have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hSt κ).1 hSt'
      refine ⟨GlobalTheory.HeckeStdFacts.mem_GLint_iff.2 ⟨fun a b => GlobalTheory.HeckeStdFacts.proj_mem s (hκU a b), fun a b => ?_⟩, ?_⟩
      · rw [← map_inv]
        exact GlobalTheory.HeckeStdFacts.proj_mem s ((inv_mem hκU) a b)
      · exact (hkey hκU).1 (hQ' s.w hsQ)
    · rintro ⟨hG, hlow⟩
      obtain ⟨hG1, hG2⟩ := GlobalTheory.HeckeStdFacts.mem_GLint_iff.1 hG
      have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV :=
        GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ htr (fun a b => hG1 a b) (fun a b => by rw [map_inv]; exact hG2 a b)
      have hrt : rTup 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = 1 := by
        funext PP
        show upperLeftBlock hr (redFn 1 PP.1 (km D D.R.nV κ)) = 1
        rw [hoff κ hκU htr PP.1 (Or.inl PP.2)]
        exact blockDiagonalExtendByOnePrimeField_one _ _
      show km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 _
      rw [mem_lev, mem_parLev, hrt]
      refine ⟨⟨hUA κ, (hSt κ).2 hκU, fun PP hPP => ?_, fun PP hPP => ?_⟩, Subgroup.one_mem _⟩
      · rw [hoff κ hκU htr PP (Or.inl hPP)]; exact Subgroup.one_mem _
      · by_cases hPs : PP = s.w
        · subst hPs; exact (hkey hκU).2 hlow
        · rw [hoff κ hκU htr PP (Or.inr ⟨hPP, hPs⟩)]; exact Subgroup.one_mem _
  · intro κ hJ htr u hu
    have hJ' : km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1
        (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) := hJ
    have hpar := (mem_lev.1 hJ').1
    have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hSt κ).1 (parLev_St hpar)
    have hrt : rTup 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = 1 := by
      funext PP
      show upperLeftBlock hr (redFn 1 PP.1 (km D D.R.nV κ)) = 1
      rw [hoff κ hκU htr PP.1 (Or.inl PP.2)]
      exact blockDiagonalExtendByOnePrimeField_one _ _
    have hQ' : redFn 1 s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) := parLev_q hpar hsQ
    obtain ⟨hd, hdv⟩ := (GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet D.host.E s φ D.R.nV D.R.r (s.loc D.R.nV κ) (redFn 1 s.w (km D D.R.nV κ)) hφ0 (hφe κ hκU)).2 hQ'
    obtain ⟨w0, hw0⟩ : ∃ w0, w0 = dBlk (blk2 D.R.r) 1 (redFn 1 s.w (km D D.R.nV κ)) := ⟨_, rfl⟩
    rw [← hw0] at hdv
    have hQ1 : ∏ PP ∈ L.Q t, L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP (km D D.R.nV κ))) = L.xiR t s.w w0 := by
      rw [hw0]
      refine Finset.prod_eq_single_of_mem s.w hsQ fun PP hPP hne => ?_
      rw [hoff κ hκU htr PP (Or.inr ⟨hPP, hne⟩)]
      show L.xiR t PP (ext1 _ _ 1) = 1
      rw [blockDiagonalExtendByOnePrimeField_one, map_one]
    have hval : stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) ⟨κ, hJ⟩ =
        L.xiR t s.w w0 := by
      show levFn 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = _
      unfold levFn
      rw [hrt, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, one_mul]
      · exact hQ1
      · intro PP hPP
        refine Finset.prod_eq_one fun c _ => ?_
        rw [hoff κ hκU htr PP (Or.inl hPP)]
        exact (congrArg _ (blockDiagonalExtendByOnePrimeField_one _ _)).trans (map_one _)
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (w0 : kP s.w)
    have hw0ne : (w0 : kP s.w) ≠ 0 := w0.ne_zero
    have haP : a ∉ s.w.asIdeal := fun h => hw0ne (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
    have ha0 : (a : D.host.E) ≠ 0 := fun h => haP (by
      rw [show a = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
    obtain ⟨k, hk⟩ : ∃ k : D.host.Eˣ, (k : D.host.E) = a := ⟨Units.mk0 _ ha0, rfl⟩
    have hres : L.xiR t s.w w0 = (L.xiH t).locK s.w k := hL.xiR t s.w hsQ a k w0 hk ha.symm
    obtain ⟨hia, hφia⟩ := hφa a
    have hu1 : Valued.v (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by
      rw [hu]
      refine le_antisymm hd (not_lt.1 fun hlt => hw0ne ?_)
      rw [hdv]; exact (hφ0 _).2 hlt
    have hu2 : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - s.i (a : D.host.E)) < 1 := by
      have h0 : φ (⟨_, hd⟩ - ⟨_, hia⟩) = 0 := by rw [map_sub, ← hdv, hφia, ha, sub_self]
      have h1 := (hφ0 _).1 h0
      rw [AddSubgroupClass.coe_sub] at h1
      rw [hu]; exact h1
    have hk1 : (L.C.mu0 i).locK s.w k = 1 := by
      have hv1 : Valued.v (((k : D.host.E) : s.w.adicCompletion D.host.E)) = 1 := by
        rw [hk]
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
          HeightOneSpectrum.intValuation_eq_one_iff]
        exact haP
      exact hunr _ hv1
    have hmul : (L.C.mu0 i * L.xiH t).locK s.w k = (L.C.mu0 i).locK s.w k * (L.xiH t).locK s.w k :=
      loc_mul _ _ s.w (atFin s.w k)
    refine hval.trans (hres.trans ?_)
    rw [hξr u a k hk hu1 hu2, hmul, hk1, one_mul]

end GlobalTheory.MtPara
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedLevelEqParahoricWithTupleCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedLevel_eq_parahoric_with_tupleCharacter : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelPara (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ξ := by
  first | exact @GlobalTheory.MtPara.levelPara | exact GlobalTheory.MtPara.levelPara | (intros; apply GlobalTheory.MtPara.levelPara <;> assumption)
end
end
