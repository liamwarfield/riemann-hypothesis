module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPartHodgeMetricUniformisationImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompMapAndFrDense
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD CompSplitPfB

namespace GlobalTheory.Reg.GenericFrameDensity

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


theorem lact_mem_dom (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  have h2 : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  show ∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (lact γ x) τ i).re
  intro τ
  refine ⟨?_, fun i => by rw [dmin_lact X hγ]; exact (h2 τ).2 i⟩
  show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
  rw [Matrix.det_mul]
  refine mul_ne_zero ?_ (h2 τ).1
  have e : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det :=
    (RingHom.map_det τ.1 _).symm
  rw [e]
  exact (map_ne_zero τ.1).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)

end Gen

end GlobalTheory.Reg.GenericFrameDensity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationNullSetsToPointClassNull
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentHolomorphicBoundedDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentHolomorphicBoundedDomain
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix ComplexOrder

namespace GlobalTheory.UnifHolo

theorem holo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (W : X.X.Opens) (g : Γ(X.X, W)), DifferentiableOn ℂ (ev X.str (σ.comp e.toRingHom) W g ∘ ψ) (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ W g
  classical
  haveI : IsOpenImmersion j := hL.1
  have hjr : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by
    have := (hU.2.1 k).1
    omega
  let L : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) ≃L[ℂ]
      (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin _).symm).toContinuousLinearEquiv
  have ho : IsOpen (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set B := L.symm ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hBdef
  have hB : IsOpen B := ho.preimage L.symm.continuous
  let x : (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) → (U.X k).dom := fun b =>
    stdFrame (U.X k) hjr (Equiv.refl _) hp (unflat (L.symm b))
  have hd : ∀ τ a c, DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a c) B := fun τ a c =>
    ((TorHolo.differentiable_stdMat (U.X k) hjr (Equiv.refl _) τ a c).comp
      L.symm.differentiable).differentiableOn.congr fun b hb => by
        show ReciprocityTheory.ChartRestriction.G.FD.mat (stdFrame _ _ _ _ _).1 τ a c = _
        rw [stdFrame_val _ _ _ _ hb]
        rfl
  have hY : IsHolTo B fun b => (cxPt T.Z (U.un k (x b))).1 := GlobalTheory.GramFamily.isHolTo_cxPt T.Z hU k hB x hd
  have hflat : ∀ u : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat u) = u := by
    intro u; funext ⟨i, a, b⟩; rfl
  have hrel : ∀ b ∈ B, cxOf e σ hj (ψ (L.symm b)) = cxPt T.Z (U.un k (x b)) := by
    intro b hb
    have h1 := hψ (x b)
    rwa [domPt_stdFrame (U.X k) hjr (Equiv.refl _) hp hb, hflat] at h1
  set g' := (j.appIso W).inv.hom g with hg'
  intro v hv
  have hb : L v ∈ B := by
    refine Set.mem_preimage.2 ?_
    rw [L.symm_apply_apply]
    exact hv.1
  have hS : L v ∈ {b ∈ B | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ (j ''ᵁ W)} := by
    refine ⟨hb, ?_⟩
    rw [← hrel _ hb, L.symm_apply_apply]
    exact le_preimage_cxOf e σ hj W hv.2
  have hdA : DifferentiableAt ℂ (fun b => valAt' (cxPt T.Z (U.un k (x b))).1 (j ''ᵁ W) g') (L v) :=
    ((hY (j ''ᵁ W) g').2 (L v) hS).differentiableAt (((hY (j ''ᵁ W) g').1).mem_nhds hS)
  have hc := (hdA.comp v L.differentiableAt).differentiableWithinAt
    (s := DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W)
  have heq : ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W,
      (ev X.str (σ.comp e.toRingHom) W g ∘ ψ) w =
        ((fun b => valAt' (cxPt T.Z (U.un k (x b))).1 (j ''ᵁ W) g') ∘ L) w := by
    intro w hw
    have hwB : L w ∈ B := by
      refine Set.mem_preimage.2 ?_
      rw [L.symm_apply_apply]
      exact hw.1
    rw [Function.comp_apply, Function.comp_apply, ev_eq_valAt'_cxOf e σ hj W g hw.2, ← hrel _ hwB,
      L.symm_apply_apply]
  exact hc.congr heq (heq v hv)

end GlobalTheory.UnifHolo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentHolomorphicBoundedDomainStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationComponent_holomorphic_boundedDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (W : X.X.Opens) (g : Γ(X.X, W)), DifferentiableOn ℂ (ev X.str (σ.comp e.toRingHom) W g ∘ ψ) (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W) := by
  first | exact @GlobalTheory.UnifHolo.holo | exact GlobalTheory.UnifHolo.holo | (intros; apply GlobalTheory.UnifHolo.holo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationNullSetsToPointClassNull
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix ComplexOrder

namespace GlobalTheory.UnifNull


open Set in
theorem iSup_apply_eq_zero {Z : Type*} [MeasurableSpace Z] {ι : Type*} (μ : ι → Measure Z) {T : Set Z}
    (hT : MeasurableSet T) (h : ∀ i, μ i T = 0) : (⨆ i, μ i) T = 0 := by
  have hle : (⨆ i, μ i) ≤ (⨆ i, μ i).restrict Tᶜ := iSup_le fun i => Measure.le_iff.2 fun B hB => by
    rw [Measure.restrict_apply hB, ← measure_inter_add_diff B hT, diff_eq,
      measure_mono_null inter_subset_right (h i), zero_add]
    exact Measure.le_iff'.1 (le_iSup μ i) _
  refine le_antisymm ((Measure.le_iff'.1 hle T).trans ?_) (zero_le)
  rw [Measure.restrict_apply hT, inter_compl_self, measure_empty]


open Set in
theorem glueNull : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [SecondCountableTopology (CxPts p σ)] (ρ : AlgChart p σ D → CxPts p σ → ENNReal) (S : Set (CxPts p σ)), (∀ c : AlgChart p σ D, volume (c.e '' (c.e.source ∩ S)) = 0) → glueMeas (fun c : AlgChart p σ D => c.e) ρ S = 0 := by
  intro k _ Y p σ D _ ρ S hS
  classical
  obtain ⟨I, hIc, hI⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : AlgChart p σ D => c.e.source) fun c => c.e.open_source
  let Z : AlgChart p σ D → Set (ReciprocityTheory.L2DbarEstimates.V D) := fun c => toMeasurable volume (c.e '' (c.e.source ∩ S))
  have hZ : ∀ c, volume (Z c) = 0 := fun c => (measure_toMeasurable _).trans (hS c)
  have hTm : ∀ c : AlgChart p σ D, MeasurableSet (c.e.source ∩ c.e ⁻¹' Z c) := by
    intro c
    have hm := (c.e.continuousOn.measurable_piecewise (continuousOn_const (c := (0 : ReciprocityTheory.L2DbarEstimates.V D)))
      c.e.open_source.measurableSet) (measurableSet_toMeasurable volume (c.e '' (c.e.source ∩ S)))
    convert c.e.open_source.measurableSet.inter hm using 1
    ext y
    simp only [mem_inter_iff, mem_preimage]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> simpa [Set.piecewise_eq_of_mem _ _ _ h1] using h2
  let T : Set (CxPts p σ) := (⋃ c : AlgChart p σ D, c.e.source)ᶜ ∪ ⋃ c ∈ I, (c.e.source ∩ c.e ⁻¹' Z c)
  have hT : MeasurableSet T :=
    (isOpen_iUnion fun c : AlgChart p σ D => c.e.open_source).measurableSet.compl.union
      (MeasurableSet.biUnion hIc fun c _ => hTm c)
  have hST : S ⊆ T := by
    intro y hy
    by_cases hO : y ∈ ⋃ c : AlgChart p σ D, c.e.source
    · right
      rw [← hI] at hO
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 hO
      exact mem_biUnion hc ⟨hyc, subset_toMeasurable _ _ ⟨y, ⟨hyc, hy⟩, rfl⟩⟩
    · exact Or.inl hO
  have hc0 : ∀ c : AlgChart p σ D, chartMeas c.e (ρ c) T = 0 := by
    intro c
    rw [chartMeas_apply _ _ hT]
    refine setLIntegral_measure_zero _ _ ?_
    have hsub : c.e '' (c.e.source ∩ T) ⊆ ⋃ c' ∈ I, (c.e ∘ c'.e.symm) ''
        (Z c' ∩ (c'.e.target ∩ c'.e.symm ⁻¹' c.e.source)) := by
      rintro _ ⟨y, ⟨hy, hyT⟩, rfl⟩
      rcases hyT with hyO | hyT
      · exact (hyO (mem_iUnion.2 ⟨c, hy⟩)).elim
      obtain ⟨c', hc', hy1, hy2⟩ := mem_iUnion₂.1 hyT
      refine mem_biUnion hc' ⟨c'.e y, ⟨hy2, c'.e.map_source hy1, ?_⟩, ?_⟩
      · simp only [mem_preimage, c'.e.left_inv hy1]; exact hy
      · simp only [Function.comp_apply, c'.e.left_inv hy1]
    refine measure_mono_null hsub ((measure_biUnion_null_iff hIc).2 fun c' _ => ?_)
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (((AlgChart.holo_trans c' c).restrictScalars ℝ).mono inter_subset_right)
      (measure_mono_null inter_subset_left (hZ c'))
  exact measure_mono_null hST (iSup_apply_eq_zero _ hT hc0)


open Set in
theorem volume_null_of_muD {ι : Type} [Fintype ι] {p q : ℕ} {N : Set (ι × Fin p × Fin q → ℂ)}
    (hN : N ⊆ DomFlat ι p q) (h0 : muD ι p q N = 0) : volume N = 0 := by
  have hc : ∀ i : ι, Continuous fun v : ι × Fin p × Fin q → ℂ => (hQ (unflat v i)).det.re := by
    intro i
    refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
    have hu : Continuous fun v : ι × Fin p × Fin q → ℂ => unflat v i :=
      continuous_pi fun a => continuous_pi fun b => continuous_apply (i, a, b)
    unfold hQ
    exact continuous_const.sub (Continuous.matrix_mul (Continuous.matrix_conjTranspose hu) hu)
  have hm : Measurable fun v : ι × Fin p × Fin q → ℂ =>
      ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ => ?_)
    simp only [zpow_neg, zpow_natCast]
    exact ((hc i).measurable.pow_const _).inv
  have hpos : ∀ v ∈ DomFlat ι p q,
      ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))) ≠ 0 := by
    intro v hv
    refine (ENNReal.ofReal_pos.2 (Finset.prod_pos fun i _ => zpow_pos ?_ _)).ne'
    have h := (hv i : (1 - (unflat v i)ᴴ * unflat v i).PosDef).det_pos
    exact (Complex.pos_iff.1 h).1
  rw [muD, withDensity_apply_eq_zero' hm.aemeasurable,
    Measure.restrict_apply' GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.measurableSet] at h0
  refine measure_mono_null ?_ h0
  intro v hv
  exact ⟨⟨hpos v (hN hv), hv⟩, hN hv⟩


open Set in
theorem chart_image_null {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {ι : Type} [Fintype ι] (c : AlgChart p σ D) (ψ : (ι → ℂ) → CxPts p σ) {s : Set (ι → ℂ)}
    (hD : D = Fintype.card ι) (hs : volume s = 0)
    (hψ : ∀ a, DifferentiableOn ℂ (ev p σ c.U (c.x a) ∘ ψ) (s ∩ ψ ⁻¹' ptsIn p σ c.U)) :
    volume (c.e '' (c.e.source ∩ ψ '' s)) = 0 := by
  set t := s ∩ ψ ⁻¹' c.e.source with ht
  have e1 : c.e '' (c.e.source ∩ ψ '' s) = (c.e ∘ ψ) '' t := by
    ext y; constructor
    · rintro ⟨_, ⟨h1, w, hw, rfl⟩, rfl⟩; exact ⟨w, ⟨hw, h1⟩, rfl⟩
    · rintro ⟨w, ⟨hw, h1⟩, rfl⟩; exact ⟨ψ w, ⟨h1, w, hw, rfl⟩, rfl⟩
  have hd : DifferentiableOn ℂ (c.e ∘ ψ) t := by
    apply differentiableOn_euclidean.2
    intro a
    have hsub : t ⊆ s ∩ ψ ⁻¹' ptsIn p σ c.U :=
      fun _ hw => ⟨hw.1, c.source_subset hw.2⟩
    exact ((hψ a).mono hsub).congr fun w hw => c.apply_eq _ hw.2 a
  have hfin : Module.finrank ℝ (ι → ℂ) = Module.finrank ℝ (ReciprocityTheory.L2DbarEstimates.V D) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (ι → ℂ), ← Module.finrank_mul_finrank ℝ ℂ (ReciprocityTheory.L2DbarEstimates.V D)]
    simp [hD]
  let L : (ι → ℂ) ≃L[ℝ] ReciprocityTheory.L2DbarEstimates.V D := ContinuousLinearEquiv.ofFinrankEq hfin
  have h1 : volume ((L.symm ∘ (c.e ∘ ψ)) '' t) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (L.symm.differentiable.comp_differentiableOn (hd.restrictScalars ℝ))
      (measure_mono_null inter_subset_left hs)
  have e2 : (c.e ∘ ψ) '' t = L.symm ⁻¹' ((L.symm ∘ (c.e ∘ ψ)) '' t) := by
    rw [← L.image_eq_preimage_symm, image_image]; simp
  haveI : (Measure.map L.symm (volume : Measure (ReciprocityTheory.L2DbarEstimates.V D))).IsAddHaarMeasure :=
    L.symm.isAddHaarMeasure_map volume
  have hac := Measure.absolutelyContinuous_isAddHaarMeasure
    (Measure.map L.symm (volume : Measure (ReciprocityTheory.L2DbarEstimates.V D))) volume
  rw [e1, e2]
  calc volume (L.symm ⁻¹' ((L.symm ∘ (c.e ∘ ψ)) '' t))
      = Measure.map L.symm volume ((L.symm ∘ (c.e ∘ ψ)) '' t) :=
        (L.symm.toHomeomorph.toMeasurableEquiv.map_apply _).symm
    _ = 0 := hac h1

theorem image_null : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ N ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) N = 0 → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' N) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ N hN h0
  have hH := GlobalTheory.T.uniformisationComponent_holomorphic_boundedDomain E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hv := volume_null_of_muD hN h0
  have hdim : X.dim = Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) := by
    rw [(GlobalTheory.FlagBaseDim.dims E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL).2]
    have h1 := ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.two_card_Psi (U.X k)
    have h2 : Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
      rw [← Nat.card_eq_fintype_card]; exact GlobalTheory.PeriodCoord.card_cmType H
    have h3 : Fintype.card (GlobalTheory.AllWt.Psi H) = Fintype.card (U.X k).Ψ := by omega
    simp only [Fintype.card_prod, Fintype.card_fin, h3, Nat.add_sub_cancel_left]
  unfold chernTopPart
  exact glueNull X.str (σ.comp e.toRingHom) X.dim _ _ fun ch =>
    chart_image_null ch ψ hdim hv fun a => (hH ch.U (ch.x a)).mono fun w hw => ⟨hN hw.1, hw.2⟩

end GlobalTheory.UnifNull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationNullSetsToPointClassNullStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_null_sets_to_pointClass_null : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ N ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) N = 0 → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' N) = 0 := by
  first | exact @GlobalTheory.UnifNull.image_null | exact GlobalTheory.UnifNull.image_null | (intros; apply GlobalTheory.UnifNull.image_null <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComponentUniformisationBoundedDomainComple
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComponentUniformisationBoundedDomainComple
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.LieBase.UnifExists

open Formalism.MJ ReciprocityTheory.ChartRestriction.G.AR.Up

theorem flat_inj {ι : Type} {p q : ℕ} {z z' : ι → Matrix (Fin p) (Fin q) ℂ} (h : flat z = flat z') : z = z' := by
  funext t a b
  exact congrFun h (t, a, b)

theorem exists_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∃ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  obtain ⟨hoi, hfj, -⟩ := hL
  haveI := hoi
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := first_index_eq_of_unfolded U hU rfl k
  have hle : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right Dw.p Dw.q
  have hrange : ∀ x : (U.X k).dom, Set.range (cxPt T.Z (U.un k x)).1 ⊆ Set.range j := by
    rintro x _ ⟨s, rfl⟩
    obtain ⟨y, hy⟩ := Φ.label k x s
    refine ⟨f y, ?_⟩
    show (f ≫ j) y = _
    rw [hfj]
    exact hy
  let lf : (U.X k).dom → CxPts X.str (σ.comp e.toRingHom) := fun x =>
    ⟨IsOpenImmersion.lift j (cxPt T.Z (U.un k x)).1 (hrange x), by
      rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, (cxPt T.Z (U.un k x)).2,
        ← Spec.map_comp]
      rfl⟩
  have hlf : ∀ x, cxOf e σ hj (lf x) = cxPt T.Z (U.un k x) := fun x =>
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have hwell : ∀ x x' : (U.X k).dom,
      domPt (U.X k) hle (Equiv.refl (U.X k).Ψ) x.1 = domPt (U.X k) hle (Equiv.refl (U.X k).Ψ) x'.1 →
      cxPt T.Z (U.un k x) = cxPt T.Z (U.un k x') := by
    intro x x' h
    have h5 : ∀ τ, moeb (frameCo (U.X k) hle x.1 τ) 0 = moeb (frameCo (U.X k) hle x'.1 τ) 0 :=
      fun τ => congrFun h τ
    exact cxPt_congr (PointWell.pt_eq_of_block hU hσ k x x'
      (fun τ => PointWell.block_of_moeb_eq _ hle hp x.2 x'.2 τ (h5 τ))
      (fun τ => PointWell.block_of_moeb_eq _ hle hp x'.2 x.2 τ (h5 τ).symm))
  let x0 : (U.X k).dom := ⟨x0F (U.X k), IW.orth_mem_dom (U.X k) _ (isOrth_x0F (U.X k))⟩
  refine ⟨fun v => if h : ∃ x : (U.X k).dom,
      flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1) = v then lf h.choose else lf x0,
    fun x => ?_⟩
  have h : ∃ x' : (U.X k).dom, flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x'.1) =
      flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1) := ⟨x, rfl⟩
  simp only [dif_pos h]
  rw [hlf]
  exact hwell _ _ (flat_inj h.choose_spec)

end GlobalTheory.LieBase.UnifExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComponentUniformisationBoundedDomainCompleStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_componentUniformisation_boundedDomain_complexPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∃ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) := by
  first | exact @GlobalTheory.LieBase.UnifExists.exists_unif | exact GlobalTheory.LieBase.UnifExists.exists_unif | (intros; apply GlobalTheory.LieBase.UnifExists.exists_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationFibreArithmeticGroupRelat
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationFibreArithmeticGroupRelat
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnifFibre

theorem fibre_gamma : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ v = ψ w → ∃ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), moebI γ (unflat v) = unflat w := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ v hv w hw hvw
  have hjr : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right Dw.p Dw.q
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by
    have := (hU.2.1 k).1
    omega
  have hflat : ∀ u : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat u) = u := by
    intro u; funext ⟨i, a, b⟩; rfl
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) hjr (U.X k).Ψ
    (Equiv.refl _) hp (unflat v) hv
  obtain ⟨x', hx', hxw⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) hjr (U.X k).Ψ
    (Equiv.refl _) hp (unflat w) hw
  have h1 := hψ ⟨x, hx⟩
  have h2 := hψ ⟨x', hx'⟩
  simp only at h1 h2
  rw [hxv, hflat] at h1
  rw [hxw, hflat] at h2
  have h3 : cxPt T.Z (U.un k ⟨x, hx⟩) = cxPt T.Z (U.un k ⟨x', hx'⟩) := by
    rw [← h1, ← h2, hvw]
  have h4 : (U.un k ⟨x, hx⟩).x = (U.un k ⟨x', hx'⟩).x := by
    have h5 := congrArg Subtype.val h3
    simp only [cxPt] at h5
    haveI := T.Z.jQ_open
    have h6 := (cancel_mono T.Z.jQ).1 h5
    have h7 := congrArg (· ≫ CategoryTheory.Limits.pullback.fst _ _) h6
    simp only [GlobalTheory.AllWt.ptF] at h7
    rwa [CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Limits.pullback.lift_fst] at h7
  obtain ⟨b, hb, hb0, hm, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hG k ⟨x, hx⟩ _ h4
  obtain ⟨γ, hγ, b', hb', heq⟩ := (hU.2.2.2.1 k k ⟨_, hm⟩ ⟨x', hx'⟩).1 ⟨t, ht⟩
  have hx'eq : x' = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact γ (ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) b' :=
    eq_of_heq (Sigma.mk.inj_iff.1 heq).2
  refine ⟨GlobalTheory.TrueCx.toUpq (U.X k) hjr (Equiv.refl (U.X k).Ψ) γ, Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩, ?_⟩
  rw [← hxv, ← hxw, hx'eq, GlobalTheory.TrueCx.domPt_rmul _ _ _ hb', GlobalTheory.TrueCx.domPt_lact _ _ _ hp γ hm]
  rw [hp] at hb0
  rw [GlobalTheory.PointOfFrames.domPt_rmul_block _ _ _ _ b hb hb0]

end GlobalTheory.UnifFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationFibreArithmeticGroupRelatStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentUniformisation_fibre_arithmeticGroup_related : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ v = ψ w → ∃ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), moebI γ (unflat v) = unflat w := by
  first | exact @GlobalTheory.UnifFibre.fibre_gamma | exact GlobalTheory.UnifFibre.fibre_gamma | (intros; apply GlobalTheory.UnifFibre.fibre_gamma <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationArithmeticGroupInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationArithmeticGroupInvariant
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnfInv

theorem one_mem_bor {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) :
    (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  intro τ
  refine ⟨?_, fun a b hab => ?_⟩
  · change ¬ (1 : Matrix (Fin r) (Fin r) ℂ).det = 0
    simp
  · simp [Matrix.one_apply, (ne_of_lt hab).symm]

theorem rmul_one {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    ReciprocityTheory.ChartRestriction.G.FD.rmul x (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = x := by
  funext τ
  show ReciprocityTheory.ChartRestriction.G.FD.mat x τ * ReciprocityTheory.ChartRestriction.G.FD.mat (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) τ = x τ
  rw [show ReciprocityTheory.ChartRestriction.G.FD.mat (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) τ = 1 from rfl,
    Matrix.mul_one]
  rfl

theorem psi_moebI_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ (flat (moebI γ (unflat v))) = ψ v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ γ hγ v hv
  obtain ⟨-, hk, -, h4, -⟩ := hU
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hk k).1]; omega
  haveI : IsOpenImmersion j := hL.1
  have hinj : Function.Injective (GlobalTheory.LieBase.cxOf (Z := T.Z) e σ hj) := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact (cancel_mono j).1 this
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.1 hγ
  obtain ⟨x, hx, hxv⟩ := FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) (Nat.le_add_right Dw.p Dw.q)
    (U.X k).Ψ (Equiv.refl _) hp0 (unflat v) hv
  have hx' : ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x ∈ (U.X k).dom := GlobalTheory.Reg.GenericFrameDensity.lact_mem_dom _ hγ₀ hx
  have hdom : domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x) =
      moebI (toUpq (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) γ₀) (unflat v) := by
    rw [domPt_lact (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) hp0 γ₀ hx]
    exact congrArg _ hxv
  have h1 := hψ ⟨x, hx⟩
  have h2 := hψ ⟨_, hx'⟩
  simp only at h1 h2
  rw [hxv] at h1
  rw [hdom] at h2
  apply hinj
  have h1' : GlobalTheory.LieBase.cxOf (Z := T.Z) e σ hj (ψ v) = cxPt T.Z (U.un k ⟨x, hx⟩) := h1
  rw [h2, h1']
  apply GlobalTheory.ShFam.cxPt_congr
  have hx'' : (⟨k, (⟨ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x, hx'⟩ : (U.X k).dom).1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) =
      ⟨k, ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ (⟨x, hx⟩ : (U.X k).dom).1)
        (fun _ => (1 : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) ℂ))⟩ := by
    rw [rmul_one]
  obtain ⟨t, ht⟩ := (h4 k k ⟨x, hx⟩ ⟨_, hx'⟩).2 ⟨γ₀, hγ₀, _, one_mem_bor _ _, hx''⟩
  exact ht.1

end GlobalTheory.UnfInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationArithmeticGroupInvariantStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentUniformisation_arithmeticGroup_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ (flat (moebI γ (unflat v))) = ψ v := by
  first | exact @GlobalTheory.UnfInv.psi_moebI_eq | exact GlobalTheory.UnfInv.psi_moebI_eq | (intros; apply GlobalTheory.UnfInv.psi_moebI_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulConjTransposeEq
noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal Topology

namespace GlobalTheory.BoundedFundDomain

theorem exists_section {G Y : Type} [Group G] [Countable G] [TopologicalSpace Y] [SecondCountableTopology Y]
    [T2Space Y] [MeasurableSpace Y] [BorelSpace Y] (a : G → Y → Y) (hc : ∀ g, Continuous (a g))
    (hmul : ∀ g h y, a (g * h) y = a g (a h y)) (hone : ∀ y, a 1 y = y)
    (hfin : ∀ y, ∃ W ∈ 𝓝 y, {g | a g y ∈ W}.Finite) :
    ∃ F : Set Y, MeasurableSet F ∧ (∀ y, ∃ g, a g y ∈ F) ∧ ∀ y ∈ F, ∀ g, a g y ∈ F → a g y = y := by
  classical
  obtain ⟨B, hB⟩ := ((TopologicalSpace.countable_countableBasis Y).insert ∅).exists_eq_range
    (Set.insert_nonempty _ _)
  have hBo : ∀ n, IsOpen (B n) := fun n => by
    have : B n ∈ insert ∅ (TopologicalSpace.countableBasis Y) := hB ▸ Set.mem_range_self n
    rcases this with h | h
    · rw [h]; exact isOpen_empty
    · exact TopologicalSpace.isOpen_of_mem_countableBasis h
  let P : ℕ → Y → Prop := fun n y => ∃ g, a g y ∈ B n ∧ ∀ g', a g' y ∈ B n → a g' y = a g y
  have hP : ∀ n g y, P n y → P n (a g y) := by
    rintro n g y ⟨k, hk, hk'⟩
    have e : a (k * g⁻¹) (a g y) = a k y := by rw [← hmul, inv_mul_cancel_right]
    refine ⟨k * g⁻¹, e ▸ hk, fun g' h => ?_⟩
    rw [e, ← hmul] at *
    exact hk' _ h
  have hP' : ∀ n g y, P n (a g y) → P n y := fun n g y h => by
    have := hP n g⁻¹ _ h
    rwa [← hmul, inv_mul_cancel, hone] at this
  have hm : ∀ n g, MeasurableSet {y | a g y ∈ B n} := fun n g => ((hBo n).preimage (hc g)).measurableSet
  have hPm : ∀ n, MeasurableSet {y | P n y} := fun n => by
    simp only [P, Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
    refine MeasurableSet.iUnion fun g => (hm n g).inter (MeasurableSet.iInter fun g' => ?_)
    have := (hm n g').compl.union (isClosed_eq (hc g') (hc g)).measurableSet
    convert this using 1
    ext y
    by_cases h : a g' y ∈ B n <;> simp [h]
  have hex : ∀ y, ∃ n, P n y := fun y => by
    obtain ⟨W, hW, hf⟩ := hfin y
    have hcl : IsClosed (((fun g => a g y) '' {g | a g y ∈ W}) \ {y}) := ((hf.image _).subset Set.sdiff_subset).isClosed
    have hn : W ∩ (((fun g => a g y) '' {g | a g y ∈ W}) \ {y})ᶜ ∈ 𝓝 y :=
      Filter.inter_mem hW (hcl.isOpen_compl.mem_nhds fun h => h.2 rfl)
    obtain ⟨U, hU, hyU, hUW⟩ := (TopologicalSpace.isBasis_countableBasis Y).mem_nhds_iff.1 hn
    obtain ⟨n, rfl⟩ : U ∈ Set.range B := hB ▸ Set.mem_insert_of_mem _ hU
    refine ⟨n, 1, by rwa [hone], fun g' h => ?_⟩
    rw [hone]
    by_contra hne
    exact (hUW h).2 ⟨⟨g', (hUW h).1, rfl⟩, hne⟩
  refine ⟨⋃ n, B n ∩ ({y | P n y} ∩ ⋂ m, ⋂ _ : m < n, {y | P m y}ᶜ), ?_, fun y => ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hBo n).measurableSet.inter ((hPm n).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hPm m).compl))
  · have h := Nat.find_spec (hex y)
    obtain ⟨g, hg, -⟩ := id h
    exact ⟨g, Set.mem_iUnion.2 ⟨_, hg, hP _ g y h,
      Set.mem_iInter₂.2 fun m hm h' => Nat.find_min (hex y) hm (hP' _ _ _ h')⟩⟩
  · intro y hy g hg
    obtain ⟨n, h1, h2, h3⟩ := Set.mem_iUnion.1 hy
    obtain ⟨n', h1', h2', h3'⟩ := Set.mem_iUnion.1 hg
    rcases lt_trichotomy n n' with h | rfl | h
    · exact (Set.mem_iInter₂.1 h3' n h (hP _ g _ h2)).elim
    · obtain ⟨k, -, hk⟩ := h2
      rw [hk g h1', ← hk 1 (by rwa [hone]), hone]
    · exact (Set.mem_iInter₂.1 h3 n' h (hP' _ g _ h2')).elim

variable {p q : ℕ}

def majMat (w : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Jpq p q + (2 : ℂ) • (fromRows w (1 : Matrix (Fin q) (Fin q) ℂ) * (hQ w)⁻¹ *
    (fromRows w (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ)

theorem mul_conjTranspose_eq {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    g.1 * g.1ᴴ = majMat (moeb g.1 0) := by
  have h0 := zero_mem_hcDom p q
  have hu := kapQ_isUnit hg h0
  have h1 := hQ_moeb hg h0
  have h2 := moeb_mul_kapQ hg h0
  have h3 := upq_right hg
  have hd : kapQ g 0 = g.1.toBlocks₂₂ := by simp [kapQ]
  rw [hd] at hu h1 h2
  rw [Matrix.mul_zero, zero_add] at h2
  set w := moeb g.1 0
  set G := g.1
  have h4 : (hQ w)⁻¹ = G.toBlocks₂₂ * G.toBlocks₂₂ᴴ := by
    apply inv_eq_left_inv
    have h5 : G.toBlocks₂₂ᴴ * hQ w * G.toBlocks₂₂ = 1 := by rw [h1]; simp [hQ]
    rw [Matrix.mul_assoc]
    exact mul_eq_one_comm.1 h5
  have h6 : fromRows w (1 : Matrix (Fin q) (Fin q) ℂ) * G.toBlocks₂₂ = fromRows G.toBlocks₁₂ G.toBlocks₂₂ := by
    rw [fromRows_mul, h2, Matrix.one_mul]
  rw [majMat, h4, ← h3, ← Matrix.mul_assoc, Matrix.mul_assoc _ G.toBlocks₂₂ᴴ, ← conjTranspose_mul, h6]
  ext a b
  have e : ∀ a c, fromRows G.toBlocks₁₂ G.toBlocks₂₂ a c = G a (Sum.inr c) := by
    rintro (a | a) c <;> rfl
  simp only [Jpq, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, conjTranspose_apply, Fintype.sum_sum_type, e,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.neg_apply,
    Matrix.zero_apply]
  simp [Matrix.one_apply]
  ring

theorem continuousAt_majMat {w : Matrix (Fin p) (Fin q) ℂ} (hw : w ∈ hcDom p q) : ContinuousAt majMat w := by
  have h : (hQ w).PosDef := hw
  have hQc : Continuous (hQ (p := p) (q := q)) := by unfold hQ; fun_prop
  have h1 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (hQ w)⁻¹) w := by
    refine ContinuousAt.comp (continuousAt_matrix_inv _ ?_) hQc.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ h.det_pos.ne'
  have h2 : Continuous fun w : Matrix (Fin p) (Fin q) ℂ => fromRows w (1 : Matrix (Fin q) (Fin q) ℂ) := by
    refine continuous_matrix ?_
    rintro (a | a) c
    · simp only [fromRows_apply_inl]; fun_prop
    · simp only [fromRows_apply_inr]; fun_prop
  have h3 : Continuous fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ =>
      Jpq p q + (2 : ℂ) • (fromRows x.1 (1 : Matrix (Fin q) (Fin q) ℂ) * x.2 *
        (fromRows x.1 (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ) :=
    continuous_const.add ((((h2.comp continuous_fst).matrix_mul continuous_snd).matrix_mul
      (h2.comp continuous_fst).matrix_conjTranspose).const_smul (2 : ℂ))
  have h4 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (w, (hQ w)⁻¹)) w := continuousAt_id.prodMk h1
  exact ContinuousAt.comp (f := fun w : Matrix (Fin p) (Fin q) ℂ => (w, (hQ w)⁻¹)) h3.continuousAt h4

theorem exists_bound {w : Matrix (Fin p) (Fin q) ℂ} (hw : w ∈ hcDom p q) :
    ∃ C : ℝ, ∀ᶠ w' in 𝓝 w, ∀ g ∈ Upq p q, moeb g.1 0 = w' → ∀ a b, ‖g.1 a b‖ ≤ C := by
  have h : ContinuousAt (fun w => ‖(majMat (p := p) (q := q) w).trace‖) w :=
    ((continuous_id.matrix_trace).continuousAt.comp (continuousAt_majMat hw)).norm
  refine ⟨√(‖(majMat w).trace‖ + 1), ?_⟩
  filter_upwards [h.eventually (gt_mem_nhds (lt_add_one _))] with w' hw' g hg e a b
  rw [← e, ← mul_conjTranspose_eq hg] at hw'
  refine Real.le_sqrt_of_sq_le (le_trans ?_ hw'.le)
  have e2 : (g.1 * g.1ᴴ).trace = ((∑ a, ∑ b, ‖g.1 a b‖ ^ 2 : ℝ) : ℂ) := by
    simp [trace, Matrix.mul_apply, Complex.mul_conj']
  rw [e2, Complex.norm_real]
  refine le_trans ?_ (le_abs_self _)
  exact (Finset.single_le_sum (f := fun b => ‖g.1 a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, ‖g.1 a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a))

theorem norm_mul_mul_le {n : Type} [Fintype n] (A M B : Matrix n n ℂ) {C : ℝ} (h : ∀ a b, ‖M a b‖ ≤ C) (a b : n) :
    ‖(A * M * B) a b‖ ≤ ∑ d, (∑ c, ‖A a c‖ * C) * ‖B d b‖ := by
  simp only [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)) (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h c d) (norm_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} (X : Data E r) (hj : j ≤ r) {Tau : Type}
  [Fintype Tau] (κ : Tau ≃ X.Ψ)

theorem eventually_finite (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : Pt Tau j (r - j)}
    (hw : w ∈ DomI Tau j (r - j)) :
    ∃ W ∈ 𝓝 w, {γ : GL (Fin r) E | γ ∈ X.Γ ∧ domPt X hj κ (lact γ x) ∈ W}.Finite := by
  choose C hC using fun t => exists_bound (hw t)
  obtain ⟨R, hR⟩ := (Set.finite_range fun s : Tau × Fin r × Fin r =>
    ∑ d, (∑ c, ‖mat (x0F X) (κ s.1) s.2.1 c‖ * C s.1) * ‖(mat x (κ s.1))⁻¹ d s.2.2‖).bddAbove
  refine ⟨_, Filter.eventually_all.2 fun t => (continuous_apply t).continuousAt.eventually (hC t),
    (GlobalTheory.LatFin.finite_automorphisms r X R).subset ?_⟩
  rintro γ ⟨hγ, h⟩
  refine ⟨X.Γ_stab γ hγ, fun τ a b => ?_⟩
  obtain ⟨t, rfl⟩ := κ.surjective τ
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp (KU.isOrth_lact X hγ hx) (κ t)
  have h1 := h t g hg (by rw [e]; rfl)
  have e2 : γ.1.map (κ t).1 = mat (x0F X) (κ t) * g.1.submatrix (idx hj) (idx hj) * (mat x (κ t))⁻¹ := by
    have hu : IsUnit (mat x (κ t)).det := (ExF.det_ne_of_orth X hx _).isUnit
    rw [e, frameCo, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id,
      mul_nonsing_inv_cancel_left _ _ (det_x0F X _).isUnit]
    exact (mul_nonsing_inv_cancel_right _ _ hu).symm
  have h2 := norm_mul_mul_le (mat (x0F X) (κ t)) (g.1.submatrix (idx hj) (idx hj)) (mat x (κ t))⁻¹
    (fun a b => h1 _ _) a b
  rw [← e2] at h2
  exact h2.trans (hR ⟨(t, a, b), rfl⟩)

theorem exists_isFD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∃ F, IsFD (gammaU X hj κ) F := by
  intro E _ _ _ r j X hj Tau _ κ hp
  have := KU.countable_Γ X
  obtain ⟨hO, hD⟩ := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_and_fderiv_moebI Tau j (r - j)
  have hU : ∀ γ : X.Γ, toUpq X hj κ γ ∈ UpqI Tau j (r - j) := fun γ => gammaU_le X hj κ hp (Subgroup.mem_map_of_mem _ γ.2)
  have hmem : ∀ (γ : X.Γ), ∀ z ∈ DomI Tau j (r - j), moebI (toUpq X hj κ γ) z ∈ DomI Tau j (r - j) :=
    fun γ z hz t => moeb_mem (g := toUpq X hj κ γ t) (z := z t) (hU γ t trivial) (hz t)
  let a : X.Γ → DomFlat Tau j (r - j) → DomFlat Tau j (r - j) := fun γ v =>
    ⟨flat (moebI (toUpq X hj κ γ) (unflat v.1)), hmem γ _ v.2⟩
  have hx : ∀ v : DomFlat Tau j (r - j), ∃ x, IsOrth X x ∧ unflat v.1 = domPt X hj κ x := fun v => by
    obtain ⟨x, hx, e⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E r j X hj Tau κ hp _ v.2
    obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
    exact ⟨x1, h1, by rw [← e, domPt_rmul X hj κ hb]⟩
  have hdom : ∀ {x}, IsOrth X x → x ∈ X.dom := fun h => KU.orth_dom X h
  have ha : ∀ (γ : X.Γ) v x, IsOrth X x → unflat v.1 = domPt X hj κ x →
      unflat (a γ v).1 = domPt X hj κ (lact γ x) := fun γ v x h e => by
    rw [domPt_lact X hj κ hp _ (hdom h), ← e]; rfl
  have hinj : ∀ v w : DomFlat Tau j (r - j), unflat v.1 = unflat w.1 → v = w := fun v w h =>
    Subtype.ext (congrArg flat h)
  have hcont : ∀ γ, Continuous (a γ) := fun γ => by
    have h : Continuous fun v : DomFlat Tau j (r - j) => flat (moebI (toUpq X hj κ γ) (unflat v.1)) :=
      continuousOn_iff_continuous_restrict.1 (hD _ (hU γ)).1.continuousOn
    exact h.subtype_mk _
  obtain ⟨F, hF, h1, h2⟩ := exists_section a hcont
    (fun γ δ v => by
      obtain ⟨x, h, e⟩ := hx v
      refine hinj _ _ ?_
      rw [ha _ _ _ h e, ha _ _ _ (KU.isOrth_lact X δ.2 h) (ha _ _ _ h e), KU.lact_lact]; rfl)
    (fun v => by
      obtain ⟨x, h, e⟩ := hx v
      refine hinj _ _ ?_
      rw [ha _ _ _ h e, e, OneMemClass.coe_one, KU.lact_one])
    (fun v => by
      obtain ⟨x, h, e⟩ := hx v
      obtain ⟨W, hW, hf⟩ := eventually_finite X hj κ hp h v.2
      have hc : Continuous fun v : DomFlat Tau j (r - j) => unflat v.1 :=
        continuous_pi fun t => continuous_matrix fun a b => (continuous_apply (t, a, b)).comp continuous_subtype_val
      refine ⟨_, hc.continuousAt.preimage_mem_nhds hW, (hf.preimage Subtype.val_injective.injOn).subset ?_⟩
      intro γ hγ
      exact ⟨γ.2, by rw [← ha γ v x h e]; exact hγ⟩)
  refine ⟨Subtype.val '' F, (MeasurableEmbedding.subtype_coe hO.measurableSet).measurableSet_image.2 hF,
    Subtype.coe_image_subset _ _, fun z hz => ?_, ?_⟩
  · obtain ⟨γ, h⟩ := h1 ⟨flat z, hz⟩
    exact ⟨_, ⟨γ, γ.2, rfl⟩, _, h, rfl⟩
  · have he : {z | z ∈ Subtype.val '' F ∧ ∃ γ ∈ gammaU X hj κ,
        flat (moebI γ (unflat z)) ∈ Subtype.val '' F ∧ moebI γ (unflat z) ≠ unflat z} = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro _ ⟨⟨v, hv, rfl⟩, _, ⟨γ, hγ, rfl⟩, ⟨w, hw, e⟩, hne⟩
      have e' : w = a ⟨γ, hγ⟩ v := Subtype.ext e
      exact hne (congrArg (fun v => unflat v.1) (h2 v hv ⟨γ, hγ⟩ (e' ▸ hw)))
    rw [he, measure_empty]

end GlobalTheory.BoundedFundDomain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricPointClassFormMassEqCovolume
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.BaseVolume

theorem mass_openPart_eq_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ptsIn X.str (σ.comp e.toRingHom) (openPart j)) = ENNReal.ofReal (GlobalTheory.TrueCx.covol (U.X k)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL
  have hj' : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k).1; omega
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_componentUniformisation_boundedDomain_complexPoints E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL
  have himg := GlobalTheory.T.uniformisation_image_boundedDomain_eq_openPart E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hfib := GlobalTheory.T.componentUniformisation_fibre_arithmeticGroup_related E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hinv := GlobalTheory.T.componentUniformisation_arithmeticGroup_invariant E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hdens := GlobalTheory.T.chernTopPart_hodgeMetric_uniformisation_image E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hnull := GlobalTheory.T.uniformisation_null_sets_to_pointClass_null E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  obtain ⟨FD, hFD⟩ := GlobalTheory.BoundedFundDomain.exists_isFD E (Dw.p + Dw.q) Dw.p (U.X k) hj' (U.X k).Ψ (Equiv.refl _) hp
  obtain ⟨hlt, hcov⟩ := GlobalTheory.FlagFibre.covol_eq_muD E (Dw.p + Dw.q) Dw.p (U.X k) hj' (U.X k).Ψ (Equiv.refl _) hp FD hFD
  obtain ⟨hFm, hFsub, hFcov, hFbad⟩ := hFD
  set μD := muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hμD
  set Bad := {v | v ∈ FD ∧ ∃ γ ∈ gammaU (U.X k) hj' (Equiv.refl (U.X k).Ψ), flat (moebI γ (unflat v)) ∈ FD ∧
    moebI γ (unflat v) ≠ unflat v} with hBad
  set B' := toMeasurable μD Bad with hB'
  have hB'0 : μD B' = 0 := by rw [hB', measure_toMeasurable]; exact hFbad
  have hfu : ∀ v : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat v) = v := fun v => rfl
  have hinj : Set.InjOn ψ (FD \ B') := by
    intro v hv w hw hvw
    obtain ⟨γ, hγ, hγe⟩ := hfib v (hFsub hv.1) w (hFsub hw.1) hvw
    have hnb : v ∉ Bad := fun h => hv.2 (subset_toMeasurable _ _ h)
    have h1 : moebI γ (unflat v) = unflat v := by
      by_contra hne
      exact hnb ⟨hv.1, γ, hγ, by rw [hγe, hfu]; exact hw.1, hne⟩
    rw [← hfu v, ← hfu w, ← hγe, h1]
  have hD := hdens (FD \ B') (Set.diff_subset.trans hFsub) (hFm.diff (measurableSet_toMeasurable _ _)) hinj
  have hN := hnull (FD ∩ B') (Set.inter_subset_left.trans hFsub) (measure_mono_null Set.inter_subset_right hB'0)
  have hmF : μD (FD \ B') = μD FD := measure_diff_null hB'0
  have hsub : ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ⊆ ψ '' (FD \ B') ∪ ψ '' (FD ∩ B') := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨γ, hγ, hγF⟩ := hFcov (unflat v) hv
    rw [← Set.image_union, Set.diff_union_inter, ← hinv γ hγ v hv]
    exact Set.mem_image_of_mem _ hγF
  have hsup : ψ '' (FD \ B') ⊆ ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) :=
    Set.image_mono (Set.diff_subset.trans hFsub)
  rw [← himg, hcov, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hlt.ne, ← hmF, ← hD]
  refine le_antisymm ?_ (measure_mono hsup)
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hN, add_zero]

end GlobalTheory.BaseVolume
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricPointClassFormMassEqCovolumeStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_pointClassForm_mass_eq_covolume : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ptsIn X.str (σ.comp e.toRingHom) (openPart j)) = ENNReal.ofReal (GlobalTheory.TrueCx.covol (U.X k)) := by
  first | exact @GlobalTheory.BaseVolume.mass_openPart_eq_covol | exact GlobalTheory.BaseVolume.mass_openPart_eq_covol | (intros; apply GlobalTheory.BaseVolume.mass_openPart_eq_covol <;> assumption)
end
