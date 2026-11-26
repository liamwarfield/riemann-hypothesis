module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceTupleThetaComparisonNormalisedDat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ModelExpCoord

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_unique)

theorem coord_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (n : ℕ) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))) (p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)) (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (V : (gen Z).affineOpens) (v : Sp (DualNumber Γ(gen Z, V.1)) ⟶ Z.t.G.left), IsOpen B → (∀ b, IsPeriod (Fu.Di i) ty (P b)) → (∀ a, DifferentiableOn ℂ (fun b => P b a) B) → (∀ b, p b ≫ pullback.snd _ _ = spMap σ) → IsTanAtG Z.t (LogKS.chart V ≫ genι Z) v → ∃ W : (Fin n → ℂ) → (Fin g → ℂ), DifferentiableOn ℂ W {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} ∧ ∀ b ∈ B, ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), y.1 = p b ≫ Z.jQ → IsDerivAt0 (fun z => GlobalTheory.ShFam.Hor.LogCh.liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b) (spMap (Formalism.L2.Pj.dualMap (evHom hy)) ≫ v) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g ty Fu i n B P p hu V v hB hP hPd hs hv
  classical
  have h1 := Fu.hol i n B P hB ⟨fun b _ => hP b, hPd⟩
  have hp : IsHolTo B p := TrueCx.TorHolo.isHolTo_of_fst _ _ hB (spMap σ) hs
    (LocLift.isHolTo_congr h1.1 fun b _ => (hu b).symm)
  have h2 := TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 hB (fun b z => (Fu.ex i (P b) z).left) p h1.2 hp
    (fun b z => by rw [Over.w (Fu.ex i (P b) z), ← hu b]; rfl)
  have hFt : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) =>
      liftEx Z Fu (p bz.1) i (P bz.1) (hu bz.1) bz.2 ≫ Z.m.φ) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  have hY : IsHolTo B fun b => p b ≫ Z.jQ := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hp Z.jQ
  set B' := {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} with hB'def
  have hB' : IsOpen B' := (hY V.1 0).1
  let yb : (Fin n → ℂ) → CxPts (genStr Z) σ := fun b =>
    ⟨p b ≫ Z.jQ, by rw [Category.assoc, Z.jQ_over]; exact hs b⟩
  have hm : ∀ b, ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 → yb b ∈ ptsIn (genStr Z) σ V.1 := fun b h => h
  have hExp : ∀ b, IsExpAt Z.t (p b ≫ Z.jQ ≫ genι Z)
      (pushEx Z Fu (p b) i (P b) (p b ≫ Z.jQ ≫ genι Z) (hu b) rfl) := fun b =>
    isExpAt_pushEx E H Dw l Xo c O β Z g ty _ Fu (p b) i (P b) (p b ≫ Z.jQ ≫ genι Z) (hu b) rfl (hP b)
  have hTan : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1),
      IsTanAtG Z.t (p b ≫ Z.jQ ≫ genι Z) (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h =>
    isTan_map (evHom (hm b h)) (by rw [← Category.assoc, spMap_evHom]; rfl) hv
  have hW0 : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), ∃! w, IsDerivAt0
      (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) w
      (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h =>
    (hExp b).2.2 _ (hTan b h)
  let W : (Fin n → ℂ) → Fin g → ℂ := fun b =>
    if h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 then (hW0 b h).exists.choose else 0
  have hWd : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), IsDerivAt0
      (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h => by
    have e : W b = (hW0 b h).exists.choose := dif_pos h
    rw [e]
    exact (hW0 b h).exists.choose_spec
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hdiff : ∀ b₀ ∈ B', DifferentiableAt ℂ W b₀ := fun b₀ hb₀ => by
    have h₀ : ⊤ ≤ (p b₀ ≫ Z.jQ) ⁻¹ᵁ V.1 := hb₀.2
    let ev : (Fin n → ℂ) → (Γ(gen Z, V.1) →+* ℂ) := fun b =>
      if h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 then evHom (hm b h) else evHom (hm b₀ h₀)
    have hevb : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), ev b = evHom (hm b h) := fun b h => dif_pos h
    have hev : ∀ cc, DifferentiableAt ℂ (fun b => ev b cc) b₀ :=
      HolLieFrame.differentiableAt_ev (B := B') (LocLift.isHolTo_mono hY hB' fun b hb => hb.1) (LogKS.chart V) ev
        (fun b hb => by rw [hevb b hb.2]; exact (spMap_evHom (hm b hb.2)).symm) hb₀
    have hder : ∀ b ∈ B', IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
        (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ v) := fun b hb => by
      rw [hevb b hb.2]
      exact hWd b hb.2
    refine HolLieFrame.differentiableAt_of_forms W b₀ fun w hw => ?_
    have hw' : ∀ (O : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, O)),
        ⊤ ≤ (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) 0 ≫ Z.m.φ) ⁻¹ᵁ O →
        fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) O f) 0 w = 0 := by
      intro O f hO
      refine hw (fun b => fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) O f) 0)
        (HolLieFrame.differentiableAt_fderiv
          (e := fun b z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) hFt hb₀.1 O f hO) ?_
      obtain ⟨Fn, hF, hF'⟩ := HolLieFrame.exists_hol_snd v ev b₀ hev O f
        ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [(hder b₀ hb₀).1]; exact hO))
      refine hF.congr_of_eventuallyEq ?_
      filter_upwards [hF', hB'.mem_nhds hb₀] with b ⟨h, e'⟩ hb
      exact ((hder b hb).2 O h f).symm.trans e'
    have d₁ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) w hw'
    have d₀ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) 0
      fun _ _ _ => map_zero _
    obtain ⟨u, ⟨hut, hud⟩, -⟩ := (hExp b₀).2.1 0
    have hu0 := isDerivAt0_unique hud d₀
    obtain ⟨w', -, hw''⟩ := (hExp b₀).2.2 u hut
    have a1 : w = w' := hw'' w (by rw [hu0]; exact d₁)
    have a0 : (0 : Fin g → ℂ) = w' := hw'' 0 hud
    exact a1.trans a0.symm
  refine ⟨W, fun b hb => (hdiff b hb).differentiableWithinAt, fun b _ y hy hyb => ?_⟩
  have hyb' : y = yb b := Subtype.ext hyb
  subst hyb'
  exact hWd b hy

end GlobalTheory.ModelExpCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMapStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expCoordinates_tangentField_holomorphic_periodMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (n : ℕ) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))) (p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)) (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (V : (gen Z).affineOpens) (v : Sp (DualNumber Γ(gen Z, V.1)) ⟶ Z.t.G.left), IsOpen B → (∀ b, IsPeriod (Fu.Di i) ty (P b)) → (∀ a, DifferentiableOn ℂ (fun b => P b a) B) → (∀ b, p b ≫ pullback.snd _ _ = spMap σ) → IsTanAtG Z.t (LogKS.chart V ≫ genι Z) v → ∃ W : (Fin n → ℂ) → (Fin g → ℂ), DifferentiableOn ℂ W {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} ∧ ∀ b ∈ B, ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), y.1 = p b ≫ Z.jQ → IsDerivAt0 (fun z => GlobalTheory.ShFam.Hor.LogCh.liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b) (spMap (Formalism.L2.Pj.dualMap (evHom hy)) ≫ v) := by
  first | exact @GlobalTheory.ModelExpCoord.coord_holomorphic | exact GlobalTheory.ModelExpCoord.coord_holomorphic | (intros; apply GlobalTheory.ModelExpCoord.coord_holomorphic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsProduct
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem psiCoord_associated {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {χ : D.X} {r r' : R}
    (h : PsiCoord D χ r) (h' : PsiCoord D χ r') : Associated r r' := by
  obtain ⟨x, hx, ex⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r).1 h
  obtain ⟨x', hx', ex'⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r').1 h'
  obtain ⟨u, hu⟩ := hx.unique hx'
  have e1 : algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u * r') := by
    rw [← ex, hu, map_mul, ← ex']
    rfl
  have e2 : r = u * r' := IsFractionRing.injective R (FractionRing R) e1
  exact ⟨u⁻¹, by rw [e2, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩

end GlobalTheory.TorRef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory

theorem dickson_finite_below_every {ι : Type} (n : ℕ) (f : ι → Fin n → ℕ) :
    ∃ F : Finset ι, ∀ i, ∃ j ∈ F, f j ≤ f i := by
  classical
  set s : Set (Fin n → ℕ) := Set.range f
  have hpwo : s.IsPWO := Set.isPWO_of_wellQuasiOrderedLE s
  set m : Set (Fin n → ℕ) := {x | Minimal (· ∈ s) x}
  have hm : m.Finite := (setOf_minimal_antichain (· ∈ s)).finite_of_partiallyWellOrderedOn
    (hpwo.mono (fun x hx => hx.prop))
  have hpre : ∀ x ∈ m, ∃ j, f j = x := fun x hx => hx.prop
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, fun i => isEmptyElim i⟩
  choose! g hg using hpre
  refine ⟨hm.toFinset.image g, fun i => ?_⟩
  obtain ⟨x, hxi, hx⟩ := hpwo.exists_le_minimal (Set.mem_range_self i)
  exact ⟨g x, Finset.mem_image_of_mem g (hm.mem_toFinset.mpr hx), by rw [hg x hx]; exact hxi⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelowStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dickson_exists_finite_subfamily_below : ∀ {ι : Type} (n : ℕ) (f : ι → Fin n → ℕ), ∃ F : Finset ι, ∀ i, ∃ j ∈ F, f j ≤ f i := by
  first | exact @GlobalTheory.dickson_finite_below_every | exact GlobalTheory.dickson_finite_below_every | (intros; apply GlobalTheory.dickson_finite_below_every <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolDiv

theorem idlAlong_fromSpecStalk {X : Scheme.{0}} (I : X.IdealSheafData) (x : X) {W : Type} [CommRing W] [IsLocalRing W]
    (g : X.presheaf.stalk x →+* W) :
    idlAlong I (Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x) = (FinalTheorems.stalkId I x).map g := by
  obtain ⟨⟨U, hU⟩, hx, -⟩ := EffCartierData.exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have e0 : ∀ (y : X) (hy : y ∈ U), X.fromSpecStalk y = Spec.map (X.presheaf.germ U y hy) ≫ hU'.fromSpec :=
    fun y hy => (hU'.fromSpecStalk_eq_fromSpecStalk hy).symm
  generalize hχ : Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x = χ
  have e1 : χ = Spec.map (X.presheaf.germ U x hx ≫ CommRingCat.ofHom g) ≫ hU'.fromSpec := by
    rw [← hχ, e0 x hx]
    exact (Spec.map_comp_assoc (X.presheaf.germ U x hx) (CommRingCat.ofHom g) hU'.fromSpec).symm
  have hc : χ (closedPoint W) ∈ U := by
    have : χ (closedPoint W) ∈ Set.range hU'.fromSpec :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f => f (closedPoint W)) e1.symm)⟩
    rwa [hU'.range_fromSpec] at this
  have e2 : χ = Spec.map (X.presheaf.germ U _ hc ≫ Scheme.stalkClosedPointTo χ) ≫ hU'.fromSpec := by
    rw [Spec.map_comp, Category.assoc, ← e0 _ hc]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ).symm
  have e3 := Spec.map_injective ((cancel_mono hU'.fromSpec).1 (e1.symm.trans e2))
  unfold idlAlong
  rw [ds_stalkId_eq_map I ⟨U, hU⟩ _ hc, ds_stalkId_eq_map I ⟨U, hU⟩ x hx, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← e3]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.PolDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundary
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

namespace GlobalTheory.ShFam

theorem exists_frPt_cxPt_of_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (y : CxPts (genStr Z) σ), ¬ LiesIn y (genBd Z) → ∀ f : EigFrame Z σ (y.1 ≫ genι Z), ∃ q : FrPt Xo c (CAt σ), cxPt Z q = y ∧ ∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ Z.m.φ = f.v τ k := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ y hy f
  have hr : Set.range y.1 ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    exact not_not.1 hy
  have := Z.jQ_open
  let zF := IsOpenImmersion.lift Z.jQ y.1 hr
  have hzF : zF ≫ Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hs : zF ≫ pullback.snd _ _ = spMap σ := by
    have h2 := y.2
    rw [← hzF, Category.assoc, Z.jQ_over] at h2
    exact h2
  obtain ⟨q, hq, hv⟩ := exists_frPt_ptF_of_eigFrame E H Dw l Xo c O β Z ℂ σ zF (y.1 ≫ genι Z) f hs
    (by rw [← Category.assoc, hzF])
  refine ⟨q, Subtype.ext ?_, hv⟩
  exact (congrArg (· ≫ Z.jQ) hq).trans hzF

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundaryStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedComplexPoint_of_eigenFrame_off_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (y : CxPts (genStr Z) σ), ¬ LiesIn y (genBd Z) → ∀ f : EigFrame Z σ (y.1 ≫ genι Z), ∃ q : FrPt Xo c (CAt σ), cxPt Z q = y ∧ ∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ Z.m.φ = f.v τ k := by
  first | exact @GlobalTheory.ShFam.exists_frPt_cxPt_of_eigFrame | exact GlobalTheory.ShFam.exists_frPt_cxPt_of_eigFrame | (intros; apply GlobalTheory.ShFam.exists_frPt_cxPt_of_eigFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStalkIdealOfCodimOne
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PrincipalHartogs

theorem mem_span_singleton_of_forall_height_le_one {B : Type} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [IsNoetherianRing B] (f s : B)
    (h : ∀ q : Ideal B, q.IsPrime → q.height ≤ 1 → ∃ u, u ∉ q ∧ u * s ∈ Ideal.span {f}) :
    s ∈ Ideal.span {f} := by
  by_cases hf : f = 0
  · subst hf
    obtain ⟨u, hu, hus⟩ := h ⊥ Ideal.isPrime_bot (by simp)
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hus ⊢
    rcases mul_eq_zero.mp hus with h0 | h0
    · exact absurd (h0 ▸ Submodule.zero_mem ⊥) hu
    · exact h0
  let K := FractionRing B
  have hfK : algebraMap B K f ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hf
  let d : Ideal B := (Ideal.span {f}).colon {s}
  have hd : ∀ a, a ∈ d ↔ a * s ∈ Ideal.span {f} := fun a => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul]
  by_cases hd1 : d = ⊤
  · simpa using (hd 1).1 (hd1 ▸ Submodule.mem_top)
  exfalso
  obtain ⟨Q, hQ, hdQ⟩ := Ideal.exists_le_maximal d hd1
  have hreg : ∀ a c : B, algebraMap B K a * (algebraMap B K s / algebraMap B K f) = algebraMap B K c →
      a ∈ d := fun a c e => by
    rw [hd, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul] at e
    rw [mul_comm f c]
    exact IsFractionRing.injective B K e
  obtain ⟨p, hp, -, h1, hpf⟩ := NormalPole.exists_height_one (K := K)
    (algebraMap B K s / algebraMap B K f) Q (fun a c e => hdQ (hreg a c e))
  obtain ⟨u, hu, hus⟩ := h p hp h1.le
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hus
  refine hu (hpf u c ?_)
  rw [← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul, hc]

end GlobalTheory.PrincipalHartogs

namespace GlobalTheory.PrincipalHartogs

end GlobalTheory.PrincipalHartogs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmPinsLev
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}



variable (D) in
def LevOver (i : Fin D.R.m) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)) {G : Type}
    (eG : G → G0 Pg D.R.r) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (Dw : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (iota : ∀ j : ℕ, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E))
    (lev : G → (Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw ((i : ℕ) + 1)).La) : Prop :=
  ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (βW i)
      (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG g) κ ∧
    ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) (Dw ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1,
      finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ iota ((i : ℕ) + 1)) (lev g a)) -
        (finHom (Wc D i) κ).1.mulVec
          (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ iota ((i : ℕ) + 1)) a)) = l.M • w

theorem levOver_iff (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
    (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) :
    LevOver D i R.Pg R.βW R.eG T.Q.l T.Q.Dw T.iota lev ↔ LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev := Iff.rfl

def CoefFam {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) : Prop :=
  ∃ gramR c0R, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L

end Generic

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DividesOfNormBoundedPoints
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Dvd

attribute [local instance] Over.cartesianMonoidalCategory

section Algebra

variable {R : Type} [CommRing R]

theorem mk_le_of_finiteType {D : Type} [CommRing D] (σ : D →+* R) (hσ : σ.FiniteType)
    (h : Cardinal.mk D ≤ Cardinal.continuum) : Cardinal.mk R ≤ Cardinal.continuum := by
  letI := σ.toAlgebra
  have : Algebra.FiniteType D R := hσ
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  refine (Cardinal.mk_le_of_surjective hf).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  exact max_le (max_le h ((Cardinal.lt_aleph0_of_finite _).le.trans Cardinal.aleph0_le_continuum)) Cardinal.aleph0_le_continuum

end Algebra

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_opn (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {x : Z.X} (hx : ∀ x' : Z.X, x' ⤳ x → x' = x) :
    x ∈ Z.opn := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.toPre.s
  have hc := irreducibleComponent_mem_irreducibleComponents x
  have ho := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hc
  have hg := hc.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hc)
  have e := hx _ (hg.specializes mem_irreducibleComponent)
  rw [e] at hg
  obtain ⟨y, hy, hyo⟩ := Z.dense.inter_open_nonempty _ ho ⟨_, mem_irreducibleComponent⟩
  have hopen : IsOpen Z.opn := Z.cover ▸ isOpen_iUnion fun a => (Z.U a).1.isOpen
  exact (hg.specializes hy).mem_open hopen hyo

theorem exists_base (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) :
    ∃ σ : Z.i.c.V W →+* Γ(Z.X, U), σ.Flat ∧ σ.FiniteType := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have := Z.flat
  let σ : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.toPre.s)).hom
  have e : spMap σ = hU.fromSpec ≫ Z.toPre.s := Spec.map_preimage _
  have h1 : Flat (spMap σ) := by rw [e]; infer_instance
  have h2 : LocallyOfFiniteType (spMap σ) := by rw [e]; infer_instance
  exact ⟨σ, (HasRingHomProperty.Spec_iff (P := @Flat)).1 h1, (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h2⟩


end Model

end GlobalTheory.HTLine.Dvd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCells
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellValuativeExistenceOverUnionOfOpens
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellValuativeExistenceOverUnionOfOpens
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Valu

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_surj {k B : Type} [CommRing k] [CommRing B] (x : Sp k ⟶ Sp B) : ∃ β : B →+* k, x = spMap β :=
  ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩

theorem exists_of_closedPoint {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.affineOpens) (hx : x (IsLocalRing.closedPoint A) ∈ (U.1 : Set X)) :
    ∃ φ : Γ(X, U.1) →+* A, x = spMap φ ≫ U.2.fromSpec := by
  have htop : x ⁻¹ᵁ U.1 = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem x hx
  have hr : Set.range x ⊆ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : y ∈ x ⁻¹ᵁ U.1 := by rw [htop]; trivial
    exact this
  have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  obtain ⟨φ, hφ⟩ := sp_surj (B := Γ(X, U.1)) (@IsOpenImmersion.lift _ _ _ U.2.fromSpec x hi hr)
  exact ⟨φ, (@IsOpenImmersion.lift_fac _ _ _ U.2.fromSpec x hi hr).symm.trans (congrArg (· ≫ U.2.fromSpec) hφ)⟩

theorem indep_cellVec {T : Type} {m : T → ℕ} {k : Type} [Field k] {M : ℕ} (D c : Let m → Fin (M + 1) → k) (w : Pm m)
    (x : CellVar m → k) (h : LeftInv D c) (τ : T) :
    LinearIndependent k fun j : Fin (m τ) => cellVec c w x ⟨τ, j⟩ := by
  have h1 := (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m k M D c w x h).1 _ _ (down_std τ (m τ) le_rfl)
  rw [GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.1] at h1
  have h2 := Matrix.linearIndependent_rows_of_det_ne_zero (h1.trans_ne one_ne_zero)
  let L : (Fin (M + 1) → k) →ₗ[k] (Fin (m τ) → k) :=
    Matrix.toLin' (Matrix.of fun l' r => D ((wLet w ∘ std τ (m τ) le_rfl) l') r)
  exact LinearIndependent.of_comp L h2

theorem inBlock_cellVec {T : Type} {m : T → ℕ} {S ι : Type} [CommRing S] {c c' : Let m → ι → S} (h : InBlock c c')
    (w : Pm m) (x : CellVar m → S) : InBlock c (cellVec c' w x) := fun z =>
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h ⟨z.1, w z.1 i⟩)

theorem map_uvec {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens} {S : Type} [CommRing S]
    (c : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) (ψ : CR m U →+* S) :
    (fun z => ψ ∘ uvec c w z) =
      cellVec (fun z => (ψ.comp (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) ∘ c z) w (ψ ∘ MvPolynomial.X) :=
  funext fun z => map_cellVec ψ _ w _ z

theorem sp_cbase {X : Scheme.{0}} {T : Type} {m : T → ℕ} {U : X.affineOpens} {S : Type} [CommRing S]
    (ψ : CR m U →+* S) :
    spMap ψ ≫ cbase m U = spMap (ψ.comp (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) ≫ U.2.fromSpec := by
  rw [cbase, ← Category.assoc, sp_comp]

theorem exists_integral_cell : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (A k : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [Algebra A k] [IsFractionRing A k] b' w' (a : Sp k ⟶ Sp (CR m (V b'))) (x : Sp A ⟶ X), Set.range x ⊆ ⋃ b, ((V b).1 : Set X) → a ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x → ∃ b w, ∃ l : Sp A ⟶ Sp (CR m (V b)), l ≫ cbase m (V b) = x ∧ spMap (algebraMap A k) ≫ l ≫ h b w = a ≫ h b' w' := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hC hP A k _ _ _ _ _ _ b' w' a x hx ha
  obtain ⟨ψ', rfl⟩ := sp_surj a
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hx ⟨IsLocalRing.closedPoint A, rfl⟩)
  obtain ⟨φ, rfl⟩ := exists_of_closedPoint x (V b) hb
  have ha' : spMap ((algebraMap A k).comp φ) ≫ (V b).2.fromSpec =
      spMap (ψ'.comp (MvPolynomial.C : Γ(X, (V b').1) →+* CR m (V b'))) ≫ (V b').2.fromSpec := by
    rw [← sp_cbase, ha, ← Category.assoc, sp_comp]
  obtain ⟨w, y, d, hy, hd, ht⟩ := GlobalTheory.T.exists_integral_flagCell_of_valuedField T m k (ValuationRing.valuation A k).valuationSubring M _ _
    (inBlock_cellVec (hC.compat k b b' _ _ ha') w' (ψ' ∘ MvPolynomial.X))
    (indep_cellVec _ _ w' _ ((hC.inv b').map _))
  have hy' : ∀ v, ∃ t : A, algebraMap A k t = y v := fun v => (ValuationRing.mem_integer_iff A k (y v)).1 (hy v)
  choose t hyt using hy'
  let χ : CR m (V b) →+* A := MvPolynomial.eval₂Hom φ t
  have hχ : χ.comp (MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)) = φ := MvPolynomial.eval₂Hom_comp_C φ t
  have hχ' : ((algebraMap A k).comp χ).comp (MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)) =
      (algebraMap A k).comp φ := by rw [RingHom.comp_assoc, hχ]
  refine ⟨b, w, spMap χ, by rw [sp_cbase, hχ], ?_⟩
  rw [← Category.assoc, sp_comp]
  refine GlobalTheory.T.flagCell_point_eq_of_triangular_frames O K β X s T m M B V α c D P p0 p h hC hP k b b' w w' _ ψ' d ?_ hd ?_
  · rw [sp_cbase, sp_cbase, hχ', ha']
  · have e : ((algebraMap A k).comp χ) ∘ MvPolynomial.X = y := funext fun v => by
      rw [← hyt]
      exact congrArg (algebraMap A k) (MvPolynomial.eval₂Hom_X' φ t v)
    rw [map_uvec, map_uvec, hχ', e]
    exact ht

end GlobalTheory.FlagEmb.Valu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellValuativeExistenceOverUnionOfOpensStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCell_valuativeExistence_over_union_of_opens : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (A k : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [Algebra A k] [IsFractionRing A k] b' w' (a : Sp k ⟶ Sp (CR m (V b'))) (x : Sp A ⟶ X), Set.range x ⊆ ⋃ b, ((V b).1 : Set X) → a ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x → ∃ b w, ∃ l : Sp A ⟶ Sp (CR m (V b)), l ≫ cbase m (V b) = x ∧ spMap (algebraMap A k) ≫ l ≫ h b w = a ≫ h b' w' := by
  first | exact @GlobalTheory.FlagEmb.Valu.exists_integral_cell | exact GlobalTheory.FlagEmb.Valu.exists_integral_cell | (intros; apply GlobalTheory.FlagEmb.Valu.exists_integral_cell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageOpensEqRangeOfValuative
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
namespace GlobalTheory

theorem preimage_opens_eq_range_of_valuative (F Z X : Scheme.{0}) (j : F ⟶ Z) (π : Z ⟶ X) (U : X.Opens)
    (hj : IsOpenImmersion j) (hd : Dense (Set.range j)) (hπ : IsSeparated π)
    (hF : TopologicalSpace.NoetherianSpace F) (hU : Set.range (j ≫ π) ⊆ (U : Set X))
    (hv : ∀ (A K : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K]
      [IsFractionRing A K] (a : Sp K ⟶ F) (b : Sp A ⟶ X), Set.range b ⊆ (U : Set X) →
      a ≫ j ≫ π = spMap (algebraMap A K) ≫ b →
      ∃ l : Sp A ⟶ F, spMap (algebraMap A K) ≫ l = a ∧ l ≫ j ≫ π = b) :
    π ⁻¹' (U : Set X) = Set.range j := by
  have hg : Set.range (j ≫ π).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hU
  let g : F ⟶ U := IsOpenImmersion.lift U.ι (j ≫ π) hg
  have hgfac : g ≫ U.ι = j ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hj' : Set.range j.base ⊆ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨x, rfl⟩
  let j' : F ⟶ (π ⁻¹ᵁ U : Z.Opens) := IsOpenImmersion.lift (π ⁻¹ᵁ U).ι j hj'
  have hj'fac : j' ≫ (π ⁻¹ᵁ U).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hcomp : j' ≫ (π ∣_ U) = g := by
    rw [← cancel_mono U.ι, hgfac, Category.assoc, morphismRestrict_ι, ← Category.assoc, hj'fac]
  haveI : QuasiCompact g := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  haveI : UniversallyClosed g := by
    apply UniversallyClosed.of_valuativeCriterion
    intro S
    obtain ⟨l, hl1, hl2⟩ := hv S.R S.K S.i₁ (S.i₂ ≫ U.ι)
      (by
        rintro _ ⟨x, rfl⟩
        rw [← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩)
      (by rw [← hgfac, ← Category.assoc, S.commSq.w, Category.assoc])
    have hl3 : l ≫ g = S.i₂ := by
      rw [← cancel_mono U.ι, Category.assoc, hgfac, hl2]
    exact ⟨⟨{ l := l, fac_left := hl1, fac_right := hl3 }⟩⟩
  haveI : UniversallyClosed (j' ≫ (π ∣_ U)) := by rw [hcomp]; infer_instance
  haveI : IsSeparated ((π ⁻¹ᵁ U).ι ≫ π) := inferInstance
  haveI : IsSeparated ((π ∣_ U) ≫ U.ι) := by rw [morphismRestrict_ι]; infer_instance
  haveI : IsSeparated (π ∣_ U) := IsSeparated.of_comp (π ∣_ U) U.ι
  haveI : UniversallyClosed j' := UniversallyClosed.of_comp_of_isSeparated j' (π ∣_ U)
  have hclosed : IsClosed (Set.range j'.base) := j'.isClosedMap.isClosed_range
  have hrange : Set.range j' = (π ⁻¹ᵁ U).ι ⁻¹' Set.range j := by
    ext w; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, (π ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hj'fac, hx]
  have hdense : Dense (Set.range j') := by
    rw [hrange]; exact hd.preimage (π ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap
  have huniv : Set.range j' = Set.univ := by
    rw [← hclosed.closure_eq]; exact hdense.closure_eq
  ext z; constructor
  · intro hz
    have hz' : z ∈ Set.range (π ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hz
    obtain ⟨w, rfl⟩ := hz'
    obtain ⟨x, rfl⟩ : w ∈ Set.range j' := huniv ▸ Set.mem_univ w
    exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, rfl⟩; exact hU ⟨x, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCells
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem preimage_iUnion_eq_range_cells : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (F Z : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)) (j : F ⟶ Z) (ν : Z ⟶ P), IsImmersion f → (∀ b w, IsOpenImmersion (i b w)) → (∀ b w, i b w ≫ f = h b w) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → IsOpenImmersion j → j ≫ ν = f → Dense (Set.range j) → TopologicalSpace.NoetherianSpace F → IsSeparated (ν ≫ p0) → (ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X) = Set.range j := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hC hP F Z f i j ν hf hi hif hcov hj hjν hd hF hsep
  have hcb : ∀ b w, i b w ≫ f ≫ p0 = cbase m (V b) := fun b w => by
    rw [← Category.assoc, hif, hP.base]
  have hjf : j ≫ ν ≫ p0 = f ≫ p0 := by rw [← Category.assoc, hjν]
  have hU : ((⨆ b, (V b).1 : X.Opens) : Set X) = ⋃ b, ((V b).1 : Set X) := by
    simp [TopologicalSpace.Opens.coe_iSup]
  rw [← hU]
  refine GlobalTheory.preimage_opens_eq_range_of_valuative F Z X j (ν ≫ p0) _ hj hd hsep hF ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hcov x
    rw [hU, hjf, ← Scheme.Hom.comp_apply, hcb b w]
    refine Set.mem_iUnion.2 ⟨b, ?_⟩
    have hr := (V b).2.range_fromSpec
    unfold cbase
    rw [Scheme.Hom.comp_apply]
    exact hr ▸ Set.mem_range_self _
  · intro A k _ _ _ _ _ _ a x hx hax
    rw [hU] at hx
    haveI : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    haveI : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨y⟩ := ‹Nonempty (Sp k)›
    obtain ⟨b', w', hy⟩ := hcov (a y)
    have hra : Set.range a ⊆ Set.range (i b' w') := by
      rintro _ ⟨z, rfl⟩
      rwa [Subsingleton.elim z y]
    haveI := hi b' w'
    let a' := IsOpenImmersion.lift (i b' w') a hra
    have ha' : a' ≫ i b' w' = a := IsOpenImmersion.lift_fac _ _ _
    have h1 : a' ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x := by
      rw [← hcb b' w', ← Category.assoc, ha', ← hax, hjf]
    obtain ⟨b, w, l, hl, hl2⟩ := GlobalTheory.T.flagCell_valuativeExistence_over_union_of_opens O K β X s T m M B V α c D P p0 p h hC hP A k b' w' a' x hx h1
    haveI : Mono f := inferInstance
    refine ⟨l ≫ i b w, ?_, ?_⟩
    · rw [← cancel_mono f, Category.assoc, Category.assoc, hif, hl2, ← hif b' w', ← Category.assoc, ha']
    · rw [hjf, Category.assoc, hcb b w, hl]

end GlobalTheory.FlagEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCellsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_iUnion_opens_eq_range_flagCells : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (F Z : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)) (j : F ⟶ Z) (ν : Z ⟶ P), IsImmersion f → (∀ b w, IsOpenImmersion (i b w)) → (∀ b w, i b w ≫ f = h b w) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → IsOpenImmersion j → j ≫ ν = f → Dense (Set.range j) → TopologicalSpace.NoetherianSpace F → IsSeparated (ν ≫ p0) → (ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X) = Set.range j := by
  first | exact @GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells | exact GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells | (intros; apply GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeAtOfToricChart
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ChartCone

theorem isCN_chartRing (k : Type) [Field k] (m e : ℕ) [CharZero (ChartRing k m e)] : IsCN (ChartRing k m e) := by
  have : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
  refine ⟨inferInstance, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).2, ?_, inferInstance⟩
  have : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  exact GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _

end GlobalTheory.ChartCone
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionState
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionState
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem st_of_fits : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), ∀ o : P.q.Over, o.Fits → o.G = P.Z₀.G → o.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → BkLaw (w.D o.Z) → ∃ x : St P, x.o = o := by
  intro hW hD hH hC K B f T w P o hfit hG heta hbk
  obtain ⟨m, hcopy, hcoh⟩ := GlobalTheory.T.exists_movedRowLiftData_to_fittingStages B f T w P.Z₀ P.hX P.Wt P.z P.q o P.intersectionNumber_baseChange P.exAt P.inGeo P.grp hfit
  obtain ⟨s, r, hpin⟩ := GlobalTheory.T.exists_reading_of_rowLiftFamily_movedData B f T w P.Z₀ P.hX P.Wt P.z P.q o
    (GlobalTheory.LinksInputs.inputs_of_hypotheses hW hD hH hC (w.D o.Z)) hfit m
  exact ⟨⟨o, hfit, hG, heta, hbk, m, hcopy, hcoh, s, r, hpin⟩, rfl⟩

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionStateStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fittingLaterStages_row_is_constructionState : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), ∀ o : P.q.Over, o.Fits → o.G = P.Z₀.G → o.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → BkLaw (w.D o.Z) → ∃ x : St P, x.o = o := by
  exact @GlobalTheory.Mem.R3.Rw.st_of_fits
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier
  GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.HodgeOnDomain

attribute [local instance] Over.cartesianMonoidalCategory

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem eigGram_transport {σ : c.F →+* ℂ} (M : EigMet Z σ) {p q : CxPts (genStr Z) σ} (e : p = q)
    (F : EigFrame Z σ (p.1 ≫ genι Z)) (G : EigFrame Z σ (q.1 ≫ genι Z)) (τ : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (h : ∀ i, IsCombAtG Z.t (q.1 ≫ genι Z) (G.v τ) (fun a => T a i) (F.v τ i)) :
    M.gram p F τ = Tᴴ * M.gram q G τ * T := by
  subst e
  rw [M.change p G F τ, EigFrame.co_eq h]

theorem eigGram_of_comb {σ : c.F →+* ℂ} (M : EigMet Z σ) (y y' : FrPt Xo c (CAt σ)) (h : y.x = y'.x)
    (τ : E →+* ℂ) (K : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hK : ∀ i, Formalism.L2.Pj.IsCombAt y'.x (y'.u τ) (fun b => (K b i : CAt σ)) (y.u τ i)) :
    M.gram (cxPt Z y) (cxFrame Z y) τ = Kᴴ * M.gram (cxPt Z y') (cxFrame Z y') τ * K := by
  refine eigGram_transport M (cxPt_congr h) _ _ τ K fun i => ?_
  have hv : IsTanAtG Xo.univ.t y'.x (y.u τ i) := h ▸ y.tan τ i
  have hx' : GlobalTheory.AllWt.ptF (S := CAt σ) y' ≫ Z.jQ ≫ genι Z = (cxPt Z y').1 ≫ genι Z := (Category.assoc _ _ _).symm
  have hx : GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ ≫ genι Z = (cxPt Z y).1 ≫ genι Z := (Category.assoc _ _ _).symm
  have e1 : (cxFrame Z y).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := ofFrPt_v_eq h hx hx' τ i hv
  rw [e1]
  exact isComb_ofFrPt (S := CAt σ) y' hx' τ (fun b => (K b i : CAt σ)) hv (hK i)

end Main

theorem eq_of_conj_eq_one {n : Type} [Fintype n] [DecidableEq n] {W P : Matrix n n ℂ} (hW : IsUnit W.det)
    (h : Wᴴ * P * W = 1) : P = (W⁻¹)ᴴ * W⁻¹ := by
  have hW' : IsUnit Wᴴ.det := by rw [det_conjTranspose]; exact hW.star
  calc P = (Wᴴ)⁻¹ * (Wᴴ * P * W) * W⁻¹ := by
        rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hW, ← Matrix.mul_assoc, nonsing_inv_mul _ hW',
          Matrix.one_mul]
    _ = (W⁻¹)ᴴ * W⁻¹ := by rw [h, Matrix.mul_one, conjTranspose_nonsing_inv]

theorem smul_submatrix_sq {m n : Type} (a : ℂ) (M : Matrix n n ℂ) (e : m → n) :
    (a • M).submatrix e e = a • M.submatrix e e := rfl

end GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeOnDomain

end GlobalTheory.HodgeOnDomain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalTrivialOfRelativeAmple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.KTrivSpread

namespace GlobalTheory.KTrivGenericPt

theorem spMap_eq_lift_comp_jK {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) :
    spMap ψ = spMap (IsFractionRing.lift (K := FractionRing R) hψ) ≫ Out.jK R := by
  rw [Out.jK, spMap, spMap, ← Spec.map_comp]
  congr 1
  ext r
  simp

theorem trivAlong_field {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {R : Type} [CommRing R] [IsDomain R]
    {g : Sp R ⟶ S} (h : TrivAlong A L (Out.jK R ≫ g)) {F : Type} [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) : TrivAlong A L (spMap ψ ≫ g) := by
  rw [spMap_eq_lift_comp_jK ψ hψ, Category.assoc]
  exact h.comp _

end GlobalTheory.KTrivGenericPt


open GlobalTheory.KTrivGenericPt in
theorem GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), IsProper t.G.hom → RelAmple t.G t.PP.L → GlobalTheory.LN.PolAt t (jK R) → KTriv t.G t.PP.L := by
  intro E _ _ _ H R _ _ _ _ t hP ha hpol
  haveI : IsProper t.G.hom := hP
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hgen : TrivAlong t.G t.PP.L (Out.jK R) :=
    trivAlong_of_kTriv (isGrpPullback_pullback t.G (Out.jK R)) t.PP.isLB hpol.2.2
  have hgen' : TrivAlong t.G t.PP.L (Out.jK R ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; exact hgen
  refine kTriv_of_primes hG R t.G hA t.PP.L t.PP.isLB ha fun p => ?_
  let O := Localization.AtPrime p.asIdeal
  have hO : Function.Injective (algebraMap R O) := IsLocalization.injective O p.asIdeal.primeCompl_le_nonZeroDivisors
  have hp : PrimeSpectrum.comap (algebraMap R O) (IsLocalRing.closedPoint O) = p :=
    PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
  by_cases hf : IsField O
  · refine ⟨O, inferInstance, algebraMap R O, ⟨_, hp⟩, ?_⟩
    letI := hf.toField
    have := trivAlong_field hgen' (algebraMap R O) hO
    rwa [Category.comp_id] at this
  · obtain ⟨V, _, _, _, ρ, h1, h2⟩ := exists_dvr O hf
    have hρ : Function.Injective (ρ.comp (algebraMap R O)) := h1.comp hO
    have : CharZero V := charZero_of_injective_ringHom hρ
    refine ⟨V, inferInstance, ρ.comp (algebraMap R O), ⟨IsLocalRing.closedPoint V, ?_⟩, ?_⟩
    · rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint, hp]
    · have key := trivAlong_dvr hG (𝟙 (Sp R)) hA t.PP t.cub ha V (spMap (ρ.comp (algebraMap R O))) ?_
      · rwa [Category.comp_id] at key
      · let F := AlgebraicClosure (FractionRing V)
        have H' := trivAlong_field hgen'
          ((algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O))))
          ((algebraMap (FractionRing V) F).injective.comp ((IsFractionRing.injective V (FractionRing V)).comp hρ))
        have e : (Out.TF (R := V) F).hom ≫ spMap (ρ.comp (algebraMap R O)) = spMap ((algebraMap (FractionRing V) F).comp
            ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O)))) :=
          (congrArg (· ≫ _) (Spec.map_comp _ _).symm).trans (Spec.map_comp _ _).symm
        rw [← e, Category.assoc] at H'
        exact H'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationDataNormalRing
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.UnifLamFibre

open GlobalTheory.CechPic

theorem isSquare_unique {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b :=
  (IsPullback.of_hasPullback G.hom G.hom).hom_ext (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm)


end GlobalTheory.UnifLamFibre
end
end
