module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicEigenvectorCoordinatesHolomorphicUnifor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHoloCoordFrameAt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineLieEigenFrameNearComplexPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineOpenSpreadStalkLieEigenspaceFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineOpenSpreadStalkLieEigenspaceFrame
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open CategoryTheory.Limits

namespace GlobalTheory.ShFam.StalkSpread

open GlobalTheory.LieLocFrame (res res_sum res_res)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_isMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (X : Var F) (j : X.X ⟶ gen Z) (z : X.X) (φz : c.F →+* X.X.presheaf.stalk z) (fz : EigFrame Z φz (stalkPt X z ≫ j ≫ genι Z)) (W₀ : X.X.Opens), z ∈ W₀ → stalkPt X z ≫ j ≫ genStr Z = spMap φz → ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)) (hz : z ∈ W), W ≤ W₀ ∧ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genStr Z = spMap φ ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (X.X.presheaf.germ W z hz).hom fz := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ X j z φz fz W₀ hz₀ hstr
  obtain ⟨U₀, hU₀, φ₀, f₀, hy₀, hs₀, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (j z)
  let gm₀ : Γ(gen Z, U₀) →+* X.X.presheaf.stalk z :=
    (X.X.presheaf.germ (j ⁻¹ᵁ U₀) z hy₀).hom.comp (j.app U₀).hom
  have hgm : ∀ (U : X.X.Opens) (hy : z ∈ U) (h : U ≤ j ⁻¹ᵁ U₀),
      (X.X.presheaf.germ U z hy).hom.comp (j.appLE U₀ U h).hom = gm₀ := fun U hy h =>
    RingHom.ext fun a => X.X.presheaf.germ_res_apply (homOfLE h) z hy _
  have hρ : ∀ (U : X.X.Opens) (hU : IsAffineOpen U) (h : U ≤ j ⁻¹ᵁ U₀),
      spMap (j.appLE U₀ U h).hom ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) =
        (show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j := fun U hU h =>
    IsAffineOpen.SpecMap_appLE_fromSpec j hU₀ hU h
  have hx₀ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) = stalkPt X z ≫ j := by
    obtain ⟨U, hU, hy, h⟩ := exists_isAffineOpen_mem_and_subset (X := X.X) (U := j ⁻¹ᵁ U₀) (x := z) hy₀
    rw [← hgm U hy h, ← spMap_comp_spMap, Category.assoc, hρ U hU h, ← Category.assoc, Spread.spMap_germ]
    rfl
  have hs₀' : (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genStr Z = spMap φ₀ := hs₀
  have hφ₀ : gm₀.comp φ₀ = φz := by
    have h1 : spMap (gm₀.comp φ₀) = spMap φz := by
      rw [← spMap_comp_spMap, ← hs₀', ← Category.assoc, hx₀, Category.assoc, hstr]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hx₁ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      stalkPt X z ≫ j ≫ genι Z := by rw [← Category.assoc, hx₀, Category.assoc]
  obtain ⟨g, hg⟩ := Spread.exists_bc f₀ gm₀ hφ₀ hx₁
  choose A B hAB hA using Spread.exists_coord g fz
  obtain ⟨U, hU, hy, s, hle, hs⟩ := Spread.exists_affine_germs z (W := W₀ ⊓ j ⁻¹ᵁ U₀) ⟨hz₀, hy₀⟩
    (fun p : Bool × (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)) =>
      (cond p.1 (A p.2.1) (B p.2.1)) p.2.2.1 p.2.2.2)
  have h₀ : U ≤ j ⁻¹ᵁ U₀ := fun w hw => (hle hw).2
  let gm : Γ(X.X, U) →+* X.X.presheaf.stalk z := (X.X.presheaf.germ U z hy).hom
  let ρ : Γ(gen Z, U₀) →+* Γ(X.X, U) := (j.appLE U₀ U h₀).hom
  let A' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X.X, U) :=
    fun τ => Matrix.of fun i k => s (true, ⟨τ, i, k⟩)
  let B' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X.X, U) :=
    fun τ => Matrix.of fun i k => s (false, ⟨τ, i, k⟩)
  have hA' : ∀ τ i k, gm (A' τ i k) = A τ i k := fun τ i k => hs (true, ⟨τ, i, k⟩)
  have hB' : ∀ τ i k, gm (B' τ i k) = B τ i k := fun τ i k => hs (false, ⟨τ, i, k⟩)
  have hAB' : ∀ τ, B' τ * A' τ = 1 := fun τ => Matrix.ext fun i k => germ_injective_of_isIntegral X.X z hy (by
    show gm _ = gm _
    have := congrFun (congrFun (hAB τ) i) k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul, hA', hB', Matrix.one_apply] at this ⊢
    rw [this]
    split_ifs <;> simp)
  have hx₂ : spMap ρ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      ((show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j) ≫ genι Z := by rw [← Category.assoc, hρ U hU h₀]
  have hx₃ : spMap gm ≫ ((show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j) ≫ genι Z =
      stalkPt X z ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, Spread.spMap_germ]
    rfl
  obtain ⟨g', hg'⟩ := Spread.exists_bc f₀ ρ rfl hx₂
  obtain ⟨fr, hfr⟩ := Spread.exists_change g' A' B' hAB'
  refine ⟨U, hU, ρ.comp φ₀, fr, hy, fun w hw => (hle hw).1, ?_, fun τ i => ?_⟩
  · rw [← hρ U hU h₀, Category.assoc, hs₀']
    exact spMap_comp_spMap φ₀ ρ
  · have hv : fz.vec τ i = res gm hx₃ (fr.vec τ i) := by
      rw [hfr, res_sum, hA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hA', hg, hg', res_res ρ hx₂ gm hx₃ (hgm U hy h₀) hx₁]
    exact congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) hv

end GlobalTheory.ShFam.StalkSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineOpenSpreadStalkLieEigenspaceFrameStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_spread_stalk_lieEigenspaceFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (X : Var F) (j : X.X ⟶ gen Z) (z : X.X) (φz : c.F →+* X.X.presheaf.stalk z) (fz : EigFrame Z φz (stalkPt X z ≫ j ≫ genι Z)) (W₀ : X.X.Opens), z ∈ W₀ → stalkPt X z ≫ j ≫ genStr Z = spMap φz → ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)) (hz : z ∈ W), W ≤ W₀ ∧ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genStr Z = spMap φ ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (X.X.presheaf.germ W z hz).hom fz := by
  first | exact @GlobalTheory.ShFam.StalkSpread.exists_affine_isMap | exact GlobalTheory.ShFam.StalkSpread.exists_affine_isMap | (intros; apply GlobalTheory.ShFam.StalkSpread.exists_affine_isMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineLieEigenFrameNearComplexPoint
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NearFrame

theorem dualMap_comp_near {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem exists_affine_frame_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), Tied e X j f₀ Eb A₀ → ∀ (y : CxPts X.str (σ.comp e.toRingHom)), ∀ A ∈ Eb.S (under y), ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)), y ∈ ptsIn X.str (σ.comp e.toRingHom) W ∧ ∀ y' (hy' : y' ∈ ptsIn X.str (σ.comp e.toRingHom) W), (evHom hy').comp φ = σ ∧ ∃ g : EigFrame Z σ ((cxOf e σ hj y').1 ≫ genι Z), FrameAt e f₀ A₀ A y' g ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (evHom hy') g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ X j f₀ Eb A₀ hj hT y A hA
  obtain ⟨φz, fz, hx0, hφ0, hv0⟩ := hT.2 (under y) A hA
  have inj := IsFractionRing.injective (X.X.presheaf.stalk (under y)) X.X.functionField
  have hgen : spMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) ≫ stalkPt X (under y) = genericPt X :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)
  have hstr : stalkPt X (under y) ≫ j ≫ genStr Z = spMap φz := by
    obtain ⟨p, hp⟩ := Spec.map_surjective (stalkPt X (under y) ≫ j ≫ genStr Z)
    have h1 : (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp p.hom =
        (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp φz := by
      refine EigLoc.spMap_inj ?_
      rw [← hφ0, ← TieBase.genericPt_str e X j hj, TieBase.spMap_trans, ← hgen]
      show _ ≫ Spec.map p = _
      rw [hp]
      simp only [Category.assoc]
    have h2 : p.hom = φz := RingHom.ext fun a => inj (RingHom.congr_fun h1 a)
    rw [← hp, ← h2]
    rfl
  obtain ⟨W, hW, φ, fW, hz, -, hWstr, hmap⟩ := GlobalTheory.T.exists_affineOpen_spread_stalk_lieEigenspaceFrame E H Dw l Xo c O β Z F X j (under y) φz fz ⊤ trivial hstr
  have hgerm : spMap (X.X.presheaf.germ W (under y) hz).hom ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) =
      stalkPt X (under y) := hW.fromSpecStalk_eq_fromSpecStalk hz
  have hφz : φz = (X.X.presheaf.germ W (under y) hz).hom.comp φ := by
    refine EigLoc.spMap_inj ?_
    rw [TieBase.spMap_trans, ← hstr, ← hWstr, ← hgerm]
    simp only [Category.assoc]
  refine ⟨W, hW, φ, fW, mem_ptsIn.2 hz, fun y' hy' => ?_⟩
  have hz' : under y' ∈ W := mem_ptsIn.1 hy'
  have hp' : spMap (evHom hy') ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = y'.1 :=
    Points.specMap_valMap_fromSpec hW y'.1 hy'
  have ha : (evHom hy').comp φ = σ := by
    refine EigLoc.spMap_inj ?_
    rw [TieBase.spMap_trans, ← hWstr, ← (cxOf e σ hj y').2]
    show _ = (y'.1 ≫ j) ≫ genStr Z
    rw [← hp']
    simp only [Category.assoc]
  refine ⟨ha, ?_⟩
  obtain ⟨g, hg⟩ := EigFrame.exists_isMap fW (evHom hy') (φ' := σ) (x' := (cxOf e σ hj y').1 ≫ genι Z) ha.symm (by
    show (y'.1 ≫ j) ≫ genι Z = _
    rw [← hp']
    simp only [Category.assoc])
  refine ⟨g, ?_, hg⟩
  let germ' := (X.X.presheaf.germ W (under y') hz').hom
  let χ : X.X.presheaf.stalk (under y') →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) y'.1).hom
  have hχ : χ.comp germ' = evHom hy' := by
    show _ = (Points.valMap y'.1 W hy').hom
    rw [← CommRingCat.hom_comp]
    congr 1
    rw [Scheme.germ_stalkClosedPointTo]
    rfl
  have hgerm' : spMap germ' ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = stalkPt X (under y') :=
    hW.fromSpecStalk_eq_fromSpecStalk hz'
  obtain ⟨fz', hfz'⟩ := EigFrame.exists_isMap fW germ' (φ' := germ'.comp φ)
    (x' := stalkPt X (under y') ≫ j ≫ genι Z) rfl (by rw [← hgerm']; simp only [Category.assoc])
  have hκ : (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField).comp germ' =
      (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp (X.X.presheaf.germ W (under y) hz).hom :=
    RingHom.ext fun a => (algebraMap_germ hz' a).trans (algebraMap_germ hz a).symm
  refine ⟨germ'.comp φ, fz', χ, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of ℂ) y'.1).symm, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hx0, ← hgerm, ← hgerm']
    simp only [← Category.assoc]
    rw [← TieBase.spMap_trans, ← TieBase.spMap_trans, hκ]
  · rw [hφ0, hφz, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hκ]
  · intro τ i
    have e : (fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField)) ≫ fz'.v τ k) =
        fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField)) ≫ fz.v τ k := by
      funext k
      rw [hfz' τ k, hmap τ k, ← Category.assoc, ← Category.assoc, ← TieBase.spMap_trans, ← TieBase.spMap_trans,
        ← dualMap_comp_near, ← dualMap_comp_near, hκ]
    rw [e]
    exact hv0 τ i
  · intro τ i
    rw [hg τ i, hfz' τ i, ← Category.assoc, ← TieBase.spMap_trans, ← dualMap_comp_near, hχ]

end GlobalTheory.NearFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineLieEigenFrameNearComplexPointStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_lieEigenFrame_near_complexPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), Tied e X j f₀ Eb A₀ → ∀ (y : CxPts X.str (σ.comp e.toRingHom)), ∀ A ∈ Eb.S (under y), ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)), y ∈ ptsIn X.str (σ.comp e.toRingHom) W ∧ ∀ y' (hy' : y' ∈ ptsIn X.str (σ.comp e.toRingHom) W), (evHom hy').comp φ = σ ∧ ∃ g : EigFrame Z σ ((cxOf e σ hj y').1 ≫ genι Z), FrameAt e f₀ A₀ A y' g ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (evHom hy') g := by
  first | exact @GlobalTheory.NearFrame.exists_affine_frame_near | exact GlobalTheory.NearFrame.exists_affine_frame_near | (intros; apply GlobalTheory.NearFrame.exists_affine_frame_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointStalkFrameVectorsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointStalkFrameVectorsEq
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase


attribute [local instance] Over.cartesianMonoidalCategory in
theorem isCombAtG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    {t : SAB H X0} {R : Type} [CommRing R] {x0 : Sp R ⟶ X0} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    {cf : Fin m → R} {w w' : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x0 v cf w)
    (h' : IsCombAtG t x0 v cf w') : w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have : u = u' := funext fun k => Over.OverMorphism.ext ((hu k).trans (hu' k).symm)
  rw [this]

theorem frameAt_v_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) (x x' : Sp ℂ ⟶ Z.X) (g : EigFrame Z σ x) (g' : EigFrame Z σ x'), FrameAt e f₀ A₀ A y g → FrameAt e f₀ A₀ A y g' → ∀ τ i, g.v τ i = g'.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ X j f₀ A₀ A y x x' g g' h h' τ i
  obtain ⟨φ, fz, ψ, hy, hc, hg⟩ := h
  obtain ⟨φ', fz', ψ', hy', hc', hg'⟩ := h'
  have hψ : ψ = ψ' := EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under y))).1 (hy.symm.trans hy'))
  subst hψ
  have hι := IsFractionRing.injective (X.X.presheaf.stalk (under y)) X.X.functionField
  obtain rfl : φ = φ' := RingHom.ext fun a => hι ((RingHom.congr_fun hc.2.1 a).symm.trans (RingHom.congr_fun hc'.2.1 a))
  obtain ⟨fK, hK⟩ := fz.exists_isMap _ hc.2.1 hc.1
  obtain ⟨fK', hK'⟩ := fz'.exists_isMap _ hc.2.1 hc.1
  have e1 : fK.co f₀ τ = fK'.co f₀ τ := by
    rw [EigFrame.co_eq (T := Matrix.of fun a k => (A₀ * A⁻¹) τ k a) fun k => by
        rw [funext (hK τ)]; exact hc.2.2 τ k,
      EigFrame.co_eq (T := Matrix.of fun a k => (A₀ * A⁻¹) τ k a) fun k => by
        rw [funext (hK' τ)]; exact hc'.2.2 τ k]
  have e2 : fK.co fK' τ = 1 := by
    rw [← fK.co_mul f₀ fK' τ, e1, fK'.co_mul, fK'.co_self]
  have e3 : fz.co fz' τ = 1 := by
    have e := (hK.co τ hK' hc.1).symm.trans e2
    ext a b
    have e' := congrFun (congrFun e a) b
    rw [Matrix.map_apply] at e'
    apply hι
    rw [e', Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e4 := fz.co_spec fz' τ i
  rw [e3] at e4
  have e5 : fz'.v τ i = fz.v τ i := isCombAtG_eq e4 (by
    convert isCombAtG_single Z.t _ (fz.tan τ) i using 2
    simp only [Matrix.one_apply, Pi.single_apply])
  rw [hg τ i, hg' τ i, e5]

end GlobalTheory.LieBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointStalkFrameVectorsEqStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoint_stalkFrame_vectors_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) (x x' : Sp ℂ ⟶ Z.X) (g : EigFrame Z σ x) (g' : EigFrame Z σ x'), FrameAt e f₀ A₀ A y g → FrameAt e f₀ A₀ A y g' → ∀ τ i, g.v τ i = g'.v τ i := by
  first | exact @GlobalTheory.LieBase.frameAt_v_eq | exact GlobalTheory.LieBase.frameAt_v_eq | (intros; apply GlobalTheory.LieBase.frameAt_v_eq <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem exists_holo_coord_frameAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∀ (kU : U.Comp) (G : V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X kU).Ψ (Dw.p + Dw.q)), (∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, cxPt T.Z (U.un kU ⟨G u, h⟩) = cxOf e σ hj (c'.e.symm u)) → (∀ τ' a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → ∃ M : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => M u a b) u) ∧ IsUnit (M (c'.e y)).det ∧ ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm u)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm u) g) ∧ ∀ (x : Sp ℂ ⟶ T.Z.X) (g : EigFrame T.Z σ x), FrameAt e f₀ A₀ A (c'.e.symm u) g → ∀ i, IsCombAtG T.Z.t ((cxPt T.Z (U.un kU ⟨G u, h⟩)).1 ≫ genι T.Z) ((cxFrame T.Z (U.un kU ⟨G u, h⟩)).v τ.1) (fun b => M u b i) (g.v τ.1 i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hLie y _ c' hyc A hA τ kU G hF hG
  obtain ⟨-, -, hTd⟩ := hLie
  obtain ⟨W, hW, φ, fW, hyW, hnear⟩ := GlobalTheory.T.exists_affine_lieEigenFrame_near_complexPoint E H Dw l Xo c O β T.Z F e σ X j f₀ Eb A₀ hj hTd y A hA
  classical
  let ev : V X.dim → (Γ(X.X, W) →+* ℂ) := fun u =>
    if h : c'.e.symm u ∈ ptsIn X.str (σ.comp e.toRingHom) W then evHom h else evHom hyW
  have hev : ∀ u (h : c'.e.symm u ∈ ptsIn X.str (σ.comp e.toRingHom) W), ev u = evHom h := fun u h => dif_pos h
  set S : Set (V X.dim) := c'.e.target ∩ c'.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W with hSdef
  have hSo : IsOpen S := c'.e.continuousOn_symm.isOpen_inter_preimage c'.e.open_target (isOpen_ptsIn _)
  have hu0 : c'.e y ∈ S := ⟨c'.e.map_source hyc, by show c'.e.symm (c'.e y) ∈ ptsIn X.str (σ.comp e.toRingHom) W; rw [c'.e.left_inv hyc]; exact hyW⟩
  have hSn : ∀ᶠ u in 𝓝 (c'.e y), u ∈ S := hSo.mem_nhds hu0
  have hevd : ∀ t, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ev u t) u := by
    intro t
    filter_upwards [hSn] with u hu
    refine ((c'.holo W t).differentiableAt (hSo.mem_nhds hu)).congr_of_eventuallyEq ?_
    filter_upwards [hSo.mem_nhds hu] with v hv
    simp only [Function.comp_apply, hev v hv.2, ev_eq hv.2]
  have hφ : ∀ᶠ u in 𝓝 (c'.e y), (ev u).comp φ = σ := by
    filter_upwards [hSn] with u hu
    rw [hev u hu.2]; exact (hnear _ hu.2).1
  have hpt : ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, (cxPt T.Z (U.un kU ⟨G u, h⟩)).1 ≫ genι T.Z =
      spMap (ev u) ≫ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι T.Z := by
    filter_upwards [hSn, hF] with u hu ⟨h, hc⟩
    refine ⟨h, ?_⟩
    rw [hc, hev u hu.2]
    have := GlobalTheory.Points.specMap_valMap_fromSpec hW (c'.e.symm u).1 hu.2
    show (c'.e.symm u).1 ≫ j ≫ genι T.Z = _
    rw [← this]
    simp only [Category.assoc]
    rfl
  obtain ⟨M, hMd, hMc⟩ := GlobalTheory.T.algebraic_eigenvector_coordinates_holomorphic_uniformisation E H Dw l Xo c O β T.Z σ U hσ hU X.dim (c'.e y) Γ(X.X, W) φ _ fW ev kU G τ.1 hevd hG hφ hpt
  refine ⟨M, hMd, ?_, ?_⟩
  · obtain ⟨h0, hc0⟩ := hMc.self_of_nhds
    obtain ⟨h0', hF0⟩ := hF.self_of_nhds
    obtain ⟨-, g0, -, hm0⟩ := hnear _ hu0.2
    have hx : (cxOf e σ hj (c'.e.symm (c'.e y))).1 ≫ genι T.Z = (cxPt T.Z (U.un kU ⟨G (c'.e y), h0⟩)).1 ≫ genι T.Z := by
      rw [hF0]
    have key : ∀ {x x' : Sp ℂ ⟶ T.Z.X} (hx : x = x') (g : EigFrame T.Z σ x) (G' : EigFrame T.Z σ x')
        (N : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ),
        (∀ i, IsCombAtG T.Z.t x' (G'.v τ.1) (fun b => N b i) (g.v τ.1 i)) → IsUnit N.det := by
      intro x x' hx g G' N h
      subst hx
      rw [← EigFrame.co_eq (f := G') (g := g) h]
      exact EigFrame.isUnit_det_co _ _ _
    refine key hx g0 (cxFrame T.Z (U.un kU ⟨G (c'.e y), h0⟩)) (M (c'.e y)) fun i => ?_
    rw [hm0 τ.1 i, ← hev _ hu0.2]
    exact hc0 i
  · filter_upwards [hMc, hSn] with u ⟨h, hc⟩ hu
    obtain ⟨-, g0, hg0, hm0⟩ := hnear _ hu.2
    refine ⟨h, ⟨g0, hg0⟩, fun x g hg i => ?_⟩
    rw [GlobalTheory.T.complexPoint_stalkFrame_vectors_eq E H Dw l Xo c O β T.Z F e σ X j f₀ A₀ A _ _ _ g g0 hg hg0 τ.1 i, hm0 τ.1 i, ← hev _ hu.2]
    exact hc i

end GlobalTheory.LieBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceHodgeGramLocalHolomorphicModel
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.LocalModel

theorem differentiableAt_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} {u : V} (hA : ∀ a b, DifferentiableAt ℂ (fun v => A v a b) u) :
    DifferentiableAt ℂ (fun v => (A v).det) u := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  have key : ∀ t : Finset (Fin d), DifferentiableAt ℂ (fun v => ∏ i ∈ t, A v (σ i) i) u := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).mul ih
  exact key _

theorem differentiableAt_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} {u : V} (hA : ∀ a b, DifferentiableAt ℂ (fun v => A v a b) u)
    (hd : (A u).det ≠ 0) (i k : Fin d) : DifferentiableAt ℂ (fun v => (A v)⁻¹ i k) u := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((differentiableAt_det hA).inv hd).mul (differentiableAt_det fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact hA _ _

theorem differentiableAt_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {a b d : ℕ}
    {A : V → Matrix (Fin a) (Fin b) ℂ} {B : V → Matrix (Fin b) (Fin d) ℂ} {u : V}
    (hA : ∀ i k, DifferentiableAt ℂ (fun v => A v i k) u) (hB : ∀ i k, DifferentiableAt ℂ (fun v => B v i k) u)
    (i k : Fin _) : DifferentiableAt ℂ (fun v => (A v * B v) i k) u := by
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun c _ => (hA i c).mul (hB c k)

theorem gram_cast {n m q q' : ℕ} (h : n = m) (h' : q' = q) (κ : ℂ) (Gm Mu : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin q) ℂ)
    (hG : Gm.submatrix (Fin.cast h.symm) (Fin.cast h.symm) = κ • (Cᴴ * (Formalism.DegreeFormula.hP z)⁻¹ * C)) :
    (Muᴴ * Gm * Mu)ᵀ = κ • ((C.submatrix (Fin.cast h) (Fin.cast h) * Mu)ᵀ *
      GlobalTheory.PointFormSign.domGram n q' (fun a b => z (Fin.cast h a) (Fin.cast h' b)) *
        (C.submatrix (Fin.cast h) (Fin.cast h) * Mu)ᴴᵀ) := by
  subst h h'
  have hG' : Gm = κ • (Cᴴ * (Formalism.DegreeFormula.hP z)⁻¹ * C) := by simpa using hG
  subst hG'
  simp only [GlobalTheory.PointFormSign.domGram, Formalism.DegreeFormula.hP, Fin.cast_eq_self, Matrix.submatrix_id_id, Matrix.of_apply]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
  rfl

theorem posDef_cast {n m q q' : ℕ} (h : n = m) (h' : q' = q) (z : Matrix (Fin m) (Fin q) ℂ)
    (hz : (1 - z * zᴴ).PosDef) :
    (1 - Matrix.of (fun a b => z (Fin.cast h a) (Fin.cast h' b)) *
      (Matrix.of (fun a b => z (Fin.cast h a) (Fin.cast h' b)))ᴴ).PosDef := by
  subst h h'
  simp only [Fin.cast_eq_self]
  exact hz

theorem lieGram_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ (κ : ℝ) (W : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ) (Z : V X.dim → (Fin (Dw.mult τ.1) → Fin (Dw.p + Dw.q - Dw.mult τ.1) → ℂ)), 0 < κ ∧ (∀ᶠ u in 𝓝 (c'.e y), lieGram e U hj f₀ A₀ A (c'.e.symm u) τ.1 = (κ : ℂ) • ((W u)ᵀ * domGram _ _ (Z u) * (W u)ᴴᵀ)) ∧ (∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ Z u) ∧ (∀ i j, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => W u i j) u) ∧ IsUnit (W (c'.e y)).det ∧ (1 - Matrix.of (Z (c'.e y)) * (Matrix.of (Z (c'.e y)))ᴴ).PosDef := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hLie y hy c' hyc A hA τ
  obtain ⟨kU, G, hG⟩ := GlobalTheory.LieBase.HoloFrame.exists_holo_frame_chart E H Dw l Xo c O β Y T F e σ U hσ hU X j hLie.1
    hj y hy c' hyc
  have hF : ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom,
      cxPt T.Z (U.un kU ⟨G u, h⟩) = cxOf e σ hj (c'.e.symm u) := hG.mono fun u ⟨h, h1, _⟩ => ⟨h, h1⟩
  have hGd : ∀ τ' a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u :=
    fun τ' a b => hG.mono fun u ⟨_, _, h2⟩ => h2 τ' a b
  obtain ⟨M, hMd, hMu, hMc⟩ := GlobalTheory.LieBase.exists_holo_coord_frameAt E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀
    Eb A₀ hj hLie y hy c' hyc A hA τ kU G hF hGd
  have hle : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X kU).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 kU).1]; omega
  have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.HodgeGenUnf.mult_psi τ
  have hq : Dw.p + Dw.q - Dw.mult τ.1 = Dw.p + Dw.q - Dw.p := by rw [hm]
  set τ' := GlobalTheory.HodgeGenUnf.letter hσ hU kU τ with hτ'

  have hco : ∀ u, (∀ τ'' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ'' a b) u) →
      ∀ a b, DifferentiableAt ℂ (fun v => GlobalTheory.TrueCx.frameCo (U.X kU) hle (G v) τ' a b) u := by
    intro u hd a b
    simp only [GlobalTheory.TrueCx.frameCo, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun c _ => (hd _ _ _).const_mul _
  have hmo : ∀ u, (∀ τ'' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ'' a b) u) →
      G u ∈ (U.X kU).dom → ∀ a b,
      DifferentiableAt ℂ (fun v => Formalism.MJ.moeb (GlobalTheory.TrueCx.frameCo (U.X kU) hle (G v) τ') 0 a b) u := by
    intro u hd hdom a b
    simp only [GlobalTheory.TrueCx.moeb_zero]
    refine differentiableAt_mul (fun i k => hco u hd _ _) (differentiableAt_inv (fun i k => hco u hd _ _) ?_) a b
    exact (GlobalTheory.TrueCx.frameCo_isUnit₂₂ (U.X kU) hle hp hdom τ').ne_zero
  refine ⟨2 * Real.pi,
    fun u => (GlobalTheory.ShFam.coW (U.X kU) hle (G u) τ').submatrix (Fin.cast hm) (Fin.cast hm) * M u,
    fun u a b => Formalism.MJ.moeb (GlobalTheory.TrueCx.frameCo (U.X kU) hle (G u) τ') 0 (Fin.cast hm a) (Fin.cast hq b),
    Real.two_pi_pos, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hMc, hF] with u hu1 hu2
    obtain ⟨h, ⟨g, hg⟩, hc⟩ := hu1
    obtain ⟨h', hx⟩ := hu2
    have hex : ∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm u)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm u) g :=
      ⟨g, hg⟩
    rw [lieGram, dite_eq_left hex]
    show ((hodgeMet T.Z U).gram _ hex.choose τ.1)ᵀ = _
    rw [GlobalTheory.HodgeOnDomain.eigGram_transport (hodgeMet T.Z U) hx.symm hex.choose (cxFrame T.Z (U.un kU ⟨G u, h⟩)) τ.1
      (M u) (hc _ _ hex.choose_spec)]
    exact gram_cast hm hq _ _ _ _ _ (GlobalTheory.HodgeGenUnf.hodgeMet_gram_frame T.Z hσ hU kU ⟨G u, h⟩ τ τ' rfl hle)
  · filter_upwards [hG] with u hu
    obtain ⟨h, -, hd⟩ := hu
    exact differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => hmo u hd h _ _
  · intro a b
    filter_upwards [hG, Filter.eventually_all.2 fun c => Filter.eventually_all.2 fun d => hMd c d] with u hu hM
    obtain ⟨h, -, hd⟩ := hu
    refine differentiableAt_mul (fun i k => ?_) (fun i k => hM i k) a b
    simp only [Matrix.submatrix_apply, GlobalTheory.ShFam.coW, Matrix.sub_apply]
    exact (hco u hd _ _).sub (differentiableAt_mul (fun i k => hmo u hd h _ _) (fun i k => hco u hd _ _) _ _)
  · obtain ⟨h, -, -⟩ := hG.self_of_nhds
    rw [Matrix.det_mul]
    refine IsUnit.mul ?_ hMu
    have e1 : ((GlobalTheory.ShFam.coW (U.X kU) hle (G (c'.e y)) τ').submatrix (Fin.cast hm) (Fin.cast hm)).det =
        (GlobalTheory.ShFam.coW (U.X kU) hle (G (c'.e y)) τ').det := Matrix.det_submatrix_equiv_self (finCongr hm) _
    rw [e1]
    exact GlobalTheory.ShFam.isUnit_coW (U.X kU) hle hp h τ'
  · obtain ⟨h, -, -⟩ := hG.self_of_nhds
    have hz := GlobalTheory.TrueCx.domPt_mem (U.X kU) hle id hp h τ'
    exact posDef_cast hm hq _ (GlobalTheory.HodgeDomain.hP_posDef hz)

end GlobalTheory.LieBase.LocalModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceHodgeGramLocalHolomorphicModelStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieEigenspaceHodgeGram_local_holomorphic_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ (κ : ℝ) (W : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ) (Z : V X.dim → (Fin (Dw.mult τ.1) → Fin (Dw.p + Dw.q - Dw.mult τ.1) → ℂ)), 0 < κ ∧ (∀ᶠ u in 𝓝 (c'.e y), lieGram e U hj f₀ A₀ A (c'.e.symm u) τ.1 = (κ : ℂ) • ((W u)ᵀ * domGram _ _ (Z u) * (W u)ᴴᵀ)) ∧ (∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ Z u) ∧ (∀ i j, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => W u i j) u) ∧ IsUnit (W (c'.e y)).det ∧ (1 - Matrix.of (Z (c'.e y)) * (Matrix.of (Z (c'.e y)))ᴴ).PosDef := by
  first | exact @GlobalTheory.LieBase.LocalModel.lieGram_local_model | exact GlobalTheory.LieBase.LocalModel.lieGram_local_model | (intros; apply GlobalTheory.LieBase.LocalModel.lieGram_local_model <;> assumption)
end
