module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRigidityTangentVectorConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRigiditySndEqZeroCanonicalChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GrpPullAb

theorem isAbelianScheme_of_grpPullback :
    ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
      (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsAbelianScheme G → IsAbelianScheme G' :=
  fun _ h hG => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG h

end GlobalTheory.GrpPullAb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_of_grpPullback' : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsAbelianScheme G → IsAbelianScheme G' := by
  first | exact @GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback | exact GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback | (intros; apply GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseIdentityAlongMorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseIdentityAlongMorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UChart.FromBaseAlong

theorem gm_comp_map {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U a) = gm (f ≫ g) z U a := by
  apply Units.ext
  show (f.stalkMap z).hom (gm g (f z) U a).val = _
  rw [← gs_unit (f ≫ g) z U h, ← gs_unit g (f z) U h, ← gs_pull f g z U h, gs_eq f z (g ⁻¹ᵁ U) h, gs_eq g (f z) U h]
  exact Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h _

theorem val_comp_map {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (g : Y' ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ g) z J := by
  rw [val_of t (r ≫ g) z J (fun k => J (r ≫ g ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_comp_map r g z _ (Set.mem_iInter.2 fun k => hJ (r ≫ g ≫ φ k)) _

theorem fromBase_along : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])) (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧ (∀ a, cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (a b : Q.X) (zz : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Z ⟶ B₀.left) → M₀.ι), Good Q.P.L zz J → Good M₀ zz J₀ → val (τ₀ a b) r zz J = gm (r ≫ cpt Q (a + b)) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q (a + b) ≫ β), J (r ≫ cpt Q (a + b)))) * (gm (r ≫ cpt Q a) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q a ≫ β), J (r ≫ cpt Q a))))⁻¹ * (gm (r ≫ cpt Q b) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q b ≫ β), J (r ≫ cpt Q b))))⁻¹ * gm (r ≫ cpt Q 0) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q 0 ≫ β), J (r ≫ cpt Q 0))) * val (τ₁ a b) (r ≫ spMap ιb) zz J₀ := by
  intro R _ _ Q τ₀ W₀ _ ιb ⟨B₀, i, M₀, c₀, τ₁, β, w, h₁, h₂, h₃, h₄, h₅, h₆, h⟩
  refine ⟨B₀, i, M₀, c₀, τ₁, β, w, h₁, h₂, h₃, h₄, h₅, h₆, fun Z r a b zz J J₀ hJ hJ₀ => ?_⟩
  have e := congrArg (Units.map (r.stalkMap zz).hom.toMonoidHom)
    (h a b (r zz) (fun ψ => J (r ≫ ψ)) (fun ψ => J₀ (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ)) (fun ψ => hJ₀ (r ≫ ψ)))
  have g : ∀ x : Q.X, Units.map (r.stalkMap zz).hom.toMonoidHom
      (gm (cpt Q x) (r zz) _ (w.s (fun _ => J₀ (r ≫ cpt Q x ≫ β), J (r ≫ cpt Q x)))) =
      gm (r ≫ cpt Q x) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q x ≫ β), J (r ≫ cpt Q x))) := fun x =>
    gm_comp_map r (cpt Q x) zz _
      (show cpt Q x (r zz) ∈ (M₀.pull β).U (fun _ => J₀ (r ≫ cpt Q x ≫ β)) ⊓ Q.P.L.U (J (r ≫ cpt Q x)) from
        ⟨Set.mem_iInter.2 fun _ => hJ₀ (r ≫ cpt Q x ≫ β), hJ (r ≫ cpt Q x)⟩) _
  have v₀ := val_comp_map (τ₀ a b) r (𝟙 _) zz hJ
  have v₁ := val_comp_map (τ₁ a b) r (spMap ιb) zz hJ₀
  rw [Category.comp_id] at v₀
  rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv] at e
  exact v₀.symm.trans (e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (g (a + b)) (congrArg (·⁻¹) (g a))) (congrArg (·⁻¹) (g b))) (g 0)) v₁))

end GlobalTheory.UChart.FromBaseAlong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseIdentityAlongMorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromBase_identity_along_morphism : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])) (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧ (∀ a, cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (a b : Q.X) (zz : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Z ⟶ B₀.left) → M₀.ι), Good Q.P.L zz J → Good M₀ zz J₀ → val (τ₀ a b) r zz J = gm (r ≫ cpt Q (a + b)) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q (a + b) ≫ β), J (r ≫ cpt Q (a + b)))) * (gm (r ≫ cpt Q a) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q a ≫ β), J (r ≫ cpt Q a))))⁻¹ * (gm (r ≫ cpt Q b) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q b ≫ β), J (r ≫ cpt Q b))))⁻¹ * gm (r ≫ cpt Q 0) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q 0 ≫ β), J (r ≫ cpt Q 0))) * val (τ₁ a b) (r ≫ spMap ιb) zz J₀ := by
  first | exact @GlobalTheory.UChart.FromBaseAlong.fromBase_along | exact GlobalTheory.UChart.FromBaseAlong.fromBase_along | (intros; apply GlobalTheory.UChart.FromBaseAlong.fromBase_along <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantUnitPulledBackBundleAutomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantUnitPulledBackBundleAutomorphism
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.PullAutConst

theorem gm_pullChart {X Z T : Scheme.{0}} (L : LB X) (F : Z ⟶ X) (f : T ⟶ Z) (y : T) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y _ ((L.pull F).g (fun _ => j) (fun _ => j')) = gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

theorem exists_glued {X Y B : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β))
    (π₁ π₂ : B ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)) (hL : L.IsLB) (hM : M₀.IsLB)
    (hF : PGen wF) (hw : PGen w) (hβ : π₁ ≫ β = π₂ ≫ β) :
    ∃ s : Γ(B, ⊤)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (j₀ : M₀.ι) (j₁ j₂ : L.ι),
      β (π₁ (f z)) ∈ M₀.U j₀ → π₁ (f z) ∈ L.U j₁ → π₂ (f z) ∈ L.U j₂ →
      gm f z ⊤ s = gw wF (f ≫ π₂) z j₀ j₂ * gw w f z j₂ (fun _ => j₁) * (gw wF (f ≫ π₁) z j₀ j₁)⁻¹ := by
  have hpt : ∀ x, β (π₁ x) = β (π₂ x) := fun x => congrArg (fun g : B ⟶ Y => g x) hβ
  obtain ⟨W, hW⟩ : ∃ W : M₀.ι × L.ι × L.ι → B.Opens, ∀ t x,
      x ∈ W t ↔ β (π₁ x) ∈ M₀.U t.1 ∧ π₁ x ∈ L.U t.2.1 ∧ π₂ x ∈ L.U t.2.2 :=
    ⟨fun t => π₁ ⁻¹ᵁ (β ⁻¹ᵁ M₀.U t.1) ⊓ (π₁ ⁻¹ᵁ L.U t.2.1 ⊓ π₂ ⁻¹ᵁ L.U t.2.2), fun _ _ => Iff.rfl⟩
  have l₂ : ∀ t, W t ≤ π₂ ⁻¹ᵁ ((M₀.pull β).U (fun _ => t.1) ⊓ L.U t.2.2) := fun t x hx =>
    ⟨mem_pull.2 (show β (π₂ x) ∈ _ by rw [← hpt]; exact ((hW t x).1 hx).1), ((hW t x).1 hx).2.2⟩
  have lw : ∀ t, W t ≤ (L.pull π₂).U (fun _ => t.2.2) ⊓ (L.pull π₁).U (fun _ => t.2.1) := fun t x hx =>
    ⟨mem_pull.2 ((hW t x).1 hx).2.2, mem_pull.2 ((hW t x).1 hx).2.1⟩
  have l₁ : ∀ t, W t ≤ π₁ ⁻¹ᵁ ((M₀.pull β).U (fun _ => t.1) ⊓ L.U t.2.1) := fun t x hx =>
    ⟨mem_pull.2 ((hW t x).1 hx).1, ((hW t x).1 hx).2.1⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ t, Γ(B, W t)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (t : M₀.ι × L.ι × L.ι), f z ∈ W t →
      gm f z (W t) (u t) =
        gw wF (f ≫ π₂) z t.1 t.2.2 * gw w f z t.2.2 (fun _ => t.2.1) * (gw wF (f ≫ π₁) z t.1 t.2.1)⁻¹ :=
    ⟨fun t => res (l₂ t) (pullU π₂ _ (wF.s (fun _ => t.1, t.2.2))) * res (lw t) (w.s (fun _ => t.2.2, fun _ => t.2.1)) *
        (res (l₁ t) (pullU π₁ _ (wF.s (fun _ => t.1, t.2.1))))⁻¹, fun Z f z t hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res f z (l₂ t) hz _).trans (gm_pull f π₂ z _ (l₂ t hz) _)) (gm_res f z (lw t) hz _)))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₁ t) hz _).trans (gm_pull f π₁ z _ (l₁ t hz) _)))))⟩
  have indep : ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (t t' : M₀.ι × L.ι × L.ι), f z ∈ W t → f z ∈ W t' →
      gw wF (f ≫ π₂) z t.1 t.2.2 * gw w f z t.2.2 (fun _ => t.2.1) * (gw wF (f ≫ π₁) z t.1 t.2.1)⁻¹ =
      gw wF (f ≫ π₂) z t'.1 t'.2.2 * gw w f z t'.2.2 (fun _ => t'.2.1) * (gw wF (f ≫ π₁) z t'.1 t'.2.1)⁻¹ := by
    rintro Z f z ⟨a, b, c⟩ ⟨a', b', c'⟩ h h'
    obtain ⟨ha, hb, hc⟩ := (hW _ _).1 h
    obtain ⟨ha', hb', hc'⟩ := (hW _ _).1 h'
    have e₂ := hF Z (f ≫ π₂) z a a' c c' (show β (π₂ (f z)) ∈ _ by rw [← hpt]; exact ha)
      (show β (π₂ (f z)) ∈ _ by rw [← hpt]; exact ha') hc hc'
    have e₁ := hF Z (f ≫ π₁) z a a' b b' ha ha' hb hb'
    have ew := hw Z f z c c' (fun _ => b) (fun _ => b') hc hc' (mem_pull.2 hb) (mem_pull.2 hb')
    rw [gm_pullChart L π₁ f z b b' hb hb'] at ew
    have hg : gm ((f ≫ π₂) ≫ β) z _ (M₀.g a a') = gm ((f ≫ π₁) ≫ β) z _ (M₀.g a a') := by
      simp only [Category.assoc, hβ]
    dsimp only
    rw [e₂, e₁, ew, hg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨s, hs⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j₁, h₁⟩ := exists_chart hL (π₁ x)
      obtain ⟨j₂, h₂⟩ := exists_chart hL (π₂ x)
      obtain ⟨j₀, h₀⟩ := exists_chart hM (β (π₁ x))
      exact Opens.mem_iSup.2 ⟨(j₀, j₁, j₂), (hW _ x).2 ⟨h₀, h₁, h₂⟩⟩) u
    (fun t t' x hx => (hu _ (𝟙 B) x t hx.1).trans ((indep _ (𝟙 B) x t t' hx.1 hx.2).trans (hu _ (𝟙 B) x t' hx.2).symm))
  refine ⟨s, fun Z f z j₀ j₁ j₂ h₀ h₁ h₂ => ?_⟩
  have hz : f z ∈ W (j₀, j₁, j₂) := (hW _ _).2 ⟨h₀, h₁, h₂⟩
  exact (gm_res f z le_top hz s).symm.trans ((congrArg (gm f z _) (hs _)).trans (hu Z f z _ hz))

theorem exists_unit : ∀ (A : Type) [CommRing A] (B' : Over (Sp A)) [GrpObj B'], IsAbelianScheme B' → ∀ {X Y : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β)) (π₁ π₂ : B'.left ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)), L.IsLB → M₀.IsLB → wF.IsGen → w.IsGen → π₁ ≫ β = π₂ ≫ β → ∃ u : Aˣ, ∀ (p : Sp A ⟶ B'.left), p ≫ B'.hom = 𝟙 _ → ∀ (zz : Sp A) (J : (Sp A ⟶ X) → L.ι) (J₀ : (Sp A ⟶ Y) → M₀.ι), Good L zz J → Good M₀ zz J₀ → gm (p ≫ π₂) zz _ (wF.s (fun _ => J₀ (p ≫ π₂ ≫ β), J (p ≫ π₂))) * gm p zz _ (w.s (fun _ => J (p ≫ π₂), fun _ => J (p ≫ π₁))) = gm (𝟙 _) zz ⊤ (unitOn u) * gm (p ≫ π₁) zz _ (wF.s (fun _ => J₀ (p ≫ π₁ ≫ β), J (p ≫ π₁))) := by
  intro A _ B' _ hB X Y L M₀ β wF π₁ π₂ w hL hM hwF hw hβ
  obtain ⟨s, hs⟩ := exists_glued L M₀ β wF π₁ π₂ w hL hM ((isGen_iff wF).1 hwF) ((isGen_iff w).1 hw) hβ
  have hbij := GlobalTheory.globalFns_holds _ B' hB
  let e := RingEquiv.ofBijective B'.hom.appTop.hom hbij
  let a : Γ(Sp A, ⊤)ˣ := Units.map e.symm.toMonoidHom s
  have ha : Units.map B'.hom.appTop.hom.toMonoidHom a = s := by
    ext
    exact e.apply_symm_apply _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom a, ?_⟩
  intro p hp zz J J₀ hJ hJ₀
  have hua : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom a) = a := by
    ext
    simp [unitOn]
  have k₁ := gm_pull p B'.hom zz ⊤ trivial a
  rw [hp] at k₁
  have key : gm p zz ⊤ s = gm (𝟙 _) zz ⊤ a := by
    rw [← ha]
    exact k₁
  have hs' := hs (Sp A) p zz (J₀ (p ≫ π₁ ≫ β)) (J (p ≫ π₁)) (J (p ≫ π₂)) (hJ₀ _) (hJ _) (hJ _)
  rw [hua, ← key, show p ≫ π₂ ≫ β = p ≫ π₁ ≫ β by rw [hβ], hs']
  exact (inv_mul_cancel_right _ _).symm

end GlobalTheory.PullAutConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantUnitPulledBackBundleAutomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_unit_pulledBack_bundle_automorphism : ∀ (A : Type) [CommRing A] (B' : Over (Sp A)) [GrpObj B'], IsAbelianScheme B' → ∀ {X Y : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β)) (π₁ π₂ : B'.left ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)), L.IsLB → M₀.IsLB → wF.IsGen → w.IsGen → π₁ ≫ β = π₂ ≫ β → ∃ u : Aˣ, ∀ (p : Sp A ⟶ B'.left), p ≫ B'.hom = 𝟙 _ → ∀ (zz : Sp A) (J : (Sp A ⟶ X) → L.ι) (J₀ : (Sp A ⟶ Y) → M₀.ι), Good L zz J → Good M₀ zz J₀ → gm (p ≫ π₂) zz _ (wF.s (fun _ => J₀ (p ≫ π₂ ≫ β), J (p ≫ π₂))) * gm p zz _ (w.s (fun _ => J (p ≫ π₂), fun _ => J (p ≫ π₁))) = gm (𝟙 _) zz ⊤ (unitOn u) * gm (p ≫ π₁) zz _ (wF.s (fun _ => J₀ (p ≫ π₁ ≫ β), J (p ≫ π₁))) := by
  first | exact @GlobalTheory.PullAutConst.exists_unit | exact GlobalTheory.PullAutConst.exists_unit | (intros; apply GlobalTheory.PullAutConst.exists_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIdentificationsAgreeConstantTangent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIdentificationsAgreeConstantTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigHom

theorem isNilpotent_ker_fst (k : Type) [Field k] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff]
  refine Submodule.mul_le.2 fun a ha b hb => ?_
  rw [RingHom.mem_ker] at ha hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  rw [Submodule.mem_bot]
  ext <;> simp [ha, hb]

theorem mk_ker_fst_eq (k : Type) [Field k] :
    Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) =
      ((Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom)).comp
        (algebraMap k (DualNumber k))).comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply]
  rw [Ideal.Quotient.eq, RingHom.mem_ker]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.RigHom

namespace GlobalTheory.RigHom

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem comp_eq_of_const : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R) (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.P.A.left ⟶ B₀.left), IsGrpPullback Q.P.A B₀ (spMap ιb) β → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (GlobalTheory.RigChart.constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ ≫ β = π₂ ≫ β := by
  intro R _ _ Q W₀ _ ιb B₀ _ β hβ k _ ρ hρ B' _ π₁ π₂ h₁ h₂ h0
  have c₁ : IsGrpPullback B' B₀ (spMap (ρ.comp ιb)) (π₁ ≫ β) :=
    (IsGrpPullback.comp h₁ hβ).congr (spMap_comp' ιb ρ) rfl
  have c₂ : IsGrpPullback B' B₀ (spMap (ρ.comp ιb)) (π₂ ≫ β) := by
    refine (IsGrpPullback.comp h₂ hβ).congr ?_ rfl
    rw [spMap_comp', hρ]
    rfl
  have hab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb h₁
  obtain ⟨e₁, he₁, f₁⟩ := grpPullback_iso c₁ (isGrpPullback_pullback B₀ (spMap (ρ.comp ιb)))
  obtain ⟨e₂, he₂, f₂⟩ := grpPullback_iso c₂ (isGrpPullback_pullback B₀ (spMap (ρ.comp ιb)))
  let I := RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom
  have hI : I ≤ nilradical (DualNumber k) := by
    obtain ⟨n, hn⟩ := isNilpotent_ker_fst k
    intro x hx
    exact ⟨n, by
      have : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this⟩
  have hj : pullback.fst B'.hom (spMap (Ideal.Quotient.mk I)) ≫ π₁ =
      pullback.fst B'.hom (spMap (Ideal.Quotient.mk I)) ≫ π₂ := by
    refine h0 _ _ (pullback.snd B'.hom (spMap (Ideal.Quotient.mk I)) ≫
      spMap ((Ideal.Quotient.mk I).comp (algebraMap k (DualNumber k)))) ?_
    rw [pullback.condition, Category.assoc, spMap_comp']
    congr 2
    exact mk_ker_fst_eq k
  have key : e₁.hom = e₂.hom := by
    refine GlobalTheory.NilRigidity.eq_of_eq_on_quotient I hI B' _ hab e₁.hom e₂.hom ?_
      (by rw [he₁.one_hom, he₂.one_hom])
    apply pullback.hom_ext
    · have f₁' : e₁.hom.left ≫ pullback.fst B₀.hom (spMap (ρ.comp ιb)) = π₁ ≫ β := f₁
      have f₂' : e₂.hom.left ≫ pullback.fst B₀.hom (spMap (ρ.comp ιb)) = π₂ ≫ β := f₂
      rw [Category.assoc, Category.assoc, f₁', f₂', ← Category.assoc, hj, Category.assoc]
    · have w₁ : e₁.hom.left ≫ pullback.snd B₀.hom (spMap (ρ.comp ιb)) = B'.hom := Over.w e₁.hom
      have w₂ : e₂.hom.left ≫ pullback.snd B₀.hom (spMap (ρ.comp ιb)) = B'.hom := Over.w e₂.hom
      rw [Category.assoc, Category.assoc, w₁, w₂]
  rw [← f₁, ← f₂, key]

end GlobalTheory.RigHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIdentificationsAgreeConstantTangentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_identifications_agree_constant_tangent : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R) (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.P.A.left ⟶ B₀.left), IsGrpPullback Q.P.A B₀ (spMap ιb) β → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (GlobalTheory.RigChart.constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ ≫ β = π₂ ≫ β := by
  first | exact @GlobalTheory.RigHom.comp_eq_of_const | exact GlobalTheory.RigHom.comp_eq_of_const | (intros; apply GlobalTheory.RigHom.comp_eq_of_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRigidOfBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfIsPartOfBasisBalFormsOfMem
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

theorem eq_zero_of_linearIndependent_int_rat {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (q : ι → ℚ) (hq : ∀ y, ∑ i, q i * (f i y : ℚ) = 0) : q = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  have hb' : ∀ i, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * q i := fun i => by
    obtain ⟨r, hr⟩ := hb i
    exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
  choose n hn using hb'
  have h0 : n = 0 := by
    rw [Fintype.linearIndependent_iff] at hf
    funext i
    refine hf n ?_ i
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : ((∑ i, n i * f i y : ℤ) : ℚ) = ((b : ℤ) : ℚ) * ∑ i, q i * (f i y : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hn i]; ring
    rw [hq y, mul_zero] at this
    exact_mod_cast this
  funext i
  have hbne : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have h := hn i
  rw [h0] at h
  simp only [Pi.zero_apply, Int.cast_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hbne

theorem eq_zero_of_linearIndependent_int {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (k : Type) [Field k] [CharZero k] (a : ι → k)
    (ha : ∀ y, ∑ i, a i * (f i y : k) = 0) : a = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace ℚ k
  have key : ∀ j, (fun i => B.coord j (a i)) = 0 := fun j =>
    eq_zero_of_linearIndependent_int_rat hf _ fun y => by
      have h := congrArg (B.coord j) (ha y)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  funext i
  apply B.repr.injective
  ext j
  have := congrFun (key j) i
  simpa [Module.Basis.coord_apply] using this

end GlobalTheory.PolFan

namespace GlobalTheory.PolFan

end GlobalTheory.PolFan
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautRigid

def dlog (k : Type) [Field k] : (DualNumber k)ˣ →* Multiplicative k where
  toFun x := Multiplicative.ofAdd ((x : DualNumber k).snd / (x : DualNumber k).fst)
  map_one' := by simp
  map_mul' x y := by
    have fne : ∀ x : (DualNumber k)ˣ, (x : DualNumber k).fst ≠ 0 := fun x h => by
      have := congrArg TrivSqZeroExt.fst x.mul_inv
      rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at this
      exact zero_ne_one this
    have hx := fne x
    have hy := fne y
    rw [← ofAdd_add]
    congr 1
    simp only [Units.val_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    field_simp
    ring

theorem fst_ne_zero {k : Type} [Field k] (x : (DualNumber k)ˣ) : (x : DualNumber k).fst ≠ 0 := fun h => by
  have := congrArg TrivSqZeroExt.fst x.mul_inv
  rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at this
  exact zero_ne_one this

theorem dlog_apply {k : Type} [Field k] (x : (DualNumber k)ˣ) :
    Multiplicative.toAdd (dlog k x) = (x : DualNumber k).snd / (x : DualNumber k).fst := rfl

def onePlus {k : Type} [Field k] (s : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr s
  inv := 1 - TrivSqZeroExt.inr s
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

theorem dlog_onePlus {k : Type} [Field k] (s : k) : Multiplicative.toAdd (dlog k (onePlus s)) = s := by
  rw [dlog_apply]; simp [onePlus]

end GlobalTheory.TautRigid

namespace GlobalTheory.TautRigid

open GlobalTheory.RigChart GlobalTheory.ToricData

variable {R : Type} [CommRing R] [IsDomain R]

def lamC (Q : DegPre R) {k : Type} [Field k] {B' : Scheme.{0}} {π₁ π₂ : B' ⟶ Q.P.A.left}
    (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B')) (y z : Q.X)
    (zz : Sp (DualNumber k)) (J : (Sp (DualNumber k) ⟶ Q.P.A.left) → Q.P.L.ι) : ((Sp (DualNumber k)).presheaf.stalk zz)ˣ :=
  gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) *
    (gm (c' y) zz _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))))⁻¹ *
    (gm (c' z) zz _ (w.s (fun _ => J (c' z ≫ π₂), fun _ => J (c' z ≫ π₁))))⁻¹ *
    gm (c' 0) zz _ (w.s (fun _ => J (c' 0 ≫ π₂), fun _ => J (c' 0 ≫ π₁)))

def AbConst (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B']
    (π₁ π₂ : B'.left ⟶ Q.P.A.left) (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) :
    Prop :=
  IsGrpPullback B' Q.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ ∧
    (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) ∧
    w.IsGen ∧ (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left)

end GlobalTheory.TautRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRigiditySndEqZeroCanonicalChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorRigid

open GlobalTheory.RigChart GlobalTheory.ToricData

theorem commGroup_fourfold_cancellation {G : Type*} [CommGroup G] (a1 a2 a3 a4 b1 b2 b3 b4 U V : G) :
    a1 * a2⁻¹ * a3⁻¹ * a4 * V = ((b1⁻¹ * (U * a1)) * (b2⁻¹ * (U * a2))⁻¹ * (b3⁻¹ * (U * a3))⁻¹ * (b4⁻¹ * (U * a4))) *
      (b1 * b2⁻¹ * b3⁻¹ * b4 * V) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem val_const_of_fromBase : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left) (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), GlobalTheory.TautRigid.AbConst Q ρ B' π₁ π₂ w c' → ∀ (y z : Q.X) (zz : Sp (DualNumber k)) (J : (Sp (DualNumber k) ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L zz J → val (τ₀ y z) (spMap ρ) zz J = GlobalTheory.TautRigid.lamC Q w c' y z zz J * val (τ₀ y z) (spMap (GlobalTheory.RigChart.constHom ρ)) zz J := by
  intro R _ _ Q τ₀ W₀ _ ιb hFB k _ ρ hρ B' iG π₁ π₂ w c' hA y z zz J hJ
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hA
  obtain ⟨B₀, iB₀, M₀, c₀, τ₁, β, wF, hB₀, hM₀, hβ, hwF, hc₀, hτ₁, hpt⟩ := GlobalTheory.T.fromBase_identity_along_morphism Q τ₀ ιb hFB
  have hπ : π₁ ≫ β = π₂ ≫ β := GlobalTheory.T.abelianPart_identifications_agree_constant_tangent Q ιb B₀ β hβ k ρ hρ B' π₁ π₂ h₁ h₂ h₃
  have hB'ab : IsAbelianScheme B' := GlobalTheory.T.isAbelianScheme_of_grpPullback' π₁ h₁ Q.P.isAb
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_constant_unit_pulledBack_bundle_automorphism (DualNumber k) B' hB'ab Q.P.L M₀ β wF π₁ π₂ w Q.P.isLB hM₀ hwF h₄ hπ
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt hM₀ zz
  have e1 := hpt _ (spMap ρ) y z zz J J₀ hJ hJ₀
  have e2 := hpt _ (spMap (GlobalTheory.RigChart.constHom ρ)) y z zz J J₀ hJ hJ₀
  have hιb : spMap ρ ≫ spMap ιb = spMap (GlobalTheory.RigChart.constHom ρ) ≫ spMap ιb := by
    have h' : (GlobalTheory.RigChart.constHom ρ).comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) := by
      exact RingHom.ext fun x => rfl
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (hρ.trans h'.symm)
  rw [hιb] at e1
  have q1 : ∀ x, spMap ρ ≫ cpt Q x = c' x ≫ π₁ := fun x => ((h₅ x).2.1).symm
  have q2 : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x = c' x ≫ π₂ := fun x => ((h₅ x).2.2).symm
  have q1' : ∀ x, spMap ρ ≫ cpt Q x ≫ β = c' x ≫ π₁ ≫ β := fun x => by
    rw [← Category.assoc, q1, Category.assoc]
  have q2' : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x ≫ β = c' x ≫ π₂ ≫ β := fun x => by
    rw [← Category.assoc, q2, Category.assoc]
  rw [q1', q1', q1', q1', q1, q1, q1, q1] at e1
  rw [q2', q2', q2', q2', q2, q2, q2, q2] at e2
  have hW : ∀ x, gm (c' x) zz _ (w.s (fun _ => J (c' x ≫ π₂), fun _ => J (c' x ≫ π₁))) =
      (gm (c' x ≫ π₂) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₂ ≫ β), J (c' x ≫ π₂))))⁻¹ *
        (gm (𝟙 _) zz ⊤ (unitOn u) * gm (c' x ≫ π₁) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₁ ≫ β), J (c' x ≫ π₁)))) :=
    fun x => eq_inv_mul_of_mul_eq (hu (c' x) (h₅ x).1 zz J J₀ hJ hJ₀)
  unfold GlobalTheory.TautRigid.lamC
  rw [e1, e2, hW, hW, hW, hW]
  exact commGroup_fourfold_cancellation _ _ _ _ _ _ _ _ _ _

theorem snd_eq_zero_of_isConstAlong : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) → ∀ j, (ρ (Cn.ψ (MvPolynomial.X (.inr j)))).snd = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn k _ ρ a hC hconst j
  obtain ⟨ε', τ₀, hε', hFB, hτ⟩ := GlobalTheory.T.canonicalFamily_periods_in_coordinates Xo c φ R hB C Cn
  obtain ⟨B', iG, π₁, π₂, w, c', h₁, h₂, h₃, h₄, h₅, h₆⟩ := hC
  have hA : GlobalTheory.TautRigid.AbConst C.P.D.toPre ρ B' π₁ π₂ w c' := ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hB1 := val_const_of_fromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) hFB k ρ hconst B' iG π₁ π₂ w c' hA
  haveI : CharZero k := by
    let f : c.F →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp (ρ.comp C.b)
    exact (f.charZero_iff f.injective).1 inferInstance
  set M : ℕ := l.M' with hMdef
  have hM : 0 < M := level_pos l
  let Q := C.P.D.toPre
  let u : Fin Cn.N → Rˣ := fun j => (Cn.tor j).unit
  have hu : ∀ j, (u j : R) = Cn.ψ (MvPolynomial.X (.inr j)) := fun j => IsUnit.unit_spec _
  let δ : Fin C.m → LinearMap.BilinForm ℤ Q.X := C.δ
  let ε : Fin Cn.N → LinearMap.BilinForm ℤ Q.X := fun j => (ε' (.inr j) : LinearMap.BilinForm ℤ Q.X)
  have hδ : ∀ i, (ε' (.inl i) : LinearMap.BilinForm ℤ Q.X) = C.δ i := fun i => by
    rw [hε', Cn.cone i]
  have hli : LinearIndependent ℤ (Sum.elim δ ε) := by
    have h0 : LinearIndependent ℤ (fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X)) :=
      ε'.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
    have hEq : Sum.elim δ ε = fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X) := by
      funext κ; rcases κ with i | i
      · exact (hδ i).symm
      · rfl
    rw [hEq]; exact h0
  have key : ∀ y z, ∑ j, ((M : ℤ) * ε j y z) • Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) =
      ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) := by
    intro y z
    set v : Rˣ := ∏ j, u j ^ ((M : ℤ) * ε j y z) with hvdef
    let f : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
    obtain ⟨hg, kk, hk, hv⟩ := hτ y z
    have hU' : GlobalTheory.RigChart.IsUnitTau Q C.s (fun i => (M : ℤ) • C.δ i) y z (GlobalTheory.UU.scaleGen (unitOn v) (τ₀ y z)) := by
      refine ⟨GlobalTheory.UU.scaleGen_isGen _ hg, kk * (f v)⁻¹, ?_, fun zz J hJ => ?_⟩
      · have hfv : ((f v : (FractionRing R)ˣ) : FractionRing R) =
            ∏ j, algebraMap R (FractionRing R) (u j : R) ^ ((M : ℤ) * ε j y z) := by
          simp only [f, v, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
            MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
        have hne : ((f v : (FractionRing R)ˣ) : FractionRing R) ≠ 0 := (f v).ne_zero
        rw [Units.val_mul, hk, Units.val_inv_eq_inv_val, Fin.prod_univ_add]
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, LinearMap.smul_apply, smul_eq_mul,
          Cn.bd, hδ, ← hu]
        rw [← hfv, mul_inv_cancel_right₀ hne]
      · have e : gm (toUnit (TK R)).left zz ⊤ (unitOn v) = gm (𝟙 (TK R).left) zz ⊤ (unitOn (f v)) := by
          rw [GlobalTheory.UU.gm_top]
          exact congrArg _ (pullTop_unitOn (algebraMap R (FractionRing R)) _)
        rw [hv zz J hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e, ← _root_.mul_assoc, ← map_mul, ← unitOn_mul,
          inv_mul_cancel_right]
    set s : k := ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) with hs
    have hE : ∀ zz : Sp (DualNumber k), gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) =
        gm (𝟙 _) zz ⊤ (unitOn (GlobalTheory.TautRigid.onePlus s * Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) := by
      intro zz
      obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt C.P.D.toPre.P.isLB zz
      have hp := h₆ y z _ hU' (GlobalTheory.TautRigid.onePlus s) rfl zz J hJ
      have hb := hB1 y z zz J hJ
      have e₁ : gm (spMap ρ) zz ⊤ (unitOn v) = gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) := by
        rw [GlobalTheory.UU.gm_top]; exact congrArg _ (pullTop_unitOn ρ v)
      have e₂ : gm (spMap (GlobalTheory.RigChart.constHom ρ)) zz ⊤ (unitOn v) =
          gm (𝟙 _) zz ⊤ (unitOn (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) := by
        rw [GlobalTheory.UU.gm_top]; exact congrArg _ (pullTop_unitOn (GlobalTheory.RigChart.constHom ρ) v)
      rw [GlobalTheory.UU.val_scaleGen _ _ _ hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e₁, e₂, hb] at hp
      change _ = GlobalTheory.TautRigid.lamC Q w c' y z zz J * _ * _ at hp
      rw [unitOn_mul, map_mul]
      exact mul_right_cancel (hp.trans ((congrArg (· * _) (_root_.mul_comm _ _)).trans (mul_mul_mul_comm _ _ _ _)))
    have hv2 := unitOn_inj.1 (unit_ext fun x _ => hE x)
    have h3 := congrArg (fun x => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k x)) hv2
    rw [map_mul, toAdd_mul, GlobalTheory.TautRigid.dlog_onePlus] at h3
    have hc0 : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) = 0 := by
      have hs0 : ∀ r : R, (GlobalTheory.RigChart.constHom ρ r).snd = 0 := fun r => by
        simp only [GlobalTheory.RigChart.constHom, RingHom.comp_apply]
        rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      rw [GlobalTheory.TautRigid.dlog_apply, Units.coe_map]
      erw [hs0, zero_div]
    rw [hc0, add_zero] at h3
    rw [← h3, hvdef, map_prod, map_prod, toAdd_prod]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zpow, map_zpow, toAdd_zpow]
  set L : Fin Cn.N → k := fun j => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) with hL
  let F : Fin C.m ⊕ Fin Cn.N → Q.X × Q.X → ℤ := fun κ p => Sum.elim δ ε κ p.1 p.2
  have hF : LinearIndependent ℤ F := by
    let e : LinearMap.BilinForm ℤ Q.X →ₗ[ℤ] (Q.X × Q.X → ℤ) :=
      { toFun := fun β p => β p.1 p.2
        map_add' := fun β β' => by funext p; rfl
        map_smul' := fun n β => by funext p; rfl }
    have he : LinearMap.ker e = ⊥ := LinearMap.ker_eq_bot.mpr fun β β' h =>
      LinearMap.ext fun y => LinearMap.ext fun z => congrFun h (y, z)
    have hEq : F = e ∘ Sum.elim δ ε := by
      funext κ p
      rcases κ with i | j <;> rfl
    rw [hEq]
    exact hli.map' e he
  have hz := GlobalTheory.PolFan.eq_zero_of_linearIndependent_int hF k
    (Sum.elim (fun i => a i * (M : k)) (fun j => -(L j * (M : k)))) fun p => by
      rw [Fintype.sum_sum_type]
      have hk := key p.1 p.2
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, LinearMap.smul_apply, smul_eq_mul] at hk
      simp only [Sum.elim_inl, Sum.elim_inr, F]
      have e1 : ∑ i, a i * (M : k) * ((δ i p.1 p.2 : ℤ) : k) = ∑ i, a i * ((M : k) * ((δ i p.1 p.2 : ℤ) : k)) :=
        Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ j, -(L j * (M : k)) * ((ε j p.1 p.2 : ℤ) : k) =
          -∑ j, (M : k) * ((ε j p.1 p.2 : ℤ) : k) * L j := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1, e2, ← hk]
      ring
  have h1 := congrFun hz (Sum.inr j)
  simp only [Sum.elim_inr, Pi.zero_apply, neg_eq_zero, mul_eq_zero, Nat.cast_eq_zero] at h1
  have hLj : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) = 0 := h1.resolve_right hM.ne'
  rw [GlobalTheory.TautRigid.dlog_apply, Units.coe_map] at hLj
  have := (div_eq_zero_iff.1 hLj).resolve_right (by
    have := GlobalTheory.TautRigid.fst_ne_zero (Units.map ρ.toMonoidHom (u j))
    rwa [Units.coe_map] at this)
  rw [← hu]
  exact this

end GlobalTheory.TorRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRigiditySndEqZeroCanonicalChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_rigidity_snd_eq_zero_canonicalChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) → ∀ j, (ρ (Cn.ψ (MvPolynomial.X (.inr j)))).snd = 0 := by
  first | exact @GlobalTheory.TorRigid.snd_eq_zero_of_isConstAlong | exact GlobalTheory.TorRigid.snd_eq_zero_of_isConstAlong | (intros; apply GlobalTheory.TorRigid.snd_eq_zero_of_isConstAlong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDataRigidAlongStratum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.Rigid

theorem isLocalHom_of_fst {R : Type} [CommRing R] [IsLocalRing R] {k : Type} [Field k] (θ : R →+* DualNumber k)
    (h : ∀ r ∈ maximalIdeal R, (θ r).fst = 0) : IsLocalHom θ := by
  refine ⟨fun r hr => ?_⟩
  by_contra hn
  have hm : r ∈ maximalIdeal R := (mem_maximalIdeal r).mpr hn
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, h r hm] at hr
  exact not_isUnit_zero hr

end GlobalTheory.UCanon.Rigid

theorem GlobalTheory.UCanon.isRigid_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), GlobalTheory.RigChart.IsRigid C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn k _ ρ a hmax hs hc
  have hbase := GlobalTheory.T.base_rigidity_tangent_vector_constant Xo c φ R hB C Cn k ρ a hc
  have htor := GlobalTheory.T.torus_rigidity_snd_eq_zero_canonicalChart Xo c φ R hB C Cn k ρ a hc hbase
  have h₁ : IsLocalHom ρ := GlobalTheory.UCanon.Rigid.isLocalHom_of_fst ρ hmax
  have h₂ : IsLocalHom (GlobalTheory.RigChart.constHom ρ) := by
    refine GlobalTheory.UCanon.Rigid.isLocalHom_of_fst _ fun r hr => ?_
    simp [GlobalTheory.RigChart.constHom, hmax r hr]
  have hψ : ρ.comp Cn.ψ = (GlobalTheory.RigChart.constHom ρ).comp Cn.ψ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      have := congrArg (fun f => f x) hbase
      simpa [GlobalTheory.RigChart.constHom] using this
    · rintro (i | j)
      · simp [GlobalTheory.RigChart.constHom, Cn.bd, hs]
      · apply TrivSqZeroExt.ext
        · simp [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl]
        · simpa [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl] using htor j
  have heq := GlobalTheory.TChart.cuniq _ R (DualNumber k) Cn.ψ Cn.compl ρ (GlobalTheory.RigChart.constHom ρ) h₁ h₂ hψ
  intro r
  rw [heq]
  simp [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDataRigidAlongStratumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_data_rigid_along_stratum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), GlobalTheory.RigChart.IsRigid C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) := by
  first | exact @GlobalTheory.UCanon.isRigid_canon | exact GlobalTheory.UCanon.isRigid_canon | (intros; apply GlobalTheory.UCanon.isRigid_canon <;> assumption)
end
