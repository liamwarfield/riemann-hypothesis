module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendFiniteModif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsPrescribedReductionFiniteExt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreThetaEmbeddingOfSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToProjSecPullSecPull
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupFibreBaseChangeCommonFieldIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupFibreBaseChangeCommonFieldIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.FibBC

theorem pullCompIso_hom_eq {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).hom = (Over.pullbackComp p f).hom.app G := Category.comp_id _

theorem pullCompIso_fst {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).hom.left ≫ pullback.fst _ p ≫ pullback.fst G.hom f = pullback.fst G.hom (p ≫ f) := by
  rw [pullCompIso_hom_eq]
  simp [Over.pullbackComp, Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]

theorem pullCompIso_inv_fst {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).inv.left ≫ pullback.fst G.hom (p ≫ f) = pullback.fst _ p ≫ pullback.fst G.hom f := by
  rw [← pullCompIso_fst, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]

theorem pullback_map_fst {S S' : Scheme.{0}} (g : S' ⟶ S) {A B : Over S} (u : A ⟶ B) :
    ((Over.pullback g).map u).left ≫ pullback.fst B.hom g = pullback.fst A.hom g ≫ u.left :=
  pullback.lift_fst _ _ _

theorem fibre_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W'] (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left), IsGrpPullback G' G ξ' β → ∀ (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W') (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y), IsMonHom e'.hom → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (i₂ : ResidueField W' →+* Ω'), spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ' → io.comp κ = i₂.comp κ' → ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y) (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left), IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧ e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') := by
  intro S G _ W' _ _ G' _ ξ' β hβ k _ Y _ κ' e' he' Ω _ x κ Ω' _ io i₂ hc hκ
  have hm : spMap i₂ ≫ spMap κ' = spMap (io.comp κ) := by
    rw [hκ, ← Spec.map_comp]; rfl
  rw [← hm]

  have h₁ : IsGrpPullback ((Over.pullback (spMap i₂ ≫ spMap (residue W'))).obj G') G (spMap io ≫ x)
      (pullback.fst G'.hom (spMap i₂ ≫ spMap (residue W')) ≫ β) :=
    ((isGrpPullback_pullback G' (spMap i₂ ≫ spMap (residue W'))).comp hβ).congr
      (by rw [hc, Category.assoc]) rfl
  obtain ⟨e₁, he₁, he₁f⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap io ≫ x)) h₁
  let e₂ := pullCompIso (spMap i₂) (spMap (residue W')) G'
  let e₃ := (Over.pullback (spMap i₂)).mapIso e'
  let e₄ := (pullCompIso (spMap i₂) (spMap κ') Y).symm
  have i₃ : IsMonHom e₃.hom := by show IsMonHom ((Over.pullback (spMap i₂)).map e'.hom); infer_instance
  have i₄ : IsMonHom e₄.hom := by show IsMonHom (pullCompIso (spMap i₂) (spMap κ') Y).inv; infer_instance
  have f₂ : e₂.hom.left ≫ pullback.fst _ (spMap i₂) ≫ pullback.fst G'.hom (spMap (residue W')) =
      pullback.fst G'.hom (spMap i₂ ≫ spMap (residue W')) := pullCompIso_fst _ _ _
  have f₃ : e₃.hom.left ≫ pullback.fst _ (spMap i₂) = pullback.fst _ (spMap i₂) ≫ e'.hom.left :=
    pullback_map_fst _ _
  have f₄ : e₄.hom.left ≫ pullback.fst Y.hom (spMap i₂ ≫ spMap κ') =
      pullback.fst _ (spMap i₂) ≫ pullback.fst Y.hom (spMap κ') := pullCompIso_inv_fst _ _ _
  refine ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄, e₁.hom.left ≫ e₂.hom.left ≫ pullback.fst _ (spMap i₂), ?_, ?_, ?_⟩
  · show IsMonHom (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom); infer_instance
  · rw [Category.assoc, Category.assoc, reassoc_of% f₂, he₁f]
  · show (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom).left ≫ _ = _
    simp only [Over.comp_left, Category.assoc]
    rw [f₄, reassoc_of% f₃]

end GlobalTheory.Mum.FibBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupFibreBaseChangeCommonFieldIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupFibre_baseChange_common_field_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W'] (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left), IsGrpPullback G' G ξ' β → ∀ (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W') (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y), IsMonHom e'.hom → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (i₂ : ResidueField W' →+* Ω'), spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ' → io.comp κ = i₂.comp κ' → ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y) (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left), IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧ e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') := by
  first | exact @GlobalTheory.Mum.FibBC.fibre_baseChange | exact GlobalTheory.Mum.FibBC.fibre_baseChange | (intros; apply GlobalTheory.Mum.FibBC.fibre_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceSectionPullbackComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceSectionPullbackComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.toProj_secPull_secPull (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X)
    (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R)
    (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤)
    (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ =
      GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ := by
  refine GlobalTheory.ProjSpace.toProj_eq_of_locally hs₂ hs₁ fun z => ?_
  obtain ⟨k, hk⟩ : ∃ k : PUnit → L.ι, z ∈ (L.pull (g ≫ h)).U k :=
    GlobalTheory.ProjSpace.exists_chart_of_iSup_nonzeroLocus hs₂ z
  let l : ((L.pull h).pull g).ι := fun _ _ => k PUnit.unit
  have hle : (L.pull (g ≫ h)).U k ≤ ((L.pull h).pull g).U l := by
    rw [GlobalTheory.Cartier.pull_U L (g ≫ h) k, GlobalTheory.Cartier.pull_U (L.pull h) g l,
      GlobalTheory.Cartier.pull_U L h (fun _ => k PUnit.unit)]
    exact fun _ hy => hy
  refine ⟨_, hk, k, le_rfl, l, hle, 1, fun j => ?_⟩
  rw [_root_.one_mul]
  unfold GlobalTheory.secPull
  rw [GlobalTheory.chartSec_f, GlobalTheory.chartSec_f, GlobalTheory.chartSec_f (GlobalTheory.chartPullPull L (g ≫ h)) (s j) k]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE_assoc,
    Scheme.Hom.appLE_map]
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceSectionPullbackCompStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphismToProjSpace_sectionPullback_comp : ∀ (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X) (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R) (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤) (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤), GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ = GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ := by
  first | exact @GlobalTheory.Mum.toProj_secPull_secPull | exact GlobalTheory.Mum.toProj_secPull_secPull | (intros; apply GlobalTheory.Mum.toProj_secPull_secPull <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb.Fib

theorem trait (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (M : Modif R) (x₀ : M.S)
    (hx : M.π x₀ = closedPoint R) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
      GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ :=
  GlobalTheory.T.exists_completeTrait_over_closedPoint_modification R hR M x₀ hx

theorem compositum (X : Scheme.{0}) (K₁ K₂ : Type) [Field K₁] [Field K₂] (a : Sp K₁ ⟶ X) (b : Sp K₂ ⟶ X)
    (h : a (closedPoint K₁) = b (closedPoint K₂)) :
    ∃ (Ω : Type) (_ : Field Ω) (i₁ : K₁ →+* Ω) (i₂ : K₂ →+* Ω), spMap i₁ ≫ a = spMap i₂ ≫ b :=
  GlobalTheory.T.exists_common_field_of_fieldPoints_same_point X K₁ K₂ a b h

theorem baseChangeIso (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W']
    (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left) (hβ : IsGrpPullback G' G ξ' β)
    (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W')
    (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y) (he' : IsMonHom e'.hom)
    (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω')
    (i₂ : ResidueField W' →+* Ω') (hc : spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ')
    (hκ : io.comp κ = i₂.comp κ') :
    ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left),
      IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧
      e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') :=
  GlobalTheory.T.groupFibre_baseChange_common_field_iso S G W' G' ξ' β hβ k Y κ' e' he' Ω x κ Ω' io i₂ hc hκ

theorem toProj_secPull_secPull (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X)
    (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R)
    (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤)
    (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ =
      GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ :=
  GlobalTheory.T.morphismToProjSpace_sectionPullback_comp R N X Y Z L s h g f hs₁ hs₂

theorem toProj_congr {R : Type} [CommRing R] {N : ℕ} {X Z : Scheme.{0}} {L : LB X} (s : Fin (N + 1) → L.Sec)
    {a b : Z ⟶ X} (hab : a = b) {f g : Z ⟶ Sp R} (hfg : f = g)
    (h₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) a) = ⊤) (h₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) b) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) a) h₁ = GlobalTheory.ProjSpace.toProj g (fun i => GlobalTheory.secPull (s i) b) h₂ := by
  subst hab; subst hfg; rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem fib : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    (∀ g : G.left, M.π (G.hom g) = closedPoint R → g ∈ GlobalTheory.Mum.SecEmb.embH s) →
    ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ M.S) (κ : ResidueField R →+* Ω), x ≫ M.π = spMap (κ.comp (residue R)) →
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω')
      (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (l : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ (GlobalTheory.Mum.SecEmb.embH s).toScheme), IsMonHom e.hom ∧
      l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = pullback.fst G.hom (spMap io ≫ x) ∧
      l ≫ GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s = e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hji O hT hH Ω _ x κ hx
  have hcl : ∀ q : Sp Ω, M.π (x q) = closedPoint R := fun q => by
    rw [← Scheme.Hom.comp_apply, hx, Subsingleton.elim q (closedPoint Ω)]
    exact IsLocalRing.comap_closedPoint (κ.comp (residue R))
  obtain ⟨W, _, _, _, φ, ξ, hW, hφi, hφl, hξ, hξ0⟩ := trait R hR M _ (hcl (closedPoint Ω))
  obtain ⟨W', _, _, _, io', G', _, β, κ', e', hW', hio', hiof, hβ, hκ', he', hptw⟩ := hT W hW φ ξ hφi hφl hξ
  have hio0 : (spMap io') (closedPoint W') = closedPoint W := by
    letI := io'.toAlgebra
    have : Algebra.IsIntegral W W' := ⟨fun a => hiof.to_isIntegral a⟩
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) hiof.to_isIntegral (maximalIdeal W')))
  have hres0 : (spMap (residue W')) (closedPoint (ResidueField W')) = closedPoint W' :=
    IsLocalRing.comap_closedPoint (residue W')
  have hpt0 : (spMap (residue W') ≫ spMap io' ≫ ξ) (closedPoint (ResidueField W')) = x (closedPoint Ω) := by
    show ξ (spMap io' (spMap (residue W') (closedPoint _))) = _
    rw [hres0, hio0, hξ0]
  obtain ⟨Ω', _, io, i₂, hc⟩ := compositum M.S Ω (ResidueField W') x _ hpt0.symm
  have hκ : io.comp κ = i₂.comp κ' := by
    have e1 : spMap ((io.comp κ).comp (residue R)) = spMap ((i₂.comp κ').comp (residue R)) := by
      rw [RingHom.comp_assoc, spMap_comp', ← hx, RingHom.comp_assoc, hκ', spMap_comp', spMap_comp', spMap_comp',
        ← hξ, ← Category.assoc, hc]
      simp only [Category.assoc]
    have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    ext a
    obtain ⟨r, rfl⟩ := residue_surjective a
    exact congrArg (fun f : R →+* Ω' => f r) e2
  obtain ⟨e, τ, he, hτ, heτ⟩ := baseChangeIso M.S G W' G' (spMap io' ≫ ξ) β hβ (ResidueField R) Y κ' e' he' Ω x κ
    Ω' io i₂ hc hκ
  have hrange : Set.range (pullback.fst G.hom (spMap io ≫ x)) ⊆ Set.range (GlobalTheory.Mum.SecEmb.embH s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hH
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition_assoc, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact hcl _
  let l := IsOpenImmersion.lift (GlobalTheory.Mum.SecEmb.embH s).ι (pullback.fst G.hom (spMap io ≫ x)) hrange
  have hl : l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = pullback.fst G.hom (spMap io ≫ x) := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Ω', inferInstance, io, e, l, he, hl, ?_⟩
  have : IsReduced ((Over.pullback (spMap (io.comp κ))).obj Y).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd Y.hom (spMap (io.comp κ)))
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have : IsReduced ((Over.pullback (spMap io ≫ x)).obj G).left := isReduced_of_isOpenImmersion e.hom.left
  have hsep : IsSeparated (PSpace.str R N) := by unfold PSpace.str; infer_instance
  refine GlobalTheory.hom_ext_of_geometricPoints_dense (PSpace.str R N) _ _ ?_ Set.univ dense_univ ?_
  · have a1 : GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s ≫ PSpace.str R N = (GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π :=
      GlobalTheory.ProjSpace.toProj_str _ _ _
    have eo : e.hom.left ≫ pullback.snd Y.hom (spMap (io.comp κ)) = pullback.snd G.hom (spMap io ≫ x) := Over.w e.hom
    have a2 : (l ≫ GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s) ≫ PSpace.str R N =
        pullback.snd G.hom (spMap io ≫ x) ≫ spMap io ≫ x ≫ M.π := by
      rw [Category.assoc, a1, reassoc_of% hl, pullback.condition_assoc, Category.assoc]
    have a3 : (e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j) ≫ PSpace.str R N =
        pullback.snd G.hom (spMap io ≫ x) ≫ spMap (io.comp κ) ≫ spMap (residue R) := by
      rw [Category.assoc, Category.assoc, hj, pullback.condition_assoc, reassoc_of% eo]
    rw [a2, a3, hx, spMap_comp', spMap_comp']
    simp only [Category.assoc]
  · intro K _ _ q _
    obtain ⟨⟨hs, hproj⟩, -⟩ := hptw K (q ≫ τ) (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W')))
      (q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ')) (by simp) (by simp)
    have e3 : q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') ≫ j =
        (q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ')) ≫ j := by simp only [Category.assoc]
    rw [reassoc_of% heτ, e3, ← hproj]
    have hqb : (q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β := by
      rw [Category.assoc, hl, ← hτ]; simp only [Category.assoc]
    have hbase : (q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π =
        (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ G'.hom ≫ spMap (io'.comp φ) := by
      have hqb' : q ≫ l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β := by
        simp only [Category.assoc] at hqb; exact hqb
      rw [Category.assoc q l, reassoc_of% hqb', hβ.1.w_assoc, Category.assoc (spMap io'), hξ, spMap_comp']
      simp only [Category.assoc]
    have hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) ((q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι)) = ⊤ := by
      rw [hqb]; exact hs
    rw [← Category.assoc]
    show (q ≫ l) ≫ GlobalTheory.ProjSpace.toProj ((GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π)
      (fun i => GlobalTheory.secPull (s i) (GlobalTheory.Mum.SecEmb.embH s).ι) (GlobalTheory.Mum.SecEmb.iSup_nonzeroLocus_embH s) = _
    rw [← GlobalTheory.ProjSpace.toProj_secPull]
    exact (toProj_secPull_secPull R N _ _ _ B s _ (q ≫ l) _ _ hs₂).trans (toProj_congr s hqb hbase _ _)

end GlobalTheory.Mum.SecEmb.Fib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibrePt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb.ThetaPt

theorem exists_trait_pt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (x : M.S),
    M.π x = closedPoint R → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W)
      (ξ : Sp W ⟶ M.S), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧
      ξ (closedPoint W) = x := by
  intro R _ _ _ hR M x hx
  obtain ⟨⟨hRn, -, -, -⟩, hR0⟩ := hR
  haveI := M.integral
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  let A := M.S.presheaf.stalk x
  let ψc : CommRingCat.of R ⟶ A :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ M.π.appTop ≫ M.S.presheaf.germ ⊤ x trivial
  have hcomp : M.S.fromSpecStalk x ≫ M.π = Spec.map ψc := by
    simp only [ψc]
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hπinj : Function.Injective M.π.appTop.hom := fun a b h => GlobalTheory.Mum.jK_appTop_injective R (by
    rw [← M.appTop_comp, ← M.appTop_comp, h])
  have hψi : Function.Injective ψc.hom := by
    simp only [ψc, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (germ_injective_of_isIntegral M.S (U := ⊤) x trivial).comp
      (hπinj.comp (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective)
  have hψl : IsLocalHom ψc.hom := by
    refine ((IsLocalRing.local_hom_tfae ψc.hom).out 1 5).2 ?_
    have e1 : (Spec.map ψc) (closedPoint A) = closedPoint R := by
      have h0 := congrArg M.π (Scheme.fromSpecStalk_closedPoint (x := x))
      rw [hx] at h0
      rw [← hcomp]
      exact h0
    exact congrArg PrimeSpectrum.asIdeal e1
  haveI : CharZero A := charZero_of_injective_ringHom hψi
  obtain ⟨V, _, _, _, φ₀, hV, hφ₀i, hφ₀l⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V)
      (φ₀ : A →+* V), GlobalTheory.LN.CDvr V ∧ Function.Injective φ₀ ∧ IsLocalHom φ₀ := by
    by_cases h : IsField A
    · letI := h.toField
      refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, PowerSeries.C, ⟨inferInstance, ?_, ?_⟩,
        PowerSeries.C_injective, inferInstance⟩
      · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
      · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := A)) PowerSeries.C_injective
    · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating A h
      exact ⟨O, inferInstance, inferInstance, inferInstance, φ,
        ⟨inferInstance, inferInstance, charZero_of_injective_ringHom h1⟩, h1, h2⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, φ₀.comp ψc.hom, spMap φ₀ ≫ M.S.fromSpecStalk x, hV,
    hφ₀i.comp hψi, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, hcomp]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom]
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x) (IsLocalRing.comap_closedPoint φ₀)) Scheme.fromSpecStalk_closedPoint)

theorem isLocalHom_of_finite {W W' : Type} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    (io : W →+* W') (hf : io.Finite) : IsLocalHom io := by
  letI := io.toAlgebra
  haveI : Module.Finite W W' := hf
  have hmax : (maximalIdeal W').comap (algebraMap W W') = maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal W'))
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have : a ∈ (maximalIdeal W').comap (algebraMap W W') := hmax ▸ (IsLocalRing.mem_maximalIdeal a).2 h
  exact (IsLocalRing.mem_maximalIdeal _).1 (Ideal.mem_comap.1 this) ha

theorem exists_closedFibre_pt {W W' : Type} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    (io : W →+* W') [IsLocalHom io] {S : Scheme.{0}} (G : Over S) (G' : Over (Sp W')) (ξ : Sp W ⟶ S)
    (β : G'.left ⟶ G.left) (h : IsPullback β G'.hom G.hom (spMap io ≫ ξ)) (g : G.left)
    (hg : G.hom g = ξ (closedPoint W)) :
    ∃ q : ((Over.pullback (spMap (residue W'))).obj G').left, (pullback.fst G'.hom (spMap (residue W')) ≫ β) q = g := by
  have h1 : (spMap io) (closedPoint W') = closedPoint W := IsLocalRing.comap_closedPoint io
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap io ≫ ξ) g
    (closedPoint W') (by rw [hg]; exact (congrArg ξ h1).symm)
  have hg1 : β (h.isoPullback.inv z) = g := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
  have hg2 : G'.hom (h.isoPullback.inv z) = closedPoint W' := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]
  have h2 : (spMap (residue W')) (closedPoint (ResidueField W')) = closedPoint W' :=
    IsLocalRing.comap_closedPoint (residue W')
  obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := spMap (residue W'))
    (h.isoPullback.inv z) (closedPoint _) (hg2.trans h2.symm)
  exact ⟨q, by rw [Scheme.Hom.comp_apply, hq1, hg1]⟩

theorem toProj_congr {R : Type} [CommRing R] {M : ℕ} {Y : Scheme.{0}} {L : LB Y} {f f' : Y ⟶ Sp R}
    (e : f = f') (s : Fin (M + 1) → L.Sec) (hs hs' : ⨆ i, nonzeroLocus (s i) = ⊤) :
    GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.ProjSpace.toProj f' s hs' := by
  subst e; rfl

theorem mem_basicOpen_theta : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    ∀ (g : (GlobalTheory.Mum.SecEmb.embH s).toScheme) (y : Y.left), y ∈ O →
    M.π (G.hom ((GlobalTheory.Mum.SecEmb.embH s).ι g)) = closedPoint R → GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s g = j y →
    ∃ i : L.ι, (GlobalTheory.Mum.SecEmb.embH s).ι g ∈ G.left.basicOpen (θ.f i) := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hji O hT g y hy hgc hgj
  obtain ⟨W, _, _, _, φ, ξ, hW, hφi, hφl, hξ, hξx⟩ := exists_trait_pt R hR M _ hgc
  obtain ⟨W', _, _, _, io, G', _, β, κ, e, hW', hio, hiof, hpb, hκ, he, H⟩ := hT W hW φ ξ hφi hφl hξ
  haveI := isLocalHom_of_finite io hiof
  obtain ⟨q, hq⟩ := exists_closedFibre_pt io G G' ξ β hpb.1 _ hξx.symm
  let Ω : Type := (((Over.pullback (spMap (residue W'))).obj G').left).residueField q
  let p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left :=
    (((Over.pullback (spMap (residue W'))).obj G').left).fromSpecResidueField q
  haveI : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨p', hp'⟩ : ∃ p', p' = p ≫ pullback.fst G'.hom (spMap (residue W')) := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', y' = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) := ⟨_, rfl⟩
  obtain ⟨⟨hs, hproj⟩, hnz⟩ := H Ω p p' y' hp' hy'
  let pt : Sp Ω := closedPoint Ω
  have hpt : ∀ z : Sp Ω, z = pt := fun z => Subsingleton.elim _ _
  have hppt : p pt = q := Scheme.fromSpecResidueField_apply q pt
  have hg' : (p' ≫ β) pt = (embH s).ι g := by
    rw [hp', Category.assoc, Scheme.Hom.comp_apply, hppt]
    exact hq
  have hrange : Set.range (p' ≫ β) ⊆ Set.range (embH s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [hpt z, hg']
    exact ⟨g, rfl⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : Sp Ω ⟶ (embH s).toScheme, l₀ ≫ (embH s).ι = p' ≫ β :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hl₀pt : l₀ pt = g := by
    apply (embH s).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hl₀, hg']
  obtain ⟨-, hs2, e2⟩ := GlobalTheory.Mum.toProj_secPull_of_gs (Z := Sp Ω) s (fun i => GlobalTheory.secPull (s i) (embH s).ι)
    ((embH s).ι ≫ G.hom ≫ M.π) (iSup_nonzeroLocus_embH s) (p' ≫ β) l₀ (fun z => by
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hB.cover.ge (Set.mem_univ ((p' ≫ β) z)))
      have hla : l₀ z ∈ (B.pull (embH s).ι).U (fun _ => a) := Set.mem_iInter.2 fun _ => by
        show (embH s).ι (l₀ z) ∈ B.U a
        rw [← Scheme.Hom.comp_apply, hl₀]; exact ha
      refine ⟨a, fun _ => a, 1, ha, hla, fun i => ?_⟩
      rw [Units.val_one, _root_.one_mul]
      refine Eq.trans ?_ (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull B (embH s).ι) (s i) l₀ z (fun _ => a) hla).symm
      rw [hl₀]; rfl)
  have hstr : p' ≫ G'.hom ≫ spMap (io.comp φ) = l₀ ≫ (embH s).ι ≫ G.hom ≫ M.π := by
    have hw : β ≫ G.hom ≫ M.π = G'.hom ≫ spMap io ≫ ξ ≫ M.π := by
      rw [← Category.assoc, hpb.1.w]; simp only [Category.assoc]
    have hc : spMap (io.comp φ) = spMap io ≫ spMap φ := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [reassoc_of% hl₀, hw, hξ, hc]
  have key : y' ≫ j = l₀ ≫ embF (G.hom ≫ M.π) s := by
    rw [← hproj, toProj_congr hstr _ hs hs2]
    exact e2
  have hyy : y' pt = y := by
    apply hji.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply, hl₀pt, hgj]
  have hθ := hnz pt (hyy ▸ hy)
  rw [hg'] at hθ
  exact TopologicalSpace.Opens.mem_iSup.1 hθ

end GlobalTheory.Mum.SecEmb.ThetaPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitRedCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

theorem sec_eq_of_inj {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hinj : ∀ W : Y.Opens, Function.Injective (h.app W).hom)
    (H : ∀ y J, Good L y J → sval s (𝟙 Y' ≫ h) y J = sval s' (𝟙 Y' ≫ h) y J) : s = s' := by
  have e : ∀ j, s.f j = s'.f j := fun j => by
    refine hinj _ (fn_ext fun y hy => ?_)
    choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
    have hJ' : Good L y J := hJ
    have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j := hy
    have m := hJ'.mem φ (𝟙 Y' ≫ h)
    refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
    exact (sec_trans s _ y hy' m).trans ((congrArg _ (H y J hJ')).trans (sec_trans s' _ y hy' m).symm)
  cases s
  cases s'
  congr
  exact funext e

end GlobalTheory.Mum.SecEmb

namespace GlobalTheory.Mum.SecEmb

theorem traitRed_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C C' : LabCover D) (Sc : Secs C.toModif C.G C.P.L.L C.α) (h : C'.S ⟶ C.S) (β : C'.G.left ⟶ C.G.left),
    h ≫ C.π = C'.π → IsGrpPullback C'.G C.G h β → LBIso C'.P.L.L (C.P.L.L.pull β) →
    ∀ σ : Fin (Sc.N + 1) → SecK C.P.L.L β Sc.k, (∀ i, Agree C.P.L.L (σ i) (Sc.s i)) →
    ∀ θ₀ : SecK C.P.L.L β 1, Agree C.P.L.L θ₀ Sc.θ →
    ∃ θ : C'.P.L.L.Sec, GlobalTheory.Mum.SecEmb.TraitRed C'.toModif C'.G σ θ Sc.Y Sc.j Sc.O := by
  intro R _ _ _ _ D C C' Sc h β hπ hpb hiso σ hσ θ₀ hθ₀
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  obtain ⟨θ₁, hθ₁⟩ := exists_sec hL (φ := fun _ : Fin 1 => β) (ε := fun _ => ((1 : ℕ) : ℤ))
    (φ' := fun _ : PUnit => β) (ε' := fun _ => 1) (fun U _ g => by simp) θ₀
  obtain ⟨w, hw⟩ := hiso
  refine ⟨DVR.secOfIso (u := w) θ₁ hw C'.P.L.isLB (LB.isLB_pull hL β), ?_⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G'', _, β'', σ'', θ'', κ, e, hW', hio, hfin, hG'', hκ, he, hσ'', hθ'', hfib⟩ :=
    Sc.trait W hW φ (ξ ≫ h) hφ hloc (by rw [Category.assoc, hπ]; exact hξ)
  obtain ⟨β', hβ'1, hβ'2⟩ : ∃ β' : G''.left ⟶ C'.G.left, β' ≫ β = β'' ∧ β' ≫ C'.G.hom = G''.hom ≫ spMap io ≫ ξ :=
    ⟨hpb.1.lift β'' (G''.hom ≫ spMap io ≫ ξ) (by rw [hG''.1.w]; simp), hpb.1.lift_fst _ _ _, hpb.1.lift_snd _ _ _⟩
  subst hβ'1

  have hρ : Function.Injective ((algebraMap W' (FractionRing W')).comp (io.comp φ)) :=
    (IsFractionRing.injective W' (FractionRing W')).comp (hio.comp hφ)
  obtain ⟨ga, -, hga⟩ := Modif.factor_gp R C.toModif (FractionRing W') _ (jK W' ≫ spMap io ≫ ξ ≫ h) hρ (by
    rw [Category.assoc, Category.assoc, Category.assoc, hπ, hξ]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl)

  have : Smooth C.G.hom := C.semi.smooth
  have : Flat G''.hom := MorphismProperty.of_isPullback (P := @Flat) hG''.1 inferInstance

  have hgen : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G''.hom (jK W')), ∃ q : Z ⟶ C.A.A.left,
      q ≫ C.α = r ≫ pullback.fst G''.hom (jK W') ≫ β' ≫ β := fun Z r => by
    refine ⟨C.α_cart.1.lift (r ≫ pullback.fst G''.hom (jK W') ≫ β' ≫ β)
      (r ≫ pullback.snd G''.hom (jK W') ≫ spMap ga) ?_, C.α_cart.1.lift_fst _ _ _⟩
    have w₁ := hG''.1.w
    simp only [Category.assoc] at w₁ ⊢
    rw [w₁, ← hga, pullback.condition_assoc]

  have key : ∀ {n : ℕ} (a : SecK C.P.L.L (β' ≫ β) n) (b : SecK C.P.L.L β n) (c : SecK C.P.L.L C.α n),
      Agree C.P.L.L a c → Agree C.P.L.L b c → ∀ (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J), Good C.P.L.L z J →
        sval a r z J = sval b (r ≫ β') z J := by
    intro n a b c ha hb
    have e₁ : a = ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec b β' := by
      refine sec_eq_of_inj hL (GlobalTheory.ExpInt.generic_app_injective G'') fun y J hJ => ?_
      rw [ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
      obtain ⟨q, hq⟩ := hgen _ (𝟙 _)
      have hq' : q ≫ C.α = (𝟙 _ ≫ pullback.fst G''.hom (jK W')) ≫ β' ≫ β := by rw [hq]; simp
      refine (ha _ _ q hq'.symm y J hJ).trans (hb _ _ q ?_ y J hJ).symm
      rw [hq']; simp
    intro Z r z J hJ
    rw [e₁, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
  have hv : ∀ i (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J), Good C.P.L.L z J →
      sval (σ'' i) r z J = sval (σ i) (r ≫ β') z J := fun i => key _ _ _ (hσ'' i) (hσ i)
  have hvθ := key _ _ _ hθ'' hθ₀
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G'', inferInstance, β', κ, e, hW', hio, hfin,
    IsGrpPullback.cancel hpb (by rw [Category.assoc]; exact hG'') hβ'2, hκ, he, ?_⟩
  intro Ω _ p p' y hp hy
  obtain ⟨⟨hs, hproj⟩, hnz⟩ := hfib Ω p p' y hp hy
  have hnzi : ∀ (x : Sp Ω) i, p' x ∈ nonzeroLocus (σ'' i) ↔ (p' ≫ β') x ∈ nonzeroLocus (σ i) := fun x i => by
    choose J hJ using fun ψ : Sp Ω ⟶ C.G.left => exists_chart hL (ψ x)
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hv i _ _ _ _ hJ]
  have ht : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) (p' ≫ β')) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
    rw [GlobalTheory.nonzeroLocus_secPull] at hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact (hnzi x i).1 hi
  refine ⟨⟨ht, ?_⟩, fun x hx => ?_⟩
  · rw [← hproj]
    refine GlobalTheory.ProjSpace.toProj_eq_of_locally hs ht fun x => ?_
    obtain ⟨c, hc⟩ := exists_chart hL ((p' ≫ β' ≫ β) x)
    have m₁ : x ∈ (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β' ≫ β) (fun _ => (Sc.k : ℤ))) p').U
        (fun _ => fun _ => c) :=
      mem_pull.2 (Set.mem_iInter.2 fun _ => by simpa using hc)
    have m₂ : x ∈ (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β) (fun _ => (Sc.k : ℤ))) (p' ≫ β')).U
        (fun _ => fun _ => c) :=
      mem_pull.2 (Set.mem_iInter.2 fun _ => by simpa using hc)
    refine ⟨(LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β' ≫ β) (fun _ => (Sc.k : ℤ))) p').U (fun _ => fun _ => c) ⊓
      (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β) (fun _ => (Sc.k : ℤ))) (p' ≫ β')).U (fun _ => fun _ => c),
      ⟨m₁, m₂⟩, _, inf_le_left, _, inf_le_right, 1, fun j => ?_⟩
    rw [_root_.one_mul]
    refine fn_ext fun z hz => ?_
    have hz' : (p' ≫ β' ≫ β) z ∈ C.P.L.L.U c := by
      have := Set.mem_iInter.1 (mem_pull.1 hz.1) 0
      simpa using this
    obtain ⟨J, hJ, eJ⟩ := exists_good C.P.L.L hL z (fun _ : PUnit => p' ≫ β' ≫ β) (fun _ => c)
      (fun _ _ _ => rfl) (fun _ => hz')
    rw [gs_res _ _ _ hz, gs_res _ _ _ hz]
    refine (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull _ _) (σ j) (𝟙 _) z _ hz.2).trans
      (Eq.trans ?_ (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull _ _) (σ'' j) (𝟙 _) z _ hz.1).symm)
    rw [Category.id_comp, Category.id_comp]
    exact (sval_of (σ j) (p' ≫ β') z J (fun _ => c) (fun _ => by rw [Category.assoc]; exact eJ ⟨⟩)).symm.trans
      ((hv j _ _ _ _ hJ).symm.trans (sval_of (σ'' j) p' z J (fun _ => c) (fun _ => eJ ⟨⟩)))
  · have h₁ := hnz x hx
    choose J hJ using fun ψ : Sp Ω ⟶ C.G.left => exists_chart hL (ψ x)
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hvθ _ _ _ _ hJ] at h₁
    refine DVR.nonzeroLocus_secOfIso w θ₁ hw C'.P.L.isLB (LB.isLB_pull hL β) ?_
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hθ₁ _ _ _ _ hJ]
    exact h₁

end GlobalTheory.Mum.SecEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEmbHOfClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

theorem exists_trait_point {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (M : Modif R) (x : M.S)
    (hx : M.π x = closedPoint R) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
      GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x := by
  have : IsNoetherianRing R := hR.1.1
  have : CharZero R := hR.2
  have := M.proper
  have := M.integral
  have := M.dominant
  have : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (M.S.fromSpecStalk x ≫ M.π)
  have hψp : ∀ q : Spec (M.S.presheaf.stalk x), Spec.map ψ q = M.π (M.S.fromSpecStalk x q) := fun q => by
    rw [hψ, Scheme.Hom.comp_apply]
  have hloc : IsLocalHom ψ.hom := by
    rw [isLocalHom_iff_comap_closedPoint]
    have := hψp (closedPoint _)
    rw [Scheme.fromSpecStalk_closedPoint, hx] at this
    exact this

  let t₀ : Sp (FractionRing R) := closedPoint (FractionRing R)
  have hsp : M.gp t₀ ⤳ x := by
    rw [specializes_iff_mem_closure]
    have h1 : Set.range M.gp ⊆ {M.gp t₀} := by
      rintro _ ⟨t, rfl⟩
      rw [Subsingleton.elim t t₀]; rfl
    exact closure_mono h1 ((IsDominant.denseRange (f := M.gp)).closure_eq ▸ Set.mem_univ x)
  have hr : M.gp t₀ ∈ Set.range (M.S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hsp
  obtain ⟨q, hq⟩ := hr
  have e1 : Spec.map ψ q = jK R t₀ := by
    rw [hψp, hq, ← Scheme.Hom.comp_apply, M.gp_π]
  have h2 : Ideal.comap ψ.hom q.asIdeal = ⊥ := by
    have := congrArg (fun p : Sp R => (p : PrimeSpectrum R).asIdeal) e1
    change Ideal.comap ψ.hom q.asIdeal = Ideal.comap (algebraMap R (FractionRing R)) t₀.asIdeal at this
    rw [this, @Ideal.eq_bot_of_prime _ _ t₀.asIdeal t₀.isPrime]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
  have hinj : Function.Injective ψ.hom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap ψ.hom q.asIdeal := by
      rw [Ideal.mem_comap, ha]; exact q.asIdeal.zero_mem
    rw [h2] at this
    exact this
  have : CharZero (M.S.presheaf.stalk x) := charZero_of_injective_ringHom hinj
  have key : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (χ : M.S.presheaf.stalk x →+* W),
      GlobalTheory.LN.CDvr W ∧ Function.Injective χ ∧ IsLocalHom χ := by
    by_cases h : IsField (M.S.presheaf.stalk x)
    · letI := h.toField
      refine ⟨PowerSeries (M.S.presheaf.stalk x), inferInstance, inferInstance, inferInstance, PowerSeries.C,
        ⟨inferInstance, ?_, ?_⟩, PowerSeries.C_injective, inferInstance⟩
      · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
      · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := M.S.presheaf.stalk x)) (RingHom.injective _)
    · obtain ⟨O, _, _, _, _, χ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating _ h
      have : CharZero O := charZero_of_injective_ringHom h1
      exact ⟨O, inferInstance, inferInstance, inferInstance, χ, ⟨inferInstance, inferInstance, inferInstance⟩, h1, h2⟩
  obtain ⟨W, _, _, _, χ, hW, hχ, hχl⟩ := key
  refine ⟨W, inferInstance, inferInstance, inferInstance, χ.comp ψ.hom, Spec.map (CommRingCat.ofHom χ) ≫ M.S.fromSpecStalk x,
    hW, hχ.comp hinj, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]; rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x) (IsLocalRing.comap_closedPoint χ)) Scheme.fromSpecStalk_closedPoint)

end GlobalTheory.Mum.SecEmb

namespace GlobalTheory.Mum.SecEmb

theorem mem_embH_of_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    ∀ g : G.left, M.π (G.hom g) = closedPoint R → g ∈ GlobalTheory.Mum.SecEmb.embH s := by
  intro R _ _ _ hR M G _ _ B L _ _ N s θ Y _ _ j _ _ O hT g hg
  obtain ⟨W, _, _, _, φ, ξ, hW, hφ, hl, hξ, hξx⟩ := exists_trait_point hR M (G.hom g) hg
  obtain ⟨W', _, _, _, io, G', _, β, κ, e, hW', hio, hfin, hcart, -, -, hpts⟩ := hT W hW φ ξ hφ hl hξ
  have hiol : IsLocalHom io := by
    letI := io.toAlgebra
    have : Module.Finite W W' := hfin
    have : FaithfulSMul W W' := (faithfulSMul_iff_algebraMap_injective W W').2 hio
    exact (inferInstance : IsLocalHom (algebraMap W W'))
  have hc : (spMap io ≫ ξ) (closedPoint W') = G.hom g :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg ξ (IsLocalRing.comap_closedPoint io)).trans hξx)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap io ≫ ξ) g
    (closedPoint W') hc.symm
  have hg1 : β (hcart.1.isoPullback.inv z) = g := by
    rw [← Scheme.Hom.comp_apply, hcart.1.isoPullback_inv_fst, hz1]
  have hg2 : G'.hom (hcart.1.isoPullback.inv z) = closedPoint W' := by
    rw [← Scheme.Hom.comp_apply, hcart.1.isoPullback_inv_snd, hz2]
  obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := spMap (residue W'))
    (hcart.1.isoPullback.inv z) (closedPoint (ResidueField W'))
    (hg2.trans (IsLocalRing.comap_closedPoint (residue W')).symm)
  let F := ((Over.pullback (spMap (residue W'))).obj G').left
  let q' : F := q
  obtain ⟨⟨hs, -⟩, -⟩ := hpts (F.residueField q') (F.fromSpecResidueField q')
    (F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W')))
    (F.fromSpecResidueField q' ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ)) rfl rfl
  have hm : closedPoint (F.residueField q') ∈
      ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) ((F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β)) := by
    rw [hs]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  rw [GlobalTheory.nonzeroLocus_secPull] at hi
  have hpt : ((F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β)
      (closedPoint (F.residueField q')) = g := by
    have h1 : (F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) (closedPoint (F.residueField q')) =
        hcart.1.isoPullback.inv z :=
      (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg (pullback.fst G'.hom (spMap (residue W'))) (Scheme.fromSpecResidueField_apply q' _)).trans hq1)
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg β h1).trans hg1)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  rw [← hpt]
  exact hi

end GlobalTheory.Mum.SecEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailFurther
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem LabCover.exists_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (M' : Modif R) (h : M'.S ⟶ C.S), M'.gp ≫ h = C.gp → h ≫ C.π = M'.π → ∃ (C' : LabCover D) (eS : C'.S ≅ M'.S) (β : C'.G.left ⟶ C.G.left), eS.hom ≫ M'.π = C'.π ∧ IsGrpPullback C'.G C.G (eS.hom ≫ h) β ∧ LBIso C'.P.L.L (C.P.L.L.pull β) := by
  intro R _ _ _ D C M' h hgp hπ
  have hex : ∃ (P' : GlobalTheory.UU.CP ((Over.pullback h).obj C.G)) (w : _),
      GlobalTheory.UU.IsCPMap P' C.P h (pullback.fst C.G.hom h) pullback.condition w :=
    GlobalTheory.UU.exists_pull C.P (GlobalTheory.UU.toBase_mul_pullback C.G h)
  obtain ⟨P', w, hP⟩ := hex
  have hG : IsGrpPullback ((Over.pullback h).obj C.G) C.G h (pullback.fst C.G.hom h) := isGrpPullback_pullback C.G h
  have hw : LBIso P'.L.L (C.P.L.L.pull (pullback.fst C.G.hom h)) := ⟨w, hP.gen⟩

  have key : ∀ {Y : Scheme.{0}} (b : Y ⟶ ((Over.pullback h).obj C.G).left) (c : Y ⟶ C.G.left),
      c = b ≫ pullback.fst C.G.hom h → LBIso (P'.L.L.pull b) (C.P.L.L.pull c) := fun b c e =>
    LBIso.chartPull (chartPullId _) (GlobalTheory.RigidBundleGlue.chartPullComp C.P.L.L _ b c e)
      (GlobalTheory.RigidBundleGlue.LBIso.pull hw b)
  let α' : C.A.A.left ⟶ ((Over.pullback h).obj C.G).left :=
    pullback.lift C.α (C.A.A.hom ≫ M'.gp) (by rw [C.α_cart.1.w, Category.assoc, hgp])
  have hα : α' ≫ pullback.fst C.G.hom h = C.α := pullback.lift_fst _ _ _
  refine ⟨{ toModif := M'
            G := (Over.pullback h).obj C.G
            semi := IsSemiAbelian.pullback h C.G C.semi
            P := P'
            A := C.A
            α := α'
            α_cart := IsGrpPullback.cancel hG (C.α_cart.congr hgp.symm hα.symm) (pullback.lift_snd _ _ _)
            α_lb := LBIso.trans C.A.isLB (pull_isLB C.P.L.isLB _) (pull_isLB P'.L.isLB _) C.α_lb
              (LBIso.symm (key α' C.α hα.symm))
            n := C.n
            n_prime := C.n_prime
            n_odd := C.n_odd
            n_unit := C.n_unit
            lab := C.lab
            trait := ?_ }, Iso.refl _, pullback.fst C.G.hom h, Category.id_comp _,
      hG.congr (Category.id_comp _).symm rfl, hw⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G'', _, _, β, D', A', U', hD, hW', hio, hfin, hcart, hlb, hlab⟩ :=
    C.trait W hW φ (ξ ≫ h) hφ hloc (by rw [Category.assoc, hπ]; exact hξ)
  let β' : G''.left ⟶ ((Over.pullback h).obj C.G).left :=
    pullback.lift β (G''.hom ≫ spMap io ≫ ξ) (by rw [hcart.1.w, Category.assoc, Category.assoc])
  have hβ : β' ≫ pullback.fst C.G.hom h = β := pullback.lift_fst _ _ _
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G'', inferInstance, inferInstance, β', D', A', U', hD, hW',
    hio, hfin, IsGrpPullback.cancel hG (hcart.congr (Category.assoc _ _ _).symm hβ.symm) (pullback.lift_snd _ _ _),
    LBIso.trans U'.LG.isLB (pull_isLB C.P.L.isLB _) (pull_isLB P'.L.isLB _) hlb (LBIso.symm (key β' β hβ.symm)), ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
  refine hlab F em hF j p p₁ p' x' h₁ h₂ h₃ ?_
  have e := congrArg (· ≫ pullback.fst C.G.hom h) h₄
  simp only [Category.assoc, hβ, hα] at e
  simpa only [Category.assoc] using e

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreThetaEmbeddingOfSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.SecEmb.geometricallyIrreducible_of_smooth {X S : Scheme.{0}} (f : X ⟶ S) (hs : Smooth f)
    (hc : GeometricallyConnected f) : GeometricallyIrreducible f := by
  constructor
  intro K _ g Z fst snd h
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h hs
  have hcs := hc.geometrically_connectedSpace g fst snd h
  exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace K Z snd this hcs

theorem GlobalTheory.Mum.SecEmb.emb_of_traitRed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens), (O : Set Y.left).Nonempty →
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O → ∃ E : Emb M.π G, E.Theta L := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hi O hO hT
  have hH := GlobalTheory.Mum.SecEmb.mem_embH_of_closed R hR M G hG B L hB hL N s θ Y hY j hj hi O hT
  exact ⟨{ N := N
           H := GlobalTheory.Mum.SecEmb.embH s
           H_all := hH
           f := GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s
           f_over := GlobalTheory.ProjSpace.toProj_str _ _ _
           Y := Y
           smooth := hY
           j := j
           j_over := hj
           imm := hi
           fib := fun Ω _ x κ hx => GlobalTheory.Mum.SecEmb.Fib.fib R hR M G hG B L hB hL N s θ Y hY j hj hi O hT hH Ω x κ hx },
    θ, O, hO, fun g y hy hc hf => GlobalTheory.Mum.SecEmb.ThetaPt.mem_basicOpen_theta R hR M G hG B L hB hL N s θ Y hY j hj hi O hT g y hy hc hf⟩

namespace GlobalTheory.Mum.SecEmb

theorem agree_pull {X P Q : Scheme.{0}} (L : LB X) {hP : P ⟶ X} {hQ : Q ⟶ X} (g : Q ⟶ P) (e : g ≫ hP = hQ) {k : ℕ}
    (σ : SecK L hP k) : ∃ σ' : SecK L hQ k, ∀ {Y : Scheme.{0}} {h : Y ⟶ X} (s : SecK L h k), Agree L σ s → Agree L σ' s := by
  subst e
  refine ⟨ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec σ g, fun s hs Z p p' hp z J hJ => ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec σ g p z hJ]
  exact hs Z (p ≫ g) p' (by rw [Category.assoc]; exact hp) z J hJ

theorem traitReg_of_secs {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G]
    (L : LB G.left) {A : Scheme.{0}} (α : A ⟶ G.left) (Sc : Secs M G L α) :
    (∀ i, TraitReg M G L (Sc.s i)) ∧ TraitReg M G L Sc.θ := by
  constructor
  · intro i W _ _ _ hW φ ξ hinj hloc hξ
    obtain ⟨W', i1, i2, i3, io, G', iG', β, σ, θ', κ, e, hW', hio, hfin, hpb, -, -, hσ, -, -⟩ :=
      Sc.trait W hW φ ξ hinj hloc hξ
    obtain ⟨σ'', h''⟩ := agree_pull L hpb.1.isoPullback.inv hpb.1.isoPullback_inv_fst (σ i)
    exact ⟨W', i1, i2, i3, io, σ'', hW', hio, hfin, h'' _ (hσ i)⟩
  · intro W _ _ _ hW φ ξ hinj hloc hξ
    obtain ⟨W', i1, i2, i3, io, G', iG', β, σ, θ', κ, e, hW', hio, hfin, hpb, -, -, -, hθ, -⟩ :=
      Sc.trait W hW φ ξ hinj hloc hξ
    obtain ⟨σ'', h''⟩ := agree_pull L hpb.1.isoPullback.inv hpb.1.isoPullback_inv_fst θ'
    exact ⟨W', i1, i2, i3, io, σ'', hW', hio, hfin, h'' _ hθ⟩

theorem core : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C C' : LabCover D) (Sc : Secs C.toModif C.G C.P.L.L C.α) (h : C'.S ⟶ C.S) (β : C'.G.left ⟶ C.G.left),
    h ≫ C.π = C'.π → IsGrpPullback C'.G C.G h β → LBIso C'.P.L.L (C.P.L.L.pull β) →
    (∀ i, ∃ σ : SecK C.P.L.L β Sc.k, Agree C.P.L.L σ (Sc.s i)) → (∃ θ : SecK C.P.L.L β 1, Agree C.P.L.L θ Sc.θ) →
    ∃ E : Emb C'.π C'.G, E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C C' Sc h β hπ hpb hL hs hθ
  choose σ hσ using hs
  obtain ⟨θ₀, hθ₀⟩ := hθ
  obtain ⟨θ, hT⟩ := GlobalTheory.Mum.SecEmb.traitRed_cover R hR D C C' Sc h β hπ hpb hL σ hσ θ₀ hθ₀
  exact GlobalTheory.Mum.SecEmb.emb_of_traitRed R hR C'.toModif C'.G C'.semi _ C'.P.L.L (LB.isLB_linComb C.P.L.isLB _ _) C'.P.L.isLB Sc.N σ θ Sc.Y Sc.smooth
    Sc.j Sc.j_over Sc.imm Sc.O Sc.O_ne hT

theorem emb_of_secs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D), Nonempty (Secs C.toModif C.G C.P.L.L C.α) → ∃ (C' : LabCover D) (E : Emb C'.π C'.G), E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C ⟨Sc⟩
  have hR' := hR
  obtain ⟨⟨hN, -, -, -⟩, hc⟩ := hR'
  have hsemi := C.semi
  obtain ⟨hs, hθ⟩ := traitReg_of_secs C.toModif C.G C.P.L.L C.α Sc
  obtain ⟨M', h, -, hgp, hπ, hσ⟩ := GlobalTheory.Mum.extend_finiteModif R C.toModif C.G hsemi.smooth hsemi.quasiCompact
    (GlobalTheory.Mum.SecEmb.geometricallyIrreducible_of_smooth _ hsemi.smooth hsemi.geomConnected) C.P.L.L C.P.L.isLB C.A.A.left C.α C.A.A.hom C.α_cart.1
    (Option (Fin (Sc.N + 1))) (fun o => o.elim 1 (fun _ => Sc.k))
    (Option.rec (motive := fun o => SecK C.P.L.L C.α (o.elim 1 (fun _ => Sc.k))) Sc.θ Sc.s)
    (by rintro (_ | i); exacts [hθ, hs i])
  obtain ⟨C', eS, β, hπ', hpb, hL⟩ := GlobalTheory.Mum.LabCover.exists_pull R D C M' h hgp hπ
  have hw : β ≫ C.G.hom = (C'.G.hom ≫ eS.hom) ≫ h := by rw [Category.assoc]; exact hpb.1.w
  refine ⟨C', core R hR D C C' Sc (eS.hom ≫ h) β (by rw [Category.assoc, hπ, hπ']) hpb hL ?_ ?_⟩
  · intro i
    obtain ⟨σ, hσi⟩ := hσ (some i)
    obtain ⟨σ', h'⟩ := agree_pull C.P.L.L (pullback.lift β (C'.G.hom ≫ eS.hom) hw) (pullback.lift_fst _ _ _) σ
    exact ⟨σ', h' _ hσi⟩
  · obtain ⟨σ, hσi⟩ := hσ none
    obtain ⟨σ', h'⟩ := agree_pull C.P.L.L (pullback.lift β (C'.G.hom ≫ eS.hom) hw) (pullback.lift_fst _ _ _) σ
    exact ⟨σ', h' _ hσi⟩

end GlobalTheory.Mum.SecEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreThetaEmbeddingOfSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedFibre_theta_embedding_of_sections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), Nonempty (Secs C.toModif C.G C.P.L.L C.α) → ∃ (C' : LabCover D) (E : Emb C'.π C'.G), E.Theta C'.P.L.L := by
  first | exact @GlobalTheory.Mum.SecEmb.emb_of_secs | exact GlobalTheory.Mum.SecEmb.emb_of_secs | (intros; apply GlobalTheory.Mum.SecEmb.emb_of_secs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverEmbeddingClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_emb_of_labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')) (C' : LabCover D') (E : Emb C'.π C'.G), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C
  obtain ⟨R₁, i₁, i₂, i₃, ρ, D₁, C₁, hρ, hD, hS⟩ := GlobalTheory.T.exists_sections_prescribed_reduction_finite_ext R hR D C
  have := hR.2
  have h₁ : Base R₁ := ⟨hρ.1, (RingHom.charZero_iff hρ.2.1).1 this⟩
  obtain ⟨C', E, hE⟩ := GlobalTheory.T.exists_closedFibre_theta_embedding_of_sections R₁ h₁ D₁ C₁ hS
  exact ⟨R₁, i₁, i₂, i₃, ρ, D₁, C', E, hρ, hD, hE⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverEmbeddingClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelledCover_embedding_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')) (C' : LabCover D') (E : Emb C'.π C'.G), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ E.Theta C'.P.L.L := by
  first | exact @GlobalTheory.Mum.exists_emb_of_labCover | exact GlobalTheory.Mum.exists_emb_of_labCover | (intros; apply GlobalTheory.Mum.exists_emb_of_labCover <;> assumption)
end
