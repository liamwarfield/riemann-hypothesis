module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePullbackAffineFunctionEqQuotientConst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePullbackAffineFunctionEqQuotientConst
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory

theorem fibre_restrict_scalar_compat : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), ι ≫ p = q ≫ spMap (Ideal.Quotient.mk m) ≫ chart U → ∀ (V : Z.Opens) (hV : V ≤ p ⁻¹ᵁ U.1) (V' : A.Opens) (hV' : V' ≤ ι ⁻¹ᵁ V) (r : Γ(X, U.1)), (ι.appLE V V' hV').hom ((p.appLE U.1 V hV).hom r) = (q.appLE ⊤ V' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
  intro X Z p U m A q ι h V hV V' hV' r
  have hU : IsAffineOpen U.1 := U.2
  have e0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U.1 := by
    rw [hU.fromSpec_preimage_self]
  have e1 : ⊤ ≤ (chart U) ⁻¹ᵁ U.1 := e0
  have k0 : hU.fromSpec.appLE U.1 ⊤ e0 ≫ (Scheme.ΓSpecIso Γ(X, U.1)).hom = 𝟙 _ := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
      ← Functor.map_comp_assoc]
    have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e0).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  have k1 : ∀ x : Γ(X, U.1), ((chart U).appLE U.1 ⊤ e1).hom x = (Scheme.ΓSpecIso Γ(X, U.1)).inv.hom x := by
    intro x
    have := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso Γ(X, U.1)).inv).hom x) k0
    simp only [CommRingCat.comp_apply, CommRingCat.id_apply, Iso.hom_inv_id_apply] at this
    exact this
  have kt : (spMap (Ideal.Quotient.mk m)).appLE ⊤ ⊤ le_top = (spMap (Ideal.Quotient.mk m)).appTop := by
    dsimp only [Scheme.Hom.appLE]
    exact (congrArg _ ((Sp (Γ(X, U.1) ⧸ m)).presheaf.map_id (Opposite.op ⊤))).trans (Category.comp_id _)
  have k2 : ∀ x : Γ(X, U.1), ((spMap (Ideal.Quotient.mk m)).appLE ⊤ ⊤ le_top).hom
      ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m x) := by
    intro x
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk m))
    have := congrArg (fun f => f.hom x) hn
    simp only [CommRingCat.comp_apply] at this
    rw [kt]
    exact this.symm
  have hF : ⊤ ≤ (spMap (Ideal.Quotient.mk m) ≫ chart U) ⁻¹ᵁ U.1 :=
    (le_top : ⊤ ≤ spMap (Ideal.Quotient.mk m) ⁻¹ᵁ ⊤).trans
      ((TopologicalSpace.Opens.map (spMap (Ideal.Quotient.mk m)).base).map (homOfLE e1)).le
  have step : ∀ (g : A ⟶ X) (hg : g = q ≫ (spMap (Ideal.Quotient.mk m) ≫ chart U)) (e : V' ≤ g ⁻¹ᵁ U.1),
      (g.appLE U.1 V' e).hom r = (q.appLE ⊤ V' le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
    rintro g rfl e
    rw [← Scheme.Hom.appLE_comp_appLE q (spMap (Ideal.Quotient.mk m) ≫ chart U) U.1 ⊤ V' hF le_top,
      ← Scheme.Hom.appLE_comp_appLE (spMap (Ideal.Quotient.mk m)) (chart U) U.1 ⊤ ⊤ e1 le_top]
    simp only [CommRingCat.comp_apply]
    rw [k1, k2]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact step _ h _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePullbackAffineFunctionEqQuotientConstStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_pullback_affineFunction_eq_quotientConst : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), ι ≫ p = q ≫ spMap (Ideal.Quotient.mk m) ≫ chart U → ∀ (V : Z.Opens) (hV : V ≤ p ⁻¹ᵁ U.1) (V' : A.Opens) (hV' : V' ≤ ι ⁻¹ᵁ V) (r : Γ(X, U.1)), (ι.appLE V V' hV').hom ((p.appLE U.1 V hV).hom r) = (q.appLE ⊤ V' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
  first | exact @GlobalTheory.fibre_restrict_scalar_compat | exact GlobalTheory.fibre_restrict_scalar_compat | (intros; apply GlobalTheory.fibre_restrict_scalar_compat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreIsAbelianSchemeRelDimOfFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreIsAbelianSchemeRelDimOfFrame
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FibreAbDim

theorem exists_isLieBasis_of_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x φ) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left))
    (hv : ∀ a, IsTanAtG t x (v a))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin n → R, IsCombAtG t x v cf w) :
    ∃ v' : Fin n → (epsR R ⟶ G'), IsLieBasis v' := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _)
  have h1 : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left := by
    have := hσ 1
    rw [map_one] at this
    rw [this]
    congr 2
  have tan : ∀ w : epsR R ⟶ G', IsTangent w ↔ IsTanAtG t x (ρ w).left := by
    intro w
    constructor
    · intro hw
      refine ⟨Over.w (ρ w), ?_⟩
      rw [hρ, ← Category.assoc, hw, h1]
    · intro hw
      apply h.1.hom_ext
      · rw [Category.assoc, ← hρ, hw.2, h1]
      · rw [Category.assoc, Over.w w, Over.w η[G']]
        show spMap _ ≫ spMap _ = 𝟙 _
        unfold spMap
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
  let v' : Fin n → (epsR R ⟶ G') := fun a => ρ.symm (Over.homMk (v a) (hv a).1)
  have hv' : ∀ a, (v' a).left ≫ φ = v a := fun a => by
    rw [← hρ]
    simp [v']
  have comb : ∀ (c : Fin n → R) (w : epsR R ⟶ G'), IsLieComb c v' w ↔ IsCombAtG t x v c (ρ w).left := by
    intro c w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun i => ρ (u i), fun i => ?_, ?_⟩
      · rw [hρ, hu, Category.assoc, hv']
        rfl
      · rw [map_list_prod, List.map_ofFn]
        rfl
    · rintro ⟨u, hu, e⟩
      refine ⟨fun i => ρ.symm (u i), fun i => ?_, ?_⟩
      · apply h.1.hom_ext
        · rw [← hρ, MulEquiv.apply_symm_apply, hu, Category.assoc, hv']
          rfl
        · rw [Category.assoc, Over.w, Over.w]
          show spMap _ = spMap _ ≫ spMap _
          unfold spMap
          rw [← Spec.map_comp]
          congr 1
          ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
      · apply ρ.injective
        rw [map_list_prod, List.map_ofFn]
        refine (Over.OverMorphism.ext ?_)
        rw [← e]
        congr 3
        funext i
        exact (ρ.apply_symm_apply (u i)).symm
  refine ⟨v', fun a => (tan _).2 ?_, fun w hw => ?_⟩
  · rw [hρ, hv']
    exact hv a
  · simpa only [comb] using hb _ ((tan w).1 hw)

theorem isAbelianScheme_and_relDim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (j : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) j → IsAbelianScheme A ∧ SmoothOfRelativeDimension n A.hom := by
  intro E _ _ _ H X t hp U n v hv hb m hm A _ j hj
  have hG := GlobalTheory.HeckePoint.isAbelianScheme_of_proper t hp
  have pullAb : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
      [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left},
      IsAbelianScheme G → IsGrpPullback G' G f φ → IsAbelianScheme G' := by
    intro S S' f G G' _ _ φ hG h
    have := hG.comm
    have hc : IsCommMonObj G' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected⟩
  have hA := pullAb hG hj
  refine ⟨hA, ?_⟩
  have h₀ := isGrpPullback_pullback t.G (chart U)
  have hG' := pullAb hG h₀
  obtain ⟨v', hv'⟩ := exists_isLieBasis_of_frame t (chart U) h₀ v hv hb
  have w : j ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U := by
    rw [hj.1.w, Category.assoc]
  have h₁ := IsGrpPullback.cancel h₀ (hj.congr rfl (h₀.1.lift_fst _ _ w).symm) (h₀.1.lift_snd _ _ w)
  have := hG'.comm
  have := hA.comm
  have := hG.comm
  obtain ⟨v₁, hv₁, -⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ _ _ A _ h₁ hG'.smooth n v' hv'
  have : IsLocalRing (Γ(X, U.1) ⧸ m) := by
    letI := Ideal.Quotient.field m
    infer_instance
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim _ A hA
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.KeyPow.exists_isLieBasis A hg
  rw [GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis hj hv₁ hv₂]
  exact hg

end GlobalTheory.FibreAbDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreIsAbelianSchemeRelDimOfFrameStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_isAbelianScheme_relDim_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → IsAbelianScheme A ∧ SmoothOfRelativeDimension n A.hom := by
  first | exact @GlobalTheory.FibreAbDim.isAbelianScheme_and_relDim | exact GlobalTheory.FibreAbDim.isAbelianScheme_and_relDim | (intros; apply GlobalTheory.FibreAbDim.isAbelianScheme_and_relDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleCoboundaryOfCoveringSubfamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleCoboundaryOfCoveringSubfamily
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.CechCobGlue

theorem resG_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) a = _
  rw [← Functor.map_comp]
  rfl

theorem cocycle_coboundary_of_subcover : ∀ (Y : Scheme.{0}) (J : Type) (W : J → Y.Opens) (κ : Type) (σ : κ → J), ⨆ k, W (σ k) = ⊤ → ∀ (E : ∀ i i' : J, Γ(Y, W i ⊓ W i')), (∀ i i' i'', resG Y (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (E i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (E i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (E i i'')) → ∀ (h' : ∀ k, Γ(Y, W (σ k))), (∀ k k', E (σ k) (σ k') = resG Y inf_le_left (h' k) - resG Y inf_le_right (h' k')) → ∃ h : ∀ i, Γ(Y, W i), ∀ i i', E i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  intro Y J W κ σ hcov E hE h' hh'
  have hcovi : ∀ i, W i ≤ ⨆ k, (W i ⊓ W (σ k)) := by
    intro i x hx
    have hx' : x ∈ (⨆ k, W (σ k)) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  let f : ∀ i k, Γ(Y, W i ⊓ W (σ k)) := fun i k => E i (σ k) + resG Y inf_le_right (h' k)
  have hf : ∀ i k k', resG Y (inf_le_left : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k)) (f i k)
      = resG Y (inf_le_right : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k')) (f i k') := by
    intro i k k'
    have hPT : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k) ⊓ W (σ k') :=
      le_inf inf_le_left (inf_le_right.trans inf_le_right)
    have e1 := congrArg (resG Y hPT) (hE i (σ k) (σ k'))
    have e2 := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W (σ k) ⊓ W (σ k'))) (hh' k k')
    simp only [map_add (f := _), map_sub, resG_comp] at e1 e2
    simp only [f, map_add (f := _), resG_comp]
    linear_combination e1 - e2
  have hg : ∀ i, ∃ s : Γ(Y, W i), ∀ k, resG Y (inf_le_left : W i ⊓ W (σ k) ≤ W i) s = f i k := by
    intro i
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun k => W i ⊓ W (σ k)) (W i)
      (fun k => homOfLE (inf_le_left : W i ⊓ W (σ k) ≤ W i)) (hcovi i) (fun k => f i k)
      (fun k k' => hf i k k')
    exact ⟨s, hs⟩
  choose h hh using hg
  refine ⟨h, fun i i' => ?_⟩
  have hcov2 : W i ⊓ W i' ≤ ⨆ k, (W i ⊓ W i' ⊓ W (σ k)) := by
    intro x hx
    have hx' : x ∈ (⨆ k, W (σ k)) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  apply Y.sheaf.eq_of_locally_eq' (fun k => W i ⊓ W i' ⊓ W (σ k)) (W i ⊓ W i')
    (fun k => homOfLE (inf_le_left : W i ⊓ W i' ⊓ W (σ k) ≤ W i ⊓ W i')) hcov2
  intro k
  show resG Y inf_le_left (E i i') = resG Y inf_le_left (resG Y inf_le_left (h i) - resG Y inf_le_right (h i'))
  have A := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    W i ⊓ W i' ⊓ W (σ k) ≤ W i ⊓ W (σ k))) (hh i k)
  have B := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
    W i ⊓ W i' ⊓ W (σ k) ≤ W i' ⊓ W (σ k))) (hh i' k)
  have C := hE i i' (σ k)
  simp only [f, map_add (f := _), resG_comp] at A B
  simp only [map_sub, resG_comp]
  linear_combination C - A + B

end GlobalTheory.CechCobGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleCoboundaryOfCoveringSubfamilyStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_coboundary_of_coveringSubfamily : ∀ (Y : Scheme.{0}) (J : Type) (W : J → Y.Opens) (κ : Type) (σ : κ → J), ⨆ k, W (σ k) = ⊤ → ∀ (E : ∀ i i' : J, Γ(Y, W i ⊓ W i')), (∀ i i' i'', resG Y (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (E i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (E i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (E i i'')) → ∀ (h' : ∀ k, Γ(Y, W (σ k))), (∀ k k', E (σ k) (σ k') = resG Y inf_le_left (h' k) - resG Y inf_le_right (h' k')) → ∃ h : ∀ i, Γ(Y, W i), ∀ i i', E i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  first | exact @GlobalTheory.CechCobGlue.cocycle_coboundary_of_subcover | exact GlobalTheory.CechCobGlue.cocycle_coboundary_of_subcover | (intros; apply GlobalTheory.CechCobGlue.cocycle_coboundary_of_subcover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1TrivialBundleRankBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1TrivialBundleRankBound
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbCoh.FDimField

theorem cechLB_triv_finite_finrank_one_le : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Module.Finite K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ∧ Module.finrank K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ≤ g := by
  intro K _ A _ g hA hsm κ _ _ D hD hcov
  let L := AlgebraicClosure K
  let f : Sp L ⟶ Sp K := spMap (algebraMap K L)
  let A' : Over (Sp L) := (Over.pullback f).obj A
  let π : A'.left ⟶ A.left := pullback.fst A.hom f
  have hGP : IsGrpPullback A' A (spMap (algebraMap K L)) π := isGrpPullback_pullback A f
  have H : IsPullback π A'.hom A.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) := hGP.1
  obtain ⟨hA', hg'⟩ :=
    GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback (algebraMap K L) A A' π g hGP hA hsm
  haveI := hA.proper
  haveI := GlobalTheory.isAffineHom_diagonal_of_isSeparated A.hom
  have hDs := GlobalTheory.isAffineOpen_finset_biInf hD
  let D' : κ → A'.left.Opens := fun i => π ⁻¹ᵁ D i
  have hD' : ∀ i, IsAffineOpen (D' i) := fun i => GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback H (hD i)
  have hcov' : ⨆ i, D' i = ⊤ := by
    show ⨆ i, π ⁻¹ᵁ D i = ⊤
    rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  obtain ⟨hfin', hrank', -⟩ :=
    GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two L A' g hA' hg' κ D' hD' hcov'

  obtain ⟨c, hc⟩ := (GlobalTheory.CechPic.iso_triv_iff (LB.triv A.left)).1 ((GlobalTheory.CechPic.setoid A.left).iseqv.refl ⟨LB.triv A.left, LB.isLB_triv A.left⟩)
  obtain ⟨w, hw⟩ := (GlobalTheory.CechPic.iso_triv_iff ((LB.triv A.left).pull π)).2
    ⟨LB.genPull (LB.triv A.left) c π, LB.isGen_genPull (LB.triv A.left) c hc π⟩
  let C := GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D
  obtain ⟨e₃⟩ := GlobalTheory.FieldChangeInter.nonempty_homology_equiv L C 1
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ 1).mapIso
    (GlobalTheory.AbLaw.cechLBBaseChangeIso (LB.isLB_triv A.left) H (fun s hs => hDs s hs))).toLinearEquiv
  have e₅ := (HomologicalComplex.homologyMapIso
    (GlobalTheory.AbLaw.cechLBCongr A'.hom D' (LB.isLB_triv A'.left) (LB.isLB_pull (LB.isLB_triv A.left) π) w hw) 1).toLinearEquiv
  let E : (L ⊗[K] C.homology 1) ≃ₗ[L] (GlobalTheory.AbLaw.cechLB A'.hom (LB.triv A'.left) D').homology 1 :=
    e₃.symm ≪≫ₗ e₄ ≪≫ₗ e₅.symm
  haveI := hfin' 1
  haveI : Module.Finite L (L ⊗[K] C.homology 1) := Module.Finite.equiv E.symm
  have hfinK : Module.Finite K (C.homology 1) := by
    have h1 : Module.rank L (L ⊗[K] C.homology 1) < Cardinal.aleph0 := Module.rank_lt_aleph0 L _
    rw [Module.rank_baseChange, Cardinal.lift_id] at h1
    exact Module.rank_lt_aleph0_iff.1 h1
  refine ⟨hfinK, le_of_eq ?_⟩
  rw [← Module.finrank_baseChange (R := L), E.finrank_eq]
  exact hrank'

end GlobalTheory.AbCoh.FDimField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1TrivialBundleRankBoundStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_cech_h1_trivial_bundle_rank_bound : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Module.Finite K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ∧ Module.finrank K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ≤ g := by
  first | exact @GlobalTheory.AbCoh.FDimField.cechLB_triv_finite_finrank_one_le | exact GlobalTheory.AbCoh.FDimField.cechLB_triv_finite_finrank_one_le | (intros; apply GlobalTheory.AbCoh.FDimField.cechLB_triv_finite_finrank_one_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyDimensionBoundCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyDimensionBoundCocycles
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrdCechDep

open GlobalTheory GlobalTheory.AbLaw

variable {K : Type} [Field K] {Y : Scheme.{0}} (s : Y ⟶ Sp K)

abbrev ch (V : Y.Opens) : SecOnR s (LB.triv Y) V ≃ₗ[Γ(Y, V)] Γ(Y, V) :=
  SecOnR.chart s (LB.isLB_triv Y) PUnit.unit le_top

theorem ch_restrict {U V : Y.Opens} (h : V ≤ U) (x : SecOnR s (LB.triv Y) U) :
    ch s V (SecOnR.restrict s (LB.triv Y) h x) = resG Y h (ch s U x) :=
  SecOn.chart_restrict (LB.isLB_triv Y) PUnit.unit le_top h x

theorem ch_smul (V : Y.Opens) (r : K) (x : SecOnR s (LB.triv Y) V) :
    ch s V (r • x) = cst s V r * ch s V x := by
  rw [SecOnR.smul_def, LinearEquiv.map_smul]
  rfl

theorem resG_eq_zero {U V : Y.Opens} (e : U = V) (h : V ≤ U) (x : Γ(Y, U)) (hx : resG Y h x = 0) :
    x = 0 := by
  subst e
  simpa using hx

section Coc

variable {κ : Type} [LinearOrder κ] (D : κ → Y.Opens)

theorem biInf_pair_le {t : Finset κ} {a c : κ} (ha : a ∈ t) (hc : c ∈ t) :
    ⨅ j ∈ t, D j ≤ D a ⊓ D c :=
  le_inf (biInf_le _ ha) (biInf_le _ hc)

theorem ne_two (t : {t : Finset κ // t.card = 1 + 1}) : t.1.Nonempty :=
  Finset.card_pos.1 (by rw [t.2]; norm_num)

def coc (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) : Cube.Term (secCube s (LB.triv Y) D) (1 + 1) :=
  fun t => (ch s (⨅ j ∈ t.1, D j)).symm
    (resG Y (biInf_pair_le D (t.1.min'_mem (ne_two t)) (t.1.max'_mem (ne_two t))) (e _ _))

theorem resG_e_congr (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) {a a' c c' : κ} (ha : a = a') (hc : c = c')
    {V : Y.Opens} (h : V ≤ D a ⊓ D c) (h' : V ≤ D a' ⊓ D c') :
    resG Y h (e a c) = resG Y h' (e a' c') := by
  subst ha hc; rfl

theorem coc_pair (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) {i i' : κ} (hii : i < i')
    (t : {t : Finset κ // t.card = 1 + 1}) (ht : t.1 = {i, i'}) :
    ch s _ (coc s D e t) = resG Y (biInf_pair_le D (by simp [ht]) (by simp [ht])) (e i i') := by
  have hmin : t.1.min' (ne_two t) = i := by
    refine le_antisymm (Finset.min'_le _ _ (by simp [ht])) (Finset.le_min' _ _ _ ?_)
    intro y hy
    rw [ht] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact le_rfl
    · exact hii.le
  have hmax : t.1.max' (ne_two t) = i' := by
    refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp [ht]))
    intro y hy
    rw [ht] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hii.le
    · exact le_rfl
  unfold coc
  rw [LinearEquiv.apply_symm_apply]
  exact resG_e_congr D e hmin hmax _ _

end Coc

section Tri

variable {κ : Type} [LinearOrder κ] (D : κ → Y.Opens)

def IsCoc (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) : Prop :=
  ∀ i i' i'', resG Y (inf_le_left : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i') (e i i') +
    resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i' ⊓ D i'')
      (e i' i'') =
    resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i'')
      (e i i'')

theorem ch_d (p : ℕ) (x : Cube.Term (secCube s (LB.triv Y) D) p)
    (t : {t : Finset κ // t.card = p + 1}) :
    ch s (⨅ j ∈ t.1, D j) (Cube.d (secCube s (LB.triv Y) D) p x t) =
      ∑ i : t.1, cubeSign t.1 i.1 • resG Y (iInf_le_iInf_of_subset D (Finset.erase_subset i.1 t.1))
        (ch s (⨅ j ∈ (Cube.eraseIdx t i).1, D j) (x (Cube.eraseIdx t i))) := by
  rw [Cube.d_apply]
  show ch s _ (∑ i : t.1, cubeSign t.1 i.1 • (SecOnR.restrict s (LB.triv Y)
    (iInf_le_iInf_of_subset D (Finset.erase_subset i.1 t.1)) (x (Cube.eraseIdx t i)) :
      SecOnR s (LB.triv Y) (⨅ j ∈ t.1, D j))) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  exact ch_restrict s _ _

theorem coc_tri (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) (he : IsCoc D e) {a b c : κ} (hab : a < b)
    (hbc : b < c) (t : {t : Finset κ // t.card = 1 + 1 + 1}) (ht : t.1 = {a, b, c}) :
    Cube.d (secCube s (LB.triv Y) D) (1 + 1) (coc s D e) t = 0 := by
  have hac := hab.trans hbc
  have ha : a ∈ t.1 := by simp [ht]
  have hb : b ∈ t.1 := by simp [ht]
  have hc : c ∈ t.1 := by simp [ht]
  have ea : t.1.erase a = {b, c} := by
    rw [ht]; exact Finset.erase_insert (by simp [hab.ne, hac.ne])
  have eb : t.1.erase b = {a, c} := by
    rw [ht, Finset.erase_insert_of_ne hab.ne, Finset.erase_insert (by simp [hbc.ne])]
  have ec : t.1.erase c = {a, b} := by
    rw [ht]
    ext i
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, h' | h' | h'⟩
      · exact Or.inl h'
      · exact Or.inr h'
      · exact (h h').elim
    · rintro (rfl | rfl)
      · exact ⟨hac.ne, Or.inl rfl⟩
      · exact ⟨hbc.ne, Or.inr (Or.inl rfl)⟩
  have sa : cubeSign t.1 a = 1 := cubeSign_eq_one_of_forall_le (by
    rw [ht]; simp [hab.le, hac.le])
  have sbc : cubeSign ({b, c} : Finset κ) b = 1 := cubeSign_eq_one_of_forall_le (by simp [hbc.le])
  have sb : cubeSign t.1 b = -1 := by
    have := cubeSign_erase_of_lt ha hab
    rw [ea, sbc] at this
    omega
  have scc : cubeSign ({b, c} : Finset κ) c = -1 := by
    have := cubeSign_erase_of_lt (t := ({b, c} : Finset κ)) (by simp) hbc
    rw [Finset.erase_insert (by simp [hbc.ne]), cubeSign_singleton] at this
    omega
  have sc : cubeSign t.1 c = 1 := by
    have := cubeSign_erase_of_lt ha hac
    rw [ea, scc] at this
    omega
  have hu : (Finset.univ : Finset t.1) = {⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩} := by
    ext ⟨i, hi⟩
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
    rw [ht] at hi
    simpa using hi
  refine (ch s (⨅ j ∈ t.1, D j)).map_eq_zero_iff.1 ?_
  rw [ch_d, hu, Finset.sum_insert (by simp [hab.ne, hac.ne]),
    Finset.sum_pair (by simp [hbc.ne])]
  rw [coc_pair s D e hbc _ ea, coc_pair s D e hac _ eb, coc_pair s D e hab _ ec, sa, sb, sc]
  have hV : ⨅ j ∈ t.1, D j ≤ D a ⊓ D b ⊓ D c :=
    le_inf (le_inf (biInf_le _ ha) (biInf_le _ hb)) (biInf_le _ hc)
  have h' := congrArg (resG Y hV) (he a b c)
  simp only [map_add (f := _), resG_resG] at h' ⊢
  rw [one_smul, one_smul, neg_smul, one_smul]
  linear_combination h'

end Tri

section Main

variable {κ : Type} [LinearOrder κ] (D : κ → Y.Opens)

theorem coc_mem (e : ∀ i i' : κ, Γ(Y, D i ⊓ D i')) (he : IsCoc D e) :
    coc s D e ∈ LinearMap.ker (Cube.d (secCube s (LB.triv Y) D) (1 + 1)) := by
  rw [LinearMap.mem_ker]
  funext t
  have h3 : t.1.card = 3 := t.2
  let f := t.1.orderEmbOfFin h3
  have ht : t.1 = {f 0, f 1, f 2} := by
    ext j
    constructor
    · intro hj
      have : j ∈ Set.range f := by rw [Finset.range_orderEmbOfFin]; exact hj
      obtain ⟨k, rfl⟩ := this
      fin_cases k <;> simp
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem _ _ _
  exact coc_tri s D e he (f.strictMono (by decide)) (f.strictMono (by decide)) t ht

theorem resG_inj {U V : Y.Opens} (e : U = V) (h : V ≤ U) {x x' : Γ(Y, U)}
    (hx : resG Y h x = resG Y h x') : x = x' := by
  subst e
  simpa using hx

theorem single_le (i : κ) : D i ≤ ⨅ j ∈ ({i} : Finset κ), D j := by simp

theorem ch_sum_smul {ι : Type} [Fintype ι] (c : ι → K)
    (x : ι → Cube.Term (secCube s (LB.triv Y) D) (1 + 1)) (t : {t : Finset κ // t.card = 1 + 1}) :
    ch s (⨅ j ∈ t.1, D j) ((∑ b, c b • x b) t) = ∑ b, AbLaw.cst s (⨅ j ∈ t.1, D j) (c b) * ch s _ (x b t) := by
  rw [Finset.sum_apply]
  have key : ∀ v : ι → SecOnR s (LB.triv Y) (⨅ j ∈ t.1, D j),
      ch s _ (∑ b, c b • v b) = ∑ b, AbLaw.cst s (⨅ j ∈ t.1, D j) (c b) * ch s _ (v b) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => ch_smul s _ _ _
  exact key fun b => x b t

end Main

section Pair

variable {κ : Type} [LinearOrder κ] (D : κ → Y.Opens)

def hh (y : Cube.Term (secCube s (LB.triv Y) D) (0 + 1)) (i : κ) : Γ(Y, D i) :=
  - resG Y (single_le D i) (ch s _ (y ⟨{i}, Finset.card_singleton i⟩))

theorem y_congr (y : Cube.Term (secCube s (LB.triv Y) D) (0 + 1)) {u u' : {t : Finset κ // t.card = 0 + 1}}
    (h : u.1 = u'.1) {V : Y.Opens} (hV : V ≤ ⨅ j ∈ u.1, D j) (hV' : V ≤ ⨅ j ∈ u'.1, D j) :
    resG Y hV (ch s _ (y u)) = resG Y hV' (ch s _ (y u')) := by
  obtain rfl : u = u' := Subtype.ext h
  rfl

theorem resG_cst {U V : Y.Opens} (h : V ≤ U) (r : K) :
    resG Y h (AbLaw.cst s U r) = AbLaw.cst s V r :=
  rs_cst s h r

theorem pair_lt {ι : Type} [Fintype ι] (e : ι → ∀ i i' : κ, Γ(Y, D i ⊓ D i')) (c : ι → K)
    (y : Cube.Term (secCube s (LB.triv Y) D) (0 + 1))
    (hy : Cube.d (secCube s (LB.triv Y) D) (0 + 1) y = ∑ b, c b • coc s D (e b)) {i i' : κ}
    (hii : i < i') :
    ∑ b, AbLaw.cst s (D i ⊓ D i') (c b) * e b i i' =
      resG Y inf_le_left (hh s D y i) - resG Y inf_le_right (hh s D y i') := by
  let t : {t : Finset κ // t.card = 0 + 1 + 1} := ⟨{i, i'}, Finset.card_pair hii.ne⟩
  have hW : D i ⊓ D i' = ⨅ j ∈ t.1, D j := by
    show D i ⊓ D i' = ⨅ j ∈ ({i, i'} : Finset κ), D j
    rw [Finset.iInf_insert, Finset.iInf_singleton]
  have hi : i ∈ t.1 := by simp [t]
  have hi' : i' ∈ t.1 := by simp [t]
  have hle : ⨅ j ∈ t.1, D j ≤ D i ⊓ D i' := biInf_pair_le D hi hi'
  apply resG_inj hW hle
  have key : ch s (⨅ j ∈ t.1, D j) (Cube.d (secCube s (LB.triv Y) D) (0 + 1) y t) =
      ch s (⨅ j ∈ t.1, D j) ((∑ b, c b • coc s D (e b)) t) := by rw [hy]
  rw [ch_d, ch_sum_smul] at key
  have hu : (Finset.univ : Finset t.1) = {⟨i, hi⟩, ⟨i', hi'⟩} := by
    ext ⟨j, hj⟩
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
    simpa [t] using hj
  rw [hu, Finset.sum_pair (by simp [hii.ne])] at key
  have si : cubeSign t.1 i = 1 := cubeSign_eq_one_of_forall_le (by simp [t, hii.le])
  have si' : cubeSign t.1 i' = -1 := by
    have := cubeSign_erase_of_lt (t := t.1) hi hii
    have e1 : t.1.erase i = {i'} := Finset.erase_insert (by simp [hii.ne])
    rw [e1, cubeSign_singleton] at this
    omega
  have ei : (Cube.eraseIdx t ⟨i, hi⟩).1 = ({i'} : Finset κ) := Finset.erase_insert (by simp [hii.ne])
  have ei' : (Cube.eraseIdx t ⟨i', hi'⟩).1 = ({i} : Finset κ) := by
    show ({i, i'} : Finset κ).erase i' = {i}
    rw [Finset.erase_insert_of_ne hii.ne, Finset.erase_singleton]
    simp
  rw [y_congr s D y (u' := ⟨{i'}, Finset.card_singleton i'⟩) ei _
      ((single_le D i').trans' (hle.trans inf_le_right)),
    y_congr s D y (u' := ⟨{i}, Finset.card_singleton i⟩) ei' _
      ((single_le D i).trans' (hle.trans inf_le_left)), si, si'] at key
  have hc : ∀ b, ch s (⨅ j ∈ t.1, D j) (coc s D (e b) t) = resG Y hle (e b i i') :=
    fun b => coc_pair s D (e b) hii t rfl
  simp only [hc] at key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hh, map_sum, map_mul, map_sub, map_neg, resG_resG, resG_cst]
  rw [one_smul, neg_smul, one_smul] at key
  linear_combination -key

end Pair

theorem exists_comb_coboundary : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (s : Y ⟶ Sp K) (g : ℕ) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), Module.Finite K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) → Module.finrank K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) ≤ g → ∀ (e : Fin (g + 1) → ∀ i i' : κ, Γ(Y, D i ⊓ D i')), (∀ b i i' i'', resG Y (inf_le_left : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i') (e b i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i' ⊓ D i'') (e b i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i'') (e b i i'')) → ∃ c : Fin (g + 1) → K, c ≠ 0 ∧ ∃ h : ∀ i, Γ(Y, D i), ∀ i i', ∑ b, (s.appLE ⊤ (D i ⊓ D i') le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  intro K _ Y s g κ _ _ D hfin hrank e he
  classical
  let A := secCube s (LB.triv Y) D
  let z : Fin (g + 1) → LinearMap.ker (Cube.d A (1 + 1)) :=
    fun b => ⟨coc s D (e b), coc_mem s D (e b) (he b)⟩
  haveI : Module.Finite K ((cechComplex A).homology 1) := hfin
  have hnli : ¬ LinearIndependent K (fun b => cechClass A 1 (z b)) := by
    intro hli
    have h1 := hli.fintype_card_le_finrank
    have h2 : Module.finrank K ((cechComplex A).homology 1) ≤ g := hrank
    simp only [Fintype.card_fin] at h1
    omega
  obtain ⟨c, hc, b0, hb0⟩ := Fintype.not_linearIndependent_iff.1 hnli
  have h0 : cechClass A 1 (∑ b, c b • z b) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simpa only [map_smul] using hc
  obtain ⟨y, hy⟩ := (cechClass_succ_eq_zero_iff A 0 _).1 h0
  have hy' : Cube.d A (0 + 1) y = ∑ b, c b • coc s D (e b) := by
    rw [hy]
    simp [z]
  refine ⟨c, fun h => hb0 (by simp [h]), hh s D y, ?_⟩
  have hdiag : ∀ b i, e b i i = 0 := by
    intro b i
    have h := he b i i i
    have h' : resG Y (inf_le_left : D i ⊓ D i ⊓ D i ≤ D i ⊓ D i) (e b i i) = 0 := add_eq_right.1 h
    exact resG_eq_zero (by simp) _ _ h'
  intro i i'
  show ∑ b, AbLaw.cst s (D i ⊓ D i') (c b) * e b i i' = _
  rcases lt_trichotomy i i' with h | rfl | h
  · exact pair_lt s D e c y hy' h
  · simp [hdiag]
  · have P := pair_lt s D e c y hy' h
    have hanti : ∀ b, resG Y (inf_le_left : D i ⊓ D i' ⊓ D i ≤ D i ⊓ D i') (e b i i') =
        - resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          D i ⊓ D i' ⊓ D i ≤ D i' ⊓ D i) (e b i' i) := by
      intro b
      have h1 := he b i i' i
      rw [hdiag, map_zero] at h1
      exact eq_neg_of_add_eq_zero_left h1
    have hW : D i ⊓ D i' = D i ⊓ D i' ⊓ D i := by
      refine le_antisymm (le_inf le_rfl inf_le_left) inf_le_left
    apply resG_inj hW inf_le_left
    have P' := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      D i ⊓ D i' ⊓ D i ≤ D i' ⊓ D i)) P
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_sub, resG_cst, resG_resG] at P' ⊢
    simp only [hanti, mul_neg, Finset.sum_neg_distrib]
    linear_combination -P'

end GlobalTheory.OrdCechDep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyDimensionBoundCocyclesStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_first_cohomology_dimension_bound_cocycles : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (s : Y ⟶ Sp K) (g : ℕ) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), Module.Finite K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) → Module.finrank K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) ≤ g → ∀ (e : Fin (g + 1) → ∀ i i' : κ, Γ(Y, D i ⊓ D i')), (∀ b i i' i'', resG Y (inf_le_left : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i') (e b i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i' ⊓ D i'') (e b i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i'') (e b i i'')) → ∃ c : Fin (g + 1) → K, c ≠ 0 ∧ ∃ h : ∀ i, Γ(Y, D i), ∀ i i', ∑ b, (s.appLE ⊤ (D i ⊓ D i') le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  first | exact @GlobalTheory.OrdCechDep.exists_comb_coboundary | exact GlobalTheory.OrdCechDep.exists_comb_coboundary | (intros; apply GlobalTheory.OrdCechDep.exists_comb_coboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageQuotientFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageQuotientFibre
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.AffinePreimageFibre

theorem isPullback_comp_mono {C : Type*} [Category C] {A B T : C} (f : A ⟶ B) (c : B ⟶ T) [Mono c] :
    IsPullback f (𝟙 A) c (f ≫ c) :=
  IsPullback.of_isLimit' ⟨by simp⟩
    (PullbackCone.IsLimit.mk _ (fun s => s.snd)
      (fun s => by
        rw [← cancel_mono c]
        simp only [Category.assoc]
        exact s.condition.symm)
      (fun s => by simp)
      (fun s m _ h2 => by simpa using h2))

theorem isAffineOpen_preimage_fibre : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), IsPullback ι q p (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ W : Z.Opens, IsAffineOpen W → W ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (ι ⁻¹ᵁ W) := by
  intro X Z p U m A q ι H W hW hWU
  haveI : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  let h : (W : Scheme) ⟶ Sp Γ(X, U.1) := p.resLE U.1 W hWU ≫ U.2.isoSpec.hom
  have hh : W.ι ≫ p = h ≫ chart U := by
    simp [h, chart, IsAffineOpen.fromSpec]
  have big := (isPullback_morphismRestrict ι W).paste_vert H
  rw [hh] at big
  have comm : (ι ∣_ W) ≫ h = ((ι ⁻¹ᵁ W).ι ≫ q) ≫ spMap (Ideal.Quotient.mk m) := by
    rw [← cancel_mono (chart U)]
    simpa [Category.assoc] using big.w
  have sq : IsPullback (ι ∣_ W) ((ι ⁻¹ᵁ W).ι ≫ q) h (spMap (Ideal.Quotient.mk m)) :=
    IsPullback.of_bot (v₂₁ := 𝟙 _) (by simpa using big) comm (isPullback_comp_mono _ _)
  haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk m)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsAffineHom (ι ∣_ W) := MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip inferInstance
  haveI : IsAffine (W : Scheme) := hW
  exact isAffine_of_isAffineHom (ι ∣_ W)

end GlobalTheory.AffinePreimageFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageQuotientFibreStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_quotientFibre : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), IsPullback ι q p (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ W : Z.Opens, IsAffineOpen W → W ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (ι ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre | exact GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre | (intros; apply GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocyclesCombinationCoefficientNon
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.FibreH1

theorem resG_appLE {Y : Scheme.{0}} {K : Type} [CommRing K] (s : Y ⟶ Sp K) {V V' : Y.Opens} (h : V' ≤ V)
    (x : Γ(Sp K, ⊤)) : resG Y h ((s.appLE ⊤ V le_top).hom x) = (s.appLE ⊤ V' le_top).hom x := by
  exact congrArg (fun φ : Γ(Sp K, ⊤) ⟶ Γ(Y, V') => φ.hom x)
    (Scheme.Hom.appLE_map s (U := ⊤) le_top (homOfLE h).op)

theorem fieldDep : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (J : Type) (W : J → A.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = ⊤ → ∀ (e : Fin (g + 1) → ∀ i i' : J, Γ(A.left, W i ⊓ W i')), (∀ b i i' i'', resG A.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e b i i'')) → ∃ c : Fin (g + 1) → K, c ≠ 0 ∧ ∃ h : ∀ i, Γ(A.left, W i), ∀ i i', ∑ b, (A.hom.appLE ⊤ (W i ⊓ W i') le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i' = resG A.left inf_le_left (h i) - resG A.left inf_le_right (h i') := by
  intro K _ A _ g hA hsm J W hW hcov e he
  haveI := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i => (W i : Set A.left))
    (fun i => (W i).isOpen) (by
      intro x _
      have hx : x ∈ (⨆ i, W i) := by rw [hcov]; trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      exact Set.mem_iUnion.2 hx)
  let σ : Fin t.card → J := fun k => (t.equivFin.symm k).1
  have hσ : ⨆ k, W (σ k) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨t.equivFin ⟨i, hi⟩, by simpa [σ] using hx⟩
  obtain ⟨hfin, hrk⟩ := GlobalTheory.T.abelian_cech_h1_trivial_bundle_rank_bound K A g hA hsm (Fin t.card) (fun k => W (σ k)) (fun k => hW _) hσ
  obtain ⟨c, hc, h', hh'⟩ := GlobalTheory.T.cech_first_cohomology_dimension_bound_cocycles K A.left A.hom g (Fin t.card) (fun k => W (σ k)) hfin hrk
    (fun b k k' => e b (σ k) (σ k')) (fun b k k' k'' => he b _ _ _)
  refine ⟨c, hc, ?_⟩
  exact GlobalTheory.T.cechCocycle_coboundary_of_coveringSubfamily A.left J W (Fin t.card) σ hσ
    (fun i i' => ∑ b, (A.hom.appLE ⊤ (W i ⊓ W i') le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i') (by
      intro i i' i''
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, resG_appLE]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_add, he b]) h' hh'

theorem fibre_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (e : Fin (n + 1) → ∀ i i' : J, Γ(A.left, ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')), (∀ b, (∀ i i' i'', resG A.left (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') (e b i i''))) → ∃ r : Fin (n + 1) → Γ(X, U.1), (∃ b, r b ∉ m) ∧ ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', ∑ b, (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b)) * e b i i' = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  intro E _ _ _ H X t hprop hamp U n v hv huniq J W hWa hcov hWU m hm A _ ι hpb e he
  letI : Field (Γ(X, U.1) ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hA, hsm⟩ := GlobalTheory.T.closedFibre_isAbelianScheme_relDim_of_frame E H X t hprop U n v hv huniq m hm A ι hpb
  have hsq := hpb.1
  have hw : ι ≫ t.G.hom = A.hom ≫ spMap (Ideal.Quotient.mk m) ≫ chart U := hsq.w
  have htop : ⨆ i, ι ⁻¹ᵁ W i = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : t.G.hom.base (ι.base x) ∈ (U.1 : Set X) := by
      change (ι ≫ t.G.hom).base x ∈ _
      rw [hw, ← U.2.range_fromSpec]
      exact ⟨_, rfl⟩
    have hx' : ι.base x ∈ (⨆ i, W i) := by rw [hcov]; exact hx
    rw [TopologicalSpace.Opens.mem_iSup] at hx' ⊢
    exact hx'
  have haff : ∀ i, IsAffineOpen (ι ⁻¹ᵁ W i) := fun i =>
    GlobalTheory.T.isAffineOpen_preimage_quotientFibre X t.G.left t.G.hom U m A.left A.hom ι hsq (W i) (hWa i) (hWU i)
  obtain ⟨c, hc, h, hh⟩ := fieldDep (Γ(X, U.1) ⧸ m) A n hA hsm J (fun i => ι ⁻¹ᵁ W i) haff htop e he
  choose r hr using fun b => Ideal.Quotient.mk_surjective (c b)
  refine ⟨r, ?_, h, fun i i' => ?_⟩
  · obtain ⟨b, hb⟩ := Function.ne_iff.1 hc
    refine ⟨b, fun hmem => hb ?_⟩
    rw [← hr b]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
  · rw [← hh i i']
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.T.fibre_pullback_affineFunction_eq_quotientConst X t.G.left t.G.hom U m A.left A.hom ι hw (W i ⊓ W i') (inf_le_left.trans (hWU i))
      (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx), hr b]

end GlobalTheory.FibreH1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocyclesCombinationCoefficientNonStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_fibre_cechCocycles_combination_coefficient_nonunit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (e : Fin (n + 1) → ∀ i i' : J, Γ(A.left, ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')), (∀ b, (∀ i i' i'', resG A.left (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') (e b i i''))) → ∃ r : Fin (n + 1) → Γ(X, U.1), (∃ b, r b ∉ m) ∧ ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', ∑ b, (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b)) * e b i i' = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  first | exact @GlobalTheory.FibreH1.fibre_dim | exact GlobalTheory.FibreH1.fibre_dim | (intros; apply GlobalTheory.FibreH1.fibre_dim <;> assumption)
end
