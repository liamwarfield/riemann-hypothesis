module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EssFiniteTypeOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiNegativeDescendsFieldExtensionCurveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem act_val_frac : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : D'.X) (y₀ : D₀.X) (g : GtPtF D' F) (g' : GtPtF D₀ F), GtPtF.IsIota y g → GtPtF.IsIota y₀ g' → Act D' D₀ pr h g g' → ∀ (χ : D₀.X) (u : LB.Gen (CmpLB D' D₀ pr (h χ) χ)), Nrm u → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → val (D₀.tau y₀ χ) (𝟙 _) z (rr J) = val (D'.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D'.c y)) z J := by
  intro R _ _ D₀ D' pr h F _ _ y y₀ g g' hg hg' ha χ u hu z J hJ
  have hsurj : Surjective (jFK (R := R) F) := GlobalTheory.Balanced.surjective_spMap _
  have hflat : Flat (jFK (R := R) F) := (inferInstance : Flat (spMap (algebraMap (FractionRing R) F)))
  have hb : g.b.left = jFK (R := R) F ≫ ptK (D'.c y) := by
    rw [hg.1]
    have e : toUnit (TF (R := R) F) = (Over.homMk (jFK (R := R) F) rfl : TF (R := R) F ⟶ TK R) ≫ toUnit (TK R) :=
      toUnit_unique _ _
    show (toUnit (TF (R := R) F) ≫ D'.c y).left = _
    rw [e, Category.assoc, Over.comp_left]
    rfl

  have step1 : ∀ (z' : (TF (R := R) F).left) (J' : _), Good (JN D' D₀) z' J' →
      val (D₀.tau y₀ χ) (jFK (R := R) F) z' (rr J') =
        val (D'.tau y (h χ)) (jFK (R := R) F) z' (rl J') * val u (jFK (R := R) F ≫ ptK (D'.c y)) z' J' := by
    intro z' J' hJ'
    have g₀ := (isPart_inr D'.P.L D₀.P.L).good hJ'
    have g₁ := (isPart_inl D'.P.L D₀.P.L).good hJ'
    have e := ha.2 χ u hu z' J' hJ'
    rw [val_corr g₀ (hg'.2 χ), val_corr g₁ (hg.2 (h χ)), val_pull g₀, val_pull g₁, hb] at e
    simp only [Category.id_comp] at e
    exact e

  have p₀ := isPart_inr D'.P.L D₀.P.L
  have p₁ := isPart_inl D'.P.L D₀.P.L
  let t₀ := p₀.gen (D₀.tau y₀ χ)
  let t₂ := LB.mulGen (JN D' D₀) _ _ _ _ (p₁.gen (D'.tau y (h χ))) (LB.pullGen (JN D' D₀) _ _ u (ptK (D'.c y)))
  have key := GlobalTheory.Balanced.val_descend (jn_isLB D' D₀) t₀ t₂ (jFK (R := R) F) (fun z' J' hJ' => by
    rw [p₀.val_gen _ _ _ hJ', val_mul hJ', p₁.val_gen _ _ _ hJ', val_pull hJ']
    exact step1 z' J' hJ') z J hJ
  rw [p₀.val_gen _ _ _ hJ, val_mul hJ, p₁.val_gen _ _ _ hJ, val_pull hJ, Category.id_comp] at key
  exact key

end GlobalTheory.Mum.Two

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFielStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPointAction_period_value_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : D'.X) (y₀ : D₀.X) (g : GtPtF D' F) (g' : GtPtF D₀ F), GtPtF.IsIota y g → GtPtF.IsIota y₀ g' → Act D' D₀ pr h g g' → ∀ (χ : D₀.X) (u : LB.Gen (CmpLB D' D₀ pr (h χ) χ)), Nrm u → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → val (D₀.tau y₀ χ) (𝟙 _) z (rr J) = val (D'.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D'.c y)) z J := by
  first | exact @GlobalTheory.Mum.Two.act_val_frac | exact GlobalTheory.Mum.Two.act_val_frac | (intros; apply GlobalTheory.Mum.Two.act_val_frac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGlue

theorem hom_ext_of_geometric {Z P S : Scheme.{0}} [IsReduced Z] (q : P ⟶ S) [IsSeparated q] (a b : Z ⟶ P)
    (hq : a ≫ q = b ≫ q)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ Z), y ≫ a = y ≫ b) : a = b := by
  let T : Z → Scheme.{0} := fun z => Sp (AlgebraicClosure (Z.residueField z))
  let pt : ∀ z, T z ⟶ Z := fun z =>
    spMap (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z))) ≫ Z.fromSpecResidueField z
  let m : (∐ T) ⟶ Z := Sigma.desc pt
  have hs : Function.Surjective m.base := by
    intro z
    refine ⟨(Sigma.ι T z).base default, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    simp only [pt, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have : IsDominant m := ⟨hs.denseRange⟩
  refine ext_of_isDominant_of_isSeparated q hq m ?_
  refine Sigma.hom_ext _ _ fun z => ?_
  simp only [m, Sigma.ι_desc_assoc]
  exact h _ (pt z)

theorem glue_geom : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp o) (I : Type)
    (W : I → X.Opens) (f : ∀ i, (W i).toScheme ⟶ PSpace o n), (⨆ i, W i) = ⊤ →
    (∀ i, f i ≫ PSpace.str o n = (W i).ι ≫ s) →
    (∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme),
      y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ f i = y' ≫ f j) →
    ∃ g : X ⟶ PSpace o n, g ≫ PSpace.str o n = s ∧ ∀ i, (W i).ι ≫ g = f i := by
  intro o _ n X _ s I W f hW hf hg
  have : IsSeparated (PSpace.str o n) := by
    have := isProper_str o n
    infer_instance
  let 𝒰 := X.openCoverOfIsOpenCover W hW
  have hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ f a = pullback.snd (W a).ι (W b).ι ≫ f b := by
    intro a b
    have : IsReduced (pullback (W a).ι (W b).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)
    refine hom_ext_of_geometric (PSpace.str o n) _ _ ?_ fun K _ _ y => ?_
    · rw [Category.assoc, Category.assoc, hf, hf, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      exact hg a b K _ _ (by rw [Category.assoc, Category.assoc, pullback.condition])
  have he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms f hc = f a := fun a => 𝒰.ι_glueMorphisms f hc a
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun (a : I) => ?_, he⟩
  change (W a).ι ≫ _ = (W a).ι ≫ _
  rw [← Category.assoc, he, hf]

end GlobalTheory.ThetaGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_projectiveSpace_maps_of_agree_geometric_points : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp o) (I : Type) (W : I → X.Opens) (f : ∀ i, (W i).toScheme ⟶ PSpace o n), (⨆ i, W i) = ⊤ → (∀ i, f i ≫ PSpace.str o n = (W i).ι ≫ s) → (∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme), y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ f i = y' ≫ f j) → ∃ g : X ⟶ PSpace o n, g ≫ PSpace.str o n = s ∧ ∀ i, (W i).ι ≫ g = f i := by
  first | exact @GlobalTheory.ThetaGlue.glue_geom | exact GlobalTheory.ThetaGlue.glue_geom | (intros; apply GlobalTheory.ThetaGlue.glue_geom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianLieSeminegativeOfNeron
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusExtendsSemiabelian
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NeronCurve

theorem exists_torus_hom_extension : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
    ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i₀ : splitTorus (Sp K) X ⟶ (Over.pullback x).obj G) [IsMonHom i₀],
    ∃ (i : splitTorus C X ⟶ G) (ψ : (splitTorus (Sp K) X).left ⟶ (splitTorus C X).left), IsMonHom i ∧
      IsGrpPullback (splitTorus (Sp K) X) (splitTorus C X) x ψ ∧ ψ ≫ i.left = i₀.left ≫ pullback.fst G.hom x := by
  intro k _ C _ hC K _ x hx G _ hG X _ _ _ i₀ _
  obtain ⟨hs, -, hc⟩ := hC
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  have : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  have hN : Geo.Tor.IsNormalScheme C :=
    GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension (Sp k) C (strHom k C) 1
      (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec k)
  obtain ⟨hxd, hxp⟩ := hx
  have hj : IsGenericPointHom x := IsGenericPointHom.of_isPreimmersion x
  have hT := GlobalTheory.Diag.isSemiAbelian C X
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian (splitTorus C X) hT
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  have := hT.quasiCompact
  have := hG.smooth
  have hφ := GlobalTheory.Diag.isGrpPullback X x
  obtain ⟨V, hV, -, g, hg, w, h₁, h₂⟩ :=
    spread_hom_generic_of_isGrpPullback hj hφ (isGrpPullback_pullback G x) i₀
  have : IsDominant V.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact V.isOpen.dense ⟨_, hV⟩⟩
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.homExtNormal C V V.ι hN inferInstance inferInstance (splitTorus C X) G hT hG g hg
  refine ⟨F, _, hF, hφ, ?_⟩
  rw [← h₂, ← hF', GlobalTheory.ExtUnique.pullback_map_left_fst, ← h₁]
  exact Category.assoc _ _ _

end GlobalTheory.NeronCurve
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NeronCurve.LieDescent

theorem semiNeg_of_iso {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] {F F' : C.Modules} (e : F ≅ F')
    (h : SemiNeg k F) : SemiNeg k F' := fun W r hW i _ =>
  h W r hW (i ≫ e.inv) (mono_comp i e.inv)

def lieBaseIso {C C' : Scheme.{0}} [IsIntegral C] (π : C' ⟶ C) (G : Over C) [GrpObj G] [IsSemiAbelian G] :
    (Scheme.Modules.pullback π).obj (Lie G) ≅ Lie ((Over.pullback π).obj G) :=
  have h := isGrpPullback_pullback G π
  have hg := (exists_isVB_of_isSemiAbelian G).choose_spec.1
  have := isIso_lieBase h hg
  asIso (lieBase h)

end GlobalTheory.NeronCurve.LieDescent

namespace GlobalTheory.NeronCurve

end GlobalTheory.NeronCurve
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyStructureSheafIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyStructureSheafIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem lid_baseChange_self {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (f : M →ₗ[K] N) (x : K ⊗[K] M) :
    TensorProduct.lid K N (f.baseChange K x) = f (TensorProduct.lid K M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem nonempty_equiv_homology_of_baseChange_self {K : Type} [Field K]
    (S : ShortComplex (ModuleCat.{0} K)) {H : Type} [AddCommGroup H] [Module K H]
    (θ : LinearMap.ker (S.g.hom.baseChange K) →ₗ[K] H) (hs : Function.Surjective θ)
    (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (S.f.hom.baseChange K)) :
    Nonempty (H ≃ₗ[K] S.homology) := by
  have hmem : ∀ x : LinearMap.ker S.g.hom,
      (TensorProduct.lid K S.X₂).symm x.1 ∈ LinearMap.ker (S.g.hom.baseChange K) := by
    intro x
    rw [LinearMap.mem_ker]
    apply (TensorProduct.lid K S.X₃).injective
    rw [lid_baseChange_self, LinearEquiv.apply_symm_apply, map_zero]
    exact x.2
  let q : LinearMap.ker S.g.hom →ₗ[K] H :=
    θ ∘ₗ ((((TensorProduct.lid K S.X₂).symm : S.X₂ →ₗ[K] K ⊗[K] S.X₂) ∘ₗ
      (LinearMap.ker S.g.hom).subtype).codRestrict _ hmem)
  have hq : ∀ x, q x = θ ⟨(TensorProduct.lid K S.X₂).symm x.1, hmem x⟩ := fun x => rfl
  have hsurj : Function.Surjective q := by
    intro h
    obtain ⟨z, rfl⟩ := hs h
    have hz : TensorProduct.lid K S.X₂ z.1 ∈ LinearMap.ker S.g.hom := by
      rw [LinearMap.mem_ker, ← lid_baseChange_self, z.2, map_zero]
    refine ⟨⟨_, hz⟩, ?_⟩
    rw [hq]
    congr 1
    exact Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  have hker : LinearMap.range S.moduleCatToCycles = LinearMap.ker q := by
    ext x
    rw [LinearMap.mem_ker, hq, hk]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(TensorProduct.lid K S.X₁).symm y, ?_⟩
      apply (TensorProduct.lid K S.X₂).injective
      rw [lid_baseChange_self, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨TensorProduct.lid K S.X₁ y, Subtype.ext ?_⟩
      have := congrArg (TensorProduct.lid K S.X₂) hy
      rw [lid_baseChange_self, LinearEquiv.apply_symm_apply] at this
      exact this
  exact ⟨((q.quotKerEquivOfSurjective hsurj).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ
    S.moduleCatHomologyIso.toLinearEquiv.symm)⟩

theorem hO_equiv_cech : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (κ : Type) [LinearOrder κ]
    [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
    Nonempty (HO1 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 1) ∧
      Nonempty (HO2 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 2) := by
  intro K _ X s κ _ _ D hsep haff hcov
  obtain ⟨M⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology K X s κ D hsep haff hcov
  have hsp : spMap (algebraMap K K) = 𝟙 (Sp K) := by
    rw [Algebra.algebraMap_self]; exact Spec.map_id _
  have hP : IsPullback (𝟙 X) s s (spMap (algebraMap K K)) := by
    rw [hsp]; exact IsPullback.id_horiz s
  obtain ⟨h1s, h1k, h2s, h2k⟩ := M.exact hP
  obtain ⟨e1⟩ := nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 0 1 2) (M.θ1 hP) h1s h1k
  obtain ⟨e2⟩ := nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 1 2 3) (M.θ2 hP) h2s h2k
  exact ⟨⟨e1 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 0 1 2 (by simp) (by simp)).toLinearEquiv.symm⟩,
    ⟨e2 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 1 2 3 (by simp) (by simp)).toLinearEquiv.symm⟩⟩

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyStructureSheafIsoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_structure_sheaf_iso : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Nonempty (HO1 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 1) ∧ Nonempty (HO2 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 2) := by
  first | exact @GlobalTheory.AbCoh.hO_equiv_cech | exact GlobalTheory.AbCoh.hO_equiv_cech | (intros; apply GlobalTheory.AbCoh.hO_equiv_cech <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPrincipallyPolarisedAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPrincipallyPolarisedAbelianScheme
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SumPol

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.PolProd

theorem exists_isPullback_restrict {X Y Z S : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (P : IsPullback p q f g) (h : Z ⟶ S) (hh : p ≫ f = h) (U : S.Opens) :
    ∃ (p' : (h ⁻¹ᵁ U).toScheme ⟶ (f ⁻¹ᵁ U).toScheme) (q' : (h ⁻¹ᵁ U).toScheme ⟶ (g ⁻¹ᵁ U).toScheme),
      p' ≫ (f ⁻¹ᵁ U).ι = (h ⁻¹ᵁ U).ι ≫ p ∧ q' ≫ (g ⁻¹ᵁ U).ι = (h ⁻¹ᵁ U).ι ≫ q ∧
        IsPullback p' q' (f ∣_ U) (g ∣_ U) := by
  have Hf := isPullback_morphismRestrict f U
  have Hg := isPullback_morphismRestrict g U
  have Hh := isPullback_morphismRestrict h U
  have w₁ : (h ∣_ U) ≫ U.ι = ((h ⁻¹ᵁ U).ι ≫ p) ≫ f := by rw [Category.assoc, hh, Hh.w]
  have w₂ : (h ∣_ U) ≫ U.ι = ((h ⁻¹ᵁ U).ι ≫ q) ≫ g := by rw [Category.assoc, ← P.w, hh, Hh.w]
  refine ⟨Hf.lift _ _ w₁, Hg.lift _ _ w₂, Hf.lift_snd _ _ _, Hg.lift_snd _ _ _, ?_⟩
  have A : IsPullback (Hf.lift _ _ w₁) (h ⁻¹ᵁ U).ι (f ⁻¹ᵁ U).ι p := by
    refine IsPullback.of_right ?_ (Hf.lift_snd _ _ _) Hf
    rw [Hf.lift_fst, hh]
    exact Hh
  have B := A.paste_vert P
  refine IsPullback.of_bot ?_ (by rw [Hf.lift_fst, Hg.lift_fst]) Hg
  rw [Hg.lift_snd, Hf.w]
  exact B

theorem relAmple_prod {S : Scheme.{0}} (A B : Over S) [IsProper A.hom] [IsProper B.hom] [IsProper (A ⊗ B).hom]
    {L : LB A.left} {M : LB B.left} {N : LB (A ⊗ B).left} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (e : cls N hN = pull (fst A B).left (cls L hL) + pull (snd A B).left (cls M hM))
    (aL : RelAmple A L) (aM : RelAmple B M) : RelAmple (A ⊗ B) N := by
  refine (relAmple_iff_isAmpleLB _ hN).2 fun U hU => ?_
  obtain ⟨p', q', hp, hq, H⟩ := exists_isPullback_restrict (p := (fst A B).left) (q := (snd A B).left)
    (f := A.hom) (g := B.hom) (IsPullback.of_hasPullback _ _) (A ⊗ B).hom (Over.w _) U
  have : IsAffine U := hU
  have h₀ := pull_isLB hN ((A ⊗ B).hom ⁻¹ᵁ U).ι
  have h₁ := pull_isLB (pull_isLB hL (A.hom ⁻¹ᵁ U).ι) p'
  have h₂ := pull_isLB (pull_isLB hM (B.hom ⁻¹ᵁ U).ι) q'
  refine IsAmpleLB.box ((relAmple_iff_isAmpleLB _ hL).1 aL U hU) ((relAmple_iff_isAmpleLB _ hM).1 aM U hU) h₀ H
    ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div h₀ h₁) h₂)).1 ?_)
  rw [cls_div (LB.isLB_div h₀ h₁) h₂, cls_div h₀ h₁, cls_pull hN, e, cls_pull (pull_isLB hL _), cls_pull hL,
    cls_pull (pull_isLB hM _), cls_pull hM, map_add, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, hp, hq]
  abel

theorem exists_sum_polAV : ∀ (S : Scheme.{0}) (P₁ P₂ : PolAV S), ∃ (P : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A), IsSumPolAV P P₁ P₂ a₁ a₂ ∧ P.L = extLB P₁.L P₂.L a₁.left a₂.left := by
  intro S P P'
  have hB : IsAbelianScheme (P.A ⊗ P'.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb
  let p := fst P.A P'.A
  let q := snd P.A P'.A
  let M : LB (P.A ⊗ P'.A).left := extLB P.L P'.L p.left q.left
  have hM : M.IsLB := isLB_tens (pull_isLB P.isLB p.left) (pull_isLB P'.isLB q.left)
  have eM : cls M hM = pull p.left (cls P.L P.isLB) + pull q.left (cls P'.L P'.isLB) := rfl
  haveI := P.isAb.proper
  haveI := P'.isAb.proper
  haveI := hB.proper
  have hdim : SmoothOfRelativeDimension (P.g + P'.g) (P.A ⊗ P'.A).hom := by
    haveI := P.smoothDim
    haveI : SmoothOfRelativeDimension P'.g (pullback.fst P.A.hom P'.A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip P'.smoothDim
    rw [add_comm]
    exact inferInstanceAs (SmoothOfRelativeDimension (P'.g + P.g) (pullback.fst P.A.hom P'.A.hom ≫ P.A.hom))
  have hrig : Rigidified (P.A ⊗ P'.A) M := by
    rw [rigidified_iff _ hM, eM, map_add (f := _), ← pull_comp, ← pull_comp, eSec_comp p, eSec_comp q,
      (rigidified_iff _ P.isLB).1 P.rigid, (rigidified_iff _ P'.isLB).1 P'.rigid, add_zero]
  have hsym : Out.Sym (P.A ⊗ P'.A) M := by
    have h₁ := ((sym_iff _ P.isLB).1 P.sym).pull_over (π' := (P.A ⊗ P'.A).hom) p.left (Over.w p)
    have h₂ := ((sym_iff _ P'.isLB).1 P'.sym).pull_over (π' := (P.A ⊗ P'.A).hom) q.left (Over.w q)
    rw [sym_iff _ hM, eM]
    convert locZero_add h₁ h₂ using 1
    rw [map_add (f := _), map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, inv_comp_left p,
      inv_comp_left q]
    abel
  refine ⟨⟨P.A ⊗ P'.A, hB, P.g + P'.g, hdim, M, hM, hrig, hsym,
    relAmple_prod _ _ P.isLB P'.isLB hM eM P.ample P'.ample,
    kTriv_prod hM P.isLB P'.isLB eM P.ktriv P'.ktriv⟩, p, q,
    ⟨inferInstance, inferInstance, ?_, PolBaseChange.lbIso_refl hM⟩, rfl⟩
  show IsIso (lift (fst P.A P'.A) (snd P.A P'.A))
  rw [lift_fst_snd]
  infer_instance

end GlobalTheory.MumProd.SumPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPrincipallyPolarisedAbelianSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_product_principallyPolarised_abelianScheme : ∀ (S : Scheme.{0}) (P₁ P₂ : PolAV S), ∃ (P : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A), IsSumPolAV P P₁ P₂ a₁ a₂ ∧ P.L = extLB P₁.L P₂.L a₁.left a₂.left := by
  first | exact @GlobalTheory.MumProd.SumPol.exists_sum_polAV | exact GlobalTheory.MumProd.SumPol.exists_sum_polAV | (intros; apply GlobalTheory.MumProd.SumPol.exists_sum_polAV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativeTransitionUnitsIsoLineBundles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativeTransitionUnitsIsoLineBundles
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem dlog_of_mul_eq {B : Type} [CommRing B] (a₁ a₂ l g : DualNumber B) (i₁ i₂ il ig : B)
    (h : a₁ * l = g * a₂) (h₁ : a₁.fst * i₁ = 1) (h₂ : a₂.fst * i₂ = 1) (hl : l.fst * il = 1)
    (hg : g.fst * ig = 1) : g.snd * ig = l.snd * il + (a₁.snd * i₁ - a₂.snd * i₂) := by
  have h0 : a₁.fst * l.fst = g.fst * a₂.fst := by simpa using congrArg TrivSqZeroExt.fst h
  have h1 : a₁.fst * l.snd + a₁.snd * l.fst = g.fst * a₂.snd + g.snd * a₂.fst := by
    have := congrArg TrivSqZeroExt.snd h
    rwa [DualNumber.snd_mul, DualNumber.snd_mul] at this
  have e1 : a₁.fst * ig * i₂ = il := by
    linear_combination (ig * i₂ * il) * h0 - (a₁.fst * ig * i₂) * hl + (a₂.fst * i₂ * il) * hg + il * h₂
  have e2 : l.fst * ig * i₂ = i₁ := by
    linear_combination (ig * i₂ * i₁) * h0 - (l.fst * ig * i₂) * h₁ + (a₂.fst * i₂ * i₁) * hg + i₁ * h₂
  linear_combination (-(ig * i₂)) * h1 + l.snd * e1 + a₁.snd * e2 - (a₂.snd * i₂) * hg - (g.snd * ig) * h₂

theorem valR_fst_mul_inv {Y : Scheme.{0}} {B : Type} [CommRing B] {x : Sp B ⟶ Y} {w : Sp (DualNumber B) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) (u : Γ(Y, O)ˣ) :
    (valR w O u.val).fst * valR x O u⁻¹.val = 1 := by
  have h' := le_preimage_of_red hw h
  subst hw
  have e : (valR w O u.val).fst = ev _ O h u.val := by
    rw [valR_eq_ev _ _ h', GlobalTheory.FlagMod.ev_spMap _ w O h']
    rfl
  rw [e, valR_eq_ev _ _ h, ← map_mul, Units.mul_inv, map_one]

theorem valR_iso_compat {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M)
    (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {S : Type} [CommRing S] (z : Sp S ⟶ Y)
    (h₁ : ⊤ ≤ z ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ z ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))) :
    valR z _ (wg.s (p₁, fun _ => j₁)).val * valR (z ≫ m) _ (L.g j₁ j₂).val =
      valR z _ (M.g p₁ p₂).val * valR z _ (wg.s (p₂, fun _ => j₂)).val := by
  have e := hwg (p₁, fun _ => j₁) (p₂, fun _ => j₂)
  have hz := GlobalTheory.FlagMod.le_preimage_inf h₁ h₂
  have hP : ⊤ ≤ z ⁻¹ᵁ ((L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂)) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_right h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_right h₂)
  have hM : ⊤ ≤ z ⁻¹ᵁ (M.U p₁ ⊓ M.U p₂) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₂)
  have hle : (L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂) ≤ m ⁻¹ᵁ (L.U j₁ ⊓ L.U j₂) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₁) PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₂) PUnit.unit))
  have hg : (L.pull m).g (fun _ => j₁) (fun _ => j₂) = res hle (pullU m _ (L.g j₁ j₂)) := by
    show ∏ _k : PUnit, (res hle (pullU m _ (L.g j₁ j₂))) ^ (1 : ℤ) = _
    simp
  have hl : valR (z ≫ m) _ (L.g j₁ j₂).val = valR z _ ((L.pull m).g (fun _ => j₁) (fun _ => j₂)).val := by
    rw [hg, valR_comp_app]
    exact (valR_resG z hle hP _).symm
  rw [hl]
  have hle₁ : (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) ⊓ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) ≤ M.U p₁ ⊓ M.U p₂ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have hle₂ : (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) ⊓ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) ≤
      (L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂) :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have e' : res (U := M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) inf_le_left (wg.s (p₁, fun _ => j₁)) =
      res hle₁ (M.g p₁ p₂) * (res hle₂ ((L.pull m).g (fun _ => j₁) (fun _ => j₂)))⁻¹ *
        res (U := M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) inf_le_right (wg.s (p₂, fun _ => j₂)) := e
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq] at e'
  have e2 := congrArg (fun u : Γ(Y, _)ˣ => ev z _ hz u.val) e'
  simp only [Units.val_mul, map_mul] at e2
  rw [← valR_eq_ev, ← valR_eq_ev, ← valR_eq_ev, ← valR_eq_ev] at e2
  exact (congrArg₂ (· * ·) (valR_resG z _ hz _) (valR_resG z _ hz _)).symm.trans
    (e2.trans (congrArg₂ (· * ·) (valR_resG z _ hz _) (valR_resG z _ hz _)))

theorem dlog_transition_iso : ∀ {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M) (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {B : Type} [CommRing B] (x : Sp B ⟶ Y) (w : Sp (DualNumber B) ⟶ Y) (hwx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) (h₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))), (valR w _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val = (valR (w ≫ m) _ (L.g j₁ j₂).val).snd * valR (x ≫ m) _ (L.g j₁ j₂)⁻¹.val + ((valR w _ (wg.s (p₁, fun _ => j₁)).val).snd * valR x _ (wg.s (p₁, fun _ => j₁))⁻¹.val - (valR w _ (wg.s (p₂, fun _ => j₂)).val).snd * valR x _ (wg.s (p₂, fun _ => j₂))⁻¹.val) := by
  intro Y Z m L M wg hwg j₁ j₂ p₁ p₂ B _ x w hwx h₁ h₂
  have hM : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ M.U p₂) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₂)
  have hL : ⊤ ≤ (x ≫ m) ⁻¹ᵁ (L.U j₁ ⊓ L.U j₂) :=
    GlobalTheory.FlagMod.le_preimage_inf
      (GlobalTheory.FlagMod.le_preimage_map m
        (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₁) PUnit.unit)) h₁)
      (GlobalTheory.FlagMod.le_preimage_map m
        (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₂) PUnit.unit)) h₂)
  have hwm : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (w ≫ m) = x ≫ m := by
    rw [← Category.assoc, hwx]
  exact dlog_of_mul_eq _ _ _ _ _ _ _ _
    (valR_iso_compat m L M wg hwg j₁ j₂ p₁ p₂ w (le_preimage_of_red hwx h₁) (le_preimage_of_red hwx h₂))
    (valR_fst_mul_inv hwx h₁ _) (valR_fst_mul_inv hwx h₂ _) (valR_fst_mul_inv hwm hL _) (valR_fst_mul_inv hwx hM _)

end GlobalTheory.CechKS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativeTransitionUnitsIsoLineBundlesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDerivative_transitionUnits_isoLineBundles : ∀ {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M) (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {B : Type} [CommRing B] (x : Sp B ⟶ Y) (w : Sp (DualNumber B) ⟶ Y) (hwx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) (h₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))), (valR w _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val = (valR (w ≫ m) _ (L.g j₁ j₂).val).snd * valR (x ≫ m) _ (L.g j₁ j₂)⁻¹.val + ((valR w _ (wg.s (p₁, fun _ => j₁)).val).snd * valR x _ (wg.s (p₁, fun _ => j₁))⁻¹.val - (valR w _ (wg.s (p₂, fun _ => j₂)).val).snd * valR x _ (wg.s (p₂, fun _ => j₂))⁻¹.val) := by
  first | exact @GlobalTheory.CechKS.dlog_transition_iso | exact GlobalTheory.CechKS.dlog_transition_iso | (intros; apply GlobalTheory.CechKS.dlog_transition_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliTraitPeriodsMonomialPosDef
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliTraitPeriodsMonomialPosDef
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.TraitTau

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues _root_.Formalism.L2.Pj

theorem exists_tauCoord {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (a b : Q.X) :
    ∃ k, Q.TauCoord a b k := by
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε), u.IsGen :=
    DVR.exists_gen_of_local (V := R) Q.M.L Q.M.isLB _ _
  have hφ : lamPts (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) =
      fun k => (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) k := by
    funext k
    fin_cases k
    · exact (congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TK R)) (Q.c a) (Q.c b))).symm
    · rfl
    · rfl
    · exact (congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TK R)))).symm
  obtain ⟨ρ, hρ⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ratio Q.M.isLB hφ (Q.tau a b)
    (LB.pullGen Q.M.L _ negε u (toUnit (TK R)).left) (Q.tau_gen a b) (DVR.pullGen_isGen _ _ _ _ hu _)
  let k : (FractionRing R)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom ρ
  have hk : unitOn k = ρ := Units.ext ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom_inv_id_apply ρ.val)
  refine ⟨k, u, hu, fun z J hJ => ?_⟩
  rw [hρ _ _ z J hJ, val_pull hJ, Category.id_comp, hk]

theorem isMonomialTau_ofDeg {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult) {m : ℕ}
    {t : Fin m → R} {β : Fin m → LinearMap.BilinForm ℤ D.X} (h : IsMonomial D t β) (hs : ∀ i y z, β i y z = β i z y)
    (ht : ∀ i, t i ≠ 0) : (Wit.ofDeg D hB).IsMonomialTau t β := by
  intro (a : D.X) (b : D.X)
  obtain ⟨k, hk⟩ := exists_tauCoord (Wit.ofDeg D hB) a b
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.RefTauCoord.main R R (Wit.ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) Function.injective_id
    (Wit.refines_ofDeg D hB) a b k hk x hx
  have hl : ∀ σ : FractionRing R →+* FractionRing R,
      (∀ r, σ (algebraMap R (FractionRing R) r) = algebraMap R (FractionRing R) (RingHom.id R r)) → ∀ y, σ y = y :=
    fun σ hσ => RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R) (k := RingHom.id _) (RingHom.ext hσ))
  rw [hl _ (fun r => by rw [IsFractionRing.lift_algebraMap]; rfl)] at hu₁
  obtain ⟨_, _, -, ha⟩ := h a
  obtain ⟨_, _, -, hb⟩ := h b
  obtain ⟨_, _, -, hab⟩ := h (a + b)
  obtain ⟨u₃, hu₃⟩ := h.tau hs ht ha hb hab
  obtain ⟨xa, ha₁, ha₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D a _).1 ha
  obtain ⟨xb, hb₁, hb₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D b _).1 hb
  obtain ⟨xab, hab₁, hab₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D (a + b) _).1 hab
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.TauCoordQuot.main R D a b x xab xa xb hx hab₁ ha₁ hb₁
  rw [← ha₂, ← hb₂, ← hab₂] at hu₃
  have hc := Taut.tauCoord_mul_unit hk (u₁ * u₂⁻¹ * u₃⁻¹)
  refine ⟨k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) (u₁ * u₂⁻¹ * u₃⁻¹), ?_, hc⟩
  refine Eq.trans (b := ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) ?_ rfl
  clear hc hk hl
  have hu : ∀ u : Rˣ, algebraMap R (FractionRing R) (u : R) ≠ 0 := fun u =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 u.ne_zero
  have e : algebraMap R (FractionRing R) u₁ * (k : FractionRing R) = algebraMap R (FractionRing R) u₂ *
      (algebraMap R (FractionRing R) u₃ * ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) := by
    rw [← hu₃, ← hu₁, hu₂, div_eq_mul_inv, mul_inv]
    ring
  have h₂ := hu u₂
  have h₃ := hu u₃
  generalize ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b = P at e ⊢
  rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  simp only [Units.val_mul, map_mul, map_units_inv]
  field_simp
  linear_combination e

theorem finrank_le {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} (T : Trait F) (hn : 2 ≤ n) (hζ : IsUnit ζ) :
    Module.finrank ℤ T.D.toPre.X ≤ g := by
  let K := AlgebraicClosure (FractionRing T.V)
  haveI : CharZero (FractionRing T.V) :=
    (RingHom.charZero_iff (IsFractionRing.injective T.V (FractionRing T.V))).1 inferInstance
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let κ : Sp K ⟶ Sp (FractionRing T.V) := spMap (algebraMap _ K)
  have hp := IsPullback.of_hasPullback F.univ.A.hom (κ ≫ T.y)
  have hq : IsPullback (T.cart.1.lift (pullback.fst F.univ.A.hom (κ ≫ T.y)) (pullback.snd F.univ.A.hom (κ ≫ T.y) ≫ κ)
      (by rw [Category.assoc]; exact hp.w)) (pullback.snd F.univ.A.hom (κ ≫ T.y)) T.A.A.hom κ :=
    IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hp) (T.cart.1.lift_snd _ _ _) T.cart.1
  have hd : SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (κ ≫ T.y)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange T.A.g).of_isPullback hq T.A.smoothDim
  have e : T.A.g = g := GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (κ ≫ T.y) hd
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F), (GlobalTheory.PolDeg.Wit.ofDeg T.D.toPre T.D.tau_bimult).IsMonomialTau ![T.ϖ] ![T.β] ∧ (∀ a, 0 ≤ T.β a a) ∧ (∀ a, a ≠ 0 → 0 < T.β a a) ∧ (2 ≤ n → IsUnit ζ → Module.finrank ℤ T.D.toPre.X ≤ g) := by
  intro g n o _ ζ F T
  refine ⟨isMonomialTau_ofDeg _ _ T.mono (fun i => ?_) (fun i => ?_), T.mono.nonneg 0, fun a ha => ?_, finrank_le T⟩
  · fin_cases i
    exact T.symm
  · fin_cases i
    exact T.irr.ne_zero
  · obtain ⟨i, hi⟩ := T.mono.exists_pos (maximalIdeal.isMaximal _).ne_top ha
    fin_cases i
    exact hi

end GlobalTheory.Poinc.TraitTau
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliTraitPeriodsMonomialPosDefStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F), (GlobalTheory.PolDeg.Wit.ofDeg T.D.toPre T.D.tau_bimult).IsMonomialTau ![T.ϖ] ![T.β] ∧ (∀ a, 0 ≤ T.β a a) ∧ (∀ a, a ≠ 0 → 0 < T.β a a) ∧ (2 ≤ n → IsUnit ζ → Module.finrank ℤ T.D.toPre.X ≤ g) := by
  first | exact @GlobalTheory.Poinc.TraitTau.main | exact GlobalTheory.Poinc.TraitTau.main | (intros; apply GlobalTheory.Poinc.TraitTau.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLevelMultipleSameAdelicPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLevelMultipleSameAdelicPart
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Pointwise

namespace GlobalTheory.GoodMultipleLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem coprime_M_N {M d : ℕ} (hM : M ≠ 0) (hd : d.Prime) (hd2 : d ≠ 2) :
    Nat.Coprime M ((2 * (M / d ^ M.factorization d)) ^ 2 + d) := by
  set c := M / d ^ M.factorization d with hc
  have hnc : ¬ d ∣ c := Nat.not_dvd_ordCompl hd hM
  have hmul : d ^ M.factorization d * c = M := Nat.ordProj_mul_ordCompl_eq_self M d
  apply Nat.coprime_of_dvd
  intro q hq hqM hqN
  have hqd : q ∣ d → q = d := fun h => (Nat.prime_dvd_prime_iff_eq hq hd).1 h
  by_cases hqc : q ∣ c
  · have h1 : q ∣ (2 * c) ^ 2 := Dvd.dvd.pow (Dvd.dvd.mul_left hqc 2) two_ne_zero
    have h2 : q ∣ d := (Nat.dvd_add_right h1).1 hqN
    exact hnc (hqd h2 ▸ hqc)
  · rw [← hmul] at hqM
    have h1 : q ∣ d ^ M.factorization d := ((Nat.Prime.dvd_mul hq).1 hqM).resolve_right hqc
    have h2 := hqd (hq.dvd_of_dvd_pow h1)
    subst h2
    have h3 : q ∣ (2 * c) ^ 2 := (Nat.dvd_add_left (dvd_refl q)).1 hqN
    have h4 := (Nat.Prime.dvd_mul hq).1 (hq.dvd_of_dvd_pow h3)
    rcases h4 with h | h
    · exact hd2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
    · exact hnc h

theorem exists_good_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H),
    ∃ l₂ : Level H, l.Dvd l₂ ∧ l₂.A = l.A ∧ ∀ q : ℕ, q.Prime → l₂.GoodAt q := by
  intro E _ _ _ H l
  have hdm := H.d_mod
  have hdp := H.d_prime
  have hM3 := l.three_le
  have hM0 : l.M ≠ 0 := by omega
  set c := l.M / H.d ^ l.M.factorization H.d with hc
  set a : ℕ := 2 * c with ha
  set N : ℕ := a ^ 2 + H.d with hN
  have hcop : Nat.Coprime l.M N := coprime_M_N hM0 hdp (by omega)
  have hdodd : Odd H.d := Nat.odd_iff.mpr (by omega)
  have hNodd : Odd N := Even.add_odd ⟨2 * c ^ 2, by rw [ha]; ring⟩ hdodd
  have hN3 : 3 ≤ N := by omega
  have hcd : Nat.Coprime a H.d := by
    rw [ha]
    refine Nat.Coprime.mul_left (Nat.coprime_two_left.mpr hdodd) ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hdp).2 (Nat.not_dvd_ordCompl hdp hM0)).symm
  set α : 𝓞 E := (a : 𝓞 E) + H.rt with hα
  have hαb : H.bar α = (a : 𝓞 E) - H.rt := by
    rw [hα, map_add (f := _), map_natCast, GlobalTheory.HostModel.bar_rt, sub_eq_add_neg]
  have hnorm : α * ((a : 𝓞 E) - H.rt) = (N : 𝓞 E) := GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H a
  have hαα : IsCoprime α ((a : 𝓞 E) - H.rt) := GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hcd hNodd
  have hαmem : α ∈ Algebra.adjoin ℤ {H.w0} := add_mem (natCast_mem _ a) (GlobalTheory.HostModel.rt_mem_adjoin H)
  have hmapI : (Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.map_span, Set.image_singleton]; exact congrArg _ (congrArg _ hαb)
  have hmapM : (l.Mb * Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) =
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.map_mul, hmapI]
  have hMN : Ideal.span {(l.M : 𝓞 E)} ⊔ Ideal.span {(N : 𝓞 E)} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact Nat.Coprime.cast hcop
  have hMle : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := by rw [← l.prod]; exact Ideal.mul_le_left
  have hMle' : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [← l.prod]; exact Ideal.mul_le_right
  have hNle : Ideal.span {(N : 𝓞 E)} ≤ Ideal.span {α} := by
    rw [Ideal.span_singleton_le_span_singleton, ← hnorm]; exact dvd_mul_right _ _
  have hNle' : Ideal.span {(N : 𝓞 E)} ≤ Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.span_singleton_le_span_singleton, ← hnorm]; exact dvd_mul_left _ _
  have c1 : IsCoprime l.Mb (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.isCoprime_iff_sup_eq.2 l.coprime
  have c2 : IsCoprime l.Mb (Ideal.span {(a : 𝓞 E) - H.rt}) := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hMN]; exact sup_le_sup hMle hNle'
  have c3 : IsCoprime (Ideal.span {α}) (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hMN]
    exact sup_le (le_sup_of_le_right hMle') (le_sup_of_le_left hNle)
  have c4 : IsCoprime (Ideal.span {α}) (Ideal.span {(a : 𝓞 E) - H.rt}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 hαα
  have hspan : l.Mb * Ideal.span {α} = Ideal.span ({x | x ∈ l.Mb ∧ x ∈ Algebra.adjoin ℤ {H.w0}} * ({α} : Set (𝓞 E))) := by
    conv_lhs => rw [l.fromK]
    exact Ideal.span_mul_span' _ _
  let l₂ : Level H :=
    { M := l.M * N
      three_le := by nlinarith
      odd := l.odd.mul hNodd
      Mb := l.Mb * Ideal.span {α}
      fromK := by
        refine le_antisymm ?_ (Ideal.span_le.2 fun x hx => hx.1)
        refine (le_of_eq hspan).trans (Ideal.span_mono ?_)
        rintro x ⟨s, hs, t, ht, rfl⟩
        rw [Set.mem_singleton_iff] at ht
        subst ht
        refine ⟨?_, mul_mem hs.2 hαmem⟩
        exact Ideal.mul_mem_mul hs.1 (Ideal.mem_span_singleton_self _)
      prod := by
        rw [hmapM]
        calc l.Mb * Ideal.span {α} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * Ideal.span {(a : 𝓞 E) - H.rt})
            = (l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) * (Ideal.span {α} * Ideal.span {(a : 𝓞 E) - H.rt}) := by ring
          _ = Ideal.span {((l.M * N : ℕ) : 𝓞 E)} := by
            rw [l.prod, Ideal.span_singleton_mul_span_singleton, hnorm,
              Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]
      coprime := by
        rw [hmapM, ← Ideal.isCoprime_iff_sup_eq]
        exact (c1.mul_right c2).mul_left (c3.mul_right c4)
      A := l.A
      A_pos := l.A_pos }
  refine ⟨l₂, ⟨dvd_mul_right _ _, Ideal.mul_le_left, dvd_refl _⟩, rfl, fun q hq => ?_⟩
  exact GlobalTheory.GlobalModelGuards.goodAt_of_coprime l₂ l.M N hM3 hN3 hcop rfl q hq

end GlobalTheory.GoodMultipleLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLevelMultipleSameAdelicPartStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodLevel_multiple_same_adelicPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H), ∃ l₂ : Level H, l.Dvd l₂ ∧ l₂.A = l.A ∧ ∀ q : ℕ, q.Prime → l₂.GoodAt q := by
  first | exact @GlobalTheory.GoodMultipleLevel.exists_good_multiple | exact GlobalTheory.GoodMultipleLevel.exists_good_multiple | (intros; apply GlobalTheory.GoodMultipleLevel.exists_good_multiple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def FrameAlong {X Y : Scheme.{0}} (L : LB X) (x : Y ⟶ X) (W : Y.Opens) (τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ) : Prop :=
  ∀ (z : Y) (k k' : L.ι), z ∈ W → x z ∈ L.U k → x z ∈ L.U k' →
    gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k) (τ k) =
      gm x z (L.U k ⊓ L.U k') (L.g k k') * gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k') (τ k')

def FrameCarriedAlong {X Y : Scheme.{0}} (L : LB X) (x : Y ⟶ X) (W : Y.Opens) (τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ)
    (f : X ⟶ X) (w : LB.Iso L (L.pull f)) (h : Y ⟶ Y) : Prop :=
  ∀ (z : Y) (j k : L.ι), z ∈ W → h z ∈ W → x z ∈ L.U k → x (h z) ∈ L.U j →
    gm h z (W ⊓ x ⁻¹ᵁ L.U j) (τ j) = gw w x z j k * gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k) (τ k)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfExponential
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfExponential
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.ExpFrame

theorem exists_isFactorAH_frame_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∀ (M : LB A.left), M.IsLB → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ g hA hg e he M hM
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.ExpKernel.kernel_isFullLattice (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e he
  obtain ⟨L₀, u₀, hu₀⟩ := GlobalTheory.exists_holUnif_of_isExp A g e Λ he hd hf hk
  obtain ⟨u, Hm, χ, hu, hAH⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  exact ⟨u, Hm, χ, fun z => by rw [hu, hu₀], hAH⟩

end GlobalTheory.ExpFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfExponentialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_exponential : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∀ (M : LB A.left), M.IsLB → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp | exact GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp | (intros; apply GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp <;> assumption)
end
end
