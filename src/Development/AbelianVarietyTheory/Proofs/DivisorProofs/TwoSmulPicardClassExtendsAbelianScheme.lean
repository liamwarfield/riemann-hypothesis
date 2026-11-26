module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationAtUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSize
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardTwoNsmulPullbackEqZeroOnTripleParamete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterSchemeTriplesAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesSurjectiveFibrewiseDenseOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveInfOfGeometricallyIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveInfOfGeometricallyIntegral
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory

theorem surjective_inf_of_geometricallyIntegral :
    ∀ (Z T : Scheme.{0}) (f : Z ⟶ T) [GeometricallyIntegral f] (O O' : Z.Opens),
      Surjective (O.ι ≫ f) → Surjective (O'.ι ≫ f) → Surjective ((O ⊓ O').ι ≫ f) := by
  intro Z T f _ O O' hO hO'
  refine ⟨fun t => ?_⟩
  have hint : IsIntegral (f.fiber t) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback f (T.fromSpecResidueField t))
  have hi : IsPreirreducible (f ⁻¹' {t}) := by
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ (f.fiberι t).continuous.continuousOn
  obtain ⟨x, hx⟩ := (O.ι ≫ f).surjective t
  obtain ⟨x', hx'⟩ := (O'.ι ≫ f).surjective t
  obtain ⟨y, hy, k₁, k₂⟩ := hi _ _ O.2 O'.2
    ⟨x.1, by rw [← hx]; rfl, x.2⟩ ⟨x'.1, by rw [← hx']; rfl, x'.2⟩
  exact ⟨⟨y, k₁, k₂⟩, hy⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveInfOfGeometricallyIntegralStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral : ∀ (Z T : Scheme.{0}) (f : Z ⟶ T) [GeometricallyIntegral f] (O O' : Z.Opens), Surjective (O.ι ≫ f) → Surjective (O'.ι ≫ f) → Surjective ((O ⊓ O').ι ≫ f) := by
  first | exact @GlobalTheory.surjective_inf_of_geometricallyIntegral | exact GlobalTheory.surjective_inf_of_geometricallyIntegral | (intros; apply GlobalTheory.surjective_inf_of_geometricallyIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesSurjectiveFibrewiseDenseOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TranslateSurj

theorem surjective_of_factor {X Y Z : Scheme.{0}} (p : X ⟶ Y) (O : X.Opens) (g : Z ⟶ X) (q : Z ⟶ Y)
    (hg : g ≫ p = q) (hq : Surjective q) (hO : ∀ z, g z ∈ O) : Surjective (O.ι ≫ p) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨z, rfl⟩ := hq.surj y
  refine ⟨⟨g z, hO z⟩, ?_⟩
  rw [← hg]
  rfl

end GlobalTheory.TranslateSurj

namespace GlobalTheory.TranslateSurj

theorem exists_translates_surjective : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (B : Over S) (j : B ⟶ A), (∀ b, j.left b ∈ V) → Smooth B.hom → GeometricallyIntegral B.hom → Surjective ((((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
  intro S A _ hA V B j hjV hBs hBg
  haveI := hA.smooth
  haveI := hA.geomConnected
  haveI := hBs
  haveI := hBg
  haveI : GeometricallyConnected B.hom := GlobalTheory.geometricallyConnected_of_geometricallyIntegral _
  haveI : Smooth (fst (A ⊗ A) B ≫ fst A A).left := by
    show Smooth (pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom); infer_instance
  haveI : GeometricallyConnected (fst (A ⊗ A) B ≫ fst A A).left := by
    show GeometricallyConnected (pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom)
    exact GeometricallyConnected.comp _ _
  haveI : GeometricallyIntegral (fst (A ⊗ A) B ≫ fst A A).left := GlobalTheory.geometricallyIntegral_of_smooth _
  have hq : Surjective (fst A B).left := by
    show Surjective (pullback.fst A.hom B.hom); infer_instance
  have key : ∀ (a₀ : A ⊗ B ⟶ A) (w : (A ⊗ A) ⊗ B ⟶ A),
      lift (lift (fst A B) a₀) (snd A B) ≫ w = snd A B ≫ j →
      Surjective ((w.left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
    intro a₀ w hw
    refine surjective_of_factor _ _ (lift (lift (fst A B) a₀) (snd A B)).left (fst A B).left ?_ hq ?_
    · rw [← Over.comp_left]; congr 1; simp
    · intro z
      show w.left ((lift (lift (fst A B) a₀) (snd A B)).left z) ∈ V
      have e : w.left ((lift (lift (fst A B) a₀) (snd A B)).left z) = j.left ((snd A B).left z) := by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hw, Over.comp_left, Scheme.Hom.comp_apply]
      rw [e]; exact hjV _
  refine GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral _ _ _ _ _ (GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral _ _ _ _ _ (GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral _ _ _ _ _ ?_ ?_) ?_) ?_
  · refine key ((fst A B)⁻¹ * (snd A B ≫ j)) _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key ((snd A B ≫ j)⁻¹ * fst A B) _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key 1 _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key 1 _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]

end GlobalTheory.TranslateSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesSurjectiveFibrewiseDenseOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translates_surjective_fibrewise_dense_open : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (B : Over S) (j : B ⟶ A), (∀ b, j.left b ∈ V) → Smooth B.hom → GeometricallyIntegral B.hom → Surjective ((((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
  first | exact @GlobalTheory.TranslateSurj.exists_translates_surjective | exact GlobalTheory.TranslateSurj.exists_translates_surjective | (intros; apply GlobalTheory.TranslateSurj.exists_translates_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOfIsOpenImmersionCompSurjec
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOfIsOpenImmersionCompSurjec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem geometricallyIntegral_of_isOpenImmersion_comp_surjective :
    ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  intro O Z T j f _ _ hs
  refine ⟨fun {K} _ y P fst snd h => ?_⟩
  have hZf : IsIntegral (pullback f y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) y _ _ (IsPullback.of_hasPullback f y)
  let fst' : P ⟶ pullback f y := pullback.lift (fst ≫ j) snd (by rw [Category.assoc]; exact h.w)
  have sq : IsPullback fst fst' j (pullback.fst f y) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd f y) (v₂₂ := f) (h₃₁ := y) ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f y)
    have e : fst' ≫ pullback.snd f y = snd := pullback.lift_snd _ _ _
    rw [e]; exact h
  have : IsOpenImmersion fst' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq inferInstance
  have hsn : Surjective snd := MorphismProperty.of_isPullback (P := @Surjective) h hs
  have : Nonempty P := by
    obtain ⟨z, -⟩ := snd.surjective (Nonempty.some inferInstance : Spec (.of K))
    exact ⟨z⟩
  exact isIntegral_of_isOpenImmersion fst'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOfIsOpenImmersionCompSurjecStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective : ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  first | exact @GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective | exact GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective | (intros; apply GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterSchemeTriplesAbelianScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ParamTriple

theorem exists_param : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens), (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∃ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), IsIntegral Y.left ∧ Smooth x.left ∧ Surjective x.left ∧ p ≫ V.ι = v.left ∧ (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) ∧ Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ := by
  intro S _ _ A _ hA V hV
  have := hA.smooth
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have hAA := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have := hAA.smooth
  have : GeometricallyIntegral (A ⊗ A).hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hAA.smooth hAA.geomConnected
  let B : Over S := Over.mk (V.ι ≫ A.hom)
  let j : B ⟶ A := Over.homMk V.ι
  have hBs : Smooth B.hom := by dsimp [B]; infer_instance
  have hBsurj : Surjective (V.ι ≫ A.hom) := ⟨fun s => by
    obtain ⟨x, hx, rfl⟩ := hV s
    exact ⟨⟨x, hx⟩, rfl⟩⟩
  have hBgi : GeometricallyIntegral B.hom := GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective _ _ _ V.ι A.hom hBsurj
  let P : Over S := (A ⊗ A) ⊗ B
  let X : P ⟶ A := fst _ _ ≫ fst A A
  let Aa : P ⟶ A := fst _ _ ≫ snd A A
  let Vv : P ⟶ A := snd _ _ ≫ j
  let O : P.left.Opens := (X * Aa).left ⁻¹ᵁ V ⊓ (X * Aa⁻¹).left ⁻¹ᵁ V ⊓ (Vv * Aa).left ⁻¹ᵁ V ⊓
    (Vv * Aa⁻¹).left ⁻¹ᵁ V
  have hsurj : Surjective (O.ι ≫ X.left) :=
    GlobalTheory.T.exists_translates_surjective_fibrewise_dense_open S A hA V B j (fun b => b.2) hBs hBgi
  let Y : Over S := Over.mk (O.ι ≫ P.hom)
  let i : Y ⟶ P := Over.homMk O.ι
  have hmem : ∀ (f : P ⟶ A), O ≤ f.left ⁻¹ᵁ V → ∀ y, (i ≫ f).left y ∈ V := by
    intro f hf y
    exact hf y.2

  let s : B ⟶ P := lift (lift j 1) (𝟙 B)
  have hsX : s ≫ X = j := by simp [s, X]
  have hsA : s ≫ Aa = 1 := by simp [s, Aa]
  have hsV : s ≫ Vv = j := by simp [s, Vv]
  have hsO : ∀ b, s.left b ∈ O := by
    intro b
    have h1 : ∀ f : P ⟶ A, s ≫ f = j → s.left b ∈ f.left ⁻¹ᵁ V := by
      intro f hf
      show (s.left ≫ f.left) b ∈ V
      rw [← Over.comp_left, hf]
      exact b.2
    refine ⟨⟨⟨h1 _ ?_, h1 _ ?_⟩, h1 _ ?_⟩, h1 _ ?_⟩
    · rw [MonObj.comp_mul, hsX, hsA, _root_.mul_one]
    · rw [MonObj.comp_mul, GrpObj.comp_inv, hsX, hsA, inv_one, _root_.mul_one]
    · rw [MonObj.comp_mul, hsV, hsA, _root_.mul_one]
    · rw [MonObj.comp_mul, GrpObj.comp_inv, hsV, hsA, inv_one, _root_.mul_one]
  have hrO : Set.range s.left ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨b, rfl⟩; exact hsO b
  let e0 : V.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι s.left hrO
  have he0 : e0 ≫ O.ι = s.left := IsOpenImmersion.lift_fac _ _ _
  let x : Y ⟶ A := i ≫ X
  let a : Y ⟶ A := i ≫ Aa
  let v : Y ⟶ A := i ≫ Vv
  let p : Y.left ⟶ V.toScheme := O.ι ≫ (snd (A ⊗ A) B).left
  have hxl : x.left = O.ι ≫ X.left := rfl
  have hre : Set.range e0 ⊆ Set.range (x.left ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨b, rfl⟩
    show (e0 ≫ x.left) b ∈ V
    rw [hxl, ← Category.assoc, he0, ← Over.comp_left, hsX]
    exact b.2
  let e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift _ e0 hre
  have he : e ≫ (x.left ⁻¹ᵁ V).ι = e0 := IsOpenImmersion.lift_fac _ _ _
  have hsec : e ≫ ((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom = 𝟙 _ := by
    rw [← Category.assoc, ← Category.assoc, he, he0]
    show (s ≫ snd (A ⊗ A) B).left = _
    rw [lift_snd]; rfl
  obtain ⟨s0⟩ := (inferInstance : Nonempty S)
  obtain ⟨x0, hx0, -⟩ := hV s0
  have : Nonempty V.toScheme := ⟨⟨x0, hx0⟩⟩
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ A.hom)
  have : Flat (A ⊗ A).hom := inferInstance
  have : UniversallyOpen (A ⊗ A).hom := inferInstance
  have : IsIntegral B.left := ‹IsIntegral V.toScheme›
  have : IsLocallyNoetherian B.left := ‹IsLocallyNoetherian V.toScheme›
  have : IsIntegral P.left := inferInstanceAs (IsIntegral (pullback (A ⊗ A).hom B.hom))
  obtain ⟨b0⟩ := (inferInstance : Nonempty V.toScheme)
  have : Nonempty O.toScheme := ⟨⟨s.left b0, hsO b0⟩⟩
  have hYi : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  have hgi : GeometricallyIntegral (((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom) := by
    refine GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective _ _ _ _ _ ?_
    have : Surjective (e ≫ ((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom) := by
      rw [hsec]; infer_instance
    exact Surjective.of_comp e _
  have hxa : x * a = i ≫ (X * Aa) := by simp only [x, a, MonObj.comp_mul]
  have hxa' : x * a⁻¹ = i ≫ (X * Aa⁻¹) := by simp only [x, a, MonObj.comp_mul, GrpObj.comp_inv]
  have hva : v * a = i ≫ (Vv * Aa) := by simp only [v, a, MonObj.comp_mul]
  have hva' : v * a⁻¹ = i ≫ (Vv * Aa⁻¹) := by simp only [v, a, MonObj.comp_mul, GrpObj.comp_inv]
  refine ⟨Y, x, a, v, p, e, hYi, ?_, hsurj, ?_, fun y => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show Smooth (O.ι ≫ pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom)
    infer_instance
  · show (O.ι ≫ (snd (A ⊗ A) B).left) ≫ V.ι = O.ι ≫ (snd (A ⊗ A) B ≫ j).left
    rw [Category.assoc, Over.comp_left]; rfl
  · rw [hxa]; exact hmem _ (fun z hz => hz.1.1.1) y
  · rw [hxa']; exact hmem _ (fun z hz => hz.1.1.2) y
  · rw [hva]; exact hmem _ (fun z hz => hz.1.2) y
  · rw [hva']; exact hmem _ (fun z hz => hz.2) y
  · show Smooth ((x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom)
    infer_instance
  · show GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom)
    rw [← Category.assoc]; exact hgi
  · show e ≫ (x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom = 𝟙 _
    rw [← hsec]; simp only [Category.assoc]

end GlobalTheory.ParamTriple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterSchemeTriplesAbelianSchemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parameterScheme_triples_abelianScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens), (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∃ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), IsIntegral Y.left ∧ Smooth x.left ∧ Surjective x.left ∧ p ≫ V.ι = v.left ∧ (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) ∧ Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ := by
  first | exact @GlobalTheory.ParamTriple.exists_param | exact GlobalTheory.ParamTriple.exists_param | (intros; apply GlobalTheory.ParamTriple.exists_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassLocallyTrivialOfTrivialSmoothNormalCo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionNearOfFlatTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionNearOfFlatTrivial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatTrivSec

variable {X Y : Scheme.{0}}

theorem isUnit_gs_iff {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f z U a) ↔ f z ∈ X.basicOpen a := by
  rw [gs_eq f z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

def pullSec (L : LB X) (θ : LB.Sec L) (F : Y ⟶ X) : LB.Sec (L.pull F) where
  f := fun I => (Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : PUnit => F) I PUnit.unit)).op).hom
    ((F.app _).hom (θ.f (I PUnit.unit)))
  compat := fun I J => fn_ext fun y hy => by
    have hI : F y ∈ L.U (I PUnit.unit) := mem_pull.1 hy.1
    have hJ : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.2
    have hm : (𝟙 Y ≫ F) y ∈ L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit) := ⟨hI, hJ⟩
    refine (gs_res (𝟙 Y) y _ hy _).trans ((gs_res (𝟙 Y) y _ hy.1 _).trans ((gs_pull (𝟙 Y) F y _ hI _).trans ?_))
    refine Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_pull_g L F (𝟙 Y) y I J hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans ((gs_res (𝟙 Y) y _ hy.2 _).trans (gs_pull (𝟙 Y) F y _ hJ _))))).symm
    exact (gs_res _ y inf_le_left hm _).symm.trans ((congrArg (gs _ y _) (θ.compat _ _)).trans
      ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hm _) (gs_res _ y _ hm _))))

theorem gs_pullSec (L : LB X) (θ : LB.Sec L) (F : Y ⟶ X) (y : Y) (J : PUnit → L.ι) (hy : y ∈ (L.pull F).U J) :
    gs (𝟙 Y) y _ ((pullSec L θ F).f J) = gs F y (L.U (J PUnit.unit)) (θ.f (J PUnit.unit)) := by
  have hI : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy
  refine (gs_res (𝟙 Y) y _ hy _).trans ((gs_pull (𝟙 Y) F y _ hI _).trans ?_)
  rw [Category.id_comp]

theorem cst_bijective_of {C : Type} [CommRing C] (V : (Sp C).Opens)
    (hV : Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom) :
    Function.Bijective (cst V.ι ⊤) := by
  have key : ∀ (V' : (Sp C).Opens) (h : V' ≤ ⊤), V' = V →
      Function.Bijective ((Sp C).presheaf.map (homOfLE h).op).hom := by
    rintro V' h rfl
    exact hV
  have h₁ : Function.Bijective V.ι.appTop.hom := by
    rw [Scheme.Opens.ι_appTop]
    exact key _ _ V.ι_image_top
  have h₀ : Function.Bijective (rs V.toScheme (le_top : (⊤ : V.toScheme.Opens) ≤ ⊤)) := by
    have : ⇑(rs V.toScheme (le_top : (⊤ : V.toScheme.Opens) ≤ ⊤)) = id := funext fun x => rs_self _ x
    rw [this]
    exact Function.bijective_id
  have h₃ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  exact h₀.comp (h₁.comp h₃)

theorem gs_cst_top {C : Type} [CommRing C] {Z : Scheme.{0}} (f : Z ⟶ Sp C) (z : Z) (x : C) :
    gs (𝟙 Z) z ⊤ (cst f ⊤ x) = gs f z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom x) := by
  refine (gs_res (𝟙 Z) z (U := f ⁻¹ᵁ ⊤) (V := ⊤) le_top trivial _).trans ((gs_pull (𝟙 Z) f z ⊤ trivial _).trans ?_)
  rw [Category.id_comp]

theorem exists_sec_near : ∀ (B C : Type) [CommRing B] [IsNoetherianRing B] [CommRing C] (g : B →+* C), g.Flat → ∀ (W : (Sp B).Opens), Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : spMap g ⁻¹ᵁ W ≤ ⊤)).op).hom → ∀ (M : LB W.toScheme), M.IsLB → Triv (M.pull (spMap g ∣_ W)) → ∀ y : Sp C, ∃ (s : M.Sec) (D : (Sp C).Opens), y ∈ D ∧ ∀ z : (spMap g ⁻¹ᵁ W).toScheme, (spMap g ⁻¹ᵁ W).ι z ∈ D → (spMap g ∣_ W) z ∈ Out.nonzeroLocus s := by
  intro B C _ _ _ g hg W hbij M hM hT y
  classical
  haveI : CompactSpace W.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (W : Set (Sp B)))
  obtain ⟨t, ht⟩ := hT
  obtain ⟨n, c, u, hcomb⟩ := FlatSec.exists_comb_of_flat B C g hg W.toScheme W.ι _ (spMap g ∣_ W)
    (spMap g ⁻¹ᵁ W).ι (isPullback_morphismRestrict (spMap g) W) M hM (genSec t ht)
  choose a ha using fun i => DVR.ValuationAtUnit.exists_glue_ratio
    (DVR.linComb_cover M hM (fun _ : PUnit => spMap g ∣_ W) (fun _ => 1)) (pullSec M (u i) (spMap g ∣_ W)) t ht
  have hb := cst_bijective_of _ hbij
  choose e he using fun i => hb.2 (a i)
  have chart : ∀ z : (spMap g ⁻¹ᵁ W).toScheme, ∃ k, (spMap g ∣_ W) z ∈ M.U k := fun z => by
    have hz : (spMap g ∣_ W) z ∈ ⨆ k, M.U k := by rw [hM.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hz
  have key : ∀ (z : (spMap g ⁻¹ᵁ W).toScheme) (k : M.ι), (spMap g ∣_ W) z ∈ M.U k → ∀ i,
      gs (spMap g ∣_ W) z _ ((u i).f k) = gs (𝟙 _) z ⊤ (a i) * (gm (𝟙 _) z _ (t.s (fun _ => k))).val := by
    intro z k hk i
    have hz : z ∈ (M.pull (spMap g ∣_ W)).U (fun _ => k) := mem_pull.2 hk
    refine (gs_pullSec M (u i) _ z (fun _ => k) hz).symm.trans ?_
    refine (congrArg (gs (𝟙 _) z _) (ha i (fun _ => k))).trans ?_
    rw [gs_mul (𝟙 _) z _ hz, gs_res (𝟙 _) z _ hz, gs_unit (𝟙 _) z _ hz]
  have hsum : ∑ i, c i * e i = 1 := by
    apply hb.1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    refine fn_ext fun z _ => ?_
    obtain ⟨k, hk⟩ := chart z
    have hz : z ∈ (M.pull (spMap g ∣_ W)).U (fun _ => k) := mem_pull.2 hk
    have h1 := hcomb z k hk
    simp only [key z k hk] at h1
    have h2 : gs (𝟙 _) z _ ((genSec t ht).f (fun _ => k)) = (gm (𝟙 _) z _ (t.s (fun _ => k))).val :=
      gs_unit (𝟙 _) z _ hz _
    rw [h2] at h1
    simp only [map_mul, he]
    rw [FlatSec.gs_sum (𝟙 _) z ⊤ trivial, gs_eq (𝟙 _) z ⊤ trivial 1, map_one, map_one]
    simp only [gs_mul (𝟙 _) z ⊤ trivial]
    have h3 : (∑ i, gs (𝟙 _) z ⊤ (cst (spMap g ⁻¹ᵁ W).ι ⊤ (c i)) * gs (𝟙 _) z ⊤ (a i)) *
        (gm (𝟙 _) z _ (t.s (fun _ => k))).val = 1 * (gm (𝟙 _) z _ (t.s (fun _ => k))).val := by
      rw [_root_.one_mul, Finset.sum_mul]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => _root_.mul_assoc _ _ _) h1.symm
    exact (Units.mul_left_inj _).1 h3
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ y.asIdeal := by
    by_contra hne
    push_neg at hne
    apply y.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hne i)
  refine ⟨u i, PrimeSpectrum.basicOpen (e i), hi, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := chart z
  have hu1 : IsUnit (gs (𝟙 _) z ⊤ (a i)) := by
    rw [← he i, gs_cst_top, isUnit_gs_iff _ z ⊤ trivial, basicOpen_eq_of_affine]
    exact hz
  have hu2 : IsUnit (gs (spMap g ∣_ W) z _ ((u i).f k)) := by
    rw [key z k hk i]
    exact hu1.mul (Units.isUnit _)
  rw [isUnit_gs_iff _ z _ hk] at hu2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hu2⟩

end GlobalTheory.FlatTrivSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionNearOfFlatTrivialStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nowhereZero_section_near_of_flat_trivial : ∀ (B C : Type) [CommRing B] [IsNoetherianRing B] [CommRing C] (g : B →+* C), g.Flat → ∀ (W : (Sp B).Opens), Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : spMap g ⁻¹ᵁ W ≤ ⊤)).op).hom → ∀ (M : LB W.toScheme), M.IsLB → Triv (M.pull (spMap g ∣_ W)) → ∀ y : Sp C, ∃ (s : M.Sec) (D : (Sp C).Opens), y ∈ D ∧ ∀ z : (spMap g ⁻¹ᵁ W).toScheme, (spMap g ⁻¹ᵁ W).ι z ∈ D → (spMap g ∣_ W) z ∈ Out.nonzeroLocus s := by
  first | exact @GlobalTheory.FlatTrivSec.exists_sec_near | exact GlobalTheory.FlatTrivSec.exists_sec_near | (intros; apply GlobalTheory.FlatTrivSec.exists_sec_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassLocallyTrivialOfTrivialSmoothNormalCo
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocalTriv

theorem hartogs_chart : ∀ (Y : Scheme.{0}) (V : Y.Opens) (hV : IsAffineOpen V), IsLocallyNoetherian (Sp Γ(Y, V)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ U : (Sp Γ(Y, V)).Opens, (∀ p : Sp Γ(Y, V), ringKrullDim (Y.presheaf.stalk (hV.fromSpec p)) ≤ 1 → p ∈ U) → Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
  intro Y V hV hLN hY U hU
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp Γ(Y, V)) := fun p => by
    let e := (asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    obtain ⟨h1, h2⟩ := hY (hV.fromSpec p)
    haveI := h1
    haveI := h2
    haveI : IsDomain ((Sp Γ(Y, V)).presheaf.stalk p) := MulEquiv.isDomain _ e.symm.toMulEquiv
    exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩
  have hb := ((GlobalTheory.extension_over_codim_two (Sp Γ(Y, V)) hN).1 U fun p hp => hU p (by
    let e := (asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    exact (ringKrullDim_eq_of_ringEquiv e).trans_le hp)).1 ⊤
  have key : ∀ (V' : (Sp Γ(Y, V)).Opens) (_ : V' = U) (h' : V' ≤ ⊤),
      Function.Bijective (resG (Sp Γ(Y, V)) h') →
        Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
    rintro _ rfl _ h
    exact h
  exact key _ (top_inf_eq U) _ hb

theorem factor_locus : ∀ (X T : Scheme.{0}) (W : X.Opens) (c : Pic W.toScheme) (j : T ⟶ X) [IsOpenImmersion j] (V : (j ⁻¹ᵁ W).toScheme.Opens), IsLocus (GlobalTheory.CechPic.pull (j ∣_ W) c) V → ∀ N : X.Opens, (∀ w ∈ N ⊓ W, ∃ z ∈ V, j ((j ⁻¹ᵁ W).ι z) = w) → GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  intro X T W c j _ V hV N hN
  have hz : ∀ z : (N ⊓ W).toScheme, ∃ z' ∈ V, (j ∣_ W) z' = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z := by
    intro z
    obtain ⟨z', hz'V, hz'⟩ := hN ((N ⊓ W).ι z) z.2
    refine ⟨z', hz'V, W.ι.isOpenEmbedding.injective ?_⟩
    have e1 : W.ι ((j ∣_ W) z') = j ((j ⁻¹ᵁ W).ι z') :=
      congrArg (fun f => f.base z') (morphismRestrict_ι j W)
    have e2 : W.ι (X.homOfLE (inf_le_right : N ⊓ W ≤ W) z) = (N ⊓ W).ι z :=
      congrArg (fun f => f.base z) (X.homOfLE_ι (inf_le_right : N ⊓ W ≤ W))
    exact e1.trans (hz'.trans e2.symm)
  let k := IsOpenImmersion.lift (j ∣_ W) (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) (by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z', -, h⟩ := hz z
    exact ⟨z', h⟩)
  have hk : k ≫ (j ∣_ W) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) := IsOpenImmersion.lift_fac _ _ _
  rw [← hk, pull_comp]
  refine GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.2 _ _ k _ V hV fun z => ?_
  obtain ⟨z', hz'V, h⟩ := hz z
  have hkz : k z = z' := (j ∣_ W).isOpenEmbedding.injective (by
    have e : (j ∣_ W) (k z) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z := congrArg (fun f => f.base z) hk
    exact e.trans h.symm)
  rw [hkz]
  exact hz'V

theorem locally_trivial : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) [Smooth q] [Surjective q], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ W : X.Opens, (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (q ∣_ W) c = 0 → ∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  intro X Y _ q _ _ hY W hW c hc x
  obtain ⟨y, rfl⟩ := q.surjective x
  obtain ⟨N0, hN0, hx0, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show q y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨N1, hN1, hy1, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ q ⁻¹ᵁ N0 from hx0)
  have hA0 : IsAffineOpen N0 := hN0
  have hA1 : IsAffineOpen N1 := hN1
  have hB : IsNoetherianRing Γ(X, N0) := IsLocallyNoetherian.component_noetherian ⟨N0, hN0⟩
  let g : Γ(X, N0) →+* Γ(Y, N1) := (q.appLE N0 N1 hle).hom
  have hg : g.Flat := HasRingHomProperty.appLE @Flat q inferInstance ⟨N0, hN0⟩ ⟨N1, hN1⟩ hle
  have hsq : spMap g ≫ hA0.fromSpec = hA1.fromSpec ≫ q := IsAffineOpen.SpecMap_appLE_fromSpec q hA0 hA1 hle
  have hpt : ∀ p, hA0.fromSpec (spMap g p) = q (hA1.fromSpec p) := fun p => by
    have := congrArg (fun f => f.base p) hsq
    simpa using this
  have hLN : IsLocallyNoetherian (Sp Γ(Y, N1)) := LocallyOfFiniteType.isLocallyNoetherian (hA1.fromSpec ≫ q)
  let W0 : (Sp Γ(X, N0)).Opens := hA0.fromSpec ⁻¹ᵁ W
  have hbij := hartogs_chart Y N1 hA1 hLN hY (spMap g ⁻¹ᵁ W0) fun p hp => by
    show hA0.fromSpec (spMap g p) ∈ W
    rw [hpt]
    exact hW _ hp
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  let M := L.pull (hA0.fromSpec ∣_ W)
  have hM : M.IsLB := pull_isLB hL _
  have hk : spMap g ⁻¹ᵁ W0 ≤ hA1.fromSpec ⁻¹ᵁ (q ⁻¹ᵁ W) := fun p hp => by
    show q (hA1.fromSpec p) ∈ W
    rw [← hpt]
    exact hp
  have hcomp : (spMap g ∣_ W0) ≫ (hA0.fromSpec ∣_ W) = hA1.fromSpec.resLE (q ⁻¹ᵁ W) _ hk ≫ (q ∣_ W) := by
    rw [← cancel_mono W.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]
    exact (morphismRestrict_ι_assoc (spMap g) W0 hA0.fromSpec).trans (congrArg _ hsq)
  have htriv : Triv (M.pull (spMap g ∣_ W0)) := by
    have h0 : cls _ (pull_isLB hM (spMap g ∣_ W0)) = 0 := by
      rw [cls_pull hM, cls_pull hL, ← pull_comp, hcomp, pull_comp, hc, map_zero]
    exact (cls_eq_zero_iff _).1 h0
  obtain ⟨y1, rfl⟩ : y ∈ Set.range hA1.fromSpec := hA1.range_fromSpec ▸ hy1
  obtain ⟨s, D, hyD, hD⟩ := GlobalTheory.T.exists_nowhereZero_section_near_of_flat_trivial Γ(X, N0) Γ(Y, N1) g hg W0 hbij M hM htriv y1
  let N : X.Opens := ⟨q '' (hA1.fromSpec '' D), q.isOpenMap _ (hA1.fromSpec.isOpenEmbedding.isOpenMap _ D.isOpen)⟩
  refine ⟨N, ⟨_, ⟨y1, hyD, rfl⟩, rfl⟩, ?_⟩
  refine factor_locus X _ W _ hA0.fromSpec (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) ⟨M, hM, s, cls_pull hL _ hM, rfl⟩ N ?_
  rintro w ⟨⟨_, ⟨d, hd, rfl⟩, rfl⟩, hwW⟩
  have hdW : d ∈ spMap g ⁻¹ᵁ W0 := by
    show hA0.fromSpec (spMap g d) ∈ W
    rw [hpt]
    exact hwW
  refine ⟨(spMap g ∣_ W0) ⟨d, hdW⟩, hD ⟨d, hdW⟩ hd, ?_⟩
  have e : W0.ι ((spMap g ∣_ W0) ⟨d, hdW⟩) = spMap g d :=
    congrArg (fun f => f.base ⟨d, hdW⟩) (morphismRestrict_ι (spMap g) W0)
  exact (congrArg hA0.fromSpec.base e).trans (hpt d)

end GlobalTheory.LocalTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassLocallyTrivialOfTrivialSmoothNormalCoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picardClass_locally_trivial_of_trivial_smooth_normal_cover : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) [Smooth q] [Surjective q], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ W : X.Opens, (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (q ∣_ W) c = 0 → ∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  first | exact @GlobalTheory.LocalTriv.locally_trivial | exact GlobalTheory.LocalTriv.locally_trivial | (intros; apply GlobalTheory.LocalTriv.locally_trivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatPreimageContainsCodimLeOnePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatPreimageContainsCodimLeOnePoints
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatCodimOne

theorem coheight_map_le_one {X Y : Scheme.{0}} (q : Y ⟶ X) (hq : GeneralizingMap q) (y : Y)
    (hy : Order.coheight y ≤ 1) : Order.coheight (q y) ≤ 1 := by
  have hy' := (Order.coheight_le_coe_iff (n := 1)).1 hy
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun z hz ↦ ?_
  obtain ⟨y', h₁, rfl⟩ := hq (show z ⤳ q y from hz.le)
  have hlt : y < y' := ⟨h₁, fun h ↦ hz.not_ge (Specializes.map h q.continuous)⟩
  have hm : IsMax y' := by simpa using hy' y' hlt
  have : IsMax (q y') := fun w hw ↦ by
    obtain ⟨y'', h₂, rfl⟩ := hq (show w ⤳ q y' from hw)
    exact Specializes.map (hm (show y' ≤ y'' from h₂)) q.continuous
  simpa using this

theorem preimage_contains_codim_le_one : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) [Flat q] (W : X.Opens), (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) := by
  intro X Y q _ W hW y hy
  show q y ∈ W
  apply hW
  rw [ringKrullDim_stalk_eq_coheight] at hy ⊢
  have h1 : Order.coheight y ≤ 1 := by exact_mod_cast hy
  have := coheight_map_le_one q (Flat.generalizingMap q) y h1
  exact_mod_cast this

end GlobalTheory.FlatCodimOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatPreimageContainsCodimLeOnePointsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_preimage_contains_codim_le_one_points : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) [Flat q] (W : X.Opens), (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.FlatCodimOne.preimage_contains_codim_le_one | exact GlobalTheory.FlatCodimOne.preimage_contains_codim_le_one | (intros; apply GlobalTheory.FlatCodimOne.preimage_contains_codim_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardExtendOfLocallyTrivialNormalCodimTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardExtendOfLocallyTrivialNormalCodimTwo
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExtendClass

open GlobalTheory.GlueLineBundle TopologicalSpace

variable {X : Scheme.{0}}

theorem gm_eq_map {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (hy : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U hy, Units.coe_map, gm_val (𝟙 X) (f y) U hy]
  show _ = (f.stalkMap y).hom ((X.presheaf.germ U (f y) hy).hom a.val)
  rw [Scheme.Hom.germ_stalkMap_apply]

theorem map_stalk_inj {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    Function.Injective (Units.map (j.stalkMap y).hom.toMonoidHom) :=
  Units.map_injective (f := (j.stalkMap y).hom.toMonoidHom)
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.injective

theorem exists_res_eq {U V : X.Opens} (h : V ≤ U) (hb : Function.Bijective (resG X h)) (u : Γ(X, V)ˣ) :
    ∃ a : Γ(X, U)ˣ, res h a = u := by
  obtain ⟨a, ha⟩ := hb.2 u.val
  obtain ⟨b, hb'⟩ := hb.2 u.inv
  have e1 : a * b = 1 := hb.1 (by rw [map_mul, map_one, ha, hb']; exact u.val_inv)
  exact ⟨⟨a, b, e1, (mul_comm _ _).trans e1⟩, Units.ext ha⟩

theorem eq_of_gm_ι (W : X.Opens) (hW : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)))
    {V : X.Opens} {a b : Γ(X, V)ˣ} (h : ∀ w : W.toScheme, W.ι w ∈ V → gm W.ι w V a = gm W.ι w V b) : a = b := by
  have e : res (inf_le_left : V ⊓ W ≤ V) a = res inf_le_left b := by
    apply unit_ext_imm
    intro x hx
    have hxW : x ∈ W := hx.2
    have hxV : x ∈ V := hx.1
    have hx' : W.ι ⟨x, hxW⟩ ∈ V ⊓ W := hx
    refine ⟨_, W.ι, inferInstance, ⟨x, hxW⟩, rfl, ?_⟩
    exact (gm_res W.ι _ inf_le_left hx' a).trans ((h _ hxV).trans (gm_res W.ι _ inf_le_left hx' b).symm)
  exact Units.ext ((hW V).1 (congrArg Units.val e))

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace
variable {X : Scheme.{0}}

theorem exists_sigma (W : X.Opens) {M : LB W.toScheme} (N : X.Opens)
    (t : LB.Gen (M.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)))) (ht : t.IsGen) :
    ∃ σ : ∀ k, Γ(W.toScheme, W.ι ⁻¹ᵁ N ⊓ M.U k)ˣ, ∀ (z : W.toScheme) (k k' : M.ι), W.ι z ∈ N → z ∈ M.U k →
      z ∈ M.U k' → gm (𝟙 _) z _ (σ k) = gm (𝟙 _) z (M.U k ⊓ M.U k') (M.g k k') * gm (𝟙 _) z _ (σ k') := by
  revert t
  set ι₁ := X.homOfLE (inf_le_right : N ⊓ W ≤ W) with hι₁
  intro t ht
  have pre : ∀ z : W.toScheme, W.ι z ∈ N → ∃ a : (N ⊓ W : X.Opens).toScheme, ι₁ a = z := fun z hz =>
    ⟨⟨z.1, hz, z.2⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have hle : ∀ k, W.ι ⁻¹ᵁ N ⊓ M.U k ≤ ι₁ ''ᵁ (M.pull ι₁).U (fun _ => k) := fun k z hz => by
    obtain ⟨a, rfl⟩ := pre z hz.1
    exact ι₁.apply_mem_image_iff.2 (mem_pull.2 hz.2)
  refine ⟨fun k => res (hle k) (imU ι₁ _ (t.s fun _ => k)), fun z k k' hz hk hk' => ?_⟩
  obtain ⟨a, rfl⟩ := pre z hz
  have ev : ∀ k, ι₁ a ∈ M.U k → gm ι₁ a (W.ι ⁻¹ᵁ N ⊓ M.U k) (res (hle k) (imU ι₁ _ (t.s fun _ => k))) =
      gm (𝟙 _) a _ (t.s fun _ => k) := fun k hk => by
    have hm : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k := ⟨hz, hk⟩
    rw [gm_res ι₁ a (hle k) hm]
    have := gm_imU ι₁ (𝟙 _) a ((M.pull ι₁).U fun _ => k) (mem_pull.2 hk) (t.s fun _ => k)
    rwa [Category.id_comp] at this
  have eg : gm ι₁ a (M.U k ⊓ M.U k') (M.g k k') = gm (𝟙 _) a _ ((M.pull ι₁).g (fun _ => k) (fun _ => k')) := by
    have := gm_pull_g M ι₁ (𝟙 _) a (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')
    rw [Category.id_comp] at this
    exact this.symm
  have m1 : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k := ⟨hz, hk⟩
  have m2 : ι₁ a ∈ M.U k ⊓ M.U k' := ⟨hk, hk'⟩
  have m3 : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k' := ⟨hz, hk'⟩
  apply map_stalk_inj ι₁ a
  beta_reduce
  rw [map_mul, ← gm_eq_map ι₁ a _ m1, ← gm_eq_map ι₁ a _ m2, ← gm_eq_map ι₁ a _ m3,
    ev k hk, ev k' hk', eg]
  exact (isGen_iff_germ t).1 ht a (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace
variable {X : Scheme.{0}}

theorem mul_ringHom_units_ratio {G : Type} [CommGroup G] (g a b : G) : g * a * (g * b)⁻¹ = a * b⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio (W : X.Opens) {M : LB W.toScheme} (hM : M.IsLB) {I : Type} (N : I → X.Opens)
    (σ : ∀ x k, Γ(W.toScheme, W.ι ⁻¹ᵁ N x ⊓ M.U k)ˣ)
    (hσ : ∀ x (z : W.toScheme) (k k' : M.ι), W.ι z ∈ N x → z ∈ M.U k → z ∈ M.U k' →
      gm (𝟙 _) z _ (σ x k) = gm (𝟙 _) z (M.U k ⊓ M.U k') (M.g k k') * gm (𝟙 _) z _ (σ x k')) (x y : I) :
    ∃ r : Γ(W.toScheme, W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y)ˣ, ∀ (z : W.toScheme) (k : M.ι), W.ι z ∈ N x → W.ι z ∈ N y →
      z ∈ M.U k → gm (𝟙 _) z _ r = gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ := by
  let O : M.ι → W.toScheme.Opens := fun k => W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y ⊓ M.U k
  have l0 : ∀ k, O k ≤ W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y := fun k => inf_le_left
  have lx : ∀ k, O k ≤ W.ι ⁻¹ᵁ N x ⊓ M.U k := fun k z hz => ⟨hz.1.1, hz.2⟩
  have ly : ∀ k, O k ≤ W.ι ⁻¹ᵁ N y ⊓ M.U k := fun k z hz => ⟨hz.1.2, hz.2⟩
  have ev : ∀ k (z : W.toScheme) (hz : z ∈ O k),
      gm (𝟙 _) z (O k) (res (ly k) (σ y k) * (res (lx k) (σ x k))⁻¹) =
        gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ := fun k z hz => by
    rw [map_mul, map_inv, gm_res _ z (ly k) hz, gm_res _ z (lx k) hz]
  obtain ⟨r, hr⟩ := glue_unit _ O l0 (fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hM z
      exact Opens.mem_iSup.2 ⟨k, show z ∈ O k from ⟨hz, hk⟩⟩) (fun k => res (ly k) (σ y k) * (res (lx k) (σ x k))⁻¹)
    (fun k k' z hz => by
      have h1 : z ∈ O k := hz.1
      have h2 : z ∈ O k' := hz.2
      have hx : W.ι z ∈ N x := h1.1.1
      have hy : W.ι z ∈ N y := h1.1.2
      have hk : z ∈ M.U k := h1.2
      have hk' : z ∈ M.U k' := h2.2
      rw [ev k z h1, ev k' z h2, hσ x z k k' hx hk hk', hσ y z k k' hy hk hk', mul_ringHom_units_ratio])
  refine ⟨r, fun z k hx hy hk => ?_⟩
  have hz : z ∈ O k := ⟨⟨hx, hy⟩, hk⟩
  rw [← gm_res _ z (l0 k) hz, hr k, ev k z hz]

theorem exists_ext (W : X.Opens) (hW : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)))
    (P Q : X.Opens) (r : Γ(W.toScheme, W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q)ˣ) :
    ∃ g : Γ(X, P ⊓ Q)ˣ, ∀ z : W.toScheme, W.ι z ∈ P → W.ι z ∈ Q → gm W.ι z (P ⊓ Q) g = gm (𝟙 _) z _ r := by
  have hle : P ⊓ Q ⊓ W ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q) := fun p hp => by
    have hpW : p ∈ W := hp.2
    have hpP : p ∈ P := hp.1.1
    have hpQ : p ∈ Q := hp.1.2
    have hm : (⟨p, hpW⟩ : W.toScheme) ∈ W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q := ⟨hpP, hpQ⟩
    exact W.ι.apply_mem_image_iff.2 hm
  obtain ⟨g, hg⟩ := exists_res_eq (inf_le_left : P ⊓ Q ⊓ W ≤ P ⊓ Q) (hW _) (res hle (imU W.ι _ r))
  refine ⟨g, fun z hP hQ => ?_⟩
  have hz : W.ι z ∈ P ⊓ Q ⊓ W := ⟨⟨hP, hQ⟩, z.2⟩
  rw [← gm_res W.ι z inf_le_left hz, hg, gm_res W.ι z hle hz]
  have := gm_imU W.ι (𝟙 _) z _ (show z ∈ W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q from ⟨hP, hQ⟩) r
  rwa [Category.id_comp] at this

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace

theorem commGroup_cocycle_mul_inv_mul_mul_inv {G : Type} [CommGroup G] (a b c : G) : b * a⁻¹ * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem commGroup_inv_eq_conj_twist_identity {G : Type} [CommGroup G] (a b g : G) : a⁻¹ = g * b * a⁻¹ * g⁻¹ * b⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.ExtendClass


open GlobalTheory.GlueLineBundle TopologicalSpace GlobalTheory.ExtendClass in
theorem GlobalTheory.extend_class_of_locally_trivial : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ W : X.Opens, (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic W.toScheme, (∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0) → ∃ c' : Pic X, GlobalTheory.CechPic.pull W.ι c' = c := by
  intro X _ hX W hW c hc
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  have hbij : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)) :=
    ((extension_over_codim_two X hX).1 W hW).1
  choose N hN ht using hc
  have ht' : ∀ x, ∃ t : LB.Gen (M.pull (X.homOfLE (inf_le_right : N x ⊓ W ≤ W))), t.IsGen := fun x =>
    (cls_eq_zero_iff (pull_isLB hM _)).1 (ht x)
  choose t htg using ht'
  choose σ hσ using fun x => exists_sigma W (N x) (t x) (htg x)
  choose r hr using exists_ratio W hM N σ hσ
  choose g hg using fun x y => exists_ext W hbij (N x) (N y) (r x y)
  let L : LB X := ⟨↥X, N, g⟩
  have hgr : ∀ x y (z : W.toScheme) k, W.ι z ∈ N x → W.ι z ∈ N y → z ∈ M.U k →
      gm W.ι z (N x ⊓ N y) (g x y) = gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ :=
    fun x y z k hx hy hk => (hg x y z hx hy).trans (hr x y z k hx hy hk)
  have hL : L.IsLB :=
    { cover := top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hN x⟩
      g_self := fun x => eq_of_gm_ι W hbij fun z hz => by
        obtain ⟨k, hk⟩ := exists_chart hM z
        dsimp only [L]
        rw [gm_res W.ι z _ hz, map_one]
        exact (hgr x x z k hz hz hk).trans (mul_inv_cancel _)
      cocycle := fun x y w => eq_of_gm_ι W hbij fun z hz => by
        obtain ⟨k, hk⟩ := exists_chart hM z
        have hx : W.ι z ∈ N x := hz.1.1
        have hy : W.ι z ∈ N y := hz.1.2
        have hw : W.ι z ∈ N w := hz.2
        have h1 : W.ι z ∈ N x ⊓ N y := ⟨hx, hy⟩
        have h2 : W.ι z ∈ N y ⊓ N w := ⟨hy, hw⟩
        have h3 : W.ι z ∈ N x ⊓ N w := ⟨hx, hw⟩
        dsimp only [L] at hz ⊢
        rw [map_mul, gm_res W.ι z _ hz, gm_res W.ι z _ hz, gm_res W.ι z _ hz]
        rw [hgr x y z k hx hy hk, hgr y w z k hy hw hk, hgr x w z k hx hw hk, commGroup_cocycle_mul_inv_mul_mul_inv] }
  have hle : ∀ p : (PUnit → L.ι) × M.ι, (L.pull W.ι).U p.1 ⊓ M.U p.2 ≤ W.ι ⁻¹ᵁ N (p.1 PUnit.unit) ⊓ M.U p.2 :=
    fun p z hz => ⟨mem_pull.1 hz.1, hz.2⟩
  let w : LB.Iso M (L.pull W.ι) := ⟨fun p => res (hle p) (σ (p.1 PUnit.unit) p.2)⁻¹⟩
  have ew : ∀ (p : (PUnit → L.ι) × M.ι) (z : W.toScheme) (hz : z ∈ (L.pull W.ι).U p.1 ⊓ M.U p.2),
      gm (𝟙 _) z _ (w.s p) = (gm (𝟙 _) z _ (σ (p.1 PUnit.unit) p.2))⁻¹ := fun p z hz =>
    (gm_res _ z (hle p) hz _).trans (map_inv _ _)
  have hw : w.IsGen := by
    rintro ⟨J, k⟩ ⟨J', k'⟩
    apply unit_ext
    intro z hz
    have hj : W.ι z ∈ L.U (J PUnit.unit) := mem_pull.1 hz.1.1
    have hj' : W.ι z ∈ L.U (J' PUnit.unit) := mem_pull.1 hz.2.1
    have hk : z ∈ M.U k := hz.1.2
    have hk' : z ∈ M.U k' := hz.2.2
    have e := gm_div_g (L := L) (L' := M) (F := W.ι) (𝟙 _) z (J PUnit.unit) (J' PUnit.unit) k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    have e' : gm (𝟙 _) z _ ((LB.div (L.pull W.ι) M).g (J, k) (J', k')) = _ := e
    refine (gm_res _ z inf_le_left hz _).trans ?_
    rw [map_mul, gm_res _ z inf_le_right hz, e', ew _ z hz.1, ew _ z hz.2]
    show _ = gm W.ι z (N (J PUnit.unit) ⊓ N (J' PUnit.unit)) (g (J PUnit.unit) (J' PUnit.unit)) * _ * _
    rw [hgr _ _ z k hj hj' hk, hσ (J' PUnit.unit) z k k' hj' hk hk']
    exact commGroup_inv_eq_conj_twist_identity _ _ _
  refine ⟨cls L hL, ?_⟩
  rw [← cls_pull hL W.ι (pull_isLB hL _)]
  exact (cls_eq_iff _ _).2 (LBIso.symm ⟨w, hw⟩)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardExtendOfLocallyTrivialNormalCodimTwoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicard_extend_of_locally_trivial_normal_codimTwo : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ W : X.Opens, (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic W.toScheme, (∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0) → ∃ c' : Pic X, GlobalTheory.CechPic.pull W.ι c' = c := by
  first | exact @GlobalTheory.extend_class_of_locally_trivial | exact GlobalTheory.extend_class_of_locally_trivial | (intros; apply GlobalTheory.extend_class_of_locally_trivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPicardClassExtendsAbelianScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DoubleClassExtension

theorem two_smul_extends : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V : A.left.Opens), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∀ c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE (le_sup_right : V ≤ A.hom ⁻¹ᵁ U ⊔ V)) c = 0 → ∃ c' : Pic A.left, GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c' = 2 • c := by
  intro S _ _ hS A _ hA U V hU hV c hc
  haveI : Smooth A.hom := hA.smooth
  haveI : GeometricallyConnected A.hom := hA.geomConnected
  haveI : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth A.hom
  haveI : GlobalTheory.IsNormalScheme S := GlobalTheory.IsNormalScheme.of_pred hS
  haveI : GlobalTheory.IsNormalScheme A.left := GlobalTheory.isNormalScheme_of_smooth A.hom
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hbig := GlobalTheory.T.mem_preimage_sup_of_stalk_krullDim_le_one_flat A.left S A.hom V U hV hU
  obtain ⟨Y, x, a, v, p, e, _, hxs, hxsurj, hpv, hmem, hsm2, hgi2, he⟩ := GlobalTheory.T.exists_parameterScheme_triples_abelianScheme S A hA V hV
  haveI := hxs
  haveI := hxsurj
  have h2 := GlobalTheory.T.cechPicard_two_nsmul_pullback_eq_zero_on_tripleParameterScheme S hS A hA U V (A.hom ⁻¹ᵁ U ⊔ V) le_sup_right hU hV le_sup_left le_rfl c hc
    Y x a v p e hpv hmem hsm2 hgi2 he
  haveI : GlobalTheory.IsNormalScheme Y.left := GlobalTheory.isNormalScheme_of_smooth x.left
  have hbigY := GlobalTheory.T.flat_preimage_contains_codim_le_one_points A.left Y.left x.left _ hbig
  have hloc := GlobalTheory.T.picardClass_locally_trivial_of_trivial_smooth_normal_cover A.left Y.left x.left (GlobalTheory.IsNormalScheme.pred _) _ hbigY (2 • c) h2
  exact GlobalTheory.T.cechPicard_extend_of_locally_trivial_normal_codimTwo A.left (GlobalTheory.IsNormalScheme.pred _) _ hbig (2 • c) hloc

end GlobalTheory.DoubleClassExtension
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPicardClassExtendsAbelianSchemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_smul_picardClass_extends_abelianScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V : A.left.Opens), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∀ c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE (le_sup_right : V ≤ A.hom ⁻¹ᵁ U ⊔ V)) c = 0 → ∃ c' : Pic A.left, GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c' = 2 • c := by
  first | exact @GlobalTheory.DoubleClassExtension.two_smul_extends | exact GlobalTheory.DoubleClassExtension.two_smul_extends | (intros; apply GlobalTheory.DoubleClassExtension.two_smul_extends <;> assumption)
end
