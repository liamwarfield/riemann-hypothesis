module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelForm
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isNormalScheme_genericFibre {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : @IsFractionRing O _ F _ β.toAlgebra) {X : Scheme.{0}} (s : X ⟶ Sp O)
    [GlobalTheory.IsNormalScheme X] : GlobalTheory.IsNormalScheme (pullback s (spMap β)) := by
  rename_i hX
  obtain ⟨hd, hi⟩ := hX
  let _ : Algebra O F := β.toAlgebra
  have : IsLocalization (nonZeroDivisors O) F := h
  have hfl : Flat (spMap β) := by
    change Flat (Spec.map (CommRingCat.ofHom β))
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (nonZeroDivisors O))
  have hso : SurjectiveOnStalks (spMap β) := by
    change SurjectiveOnStalks (Spec.map (CommRingCat.ofHom β))
    rw [HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)]
    exact RingHom.surjectiveOnStalks_of_isLocalization (M := nonZeroDivisors O) F
  have : SurjectiveOnStalks (pullback.fst s (spMap β)) :=
    @MorphismProperty.pullback_fst _ _ @SurjectiveOnStalks _ _ _ s (spMap β) _
      (@MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStableUnderBaseChange _ _ _
        SurjectiveOnStalks.stableUnderBaseChange _ _ s) hso
  have iso : ∀ x, (X.presheaf.stalk (pullback.fst s (spMap β) x)) ≃+* ((pullback s (spMap β)).presheaf.stalk x) :=
    fun x => (@asIso _ _ _ _ _ (GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap β)) x)).commRingCatIsoToRingEquiv
  refine ⟨fun x => ?_, fun x => ?_⟩
  · exact (iso x).symm.toMulEquiv.isDomain _
  · exact IsIntegrallyClosed.of_equiv (iso x)

theorem isIso_of_isFinite_of_common_dense_open {U Y T : Scheme.{0}} [IsLocallyNoetherian T]
    [IsReduced Y] [GlobalTheory.IsNormalScheme T] (j : U ⟶ Y) [IsDominant j] (e : Y ⟶ T) [IsFinite e]
    [IsOpenImmersion (j ≫ e)] [IsDominant (j ≫ e)] : IsIso e := by
  obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := GlobalTheory.existsUnique_lift_of_isOpenImmersion_of_isDominant (j ≫ e) e j (𝟙 T)
    (by rw [Category.comp_id])
  have hce : e ≫ c = 𝟙 Y := GlobalTheory.lift_unique_of_isDominant j e (c := e ≫ c) (c' := 𝟙 Y)
    (by rw [← Category.assoc, hc₁, Category.comp_id]) (by rw [Category.assoc, hc₂, Category.comp_id, Category.id_comp])
  exact ⟨⟨c, hce, hc₂⟩⟩

theorem isPullback_genericFibre_of_isFinite {O₀ O K F : Type} [CommRing O₀] [CommRing O] [Field K]
    [Field F] (β₀ : O₀ →+* K) (β : O →+* F) (b : O₀ →+* O) (i : K →+* F)
    (h₀ : @IsFractionRing O₀ _ K _ β₀.toAlgebra) (h : @IsFractionRing O _ F _ β.toAlgebra)
    (hb : β.comp b = i.comp β₀) [Smooth (spMap i)]
    {X Y U : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [GlobalTheory.IsNormalScheme Y]
    (sX : X ⟶ Sp O₀) [LocallyOfFiniteType sX] (sY : Y ⟶ Sp O) (sU : U ⟶ Sp K)
    (π : Y ⟶ X) (w : π ≫ sX = sY ≫ spMap b) [IsFinite (pullback.lift π sY w)]
    (jX : U ⟶ pullback sX (spMap β₀)) [IsOpenImmersion jX] [IsDominant jX]
    (hjX : jX ≫ pullback.snd _ _ = sU)
    (jY : pullback sU (spMap i) ⟶ pullback sY (spMap β)) [IsDominant jY]
    (hjY : jY ≫ pullback.snd _ _ = pullback.snd _ _)
    (e : pullback sY (spMap β) ⟶ pullback sX (spMap β₀))
    (he₁ : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π)
    (he₂ : e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap i)
    (hj : jY ≫ e = pullback.fst _ _ ≫ jX) :
    IsPullback e (pullback.snd _ _) (pullback.snd sX (spMap β₀)) (spMap i) := by
  have hXK : GlobalTheory.IsNormalScheme (pullback sX (spMap β₀)) := isNormalScheme_genericFibre β₀ h₀ sX
  have hYF : GlobalTheory.IsNormalScheme (pullback sY (spMap β)) := isNormalScheme_genericFibre β h sY

  have hspec : spMap i ≫ spMap β₀ = spMap β ≫ spMap b := by
    change Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom β₀) =
      Spec.map (CommRingCat.ofHom β) ≫ Spec.map (CommRingCat.ofHom b)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]

  obtain ⟨g, hg₁, hg₂⟩ : ∃ g : pullback sY (spMap β) ⟶
      pullback (pullback.snd sX (spMap β₀)) (spMap i),
      g ≫ pullback.fst _ _ = e ∧ g ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift e (pullback.snd _ _) he₂, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  obtain ⟨r, hr₁, hr₂⟩ : ∃ r : pullback (pullback.snd sX (spMap β₀)) (spMap i) ⟶ pullback sX (spMap b),
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ ∧
      r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap β := by
    refine ⟨pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spMap β) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
      hspec, Category.assoc]

  have outer := (IsPullback.of_hasPullback (pullback.snd sX (spMap β₀)) (spMap i)).paste_horiz
    (IsPullback.of_hasPullback sX (spMap β₀))
  have sq₁ : IsPullback (pullback.snd _ _) r (spMap β) (pullback.snd sX (spMap b)) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst sX (spMap b)) (v₂₂ := spMap b) (h₃₁ := sX) ?_
      hr₂.symm (IsPullback.of_hasPullback sX (spMap b)).flip
    rw [hr₁, ← hspec]
    exact outer.flip

  have sq₂ : IsPullback g (pullback.fst sY (spMap β)) r (pullback.lift π sY w) := by
    refine IsPullback.of_right ?_ ?_ sq₁
    · rw [hg₂, pullback.lift_snd]
      exact (IsPullback.of_hasPullback sY (spMap β)).flip
    · apply pullback.hom_ext
      · rw [Category.assoc, hr₁, ← Category.assoc, hg₁, he₁, Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, hr₂, ← Category.assoc, hg₂, Category.assoc, pullback.lift_snd,
          pullback.condition]
  have hgfin : IsFinite g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) sq₂.flip inferInstance

  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : pullback sU (spMap i) ⟶ pullback (pullback.snd sX (spMap β₀)) (spMap i),
      m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ jX ∧ m ≫ pullback.snd _ _ = pullback.snd _ _ := by
    refine ⟨pullback.lift (pullback.fst _ _ ≫ jX) (pullback.snd _ _) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, hjX, pullback.condition]
  have hjm : jY ≫ g = m := by
    apply pullback.hom_ext
    · rw [Category.assoc, hg₁, hj, hm₁]
    · rw [Category.assoc, hg₂, hjY, hm₂]
  have sq₃ : IsPullback m (pullback.fst sU (spMap i)) (pullback.fst _ _) jX := by
    refine IsPullback.of_right ?_ hm₁ (IsPullback.of_hasPullback (pullback.snd sX (spMap β₀)) (spMap i)).flip
    rw [hm₂, hjX]
    exact (IsPullback.of_hasPullback sU (spMap i)).flip
  have hmo : IsOpenImmersion m :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) sq₃.flip inferInstance
  have : UniversallyOpen (pullback.fst (pullback.snd sX (spMap β₀)) (spMap i)) :=
    UniversallyOpen.of_flat _
  have hmd : IsDominant m := by
    have := GlobalTheory.isDominant_pullback_fst_of_isOpenMap jX
      (pullback.fst (pullback.snd sX (spMap β₀)) (spMap i)) (Scheme.Hom.isOpenMap _)
    rw [← sq₃.isoPullback_hom_fst]
    infer_instance

  have hPn : GlobalTheory.IsNormalScheme (pullback (pullback.snd sX (spMap β₀)) (spMap i)) :=
    ⟨fun x => (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (pullback.fst _ _)
        (fun y => ⟨hXK.isDomain_stalk y, hXK.isIntegrallyClosed_stalk y⟩) x).1,
      fun x => (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (pullback.fst _ _)
        (fun y => ⟨hXK.isDomain_stalk y, hXK.isIntegrallyClosed_stalk y⟩) x).2⟩
  have : IsReduced (pullback sY (spMap β)) := by
    have : ∀ x, _root_.IsReduced ((pullback sY (spMap β)).presheaf.stalk x) :=
      fun x => by have := hYF.isDomain_stalk x; infer_instance
    exact isReduced_of_isReduced_stalk _
  have : IsOpenImmersion (jY ≫ g) := hjm ▸ hmo
  have : IsDominant (jY ≫ g) := hjm ▸ hmd
  have hgi : IsIso g := isIso_of_isFinite_of_common_dense_open jY g
  exact IsPullback.of_iso_pullback ⟨he₂⟩ (asIso g) hg₁ hg₂

theorem descends_of_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O₀ : Type) [CommRing O₀] (β₀ : O₀ →+* KA l) (C : Cpt Xo.s Xo.univ.t β₀) (b : O₀ →+* O) (_ : (ofModel Y).Above C b (pullback.fst _ _) Y.m0.toSABMap), IsDedFrac β₀ → IsDedFrac β → β.comp b = (IntermediateField.inclusion c.le).toRingHom.comp β₀ → Y.Descends := by
  intro E _ _ _ H D l Xo c O _ β Y O₀ _ β₀ C b A hβ₀ hβ hb

  have hsm : Smooth (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    change Smooth (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion c.le).toRingHom))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    let _ : Algebra (KA l) c.F := (IntermediateField.inclusion c.le).toRingHom.toAlgebra
    have : IsScalarTower ℚ (KA l) c.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : FiniteDimensional ℚ c.F := c.fin
    have : FiniteDimensional (KA l) c.F := Module.Finite.of_restrictScalars_finite ℚ (KA l) c.F
    have : Algebra.IsSeparable (KA l) c.F := Algebra.IsAlgebraic.isSeparable_of_perfectField
    have : Algebra.FormallyEtale (KA l) c.F := Algebra.FormallyEtale.of_isSeparable _ _
    have : Algebra.FinitePresentation (KA l) c.F :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    show Algebra.Smooth (KA l) c.F
    exact ⟨inferInstance, inferInstance⟩

  have hCn : GlobalTheory.IsNormalScheme C.X := ⟨fun x => (C.normal x).1, fun x => (C.normal x).2⟩
  have hYn : GlobalTheory.IsNormalScheme Y.X := ⟨fun x => (Y.normal x).1, fun x => (Y.normal x).2⟩
  have hCft : LocallyOfFiniteType C.s := by
    obtain ⟨N, i, hi, hcomp⟩ := C.proj
    have := isProper_str O₀ N
    rw [← hcomp]
    infer_instance
  obtain ⟨π, hπ, hfin, hjc, φμ, hmu, hφc⟩ : ∃ (π : Y.X ⟶ C.X) (hπ : π ≫ C.s = Y.s ≫ spMap b),
      IsFinite (pullback.lift π Y.s hπ) ∧
      (Y.jQ ≫ pullback.fst _ _) ≫ π = pullback.fst _ _ ≫ C.jQ ≫ pullback.fst _ _ ∧
      ∃ φμ : Y.t.G.left ⟶ C.t.G.left, IsGrpPullback Y.t.G C.t.G π φμ ∧
        Y.m.φ ≫ φμ = Y.m0.toSABMap.φ ≫ C.m.φ :=
    ⟨A.π, A.π_over, A.fin, A.j_comm, A.mu.φ, A.mu.cart, A.φ_comm⟩
  have hspec : spMap β ≫ spMap b = spMap (IntermediateField.inclusion c.le).toRingHom ≫ spMap β₀ := by
    change Spec.map (CommRingCat.ofHom β) ≫ Spec.map (CommRingCat.ofHom b) =
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion c.le).toRingHom) ≫
        Spec.map (CommRingCat.ofHom β₀)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]

  obtain ⟨e, he₁, he₂⟩ : ∃ e : pullback Y.s (spMap β) ⟶ pullback C.s (spMap β₀),
      e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π ∧
      e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    refine ⟨pullback.lift (pullback.fst _ _ ≫ π)
      (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion c.le).toRingHom) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, hπ, ← Category.assoc, pullback.condition, Category.assoc, hspec,
      Category.assoc]
  have hj : Y.jQ ≫ e = pullback.fst _ _ ≫ C.jQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, he₁, ← Category.assoc, hjc, Category.assoc]
    · rw [Category.assoc, he₂, ← Category.assoc, Y.jQ_over, Category.assoc, C.jQ_over,
        pullback.condition]
  have : IsOpenImmersion C.jQ := C.jQ_open
  have : IsDominant C.jQ := ⟨C.jQ_dense⟩
  have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  have hpb := isPullback_genericFibre_of_isFinite β₀ β b (IntermediateField.inclusion c.le).toRingHom
    hβ₀.2.2 hβ.2.2 hb C.s Y.s Xo.s π hπ C.jQ C.jQ_over Y.jQ Y.jQ_over e he₁ he₂ hj

  have hCm : IsGrpPullback Xo.univ.t.G C.t.G (C.jQ ≫ pullback.fst _ _) C.m.φ := C.m.cart
  obtain ⟨φK, hφK₁, hφK₂⟩ : ∃ φK : Xo.univ.t.G.left ⟶ pullback C.t.G.hom (pullback.fst C.s (spMap β₀)),
      φK ≫ pullback.fst _ _ = C.m.φ ∧ φK ≫ pullback.snd _ _ = Xo.univ.t.G.hom ≫ C.jQ := by
    refine ⟨pullback.lift C.m.φ (Xo.univ.t.G.hom ≫ C.jQ) ?_, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
    rw [hCm.1.w, Category.assoc]
  have hGK := isGrpPullback_pullback C.t.G (pullback.fst C.s (spMap β₀))
  have h3 : IsGrpPullback Xo.univ.t.G ((Over.pullback (pullback.fst C.s (spMap β₀))).obj C.t.G)
      C.jQ φK := by
    refine IsGrpPullback.cancel hGK ?_ hφK₂
    have e1 : φK ≫ pullback.fst C.t.G.hom (pullback.fst C.s (spMap β₀)) = C.m.φ := hφK₁
    rw [e1]
    exact hCm

  have h6 := isGrpPullback_pullback Y.t.G (pullback.fst Y.s (spMap β))
  obtain ⟨φ₂, hφ₂₁, hφ₂₂⟩ : ∃ φ₂ : pullback Y.t.G.hom (pullback.fst Y.s (spMap β)) ⟶
      pullback C.t.G.hom (pullback.fst C.s (spMap β₀)),
      φ₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φμ ∧ φ₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ e := by
    refine ⟨pullback.lift (pullback.fst _ _ ≫ φμ) (pullback.snd _ _ ≫ e) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, hmu.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      he₁]
  have h7 : IsGrpPullback ((Over.pullback (pullback.fst Y.s (spMap β))).obj Y.t.G)
      ((Over.pullback (pullback.fst C.s (spMap β₀))).obj C.t.G) e φ₂ := by
    refine IsGrpPullback.cancel hGK ?_ hφ₂₂
    have e1 : φ₂ ≫ pullback.fst C.t.G.hom (pullback.fst C.s (spMap β₀)) =
        pullback.fst Y.t.G.hom (pullback.fst Y.s (spMap β)) ≫ φμ := hφ₂₁
    rw [e1, he₁]
    exact IsGrpPullback.comp h6 hmu

  have hYm : IsGrpPullback Y.oF.t.G Y.t.G (Y.jQ ≫ pullback.fst _ _) Y.m.φ := Y.m.cart
  obtain ⟨ψ, hψ₁, hψ₂⟩ : ∃ ψ : Y.oF.t.G.left ⟶ pullback Y.t.G.hom (pullback.fst Y.s (spMap β)),
      ψ ≫ pullback.fst _ _ = Y.m.φ ∧ ψ ≫ pullback.snd _ _ = Y.oF.t.G.hom ≫ Y.jQ := by
    refine ⟨pullback.lift Y.m.φ (Y.oF.t.G.hom ≫ Y.jQ) ?_, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
    rw [hYm.1.w, Category.assoc]
  have hm0 := Y.m0.toSABMap.cart.1.w
  have h10 : ψ ≫ φ₂ = Y.m0.toSABMap.φ ≫ φK := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφ₂₁, ← Category.assoc, hψ₁, hφc, Category.assoc, hφK₁]
    · rw [Category.assoc, hφ₂₂, ← Category.assoc, hψ₂, Category.assoc, hj, Category.assoc, hφK₂,
        ← Category.assoc, ← Category.assoc, hm0]
  unfold Model.Descends
  exact ⟨_, pullback.snd C.s (spMap β₀), (Over.pullback (pullback.fst C.s (spMap β₀))).obj C.t.G,
    inferInstance, C.jQ, φK, e, (Over.pullback (pullback.fst Y.s (spMap β))).obj Y.t.G, inferInstance,
    pullback.fst Y.t.G.hom (pullback.fst Y.s (spMap β)), φ₂, ψ, C.jQ_open, C.jQ_over, h3, hpb, hj,
    h6, h7, hψ₁, hψ₂, h10⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescendsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.model_finite_over_moduliModel_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O₀ : Type) [CommRing O₀] (β₀ : O₀ →+* KA l) (C : Cpt Xo.s Xo.univ.t β₀) (b : O₀ →+* O) (_ : (ofModel Y).Above C b (pullback.fst _ _) Y.m0.toSABMap), IsDedFrac β₀ → IsDedFrac β → β.comp b = (IntermediateField.inclusion c.le).toRingHom.comp β₀ → Y.Descends := by
  first | exact @GlobalTheory.descends_of_above | exact GlobalTheory.descends_of_above | (intros; apply GlobalTheory.descends_of_above <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LamIsoOfPairings
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PairingDetermines

open Out CommutatorPairing DescentPairing PrimCocycle IsoDescent

section OnePoint

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A}

theorem exists_gen_transl (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (cb : CubicalStr A L) {T : Over S} (p₀ : T.left)
    (hT : ∀ p : T.left, p = p₀) (n : ℕ) (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A x).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), y ^ n = 1 → WeilIs A L.L n x y c →
        ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J), Good L.L z J →
          val u (lift t ((t ≫ y) * a)).left z J = val u (lift t a).left z J * gm t.left z ⊤ c := by
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, hu, fun y c hy hc Z t a z J hJ => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff L.isLB θx θy c).1 ((GlobalLift.weilIs_iff_commIsOf hG hA L.isLB θx θy c).1 hc)
  obtain ⟨s, hs⟩ := vu _ t z J hJ
  obtain ⟨s', hs'⟩ := vy _ t z J hJ
  have k₁ := hcm _ t a z J hJ
  have k₂ := cubN_transl (isCub_cubV cb hJ) n (t ≫ θy.pt) a (t ≫ θx.pt)
    ((map_pow (preHom t) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' a
  have t₂ := hs' ((t ≫ θx.pt) * a)
  apply Additive.ofMul.injective
  have E := fun {p q : (Z.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂

end OnePoint

section Field

variable {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A]

theorem exists_gen_lam (hG : GlobalFnsSt) (hC : CubeSt) (P : PolAV (Sp k)) (α : A ⟶ P.A) [IsMonHom α] (d n : ℕ)
    (x : 𝟙_ (Over (Sp k)) ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb P.L
        (fun I => (mulA A n).left ≫ (lift (toUnit A ≫ x) (𝟙 A)).left ≫ lamφ A I ≫ α.left) (fun I => lamε I * d)),
      u.IsGen ∧ ∀ (y : 𝟙_ (Over (Sp k)) ⟶ A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
        WeilIs P.A P.L n (x ≫ α) (y ≫ α) c → ∀ (z : A.left) (J), Good P.L z J →
          val u ((toUnit A ≫ y) * 𝟙 A).left z J = val u (𝟙 _) z J * gm (toUnit A).left z ⊤ (c ^ d) := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let T := 𝟙_ (Over (Sp k))
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hpow : ∀ y : T ⟶ A, y ^ n = 1 → (y ≫ α) ^ n = 1 := fun y hy => by
    rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_transl hG P.isAb cb p₀ hT n (x ≫ α) (hpow x hx)
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ α).left, (1 : T ⟶ P.A).left] ![-1, 1] p₀ hT
  obtain ⟨u₁, hu₁, v₁⟩ := exists_gen P.isLB
    (φ' := fun I => (mulA A n).left ≫ (lift (toUnit A ≫ x) (𝟙 A)).left ≫ lamφ A I ≫ α.left) (ε' := lamε)
    (fun U _ h => by
      have e₀ : mulA A n ≫ lift (toUnit A ≫ x) (𝟙 A) = lift (toUnit A ≫ x) (𝟙 A ^ n) := by
        rw [comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e₁ : lift (toUnit A) α ≫ mulT P.A T n ≫ translPt P.A (x ≫ α) = ((toUnit A ≫ x) * 𝟙 A ^ n) ≫ α := by
        rw [← Category.assoc, mulT, comp_lift, lift_translPt, lift_fst, MonObj.comp_pow, lift_snd, MonObj.mul_comp,
          MonObj.pow_comp, Category.id_comp, Category.assoc]
      have e₂ : lift (toUnit A) α ≫ snd T P.A ^ n = (𝟙 A ^ n) ≫ α := by
        rw [MonObj.comp_pow, lift_snd, MonObj.pow_comp, Category.id_comp]
      have e₃ : toUnit A ≫ (1 : T ⟶ P.A) = (1 : A ⟶ A) ≫ α := by rw [MonObj.comp_one, MonObj.one_comp]
      have e := prod_lam (toUnit A ≫ x) (𝟙 A ^ n) (fun q => h (q ≫ α.left))
      refine Eq.trans ?_ (e.symm.trans (Finset.prod_congr rfl fun I _ => by
        rw [← e₀, Over.comp_left, Category.assoc, Category.assoc]))
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, ← Over.comp_left, e₁, e₂, e₃, Category.assoc, zpow_neg, zpow_one, _root_.mul_one]
      ac_rfl)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₀ (lift (toUnit A) α).left) (LB.pullGen P.L _ _ σ (toUnit A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  obtain ⟨u, hu, v⟩ := WeilIsogeny.exists_gen_pow (ε' := fun I => lamε I * d) d (fun _ => rfl) u₁ hu₁
  refine ⟨u, hu, fun y c hy hc z J hJ => ?_⟩
  have w : ∀ a : A ⟶ A, val u a.left z J =
      (val u₀ (lift (toUnit A) (a ≫ α)).left z J * val σ (toUnit A).left z J) ^ d := fun a => by
    rw [v, v₁ _ _ z J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      comp_toUnit]
  have w₀ := v₀ (y ≫ α) c (hpow y hy) hc A (toUnit A) (𝟙 A ≫ α) z J hJ
  refine (w _).trans (Eq.trans ?_ (congrArg (· * _) (w (𝟙 A))).symm)
  rw [MonObj.mul_comp, Category.assoc, map_pow, ← mul_pow, mul_right_comm]
  exact congrArg (fun q => (q * _) ^ d) w₀

theorem exists_gen_axis {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : A.left ⟶ X) (e : ℤ) :
    ∃ u : LB.Gen (LB.LinComb L (fun I => (lift (𝟙 A) (1 : A ⟶ A)).left ≫ lamφ A I ≫ F) (fun I => lamε I * e)),
      u.IsGen := by
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ := PEmpty.elim) (ε := PEmpty.elim)
    (φ' := fun I => (lift (𝟙 A) (1 : A ⟶ A)).left ≫ lamφ A I ≫ F) (ε' := fun I => lamε I * e) (fun U _ h => by
      have q := prod_lam (𝟙 A) (1 : A ⟶ A) (fun q => h (q ≫ F) ^ e)
      rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel] at q
      refine (Fintype.prod_empty _).trans (q.symm.trans (Finset.prod_congr rfl fun I _ => ?_))
      rw [← zpow_mul, mul_comm e, Category.assoc]) (LB.oneGen L)
    (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact ⟨u, hu⟩

end Field

end GlobalTheory.PairingDetermines

namespace GlobalTheory

open PairingDetermines IsoDescent PrimCocycle

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalizedBoth
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GlobalTheory.TripleCompare

section Cech

variable {X Y Z : Scheme.{0}}

theorem gen_refine {A B : LB Y} (n : ℤ) (σ : B.ι → A.ι) (hle : ∀ i, B.U i ≤ A.U (σ i))
    (hg : ∀ i j, B.g i j = res (inf_le_inf (hle i) (hle j)) (A.g (σ i) (σ j)) ^ n)
    (h : ∃ t : LB.Gen A, t.IsGen) : ∃ t : LB.Gen B, t.IsGen := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun i => res (hle i) (t.s (σ i)) ^ n⟩, fun i j => ?_⟩
  have e := congrArg (res (inf_le_inf (hle i) (hle j))) (ht (σ i) (σ j))
  rw [map_mul, DVR.res_res', DVR.res_res'] at e
  rw [hg, map_zpow, map_zpow, DVR.res_res', DVR.res_res', ← mul_zpow]
  exact congrArg (· ^ n) e

theorem div_g_res (M L : LB Y) (p q : M.ι × L.ι) {V : Y.Opens}
    (h : V ≤ (M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2)) (h₁ : V ≤ M.U p.1 ⊓ M.U q.1)
    (h₂ : V ≤ L.U p.2 ⊓ L.U q.2) :
    res h ((LB.div M L).g p q) = res h₁ (M.g p.1 q.1) * (res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (DVR.res_res' _ _ _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (DVR.res_res' _ _ _))))

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem sum_g_res (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (j j' : K' ⊕ K → L.ι) {V : Y.Opens}
    (h : V ≤ LB.wchart L (Sum.elim φ' φ) j ⊓ LB.wchart L (Sum.elim φ' φ) j')
    (h₁ : V ≤ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ' (j' ∘ Sum.inl))
    (h₂ : V ≤ LB.wchart L φ (j ∘ Sum.inr) ⊓ LB.wchart L φ (j' ∘ Sum.inr)) :
    res h ((LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)).g j j') =
      res h₁ ((LB.LinComb L φ' ε').g (j ∘ Sum.inl) (j' ∘ Sum.inl)) *
        (res h₂ ((LB.LinComb L φ ε).g (j ∘ Sum.inr) (j' ∘ Sum.inr)))⁻¹ := by
  rw [DVR.linComb_g_res, DVR.linComb_g_res, DVR.linComb_g_res, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp]

theorem wchart_sum (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K' ⊕ K → L.ι) :
    LB.wchart L (Sum.elim φ' φ) j =
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := by
  refine le_antisymm (fun y hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩) fun y hy => ?_
  refine Set.mem_iInter.2 fun k => ?_
  rcases k with k | k
  · exact Set.mem_iInter.1 hy.1 k
  · exact Set.mem_iInter.1 hy.2 k

theorem lbIso_iff_gen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    Geo.Tor.LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔
      ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)), t.IsGen := by
  constructor
  · refine gen_refine (A := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) 1
      (fun j => (j ∘ Sum.inl, j ∘ Sum.inr)) (fun j => (wchart_sum φ φ' j).le) fun j j' => ?_
    have a := (wchart_sum φ φ' j).le
    have b := (wchart_sum φ φ' j').le
    refine (DVR.res_refl' _).symm.trans ((sum_g_res φ ε φ' ε' j j' le_rfl
      (inf_le_inf (a.trans inf_le_left) (b.trans inf_le_left))
      (inf_le_inf (a.trans inf_le_right) (b.trans inf_le_right))).trans (Eq.symm ?_))
    exact (zpow_one _).trans (div_g_res (LB.LinComb L φ' ε') (LB.LinComb L φ ε) _ _ _ _ _)
  · refine gen_refine (B := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) 1
      (fun p => Sum.elim p.1 p.2) (fun p => (wchart_sum φ φ' (Sum.elim p.1 p.2)).ge) fun p q => ?_
    refine (DVR.res_refl' _).symm.trans ((div_g_res (LB.LinComb L φ' ε') (LB.LinComb L φ ε) p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    exact (zpow_one _).trans (sum_g_res φ ε φ' ε' (Sum.elim p.1 p.2) (Sum.elim q.1 q.2) _ _ _)

theorem wchart_id (L : LB X) (j : PUnit.{1} → L.ι) :
    LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j = L.U (j ⟨⟩) :=
  le_antisymm (fun _ hy => Set.mem_iInter.1 hy PUnit.unit) fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem pull_id_g_res (L : LB X) (j j' : PUnit.{1} → L.ι) {V : X.Opens}
    (h : V ≤ LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j ⊓ LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j')
    (h' : V ≤ L.U (j ⟨⟩) ⊓ L.U (j' ⟨⟩)) :
    res h ((L.pull (𝟙 X)).g j j') = res h' (L.g (j ⟨⟩) (j' ⟨⟩)) := by
  rw [DVR.linComb_g_res, Fintype.prod_unique, zpow_one, DVR.tr_def L (ψ := 𝟙 X) h']
  exact DVR.pullU_of_eq_id _ rfl _ _ _ _ _

theorem lbIso_iff_pull_id (L M : LB X) :
    Geo.Tor.LBIso L M ↔ Geo.Tor.LBIso M (L.pull (𝟙 X)) := by
  constructor
  · refine gen_refine (A := LB.div M L) (B := LB.div (L.pull (𝟙 X)) M) (-1)
      (fun p => (p.2, p.1 ⟨⟩))
      (fun p => le_inf inf_le_right (inf_le_left.trans (wchart_id L p.1).le)) fun p q => ?_
    have a := (wchart_id L p.1).le
    have b := (wchart_id L q.1).le
    refine (DVR.res_refl' _).symm.trans ((div_g_res (L.pull (𝟙 X)) M p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    refine (zpow_neg_one _).trans ((congrArg (·⁻¹) (div_g_res M L (p.2, p.1 ⟨⟩) (q.2, q.1 ⟨⟩) _
      (inf_le_inf inf_le_right inf_le_right)
      (inf_le_inf (inf_le_left.trans a) (inf_le_left.trans b)))).trans ?_)
    refine (mul_inv_rev _ _).trans (congrArg₂ (· * ·) ((inv_inv _).trans ?_) rfl)
    exact (pull_id_g_res L p.1 q.1 _ _).symm
  · refine gen_refine (B := LB.div M L) (A := LB.div (L.pull (𝟙 X)) M) (-1)
      (fun p => (fun _ => p.2, p.1))
      (fun p => le_inf (inf_le_right.trans (wchart_id L fun _ => p.2).ge) inf_le_left) fun p q => ?_
    have a := (wchart_id L fun _ => p.2).ge
    have b := (wchart_id L fun _ => q.2).ge
    refine (DVR.res_refl' _).symm.trans ((div_g_res M L p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    refine (zpow_neg_one _).trans ((congrArg (·⁻¹) (div_g_res (L.pull (𝟙 X)) M (fun _ => p.2, p.1)
      (fun _ => q.2, q.1) _ (inf_le_inf (inf_le_right.trans a) (inf_le_right.trans b))
      (inf_le_inf inf_le_left inf_le_left))).trans ?_)
    refine (mul_inv_rev _ _).trans (congrArg₂ (· * ·) (inv_inv _) (congrArg (·⁻¹) ?_))
    exact pull_id_g_res L (fun _ => p.2) (fun _ => q.2) _ _

end Cech

section Clauses

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

end Clauses

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}
  {S S' : Scheme.{0}}

end Triples

end GlobalTheory.TripleCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueTwo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.GroupGlue

theorem exists_scheme {X : Scheme.{0}} {U V : X.Opens} {G₁ : Over U.toScheme} {G₂ : Over V.toScheme}
    {G₀ : Over (U ⊓ V).toScheme} {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left}
    (h₁ : IsPullback φ₁ G₀.hom G₁.hom (X.homOfLE inf_le_left))
    (h₂ : IsPullback φ₂ G₀.hom G₂.hom (X.homOfLE inf_le_right)) :
    ∃ (G : Over X) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsPullback ψ₁ G₁.hom G.hom U.ι ∧
      IsPullback ψ₂ G₂.hom G.hom V.ι ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  have : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁.flip inferInstance
  have : IsOpenImmersion φ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂.flip inferInstance
  have : IsOpenImmersion (pushout.inl φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.left))
  have : IsOpenImmersion (pushout.inr φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.right))
  have hc : ∀ z : (pushout φ₁ φ₂ : Scheme.{0}),
      z ∈ Set.range (pushout.inl φ₁ φ₂) ∨ z ∈ Set.range (pushout.inr φ₁ φ₂) := by
    intro z
    obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span φ₁ φ₂) z
    rcases i with _ | _ | _
    · refine Or.inl ⟨φ₁ x, Eq.trans ?_ hx⟩
      exact congrArg (fun g => g x) (colimit.w (span φ₁ φ₂) WalkingSpan.Hom.fst)
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  let π : pushout φ₁ φ₂ ⟶ X := pushout.desc (G₁.hom ≫ U.ι) (G₂.hom ≫ V.ι) (by
    rw [h₁.w_assoc, h₂.w_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι])
  have p1 : pushout.inl φ₁ φ₂ ≫ π = G₁.hom ≫ U.ι := pushout.inl_desc _ _ _
  have p2 : pushout.inr φ₁ φ₂ ≫ π = G₂.hom ≫ V.ι := pushout.inr_desc _ _ _
  have e1 (x : G₁.left) : π (pushout.inl φ₁ φ₂ x) = U.ι (G₁.hom x) := congrArg (fun g => g x) p1
  have e2 (x : G₂.left) : π (pushout.inr φ₁ φ₂ x) = V.ι (G₂.hom x) := congrArg (fun g => g x) p2
  have e3 (w : G₀.left) : pushout.inl φ₁ φ₂ (φ₁ w) = pushout.inr φ₁ φ₂ (φ₂ w) :=
    congrArg (fun g => g w) (pushout.condition (f := φ₁) (g := φ₂))
  refine ⟨Over.mk π, pushout.inl φ₁ φ₂, pushout.inr φ₁ φ₂, (IsOpenImmersion.isPullback _ _ _ _ p1 ?_).flip,
    (IsOpenImmersion.isPullback _ _ _ _ p2 ?_).flip, pushout.condition⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · have hy' : y.1 = (G₂.hom x).1 := hy.trans (e2 x)
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₂ x ⟨y.1, y.2, hy' ▸ (G₂.hom x).2⟩
          (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))
        exact ⟨φ₁ z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨G₁.hom y, (e1 y).symm⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · have hy' : y.1 = (G₁.hom x).1 := hy.trans (e1 x)
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₁ x ⟨y.1, hy' ▸ (G₁.hom x).2, y.2⟩
          (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))
        exact ⟨φ₂ z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨G₂.hom y, (e2 y).symm⟩

theorem exists_inf {X S : Scheme.{0}} {U V : X.Opens} (u : S ⟶ U) (v : S ⟶ V) (h : u ≫ U.ι = v ≫ V.ι) :
    ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v := by
  have hr : Set.range (u ≫ U.ι) ⊆ Set.range (U ⊓ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨(u z).2, ?_⟩
    rw [h]
    exact (v z).2
  refine ⟨IsOpenImmersion.lift _ _ hr, ?_, ?_⟩
  · rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
  · rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, h]

theorem exists_glue_two : ∀ (O : Type) [CommRing O] (X : Scheme.{0}) (U V : X.Opens) (G₁ : Over U.toScheme) [GrpObj G₁] (G₂ : Over V.toScheme) [GrpObj G₂] (G₀ : Over (U ⊓ V).toScheme) [GrpObj G₀] (a₁ : OAct O G₁) (a₂ : OAct O G₂) (a₀ : OAct O G₀) (φ₁ : G₀.left ⟶ G₁.left) (φ₂ : G₀.left ⟶ G₂.left), U ⊔ V = ⊤ → IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsGrpPullback G₀ G₁ (X.homOfLE inf_le_left) φ₁ → IsGrpPullback G₀ G₂ (X.homOfLE inf_le_right) φ₂ → (∀ x, (a₀.act x).left ≫ φ₁ = φ₁ ≫ (a₁.act x).left ∧ (a₀.act x).left ≫ φ₂ = φ₂ ≫ (a₂.act x).left) → ∃ (G : Over X) (_ : GrpObj G) (a : OAct O G) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G₁ G U.ι ψ₁ ∧ IsGrpPullback G₂ G V.ι ψ₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ ∧ ∀ x, (a₁.act x).left ≫ ψ₁ = ψ₁ ≫ (a.act x).left ∧ (a₂.act x).left ≫ ψ₂ = ψ₂ ≫ (a.act x).left := by
  intro O _ X U V G₁ i₁ G₂ i₂ G₀ _ a₁ a₂ a₀ φ₁ φ₂ hUV s₁ s₂ h₁ h₂ ha
  obtain ⟨G, ψ₁, ψ₂, p₁, p₂, hφ⟩ := exists_scheme h₁.1 h₂.1
  have m₁ : Mono ψ₁ := by
    have : IsOpenImmersion ψ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₁.flip inferInstance
    infer_instance
  have m₂ : Mono ψ₂ := by
    have : IsOpenImmersion ψ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₂.flip inferInstance
    infer_instance
  have base : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ →
      ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v := by
    intro S u v a b h
    have e₁ : a.left ≫ G₁.hom = u := Over.w a
    have e₂ : b.left ≫ G₂.hom = v := Over.w b
    refine exists_inf u v ?_
    rw [← e₁, ← e₂, Category.assoc, Category.assoc, ← p₁.w, ← p₂.w, reassoc_of% h]
  have common : ∀ {S : Scheme.{0}} (w : S ⟶ (U ⊓ V : X.Opens))
      (a : Over.mk (w ≫ X.homOfLE inf_le_left) ⟶ G₁) (b : Over.mk (w ≫ X.homOfLE inf_le_right) ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ c : Over.mk w ⟶ G₀, a.left = c.left ≫ φ₁ ∧ b.left = c.left ≫ φ₂ := by
    intro S w a b h
    refine ⟨Over.homMk (h₁.1.lift a.left w (Over.w a)) (h₁.1.lift_snd _ _ _), (h₁.1.lift_fst _ _ _).symm, ?_⟩
    rw [← cancel_mono ψ₂, ← h, Category.assoc, ← hφ]
    exact (h₁.1.lift_fst_assoc _ _ _ _).symm
  have cm : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a a' : Over.mk u ⟶ G₁) (b b' : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → a'.left ≫ ψ₁ = b'.left ≫ ψ₂ → (a * a').left ≫ ψ₁ = (b * b').left ≫ ψ₂ := by
    intro S u v a a' b b' h h'
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    obtain ⟨c', c₁', c₂'⟩ := common w a' b' h'
    have e₁ : (a * a').left = (c * c').left ≫ φ₁ := h₁.2 _ c c' a a' c₁ c₁'
    have e₂ : (b * b').left = (c * c').left ≫ φ₂ := h₂.2 _ c c' b b' c₂ c₂'
    rw [e₁, e₂, Category.assoc, Category.assoc, hφ]
  have ca : ∀ (x : O) {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → (a ≫ a₁.act x).left ≫ ψ₁ = (b ≫ a₂.act x).left ≫ ψ₂ := by
    intro x S u v a b h
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    rw [Over.comp_left, Over.comp_left, c₁, c₂]
    simp only [Category.assoc]
    rw [← reassoc_of% (ha x).1, ← reassoc_of% (ha x).2, hφ]
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) U.ι V.ι i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by
    cases i
    · exact inferInstanceAs (IsOpenImmersion U.ι)
    · exact inferInstanceAs (IsOpenImmersion V.ι)
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    have hx : x ∈ U ⊔ V := hUV ▸ trivial
    rcases hx with hx | hx
    · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · exact ⟨true, ⟨x, hx⟩, rfl⟩)
  let H : ∀ i : 𝒰.I₀, Over (𝒰.X i) := fun i => Bool.rec (motive := fun i => Over (T i)) G₁ G₂ i
  letI iH : ∀ i : 𝒰.I₀, GrpObj (H i) := fun i => Bool.rec (motive := fun i => GrpObj (H i)) i₁ i₂ i
  let ψ : ∀ i : 𝒰.I₀, (H i).left ⟶ G.left := fun i => Bool.rec (motive := fun i => (H i).left ⟶ G.left) ψ₁ ψ₂ i
  let α : ∀ i : 𝒰.I₀, OAct O (H i) := fun i => Bool.rec (motive := fun i => @OAct _ O _ (H i) (iH i)) a₁ a₂ i
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := by
    rintro (_ | _)
    exacts [p₁, p₂]
  have same : ∀ (i : 𝒰.I₀) {S : Scheme.{0}} {u v : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
      a.left ≫ ψ i = b.left ≫ ψ i → u = v := fun i S u v a b h => by
    rw [← cancel_mono (𝒰.f i), base_eq hψ a, base_eq hψ b, h]
  have hm : MulCompat ψ := by
    have d : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a a' : Over.mk u ⟶ H i) (b b' : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → a'.left ≫ ψ i = b'.left ≫ ψ i →
          (a * a').left ≫ ψ i = (b * b').left ≫ ψ i := by
      intro i S u v a a' b b' h h'
      obtain rfl := same i a b h
      rw [pt_ext hψ h, pt_ext hψ h']
    rintro (_ | _) (_ | _) S u v a a' b b' h h'
    · exact d _ S u v a a' b b' h h'
    · exact cm a a' b b' h h'
    · exact (cm b b' a a' h.symm h'.symm).symm
    · exact d _ S u v a a' b b' h h'
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  obtain ⟨A, hA⟩ := exists_oAct hG α (by
    have d : ∀ (x : O) (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → (a ≫ (α i).act x).left ≫ ψ i = (b ≫ (α i).act x).left ≫ ψ i := by
      intro x i S u v a b h
      obtain rfl := same i a b h
      rw [pt_ext hψ h]
    rintro x (_ | _) (_ | _) S u v a b h
    · exact d x _ S u v a b h
    · exact ca x a b h
    · exact (ca x b a h.symm).symm
    · exact d x _ S u v a b h)
  exact ⟨G, iG, A, ψ₁, ψ₂, isSemiAbelian_of_charts hG (by rintro (_ | _); exacts [s₁, s₂]), hG false, hG true, hφ,
    fun x => ⟨hA x false, hA x true⟩⟩

end GlobalTheory.GroupGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperZeroTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  haveI : Unique (Fin (0 + 1)) := ⟨⟨0⟩, fun i => Fin.ext (by have := i.isLt; omega)⟩
  haveI : IsIso (PSpace.str R 0) := by
    haveI : IsIso (GlobalTheory.ProjSpace.chartι R 0 0) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      rw [GlobalTheory.ProjSpace.opensRange_chartι, ← GlobalTheory.ProjSpace.iSup_chart R 0]
      apply le_antisymm (le_iSup _ 0)
      apply iSup_le
      intro i
      rw [Subsingleton.elim i 0]
    haveI : IsEmpty {j : Fin (0 + 1) // j ≠ 0} := ⟨fun j => j.2 (Subsingleton.elim _ _)⟩
    haveI : IsIso (GlobalTheory.ProjSpace.chartι R 0 0 ≫ PSpace.str R 0) := by
      rw [GlobalTheory.ProjSpace.chartι_str]
      exact inferInstanceAs (IsIso (Spec.map
        (MvPolynomial.isEmptyRingEquiv R {j : Fin (0 + 1) // j ≠ 0}).toCommRingCatIso.inv))
    exact IsIso.of_isIso_comp_left (GlobalTheory.ProjSpace.chartι R 0 0) _
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

end GlobalTheory.Models.Point

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjectAtMinimalPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem TObj.HasTh.unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (h : t.HasTh x v) (c : R) (hc : IsUnit c) :
    t.HasTh x (fun a => c * v a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, k1, k2, k3, k4, k5, k6, k7, k8⟩ := h3 p
  have hu : IsUnit (V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
    (hc.map _).map _
  obtain ⟨u', hu'⟩ : ∃ u' : Γ((Out.overRes (T := Over.mk x) V).left, ⊤)ˣ,
      u'.val = V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := hu
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, k1, k2, k3, k4, k5, k6, k7, fun i => ?_⟩
  have e := k8 i
  have e1 : V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c * v i)) =
      V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
        V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) := by
    rw [map_mul]
    exact map_mul _ _ _
  refine e1.trans ?_
  rw [Units.val_mul, _root_.mul_assoc, hu']
  exact congrArg (fun y => V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * y) e

theorem exists_object_at_minimalPrime :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ w w' d, Out.Laws → Out.Laws2 → 3 ≤ N' → Odd N' → Countable o → GoodClass em C Mat κ w w' d → ∀ 𝔭 ∈ (thIdeal em C).minimalPrimes, ∃ t v, C t ∧ t.HasTh (𝟙 _) v ∧ RingHom.ker (MvPolynomial.eval₂Hom em v) = 𝔭 := by
  intro o _ g N' J b em C Mat κ w w' d hL hL2 h3 _ _ hG 𝔭 h𝔭
  classical
  obtain ⟨r, B, θ, hB, hC⟩ := hG.fam
  have : NeZero (N' ^ 2) := ⟨pow_ne_zero _ (by omega)⟩
  have hvg := fun i : {i : Fin r // (B i).Nonempty} =>
    GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em (Ix g (N' ^ 2)) d (B i) (θ i)
      (hB i).1 (hB i).2.1 i.2 (hB i).2.2.1
  choose z hz c hc hgen using hvg
  let p : {i : Fin r // (B i).Nonempty} → Ideal (MvPolynomial (Ix g (N' ^ 2)) o) := fun i =>
    RingHom.ker (MvPolynomial.eval₂Hom em (c i • θ i (z i)))
  have hobj : ∀ i, ∃ t, C t ∧ t.HasTh (𝟙 _) (c i • θ i (z i)) := by
    intro i
    obtain ⟨t, ht, hth⟩ := ((hB i).2.2.2 (z i) (hz i)).1
    exact ⟨t, ht, hth.unit_mul (c i) (hc i).isUnit⟩
  have hle : ∀ i, thIdeal em C ≤ p i := by
    intro i
    obtain ⟨t, ht⟩ := hobj i
    exact iInf_le_of_le t (iInf_le_of_le _ (iInf_le_of_le ht le_rfl))
  have hge : Finset.univ.inf p ≤ thIdeal em C := by
    refine le_iInf fun t => le_iInf fun v => le_iInf fun htv => ?_
    obtain ⟨i, z', hz', hth⟩ := hC t htv.1
    have hspan : Ideal.span (Set.range (θ i z')) = ⊤ := by
      obtain ⟨a, ha⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ t N' ℂ (𝟙 _) (θ i z') ⊥ (by omega)
        dvd_rfl hth Ideal.isPrime_bot 0
      rw [Ideal.mem_bot] at ha
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit ha)
    obtain ⟨u, hu⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit hL hL2 o g N' J b _ _ t ℂ (𝟙 _) (θ i z') v hth htv.2 hspan
    have hv : v = (u : ℂ) • θ i z' := funext fun a => hu a
    intro F hF
    have hF' : F ∈ p ⟨i, z', hz'⟩ := Finset.inf_le (f := p) (Finset.mem_univ _) hF
    rw [RingHom.mem_ker, hv]
    exact hgen ⟨i, z', hz'⟩ F hF' z' hz' u u.ne_zero
  have hp : 𝔭.IsPrime := h𝔭.1.1
  obtain ⟨i, -, hi⟩ := hp.inf_le'.mp (hge.trans h𝔭.1.2)
  obtain ⟨t, ht, hth⟩ := hobj i
  refine ⟨t, _, ht, hth, le_antisymm hi ?_⟩
  exact h𝔭.2 ⟨RingHom.ker_isPrime _, hle i⟩ hi

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DataAtTraitsOfTraitData
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitDataIntrinsic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

theorem j_s : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem exists_generic {S T : Scheme.{0}} {i : T ⟶ S} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ) {v : T ⟶ Xo.XF c}
    (hv : v ≫ Y.j = i ≫ χ) : ∃ (t' : SAB H T) (m₁ : SABMap t' t i) (n : SABMap t' Y.oF.t v)
      (m₂ : SABMap t' Xo.univ.t (v ≫ pullback.fst _ _)), m₁.φ ≫ m.φ = n.φ ≫ Y.m.φ ∧ m₂.φ = n.φ ≫ Y.m0.toSABMap.φ := by
  obtain ⟨t', ⟨p⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y).2.1 _ (i ≫ χ)
  obtain ⟨m₁, h₁⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m p
  have key : ∀ u : T ⟶ Y.X, v ≫ Y.j = u → ∀ p : SABMap t' Y.t u, ∃ n : SABMap t' Y.oF.t v, p.φ = n.φ ≫ Y.m.φ := by
    rintro _ rfl p
    exact GlobalTheory.ObjMaps.exists_sab_cancel Y.m p
  obtain ⟨n, hn⟩ := key _ hv p
  obtain ⟨m₂, h₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap n
  exact ⟨t', m₁, n, m₂, h₁.symm.trans hn, h₂⟩

end GlobalTheory.TraitDataIntrinsic
end
