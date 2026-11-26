module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomothetyLatSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.SepCech

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

abbrev FinSub : Type := {L : IntermediateField K Ω // FiniteDimensional K L}

instance : IsDirected (FinSub K Ω) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, by haveI := a.2; haveI := b.2; infer_instance⟩, le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

instance : Nonempty (FinSub K Ω) := ⟨⟨⊥, inferInstance⟩⟩

def ringDiag : FinSub K Ω ⥤ CommRingCat.{0} where
  obj L := CommRingCat.of L.1
  map h := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom h)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

def ringCocone : Cocone (ringDiag K Ω) where
  pt := CommRingCat.of Ω
  ι := { app := fun L => CommRingCat.ofHom L.1.val.toRingHom, naturality := fun _ _ _ => rfl }

abbrev yArr (A : Type) [CommRing A] [Algebra K A] : Arrow PSh :=
  Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap K A))))

theorem ym {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) :
    yoneda.map (Spec.map g) ≫ yoneda.map (Spec.map f) = yoneda.map (Spec.map (f ≫ g)) := by
  rw [← Functor.map_comp, Spec.map_comp]

theorem spec_comm {L L' : FinSub K Ω} (h : L ⟶ L') :
    yoneda.map (Spec.map ((ringDiag K Ω).map h)) ≫ (yArr K L.1).hom = (yArr K L'.1).hom ≫ 𝟙 _ := by
  change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ 𝟙 _
  rw [Category.comp_id]
  refine (ym _ _).trans ?_
  congr 2 <;> (ext; rfl)

def arr : (FinSub K Ω)ᵒᵖ ⥤ Arrow PSh where
  obj L := yArr K L.unop.1
  map h := Arrow.homMk (yoneda.map (Spec.map ((ringDiag K Ω).map h.unop))) (𝟙 _) (spec_comm K Ω h.unop)
  map_id L := by
    refine Arrow.hom_ext _ _ ?_ ?_
    · change yoneda.map (Spec.map (𝟙 _)) = 𝟙 _
      rw [Spec.map_id, yoneda.map_id]
    · rfl
  map_comp f g := by
    refine Arrow.hom_ext _ _ ?_ ?_
    · change yoneda.map (Spec.map ((ringDiag K Ω).map (g.unop ≫ f.unop))) = _
      rw [Functor.map_comp]
      exact (ym _ _).symm
    · exact (Category.comp_id _).symm

def arrCone : Cone (arr K Ω) where
  pt := yArr K Ω
  π := { app := fun L => Arrow.homMk (yoneda.map (Spec.map ((ringCocone K Ω).ι.app L.unop))) (𝟙 _) (by
            change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ 𝟙 _
            rw [Category.comp_id]
            refine (ym _ _).trans ?_
            congr 2 <;> (ext; rfl))
         naturality := fun L L' h => by
            refine Arrow.hom_ext _ _ ?_ ?_
            · change 𝟙 _ ≫ yoneda.map (Spec.map _) = yoneda.map (Spec.map _) ≫ yoneda.map (Spec.map _)
              rw [Category.id_comp]
              refine Eq.trans ?_ (ym _ _).symm
              exact congrArg (fun x => yoneda.map (Spec.map x)) ((ringCocone K Ω).w h.unop).symm
            · exact (Category.comp_id _).symm }

def cechCone : Cone (arr K Ω ⋙ SimplicialObject.cechNerve) := SimplicialObject.cechNerve.mapCone (arrCone K Ω)

end GlobalTheory.SepCech
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityCofilteredLimitRepresentedAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityCofilteredLimitRepresentedAffine
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem eqv_of_iso (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ≅ E') : Eqv R f.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R f.inv F n, fun x => ?_, fun y => ?_⟩
  · rw [← pull_comp, Iso.inv_hom_id, pull_id]
  · rw [← pull_comp, Iso.hom_inv_id, pull_id]

theorem contCone_of_represented : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (D : I ⥤ PSh) (c : Cone D), IsLimit c → (∀ i, ∃ Z : Scheme.{0}, IsAffine Z ∧ Nonempty (yoneda.obj Z ≅ D.obj i)) → (∃ Z : Scheme.{0}, Nonempty (yoneda.obj Z ≅ c.pt)) → ContCone R F (disc.mapCone c) := by
  intro R _ F hF I _ _ D c hc hD hpt
  choose Z hZ he using hD
  obtain ⟨Z0, ⟨e0⟩⟩ := hpt
  let e : ∀ i, yoneda.obj (Z i) ≅ D.obj i := fun i => (he i).some

  let G : I ⥤ Scheme.{0} :=
    { obj := Z
      map := fun {i j} f => yoneda.preimage ((e i).hom ≫ D.map f ≫ (e j).inv)
      map_id := fun i => yoneda.map_injective (by simp)
      map_comp := fun {i j k} f g => yoneda.map_injective (by simp) }
  let isoYD : G ⋙ yoneda ≅ D := NatIso.ofComponents e (fun {i j} f => by simp [G])

  let s : Cone G :=
    { pt := Z0
      π :=
        { app := fun i => yoneda.preimage (e0.hom ≫ c.π.app i ≫ (e i).inv)
          naturality := fun i j f => yoneda.map_injective (by simp [G]) } }
  have hs : IsLimit s := by
    apply isLimitOfReflects yoneda
    have h1 : IsLimit ((Cone.postcompose isoYD.inv).obj c) := (IsLimit.postcomposeInvEquiv isoYD c).symm hc
    refine h1.ofIsoLimit (Cone.ext e0.symm (fun i => ?_))
    simp [s]
    rfl
  have h0 : ContCone R F (sch.mapCone s) := GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit R F hF I G s hs hZ
  let αI : G ⋙ sch ≅ D ⋙ disc := (Functor.associator G yoneda disc).symm ≪≫ Functor.isoWhiskerRight isoYD disc
  let βI : sch.obj Z0 ≅ disc.obj c.pt := disc.mapIso e0
  refine (GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F I (G ⋙ sch) (D ⋙ disc) (sch.mapCone s) (disc.mapCone c) αI.hom βI.hom
    (fun i => ?_) (fun i => eqv_of_iso R F (αI.app i)) (eqv_of_iso R F βI)).mp h0
  simp only [Functor.mapCone_π_app, αI, βI, s, sch, Functor.comp_map]
  simp [isoYD, ← Functor.map_comp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityCofilteredLimitRepresentedAffineStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuity_cofiltered_limit_represented_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (D : I ⥤ PSh) (c : Cone D), IsLimit c → (∀ i, ∃ Z : Scheme.{0}, IsAffine Z ∧ Nonempty (yoneda.obj Z ≅ D.obj i)) → (∃ Z : Scheme.{0}, Nonempty (yoneda.obj Z ≅ c.pt)) → ContCone R F (disc.mapCone c) := by
  first
  | exact @GlobalTheory.contCone_of_represented
  | exact GlobalTheory.contCone_of_represented
  | (intros; apply GlobalTheory.contCone_of_represented <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapSmoothSurjectiveOfIsSeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapSmoothSurjectiveOfIsSeparable
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC
namespace GlobalTheory

theorem spec_map_smooth_surjective_of_isSeparable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have hfp : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.Etale K L := ⟨inferInstance, inferInstance⟩
  have hs : Algebra.Smooth K L := inferInstance
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    rw [RingHom.Smooth]
    simp only [CommRingCat.hom_ofHom]
    exact RingHom.smooth_algebraMap.mpr hs
  · constructor
    intro x
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    exact ⟨y, Subsingleton.elim _ _⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapSmoothSurjectiveOfIsSeparableStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_and_surjective_spec_map_of_isSeparable : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L], Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  first | exact @GlobalTheory.spec_map_smooth_surjective_of_isSeparable | exact GlobalTheory.spec_map_smooth_surjective_of_isSeparable | (intros; apply GlobalTheory.spec_map_smooth_surjective_of_isSeparable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelPreservesCofilteredLimit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelPreservesCofilteredLimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

lemma cechLev_π {f g : Arrow PSh} (F : f ⟶ g) (k : SimplexCategoryᵒᵖ) (j : Fin (k.unop.len + 1)) :
    ((evaluation _ PSh).obj k).map (Arrow.mapCechNerve F) ≫ WidePullback.π (fun _ => g.hom) j =
      WidePullback.π (fun _ => f.hom) j ≫ F.left := by
  simp only [evaluation_obj_map, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_π]

lemma cechLev_base {f g : Arrow PSh} (F : f ⟶ g) (k : SimplexCategoryᵒᵖ) :
    ((evaluation _ PSh).obj k).map (Arrow.mapCechNerve F) ≫
        WidePullback.base (fun _ : Fin (k.unop.len + 1) => g.hom) =
      WidePullback.base (fun _ => f.hom) ≫ F.right := by
  simp only [evaluation_obj_map, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_base]

theorem cech_level_limit (I : Type) [SmallCategory I] [IsCofiltered I] (A : I ⥤ Arrow PSh) (cA : Cone A)
    (hl : IsLimit (Arrow.leftFunc.mapCone cA)) (_hA : ∀ ⦃i j : I⦄ (f : i ⟶ j), IsIso (A.map f).right)
    (hR : ∀ i, IsIso (cA.π.app i).right) (k : SimplexCategoryᵒᵖ) :
    Nonempty (IsLimit (((evaluation _ PSh).obj k).mapCone (SimplicialObject.cechNerve.mapCone cA))) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  let L : ∀ (s : Cone ((A ⋙ SimplicialObject.cechNerve) ⋙ (evaluation _ PSh).obj k))
      (j : Fin (k.unop.len + 1)), s.pt ⟶ cA.pt.left := fun s j =>
    hl.lift
      { pt := s.pt
        π :=
          { app := fun i => s.π.app i ≫ WidePullback.π (fun _ => (A.obj i).hom) j
            naturality := by
              intro i i' f
              have h := s.w f
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                Functor.comp_obj, Arrow.leftFunc_obj, Functor.comp_map, Arrow.leftFunc_map] at h ⊢
              rw [← h]
              exact (Category.assoc _ _ _).trans
                ((congrArg (s.π.app i ≫ ·) (cechLev_π (A.map f) k j)).trans (Category.assoc _ _ _).symm) } }
  have hLfac : ∀ s j i, L s j ≫ (cA.π.app i).left =
      s.π.app i ≫ WidePullback.π (fun _ => (A.obj i).hom) j := by
    intro s j i
    exact hl.fac _ i
  have hLbase : ∀ s j i, L s j ≫ cA.pt.hom ≫ (cA.π.app i).right =
      s.π.app i ≫ WidePullback.base (fun _ : Fin (k.unop.len + 1) => (A.obj i).hom) := by
    intro s j i
    have hw : (cA.π.app i).left ≫ (A.obj i).hom = cA.pt.hom ≫ (cA.π.app i).right := Arrow.w (cA.π.app i)
    rw [← hw, ← Category.assoc, hLfac]
    exact (Category.assoc _ _ _).trans (congrArg (s.π.app i ≫ ·) (WidePullback.π_arrow _ j))
  refine ⟨{ lift := fun s => WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) (fun j => by
              rw [← cancel_mono (cA.π.app i₀).right, Category.assoc, Category.assoc, hLbase, hLbase])
            fac := ?_
            uniq := ?_ }⟩
  · intro s i
    apply WidePullback.hom_ext
    · intro j
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) _ ≫ ·) (cechLev_π (cA.π.app i) k j)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (cA.π.app i).left) (WidePullback.lift_π _ _ _ _ j)).trans ?_
      exact hLfac s j i
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) _ ≫ ·) (cechLev_base (cA.π.app i) k)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (cA.π.app i).right) (WidePullback.lift_base _ _ _ _)).trans ?_
      exact (Category.assoc _ _ _).trans (hLbase s 0 i)
  · intro s m hm
    have hmj : ∀ j, m ≫ WidePullback.π (fun _ => cA.pt.hom) j = L s j := by
      intro j
      apply hl.hom_ext
      intro i
      refine Eq.trans ?_ (hLfac s j i).symm
      refine Eq.trans ?_ (congrArg (· ≫ WidePullback.π (fun _ => (A.obj i).hom) j) (hm i))
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (m ≫ ·) (cechLev_π (cA.π.app i) k j).symm
    apply WidePullback.hom_ext
    · intro j
      exact (hmj j).trans (WidePullback.lift_π _ _ _ _ j).symm
    · refine Eq.trans ?_ (WidePullback.lift_base _ _ _ _).symm
      refine Eq.trans ?_ (congrArg (· ≫ cA.pt.hom) (hmj 0))
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (m ≫ ·) (WidePullback.π_arrow _ 0).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelPreservesCofilteredLimitStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechNerve_level_preserves_cofiltered_limit : ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (A : I ⥤ Arrow PSh) (cA : Cone A), IsLimit (Arrow.leftFunc.mapCone cA) → (∀ ⦃i j : I⦄ (f : i ⟶ j), IsIso (A.map f).right) → (∀ i, IsIso (cA.π.app i).right) → ∀ k : SimplexCategoryᵒᵖ, Nonempty (IsLimit (((evaluation _ PSh).obj k).mapCone (SimplicialObject.cechNerve.mapCone cA))) := by
  first | exact @GlobalTheory.cech_level_limit | exact GlobalTheory.cech_level_limit | (intros; apply GlobalTheory.cech_level_limit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitFiniteSubextensionSpecArrowCone
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitFiniteSubextensionSpecArrowCone
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem isLimit_leftFunc_arrCone (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (hc : IsColimit (ringCocone K Ω)) :
    Nonempty (IsLimit (Arrow.leftFunc.mapCone (arrCone K Ω))) :=
  ⟨isLimitOfPreserves (Scheme.Spec ⋙ yoneda) hc.op⟩

end GlobalTheory.SepCech
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitFiniteSubextensionSpecArrowConeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLimit_finiteSubextensionSpecArrowCone : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω], IsColimit (GlobalTheory.SepCech.ringCocone K Ω) → Nonempty (IsLimit (Arrow.leftFunc.mapCone (GlobalTheory.SepCech.arrCone K Ω))) := by
  first | exact @GlobalTheory.SepCech.isLimit_leftFunc_arrCone | exact GlobalTheory.SepCech.isLimit_leftFunc_arrCone | (intros; apply GlobalTheory.SepCech.isLimit_leftFunc_arrCone <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitFiniteSubextensionRingCocone
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitFiniteSubextensionRingCocone
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem ringCocone_isColimit (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] :
    Nonempty (IsColimit (ringCocone K Ω)) := by
  haveI : ReflectsColimitsOfShape (FinSub K Ω) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change Ω at x
    have hx : _root_.IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    haveI := IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin K {x}, inferInstance⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨⟨i.1 ⊔ j.1, by haveI := i.2; haveI := j.2; infer_instance⟩,
      homOfLE (le_sup_left (a := i.1)), homOfLE (le_sup_right (b := j.1)), ?_⟩
    apply Subtype.ext
    exact h

end GlobalTheory.SepCech
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitFiniteSubextensionRingCoconeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isColimit_finiteSubextensionRingCocone : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω], Nonempty (CategoryTheory.Limits.IsColimit (GlobalTheory.SepCech.ringCocone K Ω)) := by
  first | (exact @GlobalTheory.SepCech.ringCocone_isColimit) | (exact GlobalTheory.SepCech.ringCocone_isColimit) | (intros; apply GlobalTheory.SepCech.ringCocone_isColimit  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationSepClosureIsEquivalence
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem aug_comm {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (g : Y' ⟶ X) (u : yoneda.obj Y ⟶ yoneda.obj Y')
    (w : u ≫ yoneda.map g = yoneda.map f ≫ 𝟙 _) :
    SimplicialObject.cechNerve.map (Arrow.homMk u (𝟙 _) w : Arrow.mk (yoneda.map f) ⟶ Arrow.mk (yoneda.map g)) ≫ GlobalTheory.EtC.cechAug g =
      GlobalTheory.EtC.cechAug f := by
  apply NatTrans.ext; funext n
  simp [GlobalTheory.EtC.cechAug, SimplicialObject.cechNerve, Arrow.mapCechNerve, Arrow.augmentedCechNerve]
  erw [NatTrans.comp_app, WidePullback.lift_base]

theorem cont (R : Type) [CommRing R] (F : Shv R) (hF : Finitary F) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] : ContCone R F (cechCone K Ω) := by
  obtain ⟨hc⟩ := GlobalTheory.T.isColimit_finiteSubextensionRingCocone K Ω
  obtain ⟨hl⟩ := GlobalTheory.T.isLimit_finiteSubextensionSpecArrowCone K Ω hc
  refine GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise R F _ _ _ (fun k => ?_)
  obtain ⟨hk⟩ := GlobalTheory.T.cechNerve_level_preserves_cofiltered_limit _ _ _ hl (fun _ _ _ => show IsIso (𝟙 _) from inferInstance)
    (fun _ => show IsIso (𝟙 _) from inferInstance) k
  refine GlobalTheory.T.continuity_cofiltered_limit_represented_affine R F hF _ _ _ hk (fun L => ?_) ?_
  · obtain ⟨Z, π, e, hπ, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsAffineHom _ _ (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) inferInstance k
    haveI := hπ
    exact ⟨Z, isAffine_of_isAffineHom π, ⟨e⟩⟩
  · obtain ⟨Z, π, e, -, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsAffineHom _ _ (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) inferInstance k
    exact ⟨Z, ⟨e⟩⟩

theorem cechAug_sepClosure_eqv : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω], Eqv R (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) F := by
  intro R _ F hF K Ω _ _ _ _
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have hc := cont R F hF K Ω
  have hA : ∀ L : (FinSub K Ω)ᵒᵖ, Eqv R (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1)))) F := by
    intro L
    haveI := L.unop.2
    haveI : Algebra.IsSeparable K L.unop.1 := Algebra.isSeparable_tower_bot_of_isSeparable K L.unop.1 Ω
    obtain ⟨h1, h2⟩ := GlobalTheory.T.smooth_and_surjective_spec_map_of_isSeparable K L.unop.1
    exact GlobalTheory.T.etC_a2 R _ F
  have hw : ∀ L : (FinSub K Ω)ᵒᵖ, (cechCone K Ω).π.app L ≫ GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) =
      GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := fun L => aug_comm _ _ _ _
  have hw2 : ∀ ⦃L L' : (FinSub K Ω)ᵒᵖ⦄ (f : L ⟶ L'), (arr K Ω ⋙ SimplicialObject.cechNerve).map f ≫
      GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L'.unop.1))) =
      GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) := fun L L' f => aug_comm _ _ _ _
  intro n
  constructor
  · refine (injective_iff_map_eq_zero (pull R _ F n)).mpr (fun z hz => ?_)
    let L0 : (FinSub K Ω)ᵒᵖ := op ⟨⊥, inferInstance⟩
    have h0 : pull R ((cechCone K Ω).π.app L0) F n
        (pull R (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L0.unop.1)))) F n z) = 0 :=
      (pull_comp R _ _ F n z).symm.trans ((congrArg (fun g => pull R g F n z) (hw L0)).trans hz)
    obtain ⟨L1, f, hf⟩ := (hc n).2 L0 _ h0
    have hf' : pull R (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L1.unop.1)))) F n z = 0 :=
      (congrArg (fun g => pull R g F n z) (hw2 f)).symm.trans
        ((pull_comp R ((arr K Ω ⋙ SimplicialObject.cechNerve).map f)
          (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L0.unop.1)))) F n z).trans hf)
    exact ((injective_iff_map_eq_zero (pull R _ F n)).mp (hA L1 n).1) z hf'
  · intro x
    obtain ⟨L, y, hy⟩ := (hc n).1 x
    obtain ⟨z, rfl⟩ := (hA L n).2 y
    refine ⟨z, ?_⟩
    rw [← hy]
    exact (congrArg (fun g => pull R g F n z) (hw L)).symm.trans (pull_comp R _ _ F n z)

end GlobalTheory.SepCech
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationSepClosureIsEquivalenceStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCechAugmentation_sepClosure_isEquivalence : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω], Eqv R (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) F := by
  first
  | exact @GlobalTheory.SepCech.cechAug_sepClosure_eqv
  | exact GlobalTheory.SepCech.cechAug_sepClosure_eqv
  | (intros; apply GlobalTheory.SepCech.cechAug_sepClosure_eqv <;> assumption)
end
