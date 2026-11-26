module

public import Development.EtaleCohomology.EtaleSheaves.LeafDegCut
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafDescendMapPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafDescendMapPf

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

abbrev J (R : Subalgebra k Ω) : Type := {S : Subalgebra k Ω // R ≤ S ∧ S.FG}

instance (R : Subalgebra k Ω) : IsDirected (J R) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, le_sup_of_le_left a.2.1, a.2.2.sup b.2.2⟩, le_sup_left (a := a.1), le_sup_right (a := a.1)⟩⟩

lemma toR_incl {R S : Subalgebra k Ω} (h : R ≤ S) : toR S ≫ incl h = toR R := by
  rw [toR, incl, toR, ← Spec.map_comp]; rfl

lemma incl_incl {R S T : Subalgebra k Ω} (h : R ≤ S) (h' : S ≤ T) :
    incl h' ≫ incl h = incl (h.trans h') := by
  rw [incl, incl, incl, ← Spec.map_comp]; rfl

lemma incl_base {R S : Subalgebra k Ω} (h : R ≤ S) :
    incl h ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k S)) := by
  rw [incl, ← Spec.map_comp]; rfl

lemma toR_base (R : Subalgebra k Ω) :
    toR R ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [toR, ← Spec.map_comp]; rfl

end LateralTheory.E.LeafDescendMapPf

namespace LateralTheory.E.LeafDescendMapPf
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

lemma incl_self {S : Subalgebra k Ω} (h : S ≤ S) : incl h = 𝟙 _ := by
  rw [incl, ← Spec.map_id]; rfl

variable (R : Subalgebra k Ω)

def F : J R ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of S.1
  map {S T} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom

def coc : Cocone (F R) where
  pt := CommRingCat.of Ω
  ι := { app S := CommRingCat.ofHom (algebraMap S.1 Ω) }

def cocIsColimit (hR : R.FG) : IsColimit (coc R) := by
  haveI : Nonempty (J R) := ⟨⟨R, le_rfl, hR⟩⟩
  haveI : ReflectsColimitsOfShape (J R) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{0})
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (x : Ω)
    have hx : x ∈ R ⊔ Algebra.adjoin k {x} := le_sup_right (a := R) (Algebra.subset_adjoin rfl)
    exact ⟨⟨R ⊔ Algebra.adjoin k {x}, le_sup_left, hR.sup (by simpa using Subalgebra.fg_adjoin_finset (R := k) ({x} : Finset Ω))⟩, ⟨x, hx⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨⟨i.1 ⊔ j.1, le_sup_of_le_left i.2.1, i.2.2.sup j.2.2⟩, homOfLE (le_sup_left (a := i.1)),
      homOfLE (le_sup_right (a := i.1)), ?_⟩
    apply Subtype.ext
    exact h

def specLim (hR : R.FG) : IsLimit (Scheme.Spec.mapCone (coc R).op) :=
  isLimitOfPreserves Scheme.Spec (cocIsColimit R hR).op

end LateralTheory.E.LeafDescendMapPf

namespace LateralTheory.E.LeafDescendMapPf
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
variable {D0 : Scheme.{0}} (q : D0 ⟶ Sp R)

abbrev D : (J R)ᵒᵖ ⥤ Scheme.{0} where
  obj S := pullback q (incl S.unop.2.1)
  map {S T} h := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ incl (leOfHom h.unop))
    (by rw [pullback.condition, Category.assoc, incl_incl])
  map_id S := by apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc, Category.id_comp, Category.comp_id, Functor.const_obj_map, incl_incl, toR_incl, incl_self, incl_base, CategoryTheory.Functor.id_obj]
  map_comp f g := by apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc, Category.id_comp, Category.comp_id, Functor.const_obj_map, incl_incl, toR_incl, incl_self, incl_base, CategoryTheory.Functor.id_obj]

variable {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (v0 : C0 ⟶ D0) (hPB : IsPullback v0 c0 q (toR R))

abbrev cone : Cone (D R q) where
  pt := C0
  π := { app S := pullback.lift v0 (c0 ≫ toR S.unop.1) (by rw [hPB.w, Category.assoc, toR_incl])
         naturality S T h := by apply pullback.hom_ext <;> (dsimp only [D]; simp only [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc, Category.id_comp, Category.comp_id, Functor.const_obj_map, incl_incl, toR_incl, incl_self, incl_base, CategoryTheory.Functor.id_obj]) <;> simp }

lemma fstAff {S : Subalgebra k Ω} (h : R ≤ S) : IsAffineHom (pullback.fst q (incl h)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback q (incl h)).flip
    (by dsimp [incl]; infer_instance)

instance {S T : (J R)ᵒᵖ} (h : S ⟶ T) : IsAffineHom ((D R q).map h) := by
  have h1 := fstAff R q S.unop.2.1
  have h2 := fstAff R q T.unop.2.1
  have : IsAffineHom ((D R q).map h ≫ pullback.fst _ _) := by
    dsimp only [D]; rw [pullback.lift_fst]; exact h1
  have hs : IsSeparated (pullback.fst q (incl T.unop.2.1)) := @IsSeparated.of_isAffineHom _ _ _ h2
  exact IsAffineHom.of_comp _ (pullback.fst q (incl T.unop.2.1))

end LateralTheory.E.LeafDescendMapPf

namespace LateralTheory.E.LeafDescendMapPf
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
variable {D0 : Scheme.{0}} (q : D0 ⟶ Sp R)
variable {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (v0 : C0 ⟶ D0) (hPB : IsPullback v0 c0 q (toR R))

abbrev specCone (s : Cone (D R q)) : Cone ((F R).op ⋙ Scheme.Spec) where
  pt := s.pt
  π := { app S := s.π.app S ≫ pullback.snd _ _
         naturality S T h := by
           have hw := s.w h
           rw [← hw]
           erw [Category.id_comp, Category.assoc, pullback.lift_snd]
           exact (Category.assoc _ _ _).symm }

def bL (hR : R.FG) (s : Cone (D R q)) : s.pt ⟶ Sp Ω := (specLim R hR).lift (specCone R q s)

lemma bL_fac (hR : R.FG) (s : Cone (D R q)) (j : (J R)ᵒᵖ) :
    bL R q hR s ≫ toR j.unop.1 = s.π.app j ≫ pullback.snd q (incl j.unop.2.1) :=
  (specLim R hR).fac (specCone R q s) j

lemma bL_uniq (hR : R.FG) (s : Cone (D R q)) (m : s.pt ⟶ Sp Ω)
    (hm : ∀ j : (J R)ᵒᵖ, m ≫ toR j.unop.1 = s.π.app j ≫ pullback.snd q (incl j.unop.2.1)) : m = bL R q hR s :=
  (specLim R hR).uniq (specCone R q s) m hm

def aL (hR : R.FG) (s : Cone (D R q)) : s.pt ⟶ D0 :=
  s.π.app (op (⟨R, le_rfl, hR⟩ : J R)) ≫ pullback.fst q (incl (le_refl R))

lemma aL_w (hR : R.FG) (s : Cone (D R q)) : aL R q hR s ≫ q = bL R q hR s ≫ toR R := by
  have := bL_fac R q hR s (op (⟨R, le_rfl, hR⟩ : J R))
  simp only [aL, Category.assoc, pullback.condition, incl_self, Category.comp_id]
  exact this.symm

def coneIsLimit (hR : R.FG) : IsLimit (cone R q c0 v0 hPB) where
  lift s := hPB.lift (aL R q hR s) (bL R q hR s) (aL_w R q hR s)
  fac s j := by
    have hw := s.w (homOfLE j.unop.2.1 : (⟨R, le_rfl, hR⟩ : J R) ⟶ j.unop).op
    apply pullback.hom_ext
    · simp only [cone, Category.assoc, pullback.lift_fst, IsPullback.lift_fst, aL, ← hw]
    · simp only [cone, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, IsPullback.lift_snd]
      exact bL_fac R q hR s j
  uniq s m hm := by
    apply hPB.hom_ext
    · rw [IsPullback.lift_fst, aL, ← hm]
      simp only [cone, Category.assoc, pullback.lift_fst]
    · rw [IsPullback.lift_snd]
      apply bL_uniq
      intro j
      rw [← hm j]
      simp only [cone, Category.assoc, pullback.lift_snd]

lemma lfp {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] : LocallyOfFinitePresentation p := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  haveI : IsNoetherianRing Γ(Sp k, U) := IsLocallyNoetherian.component_noetherian U
  exact RingHom.FinitePresentation.of_finiteType.mp (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance U V e)

end LateralTheory.E.LeafDescendMapPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SimplicialPieceDiscrete
section -- merged from Development.EtaleCohomology.EtaleSheaves.SimplicialPieceRelations
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf

namespace LateralTheory.E.SimplicialPieceRelations

abbrev Qt (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)
abbrev HC (R : Type) [CommRing R] := HomotopyCategory (Shv R) (ComplexShape.up ℤ)

def Disc0 : Prop := ∀ (R : Type) [CommRing R] {X Y : PSh} (f : X ⟶ Y),
  ∃ (a : (Qt R).obj ((chains R).obj (disc.obj X)) ≅ (Qt R).obj ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj X)))
    (b : (Qt R).obj ((chains R).obj (disc.obj Y)) ≅ (Qt R).obj ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj Y))),
    (Qt R).map ((chains R).map (disc.map f)) ≫ b.hom = a.hom ≫ (Qt R).map ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f))

variable {R : Type} [CommRing R]

theorem relY_conj_imp (F : Shv R) (n : ℤ) {A B A' B' : HC R} (g : A ⟶ B) (g' : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : g ≫ b.hom = a.hom ≫ g') : Tri.RelY (Yres R F) n g → Tri.RelY (Yres R F) n g' := by
  have hg' : g' = a.inv ≫ g ≫ b.hom := by rw [h]; simp
  rintro ⟨hs, hi⟩
  refine ⟨fun y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨x, hx⟩ := hs (a.hom ≫ y)
    refine ⟨b.inv ≫ x, ?_⟩
    simp only at hx ⊢
    rw [hg']; simp [hx]
  · simp only at hx
    rw [hg'] at hx
    have : g ≫ (b.hom ≫ x1) = g ≫ (b.hom ≫ x2) := by
      have := congrArg (fun z => a.hom ≫ z) hx
      simpa using this
    have := hi this
    simpa using congrArg (fun z => b.inv ≫ z) this

theorem relY_conj (F : Shv R) (n : ℤ) {A B A' B' : HC R} (g : A ⟶ B) (g' : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : g ≫ b.hom = a.hom ≫ g') : Tri.RelY (Yres R F) n g ↔ Tri.RelY (Yres R F) n g' :=
  ⟨relY_conj_imp F n g g' a b h, relY_conj_imp F n g' g a.symm b.symm (by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← h]; simp)⟩

def yIso (F : Shv R) (p m c : ℤ) (hc : m + p = c) : Yres R F c ≅ (Yres R F m)⟦p⟧ :=
  (Qt R).mapIso ((shiftFunctorAdd' (Cx R) m p c hc).app (res R F)) ≪≫ ((Qt R).commShiftIso p).app _

theorem relY_shift (F : Shv R) (k p : ℤ) {A B : HC R} (g : A ⟶ B) :
    Tri.RelY (Yres R F) k g → Tri.RelY (Yres R F) (k + p) (g⟦p⟧') := by
  rintro ⟨hs, hi⟩
  refine ⟨fun y => ?_, fun x1 x2 hx => ?_⟩
  · let e := yIso F p (k - 1) (k + p - 1) (by omega)
    obtain ⟨z, hz⟩ := (shiftFunctor (HC R) p).map_surjective (y ≫ e.hom)
    obtain ⟨w, hw⟩ := hs z
    refine ⟨(shiftFunctor (HC R) p).map w ≫ e.inv, ?_⟩
    simp only at hw ⊢
    rw [← Category.assoc, ← Functor.map_comp, hw, hz]; simp
  · let e := yIso F p k (k + p) rfl
    obtain ⟨w1, hw1⟩ := (shiftFunctor (HC R) p).map_surjective (x1 ≫ e.hom)
    obtain ⟨w2, hw2⟩ := (shiftFunctor (HC R) p).map_surjective (x2 ≫ e.hom)
    simp only at hx
    have h1 : (shiftFunctor (HC R) p).map (g ≫ w1) = (shiftFunctor (HC R) p).map (g ≫ w2) := by
      rw [Functor.map_comp, Functor.map_comp, hw1, hw2, ← Category.assoc, ← Category.assoc, hx]
    have h2 := hi ((shiftFunctor (HC R) p).map_injective h1)
    have : x1 ≫ e.hom = x2 ≫ e.hom := by rw [← hw1, ← hw2, h2]
    simpa using congrArg (fun z => z ≫ e.inv) this

theorem chains_f (U E : Spc) (u : U ⟶ E) (p : ℕ) :
    ((chains R).map u).f (-(p : ℤ)) =
      (chainsXIso R U p).hom ≫ (free R).map (u.app (Opposite.op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl]
  rfl

theorem piece_of (hD : Disc0) : Piece := by
  intro R _ F U E u p k h
  let f := u.app (Opposite.op (SimplexCategory.mk p))
  let s0 := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)
  have h1 : Tri.RelY (Yres R F) k ((Qt R).map ((chains R).map (disc.map f))) := (relK_iff R _ F k).1 h
  obtain ⟨a, b, hab⟩ := hD R f
  have h2 : Tri.RelY (Yres R F) k ((Qt R).map s0) := (relY_conj F k _ _ a b hab).1 h1
  have h3 := relY_shift F k (p : ℤ) _ h2
  have h4 : Tri.RelY (Yres R F) (k + p) ((Qt R).map (s0⟦(p : ℤ)⟧')) :=
    (relY_conj F _ _ _ (((Qt R).commShiftIso (p : ℤ)).app _) (((Qt R).commShiftIso (p : ℤ)).app _)
      (((Qt R).commShiftIso (p : ℤ)).hom.naturality s0)).2 h3
  let Eo := (CochainComplex.singleFunctors (Shv R)).shiftIso (p : ℤ) (-(p : ℤ)) 0 (by omega)
  have h5 : Tri.RelY (Yres R F) (k + p) ((Qt R).map ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map ((free R).map f))) :=
    (relY_conj F _ _ _ ((Qt R).mapIso (Eo.symm.app _)) ((Qt R).mapIso (Eo.symm.app _)) (by
      simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, ← Functor.map_comp]
      congr 1
      exact Eo.inv.naturality _)).2 h4
  refine (relK_iff R _ F (k + p)).2 ?_
  refine (relY_conj F _ _ _ ((Qt R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R U p)))
    ((Qt R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E p))) ?_).2 h5
  simp only [piece, Functor.mapIso_hom, ← Functor.map_comp, chains_f]
  simp [f]
  rfl

end LateralTheory.E.SimplicialPieceRelations
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.SimplicialPieceRelations SimplicialObject SimplicialObject.Augmented

namespace LateralTheory.E.SimplicialPieceDiscrete

variable (R : Type) [CommRing R]

def aug (X : PSh) : SimplicialObject.Augmented (Shv R) where
  left := ((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj X)
  right := (free R).obj X
  hom := { app := fun _ => 𝟙 _, naturality := by intros; (try simp); (try rfl) }

def augMap {X Y : PSh} (f : X ⟶ Y) : aug R X ⟶ aug R Y where
  left := ((SimplicialObject.whiskering _ _).obj (free R)).map (disc.map f)
  right := (free R).map f
  w := by
    apply NatTrans.ext; funext n; exact (Category.comp_id _).trans (Category.id_comp _).symm

def ed (X : PSh) : ExtraDegeneracy (aug R X) where
  s' := 𝟙 _
  s := fun _ => 𝟙 _
  s'_comp_ε := by simp [aug] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s₀_comp_δ₁ := by simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_δ₀ := by intro n; simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_δ := by intro n i; simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_σ := by intro n i; simp [aug, SimplicialObject.σ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _

variable {R}

def hext {K L : ChainComplex (Shv R) ℕ} (h : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingDownNat) (L.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap h.hom _
  inv := HomologicalComplex.extendMap h.inv _
  homotopyHomInvId := (Homotopy.ofEq (by rw [HomologicalComplex.extendMap_comp])).trans
    ((h.homotopyHomInvId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (by rw [HomologicalComplex.extendMap_comp])).trans
    ((h.homotopyInvHomId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

def sIso (A : Shv R) := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat A 0 (0 : ℤ) (by simp)

theorem sIso_nat {A B : Shv R} (φ : A ⟶ B) :
    HomologicalComplex.extendMap ((ChainComplex.single₀ (Shv R)).map φ) ComplexShape.embeddingDownNat ≫ (sIso B).hom =
      (sIso A).hom ≫ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ := by
  apply HomologicalComplex.to_single_hom_ext
  simp [sIso, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) (by simp),
    HomologicalComplex.single_map_f_self]
  erw [Iso.inv_hom_id_assoc]

theorem disc0 : Disc0 := by
  intro R _ X Y f
  refine ⟨HomotopyCategory.isoOfHomotopyEquiv (hext (ed R X).homotopyEquiv) ≪≫ (Qt R).mapIso (sIso _),
    HomotopyCategory.isoOfHomotopyEquiv (hext (ed R Y).homotopyEquiv) ≪≫ (Qt R).mapIso (sIso _), ?_⟩
  have hn := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := Shv R)).naturality (augMap R f)
  have key : (chains R).map (disc.map f) ≫ HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R Y)) ComplexShape.embeddingDownNat ≫ (sIso ((free R).obj Y)).hom =
      HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R X)) ComplexShape.embeddingDownNat ≫ (sIso ((free R).obj X)).hom ≫
        (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f) := by
    have h2 := congrArg (fun φ => HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) hn
    simp only [HomologicalComplex.extendMap_comp] at h2
    have h1 : HomologicalComplex.extendMap ((point ⋙ ChainComplex.single₀ (Shv R)).map (augMap R f)) ComplexShape.embeddingDownNat ≫
        (sIso ((free R).obj Y)).hom = (sIso ((free R).obj X)).hom ≫
          (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f) := sIso_nat ((free R).map f)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (sIso ((free R).obj Y)).hom) h2).trans
      ((Category.assoc _ _ _).trans (congrArg (HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R X)) ComplexShape.embeddingDownNat ≫ ·) h1)))
  have := congrArg (Qt R).map key
  simp only [Functor.map_comp] at this
  simp only [Iso.trans_hom, Category.assoc]
  exact this

theorem Piece_of : LateralTheory.E.TruncationPieces.Piece := LateralTheory.E.SimplicialPieceRelations.piece_of disc0

end LateralTheory.E.SimplicialPieceDiscrete
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.TowerFinPf
noncomputable section
open CategoryTheory Limits Category Pretriangulated GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf

namespace LateralTheory.E.TowerFinPf

abbrev Q (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

section RelYLemmas
variable (R : Type) [CommRing R] (F : Shv R) (n : ℤ)

theorem relY_of_iso {A B A' B' : HomotopyCategory (Shv R) (ComplexShape.up ℤ)} (g : A ⟶ B) (g' : A' ⟶ B')
    (e₁ : A' ≅ A) (e₂ : B' ≅ B) (w : g' ≫ e₂.hom = e₁.hom ≫ g) (h : Tri.RelY (Yres R F) n g) :
    Tri.RelY (Yres R F) n g' := by
  have w' : g ≫ e₂.inv = e₁.inv ≫ g' := by
    rw [Iso.eq_inv_comp, ← assoc, ← w, assoc, Iso.hom_inv_id, comp_id]
  refine ⟨fun y => ?_, fun x₁ x₂ hx => ?_⟩
  · obtain ⟨x, hx⟩ := h.1 (e₁.inv ≫ y)
    refine ⟨e₂.hom ≫ x, ?_⟩
    simp only at hx ⊢
    rw [← assoc, w, assoc, hx, Iso.hom_inv_id_assoc]
  · simp only at hx
    have : e₂.inv ≫ x₁ = e₂.inv ≫ x₂ := h.2 (by
      simp only
      rw [← assoc, w', assoc, hx, ← assoc, ← w', assoc])
    simpa using congrArg (e₂.hom ≫ ·) this

theorem relY_zero {A B : HomotopyCategory (Shv R) (ComplexShape.up ℤ)} (g : A ⟶ B) (hA : IsZero A) (hB : IsZero B) :
    Tri.RelY (Yres R F) n g :=
  ⟨fun y => ⟨0, hA.eq_of_src _ _⟩, fun _ _ _ => hB.eq_of_src _ _⟩

theorem isZero_cx {K : Cx R} (h : ∀ i, IsZero (K.X i)) : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  exact (h i).eq_of_src _ _

theorem relK_zero {K L : Cx R} (f : K ⟶ L) (hK : ∀ i, IsZero (K.X i)) (hL : ∀ i, IsZero (L.X i)) :
    RelK R F n f :=
  (relK_iff R f F n).2 (relY_zero R F n _ ((Q R).map_isZero (isZero_cx R hK)) ((Q R).map_isZero (isZero_cx R hL)))

theorem relK_piece_zero {K L : Cx R} (f : K ⟶ L) (p : ℕ) (hK : IsZero (K.X (-(p : ℤ)))) (hL : IsZero (L.X (-(p : ℤ)))) :
    RelK R F n (pieceC R f p) :=
  (relK_iff R _ F n).2 (relY_zero R F n _
    ((Q R).map_isZero ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).map_isZero hK))
    ((Q R).map_isZero ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).map_isZero hL)))

theorem relK_piece_iso {K L K' L' : Cx R} (f : K ⟶ L) (g : K' ⟶ L') (p : ℕ)
    (α : K'.X (-(p : ℤ)) ≅ K.X (-(p : ℤ))) (β : L'.X (-(p : ℤ)) ≅ L.X (-(p : ℤ)))
    (w : g.f (-(p : ℤ)) ≫ β.hom = α.hom ≫ f.f (-(p : ℤ))) (h : RelK R F n (pieceC R f p)) :
    RelK R F n (pieceC R g p) := by
  rw [relK_iff] at h ⊢
  refine relY_of_iso R F n _ _ ((Q R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).mapIso α))
    ((Q R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).mapIso β)) ?_ h
  simp only [Functor.mapIso_hom, pieceC, ← Functor.map_comp, w]

end RelYLemmas

theorem inv_nat {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ : C} (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) [IsIso g₁] [IsIso g₂]
    (t₂ : X₁ ⟶ X₂) (t₃ : Y₁ ⟶ Y₂) (h : g₁ ≫ t₃ = t₂ ≫ g₂) : t₃ ≫ inv g₂ = inv g₁ ≫ t₂ := by
  rw [IsIso.comp_inv_eq, assoc, IsIso.eq_inv_comp, h]

theorem aux {C : Type*} [Category C] {A₃ A₂ B₂ B₁ A₃' A₂' B₂' B₁' : C} (s₁ : A₃ ⟶ A₂) (d₁ : A₂ ⟶ B₂)
    (r₁ : B₂ ⟶ B₁) (t₁ : B₁ ⟶ B₁') (t₃ : A₃ ⟶ A₃') (s₂ : A₃' ⟶ A₂') (d₂ : A₂' ⟶ B₂') (r₂ : B₂' ⟶ B₁')
    (ta : A₂ ⟶ A₂') (tb : B₂ ⟶ B₂') (hs : t₃ ≫ s₂ = s₁ ≫ ta) (hc : ta ≫ d₂ = d₁ ≫ tb) (hr : tb ≫ r₂ = r₁ ≫ t₁) :
    (s₁ ≫ d₁ ≫ r₁) ≫ t₁ = t₃ ≫ s₂ ≫ d₂ ≫ r₂ := by
  rw [reassoc_of% hs, reassoc_of% hc, hr]; simp only [assoc]

theorem hom_nat {C : Type*} [Category C] [Preadditive C] {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
    (σ₁ : ∀ n, (S₁.map (HomologicalComplex.eval C _ n)).Splitting)
    (σ₂ : ∀ n, (S₂.map (HomologicalComplex.eval C _ n)).Splitting)
    (hs : ∀ n, φ.τ₃.f n ≫ (σ₂ n).s = (σ₁ n).s ≫ φ.τ₂.f n)
    (hr : ∀ n, φ.τ₂.f n ≫ (σ₂ n).r = (σ₁ n).r ≫ φ.τ₁.f n) :
    CochainComplex.homOfDegreewiseSplit S₁ σ₁ ≫ (CategoryTheory.shiftFunctor _ (1 : ℤ)).map φ.τ₁ =
      φ.τ₃ ≫ CochainComplex.homOfDegreewiseSplit S₂ σ₂ := by
  ext n
  simp [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.shiftFunctor_map_f']
  simpa only [assoc] using aux _ _ _ _ _ _ _ _ _ _ (hs n) (φ.τ₂.comm n (n + 1)) (hr (n + 1))

section Step
variable {R : Type} [CommRing R]

def qK (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) :
    K ⟶ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).obj (K.X a) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun j hj => (hK j (by simp at hj; omega)).eq_of_src _ _)

theorem qK_iso (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) : IsIso ((qK K a hK).f a) := by
  rw [qK, HomologicalComplex.mkHomToSingle_f]; infer_instance

theorem qK_zero (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) (hm : m ≠ a) : (qK K a hK).f m = 0 :=
  (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm).eq_of_tgt _ _

def lim (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (qK K a hK)) (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) m)

theorem ι_iso (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) (hm : m ≠ a) :
    IsIso ((kernel.ι (qK K a hK)).f m) :=
  isIso_limit_cone_parallelPair_of_eq (by exact qK_zero K a hK m hm) (lim K a hK m)

theorem ker_zero (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) :
    IsZero ((kernel (qK K a hK)).X a) := by
  have := qK_iso K a hK
  rw [IsZero.iff_id_eq_zero]
  refine Fork.IsLimit.hom_ext (lim K a hK a) ?_
  have h0 : (kernel.ι (qK K a hK)).f a = 0 := by
    rw [← cancel_mono ((qK K a hK).f a), ← HomologicalComplex.comp_f, kernel.condition]; simp
  change 𝟙 _ ≫ (kernel.ι (qK K a hK)).f a = 0 ≫ (kernel.ι (qK K a hK)).f a
  rw [h0, comp_zero, zero_comp]

theorem inv_nat' {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ : C} (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) [IsIso g₁] [IsIso g₂]
    (t₂ : X₁ ⟶ X₂) (t₃ : Y₁ ⟶ Y₂) (h : g₁ ≫ t₃ = t₂ ≫ g₂) : t₃ ≫ inv g₂ = inv g₁ ≫ t₂ := inv_nat g₁ g₂ t₂ t₃ h

abbrev MainNotions (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) : ShortComplex (Cx R) :=
  ShortComplex.mk (kernel.ι (qK K a hK)) (qK K a hK) (kernel.condition _)

def spl (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) :
    ((MainNotions K a hK).map (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) m)).Splitting :=
  if h : m = a then
    ShortComplex.Splitting.ofIsZeroOfIsIso _ (by subst h; exact ker_zero K m hK) (by subst h; exact qK_iso K m hK)
  else ShortComplex.Splitting.ofIsIsoOfIsZero _ (ι_iso K a hK m h) (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (K.X a) m h)

theorem dist (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) :
    CochainComplex.trianglehOfDegreewiseSplit (MainNotions K a hK) (spl K a hK) ∈ distTriang _ :=
  (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).2 ⟨_, _, ⟨Iso.refl _⟩⟩

variable {K L : Cx R} (f : K ⟶ L) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (hL : ∀ i, i < a → IsZero (L.X i))

abbrev pc : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).obj (K.X a) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).obj (L.X a) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).map (f.f a)

theorem hqf : qK K a hK ≫ pc f a = f ≫ qK L a hL := by
  apply HomologicalComplex.to_single_hom_ext
  simp [qK, pc, HomologicalComplex.single_map_f_self]

def sf : kernel (qK K a hK) ⟶ kernel (qK L a hL) := kernel.map _ _ f (pc f a) (hqf f a hK hL)

theorem hι : sf f a hK hL ≫ kernel.ι (qK L a hL) = kernel.ι (qK K a hK) ≫ f := by
  simp [sf]

def phiS : MainNotions K a hK ⟶ MainNotions L a hL where
  τ₁ := sf f a hK hL
  τ₂ := f
  τ₃ := pc f a
  comm₁₂ := hι f a hK hL
  comm₂₃ := (hqf f a hK hL).symm

theorem hs (m : ℤ) : (phiS f a hK hL).τ₃.f m ≫ (spl L a hL m).s = (spl K a hK m).s ≫ (phiS f a hK hL).τ₂.f m := by
  unfold spl
  split_ifs with h
  · subst h
    exact @inv_nat' _ _ _ _ _ _ _ _ (qK_iso K m hK) (qK_iso L m hL) _ _ (HomologicalComplex.congr_hom (phiS f m hK hL).comm₂₃ m).symm
  · simp only [ShortComplex.Splitting.ofIsIsoOfIsZero]
    erw [comp_zero, zero_comp]

theorem hr (m : ℤ) : (phiS f a hK hL).τ₂.f m ≫ (spl L a hL m).r = (spl K a hK m).r ≫ (phiS f a hK hL).τ₁.f m := by
  unfold spl
  split_ifs with h
  · simp only [ShortComplex.Splitting.ofIsZeroOfIsIso]
    erw [comp_zero, zero_comp]
  · exact @inv_nat' _ _ _ _ _ _ _ _ (ι_iso K a hK m h) (ι_iso L a hL m h) _ _ (HomologicalComplex.congr_hom (phiS f a hK hL).comm₁₂ m).symm

def triMap : CochainComplex.triangleOfDegreewiseSplit (MainNotions K a hK) (spl K a hK) ⟶
    CochainComplex.triangleOfDegreewiseSplit (MainNotions L a hL) (spl L a hL) :=
  Triangle.homMk _ _ (sf f a hK hL) f (pc f a) (hι f a hK hL).symm (hqf f a hK hL)
    (hom_nat (phiS f a hK hL) _ _ (hs f a hK hL) (hr f a hK hL))

end Step

section Main
variable (R : Type) [CommRing R] (F : Shv R) (n : ℤ)

theorem claim : ∀ (N : ℕ) {K L : Cx R} (f : K ⟶ L),
    (∀ i : ℤ, (0 < i ∨ i < -(N : ℤ) + 1) → IsZero (K.X i) ∧ IsZero (L.X i)) →
    (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f
  | 0, K, L, f, hz, _ => relK_zero R F n f (fun i => (hz i (by omega)).1) (fun i => (hz i (by omega)).2)
  | N + 1, K, L, f, hz, hp => by
    have hK : ∀ i, i < -(N : ℤ) → IsZero (K.X i) := fun i hi => (hz i (by push_cast; omega)).1
    have hL : ∀ i, i < -(N : ℤ) → IsZero (L.X i) := fun i hi => (hz i (by push_cast; omega)).2
    have ih := claim N (sf f (-(N : ℤ)) hK hL) (fun i hi => ?_) (fun p => ?_)
    · have h3 := hp N
      rw [relK_iff] at ih h3 ⊢
      exact Tri.relY_mid _ _ (dist K _ hK) (dist L _ hL) ((Q R).mapTriangle.map (triMap f _ hK hL))
        (Yres R F) (yresIso R F) n ih h3
    · by_cases hia : i = -(N : ℤ)
      · subst hia; exact ⟨ker_zero K _ hK, ker_zero L _ hL⟩
      · have h1 := ι_iso K _ hK i hia
        have h2 := ι_iso L _ hL i hia
        have hz' := hz i (by push_cast; omega)
        exact ⟨hz'.1.of_iso (asIso ((kernel.ι (qK K _ hK)).f i)), hz'.2.of_iso (asIso ((kernel.ι (qK L _ hL)).f i))⟩
    · by_cases hpa : -(p : ℤ) = -(N : ℤ)
      · exact relK_piece_zero R F n _ p (by rw [hpa]; exact ker_zero K _ hK) (by rw [hpa]; exact ker_zero L _ hL)
      · exact relK_piece_iso R F n f _ p (@asIso _ _ _ _ ((kernel.ι (qK K _ hK)).f _) (ι_iso K _ hK _ hpa))
          (@asIso _ _ _ _ ((kernel.ι (qK L _ hL)).f _) (ι_iso L _ hL _ hpa))
          (HomologicalComplex.congr_hom (hι f _ hK hL) _) (hp p)

end Main

end LateralTheory.E.TowerFinPf

theorem LateralTheory.E.FiltPf.TowerFin_of : LateralTheory.E.FiltPf.TowerFin := by
  intro R _ F K L f n P hz hp
  exact LateralTheory.E.TowerFinPf.claim R F n (P + 1) f (fun i hi => hz i (by push_cast at hi; omega)) hp
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StalkAICRingPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StalkAICRingPf

theorem aic_loc {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hR : AIC R) : AIC S := by
  intro p hp hn
  rcases subsingleton_or_nontrivial R with hR1 | hR1
  · refine ⟨0, ?_⟩
    have h01 : (0 : S) = 1 := by
      rw [← map_zero (algebraMap R S), ← map_one (algebraMap R S), Subsingleton.elim (0 : R) 1]
    exact @Subsingleton.elim _ (subsingleton_of_zero_eq_one h01) _ _
  set n := p.natDegree with hnd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples M (Finset.univ : Finset (Fin n)) (fun i => p.coeff i)
  choose r hr using fun i : Fin n => hb i (Finset.mem_univ _)
  set β : S := algebraMap R S b with hβ
  have hu : IsUnit β := IsLocalization.map_units S b
  set q : R[X] := X ^ n + ∑ i : Fin n, C (r i * (b : R) ^ (n - 1 - i)) * X ^ (i : ℕ) with hq
  have hqm : q.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hqd : q.natDegree = n := by
    rw [hq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]; exact degree_sum_fin_lt _
  obtain ⟨c, hc⟩ := hR q hqm (hqd ▸ hn)
  refine ⟨hu.unit⁻¹ * algebraMap R S c, ?_⟩
  have key : β ^ n * p.eval (hu.unit⁻¹ * algebraMap R S c) = algebraMap R S (q.eval c) := by
    conv_lhs => rw [hp.as_sum]
    rw [← hnd, ← Fin.sum_univ_eq_sum_range]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hq, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, map_add (f := _), map_pow, map_sum, map_mul, mul_add,
      Finset.mul_sum]
    congr 1
    · rw [← mul_pow, ← mul_assoc, hu.mul_val_inv, one_mul]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr i]
      have hβn : β ^ n = β ^ 1 * β ^ (n - 1 - (i : ℕ)) * β ^ (i : ℕ) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      simp only [Algebra.smul_def, ← hβ]
      rw [hβn, mul_pow]
      have h1 : β ^ (i : ℕ) * (↑hu.unit⁻¹ : S) ^ (i : ℕ) = 1 := by rw [← mul_pow, hu.mul_val_inv, one_pow]
      linear_combination (β ^ 1 * β ^ (n - 1 - (i:ℕ)) * p.coeff i * algebraMap R S c ^ (i:ℕ)) * h1
  rw [hc, map_zero] at key
  exact (hu.pow n).mul_right_eq_zero.1 key

theorem StalkAICRing_of : LateralTheory.E.FibreEqvPf.StalkAICRing := by
  intro S hS x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let _ := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨x, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact aic_loc (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (hS.2 U hU ⟨x, hxU⟩)

end LateralTheory.E.StalkAICRingPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafDimBoundPf
noncomputable section
open CategoryTheory AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.LeafDimBoundPf

theorem dim_le_of_quasiFinite (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.QuasiFinite A S] : ringKrullDim S ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A S)) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := hPQ.le
  refine lt_of_le_of_ne (fun x hx => hle hx) ?_
  intro h
  apply hPQ.ne
  have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) P.asIdeal Q.asIdeal hle
    (congrArg PrimeSpectrum.asIdeal h)
  exact PrimeSpectrum.ext this

theorem dim_le_of_stdSmooth1 (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R S] : ringKrullDim S ≤ ringKrullDim R + 1 := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := 1) R S
  let _ : Algebra (MvPolynomial (Fin 1) R) S := g.toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin 1) R) S := hg
  have h1 := dim_le_of_quasiFinite (MvPolynomial (Fin 1) R) S
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing] at h1
  simpa using h1

theorem dim_affineOpen {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) :
    topologicalKrullDim (V : Set X) = ringKrullDim Γ(X, V) := by
  have h1 : topologicalKrullDim (V : Set X) = topologicalKrullDim (Spec Γ(X, V)) :=
    (Scheme.homeoOfIso hV.isoSpec).isHomeomorph.topologicalKrullDim_eq
  rw [h1]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

theorem dim_affineOpen_Spec_le (A : CommRingCat.{0}) {U : (Spec A).Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(Spec A, U) ≤ ringKrullDim A := by
  rw [← dim_affineOpen hU, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := A)]
  exact topologicalKrullDim_subspace_le _ _

theorem LeafDimBound_of : LateralTheory.E.LeafDescendVCut.LeafDimBound := by
  intro k _ Ω _ _ R hR D0 q hq
  have : IsNoetherianRing R := isNoetherianRing_of_fg hR
  apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := hq.exists_isStandardSmoothOfRelativeDimension x
  have : IsNoetherianRing Γ(Sp R, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let _ : Algebra Γ(Sp R, U) Γ(D0, V) := (q.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Sp R, U) Γ(D0, V) := hs
  refine ⟨(V : Set D0), V.isOpen, hx, ?_⟩
  rw [dim_affineOpen hV]
  calc ringKrullDim Γ(D0, V) ≤ ringKrullDim Γ(Sp R, U) + 1 := dim_le_of_stdSmooth1 _ _
    _ ≤ ringKrullDim R + 1 := by
      gcongr
      exact dim_affineOpen_Spec_le (CommRingCat.of R) hU

end LateralTheory.E.LeafDimBoundPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafDimOpenPf
open AlgebraicGeometry CategoryTheory LateralTheory.E.E4 Topology

namespace LateralTheory.E.LeafDimOpenPf

theorem dim_mono {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S ⊆ T) :
    topologicalKrullDim S ≤ topologicalKrullDim T :=
  (IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

theorem dim_basicOpen (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (g : A) (hg : g ≠ 0) {n : ℕ} (hn : Algebra.trdeg k A = n) :
    topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) = n := by
  let B := Localization.Away g
  have hle : Submonoid.powers g ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain B := IsLocalization.isDomain_localization hle
  have : Algebra.FiniteType A B := inferInstance
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective B hle)
  have : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B (Submonoid.powers g)
  have htr : Algebra.trdeg k B = n := by
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k A B, hn]
  rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
      (PrimeSpectrum.localization_away_isOpenEmbedding B g).isEmbedding
      (PrimeSpectrum.localization_away_comap_range B g),
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq k B htr]

theorem LeafDimOpen_of : LateralTheory.E.LeafCloseBCut.LeafDimOpen := by
  intro k _ X b _ hX U hU hne
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨A0, _, _, _, _, _, j0, _, ⟨p0, hp0⟩, -, htr0⟩ := GlobalTheory.exists_affine_chart_trdeg_eq b x0
  obtain ⟨n, -, htn⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A0
  have hK := htr0.symm.trans htn
  have hup : topologicalKrullDim X ≤ n := by
    refine GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨A, _, _, _, _, _, j, _, hx, -, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq b x
    refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, le_of_eq ?_⟩
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans
      (GlobalTheory.ringKrullDim_eq_of_trdeg_eq k A (htr.trans hK))
  refine hup.trans ?_
  have hVo : IsOpen (j0 ⁻¹' U) := hU.preimage j0.isOpenEmbedding.continuous
  have hpV : p0 ∈ j0 ⁻¹' U := by simpa [Set.mem_preimage, hp0] using hx0
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpV hVo
  have hg : g ≠ 0 := by
    rintro rfl; exact (PrimeSpectrum.mem_basicOpen _ _).mp hpg (Ideal.zero_mem _)
  have hd := dim_basicOpen k A0 g hg htn
  calc (n : WithBot ℕ∞) = topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A0)) := hd.symm
    _ = topologicalKrullDim (j0 '' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A0))) :=
      (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
        (j0.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal)
        (by rw [Set.range_comp]; exact congrArg _ Subtype.range_coe)).symm
    _ ≤ topologicalKrullDim U := dim_mono (by rintro _ ⟨q, hq, rfl⟩; exact hsub hq)

end LateralTheory.E.LeafDimOpenPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGlueExtendPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology

namespace LateralTheory.E.LeafGlueExtendPf

lemma dominant_of_generic {C W : Scheme.{0}} (e : W ⟶ C) [IsOpenImmersion e] (x : C)
    (hx : IsGenericPoint x (⊤ : Set C)) (g : Spec (C.presheaf.stalk x) ⟶ W)
    (hg : g ≫ e = C.fromSpecStalk x) : IsDominant g := by
  constructor
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro w
  obtain ⟨pt, hpt⟩ : ∃ pt : Spec (C.presheaf.stalk x), C.fromSpecStalk x pt = x :=
    ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  rw [← hg] at hpt
  have he : e (g pt) = x := hpt
  have hmem : g pt ∈ Set.range g := ⟨_, rfl⟩
  have h1 : closure ({g pt} : Set W) ⊆ closure (Set.range g) :=
    closure_mono (Set.singleton_subset_iff.mpr hmem)
  apply h1
  rw [e.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton, he]
  show e w ∈ closure {x}
  rw [show closure ({x} : Set C) = (⊤ : Set C) from hx]
  trivial

theorem LeafGlueExtend_of : LateralTheory.E.LeafExtendCut.LeafGlueExtend := by
  intro C X S _ sC p _ x hx ψ H
  choose U hyU hxU f hf1 hf2 using H
  let 𝒰 : C.OpenCover := Scheme.Cover.mkOfCovers C (fun y => (U y).toScheme) (fun y => (U y).ι)
    (fun y => ⟨y, ⟨y, hyU y⟩, rfl⟩)
  have hcompat0 : ∀ i j : C,
      pullback.fst (U i).ι (U j).ι ≫ f i = pullback.snd (U i).ι (U j).ι ≫ f j := by
    intro i j
    have : IsReduced (pullback (U i).ι (U j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (U i).ι (U j).ι ≫ (U i).ι)
    let g := pullback.lift ((U i).fromSpecStalkOfMem x (hxU i))
      ((U j).fromSpecStalkOfMem x (hxU j))
      (by rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι])
    have : IsDominant g :=
      dominant_of_generic (pullback.fst (U i).ι (U j).ι ≫ (U i).ι) x hx g
        (by simp only [g, pullback.lift_fst_assoc, Scheme.Opens.fromSpecStalkOfMem_ι])
    refine ext_of_isDominant_of_isSeparated p ?_ g ?_
    · simp only [Category.assoc, hf2]; rw [pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hf1, hf1]
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd _ _ ≫ f j :=
    fun i j => hcompat0 i j
  refine ⟨𝒰.glueMorphisms f hcompat, ?_, ?_⟩
  · have := 𝒰.ι_glueMorphisms f hcompat x
    rw [← (U x).fromSpecStalkOfMem_ι x (hxU x), Category.assoc]
    change _ ≫ 𝒰.f x ≫ _ = _
    rw [this]
    exact hf1 x
  · refine Scheme.Cover.hom_ext 𝒰 _ _ (fun y => ?_)
    rw [𝒰.ι_glueMorphisms_assoc f hcompat y]
    exact hf2 y

end LateralTheory.E.LeafGlueExtendPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AugHolds
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.TateTwistZeroAugmentationSheaf

variable (q : ℕ)

def CP : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj U := ModuleCat.of _ C(U.unop, ULift.{1} (ZMod q))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ContinuousMap.comp g f.unop.base.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem isSheaf_etaleTopology_continuousMaps : Presheaf.IsSheaf Scheme.etaleTopology.{0} (CP q) := by
  apply Presheaf.IsSheaf.of_le (le_trans Scheme.etaleTopology_le_proetaleTopology Scheme.proetaleTopology_le_fpqcTopology)
  haveI : ReflectsLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    reflectsLimitsOfSize_shrink.{1, 1, 0, 1} _
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))
  exact isSheaf_fpqcTopology_continuousMapPresheaf (ULift.{1} (ZMod q))

def augA (U : Scheme.{0}) : (Scheme.Γ ⋙ twF q 0).obj (Opposite.op U) →ₗ[ULift.{1} (ZMod q)] C(U, ULift.{1} (ZMod q)) :=
  (twRel q 0 Γ(U, ⊤)).liftQ (Finsupp.linearCombination _ (fun _ => (1 : C(U, ULift.{1} (ZMod q))))) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, -, rfl⟩
    simp)

def augP : Scheme.Γ ⋙ twF q 0 ⟶ CP q where
  app U := ModuleCat.ofHom (augA q U.unop)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro ζ c
    apply ContinuousMap.ext; intro t
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    change (augA q V.unop) (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.unop.appTop.hom) (Finsupp.single ζ c))) t =
      (augA q U.unop (Submodule.Quotient.mk (Finsupp.single ζ c))) (f.unop.base t)
    simp only [augA]
    erw [Submodule.liftQ_apply, Submodule.liftQ_apply, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single]
    rfl

def augS : sheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0) ⟶ CP q :=
  sheafifyLift Scheme.etaleTopology.{0} (augP q) (isSheaf_etaleTopology_continuousMaps q)

def augC (T : Scheme.{0}) (x : Sec (tw q 0) T) : C(T, ULift.{1} (ZMod q)) := ((augS q).app (Opposite.op T)).hom x

def aug (T : Scheme.{0}) : Sec (tw q 0) T →+ LocallyConstant T (ZMod q) :=
  AddMonoidHom.mk' (fun x => ⟨fun t => (augC q T x t).down,
      (IsLocallyConstant.iff_continuous _).2 (continuous_uliftDown.comp (ContinuousMap.continuous _))⟩)
    (fun x y => by
      ext t
      simp only [LocallyConstant.coe_add, Pi.add_apply, LocallyConstant.coe_mk, augC]
      erw [LinearMap.map_add]
      rfl)

theorem aug_nat {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U) :
    aug q V (Sec.res g x) = (aug q U x).comap g.base.hom := by
  have h := congrArg (fun h => (ModuleCat.Hom.hom h) x) ((augS q).naturality g.op)
  ext t
  simp only [aug, AddMonoidHom.mk'_apply, LocallyConstant.coe_mk, LocallyConstant.coe_comap, Function.comp_apply]
  exact congrArg (fun k : C(V, ULift.{1} (ZMod q)) => (k t).down) h

theorem aug_gen (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) : aug q U (twGen 0 ζ) = 1 := by
  have h := congrArg (fun h => (ModuleCat.Hom.hom (NatTrans.app h (Opposite.op U))) (Submodule.Quotient.mk (Finsupp.single ζ 1)))
    (toSheafify_sheafifyLift Scheme.etaleTopology.{0} (augP q) (isSheaf_etaleTopology_continuousMaps q))
  ext t
  simp only [aug, AddMonoidHom.mk'_apply, LocallyConstant.coe_mk, LocallyConstant.coe_one, Pi.one_apply]
  have h2 := congrArg (fun k : C(U, ULift.{1} (ZMod q)) => (k t).down) h
  refine h2.trans ?_
  simp only [augP, augA]
  erw [ModuleCat.hom_ofHom, Submodule.liftQ_apply, Finsupp.linearCombination_single]
  simp

theorem Aug_holds : LateralTheory.E.TateTwistZeroAugmentationBijective.Aug := fun q => ⟨aug q, fun g x => aug_nat q g x, aug_gen q⟩

theorem Tw0_of (hB : LateralTheory.E.TateTwistZeroAugmentationBijective.AugBij) : LateralTheory.E.LCIsoPf.Tw0 := LateralTheory.E.TateTwistZeroAugmentationBijective.Tw0_of Aug_holds hB

end LateralTheory.E.TateTwistZeroAugmentationSheaf
end
end
