module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafPurPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafLocPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafDescPf

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcDegPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

section Gen
variable {C : Type*} [Category C] [Abelian C]

theorem cokPO_iso {A B Q : C} (f : A ⟶ B) (l r : B ⟶ Q) (h : IsPushout f f l r) :
    IsIso (cokernel.map f r f l h.w) := by
  refine ⟨⟨cokernel.desc r (h.desc (cokernel.π f) 0 (by simp)) (by simp), ?_, ?_⟩⟩
  · ext; simp
  · ext
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    refine h.hom_ext ?_ ?_
    · simp
    · simp

theorem cokMap_comp {A B A' B' A'' B'' : C} (f : A ⟶ B) (f' : A' ⟶ B') (f'' : A'' ⟶ B'')
    (a : A ⟶ A') (b : B ⟶ B') (w : f ≫ b = a ≫ f') (a' : A' ⟶ A'') (b' : B' ⟶ B'') (w' : f' ≫ b' = a' ≫ f'') :
    cokernel.map f f' a b w ≫ cokernel.map f' f'' a' b' w' =
      cokernel.map f f'' (a ≫ a') (b ≫ b') (by rw [← Category.assoc, w, Category.assoc, w', Category.assoc]) := by
  ext; simp

theorem cokPO_transfer {A' B' Q' A B Q : C} (f' : A' ⟶ B') (l' r' : B' ⟶ Q') (h' : IsPushout f' f' l' r')
    (f : A ⟶ B) (l r : B ⟶ Q) (h : IsPushout f f l r) (a : A' ⟶ A) (b : B' ⟶ B) (m : Q' ⟶ Q)
    (w : f' ≫ b = a ≫ f) (wl : l' ≫ m = b ≫ l) (wr : r' ≫ m = b ≫ r)
    (hi : IsIso (cokernel.map f' f a b w)) : IsIso (cokernel.map r' r b m wr) := by
  have := cokPO_iso f' l' r' h'
  have := cokPO_iso f l r h
  have e : cokernel.map f' r' f' l' h'.w ≫ cokernel.map r' r b m wr =
      cokernel.map f' f a b w ≫ cokernel.map f r f l h.w := by
    rw [cokMap_comp, cokMap_comp]; ext; simp [wl]
  have : cokernel.map r' r b m wr = inv (cokernel.map f' r' f' l' h'.w) ≫
      (cokernel.map f' f a b w ≫ cokernel.map f r f l h.w) := by rw [← e]; simp
  rw [this]; infer_instance

theorem cokIso_comp {A B A' B' : C} (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (w : f ≫ b = a ≫ f')
    [IsIso a] [IsIso b] : IsIso (cokernel.map f f' a b w) :=
  ⟨⟨cokernel.map f' f (inv a) (inv b) (by rw [IsIso.eq_inv_comp, ← Category.assoc, ← w]; simp),
    by ext; simp, by ext; simp⟩⟩

end Gen

section Spec
variable (R : Type) [CommRing R]

theorem emb_f (p : ℕ) : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl

theorem extKey (p : ℕ) {K L : ChainComplex (Shv R) ℕ} (φ : K ⟶ L) :
    (HomologicalComplex.eval _ _ (-(p:ℤ))).map ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map φ) =
      (K.extendXIso _ (emb_f p)).hom ≫ φ.f p ≫ (L.extendXIso _ (emb_f p)).inv :=
  HomologicalComplex.extendMap_f φ _ (emb_f p)

def chIso (p : ℕ) : chains R ⋙ HomologicalComplex.eval _ _ (-(p : ℤ)) ≅
    (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p)) ⋙ free R :=
  NatIso.ofComponents (fun K => ((chainsN R).obj K).extendXIso ComplexShape.embeddingDownNat (emb_f p)) (by
    intro K L g
    change (HomologicalComplex.eval _ _ _).map ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map
      ((chainsN R).map g)) ≫ _ = _ ≫ (free R).map (g.app _)
    rw [extKey]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl)

instance : PreservesColimitsOfShape WalkingSpan (free R) := by
  have h1 : PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0}) := inferInstance
  have h2' : PreservesColimitsOfSize.{0, 0} (ModuleCat.free (ULift.{1, 0} R)) :=
    (ModuleCat.adj (ULift.{1, 0} R)).leftAdjoint_preservesColimits
  have h2 : PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1, 0} R)) := inferInstance
  have h3 : PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1, 0} R)) := inferInstance
  have : PreservesColimitsOfShape WalkingSpan (freeP R) := by
    unfold freeP; infer_instance
  unfold free; infer_instance

end Spec

section Gen2

theorem cokF {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesColimitsOfShape WalkingParallelPair F] {A B A' B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (w : f ≫ b = a ≫ f')
    (hi : IsIso (cokernel.map (F.map f) (F.map f') (F.map a) (F.map b) (by rw [← F.map_comp, w, F.map_comp]))) :
    IsIso (F.map (cokernel.map f f' a b w)) := by
  have e : F.map (cokernel.map f f' a b w) = inv (cokernelComparison f F) ≫
      (cokernel.map (F.map f) (F.map f') (F.map a) (F.map b) (by rw [← F.map_comp, w, F.map_comp]) ≫
        cokernelComparison f' F) := by
    rw [IsIso.eq_inv_comp]; ext; simp [← Functor.map_comp]
  rw [e]; infer_instance

theorem cokNat {C E : Type*} [Category C] [Abelian C] [Category E] (Φ Ψ : E ⥤ C) (α : Φ ≅ Ψ)
    {X' Y' X Y : E} (g' : X' ⟶ Y') (g : X ⟶ Y) (a : X' ⟶ X) (b : Y' ⟶ Y) (w : g' ≫ b = a ≫ g)
    (hi : IsIso (cokernel.map (Ψ.map g') (Ψ.map g) (Ψ.map a) (Ψ.map b) (by simp only [← Functor.map_comp, w]))) :
    IsIso (cokernel.map (Φ.map g') (Φ.map g) (Φ.map a) (Φ.map b) (by simp only [← Functor.map_comp, w])) := by
  have h1 := cokIso_comp (Φ.map g') (Ψ.map g') (α.hom.app X') (α.hom.app Y') (α.hom.naturality g')
  have h2 := cokIso_comp (Φ.map g) (Ψ.map g) (α.hom.app X) (α.hom.app Y) (α.hom.naturality g)
  have e : cokernel.map (Φ.map g') (Φ.map g) (Φ.map a) (Φ.map b) (by simp only [← Functor.map_comp, w]) =
      (cokernel.map (Φ.map g') (Ψ.map g') (α.hom.app X') (α.hom.app Y') (α.hom.naturality g') ≫
        cokernel.map (Ψ.map g') (Ψ.map g) (Ψ.map a) (Ψ.map b) (by simp only [← Functor.map_comp, w])) ≫
      inv (cokernel.map (Φ.map g) (Ψ.map g) (α.hom.app X) (α.hom.app Y) (α.hom.naturality g)) := by
    rw [IsIso.eq_comp_inv, cokMap_comp, cokMap_comp]; ext; simp
  rw [e]; infer_instance

end Gen2

section Main
variable (R : Type) [CommRing R]

theorem hPO (P : Arrow Spc) (p : SimplexCategoryᵒᵖ) :
    IsPushout ((free R).map (P.hom.app p)) ((free R).map (P.hom.app p)) ((free R).map ((dbl.inl P).app p))
      ((free R).map ((dbl.inr P).app p)) :=
  ((evaluation _ _).obj p ⋙ free R).map_isPushout (IsPushout.of_hasPushout P.hom P.hom)

theorem chains_zero {j : ℤ} (hj : ¬ ∃ p : ℕ, j = -(p : ℤ)) (X : Spc) : IsZero (((chains R).obj X).X j) :=
  ((chainsN R).obj X).isZero_extend_X ComplexShape.embeddingDownNat j (fun i hi => hj ⟨i, hi.symm⟩)

theorem cok_zero {A B : Cx R} (g : A ⟶ B) (j : ℤ) (hB : IsZero (B.X j)) : IsZero ((cokernel g).X j) :=
  (IsZero.of_epi (cokernel.π (g.f j)) hB).of_iso (PreservesCokernel.iso (HomologicalComplex.eval _ _ j) g)

end Main

theorem LeafExcDeg_of : LeafExcDeg := by
  intro q P' P φ h
  have key : ∀ j, IsIso ((cokC q φ).f j) := by
    intro j
    by_cases hj : ∃ p : ℕ, j = -(p : ℤ)
    · obtain ⟨p, rfl⟩ := hj
      show IsIso ((HomologicalComplex.eval _ _ _).map (cokC q φ))
      refine cokF (HomologicalComplex.eval _ _ (-(p : ℤ))) _ _ _ _ _ ?_
      refine cokNat (chains (ZMod q) ⋙ HomologicalComplex.eval _ _ (-(p : ℤ))) _ (chIso (ZMod q) p)
        (dbl.inr P') (dbl.inr P) φ.right (dbl.map φ) (dbl.inr_map φ) ?_
      exact cokPO_transfer _ _ _ (hPO (ZMod q) P' _) _ _ _ (hPO (ZMod q) P _) _ _ _ (freeSq _ φ _)
        (by
          show (free (ZMod q)).map (NatTrans.app (dbl.inl P') (op (SimplexCategory.mk p))) ≫
            (free (ZMod q)).map (NatTrans.app (dbl.map φ) (op (SimplexCategory.mk p))) = _
          rw [← Functor.map_comp, ← NatTrans.comp_app, dbl.inl_map', NatTrans.comp_app, Functor.map_comp])
        (by
          show (free (ZMod q)).map (NatTrans.app (dbl.inr P') (op (SimplexCategory.mk p))) ≫
            (free (ZMod q)).map (NatTrans.app (dbl.map φ) (op (SimplexCategory.mk p))) = _
          rw [← Functor.map_comp, ← NatTrans.comp_app, dbl.inr_map, NatTrans.comp_app, Functor.map_comp]) (h _)
    · exact isIso_of_source_target_iso_zero _ (cok_zero _ _ j (chains_zero _ hj _)).isoZero
        (cok_zero _ _ j (chains_zero _ hj _)).isoZero
  exact HomologicalComplex.Hom.isIso_of_components _

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHsRelPfSplit
section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHsRelPf
noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem hk_pull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cone_map_congr {R : Type} [CommRing R] {K₁ L₁ K₂ L₂ : Cx R} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂} (h : f₁ ≫ b = a ≫ f₂) (h' : f₁ ≫ b' = a' ≫ f₂) (ha : a = a') (hb : b = b') :
    mappingCone.map f₁ f₂ a b h = mappingCone.map f₁ f₂ a' b' h' := by
  subst ha; subst hb; rfl

theorem dbl_sq (R : Type) [CommRing R] (P : Arrow Spc) :
    (chains R).map P.hom ≫ (chains R).map (dbl.inl P) = (chains R).map P.hom ≫ (chains R).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (pushout.condition (f := P.hom) (g := P.hom))

def dblCone (R : Type) [CommRing R] (P : Arrow Spc) :
    mappingCone ((chains R).map P.hom) ⟶ mappingCone ((chains R).map (dbl.inr P)) :=
  mappingCone.map _ _ ((chains R).map P.hom) ((chains R).map (dbl.inl P)) (dbl_sq R P)

theorem dblMap_sq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains R).map (dbl.inr P') ≫ (chains R).map (dbl.map φ) = (chains R).map φ.right ≫ (chains R).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp, dbl.inr_map]

def dblConeMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    mappingCone ((chains R).map (dbl.inr P')) ⟶ mappingCone ((chains R).map (dbl.inr P)) :=
  mappingCone.map _ _ ((chains R).map φ.right) ((chains R).map (dbl.map φ)) (dblMap_sq R φ)

theorem dblCone_nat (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    coneMap R φ ≫ dblCone R P = dblCone R P' ≫ dblConeMap R φ := by
  unfold coneMap dblCone dblConeMap
  rw [← mappingCone.map_comp, ← mappingCone.map_comp]
  apply cone_map_congr
  · rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (Arrow.w φ)
  · rw [← Functor.map_comp, ← Functor.map_comp, inl_map]

theorem inr_dblConeMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    mappingCone.inr _ ≫ dblConeMap R φ = (chains R).map (dbl.map φ) ≫ mappingCone.inr _ := by
  simp [dblConeMap, mappingCone.map]

def LeafDblConeQI : Prop := ∀ (R : Type) [CommRing R] (P : Arrow Spc), Mono P.hom → QuasiIso (dblCone R P)

def LeafConeSplit : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (g : K ⟶ L) (r : L ⟶ K), g ≫ r = 𝟙 K →
  ∀ (F : Shv R) (n : ℤ), Function.Injective (HK.pull R (mappingCone.inr g) F n) ∧
    ∀ y : HK R L F n, HK.pull R g F n y = 0 ↔ ∃ x, HK.pull R (mappingCone.inr g) F n x = y

theorem inr_fold_chains (R : Type) [CommRing R] (P : Arrow Spc) :
    (chains R).map (dbl.inr P) ≫ (chains R).map (dbl.fold P) = 𝟙 _ := by
  rw [← Functor.map_comp, dbl.inr_fold, CategoryTheory.Functor.map_id]

def psi (q : ℕ) (P : Arrow Spc) (n i : ℤ) (hS : LeafConeSplit) :
    HK (ZMod q) (mappingCone ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n →+ Hs q P n i :=
  (HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n).codRestrict _ fun x =>
    ((hS (ZMod q) _ _ (inr_fold_chains (ZMod q) P) (tw q i) n).2 _).2 ⟨x, rfl⟩

theorem psi_bij (q : ℕ) (P : Arrow Spc) (n i : ℤ) (hS : LeafConeSplit) : Function.Bijective (psi q P n i hS) := by
  have h := hS (ZMod q) _ _ (inr_fold_chains (ZMod q) P) (tw q i) n
  refine ⟨fun a b hab => h.1 (congrArg Subtype.val hab), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (h.2 y.1).1 y.2
  exact ⟨x, Subtype.ext hx⟩

theorem leafHsRel_of (hD : LeafDblConeQI) (hS : LeafConeSplit) : LeafHsRel := by
  intro h1 q i
  let θ : ∀ (P : Arrow Spc) (n : ℤ), Mono P.hom →
      (HK (ZMod q) (mappingCone ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hrel (ZMod q) P.hom (tw q i) n) :=
    fun P n h => by
      haveI := hD (ZMod q) P h
      exact AddEquiv.ofBijective (HK.pull (ZMod q) (dblCone (ZMod q) P) (tw q i) n) (h1 (ZMod q) _ (tw q i) n)
  refine ⟨fun P n h => (AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm.trans (θ P n h), ?_⟩
  intro P' P φ h' h n x
  have key : (AddEquiv.ofBijective (psi q P' n i hS) (psi_bij q P' n i hS)).symm (Hs.pull q φ n i x) =
      HK.pull (ZMod q) (dblConeMap (ZMod q) φ) (tw q i) n
        ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x) := by
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    set y := (AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x with hy
    have hx : x = psi q P n i hS y := by
      rw [hy]; exact ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).apply_symm_apply x).symm
    rw [hx]
    change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.map φ)) (tw q i) n
        (HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n y) =
      HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n (HK.pull (ZMod q) (dblConeMap (ZMod q) φ) (tw q i) n y)
    rw [← hk_pull_comp, ← hk_pull_comp, inr_dblConeMap]
  change HK.pull (ZMod q) (dblCone (ZMod q) P') (tw q i) n
      ((AddEquiv.ofBijective (psi q P' n i hS) (psi_bij q P' n i hS)).symm (Hs.pull q φ n i x)) =
    HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n (HK.pull (ZMod q) (dblCone (ZMod q) P) (tw q i) n
      ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x))
  rw [key, ← hk_pull_comp, ← hk_pull_comp, dblCone_nat]

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex Pretriangulated

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem toHom_pull (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    CohomologyClass.toHom (HK.pull R f F n x) =
      (HomotopyCategory.quotient _ _).map f ≫ CohomologyClass.toHom x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.toHom (CohomologyClass.mk (zcomp (Cocycle.ofHom f) x (zero_add n))) = _
  rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, ← Functor.map_comp]
  congr 1
  ext p : 1
  simp [zcomp, Cocycle.equivHomShift_symm_apply, Cochain.rightShift_v _ n 0 (zero_add n) p p (add_zero p) (p + n) rfl]

theorem leafConeSplit : LeafConeSplit := by
  intro R _ K L g r hgr F n
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished g
  let Q := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)
  have z12 : Q.map g ≫ Q.map (mappingCone.inr g) = 0 := comp_distTriang_mor_zero₁₂ _ hT
  let m3 : Q.obj (mappingCone g) ⟶ (Q.obj K)⟦(1 : ℤ)⟧ := (mappingCone.triangleh g).mor₃
  have z31 : m3 ≫ (Q.map g)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have ex2 : ∀ {X} (f : Q.obj L ⟶ X), Q.map g ≫ f = 0 → ∃ w : Q.obj (mappingCone g) ⟶ X,
      f = Q.map (mappingCone.inr g) ≫ w := fun f hf => Triangle.yoneda_exact₂ _ hT f hf
  have ex3 : ∀ {X} (f : Q.obj (mappingCone g) ⟶ X), Q.map (mappingCone.inr g) ≫ f = 0 →
      ∃ w : (Q.obj K)⟦(1 : ℤ)⟧ ⟶ X, f = m3 ≫ w :=
    fun f hf => Triangle.yoneda_exact₃ _ hT f hf
  have hinj : ∀ {M : Cx R} (a b : HK R M F n), CohomologyClass.toHom a = CohomologyClass.toHom b → a = b :=
    fun a b h => (CohomologyClass.toHom_bijective _ _ _).1 h
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · apply hinj
    have h0 : Q.map (mappingCone.inr g) ≫ CohomologyClass.toHom x = 0 := by
      rw [← toHom_pull, hx, map_zero]
    obtain ⟨w, hw⟩ := ex3 _ h0
    rw [hw, map_zero]
    have : w = (Q.map g)⟦(1 : ℤ)⟧' ≫ (Q.map r)⟦(1 : ℤ)⟧' ≫ w := by
      rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hgr, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    rw [this, ← Category.assoc, z31, zero_comp]
  · have h0 : Q.map g ≫ CohomologyClass.toHom y = 0 := by
      rw [← toHom_pull, hy, map_zero]
    obtain ⟨w, hw⟩ := ex2 _ h0
    obtain ⟨x, hx⟩ := (CohomologyClass.toHom_bijective (mappingCone g) _ _).2 w
    refine ⟨x, hinj _ _ ?_⟩
    rw [toHom_pull, hx, hw]
  · rintro ⟨x, rfl⟩
    apply hinj
    rw [toHom_pull, toHom_pull, map_zero, ← Category.assoc, z12, zero_comp]

def LeafDblCok : Prop := ∀ (R : Type) [CommRing R] (P : Arrow Spc), Mono P.hom → ∀ n : ℤ,
  IsIso (cokernel.map _ _ _ _ (sqw (dbl_sq R P) n))

theorem leafDblConeQI_of (hC : LeafConeCok) (hK : LeafDblCok) : LeafDblConeQI := by
  intro R _ P h
  have hi : Mono (dbl.inr P) := ⟨fun a b e => by
    have := congrArg (· ≫ dbl.fold P) e
    simpa [Category.assoc, dbl.inr_fold] using this⟩
  exact hC R _ _ _ _ (dbl_sq R P) (leafChainsMono R _ h) (leafChainsMono R _ hi) (hK R P h)

theorem etale_relative_cohomology_iso_of_cone_and_double_cokernel_isos (hC : LeafConeCok) (hK : LeafDblCok) : LeafHsRel :=
  leafHsRel_of (leafDblConeQI_of hC hK) leafConeSplit

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.FinLeafChart
namespace LateralTheory.Fin.LeafChart
theorem etale_chart_localization_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafLoc := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafLoc_of
theorem etale_chart_shrinking_open_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafShrink := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafShrink_of
theorem etale_chart_conormal_rank_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafRank := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of
theorem etale_chart_generator_choice_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafPick := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafPick_of
theorem etale_chart_ideal_span_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafSpan := by
  apply LateralTheory.CohomologicalPurity.LeafSpanPf.LeafSpan_of
theorem etale_chart_etaleness_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafEt := by
  apply LateralTheory.CohomologicalPurity.LeafEtPf.LeafEt_of
theorem etale_chart_coordinate_functions_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafCoord := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafCoord_of <;> first | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds
theorem etale_chart_section_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafSec := by
  apply LateralTheory.CohomologicalPurity.LeafSecPf.LeafSec_of
theorem etale_chart_polynomial_algebra_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := by
  apply LateralTheory.CohomologicalPurity.LeafPolyPf.LeafPoly_of
theorem etale_chart_neighborhood_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd_of <;> first | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds
theorem etale_coordinate_chart_existence : LateralTheory.CohomologicalPurity.LeafChart := by
  apply LateralTheory.CohomologicalPurity.ChartCut.goal_of <;> first | exact etale_chart_localization_property_holds | exact etale_chart_shrinking_open_property_holds | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds | exact etale_chart_coordinate_functions_property_holds | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds | exact etale_chart_neighborhood_property_holds
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafChart := etale_coordinate_chart_existence
end LateralTheory.Fin.LeafChart
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafActNatPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem dbl_map_fold {P' P : Arrow Spc} (φ : P' ⟶ P) :
    dbl.map φ ≫ dbl.fold P = dbl.fold P' ≫ φ.right := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext
  · simp only [dbl.map, dbl.fold, pushout.map]
    erw [pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    simp
  · simp only [dbl.map, dbl.fold, pushout.map]
    erw [pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc, pushout.inr_desc_assoc]
    simp

theorem LeafActNat_of : LeafActNat := by
  intro hA q _ P' P φ n m i j a b
  apply Subtype.ext
  have hc := (hA q).1 (dbl.map φ) (pull _ (dbl.fold P) (tw q i) n a) b.1
  change pull _ (dbl.map φ) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 -
      pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) =
    cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) -
      pull _ (dbl.fold P') _ _ (pull _ (dbl.inr P') _ _
        (cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1)))
  have e1 : pull (ZMod q) (dbl.map φ) (tw q i) n (pull _ (dbl.fold P) _ n a) =
      pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a) := by
    rw [← pull_comp, ← pull_comp, dbl_map_fold]
  have hcc : pull (ZMod q) (dbl.map φ) (tw q (i + j)) (n + m) (cup q (pull _ (dbl.fold P) _ n a) b.1) =
      cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) := by
    rw [hc, e1]
  rw [map_sub, hcc]
  congr 1
  rw [← hcc, ← pull_comp _ (dbl.map φ) (dbl.fold P), dbl_map_fold, pull_comp _ (dbl.fold P') φ.right,
    ← pull_comp _ φ.right (dbl.inr P), ← dbl.inr_map, pull_comp _ (dbl.inr P') (dbl.map φ)]

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTauUPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) : pull _ f (tw q i') n' (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f (tw q i) n a) := by
  subst h1; subst h2; rfl

theorem pull_cpow (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (h6 q).2.1 f hI]
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (h6 q).1, ih]

theorem tail_fst (d : ℕ) (R : Type) [CommRing R] :
    (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) ≫ prod.fst ≫ Pj.line d 0 =
      prod.fst ≫ Pj.line (d + 1) 1 := by
  rw [prod.map_fst_assoc, Pj.tail_line]

theorem pull_hyp (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (hI : Inv q (PR d 0 R)) :
    pull _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) _ _ (hyp q d 0 R) = hyp q (d + 1) 1 R := by
  unfold hyp
  rw [(h6 q).2.2.1 _ _ hI, tail_fst]

theorem tail_poly (hG : LeafGeo) (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
    (hq : IsUnit (q : R)) (n i : ℤ) (a : ∀ j : Fin d, Ht q (sp R) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) (tw q i) n (poly q d 0 R d n i a) =
      poly q (d + 1) 1 R d n i a := by
  have hI := hG.2.1 q d 0 R hq
  unfold poly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast, (h6 q).1, ← pull_comp, prod.map_snd, Category.comp_id, pull_cpow h6 q _ hI, pull_hyp h6 q d R hI]

theorem LeafTauU_of (hG : LeafGeo) : LeafTauU := by
  intro hPB hTl H q _ d R _ hq n i
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hb := (hTl H q d R hq i n).comp (hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q d R hq n i)
  convert hb using 1
  funext a
  exact (tail_poly hG h6 q d R hq n i a).symm

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTauTopPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem tt_cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'')
    (h4 : i' = i'') (a : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 a) = Ht.cast (h1.trans h3) (h2.trans h4) a := by
  subst h1; subst h2; subst h3; subst h4; rfl

theorem tt_pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) : pull _ f _ _ (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f _ _ a) := by
  subst h1; subst h2; rfl

theorem tt_cup_cast_right {q : ℕ} {E : Spc} {n i m j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i)
    (b : Ht q E m j) : cup q a (Ht.cast h1 h2 b) = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1; subst h2; rfl

theorem tt_cup_cast_left {q : ℕ} {E : Spc} {n i m j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a : Ht q E n i)
    (b : Ht q E m j) : cup q (Ht.cast h1 h2 a) b = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1; subst h2; rfl

theorem tauTop : LeafTauTop := by
  intro H q _ d R _ n i x a
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hr : DivisorRingCompatibility := H.2.2.2.2.2.1
  let e : ∀ j : Fin (d + 1), Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)) :=
    Fin.lastCases (motive := fun j : Fin (d + 1) =>
        Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)))
      (x.cast (by simp) (by simp))
      (fun j => (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring) (by simp only [Fin.val_castSucc]; ring))
  refine ⟨e, by simp [e], ?_⟩
  have he : ∀ j : Fin d, e j.castSucc = (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring)
      (by simp only [Fin.val_castSucc]; ring) := fun j => by simp [e]
  have hl : e (Fin.last d) = x.cast (by simp) (by simp) := by simp [e]
  unfold poly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, Fin.sum_univ_castSucc]
  refine (add_comm _ _).trans ?_
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [he, tt_pull_cast, tt_cup_cast_left, (h6 q).1, (hr q _).2.1, tt_cup_cast_right]
    repeat rw [tt_cast_cast]
    rfl
  · rw [hl, tt_pull_cast, tt_cup_cast_left]
    repeat rw [tt_cast_cast]
    rfl

theorem LeafTauTop_of : LeafTauTop := tauTop

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPushPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut
namespace PushPf

variable {J' J : Type} [SmallCategory J'] [SmallCategory J] {D' : J' ⥤ PSh} {D : J ⥤ PSh} {G : J' ⥤ J}

def phi (α : D' ⟶ G ⋙ D) (U : Scheme.{0}ᵒᵖ) : (D'.flip.obj U).Elements ⥤ (D.flip.obj U).Elements where
  obj e := (D.flip.obj U).elementsMk (G.obj e.obj) ((α.app e.obj).app U e.val)
  map {e e'} g := Functor.Elements.homMk (G.map g.hom) (by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality g.hom) U) e.val
    exact h.symm.trans (congrArg (fun y => (α.app e'.obj).app U y) g.map_val))
  map_id e := Functor.Elements.hom_ext (G.map_id e.obj)
  map_comp g g' := Functor.Elements.hom_ext (G.map_comp g.hom g'.hom)

theorem elem_ext {X : Type} [Category X] {F : J ⥤ Type} (A B : X ⥤ F.Elements) (ho : ∀ x, A.obj x = B.obj x)
    (hm : A ⋙ Functor.Elements.π F = B ⋙ Functor.Elements.π F) : A = B := by
  refine CategoryTheory.Functor.ext ho (fun x y g => ?_)
  apply (Functor.Elements.π F).map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hm g

theorem phi_nat (α : D' ⟶ G ⋙ D) {U U' : Scheme.{0}ᵒᵖ} (f : U ⟶ U') :
    phi α U ⋙ (D.flip.map f).mapElements = (D'.flip.map f).mapElements ⋙ phi α U' :=
  elem_ext _ _ (fun e => by
    refine Functor.Elements.ext _ _ rfl ?_
    change (D.flip.obj U').map (𝟙 (G.obj e.obj))
        ((D.obj (G.obj e.obj)).map f ((α.app e.obj).app U e.val)) =
      (α.app e.obj).app U' ((D'.obj e.obj).map f e.val)
    rw [(D.flip.obj U').map_id]
    exact (ConcreteCategory.congr_hom ((α.app e.obj).naturality f) e.val).symm) rfl

def bmap (α : D' ⟶ G ⋙ D) : hoc D' ⟶ hoc D where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => (chn x ⋙ phi α U : Fin (n.unop.len + 1) ⥤ _)
      naturality := fun U U' f => by
        ext x
        change (chn x ⋙ (D'.flip.map f).mapElements) ⋙ phi α U' = (chn x ⋙ phi α U) ⋙ (D.flip.map f).mapElements
        rw [Functor.assoc, Functor.assoc, phi_nat] }
  naturality n m θ := by
    ext U x
    rfl

theorem goal (α : D' ⟶ G ⋙ D) {Y' Y : PSh} (f : Y' ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y') (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, α.app j ≫ c (G.obj j) = c' j ≫ f) : bmap α ≫ aug c hc = aug c' hc' ≫ disc.map f := by
  ext n U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h ((chn x).obj 0).obj) U) ((chn x).obj 0).val

end PushPf

theorem LeafPush_of : LeafPush := fun _ _ _ _ _ _ _ α _ _ f c' c hc' hc h => ⟨PushPf.bmap α, PushPf.goal α f c' c hc' hc h⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafDescPfGlue
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

theorem le_of_comp {Y Z X : Scheme.{0}} {W : Y.Opens} {V : Z.Opens} (f : Y ⟶ Z) (g : Z ⟶ X) (U : X.Opens)
    (hV : V = g ⁻¹ᵁ U) (k : Y ⟶ X) (hk : f ≫ g = k) (hW : W ≤ k ⁻¹ᵁ U) : W ≤ f ⁻¹ᵁ V := by
  subst hV hk; intro w hw; exact hW hw

theorem pre_comp {Y Z X : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ X) (V : Z.Opens) (U : X.Opens) (hV : V = g ⁻¹ᵁ U) :
    f ⁻¹ᵁ V = (f ≫ g) ⁻¹ᵁ U := by
  subst hV; ext; rfl

theorem LeafPcGlue_pf : LeafPcGlue := by
  intro q X U m i hG A p s hcov H
  let E := fun a => Equiv.ofBijective _ (pc_bij (q := q) (p a) m i)
  obtain ⟨c, hc⟩ := hG A (fun a => (p a).j.opensRange) (fun a => (E a).symm (s a)) (fun x hx => hcov x hx) (by
    intro a b x hxa hxb hxU
    obtain ⟨y, rfl⟩ : x ∈ Set.range (p a).j := hxa
    obtain ⟨t, u, h, hcomm, ⟨z, rfl⟩, heq⟩ := H a b y hxU hxb
    let P : Pc U := ⟨t.Y, t.j ≫ (p a).j, inferInstance, t.V, t.hV.trans (pre_comp _ _ _ U (p a).hV)⟩
    have ha : P.j.opensRange ≤ (p a).j.opensRange := by rintro _ ⟨w, rfl⟩; exact ⟨t.j w, rfl⟩
    have hb : P.j.opensRange ≤ (p b).j.opensRange := by
      rintro _ ⟨w, rfl⟩
      refine ⟨u w, ?_⟩
      change (u ≫ (p b).j) w = (t.j ≫ (p a).j) w
      rw [hcomm]
    have ea : P.j.isoOpensRange.hom ≫ X.homOfLE ha = t.j ≫ (p a).j.isoOpensRange.hom := by
      rw [← cancel_mono ((p a).j.opensRange.ι)]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]; rfl
    have eb : P.j.isoOpensRange.hom ≫ X.homOfLE hb = u ≫ (p b).j.isoOpensRange.hom := by
      rw [← cancel_mono ((p b).j.opensRange.ι)]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]
      exact hcomm
    have hPV : P.V ≤ P.j ⁻¹ᵁ U := P.hV.le
    have ha' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE ha ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl
    have hb' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE hb ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl
    refine ⟨P.j.opensRange, ha, hb, ha', hb', ⟨z, rfl⟩, ?_⟩
    apply (pc_bij P m i).1
    have k1 : P.V ≤ (t.j ≫ (p a).j.isoOpensRange.hom) ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]) hPV
    have k2 : P.V ≤ (u ≫ (p b).j.isoOpensRange.hom) ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← hcomm]) hPV
    rw [pull_pull _ _ ea _ _ _ _ _ k1, pull_pull _ _ eb _ _ _ _ _ k2,
      ← pull_pull t.j _ rfl _ _ _ t.hV.le (pc_le (p a)) k1, ← pull_pull u _ rfl _ _ _ h (pc_le (p b)) k2]
    change Hs.pull q _ m i (E a ((E a).symm (s a))) = Hs.pull q _ m i (E b ((E b).symm (s b)))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact heq)
  refine ⟨c, fun a => ?_⟩
  rw [pc_res, hc a]
  exact (E a).apply_symm_apply (s a)

theorem LeafDesc_of' (hD : LeafDict) (hF : LeafFlq) (hS : LeafDescOSep) (hG : LeafDescOGlue) : LeafDesc :=
  LeafDesc_of hD hF hS hG LeafPcGlue_pf

end LateralTheory.CohomologicalPurity.Cl
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafAffEqvPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem affSieve_mem (U : Scheme.{0}) (S : Sieve U)
    (h : ∀ (A : Type) [CommRing A] (f : Spec (CommRingCat.of A) ⟶ U), S f) : S ∈ Scheme.etaleTopology U := by
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_ (Scheme.Cover.mem_grothendieckTopology U.affineCover)
  rintro _ _ ⟨_, k, _, ⟨i⟩, rfl⟩
  exact S.downward_closed (h _ (U.affineCover.f i)) k

theorem locBij {R : Type} [CommRing R] {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ : F ⟶ G)
    (h : ∀ (A : Type) [CommRing A], IsIso (φ.app (op (Spec (CommRingCat.of A))))) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology φ ∧ Presheaf.IsLocallySurjective Scheme.etaleTopology φ := by
  have hb : ∀ (A : Type) [CommRing A], Function.Bijective (φ.app (op (Spec (CommRingCat.of A)))) :=
    fun A _ => ConcreteCategory.bijective_of_isIso _
  refine ⟨⟨fun {X} x y hxy => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · refine affSieve_mem _ _ fun A _ f => ?_
    apply (hb A).1
    change φ.app _ (F.map f.op x) = φ.app _ (F.map f.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  · refine affSieve_mem _ _ fun A _ f => ?_
    obtain ⟨t, ht⟩ := (hb A).2 (G.map f.op s)
    exact ⟨t, ht⟩

theorem freeIso (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q)
    (h : ∀ (A : Type) [CommRing A], Function.Bijective (g.app (op (Spec (CommRingCat.of A))))) :
    IsIso ((free R).map g) := by
  have h2 : ∀ (A : Type) [CommRing A], IsIso (((freeP R).map g).app (op (Spec (CommRingCat.of A)))) := by
    intro A _
    have : IsIso (g.app (op (Spec (CommRingCat.of A)))) := (isIso_iff_bijective _).2 (h A)
    change IsIso ((uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R)).map (g.app (op (Spec (CommRingCat.of A)))))
    infer_instance
  obtain ⟨h3, h4⟩ := locBij _ h2
  have hW : Scheme.etaleTopology.W ((freeP R).map g) := by
    rw [GrothendieckTopology.W_iff_isLocallyBijective]; exact ⟨h3, h4⟩
  exact (GrothendieckTopology.W_iff _ _).1 hW

theorem chainsIso (R : Type) [CommRing R] {E E' : Spc} (e : E ⟶ E')
    (h : ∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
      (fun x : Sx E n (Spec (CommRingCat.of A)) => (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)) :
    IsIso ((chains R).map e) := by
  have : IsIso (((SimplicialObject.whiskering _ _).obj (free R)).map e) := by
    have hh : ∀ n, IsIso ((((SimplicialObject.whiskering _ _).obj (free R)).map e).app n) := by
      intro n
      induction n using Opposite.rec with | op n => ?_
      induction n using SimplexCategory.rec with | _ n => ?_
      exact freeIso R _ (h n)
    exact NatIso.isIso_of_isIso_app _
  change IsIso ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map
    ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map e)))
  infer_instance

theorem LeafAffEqv_of : LeafAffEqv := by
  intro hA1 q _ E E' e h i n
  have := chainsIso (ZMod q) e h
  exact hA1 (ZMod q) ((chains (ZMod q)).map e) (tw q i) n

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafRelHocPfX
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem pull_iso_bij (R : Type) [CommRing R] {E E' : Spc} (i : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R i.hom F n) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R i.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, i.inv_hom_id, pull_id]
  · rw [← pull_comp, i.hom_inv_id, pull_id]

theorem eqv_of_arrowIso (R : Type) [CommRing R] {E' E G' G : Spc} {f : E' ⟶ E} {g : G' ⟶ G} (F : Shv R)
    (e : Arrow.mk f ≅ Arrow.mk g) (hf : Eqv R f F) : Eqv R g F := by
  intro n
  have w : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
  have k : (pull R e.hom.left F n) ∘ (pull R g F n) = (pull R f F n) ∘ (pull R e.hom.right F n) := by
    funext x
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, w]
  have hl : Function.Bijective (pull R e.hom.left F n) :=
    pull_iso_bij R ((Arrow.leftFunc).mapIso e) F n
  have hr : Function.Bijective (pull R e.hom.right F n) :=
    pull_iso_bij R ((Arrow.rightFunc).mapIso e) F n
  have hc : Function.Bijective ((pull R e.hom.left F n) ∘ (pull R g F n)) := by
    rw [k]; exact (hf n).comp hr
  exact (Function.Bijective.of_comp_iff' hl _).mp hc

theorem eqv_sum_RRelH (hS : LeafSum) (R : Type) [CommRing R] (F : Shv R) {A : Type} {E' E : A → Spc} (c' : Cofan E') (c : Cofan E)
    (hc' : Nonempty (IsColimit c')) (hc : Nonempty (IsColimit c)) (f : ∀ a, E' a ⟶ E a) (φ : c'.pt ⟶ c.pt)
    (hφ : ∀ a, c'.inj a ≫ φ = f a ≫ c.inj a) (hf : ∀ a, Eqv R (f a) F) : Eqv R φ F := by
  intro n
  have k : (fun (y : H R c'.pt F n) (a : A) => pull R (c'.inj a) F n y) ∘ (pull R φ F n) =
      (fun (z : ∀ a, H R (E a) F n) (a : A) => pull R (f a) F n (z a)) ∘
        (fun (x : H R c.pt F n) (a : A) => pull R (c.inj a) F n x) := by
    funext x a
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, hφ]
  have h1 := hS R F A E' c' hc' n
  have h2 := hS R F A E c hc n
  have hc3 : Function.Bijective ((fun (y : H R c'.pt F n) (a : A) => pull R (c'.inj a) F n y) ∘ (pull R φ F n)) := by
    rw [k]
    exact (Function.Bijective.piMap (fun a => hf a n)).comp h2
  exact (Function.Bijective.of_comp_iff' h1 _).mp hc3

def LeafRelLev : Prop := LeafLevel → ∀ (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D)
  (Y G : PSh) (g : G ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) (h' : (hocF J).map α ≫ aug c hc = aug c' hc')
  (n : SimplexCategoryᵒᵖ),
  ∃ (A : Type) (ι : A → J) (E' E : A → Spc) (k' : Cofan E') (k : Cofan E) (f : ∀ a, E' a ⟶ E a) (φ : k'.pt ⟶ k.pt),
    Nonempty (IsColimit k') ∧ Nonempty (IsColimit k) ∧ (∀ a, k'.inj a ≫ φ = f a ≫ k.inj a) ∧
    (∀ a, Nonempty (Arrow.mk (pbRel (disc.map g) (disc.map (α.app (ι a))) (disc.map (c' (ι a))) (disc.map (c (ι a)))
      (h (ι a))) ≅ Arrow.mk (f a))) ∧
    Nonempty (Arrow.mk φ ≅ Arrow.mk (disc.map ((pbRel (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h').app n)))

theorem LeafRelHoc_of (hL : LeafLevel) (hS : LeafSum) (hB : LeafRelLev) : LeafRelHoc := by
  intro hA3 R _ F J _ D' D α Y G g c' c hc' hc h h' hE
  apply hA3
  intro n
  obtain ⟨A, ι, E', E, k', k, f, φ, h1, h2, h3, h4, ⟨e⟩⟩ := hB hL J D' D α Y G g c' c hc' hc h h' n
  refine eqv_of_arrowIso R F e ?_
  exact eqv_sum_RRelH hS R F k' k h1 h2 f φ h3 fun a => eqv_of_arrowIso R F (h4 a).some (hE (ι a))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafHensH : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (C : Type) [CommRing C] (K : Ideal C), HenselianRing C K →
  IsUnit (q : C) → ∀ i : ℤ, Eqv (ZMod q) (spMap (Ideal.Quotient.mk K)) (tw q i)

def LeafAffQuot : Prop := LeafQuot → ∀ (d : ℕ) (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) →
  ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η →
  Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I →
  Function.Bijective ((Ideal.Quotient.mk K).comp (η.comp (ψ.comp MvPolynomial.C)))

def LeafExcAff : Prop := Hyp → LeafIndExc → ∀ (d q : ℕ) [NeZero q] (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), IsUnit (q : R) →
  Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) → ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η →
  Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I → ∃ h,
  Exc q (opnMap (Spec.map (CommRingCat.ofHom (η.comp ψ))) (off C K) (off _ (Ideal.span (Set.range MvPolynomial.X))) h)

theorem spMap_comp' {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  change sch.map _ = sch.map _ ≫ sch.map _
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  change sch.map (Spec.map (𝟙 _)) = _
  rw [Spec.map_id, CategoryTheory.Functor.map_id]

theorem eqv_spMap_bij {A B : Type} [CommRing A] [CommRing B] (e : A →+* B) (he : Function.Bijective e)
    {S : Type} [CommRing S] (F : Shv S) : Eqv S (spMap e) F := by
  let E := RingEquiv.ofBijective e he
  have h1 : (E.symm : B →+* A).comp e = RingHom.id A := by ext x; exact E.symm_apply_apply x
  have h2 : e.comp (E.symm : B →+* A) = RingHom.id B := by ext x; exact E.apply_symm_apply x
  have : IsIso (spMap e) := ⟨⟨spMap (E.symm : B →+* A), by rw [← spMap_comp', h2, spMap_id'],
    by rw [← spMap_comp', h1, spMap_id']⟩⟩
  exact eqv_iso _ F

theorem LeafPrdAff_of (hT : LeafThom) (hA : LeafActNat) (h1 : LeafHensH) (h2 : LeafAffQuot) (h3 : LeafExcAff)
    (hQ : LeafQuot) (hI : LeafIndExc) : LeafPrdAff := by
  intro hyp d q _ R B C _ _ _ ψ η hq hψ I K hη hK hH hI' hy n i
  have hth : IsThom d (thom d) := @pick_spec _ ⟨fun _ _ _ _ _ _ => 0⟩ _ (hT hyp d)
  have hqP : IsUnit (q : MvPolynomial (Fin d) R) := by simpa using hq.map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)
  have hqC : IsUnit (q : C) := by simpa using hq.map ((η.comp ψ).comp MvPolynomial.C)
  obtain ⟨h, hE⟩ := h3 hyp hI d q R B C ψ η hq hψ I K hη hK hI'
  have hnat := (hth q).1 (MvPolynomial (Fin d) R) C (η.comp ψ) (Ideal.span (Set.range MvPolynomial.X)) K MvPolynomial.X rfl
    hy h hqP
  have hg := (hth q).2.2.1 R (Ideal.span (Set.range MvPolynomial.X)) rfl hq n i
  let p := pull (ZMod q) (spMap ((η.comp ψ).comp (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))) (tw q i) n
  have hmk := h1 hyp q C K hH hqC i n
  have he := eqv_spMap_bij _ (h2 hQ d R B C ψ η hψ I K hη hK hI') (tw q i) n
  have hp : Function.Bijective p := by
    rw [spMap_comp'] at he
    have e2 : (pull (ZMod q) (spMap (Ideal.Quotient.mk K) ≫ spMap (η.comp (ψ.comp MvPolynomial.C))) (tw q i) n : _ → _) =
        (pull (ZMod q) (spMap (Ideal.Quotient.mk K)) (tw q i) n) ∘ p := funext fun x => pull_comp _ _ _ _ _ x
    rw [e2] at he
    exact (Function.Bijective.of_comp_iff' hmk p).1 he
  have hpb : ∀ b, p b = pull (ZMod q) (spMap (η.comp ψ)) (tw q i) n (pull (ZMod q) (spMap MvPolynomial.C) (tw q i) n b) :=
    fun b => by
      change pull _ _ _ _ b = _
      rw [← pull_comp, ← spMap_comp']
  refine (Function.Bijective.of_comp_iff _ hp).1 ?_
  have key := (hE (n + 2 * d) (i + d)).comp hg
  convert key using 1
  funext b
  refine Eq.trans ?_ (hA hyp.2.2.2.2.1 q _ _ _ n (2 * d) i d _ _).symm
  rw [hnat, Function.comp_apply, hpb]
  rfl

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafLocFstPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

instance schPresPb : PreservesLimitsOfShape WalkingCospan sch :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (yoneda ⋙ disc))

theorem LeafLocFst_of (hZ : LeafZ) : LeafLocFst := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro hE H d P V q hq i
  have := P.cl
  obtain ⟨⟨z, hpb⟩, -⟩ := hZ P.X P.Z P.ι V (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) (eta H P V)
  have hpb' := hpb.map sch
  have := H.hens Γ(P.X, V.1) (P.ι.ker.ideal V)
  have hu : IsUnit (q : H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) := by
    simpa using hq.map ((eta H P V).comp (P.X.presheaf.map (homOfLE le_top).op).hom)
  have e : pullback.fst (sch.map (hensTo H P V)) (sch.map P.ι) = hpb'.isoPullback.inv ≫
      sch.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((P.ι.ker.ideal V).map (eta H P V))))) :=
    hpb'.isoPullback_inv_fst.symm
  rw [e]
  exact eqv_comp (eqv_iso _ _) (hE q _ _ hu i)

end LateralTheory.CohomologicalPurity.TubeCut
end
end
