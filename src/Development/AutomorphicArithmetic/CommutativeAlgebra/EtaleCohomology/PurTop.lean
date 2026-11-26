module

public import Development.EtaleCohomology.CohomologicalPurity.FinLeafAW
public import Development.EtaleCohomology.CohomologicalPurity.FinLeafCl
public import Development.EtaleCohomology.CohomologicalPurity.FinLeafHens
public import Development.EtaleCohomology.CohomologicalPurity.FinLeafIndExc
public import Development.EtaleCohomology.CohomologicalPurity.LeafPurNatPf
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HocolimAugmentationInjectiveOfPurityInputs
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProductLevelwiseOfAlexanderWhitney
public import Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPfQuot

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHensHPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem LeafHensH_of : LeafHensH := by
  intro hH q _ C _ K hK hq i
  exact hH.2.2.2.2.2.2.2.2.2.2.2 q C K hq i

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafZPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem zpf_pushout {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) (I : Ideal R) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ)))
      (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) := by
  letI := φ.toAlgebra
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I
  refine (CommRingCat.isPushout_tensorProduct R B (R ⧸ I)).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) e.toRingEquiv.toCommRingCatIso.symm ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · ext x
    simp [e]
    rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply]; rfl
  · ext x
    simp [e]
    rw [Algebra.smul_def, mul_one]; rfl

theorem zpf_sqA (X Z : Scheme.{0}) (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ι.ker.ideal V))))
      (ι.ker.subschemeCover.f V ≫ inv ι.toImage) V.2.fromSpec ι := by
  have h0 : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ι.ker.ideal V))))
      (ι.ker.subschemeCover.f V) V.2.fromSpec ι.ker.subschemeι := by
    have hf := V.2.isOpenImmersion_fromSpec
    have hc : IsOpenImmersion (ι.ker.subschemeCover.f V) := ι.ker.subschemeCover.map_prop V
    refine @IsOpenImmersion.isPullback _ _ _ _ _ _ _ _ hc hf ?_ ?_
    · exact (Scheme.IdealSheafData.subschemeCover_map_subschemeι _ V).trans
        (Scheme.IdealSheafData.glueDataObjι_ι _ V)
    · exact (congrArg (ι.ker.subschemeι ⁻¹ᵁ ·) V.2.opensRange_fromSpec).trans
        (Scheme.IdealSheafData.opensRange_subschemeCover_map _ V).symm
  refine h0.of_iso (Iso.refl _) (Iso.refl _) (asIso ι.toImage).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
    exact ι.toImage_imageι

theorem zpf_range_mk {A : Type} [CommRing A] (J : Ideal A) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      PrimeSpectrum.zeroLocus (J : Set A) := by
  have := _root_.range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := J))
  rw [Ideal.mk_ker] at this
  exact this

theorem LeafZ_of : LeafZ := by
  intro X Z ι _ V B _ φ
  have hP := (isPullback_SpecMap_of_isPushout _ _ _ _
    (zpf_pushout φ (ι.ker.ideal V))).paste_vert (zpf_sqA X Z ι V)
  refine ⟨⟨_, hP⟩, ?_⟩
  intro U hU
  have hr : ∀ x, (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) x ∈ Set.range ι ↔
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((ι.ker.ideal V).map φ)))) := by
    intro x; constructor
    · rintro ⟨y, hy⟩
      obtain ⟨a, ha, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      refine ⟨hP.isoPullback.inv a, ?_⟩
      rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]; exact ha
    · rintro ⟨a, rfl⟩
      exact ⟨_, (Scheme.Hom.comp_apply _ _ a).symm.trans
        ((congrArg (fun k => k a) hP.w.symm).trans (Scheme.Hom.comp_apply _ _ a))⟩
  ext x
  have h1 : x ∈ off B ((ι.ker.ideal V).map φ) ↔ x ∉ PrimeSpectrum.zeroLocus (((ι.ker.ideal V).map φ : Ideal B) : Set B) :=
    Iff.rfl
  have h2 : x ∈ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U ↔
      (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) x ∈ (U : Set X) := Iff.rfl
  simp only [SetLike.mem_coe]
  rw [h1, h2, hU, Set.mem_compl_iff, hr, zpf_range_mk]
  exact Iff.rfl
end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafLocHenPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem hs_pull_id (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  have e : dbl.map (𝟙 P) = 𝟙 _ := by
    set_option synthInstance.maxHeartbeats 200000 in
      apply pushout.hom_ext <;> (simp [dbl.map]; try rfl)
  rw [e, pull_id]

theorem exc_iso (q : ℕ) {P' P : Arrow Spc} (e : P' ≅ P) : Exc q e.hom := fun n i =>
  Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv n i,
    fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id],
    fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id]⟩

theorem abv_ext {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {Q : Arrow Spc} (α β : Q ⟶ abv U π)
    (hr : α.right = β.right) (hm : α ≫ abvMap U π = β ≫ abvMap U π) : α = β := by
  apply Arrow.hom_ext _ _ _ hr
  set_option synthInstance.maxHeartbeats 200000 in
    apply pullback.hom_ext
  · have wa := Arrow.w α
    have wb := Arrow.w β
    change α.left ≫ pullback.fst π (sch.map U.ι) = Q.hom ≫ α.right at wa
    change β.left ≫ pullback.fst π (sch.map U.ι) = Q.hom ≫ β.right at wb
    rw [hr] at wa
    exact wa.trans wb.symm
  · exact congrArg CommaMorphism.left hm

theorem opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens)
    (h1 : U'' ≤ f ⁻¹ᵁ U') (h2 : U' ≤ g ⁻¹ᵁ U) (h3 : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap f U'' U' h1 ≫ opnMap g U' U h2 = opnMap (f ≫ g) U'' U h3 := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp]

theorem LeafLocHen_of (hI : LeafIndExc) (hZ : LeafZ) (hA : LeafAbv) : LeafLocHen := by
  intro hyp H d P V q hq hfg h
  obtain ⟨a1, -, -, a4, -, -, -, -, b1, -, -, -⟩ := hyp
  have := P.cl
  set A := Γ(P.X, V.1)
  set I := P.ι.ker.ideal V
  set φ := eta H P V
  set g := V.2.fromSpec
  set f : Spec (H.obj A I) ⟶ Spec A := Spec.map (CommRingCat.ofHom φ)
  have hqA : IsUnit (q : A) := by
    have := hq.map (P.X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
    simpa using this
  have zB := (hZ P.X P.Z P.ι V (H.obj A I) φ).2 P.U P.hU
  have zA := (hZ P.X P.Z P.ι V A (RingHom.id A)).2 P.U P.hU
  rw [Ideal.map_id] at zA
  have e1 : Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ g = g := by
    rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 _ from rfl, Spec.map_id, Category.id_comp]
  rw [e1] at zA
  have hle : off (H.obj A I) (I.map φ) ≤ f ⁻¹ᵁ (off A I) := by
    rw [zB, zA]; intro x hx; exact hx
  have ind := hI a1 a4 b1 q φ I hfg (H.ind A I) hqA hle
  obtain ⟨eA, eAr, eAm⟩ := hA _ _ g _ P.U zA
  obtain ⟨eB, eBr, eBm⟩ := hA _ _ (f ≫ g) _ P.U zB
  have sq : eB.hom ≫ abvRel P.U (sch.map f) (sch.map (f ≫ g)) (sch.map g) h = opnMap f _ _ hle ≫ eA.hom := by
    apply abv_ext
    · rw [Arrow.comp_right, Arrow.comp_right, eBr, eAr]
      exact (Category.id_comp (sch.map f)).trans (Category.comp_id (sch.map f)).symm
    · rw [Category.assoc, Category.assoc, abvRel_abvMap, eBm, eAm, opnMap_comp]
  have e : abvRel P.U (sch.map f) (sch.map (f ≫ g)) (sch.map g) h = eB.inv ≫ opnMap f _ _ hle ≫ eA.hom := by
    rw [Iso.eq_inv_comp, sq]
  rw [e]
  exact exc_comp q (exc_iso q eB.symm) (exc_comp q ind (exc_iso q eA))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafLocPrdPfX
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem opnMap_comp_RLocP {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens)
    (h : U'' ≤ f ⁻¹ᵁ U') (h' : U' ≤ g ⁻¹ᵁ U) (h'' : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap f U'' U' h ≫ opnMap g U' U h' = opnMap (f ≫ g) U'' U h'' := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp]

theorem hs_pull_id_RLocP (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  exact @_root_.LateralTheory.CohomologicalPurity.TubeCut.hs_pull_id q P n i x

theorem LeafLocPrd_of (hCl : LeafCl) (hPR : LeafPrdRing) (hZ : LeafZ) (hAbv : LeafAbv) (hAN : LeafActNat) : LeafLocPrd := by
  intro hyp H d P V q _ hq hG
  have a6 : DivisorNaturality := hyp.2.2.2.2.1
  haveI := P.cl
  have hcl : IsCl d (fcl d) := pick_spec (hCl hyp d)

  have hqA : IsUnit (q : Γ(P.X, V.1)) := by
    have := hq.map (P.X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
    simpa using this
  have hoff : ∀ (B : Type) [CommRing B] (φ : Γ(P.X, V.1) →+* B),
      off B ((P.ι.ker.ideal V).map φ) = (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ P.U :=
    fun B _ φ => (hZ P.X P.Z P.ι V B φ).2 P.U P.hU
  have e0 : off Γ(P.X, V.1) (P.ι.ker.ideal V) = V.2.fromSpec ⁻¹ᵁ P.U := by
    have e := hoff Γ(P.X, V.1) (RingHom.id _)
    rw [Ideal.map_id] at e
    rw [e]; rfl
  have h0 : off Γ(P.X, V.1) (P.ι.ker.ideal V) ≤ V.2.fromSpec ⁻¹ᵁ P.U := le_of_eq e0
  haveI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  obtain ⟨c, hcdef⟩ : ∃ c, c = Hs.pull q (opnMap V.2.fromSpec _ _ h0) _ _ (fcl d q P) := ⟨_, rfl⟩
  have hc : ∀ (B : Type) [CommRing B] (φ : Γ(P.X, V.1) →+* B) (x : Fin d → B) hx h, φ.Etale →
      Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B ((P.ι.ker.ideal V).map φ)) (off _ (P.ι.ker.ideal V)) h) _ _ c
        = thom d q B ((P.ι.ker.ideal V).map φ) x hx := by
    intro B _ φ x hx h hφ
    obtain ⟨z, hz⟩ := (hZ P.X P.Z P.ι V B φ).1
    haveI : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr hφ
    have h' : off B ((P.ι.ker.ideal V).map φ) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ P.U :=
      le_of_eq (hoff B φ)
    rw [hcdef, ← hs_pull_comp, opnMap_comp_RLocP _ _ _ _ _ _ _ h']
    exact (hcl q).1 P hq B _ x hx _ z h' inferInstance hz
  have key := hPR hyp H d q Γ(P.X, V.1) (P.ι.ker.ideal V) hqA hG.1 hG.2 c hc

  have hU' := hoff _ (eta H P V)
  obtain ⟨e, he1, he2⟩ := hAbv _ P.X (hensTo H P V) _ P.U hU'
  intro n i
  have hh : off (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ((P.ι.ker.ideal V).map (eta H P V)) ≤
      Spec.map (CommRingCat.ofHom (eta H P V)) ⁻¹ᵁ off Γ(P.X, V.1) (P.ι.ker.ideal V) := by
    rw [hoff _ (eta H P V), e0]; intro x hx; exact hx
  have hk := key hh n i
  have hpe : Function.Bijective (Hs.pull q e.hom (n + 2 * d) (i + d)) :=
    Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv _ _,
      fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id_RLocP],
      fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id_RLocP]⟩
  have hcomp : ∀ a : Ht q (sch.obj (Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)))) n i,
      Hs.pull q e.hom _ _ (Hs.act q (P := abv P.U (sch.map (hensTo H P V))) a
        (Hs.pull q (abvMap P.U (sch.map (hensTo H P V))) _ _ (fcl d q P))) =
      Hs.act q (P := opn (off (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ((P.ι.ker.ideal V).map (eta H P V)))) a
        (Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom (eta H P V))) _ _ hh) _ _ c) := by
    intro a
    refine (hAN a6 q _ _ e.hom n (2 * d) i d a _).trans ?_
    rw [he1]
    erw [pull_id]
    rw [← hs_pull_comp, he2, hcdef, ← hs_pull_comp, opnMap_comp_RLocP]
  refine (Function.Bijective.of_comp_iff' hpe _).1 ?_
  have hf := funext hcomp
  rw [show (⇑(Hs.pull q e.hom (n + 2 * d) (i + d)) ∘ fun a : Ht q (sch.obj (Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)))) n i =>
      Hs.act q (P := abv P.U (sch.map (hensTo H P V))) a
        (Hs.pull q (abvMap P.U (sch.map (hensTo H P V))) _ _ (fcl d q P))) = _ from hf]
  exact hk

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafAbvPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

instance sch_preservesLimits : PreservesLimitsOfSize.{0, 0} sch := by
  unfold sch
  infer_instance

theorem sch_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPullback (sch.map fst) (sch.map snd) (sch.map f) (sch.map g) :=
  h.map sch

theorem isPullback_resLE {Y X : Scheme.{0}} (w : Y ⟶ X) (U : X.Opens) :
    IsPullback (w ⁻¹ᵁ U).ι (w.resLE U (w ⁻¹ᵁ U) le_rfl) w U.ι := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict w U).flip

theorem LeafAbv_of : LeafAbv := by
  intro Y X w U' U h
  subst h
  have hP := sch_isPullback (isPullback_resLE w U)
  refine ⟨Arrow.isoMk hP.isoPullback (Iso.refl _) ?_, rfl, ?_⟩
  · simp [opn, abv]
  · apply Arrow.hom_ext
    · rw [Arrow.comp_left]
      exact hP.isoPullback_hom_snd
    · rw [Arrow.comp_right]
      exact Category.id_comp _

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafRefinePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex
namespace LateralTheory.CohomologicalPurity.TubeCut

variable {d : ℕ}

theorem hmap_congr (H : Hens) {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} {φ ψ : A →+* B}
    (e : φ = ψ) (h : I ≤ J.comap φ) (h' : I ≤ J.comap ψ) : H.map φ h = H.map ψ h' := by subst e; rfl

theorem hmap_sq (H : Hens) {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {I : Ideal A} {J : Ideal B} {K : Ideal C} {L : Ideal D} (a : A →+* B) (b : B →+* D) (c : A →+* C) (e : C →+* D)
    (ha : I ≤ J.comap a) (hb : J ≤ L.comap b) (hc : I ≤ K.comap c) (he : K ≤ L.comap e) (e0 : b.comp a = e.comp c) :
    (H.map b hb).comp (H.map a ha) = (H.map e he).comp (H.map c hc) := by
  rw [← H.map_comp a b ha hb (fun x hx => hb (ha hx)), ← H.map_comp c e hc he (fun x hx => he (hc hx))]
  exact hmap_congr H e0 _ _

theorem appLE_congr {X Y : Scheme.{0}} {u v : X ⟶ Y} (e : u = v) (U : Y.Opens) (W : X.Opens) (h : W ≤ u ⁻¹ᵁ U) :
    u.appLE U W h = v.appLE U W (e ▸ h) := by subst e; rfl

theorem idl {P' P : SP d} (φ : P'.Hom P) (V : P.X.affineOpens) (V' : P'.X.affineOpens) (h : V'.1 ≤ φ.f ⁻¹ᵁ V.1) :
    P.ι.ker.ideal V ≤ (P'.ι.ker.ideal V').comap (φ.f.appLE V.1 V'.1 h).hom := by
  have := P.cl; have := P'.cl
  intro a ha
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, Scheme.Hom.ker_apply, RingHom.mem_ker]
  rw [← CommRingCat.comp_apply, P'.ι.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr φ.cart.w,
    Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]

theorem cotangentAtUnit_tangentBijection_naturality (H : Hens) {P' P : SP d} (φ : P'.Hom P) (V1 V2 : P.X.affineOpens) (V1' V2' : P'.X.affineOpens)
    (h1 : V1'.1 ≤ φ.f ⁻¹ᵁ V1.1) (h2 : V2'.1 ≤ φ.f ⁻¹ᵁ V2.1) (hV : V1 ≤ V2) (hV' : V1' ≤ V2') :
    Spec.map (CommRingCat.ofHom (H.map _ (P'.ι.ker.ideal_le_comap_ideal hV'))) ≫
      Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V2.1 V2'.1 h2).hom (idl φ V2 V2' h2))) =
    Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V1.1 V1'.1 h1).hom (idl φ V1 V1' h1))) ≫
      Spec.map (CommRingCat.ofHom (H.map _ (P.ι.ker.ideal_le_comap_ideal hV))) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact hmap_sq H _ _ _ _ _ _ _ _ (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE])

theorem henselization_spec_map_commutes_with_smooth_pair_hom (H : Hens) {P' P : SP d} (φ : P'.Hom P) (V : P.X.affineOpens) (V' : P'.X.affineOpens)
    (h : V'.1 ≤ φ.f ⁻¹ᵁ V.1) :
    Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V.1 V'.1 h).hom (idl φ V V' h))) ≫ hensTo H P V =
      hensTo H P' V' ≫ φ.f := by
  dsimp only [hensTo, eta]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, H.map_η, CommRingCat.ofHom_comp, Spec.map_comp_assoc]
  exact (congrArg (_ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec φ.f V.2 V'.2 h)).trans (Category.assoc _ _ _).symm

abbrev RJ {P' P : SP d} (φ : P'.Hom P) : Type :=
  {p : P'.X.affineOpens × P.X.affineOpens // Good P' p.1 ∧ Good P p.2 ∧ p.1.1 ≤ φ.f ⁻¹ᵁ p.2.1}

def Sys.ref (hC : LateralTheory.CohomologicalPurity.LeafChart) {P' P : SP d} (φ : P'.Hom P) : Sys P' where
  J := RJ φ
  V j := j.1.1
  mono h := (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1
  good j := j.2.1
  cov x := by
    obtain ⟨V, hV, -, g⟩ := hC d P (φ.f x) ⊤ trivial
    obtain ⟨V', hV', l, g'⟩ := hC d P' x (φ.f ⁻¹ᵁ V.1) hV
    exact ⟨⟨(V', V), g', g, l⟩, hV'⟩
  dir x j k hj hk := by
    have hj2 : φ.f x ∈ j.1.2.1 := j.2.2.2 hj
    have hk2 : φ.f x ∈ k.1.2.1 := k.2.2.2 hk
    obtain ⟨V, hV, l, g⟩ := hC d P (φ.f x) (j.1.2.1 ⊓ k.1.2.1) ⟨hj2, hk2⟩
    obtain ⟨V', hV', l', g'⟩ := hC d P' x (j.1.1.1 ⊓ k.1.1.1 ⊓ φ.f ⁻¹ᵁ V.1) ⟨⟨hj, hk⟩, hV⟩
    exact ⟨⟨(V', V), g', g, l'.trans inf_le_right⟩, ⟨l'.trans (inf_le_left.trans inf_le_left), l.trans inf_le_left⟩,
      ⟨l'.trans (inf_le_left.trans inf_le_right), l.trans inf_le_right⟩, hV'⟩

theorem EtaleRefine_of_push (hP : LeafPush) : LeafRefine := by
  intro hC H d P' P φ
  let S' := Sys.ref hC φ
  let G1 : S'.J ⥤ (Sys.all hC P').J := Monotone.functor (f := fun j => (⟨j.1.1, j.2.1⟩ : {V : P'.X.affineOpens // Good P' V}))
    (fun _ _ h => (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1)
  let G2 : S'.J ⥤ (Sys.all hC P).J := Monotone.functor (f := fun j => (⟨j.1.2, j.2.2.1⟩ : {V : P.X.affineOpens // Good P V}))
    (fun _ _ h => (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2)
  let α1 : S'.hen H ⋙ yoneda ⟶ G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda :=
    { app := fun j => (𝟙 ((S'.hen H ⋙ yoneda).obj j) : _ ⟶ (G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda).obj j)
      naturality := fun j k f => (Category.comp_id _).trans (Category.id_comp ((G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda).map f)).symm }
  obtain ⟨a, ha⟩ := hP _ _ _ _ G1 α1 _ _ (𝟙 (yoneda.obj P'.X)) _ _ (S'.cocHen H) ((Sys.all hC P').cocHen H)
    (fun j => (Category.id_comp _).trans (Category.comp_id _).symm)
  have ea : a ≫ (Sys.all hC P').π H = S'.π H := by
    have := ha; rw [disc.map_id, Category.comp_id] at this; exact this
  let α2 : S'.hen H ⋙ yoneda ⟶ G2 ⋙ (Sys.all hC P).hen H ⋙ yoneda :=
    { app := fun j => yoneda.map (Spec.map (CommRingCat.ofHom
        (H.map (φ.f.appLE (j.1.2).1 (j.1.1).1 j.2.2.2).hom (idl φ j.1.2 j.1.1 j.2.2.2))))
      naturality := fun j k f => (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map
        (cotangentAtUnit_tangentBijection_naturality H φ j.1.2 k.1.2 j.1.1 k.1.1 j.2.2.2 k.2.2.2 (Prod.le_def.1 (Subtype.coe_le_coe.2 f.le)).2
          (Prod.le_def.1 (Subtype.coe_le_coe.2 f.le)).1)).trans (yoneda.map_comp _ _)) }
  obtain ⟨b, hb⟩ := hP _ _ _ _ G2 α2 _ _ (yoneda.map φ.f) _ _ (S'.cocHen H) ((Sys.all hC P).cocHen H)
    (fun j => (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map (henselization_spec_map_commutes_with_smooth_pair_hom H φ j.1.2 j.1.1 j.2.2.2)).trans
      (yoneda.map_comp _ _)))
  exact ⟨S', a, b, ea, hb⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleExcisionHocolimOfLocalProperties
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut

namespace UpperTheory.Cb

private theorem dbl_map_id (P : Arrow Spc) : dbl.map (𝟙 P) = 𝟙 _ := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext <;> simp [dbl.map] <;> rfl

private theorem hs_pull_id (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  rw [dbl_map_id, pull_id]

private theorem exc_iso (q : ℕ) {P' P : Arrow Spc} (e : P' ≅ P) : Exc q e.hom := fun n i =>
  Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv n i,
    fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id],
    fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id]⟩

private theorem pb_app {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (n : SimplexCategoryᵒᵖ) :
    IsPullback (P := disc.obj ((pullback π (sch.map U.ι)).obj n)) (X := disc.obj (E.obj n)) (Y := sch.obj U.toScheme) (Z := sch.obj X)
      (disc.map ((pullback.fst π (sch.map U.ι)).app n))
      (disc.map ((pullback.snd π (sch.map U.ι)).app n)) (disc.map (π.app n)) (sch.map U.ι) := by
  have h := (IsPullback.of_hasPullback π (sch.map U.ι)).map ((evaluation _ _).obj n)
  exact IsPullback.of_forall_isPullback_app fun _ => h

private def levIso {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (n : SimplexCategoryᵒᵖ) :
    (lev n).obj (abv U π) ≅ abv U (E := disc.obj (E.obj n)) (disc.map (π.app n)) :=
  Arrow.isoMk (pb_app U π n).isoPullback (Iso.refl _)
    ((pb_app U π n).isoPullback_hom_fst.trans (Category.comp_id _).symm)

private theorem pbRel_fst {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pbRel g a π' π h ≫ pullback.fst π g = pullback.fst π' g ≫ a := pullback.lift_fst _ _ _

private theorem pbRel_snd {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pbRel g a π' π h ≫ pullback.snd π g = pullback.snd π' g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private theorem abvRel_square {X : Scheme.{0}} (U : X.Opens) {A B C D : Spc} (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (pA : A ⟶ sch.obj X) (pB : B ⟶ sch.obj X) (pC : C ⟶ sch.obj X) (pD : D ⟶ sch.obj X) (h1 : a ≫ pB = pA) (h2 : b ≫ pD = pB)
    (h3 : c ≫ pC = pA) (h4 : d ≫ pD = pC) (w : a ≫ b = c ≫ d) :
    abvRel U a pA pB h1 ≫ abvRel U b pB pD h2 = abvRel U c pA pC h3 ≫ abvRel U d pC pD h4 := by
  apply Arrow.hom_ext
  · change pbRel _ a _ _ h1 ≫ pbRel _ b _ _ h2 = pbRel _ c _ _ h3 ≫ pbRel _ d _ _ h4
    apply pullback.hom_ext
    · simp only [Category.assoc, pbRel_fst]
      rw [← Category.assoc, pbRel_fst, ← Category.assoc, pbRel_fst, Category.assoc, Category.assoc, w]
    · simp only [Category.assoc, pbRel_snd]
  · exact w

private theorem iso_gen {B G E' E P' P : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π')
    (f' : P' ⟶ E') (s' : P' ⟶ G) (f : P ⟶ E) (s : P ⟶ G) (hp' : IsPullback f' s' π' g) (hp : IsPullback f s π g)
    (t : P' ⟶ P) (h1 : t ≫ f = f' ≫ a) (h2 : t ≫ s = s') :
    t ≫ hp.isoPullback.hom = hp'.isoPullback.hom ≫ pbRel g a π' π h := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pbRel_fst, hp.isoPullback_hom_fst, ← Category.assoc _ (pullback.fst _ _),
      hp'.isoPullback_hom_fst, h1]
  · rw [Category.assoc, Category.assoc, pbRel_snd, hp.isoPullback_hom_snd, hp'.isoPullback_hom_snd, h2]

private theorem lev_abvRel {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (a : E' ⟶ E) (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X)
    (h : a ≫ π = π') (n : SimplexCategoryᵒᵖ) (hn) :
    (lev n).map (abvRel U a π' π h) ≫ (levIso U π n).hom =
      (levIso U π' n).hom ≫ abvRel U (E' := disc.obj (E'.obj n)) (E := disc.obj (E.obj n)) (disc.map (a.app n))
        (disc.map (π'.app n)) (disc.map (π.app n)) hn := by
  have f1 := pbRel_fst (sch.map U.ι) a π' π h
  have f2 := pbRel_snd (sch.map U.ι) a π' π h
  apply Arrow.hom_ext
  · exact iso_gen _ _ _ _ hn _ _ _ _ (pb_app U π' n) (pb_app U π n) (disc.map ((pbRel _ a _ _ h).app n))
      ((disc.map_comp _ _).symm.trans ((congrArg (fun t => disc.map (NatTrans.app t n)) f1).trans (disc.map_comp _ _)))
      ((disc.map_comp _ _).symm.trans (congrArg (fun t => disc.map (NatTrans.app t n)) f2))
  · rfl

section
variable {J : Type} [SmallCategory J]

private theorem inj_aug {D : J ⥤ PSh} {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c) (n : SimplexCategoryᵒᵖ)
    (σ : Fin (n.unop.len + 1) ⥤ J) : inj D n σ ≫ (aug c hc).app n = c (σ.obj 0) := by
  have e : σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := σ.map_id _
  ext U x
  change (c (σ.obj 0)).app U ((D.map (σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))))).app U x) = _
  rw [e]
  simp

private theorem inj_nat {D' D : J ⥤ PSh} (α : D' ⟶ D) (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) :
    inj D' n σ ≫ ((hocF J).map α).app n = α.app (σ.obj 0) ≫ inj D n σ := by
  ext U x
  have e : (fun i => (α.app (σ.obj i)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)) =
      fun i => (D.map (σ.map (homOfLE (Fin.zero_le i)))).app U ((α.app (σ.obj 0)).app U x) :=
    funext fun i => ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality (σ.map (homOfLE (Fin.zero_le i)))) U) x
  have hk : ∀ i k (g : i ⟶ k), (D.flip.obj U).map (σ.map g) ((α.app (σ.obj i)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)) =
      (α.app (σ.obj k)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le k)))).app U x) := fun i k g => by
    have a := congrFun e i
    have b := congrFun e k
    dsimp only at a b
    rw [a, b]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) _
  exact mkChn_congr (F := D.flip.obj U) σ e hk
    (fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) _)

end

private theorem sum_transfer (q : ℕ) {P' P : Arrow Spc} (f : P' ⟶ P) {A : Type} (Q' Q : A → Arrow Spc)
    (r' : ∀ a, Q' a ⟶ P') (r : ∀ a, Q a ⟶ P) (t : ∀ a, Q' a ⟶ Q a) (w : ∀ a, r' a ≫ f = t a ≫ r a) (ht : ∀ a, Exc q (t a))
    (B : ∀ n i : ℤ, Function.Bijective fun (x : Hs q P n i) a => Hs.pull q (r a) n i x)
    (B' : ∀ n i : ℤ, Function.Bijective fun (x : Hs q P' n i) a => Hs.pull q (r' a) n i x) : Exc q f := by
  intro n i
  refine (Function.Bijective.of_comp_iff' (B' n i) _).1 ?_
  have T : Function.Bijective (Pi.map fun a => Hs.pull q (t a) n i) := Function.Bijective.piMap fun a => ht a n i
  convert T.comp (B n i) using 1
  funext x a
  change Hs.pull q (r' a) n i (Hs.pull q f n i x) = Hs.pull q (t a) n i (Hs.pull q (r a) n i x)
  rw [← hs_pull_comp, ← hs_pull_comp, w]

private theorem exc_lvl (hL : LeafLevel) (hS : LeafHsSum) (q : ℕ) {J : Type} [SmallCategory J] {D' D : J ⥤ PSh} (α : D' ⟶ D)
    {X : Scheme.{0}} (U : X.Opens) (c' : ∀ j, D'.obj j ⟶ yoneda.obj X) (c : ∀ j, D.obj j ⟶ yoneda.obj X)
    (hc' : Coc D' c') (hc : Coc D c) (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j))
    (ht : ∀ j, Exc q (abvRel U (disc.map (α.app j)) (disc.map (c' j)) (disc.map (c j)) (h j)))
    (n : SimplexCategoryᵒᵖ) (π' : (hoc D').obj n ⟶ yoneda.obj X) (π : (hoc D).obj n ⟶ yoneda.obj X)
    (e' : π' = (aug c' hc').app n) (e : π = (aug c hc).app n) (hn) :
    Exc q (abvRel U (E' := disc.obj ((hoc D').obj n)) (E := disc.obj ((hoc D).obj n)) (disc.map (((hocF J).map α).app n))
      (disc.map π') (disc.map π) hn) := by
  obtain ⟨cD⟩ := hL J D n
  obtain ⟨cD'⟩ := hL J D' n
  have hp : ∀ σ : Fin (n.unop.len + 1) ⥤ J, disc.map (inj D n σ) ≫ disc.map π = disc.map (c (σ.obj 0)) :=
    fun σ => (disc.map_comp _ _).symm.trans (congrArg disc.map (e ▸ inj_aug c hc n σ))
  have hp' : ∀ σ : Fin (n.unop.len + 1) ⥤ J, disc.map (inj D' n σ) ≫ disc.map π' = disc.map (c' (σ.obj 0)) :=
    fun σ => (disc.map_comp _ _).symm.trans (congrArg disc.map (e' ▸ inj_aug c' hc' n σ))
  refine sum_transfer q _ (fun σ : Fin (n.unop.len + 1) ⥤ J => abv U (E := disc.obj (D'.obj (σ.obj 0))) (disc.map (c' (σ.obj 0))))
    (fun σ => abv U (E := disc.obj (D.obj (σ.obj 0))) (disc.map (c (σ.obj 0))))
    (fun σ => abvRel U (disc.map (inj D' n σ)) _ _ (hp' σ)) (fun σ => abvRel U (disc.map (inj D n σ)) _ _ (hp σ))
    (fun σ => abvRel U (disc.map (α.app (σ.obj 0))) _ _ (h _)) (fun σ => ?_) (fun σ => ht _) ?_ ?_
  · exact abvRel_square U _ _ _ _ _ _ _ _ _ _ _ _
      ((disc.map_comp _ _).symm.trans ((congrArg disc.map (inj_nat α n σ)).trans (disc.map_comp _ _)))
  · exact fun m i => hS q X U _ (fun σ : Fin (n.unop.len + 1) ⥤ J => D.obj (σ.obj 0)) (Cofan.mk _ (inj D n)) ⟨cD⟩
      π (fun σ => c (σ.obj 0)) hp m i
  · exact fun m i => hS q X U _ (fun σ : Fin (n.unop.len + 1) ⥤ J => D'.obj (σ.obj 0)) (Cofan.mk _ (inj D' n)) ⟨cD'⟩
      π' (fun σ => c' (σ.obj 0)) hp' m i

theorem etale_excision_hocolim_of_local_properties :
    LateralTheory.CohomologicalPurity.TubeCut.LeafExcLevel → LateralTheory.CohomologicalPurity.TubeCut.LeafLevel → LateralTheory.CohomologicalPurity.TubeCut.LeafHsSum → LateralTheory.CohomologicalPurity.LeafAW → LateralTheory.CohomologicalPurity.LeafBd → LateralTheory.CohomologicalPurity.LeafExc → LateralTheory.CohomologicalPurity.LeafHens → LateralTheory.CohomologicalPurity.LeafIndExc → LateralTheory.CohomologicalPurity.TubeCut.LeafExcHoc := by
  intro hE hL hS _ _ _ _ _ a3 q J _ D' D α X U c' c hc' hc h h' ht
  refine hE a3 q _ _ _ fun n => ?_
  have hn : disc.map (((hocF J).map α).app n) ≫ disc.map ((aug c hc).app n) = disc.map ((aug c' hc').app n) :=
    (disc.map_comp _ _).symm.trans (congrArg (fun t => disc.map (t.app n)) h')
  have e := lev_abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h' n hn
  have k := exc_lvl hL hS q α U c' c hc' hc h ht n _ _ rfl rfl hn
  have e' : (lev n).map (abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h') =
      (levIso U (aug c' hc') n).hom ≫ abvRel U (E' := disc.obj ((hoc D').obj n)) (E := disc.obj ((hoc D).obj n))
        (disc.map (((hocF J).map α).app n)) (disc.map ((aug c' hc').app n)) (disc.map ((aug c hc).app n)) hn ≫
        (levIso U (aug c hc) n).inv := by
    rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e']
  exact exc_comp q (exc_iso q _) (exc_comp q k (exc_iso q (levIso U (aug c hc) n).symm))

end UpperTheory.Cb
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafQisLocalPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.QisLocalPf

variable (R : Type) [CommRing R]

abbrev Fsh := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))

instance wlb : Scheme.etaleTopology.{0}.WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

instance ph : (Fsh R).PreservesHomology := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

theorem chainsN_eq : chainsN R = TubeCut.chainsP R ⋙ (Fsh R).mapHomologicalComplex _ := by
  unfold chainsN TubeCut.chainsP
  rw [Functor.assoc, AlgebraicTopology.map_alternatingFaceMapComplex]
  rfl

theorem isIso_F_map {P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (g : P ⟶ Q)
    (hi : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} g)
    (hs : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} g) : IsIso ((Fsh R).map g) := by
  exact (GrothendieckTopology.W_iff _ g).1 ((GrothendieckTopology.W_iff_isLocallyBijective _ g).2 ⟨hi, hs⟩)

theorem sc_iso {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [IsIso (F.map (ShortComplex.homologyMap φ))] :
    IsIso (@ShortComplex.homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _) := by
  have e := ShortComplex.mapHomologyIso_hom_naturality φ F
  rw [(Iso.eq_comp_inv _).2 e]
  infer_instance

theorem quasiIso_chainsN {E E' : Spc} (f : E ⟶ E')
    (hi : ∀ n, Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((TubeCut.chainsP R).map f) n))
    (hs : ∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((TubeCut.chainsP R).map f) n)) :
    QuasiIso ((chainsN R).map f) := by
  have key : ∀ {K L : ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ} (φ : K ⟶ L),
      (∀ n, IsIso ((Fsh R).map (HomologicalComplex.homologyMap φ n))) →
      QuasiIso (((Fsh R).mapHomologicalComplex _).map φ) := by
    intro K L φ h
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
    have e := ShortComplex.mapHomologyIso_hom_naturality ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) (Fsh R)
    have : IsIso ((Fsh R).map (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map φ))) := h n
    exact sc_iso (Fsh R) ((HomologicalComplex.shortComplexFunctor _ _ n).map φ)
  have hf := key ((TubeCut.chainsP R).map f) (fun n => isIso_F_map R _ (hi n) (hs n))
  rw [chainsN_eq]
  exact hf

theorem LeafQisLocal_of : TubeCut.LeafQisLocal := by
  intro R _ E E' f hi hs
  have h := quasiIso_chainsN R f hi hs
  show QuasiIso (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat)
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).2 h

end LateralTheory.CohomologicalPurity.QisLocalPf
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafLocBasePf
set_option linter.unusedSimpArgs false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.LocBasePf

theorem isPullback_of_app {K C : Type*} [Category K] [Category C] [HasPullbacks C] {P X Y Z : K ⥤ C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : ∀ k, IsPullback (fst.app k) (snd.app k) (f.app k) (g.app k)) : IsPullback fst snd f g :=
  IsPullback.of_isLimit (c := PullbackCone.mk fst snd w)
    (evaluationJointlyReflectsLimits _ fun k =>
      (isLimitMapConePullbackConeEquiv ((evaluation K C).obj k) w).symm (h k).isLimit)

section
variable {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
  (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {Y : Scheme.{0}} (g : Y ⟶ X)

include hc in
theorem cw {j k : J} (f : j ⟶ k) : D.map f ≫ c k = c j :=
  yoneda.map_injective (by simpa using hc j k f)

def D' : J ⥤ Scheme.{0} where
  obj j := pullback (c j) g
  map {j k} f := pullback.map (c j) g (c k) g (D.map f) (𝟙 Y) (𝟙 X) (by simp [cw D c hc f]) (by simp)
  map_id j := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id]
    exact (congrArg (pullback.fst (c j) g ≫ ·) (D.map_id j)).trans (Category.comp_id _)
  map_comp f f' := by apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id]

def c' (j : J) : (D' D c hc g).obj j ⟶ Y := pullback.snd (c j) g

theorem hc' : Coc (D' D c hc g ⋙ yoneda) fun j => yoneda.map (c' D c hc g j) := by
  intro j k f
  rw [Functor.comp_map, ← yoneda.map_comp]
  congr 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

def α : D' D c hc g ⋙ yoneda ⟶ D ⋙ yoneda where
  app j := yoneda.map (pullback.fst (c j) g)
  naturality j k f := by
    have e : (D' D c hc g).map f ≫ pullback.fst (c k) g = pullback.fst (c j) g ≫ D.map f := pullback.lift_fst _ _ _
    exact (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map e).trans (yoneda.map_comp _ _))

theorem sq : (hocF J).map (α D c hc g) ≫ aug _ hc = aug _ (hc' D c hc g) ≫ sch.map g := by
  ext n U x
  have key : ∀ j (a : unop U ⟶ pullback (c j) g), (a ≫ pullback.fst (c j) g) ≫ c j = (a ≫ pullback.snd (c j) g) ≫ g :=
    fun j a => by rw [Category.assoc, Category.assoc, pullback.condition]
  exact key _ _

theorem snd_map {j k : J} (f : j ⟶ k) {V : Scheme.{0}} (a : V ⟶ (D' D c hc g).obj j) :
    (a ≫ (D' D c hc g).map f) ≫ c' D c hc g k = a ≫ c' D c hc g j := by
  rw [Category.assoc]
  congr 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem snd_chain {n : ℕ} {U : Scheme.{0}ᵒᵖ} (z : Fin (n + 1) ⥤ ((D' D c hc g ⋙ yoneda).flip.obj U).Elements)
    (i : Fin (n + 1)) : (z.obj i).2 ≫ c' D c hc g (z.obj i).1 = (z.obj 0).2 ≫ c' D c hc g (z.obj 0).1 := by
  have m := (z.map (homOfLE (Fin.zero_le i))).2
  rw [← m]
  exact snd_map D c hc g _ _

include hc in
theorem c_chain {n : ℕ} {U : Scheme.{0}ᵒᵖ} (z : Fin (n + 1) ⥤ ((D ⋙ yoneda).flip.obj U).Elements)
    (i : Fin (n + 1)) : (z.obj i).2 ≫ c (z.obj i).1 = (z.obj 0).2 ≫ c (z.obj 0).1 := by
  have m := (z.map (homOfLE (Fin.zero_le i))).2
  rw [← m]
  change ((z.obj 0).2 ≫ D.map _) ≫ _ = _
  rw [Category.assoc, cw D c hc]

theorem pt_ext {U : Scheme.{0}ᵒᵖ} (p q : Σ j, unop U ⟶ pullback (c j) g)
    (h1 : (⟨p.1, p.2 ≫ pullback.fst (c p.1) g⟩ : Σ j, unop U ⟶ D.obj j) = ⟨q.1, q.2 ≫ pullback.fst (c q.1) g⟩)
    (h2 : p.2 ≫ pullback.snd (c p.1) g = q.2 ≫ pullback.snd (c q.1) g) : p = q := by
  obtain ⟨j, a⟩ := p
  obtain ⟨k, b⟩ := q
  simp only [Sigma.mk.injEq] at h1
  obtain ⟨rfl, h⟩ := h1
  have h' := eq_of_heq h
  congr 1
  exact pullback.hom_ext h' h2

include hc in
theorem lift_map {j k : J} (f : j ⟶ k) {V : Scheme.{0}} (a : V ⟶ D.obj j) (b : V ⟶ D.obj k) (y : V ⟶ Y)
    (ha : a ≫ c j = y ≫ g) (hb : b ≫ c k = y ≫ g) (hab : a ≫ D.map f = b) :
    (pullback.lift a y ha : V ⟶ (D' D c hc g).obj j) ≫ (D' D c hc g).map f = pullback.lift b y hb := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id, D', hab]

theorem pb : IsPullback ((hocF J).map (α D c hc g)) (aug _ (hc' D c hc g)) (aug _ hc) (sch.map g) := by
  refine isPullback_of_app (sq D c hc g) fun n => isPullback_of_app ?_ fun U => ?_
  · exact NatTrans.congr_app (sq D c hc g) n
  have elem_ext {F : J ⥤ Type} (a b : F.Elements)
      (h : (⟨a.obj, a.val⟩ : Σ j, F.obj j) = ⟨b.obj, b.val⟩) : a = b := by
    cases a
    cases b
    cases h
    rfl
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · exact NatTrans.congr_app (NatTrans.congr_app (sq D c hc g) n) U
  · rintro x y ⟨h1, h2⟩
    change chn x = chn y
    refine CategoryTheory.Functor.ext ?_ (fun _ _ _ => Functor.Elements.hom_ext (Subsingleton.elim _ _))
    intro i
    have he : (⟨((chn x).obj i).obj, ((chn x).obj i).val⟩ : Σ j, unop U ⟶ pullback (c j) g) =
        ⟨((chn y).obj i).obj, ((chn y).obj i).val⟩ := by
      refine pt_ext D c g _ _ ?_ ?_
      · have hh := congrArg (fun z => (chn z).obj i) h1
        exact congrArg (fun z => (⟨z.obj, z.val⟩ : Σ j, unop U ⟶ D.obj j)) hh
      · exact (snd_chain D c hc g (chn x) i).trans (h2.trans (snd_chain D c hc g (chn y) i).symm)
    exact elem_ext _ _ he
  · intro x₂ x₃ h
    have e : ∀ i, ((chn x₂).obj i).2 ≫ c ((chn x₂).obj i).1 = x₃ ≫ g := fun i =>
      (c_chain D c hc (chn x₂) i).trans h
    refine ⟨mkChn (F := (D' D c hc g ⋙ yoneda).flip.obj U) (chn x₂ ⋙ CategoryOfElements.π _)
      (fun i => pullback.lift ((chn x₂).obj i).2 x₃ (e i)) (fun i k f => ?_), ?_, ?_⟩
    · exact lift_map D c hc g _ _ _ x₃ _ _ ((chn x₂).map f).2
    · change chn _ = chn x₂
      refine CategoryTheory.Functor.ext ?_ (fun _ _ _ => Functor.Elements.hom_ext (Subsingleton.elim _ _))
      intro i
      apply elem_ext
      refine Sigma.ext rfl (heq_of_eq ?_)
      change pullback.lift _ _ _ ≫ pullback.fst (c ((chn x₂).obj i).1) g = _
      exact pullback.lift_fst _ _ _
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = x₃
      exact pullback.lift_snd _ _ _

end

theorem hr {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
    (ho : ∀ j, IsOpenImmersion (c j)) (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {Y : Scheme.{0}} (g : Y ⟶ X)
    (j : J) (y : Y) : y ∈ Set.range (c' D c hc g j) ↔ g y ∈ Set.range (c j) := by
  have := ho j
  change y ∈ Set.range (pullback.snd (c j) g) ↔ _
  rw [IsOpenImmersion.range_pullbackSnd]
  rfl

end LateralTheory.CohomologicalPurity.TubeCut.LocBasePf

namespace LateralTheory.CohomologicalPurity.TubeCut
open LocBasePf

theorem LeafLocBase_of : EtaleLocBase := by
  intro J _ D X c ho hcov hdir hc Y g
  refine ⟨D' D c hc g, c' D c hc g, ?_, ?_, ?_, hc' D c hc g, ⟨?_⟩⟩
  · intro j
    have := ho j
    change IsOpenImmersion (pullback.snd (c j) g)
    infer_instance
  · intro y
    obtain ⟨j, hj⟩ := hcov (g y)
    exact ⟨j, (hr D c ho hc g j y).2 hj⟩
  · intro y j k h1 h2
    obtain ⟨l, hl1, hl2, hl⟩ := hdir (g y) j k ((hr D c ho hc g j y).1 h1) ((hr D c ho hc g k y).1 h2)
    exact ⟨l, hl1, hl2, (hr D c ho hc g l y).2 hl⟩
  · exact Arrow.isoMk (pb D c hc g).isoPullback.symm (Iso.refl _)
      ((IsPullback.isoPullback_inv_snd _).trans (Category.comp_id _).symm)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.Imports
namespace LateralTheory.CohomologicalPurity

theorem goal_of (hG : LeafGysin) (hS : LeafSemi) : Goal :=
  fun H => ⟨hG H, hS H.2.2.2.2.2.2.1 (hG H)⟩

end LateralTheory.CohomologicalPurity
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.FinLeafSemi
section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafSemiPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem LeafSemi_of : LeafSemi := by
  intro hA9 hG
  intro q _ X Z S p ι _ d e _ _ hq U hU N i
  obtain ⟨gys, rs, hgys⟩ := hG d
  let P : SP d := ⟨X, Z, S, p, ι, e, U, inferInstance, inferInstance, inferInstance, hU⟩
  have hqX : IsUnit (q : Γ(P.X, ⊤)) := by
    simpa using hq.map p.appTop.hom
  have hex := (hgys q P hqX).1
  have hsub : ∀ m j : ℤ, m < 0 → Subsingleton (Ht q (sch.obj Z) m j) :=
    fun m j hm => (hA9 (ZMod q) (tw q j)).1 _ m hm
  obtain ⟨j, rfl⟩ : ∃ j, i = j + d := ⟨i - d, by ring⟩
  constructor
  · intro hN
    refine ⟨?_, ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d := ⟨N - 2 * d, by ring⟩
      have hm : m < 0 := by omega
      have := hsub m j hm
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := ((hex m j).2.2 a).1 ha
      rw [Subsingleton.elim b 0, map_zero]
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d - 1 := ⟨N - 2 * d + 1, by ring⟩
      have hm : m < 0 := by omega
      have := hsub m j hm
      intro u
      exact ((hex m j).1 u).1 (Subsingleton.elim _ _)
  · intro hN
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d := ⟨N - 2 * d, by ring⟩
    have hm : m < 0 := by omega
    have := hsub m j hm
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨b, rfl⟩ := ((hex m j).2.2 a).1 ha
    rw [Subsingleton.elim b 0, map_zero]

end LateralTheory.CohomologicalPurity
end
end

namespace LateralTheory.Fin.LeafSemi
theorem etale_purity_semilocal_of_reduction : LateralTheory.CohomologicalPurity.LeafSemi := by
  apply LateralTheory.CohomologicalPurity.LeafSemi_of
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafSemi := etale_purity_semilocal_of_reduction
end LateralTheory.Fin.LeafSemi
end

theorem UpperTheory.Et.purAll : LateralTheory.CohomologicalPurity.LeafTube ∧ LateralTheory.CohomologicalPurity.LeafGysin ∧ LateralTheory.CohomologicalPurity.Goal := by
  have h_EPur_LeafAW : LateralTheory.CohomologicalPurity.LeafAW := LateralTheory.Fin.LeafAW.intersectionNumber_baseChange
  have h_EPur_LeafBd : LateralTheory.CohomologicalPurity.LeafBd := by apply LateralTheory.Fin.LeafBd.intersectionNumber_baseChange
  have h_EPur_LeafCl : LateralTheory.CohomologicalPurity.LeafCl := by apply LateralTheory.Fin.LeafCl.intersectionNumber_baseChange
  have h_EPur_LeafChart : LateralTheory.CohomologicalPurity.LeafChart := by apply LateralTheory.Fin.LeafChart.intersectionNumber_baseChange
  have h_EPur_LeafHens : LateralTheory.CohomologicalPurity.LeafHens := by apply LateralTheory.Fin.LeafHens.intersectionNumber_baseChange
  have h_EPur_LeafIndExc : LateralTheory.CohomologicalPurity.LeafIndExc := by apply LateralTheory.Fin.LeafIndExc.intersectionNumber_baseChange
  have h_EPur_LeafThom : LateralTheory.CohomologicalPurity.LeafThom := by apply LateralTheory.Fin.LeafThom.intersectionNumber_baseChange
  have h_EPur_LeafSemi : LateralTheory.CohomologicalPurity.LeafSemi := by apply LateralTheory.Fin.LeafSemi.intersectionNumber_baseChange
  have h_EPur_LeafExc : LateralTheory.CohomologicalPurity.LeafExc := by apply LateralTheory.Fin.LeafExc.intersectionNumber_baseChange
  have h_EPur_LeafPurNat : LateralTheory.CohomologicalPurity.EtalePurityNaturality := by apply LateralTheory.CohomologicalPurity.LeafPurNat_of
  have h_EPur_LeafPurProj : LateralTheory.CohomologicalPurity.EtalePurityProjection := by apply LateralTheory.CohomologicalPurity.LeafPurProj_of
  have h_EPur_LeafPurRed : LateralTheory.CohomologicalPurity.EtalePurityReduction := by apply LateralTheory.CohomologicalPurity.LeafPurRed_of
  have h_EPur_TubeCut_LeafChPush : LateralTheory.CohomologicalPurity.TubeCut.LeafChPush := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafChPush_of
  have h_EPur_TubeCut_LeafHKSplit : LateralTheory.CohomologicalPurity.TubeCut.LeafHKSplit := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHKSplit_of
  have h_relative : LateralTheory.CohomologicalPurity.TubeCut.LeafRel := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafRel_of <;> assumption
  have h_equivalence_of_excision : LateralTheory.CohomologicalPurity.TubeCut.LeafEqvOfExc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafEqvOfExc_of <;> assumption
  have h_EPur_TubeCut_LeafChiSq : LateralTheory.CohomologicalPurity.TubeCut.LeafChiSq := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafChiSq_of
  have h_excision_of_equivalence : LateralTheory.CohomologicalPurity.TubeCut.LeafExcOfEqv := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafExcOfEqv_of_sq <;> assumption
  have h_EPur_TubeCut_LeafMLev : LateralTheory.CohomologicalPurity.TubeCut.LeafMLev := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafMLev_of
  have h_excision_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafExcLevel := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafExcLevel_of <;> assumption
  have h_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafLevel := by apply LateralTheory.CohomologicalPurity.LeafLevelPf.LeafLevel_of
  have h_pullback_sum : LateralTheory.CohomologicalPurity.TubeCut.LeafPbSum := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPbSum_of
  have h_double_sum : LateralTheory.CohomologicalPurity.TubeCut.LeafDblSum := by apply LateralTheory.CohomologicalPurity.TubeCut.leafDblSum_of <;> assumption
  have h_EPur_TubeCut_LeafDiscSumH : LateralTheory.CohomologicalPurity.TubeCut.LeafDiscSumH := by apply LateralTheory.CohomologicalPurity.TubeCut.leafDiscSumH
  have h_chains_sum : LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafChainsSum := by apply LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafChainsSum_of
  have h_EPur_TubeCut_SumCut_LeafHKSum : LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafHKSum := by apply LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafHKSum_of
  have h_sum₂ : LateralTheory.CohomologicalPurity.TubeCut.LeafSum := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafSum_of <;> assumption
  have h_EPur_TubeCut_LeafHsSum : LateralTheory.CohomologicalPurity.TubeCut.LeafHsSum := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHsSum_of_dbl <;> assumption
  have h_excision_hocolim : LateralTheory.CohomologicalPurity.TubeCut.LeafExcHoc := by apply UpperTheory.Cb.etale_excision_hocolim_of_local_properties <;> assumption
  have h_EPur_TubeCut_LeafDiscPb : LateralTheory.CohomologicalPurity.TubeCut.LeafDiscPb := by apply LateralTheory.CohomologicalPurity.TubeCut.leafDiscPb
  have h_universal_sum : LateralTheory.CohomologicalPurity.TubeCut.LeafUnivSum := by apply LateralTheory.CohomologicalPurity.TubeCut.leafUnivSum
  have h_EPur_TubeCut_LeafFstHoc : LateralTheory.CohomologicalPurity.TubeCut.LeafFstHoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafFstHoc_of <;> assumption
  have h_augmentation_injective_at : LateralTheory.CohomologicalPurity.TubeCut.EtaleAugInjAt := by apply UpperTheory.Cb.hocolimAugmentation_injective_of_purity_inputs <;> assumption
  have h_augmentation_injective : LateralTheory.CohomologicalPurity.TubeCut.LeafAugInj := by apply LateralTheory.CohomologicalPurity.TubeCut.EtaleAugInj_of_augInjAt <;> assumption
  have h_augmentation_surjective : LateralTheory.CohomologicalPurity.TubeCut.LeafAugSurj := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafAugSurj_of
  have h_EPur_TubeCut_LeafHomLoc : LateralTheory.CohomologicalPurity.TubeCut.LeafHomLoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHomLoc_of
  have h_augmentation_local : LateralTheory.CohomologicalPurity.TubeCut.LeafAugLocal := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafAugLocal_of <;> assumption
  have h_EPur_TubeCut_LeafLocBase : LateralTheory.CohomologicalPurity.TubeCut.EtaleLocBase := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocBase_of
  have h_quasi_isomorphism_local : LateralTheory.CohomologicalPurity.TubeCut.LeafQisLocal := by apply LateralTheory.CohomologicalPurity.QisLocalPf.LeafQisLocal_of
  have h_EPur_TubeCut_LeafLoc : LateralTheory.CohomologicalPurity.TubeCut.LeafLoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocCutAll.goal_of <;> assumption
  have h_EPur_TubeCut_LeafLocExc : LateralTheory.CohomologicalPurity.TubeCut.LeafLocExc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocExc_of <;> assumption
  have h_EPur_TubeCut_LeafZ : LateralTheory.CohomologicalPurity.TubeCut.LeafZ := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafZ_of
  have h_EPur_TubeCut_LeafLocFst : LateralTheory.CohomologicalPurity.TubeCut.LeafLocFst := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocFst_of <;> assumption
  have h_EPur_TubeCut_LeafAbv : LateralTheory.CohomologicalPurity.TubeCut.LeafAbv := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafAbv_of
  have h_EPur_TubeCut_LeafLocHen : LateralTheory.CohomologicalPurity.TubeCut.LeafLocHen := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocHen_of <;> assumption
  have h_quotient : LateralTheory.CohomologicalPurity.TubeCut.LeafQuot := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafQuot_of
  have h_EPur_TubeCut_LeafLocIso : LateralTheory.CohomologicalPurity.TubeCut.LeafLocIso := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocIso_of <;> assumption
  have h_EPur_TubeCut_LeafActNat : LateralTheory.CohomologicalPurity.TubeCut.LeafActNat := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafActNat_of
  have h_excision_affine : LateralTheory.CohomologicalPurity.TubeCut.LeafExcAff := by apply LateralTheory.CohomologicalPurity.TubeCut.leafExcAff_pf
  have h_EPur_TubeCut_LeafHensH : LateralTheory.CohomologicalPurity.TubeCut.LeafHensH := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHensH_of
  have h_product_affine : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdAff := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPrdAff_of' <;> assumption
  have h_product_ring : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdRing := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPrdRing_of <;> assumption
  have h_EPur_TubeCut_LeafLocPrd : LateralTheory.CohomologicalPurity.TubeCut.LeafLocPrd := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocPrd_of <;> assumption
  have h_product_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdLevel := by apply UpperTheory.productLevelwise_of_alexanderWhitney <;> assumption
  have h_product_hocolim : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdHoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPrdHoc_of <;> assumption
  have h_EPur_TubeCut_LeafPush : LateralTheory.CohomologicalPurity.TubeCut.LeafPush := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPush_of
  have h_refinement : LateralTheory.CohomologicalPurity.TubeCut.LeafRefine := by apply LateralTheory.CohomologicalPurity.TubeCut.EtaleRefine_of_push <;> assumption
  have h_relative_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafRelLev := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafRelLev_of
  have h_relative_hocolim : LateralTheory.CohomologicalPurity.TubeCut.LeafRelHoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafRelHoc_of <;> assumption
  have h_EPur_LeafTube : LateralTheory.CohomologicalPurity.LeafTube := by apply LateralTheory.CohomologicalPurity.TubeCut.goal_of <;> assumption
  have h_EPur_LeafPur : LateralTheory.CohomologicalPurity.LeafPur := by apply LateralTheory.CohomologicalPurity.EtalePurity_of_parts <;> assumption
  have h_EPur_LeafGysin : LateralTheory.CohomologicalPurity.LeafGysin := by apply LateralTheory.CohomologicalPurity.LeafGysin_of <;> assumption
  have h_cohomological_purity : LateralTheory.CohomologicalPurity.Goal := by apply LateralTheory.CohomologicalPurity.goal_of <;> assumption
  exact ⟨h_EPur_LeafTube, h_EPur_LeafGysin, h_cohomological_purity⟩

theorem UpperTheory.Et.purGysin : LateralTheory.CohomologicalPurity.LeafGysin := UpperTheory.Et.purAll.2.1
