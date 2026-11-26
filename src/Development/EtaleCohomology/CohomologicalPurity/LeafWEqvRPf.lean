module

public import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyOnePf
public import Development.EtaleCohomology.CohomologicalPurity.LeafDictPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExcDegPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPfQuot

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafWEqvRPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem eqv_of_isIso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  refine ⟨fun x y h => ?_, fun y => ⟨pull R (inv f) F n y, ?_⟩⟩
  · have := congrArg (pull R (inv f) F n) h
    rwa [← pull_comp, ← pull_comp, IsIso.inv_hom_id, pull_id, pull_id] at this
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R}
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_of_section {R : Type} [CommRing R] {E E' : Spc} {f : E ⟶ E'} {r : E' ⟶ E} {F : Shv R}
    (h : f ≫ r = 𝟙 _) (hr : Eqv R r F) : Eqv R f F := by
  intro n
  have hc : (pull R f F n : _ → _) ∘ pull R r F n = id := by
    funext x; change pull R f F n (pull R r F n x) = x; rw [← pull_comp, h, pull_id]
  have : Function.Bijective ((pull R f F n : _ → _) ∘ pull R r F n) := by rw [hc]; exact Function.bijective_id
  exact (Function.Bijective.of_comp_iff _ (hr n)).1 this

def fW (d : ℕ) (R : Type) [CommRing R] :
    Spec (CommRingCat.of (LaurentPolynomial (MvPolynomial (Fin d) R))) ⟶ Spec (CommRingCat.of (MvPolynomial (Fin d) R)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : MvPolynomial (Fin d) R →+* _))

theorem smooth_C (A : Type) [CommRing A] : (LaurentPolynomial.C : A →+* LaurentPolynomial A).Smooth := by
  have h1 : (Polynomial.C : A →+* Polynomial A).Smooth := by
    rw [show (Polynomial.C : A →+* Polynomial A) = algebraMap A (Polynomial A) from rfl]
    exact RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  have h2 : (algebraMap (Polynomial A) (LaurentPolynomial A)).Smooth :=
    RingHom.Smooth.holdsForLocalizationAway (R := Polynomial A) (S := LaurentPolynomial A) Polynomial.X
  have h3 := RingHom.Smooth.comp h1 h2
  convert h3 using 1
  ext a
  simp

instance (d : ℕ) (R : Type) [CommRing R] : Smooth (fW d R) := by
  rw [fW, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact smooth_C _

instance (d : ℕ) (R : Type) [CommRing R] : Surjective (fW d R) := by
  let s : LaurentPolynomial (MvPolynomial (Fin d) R) →+* MvPolynomial (Fin d) R := LaurentPolynomial.eval₂ (RingHom.id _) 1
  have hs : s.comp LaurentPolynomial.C = RingHom.id _ := by ext x <;> simp [s]
  have : Spec.map (CommRingCat.ofHom s) ≫ fW d R = 𝟙 _ := by
    rw [fW, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]; exact Spec.map_id _
  have : Surjective (Spec.map (CommRingCat.ofHom s) ≫ fW d R) := by rw [this]; infer_instance
  exact Surjective.of_comp (Spec.map (CommRingCat.ofHom s)) (fW d R)

def LeafWCech : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ ψ : W d R ⟶ cech (fW d R), IsIso ψ ∧ wa d R ≫ ψ ≫ cechAug (fW d R) = 𝟙 _

theorem LeafWEqvR_of (hW : LeafWCech) : LeafWEqvR := by
  intro hH q _ d R _ _ i
  obtain ⟨ψ, hψ, he⟩ := hW d R
  have hA : Eqv _ (cechAug (fW d R)) (tw q i) := hH.2.1 (ZMod q) (fW d R) (tw q i)
  exact eqv_of_section (by rw [← he]) (eqv_comp (eqv_of_isIso ψ _) hA)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafUnivSumPf
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem ev_pb {P Q R : PSh} (f : P ⟶ R) (g : Q ⟶ R) (U : AlgebraicGeometry.Scheme.{0}ᵒᵖ) :
    IsPullback ((pullback.fst f g).app U) ((pullback.snd f g).app U) (f.app U) (g.app U) :=
  (IsPullback.of_hasPullback f g).map ((evaluation _ _).obj U)

theorem ev_cofan {A : Type} {X : A → PSh} (c : Cofan X) (hc : IsColimit c) (U : AlgebraicGeometry.Scheme.{0}ᵒᵖ) :
    Nonempty (IsColimit (Cofan.mk (c.pt.obj U) fun a => (c.inj a).app U)) :=
  ⟨(isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) X c.inj).1
    (isColimitOfPreserves ((evaluation _ _).obj U) hc)⟩

theorem leafUnivSum : LeafUnivSum := by
  intro A X c ⟨hc⟩ Y G f g
  let ι : ∀ a, pullback (c.inj a ≫ f) g ⟶ pullback f g := fun a =>
    pullback.map (c.inj a ≫ f) g f g (c.inj a) (𝟙 G) (𝟙 Y) (by simp) (by simp)
  have h1 : ∀ a, ι a ≫ pullback.fst f g = pullback.fst _ _ ≫ c.inj a := fun a => by simp only [ι, pullback.map, pullback.lift_fst]
  have h2 : ∀ a, ι a ≫ pullback.snd f g = pullback.snd _ _ := fun a => by simp only [ι, pullback.map, pullback.lift_snd, Category.comp_id]
  change Nonempty (IsColimit (Cofan.mk (pullback f g) ι))
  refine ⟨evaluationJointlyReflectsColimits _ fun U => ?_⟩
  refine (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) _ ι).2 ?_
  dsimp only [evaluation_obj_obj, evaluation_obj_map]
  have hcU := ev_cofan c hc U
  have f1 : ∀ a z, (pullback.fst f g).app U ((ι a).app U z) =
      (c.inj a).app U ((pullback.fst (c.inj a ≫ f) g).app U z) := fun a z =>
    show ((ι a ≫ pullback.fst f g).app U) z = ((pullback.fst _ _ ≫ c.inj a).app U) z by rw [h1 a]
  have f2 : ∀ a z, (pullback.snd f g).app U ((ι a).app U z) =
      (pullback.snd (c.inj a ≫ f) g).app U z := fun a z =>
    show ((ι a ≫ pullback.snd f g).app U) z = ((pullback.snd (c.inj a ≫ f) g).app U) z by rw [h2 a]
  refine Classical.choice ((Cofan.nonempty_isColimit_iff_bijective_fromSigma
    (Cofan.mk ((pullback f g).obj U) fun j => (ι j).app U)).2 ⟨?_, ?_⟩)
  · rintro ⟨a, z⟩ ⟨b, w⟩ e
    change (ι a).app U z = (ι b).app U w at e
    have e1 := congr_arg ((pullback.fst f g).app U) e
    rw [f1, f1] at e1
    obtain ⟨rfl, hw⟩ := (Cofan.inj_apply_eq_iff_of_isColimit hcU.some _ _).1 e1
    rw [cast_eq] at hw
    have e2 := congr_arg ((pullback.snd f g).app U) e
    rw [f2, f2] at e2
    rw [Types.ext_of_isPullback (ev_pb (c.inj a ≫ f) g U) hw.symm e2]
  · intro p
    obtain ⟨a, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit hcU.some ((pullback.fst f g).app U p)
    change (c.inj a).app U y = _ at hy
    obtain ⟨z, hz1, hz2⟩ := Types.exists_of_isPullback (ev_pb (c.inj a ≫ f) g U) y
      ((pullback.snd f g).app U p) (by
        have : ((pullback.fst f g ≫ f).app U) p = ((pullback.snd f g ≫ g).app U) p := by rw [pullback.condition]
        change f.app U ((c.inj a).app U y) = _
        rw [hy]; exact this)
    refine ⟨⟨a, z⟩, ?_⟩
    change (ι a).app U z = p
    refine Types.ext_of_isPullback (ev_pb f g U) ?_ ?_
    · rw [f1, hz1, hy]
    · rw [f2, hz2]

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPairPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.KummerTheory.FlasquePf

namespace LateralTheory.CohomologicalPurity.LeafPairPf

instance presFreeMod (R : Type) [CommRing R] :
    PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1, 0} R)) :=
  (ModuleCat.adj (ULift.{1, 0} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape

instance presL (R : Type) [CommRing R] :
    PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1, 0} R)) :=
  inferInstance

instance presFreeP (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  unfold freeP; infer_instance

instance presFree (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

theorem gen_eq {R : Type} [CommRing R] {G : Shv R} {X V : Scheme.{0}} (m : (free R).obj (yoneda.obj X) ⟶ G)
    (g : V ⟶ X) : (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V g) = Sec.res g (DictPf.ev m) := by
  have nat := congrArg (fun k => k.hom (freeGen R (yoneda.obj X) X (𝟙 X))) (m.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at nat
  change _ = (G.obj.map g.op).hom ((m.hom.app (op X)).hom (freeGen R (yoneda.obj X) X (𝟙 X)))
  rw [← nat]
  change _ = (m.hom.app (op V)).hom (Sec.res g (freeGen R (yoneda.obj X) X (𝟙 X)))
  rw [freeGen_res]
  congr 2

theorem ext_gen {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (m m' : (free R).obj (yoneda.obj X) ⟶ G)
    (h : DictPf.ev m = DictPf.ev m') : m = m' := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  ext V : 2
  apply ModuleCat.free_hom_ext
  intro x
  change (m.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down) = (m'.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down)
  rw [gen_eq m x.down, gen_eq m' x.down, h]

theorem ev_ofSec {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (s : Sec G X) : DictPf.ev (ofSec G s) = s :=
  ofSec_gen G s

theorem ev_pre {R : Type} [CommRing R] {G : Shv R} {Y X : Scheme.{0}} (f : Y ⟶ X)
    (m : (free R).obj (yoneda.obj X) ⟶ G) : DictPf.ev ((free R).map (yoneda.map f) ≫ m) = Sec.res f (DictPf.ev m) := by
  rw [← gen_eq]
  change (m.hom.app (op Y)).hom ((((free R).map (yoneda.map f)).hom.app (op Y)).hom (freeGen R (yoneda.obj Y) Y (𝟙 Y))) = _
  rw [freeGen_map]
  congr 2

theorem LeafPair_of : DictPf.LeafPair := by
  intro R _ G X U
  refine ⟨fun s s' hs => ?_, fun m m' h1 h2 => ?_⟩
  · have w : (free R).map (yoneda.map U.ι) ≫ ofSec G s = (free R).map (yoneda.map U.ι) ≫ ofSec G s' := by
      apply ext_gen
      rw [ev_pre, ev_pre, ev_ofSec, ev_ofSec]; exact hs
    refine ⟨(PreservesPushout.iso (free R) (yoneda.map U.ι) (yoneda.map U.ι)).inv ≫ pushout.desc _ _ w, ?_, ?_⟩
    · rw [← Category.assoc, PreservesPushout.inl_iso_inv, pushout.inl_desc, ev_ofSec]
    · rw [← Category.assoc, PreservesPushout.inr_iso_inv, pushout.inr_desc, ev_ofSec]
  · apply (cancel_epi (PreservesPushout.iso (free R) (yoneda.map U.ι) (yoneda.map U.ι)).hom).1
    apply pushout.hom_ext
    · rw [← Category.assoc, ← Category.assoc, PreservesPushout.inl_iso_hom]; exact h1
    · rw [← Category.assoc, ← Category.assoc, PreservesPushout.inr_iso_hom]; exact h2

end LateralTheory.CohomologicalPurity.LeafPairPf
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcAffPf
section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPfNbhd
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem indNbhd_of_nbhd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (h : Nbhd φ I) :
    IndNbhd φ I :=
  ⟨Discrete PUnit, inferInstance, inferInstance, (Functor.const _).obj (CommRingCat.of B),
    (Functor.const _).map (CommRingCat.ofHom φ), 𝟙 _, ⟨isColimitConstCocone (Discrete PUnit) (CommRingCat.of B)⟩,
    fun _ => ⟨h, Category.comp_id _⟩⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem off_map_le {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (J : Ideal A) :
    off B (J.map φ) ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ off A J := by
  intro x hx
  change x ∈ (PrimeSpectrum.zeroLocus _)ᶜ at hx
  change PrimeSpectrum.comap φ x ∈ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  intro h; apply hx
  rw [PrimeSpectrum.mem_zeroLocus] at h
  exact (Ideal.map_le_iff_le_comap.2 h : J.map φ ≤ _)

theorem opnMap_comp' {X'' X' X : Scheme.{0}} (k : X'' ⟶ X) (g : X'' ⟶ X') (f : X' ⟶ X) (hk : k = g ≫ f)
    (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens) (h1 : U'' ≤ g ⁻¹ᵁ U') (h2 : U' ≤ f ⁻¹ᵁ U)
    (h : U'' ≤ k ⁻¹ᵁ U) : opnMap k U'' U h = opnMap g U'' U' h1 ≫ opnMap f U' U h2 := by
  subst hk
  apply Arrow.hom_ext
  · change sch.map (Scheme.Hom.resLE (g ≫ f) U U'' h) =
      sch.map (Scheme.Hom.resLE g U' U'' h1) ≫ sch.map (Scheme.Hom.resLE f U U' h2)
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map (g ≫ f) = sch.map g ≫ sch.map f
    exact Functor.map_comp _ _ _

theorem leafExcAff_pf : LeafExcAff := by
  intro hyp hIE d q _ R B C _ _ _ ψ η hq hψ I K hη hK hI
  have hJI : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ = I := by
    rw [Ideal.map_span, ← Set.range_comp]; exact hI
  subst hJI; subst hK
  have hJfg : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hIfg := hJfg.map ψ
  have hqP : IsUnit (q : MvPolynomial (Fin d) R) := by
    simpa using hq.map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)
  have hqB : IsUnit (q : B) := by simpa using hqP.map ψ
  have e1 := hIE hyp.1 hyp.2.2.2.1 hyp.2.2.2.2.2.2.2.2.1 q ψ _ hJfg (indNbhd_of_nbhd ψ _ hψ) hqP (off_map_le ψ _)
  have e2 := hIE hyp.1 hyp.2.2.2.1 hyp.2.2.2.2.2.2.2.2.1 q η _ hIfg hη hqB (off_map_le η _)
  have hle : off C ((Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ |>.map η) ≤
      Spec.map (CommRingCat.ofHom (η.comp ψ)) ⁻¹ᵁ off _ (Ideal.span (Set.range MvPolynomial.X)) := by
    rw [Ideal.map_map]; exact off_map_le _ _
  refine ⟨hle, ?_⟩
  have hs : Spec.map (CommRingCat.ofHom (η.comp ψ)) =
      Spec.map (CommRingCat.ofHom η) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [← Spec.map_comp]; rfl
  rw [opnMap_comp' _ _ _ hs _ _ _ (off_map_le η _) (off_map_le ψ _)]
  exact exc_comp q e2 e1

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafChainsSumPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut.ChainsSumPf

universe v u
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

def zeroColim {D : Type*} [Category* D] {J : Type*} [Category* J] (G : D ⥤ C) (hG : ∀ X, IsZero (G.obj X))
    {K : J ⥤ D} (s : Cocone K) : IsColimit (G.mapCocone s) where
  desc _ := 0
  fac _ _ := (hG _).eq_of_src _ _
  uniq _ _ _ := (hG _).eq_of_src _ _

theorem presZero {D : Type*} [Category* D] {J : Type*} [Category* J] (G : D ⥤ C) (hG : ∀ X, IsZero (G.obj X)) :
    PreservesColimitsOfShape J G :=
  ⟨fun {_} => ⟨fun {s} _ => ⟨zeroColim G hG s⟩⟩⟩

theorem presExtend {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    (J : Type*) [Category* J] [HasColimitsOfShape J C] : PreservesColimitsOfShape J (e.extendFunctor C) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro i'
  cases h : e.r i' with
  | none => exact presZero _ fun K => K.isZero_extend_X' e i' h
  | some p =>
    have hp : e.f p = i' := e.f_eq_of_r_eq_some h
    let φ : HomologicalComplex.eval C c p ≅ e.extendFunctor C ⋙ HomologicalComplex.eval C c' i' :=
      NatIso.ofComponents (fun K => (K.extendXIso e hp).symm) (fun {K L} f => by
        simp [ComplexShape.Embedding.extendFunctor, HomologicalComplex.extendMap_f _ e hp])
    exact preservesColimitsOfShape_of_natIso φ

theorem presAFM {C : Type*} [Category* C] [Preadditive C] (J : Type*) [Category* J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (AlgebraicTopology.alternatingFaceMapComplex C) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  let φ : (evaluation _ C).obj (op (SimplexCategory.mk n)) ≅
      AlgebraicTopology.alternatingFaceMapComplex C ⋙ HomologicalComplex.eval C _ n :=
    NatIso.ofComponents (fun X => Iso.refl _) (fun {X Y} f => (Category.comp_id _).trans (Category.id_comp _).symm)
  exact preservesColimitsOfShape_of_natIso φ

variable (R : Type) [CommRing R]

theorem presFree (A : Type) : PreservesColimitsOfShape (Discrete A) (free R) := by
  have h1 : PreservesColimitsOfSize.{0, 0} (ModuleCat.free (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits
  have h2 : PreservesColimitsOfSize.{0, 0} (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))) :=
    (sheafificationAdjunction _ _).leftAdjoint_preservesColimits
  unfold free freeP
  infer_instance

instance hasCoprodShv (A : Type) : HasColimitsOfShape (Discrete A) (Shv R) := by
  have : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits (Shv R)
  have : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} _
  infer_instance

theorem presChains (A : Type) : PreservesColimitsOfShape (Discrete A) (chains R) := by
  have := presFree R A
  have : PreservesColimitsOfShape (Discrete A) ((SimplicialObject.whiskering PSh (Shv R)).obj (free R)) := by
    unfold SimplicialObject.whiskering; infer_instance
  have := presAFM (C := Shv R) (Discrete A)
  have := presExtend (C := Shv R) ComplexShape.embeddingDownNat (Discrete A)
  unfold chains chainsN
  infer_instance

end LateralTheory.CohomologicalPurity.TubeCut.SumCut.ChainsSumPf

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut

theorem LeafChainsSum_of : LeafChainsSum := by
  intro R _ A E c ⟨hc⟩
  have := ChainsSumPf.presChains R A
  exact ⟨isColimitCofanMkObjOfIsColimit (chains R) E c.inj hc⟩

end LateralTheory.CohomologicalPurity.TubeCut.SumCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPbSumPfR
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.PbSumPf

theorem types_univ {A : Type} {F : Discrete A ⥤ Type} (c : Cocone F) (hc : IsColimit c) :
    IsUniversalColimit c := by
  intro F' c' α f e _ H
  let i' : Discrete.functor (fun a => F'.obj ⟨a⟩) ≅ F' := Discrete.natIso (fun _ => Iso.refl _)
  let i : Discrete.functor (fun a => F.obj ⟨a⟩) ≅ F := Discrete.natIso (fun _ => Iso.refl _)
  let d : Cofan (fun a => F'.obj ⟨a⟩) := (Cocone.precompose i'.hom).obj c'
  let b : Cofan (fun a => F.obj ⟨a⟩) := (Cocone.precompose i.hom).obj c
  have hb : IsColimit b := (IsColimit.precomposeHomEquiv i c).symm hc
  have hd : ∀ a z, d.inj a z = c'.ι.app ⟨a⟩ z := fun _ _ => rfl
  have hbi : ∀ a z, b.inj a z = c.ι.app ⟨a⟩ z := fun _ _ => rfl
  have e1 : ∀ j x, c.ι.app j (α.app j x) = f (c'.ι.app j x) := fun j x => by
    have := ConcreteCategory.congr_hom (NatTrans.congr_app e j) x
    simpa using this
  refine ⟨(IsColimit.precomposeHomEquiv i' c') ((Cofan.nonempty_isColimit_iff_bijective_fromSigma d).2 ⟨?_, ?_⟩).some⟩
  · rintro ⟨a, z⟩ ⟨a', w⟩ h
    change d.inj a z = d.inj a' w at h
    rw [hd, hd] at h
    have h2 : b.inj a (α.app ⟨a⟩ z) = b.inj a' (α.app ⟨a'⟩ w) := by
      rw [hbi, hbi, e1, e1, h]
    obtain rfl := Cofan.eq_of_inj_apply_eq_of_isColimit hb _ _ h2
    have h3 := Cofan.inj_injective_of_isColimit hb a h2
    have := Types.ext_of_isPullback (H ⟨a⟩) h h3
    subst this
    rfl
  · intro y
    obtain ⟨a, x, hx⟩ := Cofan.inj_jointly_surjective_of_isColimit hb (f y)
    rw [hbi] at hx
    obtain ⟨z, hz1, _⟩ := Types.exists_of_isPullback (H ⟨a⟩) y x hx.symm
    exact ⟨⟨a, z⟩, hz1⟩

theorem univ_of_eval {J C D : Type*} [Category J] [Category C] [Category D] [HasPullbacks D]
    (F : J ⥤ C ⥤ D) (c : Cocone F)
    (hc : ∀ x : C, IsUniversalColimit (((evaluation C D).obj x).mapCocone c)) : IsUniversalColimit c := by
  intro F' c' α f e hα H
  exact ⟨evaluationJointlyReflectsColimits _ fun x =>
    (hc x (((evaluation C D).obj x).mapCocone c') (Functor.whiskerRight α _) (((evaluation C D).obj x).map f)
      (by ext y; dsimp; exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _) fun j => (H j).map ((evaluation C D).obj x)).some⟩

theorem spc_univ {A : Type} (F : Discrete A ⥤ Spc) (c : Cocone F) (hc : IsColimit c) : IsUniversalColimit c :=
  univ_of_eval (C := SimplexCategoryᵒᵖ) (D := PSh) F c fun n =>
    univ_of_eval (C := Scheme.{0}ᵒᵖ) (D := Type) _ _ fun Y =>
      types_univ _ (isColimitOfPreserves _ (isColimitOfPreserves ((evaluation _ _).obj n) hc))

theorem pb_of_eq {C : Type*} [Category C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f f' : X ⟶ Z} {g : Y ⟶ Z}
    (e : f = f') (hp : IsPullback fst snd f' g) : IsPullback fst snd f g := by subst e; exact hp

theorem pb_of_eq_snd {C : Type*} [Category C] {P X Y Z : C} {fst : P ⟶ X} {snd snd' : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (e : snd = snd') (hp : IsPullback fst snd' f g) : IsPullback fst snd f g := by subst e; exact hp

end LateralTheory.CohomologicalPurity.TubeCut.PbSumPf

namespace LateralTheory.CohomologicalPurity.TubeCut
open PbSumPf

theorem LeafPbSum_of : LeafPbSum := by
  intro X U A E c hc π π' h
  have hS := (leafDiscSumH A E c hc).some
  have Uv := spc_univ _ _ hS
  let g := sch.map U.ι
  refine Uv (Cofan.mk (abv U (E := disc.obj c.pt) (disc.map π)).left
      fun a => (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left)
    (Discrete.natTrans fun a => pullback.fst (disc.map (π' a.as)) g)
    (pullback.fst (disc.map π) g) ?_ (.of_discrete _) ?_
  · apply NatTrans.ext; funext ⟨a⟩
    exact (pullback.lift_fst (f := disc.map π) (g := g) _ _ _).symm
  · rintro ⟨a⟩
    have outer : IsPullback (pullback.fst (disc.map (π' a)) g)
        ((abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left ≫ pullback.snd (disc.map π) g)
        (disc.map (c.inj a) ≫ disc.map π) g := by
      have e2 : (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left ≫ pullback.snd (disc.map π) g
          = pullback.snd (disc.map (π' a)) g := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
      exact pb_of_eq_snd e2 (pb_of_eq (h a) (IsPullback.of_hasPullback _ _))
    have sq := IsPullback.of_bot outer (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback (disc.map π) g)
    exact sq.flip

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHKSumPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut.HKSumPf

variable {R : Type} [CommRing R] {A : Type} {K : A → Cx R} {c : Cofan K}

instance hasColShv : HasColimitsOfShape (Discrete A) (Shv R) := by
  have : IsGrothendieckAbelian.{1} (Shv R) := inferInstance
  have : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits (Shv R)
  have : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} _
  infer_instance

def hcp (hc : IsColimit c) (p : ℤ) : IsColimit ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) p).mapCocone c) :=
  haveI : PreservesColimitsOfShape (Discrete A) (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) p) := inferInstance
  isColimitOfPreserves _ hc

variable {L : Cx R} {n : ℤ}

def glue (hc : IsColimit c) (y : ∀ a, Cochain (K a) L n) : Cochain c.pt L n :=
  Cochain.mk fun p q hpq => (hcp hc p).desc
    ⟨L.X q, Discrete.natTrans fun j => (y j.as).v p q hpq⟩

theorem glue_v (hc : IsColimit c) (y : ∀ a, Cochain (K a) L n) (a : A) (p q : ℤ) (hpq : p + n = q) :
    (c.inj a).f p ≫ (glue hc y).v p q hpq = (y a).v p q hpq := by
  simp only [glue]
  exact (hcp hc p).fac _ ⟨a⟩

theorem comp_glue (hc : IsColimit c) (y : ∀ a, Cochain (K a) L n) (a : A) :
    (Cochain.ofHom (c.inj a)).comp (glue hc y) (zero_add n) = y a := by
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, glue_v]

theorem ext_cochain (hc : IsColimit c) {z₁ z₂ : Cochain c.pt L n}
    (h : ∀ a, (Cochain.ofHom (c.inj a)).comp z₁ (zero_add n) = (Cochain.ofHom (c.inj a)).comp z₂ (zero_add n)) :
    z₁ = z₂ := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  refine (hcp hc p).hom_ext fun ⟨a⟩ => ?_
  have := congrArg (fun z => z.v p q hpq) (h a)
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at this
  exact this

end LateralTheory.CohomologicalPurity.TubeCut.SumCut.HKSumPf

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut
open HKSumPf

theorem LeafHKSum_of : LeafHKSum := by
  intro R _ F A K c hc' n
  obtain ⟨hc⟩ := hc'
  have key : ∀ (a : A) (z : Cocycle c.pt (res R F) n),
      HK.pull R (c.inj a) F n (CohomologyClass.mk z) =
        CohomologyClass.mk (zcomp (Cocycle.ofHom (c.inj a)) z (zero_add n)) := fun _ _ => rfl
  constructor
  · let Φ : HK R c.pt F n →+ (∀ a, HK R (K a) F n) := AddMonoidHom.pi fun a => HK.pull R (c.inj a) F n
    change Function.Injective Φ
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := x.mk_surjective
    have h1 : ∀ a, ∃ β : Cochain (K a) (res R F) (n - 1),
        δ (n - 1) n β = (Cochain.ofHom (c.inj a)).comp z.1 (zero_add n) := by
      intro a
      have := congrFun hx a
      change HK.pull R (c.inj a) F n (CohomologyClass.mk z) = 0 at this
      rw [key, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at this
      exact this
    choose β hβ using h1
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨glue hc β, ext_cochain hc fun a => ?_⟩
    rw [← δ_ofHom_comp, comp_glue, hβ]
  · intro f
    have h1 : ∀ a, ∃ z : Cocycle (K a) (res R F) n, CohomologyClass.mk z = f a := fun a => (f a).mk_surjective
    choose z hz using h1
    have hcoc : δ n (n + 1) (glue hc fun a => (z a).1) = 0 := by
      refine ext_cochain hc fun a => ?_
      rw [← δ_ofHom_comp, comp_glue, Cochain.comp_zero]
      exact Cocycle.δ_eq_zero _ _
    refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hcoc), funext fun a => ?_⟩
    show HK.pull R (c.inj a) F n _ = _
    rw [key, ← hz a]
    congr 1
    exact Cocycle.ext (comp_glue hc _ a)

end LateralTheory.CohomologicalPurity.TubeCut.SumCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPurProjPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurProjPf

open PurPf

def HsCast {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) : Hs q P N' I' := by
  subst hN; subst hI; exact x

theorem HsCast_val {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) :
    (HsCast hN hI x).1 = Ht.cast hN hI x.1 := by
  subst hN; subst hI; rfl

theorem HsCast_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) {N N' I I' : ℤ} (hN : N = N') (hI : I = I')
    (x : Hs q P N I) : Hs.pull q φ N' I' (HsCast hN hI x) = HsCast hN hI (Hs.pull q φ N I x) := by
  subst hN; subst hI; rfl

theorem HsCast_fgt {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) :
    Hs.fgt q P N' I' (HsCast hN hI x) = Ht.cast hN hI (Hs.fgt q P N I x) := by
  subst hN; subst hI; rfl

theorem act_val (hA : DivisorNaturality) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : (Hs.act q a b).1 = cup q (pull _ (dbl.fold P) _ n a) b.1 := by
  have hb : pull _ (dbl.inr P) (tw q j) m b.1 = 0 := b.2
  change cup q (pull _ (dbl.fold P) _ n a) b.1 -
    pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1)) = _
  rw [(hA q).1, hb]
  simp only [map_zero, sub_zero]

theorem act_cup (hA : DivisorNaturality) (hR : DivisorRingCompatibility) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m k i j l : ℤ}
    (x : Ht q P.right n i) (y : Ht q P.right m j) (c : Hs q P k l) :
    Hs.act q (cup q x y) c = HsCast (by ring) (by ring) (Hs.act q x (Hs.act q y c)) := by
  apply Subtype.ext
  rw [HsCast_val, act_val hA, act_val hA, act_val hA, (hA q).1, (hR q _).2.1]

theorem fgt_act (hA : DivisorNaturality) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i)
    (s : Hs q P m j) : Hs.fgt q P _ _ (Hs.act q a s) = cup q a (Hs.fgt q P m j s) := by
  change pull _ (dbl.inl P) _ _ (Hs.act q a s).1 = cup q a (pull _ (dbl.inl P) _ _ s.1)
  rw [act_val hA, (hA q).1, ← pull_comp, show dbl.inl P ≫ dbl.fold P = 𝟙 _ from pushout.inl_desc (f := P.hom) (g := P.hom) _ _ _, pull_id]

theorem purT_char {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) : ∃ e : Ht q (T P).E n i,
      pull _ (pullback.fst (T P).π (sch.map P.ι)) _ _ e = pull _ (pullback.snd (T P).π (sch.map P.ι)) _ _ x ∧
      Hs.pull q (abvMap P.U (T P).π) _ _ (purT T q P n i x) =
        Hs.act q (P := abv P.U (T P).π) e (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P)) := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  refine ⟨(AddEquiv.ofBijective _ (((T P).ok q hq).1 i n)).symm
    (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n x), ?_, ?_⟩
  · exact AddEquiv.ofBijective_apply_symm_apply _ (((T P).ok q hq).1 i n)
  · unfold purT
    rw [dite_eq_left h]
    exact AddEquiv.ofBijective_apply_symm_apply _ (((T P).ok q hq).2.2.1 (n + 2 * d) (i + d))

end PurProjPf

open PurPf PurProjPf

theorem LeafPurProj_of : EtalePurityProjection := by
  intro hH d T q _ P hq n m i j a b
  have hA : DivisorNaturality := hH.2.2.2.2.1
  have hR : DivisorRingCompatibility := hH.2.2.2.2.2.1
  obtain ⟨eb, heb1, heb2⟩ := purT_char T q P hq m j b
  obtain ⟨ex, hex1, hex2⟩ := purT_char T q P hq (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)
  have hex : ex = cup q (pull (ZMod q) (T P).π (tw q i) n a) eb := by
    apply (((T P).ok q hq).1 (i + j) (n + m)).1
    set_option synthInstance.maxHeartbeats 200000 in
      rw [hex1, (hA q).1, (hA q).1, heb1, ← pull_comp, ← pull_comp, pullback.condition]
  have hN : n + (m + 2 * (d : ℤ)) = n + m + 2 * d := by ring
  have hI : i + (j + (d : ℤ)) = i + j + d := by ring
  have key : purT T q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b) =
      HsCast hN hI (Hs.act q (P := opn P.U) (n := n) (i := i) a (purT T q P m j b)) := by
    apply (((T P).ok q hq).2.2.1 (n + m + 2 * d) (i + j + d)).1
    rw [hex2, hex, HsCast_pull]
    refine (act_cup hA hR q (P := abv P.U (T P).π) (pull (ZMod q) (T P).π (tw q i) n a) eb
      (Hs.pull q (abvMap P.U (T P).π) (2 * d) d (fcl d q P))).trans ?_
    rw [TubeCut.LeafActNat_of hA q _ _ (abvMap P.U (T P).π) n (m + 2 * d) i (j + d) a (purT T q P m j b), heb2]
    rfl
  rw [key, HsCast_fgt]
  exact congrArg (Ht.cast hN hI) (fgt_act hA q (P := opn P.U) a (purT T q P m j b))

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHomLocPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.TubeCut
namespace HomLocPf

variable {R : Type} [CommRing R]

lemma exact_cyc (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) :
    ((ShortComplex.mk (K.iCycles n) (K.d n ((ComplexShape.down ℕ).next n)) (K.iCycles_d _ _)).map
      ((evaluation _ _).obj T)).Exact :=
  (ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel n _ rfl)).map _

lemma exact_bdy (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) :
    ((ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
      (K.toCycles_comp_homologyπ _ _)).map ((evaluation _ _).obj T)).Exact :=
  (ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel _ n (ChainComplex.prev ℕ n))).map _

lemma iCyc_inj (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) : Function.Injective ((K.iCycles n).app T).hom := by
  rw [← ModuleCat.mono_iff_injective]
  exact (inferInstance : Mono (((evaluation _ _).obj T).map (K.iCycles n)))

lemma π_surj (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) : Function.Surjective ((K.homologyπ n).app T).hom := by
  rw [← ModuleCat.epi_iff_surjective]
  exact (inferInstance : Epi (((evaluation _ _).obj T).map (K.homologyπ n)))

lemma lift_cyc (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) (hx : Cyc K n T x) :
    ∃ y, ((K.iCycles n).app T).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (exact_cyc K n T) x (hx _)

lemma cyc_i (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) : Cyc K n T (((K.iCycles n).app T).hom y) := by
  intro m
  change ((K.iCycles n ≫ K.d n m).app T).hom y = 0
  rw [K.iCycles_d]; rfl

lemma π_zero_iff (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((K.homologyπ n).app T).hom y = 0 ↔ Bdy K n T (((K.iCycles n).app T).hom y) := by
  have ti : ∀ z, ((K.iCycles n).app T).hom (((K.toCycles (n + 1) n).app T).hom z) = ((K.d (n + 1) n).app T).hom z := by
    intro z
    change ((K.toCycles (n + 1) n ≫ K.iCycles n).app T).hom z = _
    rw [K.toCycles_i]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (exact_bdy K n T) y h
    exact ⟨z, (ti z).symm.trans (congrArg _ hz)⟩
  · rintro ⟨z, hz⟩
    rw [← ti] at hz
    rw [← iCyc_inj K n T hz]
    change ((K.toCycles (n + 1) n ≫ K.homologyπ n).app T).hom z = 0
    rw [K.toCycles_comp_homologyπ]; rfl

lemma nat_i (K : PCx R) (n : ℕ) {T U : Scheme.{0}ᵒᵖ} (g : T ⟶ U) (y) :
    ((K.X n).map g).hom (((K.iCycles n).app T).hom y) = ((K.iCycles n).app U).hom (((K.cycles n).map g).hom y) := by
  change (((K.iCycles n).app T ≫ (K.X n).map g)).hom y = (((K.cycles n).map g ≫ (K.iCycles n).app U)).hom y
  rw [(K.iCycles n).naturality]

lemma nat_π (K : PCx R) (n : ℕ) {T U : Scheme.{0}ᵒᵖ} (g : T ⟶ U) (y) :
    ((K.homology n).map g).hom (((K.homologyπ n).app T).hom y) = ((K.homologyπ n).app U).hom (((K.cycles n).map g).hom y) := by
  change (((K.homologyπ n).app T ≫ (K.homology n).map g)).hom y = (((K.cycles n).map g ≫ (K.homologyπ n).app U)).hom y
  rw [(K.homologyπ n).naturality]

lemma cm_i {K L : PCx R} (φ : K ⟶ L) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((L.iCycles n).app T).hom (((HomologicalComplex.cyclesMap φ n).app T).hom y) =
      ((φ.f n).app T).hom (((K.iCycles n).app T).hom y) := by
  change ((HomologicalComplex.cyclesMap φ n ≫ L.iCycles n).app T).hom y = ((K.iCycles n ≫ φ.f n).app T).hom y
  rw [HomologicalComplex.cyclesMap_i]

lemma hm_π {K L : PCx R} (φ : K ⟶ L) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((HomologicalComplex.homologyMap φ n).app T).hom (((K.homologyπ n).app T).hom y) =
      ((L.homologyπ n).app T).hom (((HomologicalComplex.cyclesMap φ n).app T).hom y) := by
  change ((K.homologyπ n ≫ HomologicalComplex.homologyMap φ n).app T).hom y =
    ((HomologicalComplex.cyclesMap φ n ≫ L.homologyπ n).app T).hom y
  rw [HomologicalComplex.homologyπ_naturality]

end HomLocPf

open HomLocPf in
theorem LeafHomLoc_of : LeafHomLoc := by
  intro R _ K L φ n hinj hsurj
  refine ⟨⟨fun {X} a b h => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · change ((HomologicalComplex.homologyMap φ n).app X).hom a = ((HomologicalComplex.homologyMap φ n).app X).hom b at h
    obtain ⟨y, hy⟩ := π_surj K n X (a - b)
    have hb : Bdy L n X (((φ.f n).app X).hom (((K.iCycles n).app X).hom y)) := by
      rw [← cm_i, ← π_zero_iff, ← hm_π, hy, map_sub, h, sub_self]
    obtain ⟨S, hS, hSx⟩ := hinj X _ (cyc_i K n X y) hb
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V f hf
    rw [Presheaf.equalizerSieve_apply]
    change ((K.homology n).map f.op).hom a = ((K.homology n).map f.op).hom b
    rw [← sub_eq_zero, ← map_sub, ← hy, nat_π, π_zero_iff, ← nat_i]
    exact hSx f hf
  · obtain ⟨y, rfl⟩ := π_surj L n _ s
    obtain ⟨S, hS, hSx⟩ := hsurj (op U) _ (cyc_i L n _ y)
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V f hf
    obtain ⟨x', hx', hb⟩ := hSx f hf
    obtain ⟨y', rfl⟩ := lift_cyc K n _ x' hx'
    refine ⟨((K.homologyπ n).app (op V)).hom y', ?_⟩
    change ((HomologicalComplex.homologyMap φ n).app (op V)).hom (((K.homologyπ n).app (op V)).hom y') =
      ((L.homology n).map f.op).hom (((L.homologyπ n).app (op U)).hom y)
    rw [hm_π, nat_π, ← sub_eq_zero, ← map_sub, π_zero_iff, map_sub, cm_i, ← nat_i]
    exact hb

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHKSplitPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

section Gen
variable {C : Type*} [Category C] [Abelian C] {A B D Q I : CochainComplex C ℤ}

def hsCok (f : A ⟶ B) (l r : B ⟶ D) (hpo : IsPushout f f l r) (p : D ⟶ cokernel f)
    (hl : l ≫ p = cokernel.π f) (hr : r ≫ p = 0) : IsColimit (CokernelCofork.ofπ p hr) :=
  CokernelCofork.IsColimit.ofπ p hr
    (fun g' _ => cokernel.desc f (l ≫ g') (by rw [← Category.assoc, hpo.w, Category.assoc]; simp [*]))
    (fun g' eq' => by
      apply hpo.hom_ext
      · rw [← Category.assoc, hl, cokernel.π_desc]
      · rw [← Category.assoc, hr, zero_comp, eq'])
    (fun g' eq' m hm => by
      apply (cancel_epi (cokernel.π f)).1
      rw [cokernel.π_desc, ← hl, Category.assoc, hm])

def hsCokDeg {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) (k : ℤ) :
    IsColimit ((CokernelCofork.ofπ p hr).map (HomologicalComplex.eval C _ k)) :=
  CokernelCofork.mapIsColimit _ hc _

def hsCokDeg' {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) (k : ℤ) :
    IsColimit (CokernelCofork.ofπ (f := r.f k) (p.f k) (by rw [← HomologicalComplex.comp_f, hr]; rfl)) :=
  hsCokDeg hr hc k

theorem hsFac {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) {m : ℤ}
    (z : Cochain D I m) (hz : (Cochain.ofHom r).comp z (zero_add m) = 0) :
    ∃ y : Cochain Q I m, (Cochain.ofHom p).comp y (zero_add m) = z := by
  have key : ∀ a b (h : a + m = b), r.f a ≫ z.v a b h = 0 := fun a b h => by
    have := congrArg (fun w => w.v a b h) hz
    simpa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using this
  refine ⟨Cochain.mk (fun a b h => (CokernelCofork.IsColimit.desc' (hsCokDeg' hr hc a) (z.v a b h) (key a b h)).1), ?_⟩
  ext a b h
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  exact (CokernelCofork.IsColimit.desc' (hsCokDeg' hr hc a) (z.v a b h) (key a b h)).2

theorem hsCancel {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) {m : ℤ}
    (y₁ y₂ : Cochain Q I m) (h : (Cochain.ofHom p).comp y₁ (zero_add m) = (Cochain.ofHom p).comp y₂ (zero_add m)) :
    y₁ = y₂ := by
  ext a b hab
  have := congrArg (fun w => w.v a b hab) h
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at this
  have : Epi (p.f a) := epi_of_isColimit_cofork (hsCokDeg' hr hc a)
  exact (cancel_epi (p.f a)).1 ‹_›

theorem hsRS {r : B ⟶ D} {s : D ⟶ B} (hrs : r ≫ s = 𝟙 _) {m : ℤ} (z : Cochain B I m) :
    (Cochain.ofHom r).comp ((Cochain.ofHom s).comp z (zero_add m)) (zero_add m) = z := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hrs]
  ext a b h
  simp

theorem hsRP {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) {m : ℤ} (z : Cochain Q I m) :
    (Cochain.ofHom r).comp ((Cochain.ofHom p).comp z (zero_add m)) (zero_add m) = 0 := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hr, Cochain.ofHom_zero, Cochain.zero_comp]

theorem hsInj {r : B ⟶ D} {s : D ⟶ B} {p : D ⟶ Q} (hrs : r ≫ s = 𝟙 _) (hr : r ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hr)) (n : ℤ) :
    Function.Injective (cpre (Cocycle.ofHom p) I n n (zero_add n)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
  obtain ⟨β, hβ⟩ := hx
  change δ (n - 1) n β = (Cochain.ofHom p).comp x.1 (zero_add n) at hβ
  obtain ⟨γ, hγ⟩ := hsFac hr hc (β - (Cochain.ofHom s).comp ((Cochain.ofHom r).comp β (zero_add _)) (zero_add _))
    (by rw [Cochain.comp_sub, hsRS hrs, sub_self])
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨γ, hsCancel hr hc _ _ ?_⟩
  rw [← δ_ofHom_comp, hγ, δ_sub, δ_ofHom_comp, δ_ofHom_comp, hβ, hsRP hr, Cochain.comp_zero, sub_zero]

theorem hsExact {r : B ⟶ D} {s : D ⟶ B} {p : D ⟶ Q} (hrs : r ≫ s = 𝟙 _) (hr : r ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hr)) (n : ℤ) (x : CohomologyClass D I n)
    (hx : cpre (Cocycle.ofHom r) I n n (zero_add n) x = 0) :
    ∃ y, cpre (Cocycle.ofHom p) I n n (zero_add n) y = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
  obtain ⟨β, hβ⟩ := hx
  change δ (n - 1) n β = (Cochain.ofHom r).comp x.1 (zero_add n) at hβ
  obtain ⟨y, hy⟩ := hsFac hr hc (x.1 - δ (n - 1) n ((Cochain.ofHom s).comp β (zero_add _)))
    (by rw [Cochain.comp_sub, δ_ofHom_comp, hsRS hrs, hβ, sub_self])
  have hδ : δ n (n + 1) y = 0 := by
    apply hsCancel hr hc
    rw [← δ_ofHom_comp, hy, δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero, Cochain.comp_zero]
  refine ⟨CohomologyClass.mk (Cocycle.mk y (n + 1) rfl hδ), ?_⟩
  change CohomologyClass.mk _ = _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨-((Cochain.ofHom s).comp β (zero_add _)), ?_⟩
  change _ = (Cochain.ofHom p).comp y (zero_add n) - x.1
  rw [hy, δ_neg]; abel

end Gen

theorem LeafHKSplit_of : LeafHKSplit := by
  intro R _ F n A B D f l r s hpo hrs p hl hr
  have hc := hsCok f l r hpo p hl hr
  exact ⟨hsInj hrs hr hc n, fun x hx => hsExact hrs hr hc n x hx⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end
