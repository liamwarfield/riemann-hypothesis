module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafPurPf

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPBMapPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

abbrev evNU (n : ℕ) (U : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation _ _).obj (op (SimplexCategory.mk n)) ⋙ (evaluation _ _).obj (op U)

theorem pb_ext {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) {n : ℕ} {U : Scheme.{0}} (x y : Sx (pullback f g) n U)
    (h1 : ((pullback.fst f g).app _).app _ x = ((pullback.fst f g).app _).app _ y)
    (h2 : ((pullback.snd f g).app _).app _ x = ((pullback.snd f g).app _).app _ y) : x = y := by
  let G := evNU n U
  let I := PreservesPullback.iso G f g ≪≫ Types.pullbackIsoPullback (G.map f) (G.map g)
  have hi : Function.Injective I.hom := (isIso_iff_bijective I.hom).1 inferInstance |>.1
  apply hi
  apply Subtype.ext
  have a1 := (ConcreteCategory.congr_hom (PreservesPullback.iso_hom_fst G f g))
  have a2 := (ConcreteCategory.congr_hom (PreservesPullback.iso_hom_snd G f g))
  refine Prod.ext ?_ ?_
  · simp only [I, Iso.trans_hom]
    rw [types_comp_apply, types_comp_apply, Types.pullbackIsoPullback_hom_fst, Types.pullbackIsoPullback_hom_fst]
    exact (a1 x).trans (h1.trans (a1 y).symm)
  · simp only [I, Iso.trans_hom]
    rw [types_comp_apply, types_comp_apply, Types.pullbackIsoPullback_hom_snd, Types.pullbackIsoPullback_hom_snd]
    exact (a2 x).trans (h2.trans (a2 y).symm)

theorem pb_mk {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) {n : ℕ} {U : Scheme.{0}} (a : Sx X n U) (b : Sx Y n U)
    (h : (f.app _).app _ a = (g.app _).app _ b) : ∃ x : Sx (pullback f g) n U,
    ((pullback.fst f g).app _).app _ x = a ∧ ((pullback.snd f g).app _).app _ x = b := by
  let G := evNU n U
  let z : Types.PullbackObj (G.map f) (G.map g) := ⟨(a, b), h⟩
  refine ⟨(PreservesPullback.iso G f g).inv ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z), ?_, ?_⟩
  · have := (ConcreteCategory.congr_hom (PreservesPullback.iso_inv_fst G f g))
      ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z)
    refine this.trans ?_
    exact (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_fst (G.map f) (G.map g))) z
  · have := (ConcreteCategory.congr_hom (PreservesPullback.iso_inv_snd G f g))
      ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z)
    refine this.trans ?_
    exact (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_snd (G.map f) (G.map g))) z

theorem pr_ext {X Y : Spc} {n : ℕ} {U : Scheme.{0}} (x y : Sx (X ⨯ Y) n U)
    (h1 : ((prod.fst : X ⨯ Y ⟶ X).app _).app _ x = ((prod.fst : X ⨯ Y ⟶ X).app _).app _ y)
    (h2 : ((prod.snd : X ⨯ Y ⟶ Y).app _).app _ x = ((prod.snd : X ⨯ Y ⟶ Y).app _).app _ y) : x = y := by
  let G := evNU n U
  let I := PreservesLimitPair.iso G X Y ≪≫ Types.binaryProductIso (G.obj X) (G.obj Y)
  have hi : Function.Injective I.hom := (isIso_iff_bijective I.hom).1 inferInstance |>.1
  apply hi
  have a1 := (ConcreteCategory.congr_hom (prodComparison_fst G X Y))
  have a2 := (ConcreteCategory.congr_hom (prodComparison_snd G X Y))
  have b1 := (ConcreteCategory.congr_hom (Types.binaryProductIso_hom_comp_fst (G.obj X) (G.obj Y)))
  have b2 := (ConcreteCategory.congr_hom (Types.binaryProductIso_hom_comp_snd (G.obj X) (G.obj Y)))
  refine Prod.ext ?_ ?_
  · simp only [I, Iso.trans_hom, types_comp_apply, PreservesLimitPair.iso_hom]
    exact (b1 _).trans ((a1 x).trans (h1.trans ((a1 y).symm.trans (b1 _).symm)))
  · simp only [I, Iso.trans_hom, types_comp_apply, PreservesLimitPair.iso_hom]
    exact (b2 _).trans ((a2 x).trans (h2.trans ((a2 y).symm.trans (b2 _).symm)))

theorem um_basic {U : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(U, ⊤)) (hv : Ideal.span (Set.range v) = ⊤) (p : U) :
    ∃ i : Fin N, 0 ≤ i.val ∧ p ∈ U.basicOpen (v i) := by
  have h := iSup_basicOpen_of_span_eq_top (X := U) ⊤ (Set.range v) hv
  have hp : p ∈ (⊤ : U.Opens) := trivial
  rw [← h] at hp
  obtain ⟨_, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  obtain ⟨⟨i, rfl⟩, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  exact ⟨i, Nat.zero_le _, hi⟩

theorem basic_um {A : Type} [CommRing A] {N : ℕ} (v : Fin N → Γ(Spec (CommRingCat.of A), ⊤))
    (hv : ∀ p, ∃ i : Fin N, 0 ≤ i.val ∧ p ∈ (Spec (CommRingCat.of A)).basicOpen (v i)) :
    Ideal.span (Set.range v) = ⊤ := by
  rw [← (isAffineOpen_top (Spec (CommRingCat.of A))).iSup_basicOpen_eq_self_iff]
  apply le_antisymm le_top
  intro p _
  obtain ⟨i, -, hi⟩ := hv p
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨v i, i, rfl⟩, hi⟩

def cstV (N : ℕ) (E : Spc) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (Functor.const (Fin (n.unop.len + 1))).obj (SingleObj.star (GL (Fin N) Γ(U.unop, ⊤)))
      naturality := fun U U' g => by
        ext x
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq ?_)
        exact (map_one (Matrix.GeneralLinearGroup.map _)).symm }
  naturality n m f := rfl

def conv {N n : ℕ} {U : Scheme.{0}} (c : ComposableArrows (Um N Γ(U, ⊤)) n)
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1) : ComposableArrows (Vec N 0 U) n where
  obj i := ⟨(c.obj i).1, um_basic _ (c.obj i).2⟩
  map {i j} h := ⟨(c.map h).1.2, fun k => by
    have := congrFun (c.map h).2 k
    rw [hc h] at this
    simpa using this⟩
  map_id i := Subtype.ext (congrArg (fun p => (Subtype.val p).2) (c.map_id i))
  map_comp f g := Subtype.ext (congrArg (fun p => (Subtype.val p).2) (c.map_comp f g))

theorem conv_congr {N n : ℕ} {U : Scheme.{0}} {c c' : ComposableArrows (Um N Γ(U, ⊤)) n} (e : c = c')
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1)
    (hc' : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c'.map h).1.1 = 1) : conv c hc = conv c' hc' := by
  subst e; rfl

theorem pb_gl {N : ℕ} {E : Spc} {n : SimplexCategoryᵒᵖ} {U : Scheme.{0}ᵒᵖ}
    (x : ((pullback (cstV N E) (PGL.pr N)).obj n).obj U) {i j : Fin (n.unop.len + 1)} (h : i ⟶ j) :
    ((((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x : ComposableArrows (Um N Γ(U.unop, ⊤)) n.unop.len).map h).1.1
      = 1 := by
  have e0 := ConcreteCategory.congr_hom
    (congrArg (fun φ : pullback (cstV N E) (PGL.pr N) ⟶ ofCat (glCat N) => (φ.app n).app U) (pullback.condition (f := cstV N E) (g := PGL.pr N))) x
  have e : ((Functor.const (Fin (n.unop.len + 1))).obj (SingleObj.star (GL (Fin N) Γ(U.unop, ⊤))) :
      ComposableArrows (SingleObj (GL (Fin N) Γ(U.unop, ⊤))) n.unop.len) =
      (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x : ComposableArrows (Um N Γ(U.unop, ⊤)) n.unop.len) ⋙
        Um.toGL N Γ(U.unop, ⊤) := e0
  have := Functor.congr_hom e.symm h
  exact this.trans ((Category.id_comp _).trans (Category.comp_id _))

def fMap (N : ℕ) (E : Spc) : pullback (cstV N E) (PGL.pr N) ⟶ Pj N 0 where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        (conv (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) (pb_gl x) : ComposableArrows (Vec N 0 U.unop) n.unop.len)
      naturality := fun U U' g => by
        ext x
        have e1 : (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U' (((pullback (cstV N E) (PGL.pr N)).obj n).map g x) :
            ComposableArrows (Um N Γ(U'.unop, ⊤)) n.unop.len) =
            ((PGL N).obj n).map g (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) :=
          ConcreteCategory.congr_hom (((pullback.snd (cstV N E) (PGL.pr N)).app n).naturality g) x
        refine (conv_congr e1 (pb_gl _) (by intro i j h; rw [← e1]; exact pb_gl _ h)).trans ?_
        exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl)) }
  naturality n m f := by
    ext U x
    have e1 : (((pullback.snd (cstV N E) (PGL.pr N)).app m).app U (((pullback (cstV N E) (PGL.pr N)).map f).app U x) :
        ComposableArrows (Um N Γ(U.unop, ⊤)) m.unop.len) =
        ((PGL N).map f).app U (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) :=
      ConcreteCategory.congr_hom (congrArg (fun φ : (pullback (cstV N E) (PGL.pr N)).obj n ⟶ (PGL N).obj m => φ.app U) ((pullback.snd (cstV N E) (PGL.pr N)).naturality f)) x
    refine (conv_congr e1 (pb_gl _) (by intro i j h; rw [← e1]; exact pb_gl _ h)).trans ?_
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl))

def back {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n where
  obj i := ⟨(w.obj i).1, basic_um _ (w.obj i).2⟩
  map h := ⟨(1, (w.map h).1), by funext k; simpa using (w.map h).2 k⟩
  map_id i := Subtype.ext (Prod.ext rfl (congrArg Subtype.val (w.map_id i)))
  map_comp f g := Subtype.ext (Prod.ext (one_mul 1).symm (congrArg Subtype.val (w.map_comp f g)))

theorem back_conv {A : Type} [CommRing A] {N n : ℕ} (c : ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n)
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1) : back (conv c hc) = c :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ h => heq_of_eq (Subtype.ext (Prod.ext (hc h).symm rfl)))

theorem conv_back {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    conv (back w) (fun _ => rfl) = w :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl))

theorem back_gl {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    ((Functor.const (Fin (n + 1))).obj (SingleObj.star (GL (Fin N) Γ(Spec (CommRingCat.of A), ⊤))) :
      ComposableArrows (SingleObj (GL (Fin N) Γ(Spec (CommRingCat.of A), ⊤))) n) = back w ⋙ Um.toGL N _ :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem conv_inj {A : Type} [CommRing A] {N n : ℕ} {c c' : ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n}
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1)
    (hc' : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c'.map h).1.1 = 1) (e : conv c hc = conv c' hc') : c = c' :=
  (back_conv c hc).symm.trans ((congrArg back e).trans (back_conv c' hc'))

theorem fMap_line (N : ℕ) (E : Spc) : fMap N E ≫ Pj.line N 0 = pullback.snd (cstV N E) (PGL.pr N) ≫ PGL.line N := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem eMap_bij (N : ℕ) (R : Type) [CommRing R] (n : ℕ) (A : Type) [CommRing A] : Function.Bijective
      (fun x : Sx (pullback (cstV N (sp R)) (PGL.pr N)) n (Spec (CommRingCat.of A)) =>
        ((prod.lift (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)) : _ ⟶ PR N 0 R).app
          (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x) := by
  have k1 := fun z => ConcreteCategory.congr_hom (congrArg (fun φ : pullback (cstV N (sp R)) (PGL.pr N) ⟶ Pj N 0 =>
        (φ.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A)))) (prod.lift_fst (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)))) z
  have k2 := fun z => ConcreteCategory.congr_hom (congrArg (fun φ : pullback (cstV N (sp R)) (PGL.pr N) ⟶ sp R =>
        (φ.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A)))) (prod.lift_snd (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)))) z
  constructor
  · intro x y hxy
    apply pb_ext
    · exact (k2 x).symm.trans ((congrArg _ hxy).trans (k2 y))
    · exact conv_inj (pb_gl x) (pb_gl y) ((k1 x).symm.trans ((congrArg _ hxy).trans (k1 y)))
  · intro z
    obtain ⟨x, hx1, hx2⟩ := pb_mk (cstV N (sp R)) (PGL.pr N) (n := n) (U := Spec (CommRingCat.of A))
      (((prod.snd : PR N 0 R ⟶ _).app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) z)
      (back (((prod.fst : PR N 0 R ⟶ _).app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) z))
      (back_gl _)
    refine ⟨x, pr_ext _ _ ?_ ?_⟩
    · exact (k1 x).trans ((conv_congr hx2 (pb_gl x) (fun _ => rfl)).trans (conv_back _))
    · exact (k2 x).trans hx1

theorem LeafPBMap_of : LeafPBMap := by
  set_option synthInstance.maxHeartbeats 100000 in
    exact fun N R _ =>
      ⟨cstV N (sp R), prod.lift (fMap N (sp R)) (pullback.fst _ _), prod.lift_snd _ _,
        by rw [prod.lift_fst_assoc]; exact fMap_line N (sp R), fun n A _ => eMap_bij N R n A⟩

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafLocIsoPf
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

noncomputable section
namespace LateralTheory.CohomologicalPurity.TubeCut

instance sch_preservesPullbacks : PreservesLimitsOfShape WalkingCospan sch :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (yoneda ⋙ SimplicialObject.const PSh))

theorem pbRel_isIso_of {B G E' E Q₁ Q₀ : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π')
    {f₁ : Q₁ ⟶ E'} {z₁ : Q₁ ⟶ G} {f₀ : Q₀ ⟶ E} {z₀ : Q₀ ⟶ G} (h₁ : IsPullback f₁ z₁ π' g) (h₀ : IsPullback f₀ z₀ π g)
    (k : Q₁ ⟶ Q₀) [IsIso k] (kf : k ≫ f₀ = f₁ ≫ a) (kz : k ≫ z₀ = z₁) : IsIso (pbRel g a π' π h) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have e : h₁.isoPullback.hom ≫ pbRel g a π' π h = k ≫ h₀.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pbRel, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, kf]
    · simp only [pbRel, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd, kz, Category.comp_id]
  have e' : pbRel g a π' π h = h₁.isoPullback.inv ≫ k ≫ h₀.isoPullback.hom := by
    rw [← e, Iso.inv_hom_id_assoc]
  rw [e']; infer_instance

theorem isIso_specMap_of_bij {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hb : Function.Bijective f) :
    IsIso (Spec.map (CommRingCat.ofHom f)) := by
  have : IsIso (CommRingCat.ofHom f) := (RingEquiv.ofBijective f hb).toCommRingCatIso.isIso_hom
  infer_instance

theorem quot_bij_of_eq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I J : Ideal A) (e : J = I) (K : Ideal B)
    (hK : K = I.map φ) (h : J ≤ K.comap φ) (hb : Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap K φ h) := by
  subst e; subst hK; exact hb

theorem LeafLocIso_of (hZ : LeafZ) (hQ : LeafQuot) : LeafLocIso := by
  intro H d P V h
  have := P.cl
  set A := Γ(P.X, V.1)
  set I := P.ι.ker.ideal V
  set φ : A →+* H.obj A I := eta H P V
  obtain ⟨⟨z₁, h₁⟩, -⟩ := hZ P.X P.Z P.ι V (H.obj A I) φ
  obtain ⟨⟨z₀, h₀'⟩, -⟩ := hZ P.X P.Z P.ι V A (RingHom.id A)
  have e₀ : Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ V.2.fromSpec = V.2.fromSpec := by simp
  rw [e₀] at h₀'
  have hle : I.map (RingHom.id A) ≤ (I.map φ).comap φ := by rw [Ideal.map_id]; exact Ideal.le_comap_map
  set qm := Ideal.quotientMap (I.map φ) φ hle
  have hb : Function.Bijective qm := quot_bij_of_eq φ I _ (Ideal.map_id I) _ rfl hle (hQ A (H.obj A I) φ I (H.ind A I))
  have hcomp : qm.comp (Ideal.Quotient.mk (I.map (RingHom.id A))) = (Ideal.Quotient.mk (I.map φ)).comp φ :=
    Ideal.quotientMap_comp_mk hle
  have kf : Spec.map (CommRingCat.ofHom qm) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (RingHom.id A)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]
  have kz : Spec.map (CommRingCat.ofHom qm) ≫ z₀ = z₁ := by
    rw [← cancel_mono P.ι, Category.assoc, ← h₀'.w, ← h₁.w, ← Category.assoc, kf, Category.assoc]
  have := isIso_specMap_of_bij qm hb
  exact pbRel_isIso_of _ _ _ _ h (h₁.map sch) (h₀'.map sch) (sch.map (Spec.map (CommRingCat.ofHom qm)))
    (by rw [← sch.map_comp, kf, sch.map_comp]) (by rw [← sch.map_comp, kz])

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafLevelPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.LeafLevelPf
open LateralTheory.CohomologicalPurity.TubeCut

variable {J : Type} [SmallCategory J]

theorem elt_eqToHom {F : J ⥤ Type} {a b : F.Elements} (h : a = b) :
    (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by subst h; rfl

theorem chn_eq (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) (x : ((hoc D).obj n).obj U) :
    (inj D n (chn x ⋙ Functor.Elements.π _)).app U (chn x |>.obj 0).val = x := by
  change mkChn (F := D.flip.obj U) _ _ _ = chn x
  fapply CategoryTheory.Functor.ext
  · intro i
    let f := (chn x).map (homOfLE (Fin.zero_le i))
    refine Functor.Elements.ext _ _ (by rfl) ?_
    change (D.flip.obj U).map (𝟙 ((chn x).obj i).obj)
      ((D.flip.obj U).map f.hom ((chn x).obj 0).val) = ((chn x).obj i).val
    rw [(D.flip.obj U).map_id]
    exact f.map_val
  · intro i k g
    apply Functor.Elements.hom_ext
    rw [Functor.Elements.comp_hom, Functor.Elements.comp_hom]
    erw [elt_eqToHom, elt_eqToHom]
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

theorem bij (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) :
    Function.Bijective (Cofan.mk (((hoc D).obj n).obj U) (fun σ => ((evaluation _ _).obj U).map (inj D n σ)) :
      Cofan fun σ : Fin (n.unop.len + 1) ⥤ J => ((evaluation _ _).obj U).obj (D.obj (σ.obj 0))).cofanTypes.fromSigma := by
  constructor
  · rintro ⟨σ, a⟩ ⟨σ', a'⟩ h
    change (inj D n σ).app U a = (inj D n σ').app U a' at h
    have e : σ = σ' := congrArg (fun F => F ⋙ Functor.Elements.π (D.flip.obj U)) h
    subst e
    have h2 := congrArg (fun F : Fin (n.unop.len + 1) ⥤ (D.flip.obj U).Elements => F.obj 0) h
    have h3 : (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a =
        (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a' := by
      change (D.flip.obj U).elementsMk (σ.obj 0) _ = (D.flip.obj U).elementsMk (σ.obj 0) _ at h2
      injection h2
    have hid : ∀ b : ((evaluation _ _).obj U).obj (D.obj (σ.obj 0)), (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U b = b := by
      intro b
      have : (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := rfl
      rw [this, σ.map_id, D.map_id]; rfl
    rw [hid, hid] at h3
    subst h3; rfl
  · intro x
    exact ⟨⟨chn x ⋙ Functor.Elements.π _, (chn x |>.obj 0).val⟩, chn_eq D n U x⟩

theorem LeafLevel_of : LeafLevel := by
  intro J _ D n
  refine ⟨evaluationJointlyReflectsColimits _ fun U => ?_⟩
  refine (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) _ _).symm ?_
  exact Classical.choice ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).2 (bij D n U))

end LateralTheory.CohomologicalPurity.LeafLevelPf
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafQuotPf
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem LeafQuot_of : LeafQuot := by
  intro A B _ _ φ I h
  obtain ⟨J, _, _, D, s, t, ⟨hc⟩, hj⟩ := h
  have hst : ∀ j (a : A), (t.app j).hom ((s.app j).hom a) = φ a := fun j a =>
    congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom a) (hj j).2
  have sn : ∀ {j k : J} (f : j ⟶ k), (D.map f).hom.comp (s.app j).hom = (s.app k).hom := by
    intro j k f
    have := s.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    rw [this]; rfl
  have tn : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), (t.app k).hom ((D.map f).hom y) = (t.app j).hom y := by
    intro j k f y
    have := t.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    exact congrArg (fun g : D.obj j ⟶ CommRingCat.of B => g.hom y) this
  have mv : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), y ∈ I.map (s.app j).hom →
      (D.map f).hom y ∈ I.map (s.app k).hom := by
    intro j k f y hy
    have := Ideal.mem_map_of_mem (D.map f).hom hy
    rwa [Ideal.map_map, sn f] at this
  have rep : ∀ b : B, ∃ j, ∃ y : D.obj j, (t.app j).hom y = b := fun b =>
    Concrete.isColimit_exists_rep D hc b
  have mem : ∀ x ∈ I.map φ, ∃ j, ∃ y : D.obj j, y ∈ I.map (s.app j).hom ∧ (t.app j).hom y = x := by
    intro x hx
    obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, ha, rfl⟩ := h
      exact ⟨j0, (s.app j0).hom a, Ideal.mem_map_of_mem _ ha, hst j0 a⟩
    | zero => exact ⟨j0, 0, zero_mem _, map_zero _⟩
    | add x x' _ _ h h' =>
      obtain ⟨j, y, hy, rfl⟩ := h
      obtain ⟨k, y', hy', rfl⟩ := h'
      refine ⟨IsFiltered.max j k, (D.map (IsFiltered.leftToMax j k)).hom y + (D.map (IsFiltered.rightToMax j k)).hom y',
        add_mem (mv _ _ hy) (mv _ _ hy'), ?_⟩
      rw [map_add (f := _), tn, tn]
    | smul b x _ h =>
      obtain ⟨j, y, hy, rfl⟩ := h
      obtain ⟨k, c, rfl⟩ := rep b
      refine ⟨IsFiltered.max k j, (D.map (IsFiltered.leftToMax k j)).hom c * (D.map (IsFiltered.rightToMax k j)).hom y,
        Ideal.mul_mem_left _ _ (mv _ _ hy), ?_⟩
      rw [map_mul, tn, tn]; rfl
  constructor
  · intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.eq] at huv
    rw [Ideal.Quotient.eq]
    rw [← map_sub] at huv
    obtain ⟨j, y, hy, hy'⟩ := mem _ huv
    rw [← hst j] at hy'
    obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc y ((s.app j).hom (a - a')) hy'
    have h1 : (s.app k).hom (a - a') ∈ I.map (s.app k).hom := by
      have e : (D.map g).hom ((s.app j).hom (a - a')) = (D.map f).hom y := hfg.symm
      have e2 : ((D.map g).hom.comp (s.app j).hom) (a - a') = (s.app k).hom (a - a') :=
        congrArg (fun r : A →+* D.obj k => r (a - a')) (sn g)
      rw [← e2]
      have := mv f y hy
      rw [← e] at this
      exact this
    have h2 := (hj k).1.2.1 (a₁ := Ideal.Quotient.mk I (a - a')) (a₂ := 0) (by
      rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact h1)
    exact (Ideal.Quotient.eq_zero_iff_mem).1 h2
  · intro w
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨j, y, rfl⟩ := rep b
    obtain ⟨u, hu⟩ := (hj j).1.2.2 (Ideal.Quotient.mk _ y)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hu
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    have hc' : (t.app j).hom.comp (s.app j).hom = φ :=
      congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom) (hj j).2
    have := Ideal.mem_map_of_mem (t.app j).hom hu
    rw [Ideal.map_map, hc', map_sub, hst] at this
    exact this

end LateralTheory.CohomologicalPurity.TubeCut
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPurRedPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurRedPf

open PurPf

theorem inv_red (q r : ℕ) {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (hq : Function.Bijective (pull (ZMod q) f (tw q i) n)) (hr : Function.Bijective (pull (ZMod r) f (tw r i) n))
    (y : Ht q E n i) :
    (AddEquiv.ofBijective _ hr).symm (red q r E n i y) = red q r E' n i ((AddEquiv.ofBijective _ hq).symm y) := by
  apply hr.1
  rw [AddEquiv.ofBijective_apply_symm_apply]
  rw [GlobalTheory.EtC.pull_red]
  congr 1
  exact ((AddEquiv.ofBijective _ hq).apply_symm_apply y).symm

def redS (q r : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs r P n i :=
  ⟨red q r _ n i x.1, by
    change pull _ (dbl.inr P) (tw r i) n (red q r _ n i x.1) = 0
    have hx : pull _ (dbl.inr P) (tw q i) n x.1 = 0 := x.2
    rw [GlobalTheory.EtC.pull_red, hx, map_zero]⟩

theorem redS_coe (q r : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : (redS q r P n i x).1 = red q r _ n i x.1 := rfl

theorem Hs.pullS_red (q r : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull r φ n i (redS q r P n i x) = redS q r P' n i (Hs.pull q φ n i x) := by
  apply Subtype.ext
  change pull _ (dbl.map φ) (tw r i) n (red q r _ n i x.1) = red q r _ n i (pull _ (dbl.map φ) (tw q i) n x.1)
  rw [GlobalTheory.EtC.pull_red]

theorem Hs.inv_red (q r : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ)
    (hq : Function.Bijective (Hs.pull q φ n i)) (hr : Function.Bijective (Hs.pull r φ n i)) (y : Hs q P' n i) :
    (AddEquiv.ofBijective _ hr).symm (redS q r P' n i y) = redS q r P n i ((AddEquiv.ofBijective _ hq).symm y) := by
  apply hr.1
  rw [AddEquiv.ofBijective_apply_symm_apply, Hs.pullS_red]
  congr 1
  exact ((AddEquiv.ofBijective _ hq).apply_symm_apply y).symm

theorem Hs.act_red (hA : A11) (q r : ℕ) [NeZero q] (hrq : r ∣ q) {P : Arrow Spc} {n m i j : ℤ}
    (a : Ht q P.right n i) (b : Hs q P m j) :
    Hs.act r (red q r _ n i a) (redS q r P m j b) = redS q r P _ _ (Hs.act q a b) := by
  apply Subtype.ext
  have hc : cup r (pull _ (dbl.fold P) (tw r i) n (red q r _ n i a)) (red q r _ m j b.1) =
      red q r _ _ _ (cup q (pull _ (dbl.fold P) (tw q i) n a) b.1) := by
    rw [(hA q r hrq (dbl P)).1, GlobalTheory.EtC.pull_red]
  simp only [Hs.act, Hs.proj, redS_coe]
  rw [hc, map_sub, GlobalTheory.EtC.pull_red, GlobalTheory.EtC.pull_red]

theorem fcl_isCl (hH : Hyp) (hCl : LeafCl) (d : ℕ) : IsCl d (fcl d) := by
  unfold fcl
  exact pick_spec (hCl hH d)

theorem purT_eq {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (a : Ht q (sch.obj P.Z) n i) :
    purT T q P n i a = (AddEquiv.ofBijective _ (((T P).ok q hq).2.2.1 (n + 2 * d) (i + d))).symm
      (Hs.act q (P := abv P.U (T P).π) ((AddEquiv.ofBijective _ (((T P).ok q hq).1 i n)).symm
        (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n a))
        (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P))) := by
  unfold purT
  rw [dite_eq_left ⟨NeZero.ne q, hq⟩]
  rfl

theorem act_fcl (hH : Hyp) (hCl : LeafCl) {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d)
    (hq : IsUnit (q : Γ(P.X, ⊤))) (r : ℕ) (hrq : r ∣ q) (n i : ℤ) (x : Ht q (T P).E n i) :
    Hs.act r (P := abv P.U (T P).π) (red q r (T P).E n i x) (Hs.pull r (abvMap P.U (T P).π) _ _ (fcl d r P)) =
      redS q r _ _ _ (Hs.act q (P := abv P.U (T P).π) x (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P))) := by
  have hfr : fcl d r P = redS q r _ _ _ (fcl d q P) := Subtype.ext (((fcl_isCl hH hCl d) q).2.2 r hrq P hq)
  rw [hfr, Hs.pullS_red]
  exact Hs.act_red hH.2.2.2.2.2.2.2.1 q r hrq _ _

end PurRedPf

open PurPf PurRedPf

theorem LeafPurRed_of : EtalePurityReduction := by
  intro hH hCl d T q _ P hq r hrq n i a
  have hq0 : q ≠ 0 := NeZero.ne q
  have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (zero_dvd_iff.mp hrq)
  have : NeZero r := ⟨hr0⟩
  have hru : IsUnit (r : Γ(P.X, ⊤)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hrq) hq
  rw [purT_eq T r P hru, purT_eq T q P hq, GlobalTheory.EtC.pull_red, inv_red q r _ n i (((T P).ok q hq).1 i n) (((T P).ok r hru).1 i n), act_fcl hH hCl T q P hq r hrq, Hs.inv_red q r _ _ _, redS_coe]

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafLocExcPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem five_bij {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type*} [AddCommGroup A1] [AddCommGroup A2] [AddCommGroup A3]
    [AddCommGroup A4] [AddCommGroup A5] [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3] [AddCommGroup B4]
    [AddCommGroup B5] (f1 : A1 →+ A2) (f2 : A2 →+ A3) (f3 : A3 →+ A4) (f4 : A4 →+ A5)
    (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (v1 : A1 →+ B1) (v2 : A2 →+ B2) (v3 : A3 →+ B3) (v4 : A4 →+ B4) (v5 : A5 →+ B5)
    (hf2 : Function.Exact f1 f2) (hf3 : Function.Exact f2 f3) (hf4 : Function.Exact f3 f4)
    (hg2 : Function.Exact g1 g2) (hg3 : Function.Exact g2 g3) (hg4 : Function.Exact g3 g4)
    (c1 : ∀ x, g1 (v1 x) = v2 (f1 x)) (c2 : ∀ x, g2 (v2 x) = v3 (f2 x)) (c3 : ∀ x, g3 (v3 x) = v4 (f3 x))
    (c4 : ∀ x, g4 (v4 x) = v5 (f4 x))
    (h1 : Function.Surjective v1) (h2 : Function.Bijective v2) (h4 : Function.Bijective v4)
    (h5 : Function.Injective v5) : Function.Bijective v3 := by
  refine ⟨(injective_iff_map_eq_zero v3).2 fun a ha => ?_, fun b => ?_⟩
  · have e4 : f3 a = 0 := h4.1 (by rw [← c3, ha]; simp)
    obtain ⟨a2, rfl⟩ := (hf3 a).1 e4
    have e2 : g2 (v2 a2) = 0 := by rw [c2, ha]
    obtain ⟨b1, hb1⟩ := (hg2 _).1 e2
    obtain ⟨a1, rfl⟩ := h1 b1
    have e1 : f1 a1 = a2 := h2.1 (by rw [← c1, hb1])
    subst e1
    exact (hf2 _).2 ⟨a1, rfl⟩
  · obtain ⟨a4, ha4⟩ := h4.2 (g3 b)
    have e5 : f4 a4 = 0 := h5 (by rw [← c4, ha4, map_zero]; exact (hg4 _).2 ⟨b, rfl⟩)
    obtain ⟨a3, ha3⟩ := (hf4 a4).1 e5
    have e3 : g3 (b - v3 a3) = 0 := by rw [map_sub, c3, ha3, ha4, sub_self]
    obtain ⟨b2, hb2⟩ := (hg3 _).1 e3
    obtain ⟨a2, rfl⟩ := h2.2 b2
    refine ⟨a3 + f2 a2, ?_⟩
    rw [map_add (f := _), ← c2, hb2]
    abel

theorem mono_sch_open {X : Scheme.{0}} (U : X.Opens) : Mono (sch.map U.ι) := by
  have hy : Mono (yoneda.map U.ι) := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun T => ?_
    exact (mono_iff_injective _).2 fun a b h => (cancel_mono U.ι).1 h
  exact @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun _ => hy

theorem eqv_of_loc (a1 : A1) {X : Scheme.{0}} {E : Spc} {π : E ⟶ sch.obj X} (L : Loc π) (R : Type) [CommRing R]
    {Y : Scheme.{0}} (g : Y ⟶ X) (F : Shv R) : Eqv R (pullback.snd π (sch.map g)) F :=
  fun n => @a1 R _ _ _ _ (L R Y g) F n

theorem eqv_base (a1 : A1) {X : Scheme.{0}} {E : Spc} {π : E ⟶ sch.obj X} (L : Loc π) (R : Type) [CommRing R]
    (F : Shv R) : Eqv R π F := by
  have hi : IsIso (sch.map (𝟙 X)) := inferInstance
  have e : pullback.fst π (sch.map (𝟙 X)) ≫ π = pullback.snd π (sch.map (𝟙 X)) ≫ sch.map (𝟙 X) := pullback.condition
  have h1 : Eqv R (pullback.fst π (sch.map (𝟙 X)) ≫ π) F := by
    rw [e]; exact eqv_comp (eqv_of_loc a1 L R _ F) (eqv_iso _ F)
  have e' : π = inv (pullback.fst π (sch.map (𝟙 X))) ≫ pullback.fst π (sch.map (𝟙 X)) ≫ π :=
    (IsIso.inv_hom_id_assoc _ _).symm
  rw [e']
  exact eqv_comp (eqv_iso _ F) h1

theorem fgt_nat (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right _ _ (Hs.fgt q P n i x) := by
  have e : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P := pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp, e]

theorem hom_nat (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Ht q P.right n i) :
    pull _ P'.hom (tw q i) n (pull _ φ.right _ _ x) = pull _ φ.left _ _ (pull _ P.hom _ n x) := by
  rw [← pull_comp, ← pull_comp, Arrow.w φ]

theorem LeafLocExc_of (bd : LeafBd) : LeafLocExc := by
  intro a1 q X U E π L
  obtain ⟨δ, ex, nat, -⟩ := bd
  have hm : Mono (opn U).hom := mono_sch_open U
  have hm' : Mono (abv U π).hom := by
    change Mono (pullback.fst π (sch.map U.ι)); have := mono_sch_open U; infer_instance
  have eR : ∀ i n, Function.Bijective (pull _ (abvMap U π).right (tw q i) n) := fun i =>
    eqv_base a1 L (ZMod q) (tw q i)
  have eL : ∀ i n, Function.Bijective (pull _ (abvMap U π).left (tw q i) n) := fun i =>
    eqv_of_loc a1 L (ZMod q) U.ι (tw q i)
  intro n i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact five_bij (pull _ (opn U).hom (tw q i) m) (δ q (opn U) m i) (Hs.fgt q (opn U) (m + 1) i)
    (pull _ (opn U).hom (tw q i) (m + 1))
    (pull _ (abv U π).hom (tw q i) m) (δ q (abv U π) m i) (Hs.fgt q (abv U π) (m + 1) i)
    (pull _ (abv U π).hom (tw q i) (m + 1))
    (pull _ (abvMap U π).right _ _) (pull _ (abvMap U π).left _ _) (Hs.pull q (abvMap U π) (m + 1) i)
    (pull _ (abvMap U π).right _ _) (pull _ (abvMap U π).left _ _)
    (ex q _ hm m i).2.1 (ex q _ hm m i).2.2 (ex q _ hm (m + 1) i).1
    (ex q _ hm' m i).2.1 (ex q _ hm' m i).2.2 (ex q _ hm' (m + 1) i).1
    (hom_nat q _ m i) (fun x => (nat q _ _ (abvMap U π) hm' hm m i x).symm) (fgt_nat q _ (m + 1) i)
    (hom_nat q _ (m + 1) i)
    (eR i m).2 (eL i m) (eR i (m + 1)) (eL i (m + 1)).1

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafZlocPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.ZlocPf

theorem res_comp {R : Type} [CommRing R] {G : Shv R} {T V W : Scheme.{0}} (f : T ⟶ V) (g : V ⟶ W) (a : Sec G W) :
    Sec.res (f ≫ g) a = Sec.res f (Sec.res g a) := by
  show (G.obj.map (f ≫ g).op).hom a = (G.obj.map f.op).hom ((G.obj.map g.op).hom a)
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_zero {R : Type} [CommRing R] {G : Shv R} {V W : Scheme.{0}} (f : V ⟶ W) :
    Sec.res f (0 : Sec G W) = 0 := by
  show (G.obj.map f.op).hom 0 = 0
  exact map_zero _

theorem map_res {R : Type} [CommRing R] {G H : Shv R} (φ : G ⟶ H) {V W : Scheme.{0}} (f : V ⟶ W) (a : Sec G W) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  have e := φ.hom.naturality f.op
  show (G.obj.map f.op ≫ φ.hom.app (op V)).hom a = (φ.hom.app (op W) ≫ H.obj.map f.op).hom a
  rw [e]

theorem sep {R : Type} [CommRing R] {G : Shv R} {Y : Scheme.{0}} (s : Sec G Y)
    (H : ∀ y : Y, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y), IsOpenImmersion f ∧ y ∈ Set.range f ∧ Sec.res f s = 0) : s = 0 := by
  let I := {p : Σ Z : Scheme.{0}, Z ⟶ Y // IsOpenImmersion p.2 ∧ Sec.res p.2 s = 0}
  let Zf : I → Scheme.{0} := fun i => i.1.1
  let ff : ∀ i : I, Zf i ⟶ Y := fun i => i.1.2
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.property
  have hmem : Sieve.generate (Presieve.ofArrows Zf ff) ∈ Scheme.etaleTopology Y := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun y => ?_, fun i => ?_⟩
    · obtain ⟨Z, f, hf, hy, hs⟩ := H y
      exact ⟨⟨⟨Z, f⟩, hf, hs⟩, hy⟩
    · haveI := i.2.1
      exact (inferInstance : Etale i.1.2)
  have hS := hG.isSheafFor _ hmem
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hS
  have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) ff
      (fun _ => (0 : Sec G _)) := by
    intro i j Z gi gj _
    change (G.obj.map gi.op).hom 0 = (G.obj.map gj.op).hom 0
    simp
  obtain ⟨t, -, ht⟩ := hS _ hc
  have e1 := ht s (fun i => i.2.2)
  have e2 := ht 0 (fun i => res_zero (G := G) i.1.2)
  rw [e1, e2]

theorem vanish {R : Type} [CommRing R] {G : Shv R} {Y Z T : Scheme.{0}} (f : Z ⟶ Y) [IsOpenImmersion f] (g : T ⟶ Y)
    (hr : Set.range g ⊆ Set.range f) (s : Sec G Y) (h0 : Sec.res f s = 0) : Sec.res g s = 0 := by
  rw [← IsOpenImmersion.lift_fac f g hr, res_comp, h0, res_zero]

theorem pt {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (q : V.toScheme) : W.ι (X.homOfLE h q) = V.ι q := by
  rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

theorem memι {X : Scheme.{0}} (V : X.Opens) (q : V.toScheme) : V.ι q ∈ V := by
  show V.ι q ∈ (V : Set X)
  rw [← Scheme.Opens.range_ι V]; exact ⟨q, rfl⟩

theorem lift_pt {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (y : W.toScheme) (hy : W.ι y ∈ V) :
    y ∈ Set.range (X.homOfLE h) := by
  change W.ι y ∈ (V : Set X) at hy
  rw [← Scheme.Opens.range_ι V] at hy
  obtain ⟨q, hq⟩ := hy
  refine ⟨q, W.ι.isOpenEmbedding.injective ?_⟩
  rw [pt, hq]

theorem rangeU {X : Scheme.{0}} (U : X.Opens) {V W : X.Opens} (h : V ≤ W) :
    Set.range ((V.ι ⁻¹ᵁ U).ι ≫ X.homOfLE h) ⊆ Set.range (W.ι ⁻¹ᵁ U).ι := by
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  show W.ι (((V.ι ⁻¹ᵁ U).ι ≫ X.homOfLE h) p) ∈ U
  rw [Scheme.Hom.comp_apply, pt]
  exact memι (V.ι ⁻¹ᵁ U) p

open LateralTheory.CohomologicalPurity.Cl in
theorem LeafZloc_of : LateralTheory.CohomologicalPurity.Cl.Flq.LeafZloc := by
  intro R _ K X U n
  refine ⟨?_, ?_⟩
  · intro V W h a ha
    obtain ⟨ha1, ha2⟩ := (mem_Zc a).1 ha
    refine (mem_Zc _).2 ⟨?_, ?_⟩
    · rw [← res_comp]; exact vanish _ _ (rangeU U h) a ha1
    · rw [map_res, ha2, res_zero]
  · intro W a H
    refine (mem_Zc _).2 ⟨?_, ?_⟩
    · apply sep; intro y
      obtain ⟨V, h, hxV, hb⟩ := H (W.ι ((W.ι ⁻¹ᵁ U).ι y)) (memι W _)
      obtain ⟨hb1, -⟩ := (mem_Zc _).1 hb
      let O : (W.ι ⁻¹ᵁ U).toScheme.Opens := ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) ⁻¹ᵁ V
      refine ⟨O.toScheme, O.ι, inferInstance, ?_, ?_⟩
      · rw [Scheme.Opens.range_ι]
        show ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) y ∈ V
        rw [Scheme.Hom.comp_apply]; exact hxV
      · rw [← res_comp]
        apply vanish ((V.ι ⁻¹ᵁ U).ι ≫ X.homOfLE h) _ ?_ a (by rw [res_comp]; exact hb1)
        rintro _ ⟨z, rfl⟩
        have hz : ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) (O.ι z) ∈ V := memι O z
        rw [Scheme.Hom.comp_apply] at hz
        have hwU : W.ι ((W.ι ⁻¹ᵁ U).ι (O.ι z)) ∈ U := memι (W.ι ⁻¹ᵁ U) (O.ι z)
        obtain ⟨q, hq⟩ := lift_pt h _ hz
        have hqU : q ∈ (V.ι ⁻¹ᵁ U : Set V.toScheme) := by
          show V.ι q ∈ U
          rw [← pt h, hq]; exact hwU
        rw [← Scheme.Opens.range_ι] at hqU
        obtain ⟨p, hp⟩ := hqU
        exact ⟨p, by rw [Scheme.Hom.comp_apply, hp, hq, Scheme.Hom.comp_apply]⟩
    · apply sep; intro y
      obtain ⟨V, h, hxV, hb⟩ := H (W.ι y) (memι W y)
      obtain ⟨-, hb2⟩ := (mem_Zc _).1 hb
      refine ⟨V.toScheme, X.homOfLE h, inferInstance, lift_pt h y hxV, ?_⟩
      rw [← map_res]; exact hb2

end LateralTheory.CohomologicalPurity.ZlocPf
end
end
