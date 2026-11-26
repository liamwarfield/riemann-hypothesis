module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafPurPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafLocPf

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

theorem HK.pull_sub' (R : Type) [CommRing R] {K L : Cx R} (f g : K ⟶ L) (F : Shv R) (n : ℤ)
    (x : HK R L F n) : HK.pull R (f - g) F n x = HK.pull R f F n x - HK.pull R g F n x := by
  rcases x.mk_surjective with ⟨z, rfl⟩
  simp only [HK.pull, HK.pre, cpre_mk]
  rw [← CohomologyClass.mk_sub]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_sub, Cochain.sub_comp]

theorem HK.pull_zero' (R : Type) [CommRing R] {K L : Cx R} (F : Shv R) (n : ℤ)
    (x : HK R L F n) : HK.pull R (0 : K ⟶ L) F n x = 0 := by
  have h := HK.pull_sub' R (0 : K ⟶ L) 0 F n x
  rw [sub_self, sub_self] at h
  exact h

def secC (q : ℕ) (P : Arrow Spc) :
    cokernel ((chains (ZMod q)).map (dbl.inr P)) ⟶ (chains (ZMod q)).obj (dbl P) :=
  cokernel.desc _ (𝟙 _ - (chains (ZMod q)).map (dbl.fold P) ≫ (chains (ZMod q)).map (dbl.inr P)) (by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ← Functor.map_comp, dbl.inr_fold,
      CategoryTheory.Functor.map_id, Category.id_comp, sub_self])

theorem pi_secC (q : ℕ) (P : Arrow Spc) :
    cokernel.π ((chains (ZMod q)).map (dbl.inr P)) ≫ secC q P =
      𝟙 _ - (chains (ZMod q)).map (dbl.fold P) ≫ (chains (ZMod q)).map (dbl.inr P) := by
  simp [secC]

theorem secC_pi (q : ℕ) (P : Arrow Spc) :
    secC q P ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr P)) = 𝟙 _ := by
  rw [← cancel_epi (cokernel.π _), ← Category.assoc, pi_secC, Category.comp_id, Preadditive.sub_comp,
    Category.id_comp, Category.assoc, cokernel.condition, Limits.comp_zero, sub_zero]

def eHom (q : ℕ) (n i : ℤ) (P : Arrow Spc) :
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n →+ Hs q P n i :=
  (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n).codRestrict _ fun x => by
    change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.inr P)) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) = 0
    rw [← HK.pull_comp', cokernel.condition, HK.pull_zero']

def eEquiv (q : ℕ) (n i : ℤ) (P : Arrow Spc) :
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hs q P n i where
  toFun := eHom q n i P
  invFun y := HK.pull (ZMod q) (secC q P) (tw q i) n y.1
  left_inv x := by
    change HK.pull (ZMod q) (secC q P) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) = x
    rw [← HK.pull_comp', secC_pi, HK.pull_id']
  right_inv y := by
    apply Subtype.ext
    change HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n
      (HK.pull (ZMod q) (secC q P) (tw q i) n y.1) = y.1
    have hy : HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.inr P)) (tw q i) n y.1 = 0 := y.2
    rw [← HK.pull_comp', pi_secC, HK.pull_sub', HK.pull_id', HK.pull_comp', hy, map_zero, sub_zero]
  map_add' := map_add _

theorem EtaleExcIdent : LeafExcIdent := by
  intro q n i
  refine ⟨eEquiv q n i, fun {P' P} φ x => ?_⟩
  apply Subtype.ext
  change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.map φ)) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) =
    HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P'))) (tw q i) n
      (HK.pull (ZMod q) (cokC q φ) (tw q i) n x)
  rw [← HK.pull_comp', ← HK.pull_comp']
  congr 2
  simp [cokC]

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafChartFactPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

def WVec (d : ℕ) (U : Scheme.{0}) : Type := {v : Vec (d + 1) 0 U // IsUnit (v.1 0)}

instance (d : ℕ) (U : Scheme.{0}) : SmallCategory (WVec d U) where
  Hom v w := v.1 ⟶ w.1
  id v := 𝟙 v.1
  comp f g := f ≫ g
  id_comp f := Category.id_comp (obj := Vec (d + 1) 0 U) f
  comp_id f := Category.comp_id (obj := Vec (d + 1) 0 U) f
  assoc f g h := Category.assoc (obj := Vec (d + 1) 0 U) f g h

def WVec.map (d : ℕ) {V U : Scheme.{0}} (f : V ⟶ U) : WVec d U ⥤ WVec d V where
  obj v := ⟨(Vec.map (d + 1) 0 f).obj v.1, v.2.map f.appTop.hom⟩
  map u := (Vec.map (d + 1) 0 f).map u
  map_id v := (Vec.map (d + 1) 0 f).map_id v.1
  map_comp p q := (Vec.map (d + 1) 0 f).map_comp p q

def wCat (d : ℕ) : Scheme.{0}ᵒᵖ ⥤ Cat.{0,0} where
  obj U := Cat.of (WVec d U.unop)
  map f := (WVec.map d f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

def Wsp (d : ℕ) : Spc := (wCat d ⋙ nerveFunctor).flip

def WVec.incl (d : ℕ) (U : Scheme.{0}) : WVec d U ⥤ Vec (d + 1) 0 U where
  obj v := v.1
  map u := u

def Wincl (d : ℕ) : Wsp d ⟶ Pj (d + 1) 0 :=
  nerveMap { app := fun U => (WVec.incl d U.unop).toCatHom, naturality := fun _ _ _ => rfl }

def Wpt {d : ℕ} {X : Scheme.{0}} (v : WVec d X) : sch.obj X ⟶ Wsp d where
  app n :=
    { app := fun U => TypeCat.ofHom fun (f : U.unop ⟶ X) =>
        (Functor.const (Fin (n.unop.len + 1))).obj ((WVec.map d f).obj v)
      naturality := fun U U' g => by
        ext f
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq ?_)
        exact ((WVec.map d g.unop).map_id ((WVec.map d f).obj v)).symm }
  naturality n m f := rfl

theorem wpt_incl {d : ℕ} {X : Scheme.{0}} (v : WVec d X) : Wpt v ≫ Wincl d = Pj.pt v.1 := rfl

def wvec1 {d : ℕ} {A : Type} [CommRing A] (x : Fin d → A) : WVec d (Spec (CommRingCat.of A)) :=
  ⟨vec1 x, by
    show IsUnit ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) 0))
    rw [Fin.cons_zero, map_one]; exact isUnit_one⟩

abbrev W (d : ℕ) (R : Type) [CommRing R] : Spc := Wsp d ⨯ sp R

def wb (d : ℕ) (R : Type) [CommRing R] : W d R ⟶ PR (d + 1) 0 R := prod.map (Wincl d) (𝟙 _)

def wa (d : ℕ) (R : Type) [CommRing R] : sp (MvPolynomial (Fin d) R) ⟶ W d R :=
  prod.lift (Wpt (wvec1 MvPolynomial.X)) (spMap MvPolynomial.C)

theorem wa_wb (d : ℕ) (R : Type) [CommRing R] : wa d R ≫ wb d R =
    (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
      sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) := by
  simp only [wa, wb, prod.lift_map, Category.comp_id, wpt_incl]
  rfl

theorem opn_mono {X : Scheme.{0}} (U : X.Opens) : Mono (opn U).hom := by
  change Mono (sch.map U.ι)
  have h : ∀ n, Mono ((sch.map U.ι).app n) := by
    intro n
    have : ∀ V, Mono (((sch.map U.ι).app n).app V) := by
      intro V
      rw [mono_iff_injective]
      intro f g h
      change f ≫ U.ι = g ≫ U.ι at h
      exact (cancel_mono U.ι).1 h
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

def LeafWCov : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  Cover2 (ZMod q) (wb d R) (pr d R).hom

def LeafWEqvR : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  ∀ i, Eqv _ (wa d R) (tw q i)

def LeafWEqvL : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
  (I : Ideal (MvPolynomial (Fin d) R)), Ideal.span (Set.range MvPolynomial.X) = I → IsUnit (q : R) →
  ∀ g : (opn (off (MvPolynomial (Fin d) R) I)).left ⟶ pullback (wb d R) (pr d R).hom,
  g ≫ pullback.fst _ _ = (opn (off (MvPolynomial (Fin d) R) I)).hom ≫ wa d R → ∀ i, Eqv _ g (tw q i)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

namespace LateralTheory.CohomologicalPurity.Thom.ExcP

open Chart in
theorem LeafChartFact_of (hG : LeafGeo) (hC : LeafWCov) (hR : LeafWEqvR) (hL : LeafWEqvL) :
    LeafChartFact := by
  intro hH q _ d R _ I hI hq Φ hΦ
  have := hG.1 d R
  have hab : wa d R ≫ wb d R = Φ.right := by rw [hΦ, wa_wb]
  have hw : ((opn (off (MvPolynomial (Fin d) R) I)).hom ≫ wa d R) ≫ wb d R = Φ.left ≫ (pr d R).hom := by
    erw [Category.assoc, hab]; exact (Arrow.w Φ).symm
  let P : Arrow Spc := Arrow.mk (pullback.fst (wb d R) (pr d R).hom)
  let β : P ⟶ pr d R := Arrow.homMk (pullback.snd _ _) (wb d R) pullback.condition.symm
  let α : opn (off (MvPolynomial (Fin d) R) I) ⟶ P :=
    Arrow.homMk (pullback.lift _ _ hw) (wa d R) (pullback.lift_fst _ _ _)
  refine ⟨P, α, β, ?_, opn_mono _, (IsPullback.of_hasPullback (wb d R) (pr d R).hom).mono_fst_of_mono this,
    hL hH q d R I hI hq _ (pullback.lift_fst _ _ _), hR hH q d R hq, IsPullback.of_hasPullback _ _, hC hH q d R hq⟩
  exact hom_ext (hG.1 d R) (by rw [Arrow.comp_right]; exact hab)

end LateralTheory.CohomologicalPurity.Thom.ExcP
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokPfSurj
section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def pcok (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A) (b : B' ⟶ B)
    (w : i' ≫ b = a ≫ i) : cokernel ((freeP R).map i') ⟶ cokernel ((freeP R).map i) :=
  cokernel.map _ _ ((freeP R).map a) ((freeP R).map b) (by rw [← Functor.map_comp, ← Functor.map_comp, w])

theorem isIso_cokernel_map_of_etale_local_iso (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i) (hW : Scheme.etaleTopology.W (pcok R i' i a b w)) :
    IsIso (cokernel.map ((free R).map i') ((free R).map i) ((free R).map a) ((free R).map b)
      (by rw [← Functor.map_comp, ← Functor.map_comp, w])) := by
  rw [GrothendieckTopology.W_iff] at hW
  let G := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  have w' : (freeP R).map i' ≫ (freeP R).map b = (freeP R).map a ≫ (freeP R).map i := by
    rw [← Functor.map_comp, ← Functor.map_comp, w]
  have key := cokernel_map_comp_cokernelComparison ((freeP R).map i') G ((freeP R).map i) ((freeP R).map a)
    ((freeP R).map b) w'
  have h2 : IsIso (cokernelComparison ((freeP R).map i') G ≫ G.map (pcok R i' i a b w)) := by
    have : IsIso (G.map (pcok R i' i a b w)) := hW
    infer_instance
  have h3 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, w', G.map_comp])) := by
    have h4 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, w', G.map_comp]) ≫ cokernelComparison _ G) := by
      rw [key]; exact h2
    exact IsIso.of_isIso_comp_right _ (cokernelComparison ((freeP R).map i) G)
  exact h3

def LeafFreeCokSurj : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y) →
  Presheaf.IsLocallySurjective Scheme.etaleTopology (pcok R i' i a b w)

def LeafFreeCokInj : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B'.obj (op T)) (x : A.obj (op T)), i.app (op T) x = b.app (op T) y →
    ∃ x' : A'.obj (op T), i'.app (op T) x' = y) →
  (∀ (T : Scheme.{0}) (y₁ y₂ : B'.obj (op T)), b.app (op T) y₁ = b.app (op T) y₂ →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      B'.map g.op y₁ = B'.map g.op y₂ ∨ ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op y₁)) →
  Presheaf.IsLocallyInjective Scheme.etaleTopology (pcok R i' i a b w)

theorem LeafFreeCok_of (hS : LeafFreeCokSurj) (hI : LeafFreeCokInj) : LeafFreeCok := by
  intro R _ A' B' A B i' i a b w h1 h2 h3
  apply isIso_cokernel_map_of_etale_local_iso
  have := hS R i' i a b w h2
  have := hI R i' i a b w h1 h3
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

end LateralTheory.CohomologicalPurity
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

variable {R : Type} [CommRing R]

theorem imageSieve_add' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}}
    (s₁ s₂ : G.obj (op T)) :
    Presheaf.imageSieve f s₁ ⊓ Presheaf.imageSieve f s₂ ≤ Presheaf.imageSieve f (s₁ + s₂) := by
  rintro V g ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩
  exact ⟨t₁ + t₂, by rw [map_add (f := _), map_add (f := _), h₁, h₂]⟩

theorem imageSieve_smul' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}}
    (r : ULift.{1} R) (s : G.obj (op T)) :
    Presheaf.imageSieve f s ≤ Presheaf.imageSieve f (r • s) := by
  rintro V g ⟨t, h⟩
  exact ⟨r • t, by rw [map_smul, map_smul, h]⟩

theorem imageSieve_zero' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}} :
    Presheaf.imageSieve f (0 : G.obj (op T)) = ⊤ := by
  ext V g
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩

theorem pcok_π_apply (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i) (V : Scheme.{0}ᵒᵖ) (m : ((freeP R).obj B').obj V) :
    (pcok R i' i a b w).app V ((cokernel.π ((freeP R).map i')).app V m) =
      (cokernel.π ((freeP R).map i)).app V (((freeP R).map b).app V m) := by
  have e : cokernel.π ((freeP R).map i') ≫ pcok R i' i a b w = (freeP R).map b ≫ cokernel.π _ := by
    simp [pcok]
  have := ConcreteCategory.congr_hom (NatTrans.congr_app e V) m
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using this

theorem π_freeP_apply (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ)
    (m : ((freeP R).obj A).obj V) :
    (cokernel.π ((freeP R).map i)).app V (((freeP R).map i).app V m) = 0 := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (cokernel.condition ((freeP R).map i)) V) m
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  rw [this]; rfl

theorem freePresheaf_map_freeMk (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ) (x : A.obj V) :
    ((freeP R).map i).app V (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (i.app V x)) := by
  exact ModuleCat.free_map_apply _ _

theorem freePresheaf_obj_map_freeMk (R : Type) [CommRing R] (B : PSh) {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) (x : B.obj V) :
    ((freeP R).obj B).map g (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (B.map g x)) := by
  exact ModuleCat.free_map_apply _ _

theorem π_app_surj (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ) :
    Function.Surjective ((cokernel.π ((freeP R).map i)).app V) := by
  have : Epi ((cokernel.π ((freeP R).map i)).app V) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 this

theorem exists_finset_adjoin_laurent_preimage (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i)
    (h2 : ∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y)
    (T : Scheme.{0}) (v : ((freeP R).obj B).obj (op T)) :
    Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈
      Scheme.etaleTopology T := by
  let J := Scheme.etaleTopology.{0}
  let N : Submodule (ULift.{1} R) (((freeP R).obj B).obj (op T)) :=
    { carrier := {v | Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈ J T}
      zero_mem' := by
        simp only [Set.mem_setOf_eq]; rw [map_zero, imageSieve_zero']; exact J.top_mem T
      add_mem' := fun {v₁ v₂} h₁ h₂ => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_add (f := _)]; exact J.superset_covering (imageSieve_add' _ _ _) (J.intersection_covering h₁ h₂)
      smul_mem' := fun r v h => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_smul]; exact J.superset_covering (imageSieve_smul' _ _ _) h }
  have gen : ∀ x, ModuleCat.freeMk x ∈ N := by
    rintro ⟨y⟩
    show Presheaf.imageSieve _ _ ∈ J T
    obtain ⟨S, hS, hS'⟩ := h2 T y
    refine J.superset_covering ?_ hS
    intro V g hg
    have nat := NatTrans.naturality_apply (cokernel.π ((freeP R).map i)) g.op (ModuleCat.freeMk (ULift.up y))
    rcases hS' g hg with ⟨x₀, hx₀⟩ | ⟨y', hy'⟩
    · refine ⟨0, ?_⟩
      rw [map_zero]; erw [← nat]
      rw [freePresheaf_obj_map_freeMk]; erw [← hx₀]; rw [← freePresheaf_map_freeMk R i (op V) x₀]; exact (π_freeP_apply R i (op V) _).symm
    · refine ⟨_, (pcok_π_apply R i' i a b w (op V) (ModuleCat.freeMk (ULift.up y'))).trans ?_⟩
      rw [freePresheaf_map_freeMk R b (op V) y']; erw [hy', ← freePresheaf_obj_map_freeMk R B g.op y]; exact nat
  show v ∈ N
  induction v using Finsupp.induction_linear with
  | zero => exact N.zero_mem
  | add v₁ v₂ h₁ h₂ => exact N.add_mem h₁ h₂
  | single x r =>
    have := N.smul_mem r (gen x)
    convert this using 1
    first
    | exact (Finsupp.smul_single_one x r).symm
    | (unfold ModuleCat.freeMk; erw [Finsupp.smul_single_one])

theorem leafFreeCokSurj : LeafFreeCokSurj := by
  intro R _ A' B' A B i' i a b w h2
  constructor
  intro T s
  obtain ⟨v, rfl⟩ := π_app_surj R i (op T) s
  exact exists_finset_adjoin_laurent_preimage R i' i a b w h2 T v

theorem LeafFreeCok_of_inj (hI : LeafFreeCokInj) : LeafFreeCok := LeafFreeCok_of leafFreeCokSurj hI

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcLevelPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def MM {P' P : Arrow Spc} (φ : P' ⟶ P) : Spc := pushout P'.hom (P'.hom ≫ φ.right)

def gM {P' P : Arrow Spc} (φ : P' ⟶ P) : MM φ ⟶ dbl P :=
  pushout.desc (φ.right ≫ dbl.inl P) (dbl.inr P) (by
    rw [← Category.assoc, ← Arrow.w φ, Category.assoc, Category.assoc]
    exact congrArg (φ.left ≫ ·) (pushout.condition (f := P.hom) (g := P.hom)))

def LeafExcOfEqv : Prop := ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), (∀ i, Eqv (ZMod q) (gM φ) (tw q i)) → Exc q φ

def LeafEqvOfExc : Prop := ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), Exc q φ → ∀ i, Eqv (ZMod q) (gM φ) (tw q i)

def LeafMLev : Prop := ∀ (P' P : Arrow Spc) (φ : P' ⟶ P) (n : SimplexCategoryᵒᵖ),
  ∃ (a : disc.obj ((MM φ).obj n) ≅ MM ((lev n).map φ)) (b : disc.obj ((dbl P).obj n) ≅ dbl ((lev n).obj P)),
    disc.map ((gM φ).app n) ≫ b.hom = a.hom ≫ gM ((lev n).map φ)

theorem LeafExcLevel_of (h1 : LeafExcOfEqv) (h2 : LeafEqvOfExc) (h3 : LeafMLev) : LeafExcLevel := by
  intro a3 q P' P φ hl
  apply h1 q P' P φ
  intro i
  apply a3
  intro n
  obtain ⟨a, b, w⟩ := h3 P' P φ n
  have e : disc.map ((gM φ).app n) = a.hom ≫ gM ((lev n).map φ) ≫ b.inv := by
    rw [← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  exact eqv_comp (eqv_iso _ _) (eqv_comp (h2 q _ _ _ (hl n) i) (eqv_iso _ _))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafSurjGeoPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity

theorem LeafSurjGeo_of : LeafSurjGeo := by
  intro X' X Z f _ ι' ι _ hp U hU T t
  let F : Bool → Scheme.{0} := fun b => Bool.rec (pullback t f) (t ⁻¹ᵁ U).toScheme b
  let m : ∀ b, F b ⟶ T := fun b => Bool.rec (pullback.fst t f) (t ⁻¹ᵁ U).ι b
  have hR : Presieve.ofArrows F m ∈ Scheme.precoverage @Etale T := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : t.base x ∈ (U : Set X)
      · refine ⟨true, ?_⟩
        show x ∈ Set.range (t ⁻¹ᵁ U).ι.base
        rw [Scheme.Opens.range_ι]; exact hx
      · rw [hU, Set.notMem_compl_iff] at hx
        obtain ⟨z, hz⟩ := hx
        have hw : f.base (ι'.base z) = ι.base z := by
          rw [← Scheme.Hom.comp_apply, hp.w]; simp
        obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := f) x (ι'.base z)
          (by rw [hw, hz])
        exact ⟨false, p, hp1⟩
    · cases b <;> dsimp [m] <;> infer_instance
  refine ⟨Sieve.generate (Presieve.ofArrows F m),
    Precoverage.generate_mem_toGrothendieck hR, ?_⟩
  intro V g hg
  obtain ⟨W, h, k, hk, rfl⟩ := hg
  obtain ⟨b⟩ := hk
  cases b
  · right
    refine ⟨h ≫ pullback.snd t f, ?_⟩
    simp only [m, Category.assoc, ← pullback.condition]
  · left
    refine ⟨h ≫ (t ∣_ U), ?_⟩
    simp only [m, Category.assoc, morphismRestrict_ι]

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafAugLocalPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

abbrev PCx (R : Type) [CommRing R] := ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ

def Cyc {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) : Prop :=
  ∀ m, ((K.d n m).app T).hom x = 0

def Bdy {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) : Prop :=
  ∃ y, ((K.d (n + 1) n).app T).hom y = x

def InjC {R : Type} [CommRing R] {K L : PCx R} (φ : K ⟶ L) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T), Cyc K n T x → Bdy L n T ((φ.f n).app T |>.hom x) →
    ∃ S ∈ Scheme.etaleTopology.{0} T.unop, ∀ ⦃U : Scheme.{0}⦄ (f : U ⟶ T.unop), S f → Bdy K n (op U) (((K.X n).map f.op).hom x)

def SurjC {R : Type} [CommRing R] {K L : PCx R} (φ : K ⟶ L) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{0}ᵒᵖ) (x : (L.X n).obj T), Cyc L n T x →
    ∃ S ∈ Scheme.etaleTopology.{0} T.unop, ∀ ⦃U : Scheme.{0}⦄ (f : U ⟶ T.unop), S f →
      ∃ x', Cyc K n (op U) x' ∧ Bdy L n (op U) (((φ.f n).app (op U)).hom x' - ((L.X n).map f.op).hom x)

def LeafHomLoc : Prop := ∀ (R : Type) [CommRing R] (K L : PCx R) (φ : K ⟶ L) (n : ℕ), InjC φ n → SurjC φ n →
  Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap φ n) ∧
  Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap φ n)

def LeafAugSurj : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    SurjC ((chainsP R).map (aug _ hc)) n

def LeafAugInj : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    InjC ((chainsP R).map (aug _ hc)) n

theorem LeafAugLocal_of (h1 : LeafHomLoc) (hs : LeafAugSurj) (hi : LeafAugInj) : LeafAugLocal := by
  intro J _ D X c ho hcov hdir hc R _ n
  exact h1 R _ _ _ n (hi J D X c ho hcov hdir hc R n) (hs J D X c ho hcov hc R n)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTailRepPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem Vec.hom_subsingleton (N k : ℕ) (U : Scheme.{0}) (v w : Vec N k U) : Subsingleton (v ⟶ w) := by
  constructor
  intro a b
  apply Subtype.ext; apply Units.ext
  rw [← sub_eq_zero]
  set s : Γ(U, ⊤) := (a.1 : Γ(U, ⊤)) - b.1 with hs_def
  have hs : ∀ i, s * w.1 i = 0 := fun i => by rw [hs_def, sub_mul, ← a.2 i, ← b.2 i, sub_self]
  have hcov : (⊤ : U.Opens) ≤ iSup fun i => U.basicOpen (w.1 i) := by
    intro p _
    obtain ⟨i, -, hp⟩ := w.2 p
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hp⟩
  refine U.sheaf.eq_of_locally_eq' (fun i => U.basicOpen (w.1 i)) ⊤ (fun i => homOfLE le_top) hcov s 0 fun i => ?_
  have hu : IsUnit (U.presheaf.map (homOfLE (U.basicOpen_le (w.1 i))).op (w.1 i)) :=
    U.toRingedSpace.isUnit_res_basicOpen (w.1 i)
  have h0 := congrArg (U.presheaf.map (homOfLE (U.basicOpen_le (w.1 i))).op) (hs i)
  rw [map_mul, map_zero] at h0
  change U.presheaf.map _ s = U.presheaf.map _ 0
  rw [map_zero]
  exact (hu.mul_left_eq_zero).1 h0

theorem off_le_C (A : Type) [CommRing A] (I : Ideal A) : off (Polynomial A) (I.map Polynomial.C) ≤
    Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I := by
  intro p hp
  simp only [off, Scheme.Hom.mem_preimage] at hp ⊢
  intro hI
  apply hp
  have hI' : ∀ x ∈ I, Polynomial.C x ∈ p.asIdeal := fun x hx => hI hx
  show ((Ideal.map Polynomial.C I : Ideal (Polynomial A)) : Set (Polynomial A)) ⊆ p.asIdeal
  exact Ideal.map_le_iff_le_comap.2 (fun x hx => hI' x hx)

def LeafTailNerve : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (n : SimplexCategoryᵒᵖ),
  ∃ (R' : Type) (_ : CommRing R') (_ : R →+* R')
    (e₁ : (PR (d + 1) 1 R).obj n ≅ (PR (d + 1) 1 R').obj (op (SimplexCategory.mk 0)))
    (e₂ : (PR d 0 R).obj n ≅ (PR d 0 R').obj (op (SimplexCategory.mk 0))),
    (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app n ≫ e₂.hom =
      e₁.hom ≫ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R' ⟶ PR d 0 R').app (op (SimplexCategory.mk 0))

def LeafTailRep0 : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : (PR (d + 1) 1 R).obj (op (SimplexCategory.mk 0)) ≅ yoneda.obj (off (Polynomial A) (I.map Polynomial.C)).toScheme)
      (e₂ : (PR d 0 R).obj (op (SimplexCategory.mk 0)) ≅ yoneda.obj (off A I).toScheme),
      (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app (op (SimplexCategory.mk 0)) ≫ e₂.hom =
        e₁.hom ≫ yoneda.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTailRep_of (hN : LeafTailNerve) (h0 : LeafTailRep0) : LeafTailRep := by
  intro d R _ n
  obtain ⟨R', _, ψ, e₁, e₂, w₁⟩ := hN d R n
  obtain ⟨A, _, I, φ, hI, h, f₁, f₂, w₂⟩ := h0 d R'
  refine ⟨A, inferInstance, I, φ.comp ψ, hI, h, disc.mapIso (e₁ ≪≫ f₁), disc.mapIso (e₂ ≪≫ f₂), ?_⟩
  change disc.map _ ≫ disc.map (e₂.hom ≫ f₂.hom) = disc.map (e₁.hom ≫ f₁.hom) ≫ disc.map (yoneda.map _)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, w₁, Category.assoc, w₂, Category.assoc]

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHtpyMVPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafFreeCov : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (U V : X.Opens),
  Epi (biprod.desc ((free R).map (yoneda.map (X.homOfLE (le_sup_left : U ≤ U ⊔ V))))
    ((free R).map (yoneda.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V)))))

namespace HtpyMVPf

theorem bij_pull_iso (R : Type) [CommRing R] (F : Shv R) {A B : Spc} (e : A ≅ B) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine ⟨fun x y h => ?_, fun y => ⟨pull R e.inv F n y, ?_⟩⟩
  · have hx := pull_comp R e.inv e.hom F n x
    have hy := pull_comp R e.inv e.hom F n y
    rw [e.inv_hom_id, pull_id] at hx hy
    rw [hx, hy, h]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem eqv_of_sq (R : Type) [CommRing R] (F : Shv R) {A B A' B' : Spc} (f : A ⟶ B) (g : A' ⟶ B')
    (α : A ≅ A') (β : B ≅ B') (w : α.hom ≫ g = f ≫ β.hom) (hf : Eqv R f F) : Eqv R g F := by
  intro n
  have h1 : (pull R α.hom F n) ∘ (pull R g F n) = (pull R f F n) ∘ (pull R β.hom F n) := by
    funext x; simp only [Function.comp_apply, ← pull_comp, w]
  have h2 : Function.Bijective ((pull R α.hom F n) ∘ (pull R g F n)) := by
    rw [h1]; exact (hf n).comp (bij_pull_iso R F β n)
  exact (Function.Bijective.of_comp_iff' (bij_pull_iso R F α n) _).1 h2

theorem mono_sch {Y Z : Scheme.{0}} (f : Y ⟶ Z) [Mono f] : Mono (sch.map f) := by
  have hy : Mono (yoneda.map f) := by
    have : ∀ T, Mono ((yoneda.map f).app T) := fun T => by
      rw [mono_iff_injective]
      intro a b h
      exact (cancel_mono f).1 h
    exact NatTrans.mono_of_mono_app _
  have : ∀ n, Mono ((sch.map f).app n) := fun _ => hy
  exact NatTrans.mono_of_mono_app _

theorem sch_pres : PreservesLimitsOfShape WalkingCospan sch := by
  unfold sch; infer_instance

end HtpyMVPf

theorem LeafHtpyMV_of (hF : LeafFreeCov) : LeafHtpyMV := by
  intro a4 R _ F X' X p U V U' V' hU hV hI hS hu hv hi
  have cov : ∀ (Y : Scheme.{0}) (A B : Y.Opens),
      Cover2 R (sch.map (Y.homOfLE (le_sup_left : A ≤ A ⊔ B))) (sch.map (Y.homOfLE (le_sup_right : B ≤ A ⊔ B))) :=
    fun Y A B => ⟨HtpyMVPf.mono_sch _, HtpyMVPf.mono_sch _, fun _ => hF R Y A B⟩
  have eu : X'.homOfLE (le_sup_left : U' ≤ U' ⊔ V') ≫ p.resLE (U ⊔ V) (U' ⊔ V') hS =
      p.resLE U U' hU ≫ X.homOfLE (le_sup_left : U ≤ U ⊔ V) := by
    simp
  have ev : X'.homOfLE (le_sup_right : V' ≤ U' ⊔ V') ≫ p.resLE (U ⊔ V) (U' ⊔ V') hS =
      p.resLE V V' hV ≫ X.homOfLE (le_sup_right : V ≤ U ⊔ V) := by
    simp
  have hu' := congrArg sch.map eu
  have hv' := congrArg sch.map ev
  rw [sch.map_comp, sch.map_comp] at hu' hv'
  refine a4 R _ _ _ _ _ _ _ hu' hv' F (cov X' U' V') (cov X U V) hu hv ?_
  have := HtpyMVPf.sch_pres
  have P' := (isPullback_opens_inf_le (X := X') (le_sup_left : U' ≤ U' ⊔ V') (le_sup_right : V' ≤ U' ⊔ V')).map sch
  have P := (isPullback_opens_inf_le (X := X) (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch
  refine HtpyMVPf.eqv_of_sq R F _ _ P'.isoPullback P.isoPullback ?_ hi
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc, Category.assoc,
      IsPullback.isoPullback_hom_fst, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp
  · rw [Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc, Category.assoc,
      IsPullback.isoPullback_hom_snd, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafInjGeoPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity

theorem injGeo_fib {X' X Z : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X)
    (hp : IsPullback ι' (𝟙 Z) f ι) :
    pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f =
      pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.snd f f := by
  have h1 : (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) ≫ f =
      pullback.snd (pullback.fst f f ≫ f) ι ≫ ι := by
    rw [Category.assoc]; exact pullback.condition
  have h2 : (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.snd f f) ≫ f =
      pullback.snd (pullback.fst f f ≫ f) ι ≫ ι := by
    rw [Category.assoc, ← pullback.condition]; exact h1
  have e1 := hp.lift_fst _ _ h1
  have e2 := hp.lift_fst _ _ h2
  have s1 := hp.lift_snd _ _ h1
  have s2 := hp.lift_snd _ _ h2
  rw [Category.comp_id] at s1 s2
  rw [← e1, ← e2, s1, s2]

theorem injGeo_fib_diag {X' X Z : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X)
    (hp : IsPullback ι' (𝟙 Z) f ι) :
    pullback.fst (pullback.fst f f ≫ f) ι =
      (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · simp
  · simp [injGeo_fib f ι' ι hp]

theorem injGeo_mem {X' X Z : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X)
    (hp : IsPullback ι' (𝟙 Z) f ι) (q : ↑(pullback f f))
    (hq : (pullback.fst f f ≫ f) q ∈ Set.range ι) : q ∈ Set.range (pullback.diagonal f) := by
  obtain ⟨r, rfl⟩ : q ∈ Set.range (pullback.fst (pullback.fst f f ≫ f) ι) := by
    rw [Scheme.Pullback.range_fst]; exact hq
  rw [injGeo_fib_diag f ι' ι hp]
  exact ⟨(pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) r, rfl⟩

theorem LeafInjGeo_of : LeafInjGeo := by
  intro X' X Z f _ ι' ι _ hp U hU T y₁ y₂ hy
  classical
  let p : T ⟶ pullback f f := pullback.lift y₁ y₂ hy
  let W : T.Opens := p ⁻¹ᵁ (pullback.diagonal f).opensRange
  let V : T.Opens := (y₁ ≫ f) ⁻¹ᵁ U
  have hW : ∀ (O : T.Opens), O ≤ W → O.ι ≫ y₁ = O.ι ≫ y₂ := by
    intro O hO
    have H : Set.range (O.ι ≫ p) ⊆ Set.range (pullback.diagonal f) := by
      rintro _ ⟨t, rfl⟩
      have := hO (show O.ι t ∈ O by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨t, rfl⟩)
      simpa [W] using this
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) (O.ι ≫ p) H
    have a1 : O.ι ≫ y₁ = (O.ι ≫ p) ≫ pullback.fst f f := by simp only [p, Category.assoc, pullback.lift_fst]
    have a2 : O.ι ≫ y₂ = (O.ι ≫ p) ≫ pullback.snd f f := by simp only [p, Category.assoc, pullback.lift_snd]
    rw [a1, a2, ← hl, Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  let O : T → T.Opens := fun τ => if (y₁ ≫ f) τ ∈ (U : Set X) then V else W
  have hO : ∀ τ, O τ ≤ W ∨ O τ ≤ V := by
    intro τ; simp only [O]; split_ifs
    · exact Or.inr le_rfl
    · exact Or.inl le_rfl
  have hcov : ∀ τ, τ ∈ O τ := by
    intro τ; simp only [O]; split_ifs with h
    · simpa [V] using h
    · have h' : (y₁ ≫ f) τ ∈ Set.range ι := by
        have : (y₁ ≫ f) τ ∉ (Set.range ι)ᶜ := by rw [← hU]; exact h
        simpa using this
      have hq : (pullback.fst f f ≫ f) (p τ) ∈ Set.range ι := by
        have : p ≫ pullback.fst f f ≫ f = y₁ ≫ f := by simp only [p, pullback.lift_fst_assoc]
        rw [← this] at h'; simpa using h'
      simpa [W] using injGeo_mem f ι' ι hp (p τ) hq
  refine ⟨Sieve.generate (Presieve.ofArrows (fun τ => (O τ).toScheme) (fun τ => (O τ).ι)),
    Precoverage.generate_mem_toGrothendieck ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ?_), ?_⟩
  · refine ⟨fun τ => ⟨τ, ?_⟩, fun τ => inferInstance⟩
    exact ⟨⟨τ, hcov τ⟩, rfl⟩
  · rintro Y g ⟨Y', h, _, ⟨τ⟩, rfl⟩
    rcases hO τ with h1 | h1
    · left
      simp only [Category.assoc, hW _ h1]
    · right
      refine ⟨h ≫ (y₁ ≫ f).resLE U (O τ) h1, ?_⟩
      simp [Scheme.Hom.resLE_comp_ι]
end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafSumPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut

def LeafChainsSum : Prop := ∀ (R : Type) [CommRing R] (A : Type) (E : A → Spc) (c : Cofan E), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj c.pt) fun a => (chains R).map (c.inj a)))

def LeafHKSum : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) (K : A → Cx R) (c : Cofan K),
  Nonempty (IsColimit c) → ∀ n : ℤ, Function.Bijective fun (x : HK R c.pt F n) (a : A) => HK.pull R (c.inj a) F n x

end LateralTheory.CohomologicalPurity.TubeCut.SumCut

namespace LateralTheory.CohomologicalPurity.TubeCut
open SumCut

theorem LeafSum_of (hc : LeafChainsSum) (hk : LeafHKSum) : LeafSum := by
  intro R _ F A E c hc' n
  exact hk R F A (fun a => (chains R).obj (E a)) _ (hc R A E c hc') n

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafRelPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafChPush : Prop := ∀ (q : ℕ) (P : Arrow Spc),
  IsPushout ((chains (ZMod q)).map P.hom) ((chains (ZMod q)).map P.hom) ((chains (ZMod q)).map (dbl.inl P))
    ((chains (ZMod q)).map (dbl.inr P))

def LeafHKSplit : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B D : Cx R} (f : A ⟶ B) (l r : B ⟶ D)
  (s : D ⟶ B), IsPushout f f l r → r ≫ s = 𝟙 _ → ∀ p : D ⟶ cokernel f, l ≫ p = cokernel.π f → r ≫ p = 0 →
  Function.Injective (HK.pull R p F n) ∧ ∀ x, HK.pull R r F n x = 0 → ∃ y, HK.pull R p F n y = x

theorem hk_pull_pull {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R f F n (HK.pull R g F n x) = HK.pull R (f ≫ g) F n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem hk_pull_zero {R : Type} [CommRing R] {K L : Cx R} (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (0 : K ⟶ L) F n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [← CohomologyClass.mk_zero]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem LeafRel_of (h1 : LeafChPush) (h2 : LeafHKSplit) : LeafRel := by
  intro q i
  have ex : ∀ P : Arrow Spc, ∃ p : (chains (ZMod q)).obj (dbl P) ⟶ cokernel ((chains (ZMod q)).map P.hom),
      (chains _).map (dbl.inl P) ≫ p = cokernel.π _ ∧ (chains _).map (dbl.inr P) ≫ p = 0 := fun P =>
    ⟨(h1 q P).desc (cokernel.π _) 0 (by simp), (h1 q P).inl_desc _ _ _, (h1 q P).inr_desc _ _ _⟩
  choose p hl hr using ex
  have hs : ∀ P : Arrow Spc, (chains (ZMod q)).map (dbl.inr P) ≫ (chains _).map (dbl.fold P) = 𝟙 _ := fun P => by
    rw [← Functor.map_comp, dbl.inr_fold, CategoryTheory.Functor.map_id]
  have mem : ∀ (P : Arrow Spc) (n : ℤ) x, HK.pull _ (p P) (tw q i) n x ∈ Hs q P n i := fun P n x => by
    change HK.pull _ ((chains _).map (dbl.inr P)) (tw q i) n (HK.pull _ (p P) (tw q i) n x) = 0
    rw [hk_pull_pull, hr, hk_pull_zero]
  refine ⟨fun P n => AddEquiv.ofBijective ((HK.pull _ (p P) (tw q i) n).codRestrict _ (mem P n)) ⟨fun x y h => ?_, fun x => ?_⟩,
    fun P n p' hl' hr' x => ?_⟩
  · exact (h2 _ (tw q i) n _ _ _ _ (h1 q P) (hs P) (p P) (hl P) (hr P)).1 (congrArg Subtype.val h)
  · obtain ⟨y, hy⟩ := (h2 _ (tw q i) n _ _ _ _ (h1 q P) (hs P) (p P) (hl P) (hr P)).2 x.1 x.2
    exact ⟨y, Subtype.ext hy⟩
  · have e : p' = p P := (h1 q P).hom_ext (hl'.trans (hl P).symm) (hr'.trans (hr P).symm)
    subst e; rfl

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafOffContPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def OffContN (r : ℕ) : Prop := ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (x : Fin r → A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  HtOffCont q φ (Ideal.span (Set.range x)) D s t n i

def OffContBasic : Prop := A1 → A4 → B1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (f : A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  HtOffCont q φ (Ideal.span {f}) D s t n i

def OffContStep : Prop := A1 → A4 → B1 → LeafBd → LeafExc → OffContBasic → ∀ r : ℕ, OffContN r → OffContN (r + 1)

theorem offContN_zero (hb : OffContBasic) (a1 : A1) (a4 : A4) (b1 : B1) : OffContN 0 := by
  intro q A B _ _ φ x hq J _ _ D s t hc he n i
  have hx : Ideal.span (Set.range x) = Ideal.span {(0 : A)} := by
    rw [Set.range_eq_empty, Ideal.span_empty, Ideal.span_singleton_eq_bot.mpr rfl]
  rw [hx]
  exact hb a1 a4 b1 q φ 0 hq J D s t hc he n i

theorem offContN_all (hb : OffContBasic) (hs : OffContStep) (a1 : A1) (a4 : A4) (b1 : B1) (bd : LeafBd)
    (ex : LeafExc) : ∀ r, OffContN r := by
  intro r
  induction r with
  | zero => exact offContN_zero hb a1 a4 b1
  | succ r ih => exact hs a1 a4 b1 bd ex hb r ih

theorem leafOffCont_of (hb : OffContBasic) (hs : OffContStep) : LeafOffCont := by
  intro a1 a4 b1 bd ex q A B _ _ φ I hI hq J _ _ D s t hc he n i
  obtain ⟨S, hS⟩ := hI
  have h := offContN_all hb hs a1 a4 b1 bd ex S.card q φ (fun k => (S.equivFin.symm k : A)) hq J D s t hc he n i
  have hr : Set.range (fun k => (S.equivFin.symm k : A)) = (S : Set A) := by
    ext a; constructor
    · rintro ⟨k, rfl⟩; exact (S.equivFin.symm k).2
    · intro ha; exact ⟨S.equivFin ⟨a, ha⟩, by simp⟩
  rw [hr, hS] at h
  exact h

theorem off_span_singleton (A : Type) [CommRing A] (f : A) :
    ((off A (Ideal.span {f}) : Set (Spec (CommRingCat.of A))) =
      ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A))) := by
  change (PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A))ᶜ = _
  rw [PrimeSpectrum.zeroLocus_span, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]

theorem range_fin_succ {A : Type} {r : ℕ} (x : Fin (r + 1) → A) :
    Set.range x = Set.range (fun k : Fin r => x k.castSucc) ∪ {x (Fin.last r)} := by
  rw [Set.union_singleton]
  ext a; constructor
  · rintro ⟨k, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · exact Set.mem_insert_of_mem _ ⟨k', rfl⟩
    · exact Set.mem_insert _ _
  · rintro (rfl | ⟨k, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

end LateralTheory.CohomologicalPurity
end
end
