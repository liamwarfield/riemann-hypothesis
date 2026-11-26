module

public import Development.EtaleCohomology.EtaleSheaves.TwPairExists
public import Development.EtaleCohomology.EtaleSheaves.UnitExistence.CocycleOfSec
public import Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2
public import Development.EtaleCohomology.TateTwists.HoldsOf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization
section -- merged from Development.EtaleCohomology.TateTwists.EtaleLocallyExistsQthRootOfUnitWhenQInvertible
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.FirstChernUniqueness

lemma sec_sub {q : ℕ} {F : Shv (ZMod q)} (hF : IsZero F) (U : Scheme.{0}) (a b : Sec F U) : a = b := by
  have h1 : IsZero F.obj := (sheafToPresheaf _ _).map_isZero hF
  have h2 : IsZero (F.obj.obj (op U)) := h1.obj (op U)
  have := (ModuleCat.isZero_iff_subsingleton.mp h2)
  exact Subsingleton.elim _ _

lemma res_zero_neg (q : ℕ) (s : ℤ) (hs : s < 0) : IsZero ((res _ (tw q 1)).X s) := by
  unfold res
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)

lemma sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact (NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x)

lemma loc_imp {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

def EtaleLocallyExistsQthRootOfUnitWhenQInvertible : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
  Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

lemma glMat_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    (glMat (y.res g) : Matrix (Fin 1) (Fin 1) Γ(V, ⊤)) = g.appTop.hom.mapMatrix (glMat y : Matrix (Fin 1) (Fin 1) Γ(U, ⊤)) := by
  rfl

lemma lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit
  have hn : (L.app (op (SimplexCategory.mk 1))).app (op V) (x.res g) =
      Sx.res g ((L.app (op (SimplexCategory.mk 1))).app (op U) x) := by
    unfold Sx.res; rw [NatTrans.naturality_apply]
  rw [hn]
  ext
  simp only [Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [glMat_res, RingHom.map_det]

lemma root_line (hr : EtaleLocallyExistsQthRootOfUnitWhenQInvertible) (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hi : Inv q E)
    (U : Scheme.{0}) (x : Sx E 1 U) : Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = lineUnit L (x.res g) := by
  refine loc_imp (hr q U (hi U ⟨x.sub 0 0 (by omega)⟩) (lineUnit L x)) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  exact ⟨v, by rw [lineUnit_res]; exact hv⟩

lemma loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hSP V g hg.1, hTQ V g hg.2⟩⟩

end LateralTheory.EtaleFoundations.FirstChernUniqueness
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChernClassSpecialization
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleExistenceAndUniqueness

open LateralTheory.E.CupProductRingLaws

section Ext
variable {R : Type} [CommRing R]

theorem free_hom_ext {P : PSh} {F : Shv R} (f g : (free R).obj P ⟶ F)
    (h : ∀ U x, (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (J := Scheme.etaleTopology) f.hom g.hom F.property
  ext U : 2
  induction U using Opposite.rec with | _ U => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  exact h U x

theorem cochain_ext_ev {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (hev : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev α p s h U x = ev β p s h U x) :
    α = β := by
  apply Cochain.ext
  intro p s hps
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨p.natAbs, by omega⟩
    have : (chainsXIso R E k).inv ≫ α.v _ _ hps = (chainsXIso R E k).inv ≫ β.v _ _ hps :=
      free_hom_ext _ _ (fun U x => hev k s hps U x)
    simpa using this
  · refine (HomologicalComplex.isZero_extend_X _ _ p (fun i => ?_)).eq_of_src _ _
    show -(i : ℤ) ≠ p
    omega

theorem res_isZero (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) :=
  HomologicalComplex.isZero_extend_X _ _ s (fun i => by show (i : ℤ) ≠ s; omega)

end Ext

def EtaleKummerChernCocycleEvaluationsUnique : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ γ γ', IsEtaleFirstChernClassCocycle q L γ → IsEtaleFirstChernClassCocycle q L γ' →
    (∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 1 (by simp) U x = ev γ'.1 1 1 (by simp) U x) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev γ.1 2 0 (by simp) U x = ev γ'.1 2 0 (by simp) U x

def EtaleKummerChernCocycleExists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ γ, IsEtaleFirstChernClassCocycle q L γ

theorem etale_kummer_chern_cocycle_eq_of_evaluation_uniqueness (hU : EtaleKummerChernCocycleEvaluationsUnique) (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hq : Inv q E)
    (γ γ' : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (h : IsEtaleFirstChernClassCocycle q L γ) (h' : IsEtaleFirstChernClassCocycle q L γ') :
    γ = γ' := by
  obtain ⟨h1, h2⟩ := hU q L hq γ γ' h h'
  apply Subtype.ext
  apply cochain_ext_ev
  intro p s hs U x
  rcases p with _ | _ | _ | p
  · obtain rfl : s = 2 := by omega
    rw [h.1 U x, h'.1 U x]
  · obtain rfl : s = 1 := by omega
    exact h1 U x
  · obtain rfl : s = 0 := by omega
    exact h2 U x
  · unfold ev
    rw [(res_isZero (tw q 1) s (by omega)).eq_of_tgt ((chainsXIso _ E _).inv ≫ γ.1.v _ _ hs)
      ((chainsXIso _ E _).inv ≫ γ'.1.v _ _ hs)]

theorem etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique (hE : EtaleKummerChernCocycleExists) (hU : EtaleKummerChernCocycleEvaluationsUnique) : EtaleFirstChernClassRepresentedByChernCocycle := by
  intro q _ E L hq
  obtain ⟨γ0, h0⟩ := hE q L hq
  refine ⟨⟨γ0, h0⟩, fun γ hγ => ?_⟩
  have hex : ∃ c : Ht q E 2 1, ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c ∧ IsEtaleFirstChernClassCocycle q L γ :=
    ⟨_, γ0, rfl, h0⟩
  obtain ⟨γ1, hc, h1⟩ := pick_spec hex
  have : γ1 = γ := etale_kummer_chern_cocycle_eq_of_evaluation_uniqueness hU q L hq γ1 γ h1 hγ
  subst this
  exact hc.symm

end LateralTheory.E.ChernCocycleExistenceAndUniqueness
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassRootLocalization

open LateralTheory.E.CupProductRingLaws LateralTheory.E.ChernCocycleExistenceAndUniqueness

theorem sec_sep {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b := by
  obtain ⟨S, hS, hab⟩ := h
  have hF := ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF S hS).isSeparatedFor.ext (fun V g hg => hab V g hg)

variable {R : Type} [CommRing R] in
theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    freeGen R P V (P.map g.op x) = Sec.res g (freeGen R P U x) := by
  have key := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology ((freeP R).obj P)) g.op
    (ModuleCat.freeMk (R := ULift.{1} R) (show uliftFunctor.{1, 0}.obj (P.obj (op U)) from ULift.up x))
  refine Eq.trans ?_ key
  unfold freeGen
  congr 1
  simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.comp_map]
  erw [ModuleCat.free_map_apply]
  rfl

variable {R : Type} [CommRing R] in
theorem ev_res {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) : ev α p s h V (x.res g) = Sec.res g (ev α p s h U x) := by
  unfold ev Sx.res
  rw [freeGen_res]
  exact NatTrans.naturality_apply (((chainsXIso R E p).inv ≫ α.v _ _ h).hom) g.op _

def LeafRootLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
  Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

theorem evUnique_of (hr : LeafRootLoc) : EtaleKummerChernCocycleEvaluationsUnique := by
  intro q _ E L hq γ γ' h h'
  constructor
  · intro U x
    apply sec_sep
    refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U x) fun V g hv => ?_
    obtain ⟨v, hv⟩ := hv
    rw [← ev_res, ← ev_res, h.2.1 V _ v hv, h'.2.1 V _ v hv]
  · intro U x
    apply sec_sep
    refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_and (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U (x.sub 0 1 (by omega)))
      (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U (x.sub 1 1 (by omega)))) fun V g hv => ?_
    obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hv
    rw [← LateralTheory.EtaleFoundations.FirstChernUniqueness.sub_res] at hv hw
    rw [← ev_res, ← ev_res, h.2.2 V _ v w hv hw, h'.2.2 V _ v w hv hw]

theorem etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique (hE : EtaleKummerChernCocycleExists) (hr : LeafRootLoc) : EtaleFirstChernClassRepresentedByChernCocycle :=
  LateralTheory.E.ChernCocycleExistenceAndUniqueness.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique hE (evUnique_of hr)

end LateralTheory.E.ChernClassRootLocalization
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChernClassExistence
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassExistence

def LeafEvMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def LeafEvDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

def EtaleKummerChernEdgeValuesExistNatural : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      a U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def EtaleKummerChernTriangleValuesExistNatural : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      a U x = kumT q U v + kumT q U w - kumT q U (v * w)

def EtaleKummerChernCochainCoboundaryVanishesOnEdges : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev (δ 2 3 α) 1 2 (by simp) U x = 0

def EtaleKummerChernCochainCoboundaryVanishesOnTriangles : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev (δ 2 3 α) 2 1 (by simp) U x = 0

def EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 3 U), ev (δ 2 3 α) 3 0 (by simp) U x = 0

theorem cx_ext_pf : LateralTheory.EtaleFoundations.cx_ext := by
  intro R _ E I n α h
  apply LateralTheory.E.ChernCocycleExistenceAndUniqueness.cochain_ext_ev α 0
  intro p s hs U x
  rw [h]
  simp [ev]

theorem res_neg_pf : LateralTheory.EtaleFoundations.res_neg := by
  intro q s hs U a
  exact LateralTheory.EtaleFoundations.FirstChernUniqueness.sec_sub (LateralTheory.EtaleFoundations.FirstChernUniqueness.res_zero_neg q s hs) U a 0

theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : LeafEvMk) (hd : LeafEvDelta) (h1 : EtaleKummerChernEdgeValuesExistNatural) (h2 : EtaleKummerChernTriangleValuesExistNatural)
    (c1 : EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) : LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists := by
  intro q _ E L hi
  exact LateralTheory.EtaleFoundations.exists_closed_etale_kummer_chern_class_cochain_of_values hmk h1 h2 (LateralTheory.EtaleFoundations.etale_first_chern_cochain_closed_of_components hd cx_ext_pf res_neg_pf c1 c2 c3) q L hi

end LateralTheory.E.ChernClassExistence
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChernClassEvaluation
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.E.ChernClassEvaluation

variable {R : Type} [CommRing R]

theorem chains_d (E : Spc) (p : ℕ) :
    ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  refine (HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl).trans ?_
  unfold chainsXIso
  congr 2
  simp [chainsN]

theorem freeGen_nat {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map f).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  unfold freeGen
  change ((((toSheafify _ ((freeP R).obj P)) ≫ sheafifyMap _ ((freeP R).map f)).app (op U)).hom _) = _
  rw [← toSheafify_naturality, NatTrans.comp_app, ModuleCat.hom_comp]
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y)
    (by erw [ModuleCat.free_map_apply]; rfl)

def evH {A B : Shv R} (U : Scheme.{0}) (y : Sec A U) : (A ⟶ B) →+ Sec B U where
  toFun f := (f.hom.app (op U)).hom y
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evH_apply {A B : Shv R} (U : Scheme.{0}) (y : Sec A U) (f : A ⟶ B) :
    (f.hom.app (op U)).hom y = evH U y f := rfl

theorem evDelta_pf : ChernClassExistence.LeafEvDelta := by
  intro R _ E I n m hm α U
  constructor
  · intro x
    unfold ev
    rw [δ_v n m hm α (-((0 : ℕ) : ℤ)) m (by simp) n 1 (by omega) (by simp)]
    have hz : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0 :=
      (HomologicalComplex.isZero_extend_X _ _ 1 (fun i => by show -(i : ℤ) ≠ 1; omega)).eq_of_tgt _ _
    rw [hz]
    simp [Sec.map]
  · intro p s t hs ht x
    unfold ev
    rw [δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by push_cast; omega), chains_d]
    simp only [Preadditive.comp_add, Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]
    simp [Sec.map, Units.smul_def, Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul, freeGen_nat, Sx.face]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [evH_apply, map_zsmul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← evH_apply]
    simp [freeGen_nat]

theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : ChernClassExistence.LeafEvMk) (h1 : ChernClassExistence.EtaleKummerChernEdgeValuesExistNatural) (h2 : ChernClassExistence.EtaleKummerChernTriangleValuesExistNatural)
    (c1 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) :
    LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists :=
  ChernClassExistence.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness hmk evDelta_pf h1 h2 c1 c2 c3

end LateralTheory.E.ChernClassEvaluation
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChernClassValueFirst
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor

theorem kumT_ex_of (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists := by
  intro q _
  unfold kumT
  exact pick_spec (hk q)

theorem prim_loc_of (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally :=
  LateralTheory.EtaleFoundations.etale_locally_roots_of_unity_structure_of_exists_and_kummer LateralTheory.EtaleFoundations.etale_locally_exists_primitive_root_of_unity_of_invertible_order hr

theorem etale_kummer_chern_edge_values_exist_of_local_roots_and_kummer_torsor (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) :
    LateralTheory.E.ChernClassExistence.EtaleKummerChernEdgeValuesExistNatural :=
  LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_one_value_of_roots_kummer_gluing (prim_loc_of hr) (kumT_ex_of hk) LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf

end LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleFirst
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleEdgeCoboundary


open LateralTheory.E.ChernClassRootLocalization in
theorem sec_dd (q : ℕ) {V : Scheme.{0}} (y : Sec ((res _ (tw q 1)).X 0) V) :
    Sec.map ((res _ (tw q 1)).d 1 2) (Sec.map ((res _ (tw q 1)).d 0 1) y) = 0 := by
  have h : (res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2 = 0 := HomologicalComplex.d_comp_d _ _ _ _
  change ((((res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2).hom.app (op V)).hom y) = 0
  rw [h]
  rfl

theorem etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges := by
  intro q _ E L hi α hα U x
  have key : ∀ (V : Scheme.{0}) (x' : Sx E 1 V), ev (δ 2 3 α) 1 2 (by simp) V x' =
      Sec.map ((res _ (tw q 1)).d 1 2) (ev α 1 1 (by simp) V x') := by
    intro V x'
    have := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (I := res _ (tw q 1)) (n := 2) (m := 3) (by norm_num) α V).2
      0 1 2 (by simp) (by simp) x'
    rw [this]
    simp [hα.1]
  apply LateralTheory.E.ChernClassRootLocalization.sec_sep
  refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U x) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  rw [← LateralTheory.E.ChernClassRootLocalization.ev_res, key, hα.2.1 V _ v hv, sec_dd]
  exact (map_zero ((res _ (tw q 1)).X 2 |>.obj.map g.op).hom).symm

end LateralTheory.E.ChernCocycleEdgeCoboundary
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleThird
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleFaceDegeneracyIdentities

theorem pull_pull {E : Spc} {U : Scheme.{0}} {a b c : ℕ} (f : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (g : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (x : Sx E c U) :
    (E.map f.op).app (op U) ((E.map g.op).app (op U) x) = (E.map (f ≫ g).op).app (op U) x := by
  rw [op_comp, E.map_comp]; rfl

theorem pull_congr {E : Spc} {U : Scheme.{0}} {a b : ℕ} {f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b}
    (h : f = g) (x : Sx E b U) : (E.map f.op).app (op U) x = (E.map g.op).app (op U) x := by rw [h]

theorem f0s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 0).sub 0 1 (by omega) = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem L_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (y : Sx E n U) : (L.app (op (SimplexCategory.mk m))).app (op U) ((E.map f.op).app (op U) y) =
      ((ofCat (glCat 1)).map f.op).app (op U) ((L.app (op (SimplexCategory.mk n))).app (op U) y) := by
  have h := L.naturality f.op
  have h2 := NatTrans.congr_app h (op U)
  first
  | exact (by simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom h2 y)
  | exact (by simpa only [NatTrans.comp_app, types_comp_apply] using congr_fun h2 y)

theorem line_mul {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (y : Sx E 2 U) :
    lineUnit L (y.face 1) = lineUnit L (y.sub 0 1 (by omega)) * lineUnit L (y.sub 1 1 (by omega)) := by
  unfold lineUnit Sx.face Sx.sub SimplicialObject.δ
  rw [L_nat, L_nat, L_nat]
  generalize (L.app (op (SimplexCategory.mk 2))).app (op U) y = z
  let z' : ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 := z
  change Matrix.GeneralLinearGroup.det (z'.map' 0 2) = Matrix.GeneralLinearGroup.det (z'.map' 0 1) * Matrix.GeneralLinearGroup.det (z'.map' 1 2)
  rw [z'.map'_comp 0 1 2, SingleObj.comp_as_mul, map_mul, mul_comm]

theorem f0s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 0).sub 1 1 (by omega) = x.sub 2 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f1s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 1).sub 1 1 (by omega) = x.sub 2 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f1s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 1).sub 0 1 (by omega) = (x.face 3).face 1 := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull, pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f2s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 2).sub 0 1 (by omega) = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f2s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 2).sub 1 1 (by omega) = (x.face 0).face 1 := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull, pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f3s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 3).sub 0 1 (by omega) = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f3s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 3).sub 1 1 (by omega) = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem local_zero (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1))
    (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (hC : LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α) {V : Scheme.{0}}
    (x : Sx E 3 V) (a b c : (Γ(V, ⊤))ˣ) (ha : a ^ q = lineUnit L (x.sub 0 1 (by omega)))
    (hb : b ^ q = lineUnit L (x.sub 1 1 (by omega))) (hc : c ^ q = lineUnit L (x.sub 2 1 (by omega))) :
    ev (δ 2 3 α) 3 0 (by simp) V x = 0 := by
  have hd := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (I := res _ (tw q 1)) (n := 2) (m := 3) (by norm_num) α V).2
    2 (-1) 0 (by norm_num) (by norm_num) x
  refine hd.trans ?_
  have h0 : ev α 3 (-1) (by norm_num) V x = 0 :=
    LateralTheory.EtaleFoundations.FirstChernUniqueness.sec_sub (LateralTheory.EtaleFoundations.FirstChernUniqueness.res_zero_neg q (-1) (by norm_num)) V _ _
  have v0 := hC.2.2 V (x.face 0) b c (by rw [f0s0]; exact hb) (by rw [f0s1]; exact hc)
  have v1 := hC.2.2 V (x.face 1) (a * b) c (by rw [f1s0, line_mul, f3s0, f3s1, mul_pow, ha, hb]) (by rw [f1s1]; exact hc)
  have v2 := hC.2.2 V (x.face 2) a (b * c) (by rw [f2s0]; exact ha) (by rw [f2s1, line_mul, f0s0, f0s1, mul_pow, hb, hc])
  have v3 := hC.2.2 V (x.face 3) a b (by rw [f3s0]; exact ha) (by rw [f3s1]; exact hb)
  rw [Fin.sum_univ_four]
  erw [h0, v0, v1, v2, v3]
  rw [mul_assoc]
  simp only [Sec.map, map_zero, zero_add]
  convert smul_zero (Int.negOnePow 3) using 2
  simp
  abel


open LateralTheory.EtaleFoundations.FirstChernUniqueness in
theorem etale_kummer_chern_cochain_coboundary_vanishes_on_tetrahedra_of_root_localization (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra := by
  intro q _ E L hi α hC U x
  apply LateralTheory.E.ChernClassRootLocalization.sec_sep
  refine loc_imp (loc_and (root_line hr q L hi U (x.sub 0 1 (by omega)))
    (loc_and (root_line hr q L hi U (x.sub 1 1 (by omega))) (root_line hr q L hi U (x.sub 2 1 (by omega)))))
    fun V g hv => ?_
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := hv
  rw [← sub_res] at ha hb hc
  rw [← LateralTheory.E.ChernClassRootLocalization.ev_res, local_zero q L α hC (x.res g) a b c ha hb hc]
  simp [Sec.res]

end LateralTheory.E.ChernCocycleFaceDegeneracyIdentities
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChernClassValueSecond
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor

theorem etale_kummer_chern_triangle_values_exist_of_local_roots_and_kummer_tor (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) :
    LateralTheory.E.ChernClassExistence.EtaleKummerChernTriangleValuesExistNatural :=
  LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_two_value_of_roots_kummer_gluing (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.prim_loc_of hr) (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.kumT_ex_of hk)
    LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf

end LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleSecond
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleFaceFormulas

lemma δ0_eq : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 1 1 (by omega) := by
  ext i; fin_cases i <;> rfl

lemma δ2_eq : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 0 1 (by omega) := by
  ext i; fin_cases i <;> rfl

lemma face0 {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ; rw [δ0_eq]

lemma face2 {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ; rw [δ2_eq]

lemma glMat_face1 {U : Scheme.{0}} (y : Sx (ofCat (glCat 1)) 2 U) :
    glMat (y.face 1) = glMat (y.sub 1 1 (by omega)) * glMat (y.sub 0 1 (by omega)) := by
  let z : ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 := y
  have h1 : glMat (y.face 1) = z.map' 0 2 := rfl
  have h2 : glMat (y.sub 1 1 (by omega)) = z.map' 1 2 := rfl
  have h3 : glMat (y.sub 0 1 (by omega)) = z.map' 0 1 := rfl
  rw [h1, h2, h3, ← SingleObj.comp_as_mul, ← z.map'_comp 0 1 2]

lemma L_map {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} {m n : ℕ}
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx E n U) :
    (L.app (op (SimplexCategory.mk m))).app (op U) ((E.map θ.op).app (op U) x) =
      ((ofCat (glCat 1)).map θ.op).app (op U) ((L.app (op (SimplexCategory.mk n))).app (op U) x) :=
  congrArg (fun φ => φ.app (op U) x) (L.naturality θ.op)

lemma lineUnit_face1 {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) :
    lineUnit L (x.face 1) = lineUnit L (x.sub 0 1 (by omega)) * lineUnit L (x.sub 1 1 (by omega)) := by
  have key := glMat_face1 ((L.app (op (SimplexCategory.mk 2))).app (op U) x)
  unfold lineUnit
  unfold Sx.face Sx.sub SimplicialObject.δ at *
  rw [L_map, L_map, L_map, key, map_mul, mul_comm]

open LateralTheory.E.ChernClassRootLocalization in
lemma etale_kummer_chern_cochain_coboundary_triangle_eq_zero_of_qth_roots (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1))
    (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (hα : LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α)
    (V : Scheme.{0}) (y : Sx E 2 V) (v w : (Γ(V, ⊤))ˣ) (hv : v ^ q = lineUnit L (y.sub 0 1 (by omega)))
    (hw : w ^ q = lineUnit L (y.sub 1 1 (by omega))) : ev (δ 2 3 α) 2 1 (by simp) V y = 0 := by
  have hd := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (show (2:ℤ) + 1 = 3 by norm_num) α V).2 1 0 1
    (by norm_num) (by norm_num) y
  have e0 : ev α 1 1 (by omega) V (y.face 0) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w) :=
    hα.2.1 V _ w (by rw [face0]; exact hw)
  have e2 : ev α 1 1 (by omega) V (y.face 2) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V v) :=
    hα.2.1 V _ v (by rw [face2]; exact hv)
  have e1 : ev α 1 1 (by omega) V (y.face 1) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V (v * w)) :=
    hα.2.1 V _ (v * w) (by rw [lineUnit_face1, mul_pow, hv, hw])
  have e3 := hα.2.2 V y v w hv hw
  refine hd.trans ?_
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_zero]
  have e3' : ev α (1 + 1) 0 (by omega) V y = kumT q V v + kumT q V w - kumT q V (v * w) := e3
  have hn : (3 : ℤ).negOnePow = -1 := by rw [Int.negOnePow_odd]; decide
  rw [e3', e0, e1, e2, hn]
  simp only [Sec.map, map_add (f := _), map_sub]
  simp
  abel

open LateralTheory.E.ChernClassRootLocalization in
theorem etale_kummer_chern_cochain_coboundary_vanishes_on_triangles_of_local_r (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTriangles := by
  intro q _ E L hi α hα U x
  apply sec_sep
  refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_and
    (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U (x.sub 0 1 (by omega)))
    (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U (x.sub 1 1 (by omega)))) fun V g hvw => ?_
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hvw
  rw [← LateralTheory.EtaleFoundations.FirstChernUniqueness.sub_res] at hv hw
  rw [← ev_res]
  exact (etale_kummer_chern_cochain_coboundary_triangle_eq_zero_of_qth_roots q L α hα V _ v w hv hw).trans (map_zero ((_ : Sec _ U →ₗ[_] Sec _ V))).symm

end LateralTheory.E.ChernCocycleFaceFormulas
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafEvMkPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafEvMkPf

variable {R : Type} [CommRing R]

def preLift {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.ofHom (Finsupp.lift (F.obj.obj U) (ULift.{1} R) (ULift.{1} (P.obj U)) (fun y => a U.unop y.down))
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro y'
    obtain ⟨y⟩ := y'
    have := ha V.unop U.unop g.unop y
    simp only [Sec.res, Quiver.Hom.op_unop, op_unop] at this
    dsimp [freeP]
    change (Finsupp.lift (F.obj.obj V) (ULift.{1} R) (ULift.{1} (P.obj V)) (fun y => a V.unop y.down))
        (Finsupp.mapDomain (fun x : ULift.{1} (P.obj U) => ULift.up (P.map g x.down)) (Finsupp.single (ULift.up y) 1)) =
      F.obj.map g ((Finsupp.lift (F.obj.obj U) (ULift.{1} R) (ULift.{1} (P.obj U)) (fun y => a U.unop y.down)) (Finsupp.single (ULift.up y) 1))
    rw [Finsupp.mapDomain_single, Finsupp.lift_apply, Finsupp.lift_apply, Finsupp.sum_single_index, Finsupp.sum_single_index]
    · simpa using this.symm
    all_goals simp

theorem preLift_app {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U) (ha) (U : Scheme.{0})
    (x : P.obj (op U)) : ((preLift a ha).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = a U x := by
  show (Finsupp.lift (F.obj.obj (op U)) (ULift.{1} R) (ULift.{1} (P.obj (op U))) (fun y => a U y.down)) (Finsupp.single (ULift.up x) 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

def shLift {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (free R).obj P ⟶ F :=
  ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology (preLift a ha) F.property)

theorem shLift_gen {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U) (ha) (U : Scheme.{0})
    (x : P.obj (op U)) : ((shLift a ha).hom.app (op U)).hom (freeGen R P U x) = a U x := by
  unfold freeGen
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyLift Scheme.etaleTopology (preLift a ha) F.property).app (op U)).hom _ = _
  rw [toSheafify_sheafifyLift]
  exact preLift_app a ha U x

variable {E : Spc} {I : Cx R} {n : ℤ}

def comp (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : ((chains R).obj E).X (-(p : ℤ)) ⟶ I.X s :=
  (chainsXIso R E p).hom ≫ shLift (P := E.obj (op (SimplexCategory.mk p))) (a p s h) (fun V U g x => ha p s h V U g x)

theorem comp_key (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p q : ℕ) (hq : q = p) (s : ℤ) (h : -(p : ℤ) + n = s) (h' : -(q : ℤ) + n = s)
    (e : ((chains R).obj E).X (-(p : ℤ)) = ((chains R).obj E).X (-(q : ℤ))) :
    (chainsXIso R E p).inv ≫ eqToHom e ≫ comp a ha q s h' =
      shLift (P := E.obj (op (SimplexCategory.mk p))) (a p s h) (fun V U g x => ha p s h V U g x) := by
  subst hq
  simp [comp]

theorem LeafEvMk_of : LateralTheory.E.ChernClassExistence.LeafEvMk := by
  intro R _ E I n a ha
  refine ⟨Cochain.mk fun i j hij => if hi : i ≤ 0 then
      eqToHom (congrArg (fun k => ((chains R).obj E).X k) (by omega : i = -(((-i).toNat : ℕ) : ℤ))) ≫
        comp a ha ((-i).toNat) j (by omega) else 0, ?_⟩
  intro p s h U x
  unfold ev
  rw [Cochain.mk_v, dite_eq_left (by omega), comp_key a ha p _ (by omega) s h]
  exact shLift_gen _ _ U x

end LateralTheory.E.LeafEvMkPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafRootLocPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LeafRootLocPf

def kpair {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : A) : StandardEtalePair A where
  f := X ^ q - C u
  monic_f := monic_X_pow_sub_C _ (NeZero.ne q)
  g := X
  cond := ⟨C c * X, 0, q, by
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    subst hk
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero, Nat.add_sub_cancel]
    rw [show (C (((k + 1 : ℕ) : A)) * X ^ k) * (C c * X) = C (c * ((k + 1 : ℕ) : A)) * X ^ (k + 1) by
      rw [C_mul, pow_succ]; ring]
    rw [hc, C_1, one_mul]⟩

theorem kpair_root {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : A) :
    (kpair q c hc u).X ^ q = algebraMap A (kpair q c hc u).Ring u := by
  have h : aeval (kpair q c hc u).X (X ^ q - C u) = 0 := (kpair q c hc u).hasMap_X.1
  rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

theorem kpair_surj {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : Aˣ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (kpair q c hc (u : A)).Ring)) := by
  intro p
  let K := p.asIdeal.ResidueField
  let Ω := AlgebraicClosure K
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω u) (Nat.pos_of_ne_zero (NeZero.ne q))
  have hu : IsUnit (algebraMap A Ω u) := u.isUnit.map _
  have hzu : IsUnit z := by
    rw [← hz] at hu; exact (isUnit_pow_iff (NeZero.ne q)).mp hu
  have hm : (kpair q c hc (u : A)).HasMap z := by
    refine ⟨?_, ?_⟩
    · simp [kpair, hz]
    · simpa [kpair] using hzu
  let ψ := (kpair q c hc (u : A)).lift z hm
  refine ⟨⟨RingHom.ker ψ.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
  ext1
  change Ideal.comap _ (RingHom.ker ψ.toRingHom) = p.asIdeal
  rw [RingHom.comap_ker, show ψ.toRingHom.comp (algebraMap A _) = algebraMap A Ω from ψ.comp_algebraMap]
  rw [IsScalarTower.algebraMap_eq A K Ω, ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap K Ω).injective, ← RingHom.ker_eq_comap_bot,
    Ideal.ker_algebraMap_residueField]

theorem loc_of_cover {U Y : Scheme.{0}} (π : Y ⟶ U) [Etale π] [Surjective π]
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : ∀ (V : Scheme.{0}) (h : V ⟶ Y), P V (h ≫ π)) : Loc U P := by
  let 𝒰 : U.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers PUnit.{1} (fun _ => Y) (fun _ => π)
      (fun x => ⟨PUnit.unit, π.surjective x⟩) inferInstance
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.Cover.mem_grothendieckTopology 𝒰, ?_⟩
  intro V g hg
  obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  exact hP V h

theorem LeafRootLoc_of : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc := by
  intro q _ U hq u
  obtain ⟨c, hc⟩ := hq.exists_left_inv
  let P := kpair q c hc (u : Γ(U, ⊤))
  let B : CommRingCat.{0} := CommRingCat.of P.Ring
  let φ : Γ(U, ⊤) ⟶ B := CommRingCat.ofHom (algebraMap _ P.Ring)
  have : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have : Surjective (Spec.map φ) := ⟨kpair_surj q c hc u⟩
  refine loc_of_cover (pullback.fst U.toSpecΓ (Spec.map φ)) _ fun V h => ?_
  have hX : IsUnit P.X := (isUnit_pow_iff (NeZero.ne q)).mp (by rw [kpair_root]; exact u.isUnit.map _)
  have e : (h ≫ pullback.snd _ _) ≫ Spec.map φ = (h ≫ pullback.fst _ _) ≫ U.toSpecΓ := by
    simp [pullback.condition]
  have hcomp : φ ≫ (Scheme.ΓSpecIso B).inv ≫ (h ≫ pullback.snd _ _).appTop = (h ≫ pullback.fst _ _).appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop, e,
      Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨Units.map ((h ≫ pullback.snd _ _).appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom).toMonoidHom hX.unit, ?_⟩
  ext
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  rw [← map_pow, kpair_root]
  exact congrArg (fun f => f.hom (u : Γ(U, ⊤))) hcomp

end LateralTheory.E.LeafRootLocPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafNatCupPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNatCupPf

section

variable {R : Type} [CommRing R]

theorem chainsXIso_inv_map {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  rw [ComplexShape.embeddingDownNat.extendFunctor_map (C := Shv R)]
  erw [HomologicalComplex.extendMap_f _ _ (i := p) (i' := -(p : ℤ)) rfl]
  simp only [chainsN]
  erw [Iso.inv_hom_id_assoc]
  simp
  rfl

theorem free_map_freeGen {P Q : PSh} (g : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  have h2 : (((freeP R).map g).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (g.app (op U) x)) :=
    ModuleCat.free_map_apply (R := ULift.{1} R) _ _
  exact h.symm.trans (congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom h2)

theorem ev_pull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  simp only [ev]
  rw [Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (add_zero _) h, Cochain.ofHom_v,
    ← Category.assoc, chainsXIso_inv_map, Category.assoc]
  rw [← free_map_freeGen]
  rfl

theorem sub_pull {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (f.app (op (SimplexCategory.mk l))).app (op U) (x.sub j l h) =
      Sx.sub (E := E') (N := N) ((f.app (op (SimplexCategory.mk N))).app (op U) x) j l h := by
  have := ConcreteCategory.congr_hom (congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x
  simp only [Sx.sub]
  exact this

theorem isAW_pull {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E') I n) (β : Cochain ((chains R).obj E') J m) (γ : Cochain ((chains R).obj E') K k)
    (hγ : μ.IsAW hk α β γ) :
    μ.IsAW hk ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp β (zero_add m))
      ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add k)) := by
  intro N w h U x
  rw [ev_pull, hγ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_pull, ev_pull, sub_pull, sub_pull]

theorem pull_mk {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (z : Cocycle ((chains R).obj E') (res R F) n) :
    pull R f F n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) :=
  rfl

theorem zcomp_ofHom_val {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (z : Cocycle ((chains R).obj E') I n) :
    (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)).1 = (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add n) :=
  rfl

end

open CupProductRingLaws in
theorem LeafNatCup_of (hc : LeafCupSpec) : LeafNatCup := by
  intro q _ E E' f n m i j a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (hc (ZMod q) (twPair q i j) E' rfl).1 α β
  have e1 : cup q (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
    (hc (ZMod q) (twPair q i j) E' rfl).2 α β γ hγ
  have hAW := isAW_pull (twPair q i j) f rfl α.1 β.1 γ.1 hγ
  rw [← zcomp_ofHom_val, ← zcomp_ofHom_val, ← zcomp_ofHom_val] at hAW
  have e2 := (hc (ZMod q) (twPair q i j) E rfl).2 _ _ _ hAW
  rw [e1, pull_mk, pull_mk, pull_mk]
  exact e2.symm

end LateralTheory.E.LeafNatCupPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafNatOnePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNatOnePf

variable {R : Type} [CommRing R]

theorem free_map_freeGen {P Q : PSh} (g : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp] at h
  unfold freeGen
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y) ?_)
  exact ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (g.app (op U))) (ULift.up.{1} x)

theorem chainsXIso_nat {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  unfold chainsXIso chains
  rw [Functor.comp_map, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ _ (i := p) (i' := -(p : ℤ)) rfl]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem ev_pull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  unfold ev
  rw [Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (by omega) (by omega), Cochain.ofHom_v,
    ← Category.assoc, chainsXIso_nat, Category.assoc]
  rw [← free_map_freeGen]
  rfl

theorem LeafNatOne_of (hOne : LateralTheory.E.CupProductRingLaws.LeafOneSpec) : LateralTheory.E.CupProductRingLaws.LeafNatOne := by
  intro q _ E E' f hE'
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨(f.app (op (SimplexCategory.mk 0))).app (op U) x⟩
  obtain ⟨⟨α, hα⟩, h'⟩ := hOne q E' hE'
  rw [h' α hα]
  let β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0 :=
    zcomp (Cocycle.ofHom ((chains (ZMod q)).map f)) α (zero_add 0)
  have hβ : LateralTheory.E.CupProductRingLaws.IsOneCocycle q E β := fun U x ζ => by
    rw [← hα U ((f.app (op (SimplexCategory.mk 0))).app (op U) x) ζ]
    exact ev_pull f α.1 0 0 _ U x
  rw [(hOne q E hE).2 β hβ]
  rfl

end LateralTheory.E.LeafNatOnePf
end
end

namespace LateralTheory.E.LeafA6nat_xy7V2Cut

theorem kumTExists : LateralTheory.E.CupProductRingLaws.LeafKumTExists := fun q _ =>
  ⟨_, LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange q⟩

theorem oneSpec : LateralTheory.E.CupProductRingLaws.LeafOneSpec :=
  LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of
    (LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit LateralTheory.E.UnitSections.LeafUnitSec_of)
    LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of

theorem etaleFirstChernClass_represented_by_chern_cocycle : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle :=
  have hr := LateralTheory.E.LeafRootLocPf.LeafRootLoc_of
  LateralTheory.E.ChernClassRootLocalization.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique
    (LateralTheory.E.ChernClassEvaluation.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness LateralTheory.E.LeafEvMkPf.LeafEvMk_of
      (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.etale_kummer_chern_edge_values_exist_of_local_roots_and_kummer_torsor hr kumTExists) (LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor.etale_kummer_chern_triangle_values_exist_of_local_roots_and_kummer_tor hr kumTExists)
      (LateralTheory.E.ChernCocycleEdgeCoboundary.etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots hr) (LateralTheory.E.ChernCocycleFaceFormulas.etale_kummer_chern_cochain_coboundary_vanishes_on_triangles_of_local_r hr) (LateralTheory.E.ChernCocycleFaceDegeneracyIdentities.etale_kummer_chern_cochain_coboundary_vanishes_on_tetrahedra_of_root_localization hr))
    hr

theorem natKum : LateralTheory.E.CupProductRingLaws.LeafNatKum := fun q _ =>
  ((LateralTheory.Fix.EtaleKummerClassExplicitCocycle.holds_of LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange) q).2.1

theorem goal_of : LateralTheory.E.D2.LeafA6nat := fun q _ =>
  ⟨LateralTheory.E.LeafNatCupPf.LeafNatCup_of LateralTheory.Fix.CupProductTensor.cupSpec q,
   LateralTheory.E.LeafNatOnePf.LeafNatOne_of oneSpec q,
   LateralTheory.E.FirstChernNaturality.etale_first_chern_class_natural_of_spec etaleFirstChernClass_represented_by_chern_cocycle q,
   natKum q⟩

end LateralTheory.E.LeafA6nat_xy7V2Cut
