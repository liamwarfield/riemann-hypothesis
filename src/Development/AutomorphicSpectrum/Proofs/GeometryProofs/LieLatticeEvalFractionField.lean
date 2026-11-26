module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.EqOfSpecializes
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

section Rings

variable {S : Scheme.{0}} {A B D : Type} [CommRing A] [CommRing B] [CommRing D]

theorem dualMap_comp (f : A →+* B) (g : B →+* D) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem spec_dualMap_comp (f : A →+* B) (g : B →+* D) :
    Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) =
      Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) := by
  rw [dualMap_comp]
  exact Spec.map_comp (CommRingCat.ofHom (dualMap f)) (CommRingCat.ofHom (dualMap g))

theorem isTanAt_epsHom {G : Over S} [GrpObj G] (φ : A →+* B) (x : Spec (CommRingCat.of A) ⟶ S)
    (x' : Spec (CommRingCat.of B) ⟶ S) (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G x' (LieCarrier.epsHom φ x x' h ≫ v) := by
  rw [LieEx.isTanAt_iff] at hv ⊢
  have key : (LieEx.zsec x' : _ ⟶ LieEx.ob x' B) ≫ LieCarrier.epsHom φ x x' h =
      (Over.homMk (Spec.map (CommRingCat.ofHom φ)) h : Over.mk x' ⟶ Over.mk x) ≫ LieEx.zsec x := by
    ext1
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [dualMap, TrivSqZeroExt.fst_add]
  rw [← Category.assoc, key, Category.assoc, hv, MonObj.comp_one]

theorem stalk_hom_ext {X : Scheme.{0}} (c : X) (a b : X.presheaf.stalk c →+* B)
    (h : Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk c = Spec.map (CommRingCat.ofHom b) ≫ X.fromSpecStalk c) :
    a = b := by
  have h1 := (cancel_mono (X.fromSpecStalk c)).1 h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

end Rings

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E] {R : Type} [CommRing R] [IsLocalRing R] {C : Type} [Field C] [Algebra R C]

theorem centre_specializes (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) ⤳ centre z := by
  have h : (Spec.map (CommRingCat.ofHom (algebraMap R C))) (IsLocalRing.closedPoint C) ⤳
      IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint _
  exact h.map z.continuous

theorem valAt_base (M : LieModel G ξ E) (z : Spec (CommRingCat.of R) ⟶ X) {e : E} (hc : genPt ξ ⤳ centre z)
    (hc' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z))
    (v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G)
    (hv : M.Extends ⟨centre z, hc⟩ e v) (t : epsAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) ⟶ G)
    (u : epsAt z ⟶ G) (ht : t.left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ u.left)
    (hu : u.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v.left) :
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e t := by
  set_option maxHeartbeats 0 in
  have hsp := centre_specializes (C := C) z
  have F1 : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes hsp).hom) ≫ X.fromSpecStalk (centre z) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have gen_eq : (genMap ξ ⟨_, hc'⟩).comp (X.presheaf.stalkSpecializes hsp).hom = genMap ξ ⟨_, hc⟩ := by
    apply stalk_hom_ext
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, F1]
    exact (LieCarrier.genMap_fromSpecStalk ⟨_, hc'⟩).trans (LieCarrier.genMap_fromSpecStalk ⟨_, hc⟩).symm
  have s_eq : (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)).hom.comp
      (X.presheaf.stalkSpecializes hsp).hom = (algebraMap R C).comp (Scheme.stalkClosedPointTo z).hom := by
    apply stalk_hom_ext
    have L : Spec.map (X.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo
        (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) ≫ X.fromSpecStalk (centre z) =
        Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z :=
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (Spec.map (Scheme.stalkClosedPointTo _) ≫ ·)
          (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp)).trans
            (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)))
    have Rt : Spec.map (Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom (algebraMap R C)) ≫
        X.fromSpecStalk (centre z) = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z :=
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        (congrArg (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ·)
          (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)))
    exact L.trans Rt.symm
  refine ⟨hc', LieCarrier.epsHom (X.presheaf.stalkSpecializes hsp).hom _ _ F1 ≫ v,
    ⟨isTanAt_epsHom _ _ _ _ _ hv.1, ?_⟩, ?_⟩
  · change (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ ⟨_, hc'⟩))) ≫
      Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes hsp).hom)) ≫ v.left
    have e := spec_dualMap_comp (X.presheaf.stalkSpecializes hsp).hom (genMap ξ ⟨_, hc'⟩)
    rw [gen_eq] at e
    exact hv.2.trans ((congrArg (· ≫ v.left) e).trans (Category.assoc _ _ _))
  · change t.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo _).hom)) ≫
      Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes hsp).hom)) ≫ v.left
    have e1 := spec_dualMap_comp (Scheme.stalkClosedPointTo z).hom (algebraMap R C)
    have e2 := spec_dualMap_comp (X.presheaf.stalkSpecializes hsp).hom
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)).hom
    have e3 := (congrArg (fun f : X.presheaf.stalk (centre z) →+* C => Spec.map (CommRingCat.ofHom (dualMap f)))
      s_eq).symm.trans e2
    exact ht.trans ((congrArg (_ ≫ ·) hu).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ v.left) (e1.symm.trans e3)).trans (Category.assoc _ _ _))))

end GlobalTheory.CompanionTheory.Ar.LieFib

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieLat_fibAt_iff : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (C : Type) [Field C] [Algebra R C] (EC : Type) [AddCommGroup EC] [Module C EC] [Module R EC] [IsScalarTower R C EC] (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC), IsCptGen ξ → Smooth G.hom → genPt ξ ⤳ centre z → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) → ∀ w : EC, w ∈ M.fibAt M.lat z MC ↔ ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ v.left := by
  intro X G _ _ Ω _ ξ E _ _ M R _ _ z C _ _ EC _ _ _ _ MC hξ hG h h' w
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G R z
  obtain ⟨ev, hev, -, hspan⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ E M R z h ER MR hξ hG
  obtain ⟨evC, hevC, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ E M C _ h' EC MC hξ hG
  have hj : ∀ u : ER, ∃ w, MC.pt w = LieCarrier.epsHom (algebraMap R C) z _ rfl ≫ MR.pt u := fun u =>
    MC.onto _ (LieFib.isTanAt_epsHom _ _ _ _ _ (MR.tan u))
  choose j hj using hj
  have hjl : ∀ u, (MC.pt (j u)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ (MR.pt u).left := fun u =>
    congrArg CommaMorphism.left (hj u)
  have hadd : ∀ u u', j (u + u') = j u + j u' := fun u u' => MC.inj (by
    rw [hj, MC.add, hj, hj, MR.add, MonObj.comp_mul])
  have hsmul : ∀ (r : R) u, j (r • u) = r • j u := fun r u => MC.inj (Over.OverMorphism.ext (by
    rw [← algebraMap_smul C r (j u), MC.smul, hjl, hjl, MR.smul]
    have e : Spec.map (CommRingCat.ofHom (epsMul (algebraMap R C r))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) =
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ Spec.map (CommRingCat.ofHom (epsMul r)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        LieCarrier.dualMap_epsMul]
    rw [← Category.assoc, ← e, Category.assoc]))
  let jL : ER →ₗ[R] EC := { toFun := j, map_add' := hadd, map_smul' := hsmul }
  have hgen : ∀ (e : E) (he : e ∈ M.lat ⟨centre z, h⟩),
      M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt (j (ev ⟨e, he⟩))) := by
    intro e he
    obtain ⟨h2, v, hv, hu⟩ := (hev e _).2 ⟨he, rfl⟩
    exact LieFib.valAt_base M z h h' v hv _ _ (hjl _) hu
  constructor
  · intro hw
    have hle : M.fibAt M.lat z MC ≤ LinearMap.range jL := by
      refine Submodule.span_le.2 ?_
      rintro w' ⟨h2, e, he, hval⟩
      obtain ⟨he', hw'⟩ := (hevC e _).1 hval
      obtain ⟨he'', hw''⟩ := (hevC e _).1 (hgen e he)
      exact ⟨ev ⟨e, he⟩, hw''.symm.trans hw'⟩
    obtain ⟨u, rfl⟩ := hle hw
    exact ⟨MR.pt u, MR.tan u, hjl u⟩
  · rintro ⟨v, hv, hw⟩
    obtain ⟨u, rfl⟩ := MR.onto v hv
    have hwu : w = j u := MC.inj (Over.OverMorphism.ext (hw.trans (hjl u).symm))
    subst hwu
    have hu : u ∈ Submodule.span R (Set.range ev) := hspan ▸ Submodule.mem_top
    have hle : (Submodule.span R (Set.range ev)).map jL ≤ M.fibAt M.lat z MC := by
      rw [Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨⟨e, he⟩, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨h, e, he, hgen e he⟩
    exact hle (Submodule.mem_map_of_mem hu)

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_eval_fraction_field : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (C : Type) [Field C] [Algebra R C] (EC : Type) [AddCommGroup EC] [Module C EC] [Module R EC] [IsScalarTower R C EC] (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC), IsCptGen ξ → Smooth G.hom → genPt ξ ⤳ centre z → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) → ∀ w : EC, w ∈ M.fibAt M.lat z MC ↔ ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ v.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff | exact GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.LieFun

open GlobalTheory.CompanionTheory.Ar.LieTangent

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
  {E : Type} [AddCommGroup E] [Module Ω E]

def Stalk (M : LieModel G ξ E) (p : Cpt ξ) : Type := M.lat p

instance (M : LieModel G ξ E) (p : Cpt ξ) : AddCommGroup (Stalk M p) :=
  inferInstanceAs (AddCommGroup (M.lat p))

instance Stalk.module (M : LieModel G ξ E) (p : Cpt ξ) : Module (X.presheaf.stalk p.1) (Stalk M p) :=
  Module.compHom (M.lat p) (genMap ξ p).rangeRestrict

def Stalk.val {M : LieModel G ξ E} {p : Cpt ξ} (e : Stalk M p) : E := Subtype.val (p := (· ∈ M.lat p)) e

theorem Stalk.mem {M : LieModel G ξ E} {p : Cpt ξ} (e : Stalk M p) : e.val ∈ M.lat p := Subtype.property e

theorem Stalk.ext {M : LieModel G ξ E} {p : Cpt ξ} {e e' : Stalk M p} (h : e.val = e'.val) : e = e' :=
  Subtype.ext h

def Stalk.tan {M : LieModel G ξ E} {p : Cpt ξ} (e : Stalk M p) :
    epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G :=
  ((M.mem_lat_iff p e.val).1 e.mem).choose

theorem Stalk.tan_spec {M : LieModel G ξ E} {p : Cpt ξ} (e : Stalk M p) : M.Extends p e.val e.tan :=
  ((M.mem_lat_iff p e.val).1 e.mem).choose_spec

def stalkLie (hξ : IsCptGen ξ) (M : LieModel G ξ E) (p : Cpt ξ) :
    LieModel (R := X.presheaf.stalk p.1) G (X.fromSpecStalk p.1) (Stalk M p) where
  pt e := e.tan
  tan e := e.tan_spec.1
  inj e e' h := by
    refine Stalk.ext (M.inj (Over.OverMorphism.ext ?_))
    rw [e.tan_spec.2, e'.tan_spec.2, show e.tan = e'.tan from h]
  onto v hv := by
    let φ := genMap ξ p
    let d := GlobalTheory.CompanionTheory.Ar.dualMap φ
    have halg : d.comp (algebraMap (X.presheaf.stalk p.1) (DualNumber (X.presheaf.stalk p.1))) =
        (algebraMap Ω (DualNumber Ω)).comp φ := by
      refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
        simp [d, GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    let base : epsAt ξ ⟶ epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) :=
      Over.homMk (Spec.map (CommRingCat.ofHom d)) (by
        change _ ≫ _ ≫ X.fromSpecStalk p.1 = _ ≫ ξ
        rw [← Category.assoc, spec_comp, halg, ← spec_comp, Category.assoc, spec_genMap])
    have ht : IsTanAt G ξ (base ≫ v) := by
      have hfst : (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom.comp d =
          φ.comp (TrivSqZeroExt.fstHom (X.presheaf.stalk p.1) (X.presheaf.stalk p.1)
            (X.presheaf.stalk p.1)).toRingHom := by
        refine RingHom.ext fun a => ?_
        simp [d, GlobalTheory.CompanionTheory.Ar.dualMap]
      change Spec.map _ ≫ Spec.map (CommRingCat.ofHom d) ≫ v.left = _
      rw [← Category.assoc, spec_comp, hfst, ← spec_comp, Category.assoc, hv]
      exact congrArg (·.left) (comp_one (M := G)
        (Over.homMk (Spec.map (CommRingCat.ofHom φ)) (spec_genMap ξ p) :
          Over.mk ξ ⟶ Over.mk (X.fromSpecStalk p.1)))
    obtain ⟨e, he⟩ := M.onto _ ht
    have hx : M.Extends p e v := ⟨hv, congrArg (·.left) he⟩
    let e' : Stalk M p := ⟨e, (M.mem_lat_iff _ _).2 ⟨v, hx⟩⟩
    exact ⟨e', e'.tan_spec.unique (hξ.inj p) hx⟩
  add e e' := (e + e').tan_spec.unique (hξ.inj p) (e.tan_spec.add e'.tan_spec)
  smul c e := congrArg (fun q => q.left) ((c • e).tan_spec.unique (hξ.inj p) (e.tan_spec.smul c))

def castLie {R : Type} [CommRing R] {x y : Sp R ⟶ X} (h : x = y) {F : Type} [AddCommGroup F] [Module R F]
    (M : LieModel G x F) : LieModel G y F := h ▸ M

theorem castLie_left {R : Type} [CommRing R] {x y : Sp R ⟶ X} (h : x = y) {F : Type} [AddCommGroup F]
    [Module R F] (M : LieModel G x F) (e : F) : ((castLie h M).pt e).left = (M.pt e).left := by
  subst h
  rfl

end GlobalTheory.CompanionTheory.Ar.RootHt.LieFun

namespace GlobalTheory.CompanionTheory.Ar.RootHt

open GlobalTheory.CompanionTheory.Ar.RootHt.LieFun GlobalTheory.CompanionTheory.Ar.LieTangent

theorem exists_lieFunctional : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (R : Type) [CommRing R] [IsLocalRing R]
    (z : Sp R ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type) [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER)
    (f : Module.Dual Ω Li), IsCptGen ξ → (∀ e ∈ M.lat ⟨centre z, h⟩, f e ∈ regAt ξ ⟨centre z, h⟩) →
    ∃ g : ER →ₗ[R] R, ∀ (e : Li) (x : ER) (u : R), M.ValAt z e (MR.pt x) → ValAt ξ z (f e) u → g x = u := by
  intro X G _ _ _ Ω _ ξ Li _ _ M R _ _ z h ER _ _ MR f hξ hf
  obtain ⟨ev, hev, hlin, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M R z h ER MR hξ inferInstance
  let ψ : X.presheaf.stalk (centre z) →+* R := (Scheme.stalkClosedPointTo z).hom
  letI : Algebra (X.presheaf.stalk (centre z)) R := ψ.toAlgebra
  letI : Module (X.presheaf.stalk (centre z)) ER := Module.compHom ER ψ
  haveI : IsScalarTower (X.presheaf.stalk (centre z)) R ER :=
    ⟨fun s r x => by
      change (ψ s * r) • x = ψ s • r • x
      rw [mul_smul]⟩
  letI : Module (X.presheaf.stalk (centre z)) (Stalk M ⟨centre z, h⟩) := Stalk.module M ⟨centre z, h⟩
  have hgi : Function.Injective (genMap ξ ⟨centre z, h⟩) := hξ.inj ⟨centre z, h⟩

  let j : Stalk M ⟨centre z, h⟩ →ₗ[X.presheaf.stalk (centre z)] ER :=
    { toFun := fun e => ev ⟨e.val, e.mem⟩
      map_add' := fun e e' => ev.map_add ⟨e.val, e.mem⟩ ⟨e'.val, e'.mem⟩
      map_smul' := fun s e => hlin ⟨genMap ξ ⟨centre z, h⟩ s, s, rfl⟩ (ψ s) ⟨e.val, e.mem⟩ ⟨h, s, rfl, rfl⟩ }
  have hbc : IsBaseChange R j := by
    refine GlobalTheory.T.lie_model_isBaseChange X G (X.presheaf.stalk (centre z)) R (X.fromSpecStalk (centre z)) (Stalk M ⟨centre z, h⟩) ER
      (stalkLie hξ M ⟨centre z, h⟩) (castLie (spec_centre z).symm MR) j fun e => ?_
    obtain ⟨h', v, hv, hw⟩ := (hev e.val (ev ⟨e.val, e.mem⟩)).2 ⟨e.mem, rfl⟩
    have hvv : v = e.tan := hv.unique (hξ.inj _) e.tan_spec
    subst hvv
    show ((castLie (spec_centre z).symm MR).pt (j e)).left ≫ 𝟙 G.left = _
    rw [Category.comp_id, castLie_left]
    exact hw
  have hs : ∀ e : Stalk M ⟨centre z, h⟩, ∃ s, genMap ξ ⟨centre z, h⟩ s = f e.val := fun e => hf e.val e.mem
  choose σ hσ using hs
  let f' : Stalk M ⟨centre z, h⟩ →ₗ[X.presheaf.stalk (centre z)] R :=
    { toFun := fun e => ψ (σ e)
      map_add' := fun e e' => by
        have : σ (e + e') = σ e + σ e' := hgi (by
          simp only [map_add, hσ]
          exact map_add f e.val e'.val)
        rw [this, map_add (f := _)]
      map_smul' := fun s e => by
        have : σ (s • e) = s * σ e := hgi (by
          rw [hσ, map_mul, hσ]
          show f (genMap ξ ⟨centre z, h⟩ s • e.val) = _
          rw [map_smul, smul_eq_mul])
        rw [this, map_mul]
        rfl }
  refine ⟨hbc.lift f', fun e x u hV hU => ?_⟩
  obtain ⟨he, rfl⟩ := (hev e x).1 hV
  obtain ⟨h2, s, hs1, hs2⟩ := hU
  let e' : Stalk M ⟨centre z, h⟩ := ⟨e, he⟩
  have h3 : hbc.lift f' (j e') = f' e' := hbc.lift_eq f' e'
  have h4 : σ e' = s := hgi ((hσ e').trans hs1.symm)
  have h5 : f' e' = ψ (σ e') := rfl
  rw [h4] at h5
  exact (h3.trans h5).trans hs2

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_regular_at_local_point : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (R : Type) [CommRing R] [IsLocalRing R]
    (z : Sp R ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type) [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER)
    (f : Module.Dual Ω Li), IsCptGen ξ → (∀ e ∈ M.lat ⟨centre z, h⟩, f e ∈ regAt ξ ⟨centre z, h⟩) →
    ∃ g : ER →ₗ[R] R, ∀ (e : Li) (x : ER) (u : R), M.ValAt z e (MR.pt x) → ValAt ξ z (f e) u → g x = u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional | exact GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodge
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodge
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LiePullSab

theorem exists_bc {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (x : Spec (CommRingCat.of R) ⟶ S) (y : Spec (CommRingCat.of R') ⟶ S)
    (hy : Spec.map (CommRingCat.ofHom f) ≫ x = y) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E']
    [Module R' E'] (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', ∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap f)) ≫ (M.pt e).left := by
  subst hy
  let _ := f.toAlgebra
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_base_change_map S G R R' x E E' M M'
  exact ⟨j, hj⟩

theorem lie_pull_lat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∃ j : V →+ V', (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) ∧ (∀ (a : Ω) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)) ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ M'.lat = M.lat.pull ξ' f j := by
  intro E _ _ _ H X t X' t' f m Ω Ω' _ _ ξ ξ' i V V' _ _ _ _ M M' hξ hξ' hd
  obtain ⟨j, hj⟩ := exists_bc i ξ (ξ' ≫ f) (Eq.symm hd) M (LieMove.pushModel m.cart M')
  have hj' : ∀ e, (M'.pt (j e)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left := hj
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := GlobalTheory.T.lie_lattice_dominant_compat X X' Ω Ω' ξ ξ' f i t.G t'.G m.φ V V' M M' j hξ hξ' hd m.cart
    t.semi.smooth hj'
  exact ⟨j, hj', h₁, h₂, h₃, h₄⟩

end GlobalTheory.CompanionTheory.Ar.LiePullSab
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodgeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_dominant_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∃ j : V →+ V', (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) ∧ (∀ (a : Ω) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)) ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ M'.lat = M.lat.pull ξ' f j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat | exact GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.GenPtModel

theorem mem_genericPoints_of_eq {X : Scheme.{0}} {x : X}
    (h : ∀ p : X, p ⤳ x → p = x) : x ∈ genericPoints X := by
  show closure {x} ∈ irreducibleComponents X
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, fun T hT hxT => ?_⟩
  obtain ⟨p, hp⟩ := QuasiSober.sober hT.2 hT.1
  have hpx : p = x := h p ((hp.specializes_iff_mem).2 (hxT (subset_closure (Set.mem_singleton x))))
  intro y hy
  rw [← hpx]
  exact specializes_iff_mem_closure.1 ((hp.specializes_iff_mem).2 hy)

theorem genPt_mem_genericPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ∈ genericPoints Y.X := by
  intro E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hξ
  apply mem_genericPoints_of_eq
  intro p hp
  have hp' : p ∈ Set.range (Y.X.fromSpecStalk (GlobalTheory.CompanionTheory.Ar.genPt ξ₀)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hp
  obtain ⟨q, rfl⟩ := hp'
  have hfield : IsField (Y.X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ₀)) :=
    MulEquiv.isField (Field.toIsField Ω₀)
      (RingEquiv.ofBijective (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo ξ₀)) hξ.bij).toMulEquiv
  have hq : q = IsLocalRing.closedPoint _ := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal q.isPrime.ne_top
    · intro a ha
      by_cases h0 : a = 0
      · rw [h0]
        exact q.asIdeal.zero_mem
      · obtain ⟨b, hb⟩ := hfield.mul_inv_cancel h0
        exact absurd ⟨⟨a, b, hb, by rw [mul_comm]; exact hb⟩, rfl⟩ ((IsLocalRing.mem_maximalIdeal a).1 ha)
  rw [hq, Scheme.fromSpecStalk_closedPoint]

end GlobalTheory.CompanionTheory.Ar.GenPtModel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_generic_is_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ∈ genericPoints Y.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints | exact GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints | (intros; apply GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddle
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagRead

open GlobalTheory.CompanionTheory.Ar.FlagPull

theorem fieldRange_finite {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω)
    (hfin : letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) :
    FiniteDimensional i.fieldRange Ω ∧
      Module.finrank i.fieldRange Ω = (letI := i.toAlgebra; Module.finrank Ω₁ Ω) := by
  letI := i.toAlgebra
  haveI := hfin
  let e : Ω₁ ≃+* i.fieldRange := RingEquiv.ofBijective i.rangeRestrictField
    ⟨fun x y h => i.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨a, Subtype.ext ha⟩⟩
  have he : (algebraMap i.fieldRange Ω).comp (e : Ω₁ →+* i.fieldRange) =
      ((RingEquiv.refl Ω : Ω ≃+* Ω) : Ω →+* Ω).comp (algebraMap Ω₁ Ω) := by
    ext x
    rfl
  exact ⟨Module.Finite.of_equiv_equiv e (RingEquiv.refl Ω) he,
    (Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl Ω) he).symm⟩

theorem span_eq_of_indep {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b b' : Fin r → V}
    {W : Submodule Ω V} (hb : LinearIndependent Ω b) (hle : ∀ k, b k ∈ W) (hb' : LinearIndependent Ω b')
    (hs : Submodule.span Ω (Set.range b') = W) : Submodule.span Ω (Set.range b) = W := by
  subst hs
  haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range b')) :=
    FiniteDimensional.span_of_finite Ω (Set.finite_range _)
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨k, rfl⟩
    exact hle k
  · rw [finrank_span_eq_card hb, finrank_span_eq_card hb']

theorem generic_read : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module B.Ω₀ Li₀) (M₀ : LieModel Y.t.G B.ξ₀ Li₀) (j : Li₀ →+ B.Li) (V₀ : CMType H ⊕ CMType H → Submodule B.Ω₀ Li₀), (∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s) ∧ (∀ e, (B.M.pt (j e)).left ≫ B.m.φ = spMap (dualMap B.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ B.Vgen s) ∧ (letI := B.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ (fun s a => jA (Fl.b s a)) ((letI := i.toAlgebra; Module.finrank Ω₁ Ω) * Fl.deg)) := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hfin hd hf hcst hj hpt hρ
  obtain ⟨hfd, hfr⟩ := fieldRange_finite i hfin
  haveI := hfd
  have hgen : genPt A.ξ₀ = genPt B.ξ₀ := by
    have h1 := RegAtDom.map_genPt hd
    have h2 := RegAtDom.map_genPt A.fn_over
    have h3 := RegAtDom.map_genPt B.fn_over
    rw [← h2, ← h3, ← h1, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_iso A.gen₀ B.gen₀ hgen
  have hfn : B.fn.comp ψ.toRingHom = i.comp A.fn := by
    haveI := mono_of_isCptGen A.gen₀
    have e1 : spMap B.fn ≫ B.ξ₀ = B.ξ ≫ B.f := B.fn_over.symm
    have e2 : spMap A.fn ≫ A.ξ₀ = A.ξ ≫ A.f := A.fn_over.symm
    have e3 : B.ξ ≫ h = spMap i ≫ A.ξ := hd
    have e4 : spMap (B.fn.comp ψ.toRingHom) = spMap (i.comp A.fn) := by
      refine (cancel_mono A.ξ₀).1 ?_
      rw [FlagPull.spMap_comp, FlagPull.spMap_comp, Category.assoc, Category.assoc, hψ, e1, e2, hf, ← Category.assoc, e3,
        Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e4)
  letI mod' : Module B.Ω₀ Fl.Li₀ := Module.compHom _ ψ.symm.toRingHom
  have hs : ∀ (a : A.Ω₀) (e : Fl.Li₀), ψ a • e = a • e := fun a e => by
    show ψ.symm (ψ a) • e = a • e
    rw [ψ.symm_apply_apply]
  have hemb : ∀ s, B.emb s = i.comp (A.emb s) := fun s => by
    simp only [HodgeCpt.emb]
    rw [hcst]
    rfl
  have hVgen : ∀ s w, jA w ∈ B.Vgen s ↔ w ∈ A.Vgen s := fun s w => by
    show jA w ∈ eigSp B.ρ (B.emb s) ↔ w ∈ eigSp A.ρ (A.emb s)
    rw [hemb]
    exact mem_eigSp_iff hj _ _ _ hρ w
  let V₀' : CMType H ⊕ CMType H → Submodule B.Ω₀ Fl.Li₀ := fun s =>
    { carrier := (Fl.V₀ s : Set Fl.Li₀)
      add_mem' := fun ha hb => (Fl.V₀ s).add_mem ha hb
      zero_mem' := (Fl.V₀ s).zero_mem
      smul_mem' := fun c x hx => (Fl.V₀ s).smul_mem (ψ.symm c) hx }
  have hsq : spMap (dualMap i) ≫ spMap (dualMap A.fn) = spMap (dualMap B.fn) ≫ spMap (dualMap ψ.toRingHom) := by
    rw [← FlagPull.spMap_comp, ← FlagPull.spMap_comp, ← dualMap_comp, ← dualMap_comp, hfn]
  have hspan : ∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s := by
    intro s
    letI := A.fn.toAlgebra
    obtain ⟨cc, u, hcV, -, -, hb, -, -, hfl, -⟩ := Fl.generic
    have hmemc : ∀ k, Fl.j (cc s k) ∈ A.Vgen s := fun k => (Fl.V₀_mem s _).1 (by
      rw [← (hcV s).2]
      exact Submodule.subset_span ⟨k, rfl⟩)
    have hbk : ∀ a, Fl.b s a ∈ A.Vgen s := by
      intro a
      have h1 : Fl.b s a ∈ flagStep Ω₁ (Fl.b s) (labelRk D s) := Submodule.subset_span ⟨a, a.2, rfl⟩
      rw [hfl s] at h1
      refine (Submodule.span_le (p := A.Vgen s).2 ?_) h1
      rintro _ ⟨k, -, rfl⟩
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmemc l)
    obtain ⟨U, hU, b', hb', hfr'⟩ := B.vb s ⟨genPt B.ξ, specializes_rfl⟩ (Set.mem_univ _)
    exact span_eq_of_indep (hj.2 _ _ (hb s)) (fun k => (hVgen s _).2 (hbk k))
      (hfr' _ (Set.mem_univ _) hU).1 hb'
  refine ⟨Fl.Li₀, Fl.acg, mod', transport ψ hψ hs Fl.M₀, jA.comp Fl.j, V₀', hspan, fun e => ?_,
    fun s e => (Fl.V₀_mem s e).trans (hVgen s _).symm, ?_⟩
  · show (B.M.pt (jA (Fl.j e))).left ≫ B.m.φ =
      spMap (dualMap B.fn) ≫ spMap (dualMap ψ.toRingHom) ≫ (Fl.M₀.pt e).left
    rw [hpt, Fl.j_pt, ← Category.assoc, hsq, Category.assoc]
  · have := genericFlag_pull A.fn B.fn ψ i hfn hs Fl.j jA hj Fl.V₀ V₀' (fun _ _ => Iff.rfl) Fl.b Fl.deg Fl.generic
    rw [hfr] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.FlagRead
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_comparison_middle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module B.Ω₀ Li₀) (M₀ : LieModel Y.t.G B.ξ₀ Li₀) (j : Li₀ →+ B.Li) (V₀ : CMType H ⊕ CMType H → Submodule B.Ω₀ Li₀), (∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s) ∧ (∀ e, (B.M.pt (j e)).left ≫ B.m.φ = spMap (dualMap B.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ B.Vgen s) ∧ (letI := B.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ (fun s a => jA (Fl.b s a)) ((letI := i.toAlgebra; Module.finrank Ω₁ Ω) * Fl.deg)) := by
  exact @GlobalTheory.CompanionTheory.Ar.FlagRead.generic_read
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsClopenIrreducibleCpt
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsClopenIrreducibleCpt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_cptOver_mem_isClopen_isIrreducible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (u : Xo.XF c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ (U : Set (Xo.XF c)) (_ : CptOver Y U), u ∈ U ∧ IsClopen U ∧ IsIrreducible U := by
  intro E _ _ _ H D l Xo c O _ β Y u hyp
  obtain ⟨hinj, hnoeth, hfrac⟩ := hyp
  have hmem := irreducibleComponent_mem_irreducibleComponents u
  obtain ⟨Z⟩ := nonempty_cptOver_of_fraction hinj hfrac Y _ hmem
  obtain ⟨U', hU', -⟩ := cptOver_isOpen_isDomain E H D l Xo c O β Y _ Z ⟨hinj, hnoeth, hfrac⟩
  refine ⟨irreducibleComponent u, Z, mem_irreducibleComponent, ⟨isClosed_of_mem_irreducibleComponents _ hmem, ?_⟩,
    isIrreducible_irreducibleComponent⟩
  rw [← hU']
  exact U'.isOpen

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsClopenIrreducibleCptStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clopen_irreducible_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (u : Xo.XF c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ (U : Set (Xo.XF c)) (_ : CptOver Y U), u ∈ U ∧ IsClopen U ∧ IsIrreducible U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_cptOver_mem_isClopen_isIrreducible | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_cptOver_mem_isClopen_isIrreducible | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_cptOver_mem_isClopen_isIrreducible <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSectionEqOfConnected
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSectionEqOfConnected
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.HolTorsion in
theorem cubWeil_const_of_isHolTo_family : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1 ∧ (x b).left ≫ G.hom = (x' b).left ≫ G.hom) → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → ∀ b ∈ B, GlobalTheory.UU.CubWeil c N (x b) (x' b) (unitOn ζ) := by
  intro X G _ _ L c m N B y x x' ζ b₀ hN _ hB hb₀ hx hx' htor h₀ b₁ hb₁
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  let mk : G ⟶ G := (𝟙 G) ^ N
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ N = 1 ↔ u.left ≫ mk.left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ mk.left = (u ^ N).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst mk.left o
  let q := pullback.snd mk.left o
  have H : IsPullback p q mk.left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w mk, ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2.1) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  let T : Over X := Over.mk (pullback.fst q q ≫ q)
  let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
    show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq])
  let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
    show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq, pullback.condition])
  have hu : u ^ N = 1 := (hkill T u).2 (by
    show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, Category.assoc])
  have hv : v ^ N = 1 := (hkill T v).2 (by
    show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, pullback.condition, Category.assoc])
  obtain ⟨e, he, -⟩ := GlobalTheory.UU.existsUnique_cubWeil c hu hv
  have hek : e.val ^ N = 1 := congrArg Units.val he.pow_eq_one
  have hpull : ∀ w ∈ B, GlobalTheory.UU.CubWeil c N (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
    intro w hw
    let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
      show z w ≫ pullback.fst q q ≫ q = y w
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
    have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
      show z w ≫ pullback.fst q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
    have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
      show z w ≫ pullback.snd q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
    have := he.comp h
    rw [e₁, e₂] at this
    exact this
  have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn ζ := (hpull b₀ hb₀).unique h₀
  have e₁ : Units.map (z b₁).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
    Units.ext ((val_map_appTop (z b₁) e.val).trans
      ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hN hek hb₀ hb₁)).trans (val_map_appTop (z b₀) e.val).symm))
  have := hpull b₁ hb₁
  rw [e₁, e₀] at this
  exact this

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSectionEqOfConnectedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_section_eq_of_connected : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1 ∧ (x b).left ≫ G.hom = (x' b).left ≫ G.hom) → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → ∀ b ∈ B, GlobalTheory.UU.CubWeil c N (x b) (x' b) (unitOn ζ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.cubWeil_const_of_isHolTo_family | exact GlobalTheory.CompanionTheory.Ar.Flat.cubWeil_const_of_isHolTo_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.cubWeil_const_of_isHolTo_family <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsReindexed
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsReindexed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordsDown

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isUnit_natCast_of_local {A : Type*} [CommRing A] (φ : A →+* ℂ) [IsLocalHom φ] (r : ℕ) (hr : r.Prime) :
    IsUnit (r : A) := by
  apply isUnit_of_map_unit φ
  rw [map_natCast]
  exact isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hr.ne_zero)

theorem unitAt_centre {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (z : Spec (CommRingCat.of ℂ) ⟶ X')
    (h : genPt ξ' ⤳ centre z) (r : ℕ) (hr : r.Prime) : unitAt ξ' ⟨centre z, h⟩ (r : Ω) := by
  have hz : IsLocalHom (Scheme.stalkClosedPointTo z).hom := inferInstance
  have hu : IsUnit ((r : X'.presheaf.stalk (centre z))) := isUnit_natCast_of_local (Scheme.stalkClosedPointTo z).hom r hr
  have hu' : IsUnit ((r : Ω)) := by
    have := hu.map (genMap ξ' ⟨centre z, h⟩)
    rwa [map_natCast] at this
  obtain ⟨u, hu1⟩ := hu.exists_right_inv
  refine ⟨hu'.ne_zero, ⟨(r : X'.presheaf.stalk (centre z)), map_natCast _ _⟩, ⟨u, ?_⟩⟩
  have e := congrArg (genMap ξ' ⟨centre z, h⟩) hu1
  rw [map_mul, map_natCast, map_one] at e
  exact eq_inv_of_mul_eq_one_right e

theorem genMap_stalkMap (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

theorem valAt_down {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (g : X' ⟶ X) (hinj : IsCptGen ξ')
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (h' : genPt ξ' ⤳ centre z)
    (h : genPt (ξ' ≫ g) ⤳ g (centre z))
    (hreg : regAt ξ' ⟨centre z, h'⟩ = regAt (ξ' ≫ g) ⟨g (centre z), h⟩)
    {a : Ω} {r : ℂ} (hv : ValAt ξ' z a r) : ValAt (ξ' ≫ g) (z ≫ g) a r := by
  obtain ⟨h1, s, hs, rfl⟩ := hv
  have ha : a ∈ regAt (ξ' ≫ g) ⟨g (centre z), h⟩ := by
    rw [← hreg]
    exact ⟨s, hs⟩
  obtain ⟨s₀, hs₀⟩ := ha
  have e : (g.stalkMap (centre z)).hom s₀ = s := by
    apply hinj.inj ⟨centre z, h'⟩
    rw [genMap_stalkMap ξ' g ⟨centre z, h'⟩ h s₀]
    exact hs₀.trans hs.symm
  subst e
  refine ⟨h, s₀, hs₀, ?_⟩
  exact congrArg (fun t => t.hom s₀) (Scheme.stalkClosedPointTo_comp z g)

theorem coordsAt_down : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (K' : Type) (J' : K' → Type) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, J' k) → ℂ), (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → IsCptGen ξ' → ξ' ≫ g = ξ → (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) → (∀ q' : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt ξ' q' = regAt ξ ⟨g q'.1, h⟩) → CoordsAt ξ' y' z w → CoordsAt ξ y (z ≫ g) (fun p : (Σ k, J k) => w ⟨bk p.1, bx p.1 p.2⟩) := by
  intro X X' Ω _ ξ ξ' g K J y K' J' y' bk bx z w hall hall' hgen hcomp hy hreg hw
  subst hcomp
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c, hc⟩ := hw.1 (bk k)
    exact ⟨(bx k).symm c, by simpa using hc⟩
  · obtain ⟨hne, hv⟩ := hw.2 (bk k) (bx k c) hc
    refine ⟨by rwa [hy] at hne, fun i => ?_⟩
    obtain ⟨r, hr, e⟩ := hv (bx k i)
    rw [hy, hy] at hr
    have h' := hall' (centre z)
    have h := hall (g (centre z))
    refine ⟨r, valAt_down g hgen z h' h (hreg ⟨centre z, h'⟩ (fun p hp hf => hf (unitAt_centre z h' p hp)) h) hr, e⟩

end GlobalTheory.CompanionTheory.Ar.CoordsDown
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsReindexedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_coords_reindexed : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (K' : Type) (J' : K' → Type) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, J' k) → ℂ), (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → IsCptGen ξ' → ξ' ≫ g = ξ → (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) → (∀ q' : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt ξ' q' = regAt ξ ⟨g q'.1, h⟩) → CoordsAt ξ' y' z w → CoordsAt ξ y (z ≫ g) (fun p : (Σ k, J k) => w ⟨bk p.1, bx p.1 p.2⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down | exact GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionRing
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem lieMap_act_pull (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X)
    (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
    (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω' V')
    (j : V →+ V') : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) →
    ∀ a e, j (ρ a e) = ρ' a (j e) := by
  intro _ ha ha' hj a e
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  apply M'.inj
  refine hcanc _ _ ?_
  rw [ha' a (j e), hj, ha a e, Over.comp_left, Over.comp_left, Category.assoc, m.act a]
  have h2 := congrArg (· ≫ (t.act.act a).left) (hj e)
  simp only [Category.assoc] at h2 ⊢
  exact h2.symm

end GlobalTheory.CompanionTheory.Ar.FlagStep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_pullback_action_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X)
    (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
    (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω' V')
    (j : V →+ V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) →
    ∀ a e, j (ρ a e) = ρ' a (j e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull | exact GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull <;> assumption)
end
end
