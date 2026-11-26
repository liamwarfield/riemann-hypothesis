module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormula
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.HodgeAffineIsoType

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.TermAff
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsRestrictOpenBijective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsRestrictOpenBijective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section
namespace GlobalTheory.CompanionTheory.FormOpen

variable {K : Type} [CommRing K]

theorem mOm_bijective {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    {φ : A →+* B} (hφ : SemiHom (RingHom.id K) φ) (hb : Function.Bijective φ) (j : ℕ) :
    Function.Bijective (hφ.mOm j) := by
  let e : A ≃+* B := RingEquiv.ofBijective φ hb
  have he : ∀ a, e a = φ a := fun _ ↦ rfl
  have hψ : SemiHom (RingHom.id K) (e.symm : B →+* A) := fun r b ↦ by
    apply e.injective
    change e (e.symm (r • b)) = e (RingHom.id K r • e.symm b)
    rw [RingEquiv.apply_symm_apply, he, RingHom.id_apply, show φ (r • e.symm b) = _ from hφ r _,
      ← he, RingEquiv.apply_symm_apply, RingHom.id_apply]
  have hA : SemiHom (RingHom.id K) (RingHom.id A) := fun _ _ ↦ rfl
  have hB : SemiHom (RingHom.id K) (RingHom.id B) := fun _ _ ↦ rfl
  have l : Function.LeftInverse (hψ.mOm j) (hφ.mOm j) := fun x ↦
    (SemiHom.mOm_mOm (ρ := RingHom.id K) hφ hψ hA (fun a ↦ e.symm_apply_apply a) x).trans
      (hA.mOm_id (fun _ ↦ rfl) x)
  have r : Function.RightInverse (hψ.mOm j) (hφ.mOm j) := fun x ↦
    (SemiHom.mOm_mOm (ρ := RingHom.id K) hψ hφ hB (fun a ↦ e.apply_symm_apply a) x).trans
      (hB.mOm_id (fun _ ↦ rfl) x)
  exact ⟨l.injective, r.surjective⟩

variable {X : Scheme.{0}}

theorem app_map_eq (V : X.Opens) (h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.app V ≫ V.toScheme.presheaf.map (homOfLE h).op = V.topIso.inv := by
  simp only [Scheme.Opens.topIso, Scheme.Opens.ι_app, Scheme.Opens.toScheme_presheaf_map,
    Iso.op_inv, Functor.mapIso_inv, eqToIso.inv, ← Functor.map_comp, ← op_comp]
  rfl

theorem res_appSec_bijective (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens)
    (h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    Function.Bijective ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp
      (appSec q (V.ι ≫ q) V.ι V)) := by
  have e : ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp (appSec q (V.ι ≫ q) V.ι V) :
      Sec q V → Sec (V.ι ≫ q) ⊤) = V.topIso.inv.hom := by
    rw [← app_map_eq V h]; rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso V.topIso.inv

theorem formRes_formPull_open_bijective {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ) :
    Function.Bijective fun x : OmU q V a => formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V by simp) a
      (formPull (f := V.ι) rfl V a x) := by
  have h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have hγ : SemiHom (RingHom.id K) ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp
      (appSec q (V.ι ≫ q) V.ι V)) :=
    (semiHom_appSec rfl V).comp (SemiHom.of_algHom (Sec.res (V.ι ≫ q) h))
  have e : (fun x : OmU q V a => formRes (V.ι ≫ q) h a (formPull (f := V.ι) rfl V a x)) =
      hγ.mOm a := funext fun x ↦
    SemiHom.mOm_mOm (semiHom_appSec rfl V) (SemiHom.of_algHom (Sec.res (V.ι ≫ q) h)) hγ
      (fun _ ↦ rfl) x
  rw [e]
  exact mOm_bijective hγ (res_appSec_bijective q V h) a

end GlobalTheory.CompanionTheory.FormOpen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsRestrictOpenBijectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_restrict_open_bijective : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ),
    Function.Bijective fun x : OmU q V a => formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V by simp) a
      (formPull (f := V.ι) rfl V a x) := by
  first | exact @GlobalTheory.CompanionTheory.FormOpen.formRes_formPull_open_bijective | exact GlobalTheory.CompanionTheory.FormOpen.formRes_formPull_open_bijective | (intros; apply GlobalTheory.CompanionTheory.FormOpen.formRes_formPull_open_bijective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictGradedPullNatural
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictGradedPullNatural
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.OpenThick

variable {K : Type} [CommRing K]

section Pt

variable {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

abbrev Pt (q : X ⟶ Spec (CommRingCat.of K)) (B : Type) [CommRing B] : Type :=
  PtOver X q (Ideal.Quotient.mk (⊥ : Ideal K)) B

theorem pt_ext (V : X.Opens) {B : Type} [CommRing B] {y y' : Pt (V.ι ≫ q) B} (h1 : y.1.1 = y'.1.1)
    (h2 : y.1.2 ≫ V.ι = y'.1.2 ≫ V.ι) : y = y' :=
  Subtype.ext (Prod.ext h1 ((cancel_mono V.ι).1 h2))

def liftPt (V : X.Opens) {B : Type} [CommRing B] (y : Pt q B) (h : ⊤ ≤ y.1.2 ⁻¹ᵁ V) : Pt (V.ι ≫ q) B :=
  ⟨(y.1.1, IsOpenImmersion.lift V.ι y.1.2 (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact h (Set.mem_univ x))), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact y.2⟩

theorem liftPt_fac (V : X.Opens) {B : Type} [CommRing B] (y : Pt q B) (h : ⊤ ≤ y.1.2 ⁻¹ᵁ V) :
    (liftPt V y h).1.2 ≫ V.ι = y.1.2 := IsOpenImmersion.lift_fac _ _ _

theorem liftPt_map (V : X.Opens) {B B' : CommRingCat.{0}} (φ : B ⟶ B') (y : Pt q B) (y' : Pt q B')
    (h : ⊤ ≤ y.1.2 ⁻¹ᵁ V) (h' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V)
    (e : (ptFun X q (Ideal.Quotient.mk (⊥ : Ideal K))).map φ y = y') :
    (ptFun V.toScheme (V.ι ≫ q) (Ideal.Quotient.mk (⊥ : Ideal K))).map φ (liftPt V y h) = liftPt V y' h' := by
  subst e
  refine pt_ext V rfl ?_
  change (Spec.map φ ≫ (liftPt V y h).1.2) ≫ V.ι = (liftPt V _ h').1.2 ≫ V.ι
  rw [Category.assoc, liftPt_fac, liftPt_fac]
  rfl

theorem pt_id {Z : Scheme.{0}} {r : Z ⟶ Spec (CommRingCat.of K)} {B : Type} [CommRing B] (J : Ideal B) (hJ)
    (y : Pt r (B ⧸ J)) :
    (ptFun Z r (Ideal.Quotient.mk (⊥ : Ideal K))).map
      (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B) hJ)) y = y := by
  have e : Ideal.quotientMap J (RingHom.id B) hJ = RingHom.id (B ⧸ J) := by
    ext
    rfl
  rw [e]
  exact congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
    ((ptFun Z r (Ideal.Quotient.mk (⊥ : Ideal K))).map_id (CommRingCat.of (B ⧸ J)))) y

end Pt

section Thickenings

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

abbrev InV (V : X.Opens) (T : Thick (smFun X q)) : Prop :=
  InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) V T

def smH {T T' : Thick (smFun X q)} (φ : T.B →+* T'.B) (comm : ∀ r, φ (T.i r) = T'.i r)
    (dp : IsDPMorphism T.δ T'.δ φ) (hle : T.J ≤ T'.J.comap φ)
    (hpt : (smFun X q).Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ hle)) T.y = T'.y) : T ⟶ T' :=
  mkH (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (T := T) (T' := T') φ comm dp hle hpt

theorem sm_ext {T T' : Thick (smFun X q)} {f g : T ⟶ T'} (h : f.φ = g.φ) : f = g :=
  hom_ext (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (T := T) (T' := T') h

def liftT (V : X.Opens) (T : Thick (smFun X q)) (h : InV V T) : Thick (smFun V.toScheme (V.ι ≫ q)) :=
  mkT (γ := dividedPowersBot K) (p := 0) (q := V.ι ≫ q) (κ := Ideal.Quotient.mk ⊥) T.B T.i T.J T.δ T.adm T.compat
    (liftPt V T.y h) T.w

theorem inV_of {V : X.Opens} {s : ℕ} {T : Thick (smFun X q)} (h : KS q s {V} T) : InV V T := by
  obtain ⟨-, V', hV', hT⟩ := h
  obtain rfl := Set.mem_singleton_iff.1 hV'
  exact hT


variable (q) in
def mF (V : X.Opens) (s : ℕ) : (KS q s {V}).FullSubcategory ⥤ (KS (V.ι ≫ q) s {⊤}).FullSubcategory where
  obj T := ⟨liftT V T.obj (inV_of T.property), T.property.1, ⊤, rfl, fun _ _ => trivial⟩
  map {T T'} f := ObjectProperty.homMk (smH (T := liftT V T.obj (inV_of T.property)) (T' := liftT V T'.obj (inV_of T'.property))
    f.hom.φ f.hom.comm f.hom.dp f.hom.hle (liftPt_map V (CommRingCat.ofHom (Ideal.quotientMap T'.obj.J f.hom.φ f.hom.hle)) T.obj.y T'.obj.y (inV_of T.property) (inV_of T'.property) f.hom.pt))
  map_id _ := ObjectProperty.hom_ext _ (sm_ext rfl)
  map_comp _ _ := ObjectProperty.hom_ext _ (sm_ext rfl)


variable (q) in
def mV (V : X.Opens) (s a : ℕ) :
    CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a)
      ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a) (RingHom.id K) where
  G := mF q V s
  τ T := LinearMap.id
  nat _ _ := rfl

end Thickenings

section Equivalence

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem liftPt_unmap (V : X.Opens) {B B' : CommRingCat.{0}} (φ : B ⟶ B') (y : Pt q B) (y' : Pt q B')
    (h : ⊤ ≤ y.1.2 ⁻¹ᵁ V) (h' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V)
    (e : (ptFun V.toScheme (V.ι ≫ q) (Ideal.Quotient.mk (⊥ : Ideal K))).map φ (liftPt V y h) = liftPt V y' h') :
    (ptFun X q (Ideal.Quotient.mk (⊥ : Ideal K))).map φ y = y' := by
  refine Subtype.ext (Prod.ext (congrArg (fun z : Pt (V.ι ≫ q) B' => z.1.1) e) ?_)
  have e2 := congrArg (fun z : Pt (V.ι ≫ q) B' => z.1.2 ≫ V.ι) e
  change (Spec.map φ ≫ (liftPt V y h).1.2) ≫ V.ι = (liftPt V y' h').1.2 ≫ V.ι at e2
  rw [Category.assoc, liftPt_fac, liftPt_fac] at e2
  exact e2

instance mF_faithful (V : X.Opens) (s : ℕ) : (mF q V s).Faithful where
  map_injective {T T'} f g e :=
    ObjectProperty.hom_ext _ (sm_ext (T := T.obj) (T' := T'.obj) (congrArg (fun t => t.hom.φ) e))

instance mF_full (V : X.Opens) (s : ℕ) : (mF q V s).Full where
  map_surjective {T T'} g :=
    ⟨ObjectProperty.homMk (smH (T := T.obj) (T' := T'.obj) g.hom.φ g.hom.comm g.hom.dp g.hom.hle
      (liftPt_unmap V (CommRingCat.ofHom (Ideal.quotientMap T'.obj.J g.hom.φ g.hom.hle)) T.obj.y T'.obj.y
        (inV_of T.property) (inV_of T'.property) g.hom.pt)),
      ObjectProperty.hom_ext _ (sm_ext rfl)⟩

theorem top_le_comp (V : X.Opens) {Z : Scheme.{0}} (z : Z ⟶ V.toScheme) : ⊤ ≤ (z ≫ V.ι) ⁻¹ᵁ V := by
  intro x _
  change (z ≫ V.ι) x ∈ V
  rw [Scheme.Hom.comp_apply]
  have hx : V.ι (z x) ∈ (V : Set X) := Scheme.Opens.range_ι V ▸ ⟨z x, rfl⟩
  exact hx

def pushPt (V : X.Opens) {B : Type} [CommRing B] (y : Pt (V.ι ≫ q) B) : Pt q B :=
  ⟨(y.1.1, y.1.2 ≫ V.ι), by
    rw [Category.assoc]
    exact y.2⟩

theorem lift_push (V : X.Opens) {B : Type} [CommRing B] (y : Pt (V.ι ≫ q) B) (h : ⊤ ≤ (pushPt V y).1.2 ⁻¹ᵁ V) :
    liftPt V (pushPt V y) h = y :=
  pt_ext V rfl (liftPt_fac V (pushPt V y) h)

def downT (V : X.Opens) (T : Thick (smFun V.toScheme (V.ι ≫ q))) : Thick (smFun X q) :=
  mkT (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.B T.i T.J T.δ T.adm T.compat
    (pushPt V T.y) T.w

theorem down_inV (V : X.Opens) (T : Thick (smFun V.toScheme (V.ι ≫ q))) : InV V (downT V T) :=
  top_le_comp V _

def dnHom (V : X.Opens) (T : Thick (smFun V.toScheme (V.ι ≫ q))) (h : InV V (downT V T)) :
    liftT V (downT V T) h ⟶ T :=
  smH (T := liftT V (downT V T) h) (T' := T) (RingHom.id T.B) (fun _ => rfl) (DPMorphism.id T.δ).isDPMorphism
    (fun _ hx => hx) ((pt_id T.J _ _).trans (lift_push V T.y h))

def dnInv (V : X.Opens) (T : Thick (smFun V.toScheme (V.ι ≫ q))) (h : InV V (downT V T)) :
    T ⟶ liftT V (downT V T) h :=
  smH (T := T) (T' := liftT V (downT V T) h) (RingHom.id T.B) (fun _ => rfl) (DPMorphism.id T.δ).isDPMorphism
    (fun _ hx => hx) ((pt_id T.J _ _).trans (lift_push V T.y h).symm)

theorem ks_of {V : X.Opens} {s : ℕ} {T : Thick (smFun X q)} (h1 : TF 1 s T) (h2 : InV V T) : KS q s {V} T :=
  ⟨h1, V, rfl, h2⟩

def pushK (V : X.Opens) (s : ℕ) (T : (KS (V.ι ≫ q) s {⊤}).FullSubcategory) : (KS q s {V}).FullSubcategory :=
  ⟨downT V T.obj, ks_of T.property.1 (down_inV V T.obj)⟩

def pushIso (V : X.Opens) (s : ℕ) (T : (KS (V.ι ≫ q) s {⊤}).FullSubcategory) : (mF q V s).obj (pushK V s T) ≅ T where
  hom := ObjectProperty.homMk (dnHom V T.obj (inV_of (pushK V s T).property))
  inv := ObjectProperty.homMk (dnInv V T.obj (inV_of (pushK V s T).property))
  hom_inv_id := ObjectProperty.hom_ext _ (sm_ext rfl)
  inv_hom_id := ObjectProperty.hom_ext _ (sm_ext rfl)

instance mF_essSurj (V : X.Opens) (s : ℕ) : (mF q V s).EssSurj where
  mem_essImage T := ⟨pushK V s T, ⟨pushIso V s T⟩⟩

instance mF_equiv (V : X.Opens) (s : ℕ) : (mF q V s).IsEquivalence := { }

theorem mV_bij (V : X.Opens) (s a n : ℕ) : Function.Bijective ((mV q V s a).pull n) :=
  haveI : (mV q V s a).G.IsLeftAdjoint := inferInstanceAs (mF q V s).IsLeftAdjoint
  P.adj_mor (mV q V s a) (fun _ => Function.bijective_id) n

end Equivalence

section Natural

variable {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}
  (u : X ⟶ Y) (hu : u ≫ p = q) (V : X.Opens) (W : Y.Opens) (h : V ≤ u ⁻¹ᵁ W)
  (hh : u.resLE W V h ≫ (W.ι ≫ p) = V.ι ≫ q)

theorem push_lift {B : CommRingCat.{0}} (y : Pt q B) (hV : ⊤ ≤ y.1.2 ⁻¹ᵁ V)
    (hW : ⊤ ≤ ((smMor u hu).pt.app B y : Pt p B).1.2 ⁻¹ᵁ W) :
    ((smMor (u.resLE W V h) hh).pt.app B (liftPt V y hV) : Pt (W.ι ≫ p) B) =
      liftPt W ((smMor u hu).pt.app B y) hW := by
  refine pt_ext W rfl ?_
  change ((liftPt V y hV).1.2 ≫ u.resLE W V h) ≫ W.ι = _
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, liftPt_fac, liftPt_fac]
  rfl

variable (s a : ℕ) (hG : ∀ T, KS q s {V} T → KS p s {W} ((pullM u hu a).G.obj T))
  (hG' : ∀ T, KS (V.ι ≫ q) s {⊤} T → KS (W.ι ≫ p) s {⊤} ((pullM (u.resLE W V h) hh a).G.obj T))

def etaN : (mV q V s a).G ⋙ (morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤}) (U' := KS (V.ι ≫ q) s {⊤}) hG').G ⟶
    (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG).G ⋙ (mV p W s a).G where
  app T := ObjectProperty.homMk (smH (RingHom.id _) (fun _ => rfl) (DPMorphism.id T.obj.δ).isDPMorphism (fun _ hx => hx)
    ((pt_id T.obj.J _ _).trans (push_lift u hu V W h hh T.obj.y (inV_of T.property) (inV_of (hG _ T.property)))))
  naturality _ _ _ := ObjectProperty.hom_ext _ (sm_ext rfl)

theorem mV_nat (n : ℕ) (x) :
    (mV q V s a).pull n ((morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤}) (U' := KS (V.ι ≫ q) s {⊤}) hG').pull n x) =
      (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG).pull n ((mV p W s a).pull n x) := by
  have e1 := (P.pull_comp (σ'' := RingHom.id K) (morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤})
    (U' := KS (V.ι ≫ q) s {⊤}) hG') (mV q V s a) n x).1
  have e2 := (P.pull_comp (σ'' := RingHom.id K) (mV p W s a) (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG) n x).1
  refine e1.symm.trans (Eq.trans ?_ e2)
  refine P.prism _ _ (etaN u hu V W h hh s a hG hG') (fun T z => ?_) n x
  obtain ⟨z, hz⟩ := z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

end Natural

theorem open_thick : ∀ (K : Type) [CommRing K], ∃ m : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a : ℕ),
    CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a) ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a)
      (RingHom.id K),
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a n : ℕ), Function.Bijective ((m q V s a).pull n)) ∧
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q)
      (V : X.Opens) (W : Y.Opens) (h : V ≤ u ⁻¹ᵁ W) (hh : u.resLE W V h ≫ (W.ι ≫ p) = V.ι ≫ q) (s a : ℕ)
      (hG : ∀ T, KS q s {V} T → KS p s {W} ((pullM u hu a).G.obj T))
      (hG' : ∀ T, KS (V.ι ≫ q) s {⊤} T → KS (W.ι ≫ p) s {⊤} ((pullM (u.resLE W V h) hh a).G.obj T)) (n : ℕ) x,
      (m q V s a).pull n ((morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤}) (U' := KS (V.ι ≫ q) s {⊤}) hG').pull n x) =
        (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG).pull n ((m p W s a).pull n x) :=
  fun K _ => ⟨@fun X q V s a => mV q V s a, @fun X q V s a n => mV_bij V s a n,
    @fun X Y q p u hu V W h hh s a hG hG' n x => mV_nat u hu V W h hh s a hG hG' n x⟩

end GlobalTheory.CompanionTheory.OpenThick
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictGradedPullNaturalStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_graded_pull_natural : ∀ (K : Type) [CommRing K], ∃ m : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a : ℕ),
    CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a) ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a)
      (RingHom.id K),
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a n : ℕ), Function.Bijective ((m q V s a).pull n)) ∧
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q)
      (V : X.Opens) (W : Y.Opens) (h : V ≤ u ⁻¹ᵁ W) (hh : u.resLE W V h ≫ (W.ι ≫ p) = V.ι ≫ q) (s a : ℕ)
      (hG : ∀ T, KS q s {V} T → KS p s {W} ((pullM u hu a).G.obj T))
      (hG' : ∀ T, KS (V.ι ≫ q) s {⊤} T → KS (W.ι ≫ p) s {⊤} ((pullM (u.resLE W V h) hh a).G.obj T)) (n : ℕ) x,
      (m q V s a).pull n ((morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤}) (U' := KS (V.ι ≫ q) s {⊤}) hG').pull n x) =
        (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG).pull n ((m p W s a).pull n x) := by
  first | exact @GlobalTheory.CompanionTheory.OpenThick.open_thick | exact GlobalTheory.CompanionTheory.OpenThick.open_thick | (intros; apply GlobalTheory.CompanionTheory.OpenThick.open_thick <;> assumption)
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace CrystallineSemistableComparison.Om.Nt2.TermAff

theorem mOm_four {K A B₁ B₂ B₃ B₄ C₁ C₂ C₃ : Type} [CommRing K] [CommRing A] [Algebra K A]
    [CommRing B₁] [Algebra K B₁] [CommRing B₂] [Algebra K B₂] [CommRing B₃] [Algebra K B₃] [CommRing B₄] [Algebra K B₄]
    [CommRing C₁] [Algebra K C₁] [CommRing C₂] [Algebra K C₂] [CommRing C₃] [Algebra K C₃]
    {α₁ : A →+* B₁} {α₂ : B₁ →+* B₂} {α₃ : B₂ →+* B₃} {α₄ : B₃ →+* B₄}
    {β₁ : A →+* C₁} {β₂ : C₁ →+* C₂} {β₃ : C₂ →+* C₃} {β₄ : C₃ →+* B₄}
    (h₁ : SemiHom (RingHom.id K) α₁) (h₂ : SemiHom (RingHom.id K) α₂) (h₃ : SemiHom (RingHom.id K) α₃) (h₄ : SemiHom (RingHom.id K) α₄)
    (k₁ : SemiHom (RingHom.id K) β₁) (k₂ : SemiHom (RingHom.id K) β₂) (k₃ : SemiHom (RingHom.id K) β₃) (k₄ : SemiHom (RingHom.id K) β₄)
    (e : ∀ b, α₄ (α₃ (α₂ (α₁ b))) = β₄ (β₃ (β₂ (β₁ b)))) {j : ℕ} (x : Om K A j) :
    h₄.mOm j (h₃.mOm j (h₂.mOm j (h₁.mOm j x))) = k₄.mOm j (k₃.mOm j (k₂.mOm j (k₁.mOm j x))) := by
  have a₂ : SemiHom (RingHom.id K) (α₂.comp α₁) := h₁.comp h₂
  have a₃ : SemiHom (RingHom.id K) (α₃.comp (α₂.comp α₁)) := a₂.comp h₃
  have a₄ : SemiHom (RingHom.id K) (α₄.comp (α₃.comp (α₂.comp α₁))) := a₃.comp h₄
  have b₂ : SemiHom (RingHom.id K) (β₂.comp β₁) := k₁.comp k₂
  have b₃ : SemiHom (RingHom.id K) (β₃.comp (β₂.comp β₁)) := b₂.comp k₃
  have b₄ : SemiHom (RingHom.id K) (β₄.comp (β₃.comp (β₂.comp β₁))) := b₃.comp k₄
  have e' : α₄.comp (α₃.comp (α₂.comp α₁)) = β₄.comp (β₃.comp (β₂.comp β₁)) := RingHom.ext e
  rw [SemiHom.mOm_mOm h₁ h₂ a₂ (fun _ => rfl), SemiHom.mOm_mOm a₂ h₃ a₃ (fun _ => rfl), SemiHom.mOm_mOm a₃ h₄ a₄ (fun _ => rfl),
    SemiHom.mOm_mOm k₁ k₂ b₂ (fun _ => rfl), SemiHom.mOm_mOm b₂ k₃ b₃ (fun _ => rfl), SemiHom.mOm_mOm b₃ k₄ b₄ (fun _ => rfl)]
  have key : ∀ (γ δ : A →+* B₄) (hγ : SemiHom (RingHom.id K) γ) (hδ : SemiHom (RingHom.id K) δ), γ = δ → hγ.mOm j x = hδ.mOm j x := by
    intro γ δ hγ hδ h
    subst h
    rfl
  exact key _ _ a₄ b₄ e'

section Forms

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def fb (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ) : OmU q V a →ₗ[K] OmU (V.ι ≫ q) ⊤ a :=
  (formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V by simp) a).comp (formPull (f := V.ι) rfl V a)

theorem fb_bij (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ) : Function.Bijective (fb q V a) :=
  GlobalTheory.T.forms_restrict_open_bijective q V a

theorem over_res {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q)
    {V : X.Opens} {W : Y.Opens} (h : V ≤ u ⁻¹ᵁ W) : u.resLE W V h ≫ (W.ι ≫ p) = V.ι ≫ q := by
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hu]

theorem fb_nat {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q)
    {V : X.Opens} {W : Y.Opens} (h : V ≤ u ⁻¹ᵁ W) (a : ℕ) (ω : OmU p W a) :
    fb q V a (formRes q h a (formPull hu W a ω)) =
      formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ (u.resLE W V h) ⁻¹ᵁ ⊤ by simp) a
        (formPull (over_res hu h) ⊤ a (fb p W a ω)) := by
  refine mOm_four (semiHom_appSec hu W) (SemiHom.of_algHom (Sec.res q h)) (semiHom_appSec rfl V)
    (SemiHom.of_algHom (Sec.res (V.ι ≫ q) _))
    (semiHom_appSec rfl W) (SemiHom.of_algHom (Sec.res (W.ι ≫ p) _)) (semiHom_appSec (over_res hu h) ⊤)
    (SemiHom.of_algHom (Sec.res (V.ι ≫ q) _)) (fun b => ?_) ω
  have hT1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have hT2 : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := by simp
  have hT3 : (⊤ : V.toScheme.Opens) ≤ (u.resLE W V h) ⁻¹ᵁ ⊤ := by simp
  have key : ∀ (f g : V.toScheme ⟶ Y) (hfg : f = g) (e : ⊤ ≤ f ⁻¹ᵁ W) (e' : ⊤ ≤ g ⁻¹ᵁ W), f.appLE W ⊤ e = g.appLE W ⊤ e' := by
    intro f g hfg e e'
    subst hfg
    rfl
  have e1 := Scheme.Hom.appLE_comp_appLE V.ι u W V ⊤ h hT1
  have e2 := Scheme.Hom.appLE_comp_appLE (u.resLE W V h) W.ι W ⊤ ⊤ hT2 hT3
  have e3 := key _ _ (Scheme.Hom.resLE_comp_ι u h).symm
    (hT1.trans (V.ι.preimage_mono h)) ((hT3.trans ((u.resLE W V h).preimage_mono hT2)))
  exact congrArg (fun φ => φ.hom b) (e1.trans (e3.trans e2.symm))

end Forms

section Main

variable {K : Type} [Field K] {X Y : Scheme.{0}}

abbrev trM (q : X ⟶ Spec (CommRingCat.of K)) (s a : ℕ) :
    CH.Mor (HT.grT (smFun X q) a) ((KS q s {⊤}).ι ⋙ HT.grT (smFun X q) a) (RingHom.id K) :=
  CH.Mor.restrict (HT.grT (smFun X q) a) (KS q s {⊤}).ι

theorem trM_bij (q : X ⟶ Spec (CommRingCat.of K)) (s a : ℕ) (h : a < s) (n : ℕ) : Function.Bijective ((trM q s a).pull n) :=
  GlobalTheory.T.graded_restrict_pull_bijective q {⊤} (by simp) a s h n

theorem ks_top {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} (r : X ⟶ Y) (hr : r ≫ p = q) (s a : ℕ)
    (T) (hT : KS q s {⊤} T) : KS p s {⊤} ((pullM r hr a).G.obj T) :=
  ⟨hT.1, ⊤, rfl, le_of_eq rfl⟩

theorem trM_nat {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} (r : X ⟶ Y) (hr : r ≫ p = q) (s a n : ℕ)
    (hG : ∀ T, KS q s {⊤} T → KS p s {⊤} ((pullM r hr a).G.obj T)) (z : CH.H (HT.grT (smFun Y p) a) n) :
    (morU (pullM r hr a) (U := KS p s {⊤}) (U' := KS q s {⊤}) hG).pull n ((trM p s a).pull n z) =
      (trM q s a).pull n ((pullM r hr a).pull n z) := by
  have h1 := (P.pull_comp (σ'' := RingHom.id K) (trM p s a) (morU (pullM r hr a) (U := KS p s {⊤}) (U' := KS q s {⊤}) hG) n z).1
  have h2 := (P.pull_comp (σ'' := RingHom.id K) (pullM r hr a) (trM q s a) n z).1
  rw [← h1, ← h2]
  rfl

def tq (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ), HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a)
    (m : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a : ℕ),
      CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a) ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a)
        (RingHom.id K))
    (hm : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a n : ℕ), Function.Bijective ((m q V s a).pull n))
    (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) :
    CH.H (FV q V a) a ≃ₗ[K] OmU q V a :=
  haveI : IsAffine V.toScheme := hV
  (LinearEquiv.ofBijective ((m q V (a + 1) a).pull a) (hm q V (a + 1) a a)).symm ≪≫ₗ
    (LinearEquiv.ofBijective ((trM (V.ι ≫ q) (a + 1) a).pull a) (trM_bij _ _ _ (Nat.lt_succ_self a) a)).symm ≪≫ₗ
      e (V.ι ≫ q) a ≪≫ₗ (LinearEquiv.ofBijective (fb q V a) (fb_bij q V a)).symm

theorem tq_spec (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ), HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a)
    (m : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a : ℕ),
      CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a) ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a)
        (RingHom.id K))
    (hm : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a n : ℕ), Function.Bijective ((m q V s a).pull n))
    (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) (z : HT.Hdg (V.ι ≫ q) a a) :
    haveI : IsAffine V.toScheme := hV
    fb q V a (tq e m hm q V hV a ((m q V (a + 1) a).pull a ((trM (V.ι ≫ q) (a + 1) a).pull a z))) = e (V.ι ≫ q) a z := by
  haveI : IsAffine V.toScheme := hV
  have h1 := (LinearEquiv.ofBijective ((m q V (a + 1) a).pull a) (hm q V (a + 1) a a)).symm_apply_apply
    ((trM (V.ι ≫ q) (a + 1) a).pull a z)
  have h2 := (LinearEquiv.ofBijective ((trM (V.ι ≫ q) (a + 1) a).pull a) (trM_bij _ _ _ (Nat.lt_succ_self a) a)).symm_apply_apply z
  have h4 : tq e m hm q V hV a ((m q V (a + 1) a).pull a ((trM (V.ι ≫ q) (a + 1) a).pull a z)) =
      (LinearEquiv.ofBijective (fb q V a) (fb_bij q V a)).symm (e (V.ι ≫ q) a z) := by
    refine congrArg (fun w => (LinearEquiv.ofBijective (fb q V a) (fb_bij q V a)).symm (e (V.ι ≫ q) a w)) ?_
    exact (congrArg (LinearEquiv.ofBijective ((trM (V.ι ≫ q) (a + 1) a).pull a) (trM_bij _ _ _ (Nat.lt_succ_self a) a)).symm h1).trans h2
  rw [h4]
  exact (LinearEquiv.ofBijective (fb q V a) (fb_bij q V a)).apply_symm_apply _

end Main


set_option maxHeartbeats 400000 in
theorem term_aff : ∀ (K : Type) [Field K] [CharZero K],
    ∃ t : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (V : X.Opens), IsAffineOpen V → ∀ a : ℕ,
      CH.H (FV q V a) a ≃ₗ[K] OmU q V a,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (V : X.Opens) (W : Y.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ u ⁻¹ᵁ W)
      (a : ℕ) (hG : ∀ T, KS q (a + 1) {V} T → KS p (a + 1) {W} ((pullM u hu a).G.obj T)) (x : CH.H (FV p W a) a),
      t q V hV a ((morU (pullM u hu a) (U := KS p (a + 1) {W}) (U' := KS q (a + 1) {V}) hG).pull a x) =
        formRes q h a (formPull hu W a (t p W hW a x)) := by
  intro K _ _
  obtain ⟨e, ε, -, he, -, -⟩ := CrystallineSemistableComparison.Om.L2.hodge_affine_iso_sign K
  obtain ⟨m, hm, hn⟩ := GlobalTheory.T.restrict_graded_pull_natural K
  refine ⟨fun q _ V hV a => tq (@e) (@m) (@hm) q V hV a, ?_⟩
  intro X Y q p _ _ u hu V W hV hW h a hG x
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine W.toScheme := hW
  obtain ⟨y, rfl⟩ := (hm p W (a + 1) a a).2 x
  obtain ⟨z, rfl⟩ := (trM_bij (W.ι ≫ p) (a + 1) a (Nat.lt_succ_self a) a).2 y
  have hh := over_res hu h
  have hG' := ks_top (u.resLE W V h) hh (a + 1) a
  refine (fb_bij q V a).1 ?_
  have s1 := hn q p u hu V W h hh (a + 1) a hG hG' a ((trM (W.ι ≫ p) (a + 1) a).pull a z)
  have s2 := trM_nat (u.resLE W V h) hh (a + 1) a a hG' z
  have s3 := tq_spec (@e) (@m) (@hm) q V hV a ((pullM (u.resLE W V h) hh a).pull a z)
  have s4 := tq_spec (@e) (@m) (@hm) p W hW a z
  have s5 := fb_nat hu h a (tq (@e) (@m) (@hm) p W hW a ((m p W (a + 1) a).pull a ((trM (W.ι ≫ p) (a + 1) a).pull a z)))
  have s6 := he _ _ (u.resLE W V h) hh a z
  have s7 := s1.symm.trans (congrArg ((m q V (a + 1) a).pull a) s2)
  have s8 := (congrArg (fun w => fb q V a (tq (@e) (@m) (@hm) q V hV a w)) s7).trans s3
  have s9 := s5.trans (congrArg (fun w => formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ (u.resLE W V h) ⁻¹ᵁ ⊤ by simp) a
        (formPull (over_res hu h) ⊤ a w)) s4)
  exact s8.trans (s6.trans s9.symm)

end CrystallineSemistableComparison.Om.Nt2.TermAff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapMPull
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm

section Cap
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_mono {V W : X.Opens} (h : V ≤ W) (T : Thick (smFun X q))
    (hT : InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) V T) :
    InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) W T :=
  fun x hx => h (hT hx)

theorem coe_capO {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) :
    ((capO U i : X.Opens) : Set X) = ⋂ k, (U (i k) : Set X) := by
  have h : capO U i = Finset.univ.inf fun k => U (i k) := by
    rw [Finset.inf_univ_eq_iInf]; rfl
  rw [h, TopologicalSpace.Opens.coe_finset_inf]
  ext x
  simp [Finset.inf_eq_iInf]

theorem inU_capO {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (smFun X q)) :
    InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (capO U i) T ↔
      ∀ k, InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (U (i k)) T := by
  constructor
  · exact fun h k => inU_mono q (capO_le U i k) T h
  · intro h x hx
    have : (pt T x) ∈ ((capO U i : X.Opens) : Set X) := by
      rw [coe_capO]
      exact Set.mem_iInter.2 fun k => h k hx
    exact this

variable (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι)

theorem kc_of_ks (T : Thick (smFun X q)) (h : KS q (a + 1) {capO U.U i} T) : KC q U a T := by
  obtain ⟨h1, V, rfl, h2⟩ := h
  exact ⟨h1, U.U (i 0), ⟨_, rfl⟩, inU_mono q (capO_le U.U i 0) T h2⟩

theorem ks_of_cap (T : (KC q U a).FullSubcategory) (h : capT (Vk q U a) i T) : KS q (a + 1) {capO U.U i} T.obj :=
  ⟨T.property.1, _, rfl, (inU_capO q U.U i T.obj).2 h⟩

def capG : (KS q (a + 1) {capO U.U i}).FullSubcategory ⥤ (capT (Vk q U a) i).FullSubcategory :=
  (capT (Vk q U a) i).lift ((KC q U a).lift (KS q (a + 1) {capO U.U i}).ι fun T => kc_of_ks q U a n i _ T.property)
    fun T => by
      obtain ⟨h1, V, rfl, h2⟩ := T.property
      exact (inU_capO q U.U i T.obj).1 h2

def capH : (capT (Vk q U a) i).FullSubcategory ⥤ (KS q (a + 1) {capO U.U i}).FullSubcategory :=
  (KS q (a + 1) {capO U.U i}).lift ((capT (Vk q U a) i).ι ⋙ (KC q U a).ι) fun T => ks_of_cap q U a n i T.obj T.property

def capE : (KS q (a + 1) {capO U.U i}).FullSubcategory ≌ (capT (Vk q U a) i).FullSubcategory :=
  CategoryTheory.Equivalence.mk (capG q U a n i) (capH q U a n i)
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl))

def capM : CH.Mor ((capT (Vk q U a) i).ι ⋙ Fk q U a) ((KS q (a + 1) {capO U.U i}).ι ⋙ HT.grT (smFun X q) a) (RingHom.id K) where
  G := capG q U a n i
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem capM_bij (r : ℕ) : Function.Bijective ((capM q U a n i).pull r) := by
  haveI : (capM q U a n i).G.IsLeftAdjoint := (capE q U a n i).isLeftAdjoint_functor
  exact CrystallineSemistableComparison.P.adj_mor (capM q U a n i) (fun _ => Function.bijective_id) r

end Cap
end GlobalTheory.CompanionTheory.OmGlobTerm

noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm

section Nat
variable {K : Type} [CommRing K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

theorem ks_pull (u : X ⟶ Y) (hu : u ≫ p = q) {V : X.Opens} {W : Y.Opens} (h : V ≤ u ⁻¹ᵁ W) (s a : ℕ) (T : Thick (smFun X q))
    (hT : KS q s {V} T) : KS p s {W} ((pullM u hu a).G.obj T) := by
  obtain ⟨h1, V', rfl, h2⟩ := hT
  exact ⟨h1, W, rfl, fun x hx => h (h2 hx)⟩

theorem capM_res (U : Cov q) (a m n : ℕ) (i : Fin (n + 1) → U.ι) (θ : Fin (m + 1) → Fin (n + 1))
    (x : HU (Fk q U a) (capT (Vk q U a) (i ∘ θ)) a) :
    (capM q U a n i).pull a ((resU (Fk q U a) (U := capT (Vk q U a) (i ∘ θ)) (V := capT (Vk q U a) i) fun T hT k => hT (θ k)).pull a x) =
      (resU (HT.grT (smFun X q) a) (U := KS q (a + 1) {capO U.U (i ∘ θ)}) (V := KS q (a + 1) {capO U.U i}) (by
        rintro T ⟨h1, V', rfl, h2⟩
        exact ⟨h1, _, rfl, inU_mono q (capO_comp U.U i θ) T h2⟩)).pull a ((capM q U a m (i ∘ θ)).pull a x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem capM_pull (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι) (a : ℕ)
    (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T)) (n : ℕ) (i : Fin (n + 1) → U.ι)
    (hG' : ∀ T, capT (Vk q U a) i T →
      capT (Vk p W a) (τ ∘ i) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T))
    (h : ∀ T, KS q (a + 1) {capO U.U i} T → KS p (a + 1) {capO W.U (τ ∘ i)} ((pullM u hu a).G.obj T))
    (x : HU (Fk p W a) (capT (Vk p W a) (τ ∘ i)) a) :
    (capM q U a n i).pull a ((morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
        (U' := capT (Vk q U a) i) hG').pull a x) =
      (morU (pullM u hu a) (U := KS p (a + 1) {capO W.U (τ ∘ i)}) (U' := KS q (a + 1) {capO U.U i}) h).pull a
        ((capM p W a n (τ ∘ i)).pull a x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end Nat
end GlobalTheory.CompanionTheory.OmGlobTerm

noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm

section Id
variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def idT (hu : 𝟙 X ≫ q = q) (T : Thick (smFun X q)) : T ⟶ (smMor (𝟙 X) hu).functor.obj T :=
  mkH (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (T := T) (T' := (smMor (𝟙 X) hu).functor.obj T) (RingHom.id _) (fun _ => rfl) ⟨Ideal.map_le_iff_le_comap.2 (fun x hx => hx), fun x hx => rfl⟩ (fun x hx => hx) (by
    have e : CommRingCat.ofHom (Ideal.quotientMap ((smMor (𝟙 X) hu).functor.obj T).J (RingHom.id T.B) (fun x hx => hx)) = 𝟙 (CommRingCat.of (T.B ⧸ T.J)) := by
      refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl))
    refine Eq.trans (congrArg (fun f => (ConcreteCategory.hom ((nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)).Pt.map f)) T.y) e) ?_
    refine Eq.trans (congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _)) ((nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)).Pt.map_id _)) T.y) ?_
    exact Subtype.ext (Prod.ext rfl (Category.comp_id _).symm))

theorem morU_id (hu : 𝟙 X ≫ q = q) (a : ℕ) (Q Q' : ObjectProperty (Thick (smFun X q)))
    (h : ∀ T, Q' T → Q ((pullM (𝟙 X) hu a).G.obj T)) (hle : Q' ≤ Q) (n : ℕ) (x) :
    (morU (pullM (𝟙 X) hu a) (U := Q) (U' := Q') h).pull n x = (resU (HT.grT (smFun X q) a) hle).pull n x := by
  symm
  refine CrystallineSemistableComparison.P.prism (resU (HT.grT (smFun X q) a) hle) (morU (pullM (𝟙 X) hu a) (U := Q) (U' := Q') h)
    { app := fun T => ObjectProperty.homMk (idT hu T.obj)
      naturality := fun T T' f => ?_ } ?_ n x
  · refine ObjectProperty.hom_ext _ ?_
    exact hom_ext (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) rfl
  · intro T x
    obtain ⟨y, hy, rfl⟩ := HT.sq_surj _ _ x
    rfl

end Id
end GlobalTheory.CompanionTheory.OmGlobTerm
end
end
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm.AssemblyHe1

theorem capO_isAffineOpen {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q)
    {n : ℕ} (i : Fin (n + 1) → U.ι) : IsAffineOpen (capO U.U i) := by
  classical
  have h := U.inter (Finset.image i Finset.univ) ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ 0)⟩
  have e : (⨅ α ∈ Finset.image i Finset.univ, U.U α) = capO U.U i := by
    refine le_antisymm ?_ ?_
    · exact le_iInf fun k => iInf₂_le (i k) (Finset.mem_image_of_mem i (Finset.mem_univ k))
    · refine le_iInf₂ fun α hα => ?_
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
      exact capO_le U.U i k
  rwa [e] at h

def capEquiv {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) : HU (Fk q U a) (capT (Vk q U a) i) a ≃ₗ[K] CH.H (FV q (capO U.U i) a) a :=
  LinearEquiv.ofBijective ((capM q U a n i).pull a) (capM_bij q U a n i a)

theorem term : ∀ (K : Type) [Field K] [CharZero K],
    ∃ t : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι),
      HU (Fk q U a) (capT (Vk q U a) i) a ≃ₗ[K] OmU q (capO U.U i) a,
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a m n : ℕ) (i : Fin (n + 1) → U.ι)
      (θ : Fin (m + 1) → Fin (n + 1)) (x : HU (Fk q U a) (capT (Vk q U a) (i ∘ θ)) a),
      t q U a n i ((resU (Fk q U a) (U := capT (Vk q U a) (i ∘ θ)) (V := capT (Vk q U a) i) fun T hT k => hT (θ k)).pull a x) =
        formRes q (capO_comp U.U i θ) a (t q U a m (i ∘ θ) x)) ∧
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
      (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ)
      (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T)) (n : ℕ) (i : Fin (n + 1) → U.ι)
      (hG' : ∀ T, capT (Vk q U a) i T →
        capT (Vk p W a) (τ ∘ i) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T))
      (x : HU (Fk p W a) (capT (Vk p W a) (τ ∘ i)) a),
      t q U a n i ((morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
        (U' := capT (Vk q U a) i) hG').pull a x) =
        formRes q (hτ n i) a (formPull hu (capO W.U (τ ∘ i)) a (t p W a n (τ ∘ i) x)) := by
  intro K _ _
  obtain ⟨t0, h0⟩ := CrystallineSemistableComparison.Om.Nt2.TermAff.term_aff K
  refine ⟨fun {X} q _ U a n i => (capEquiv q U a n i).trans (t0 q (capO U.U i) (capO_isAffineOpen q U i) a), ?_, ?_⟩
  · intro X q _ U a m n i θ x
    have hle : KS q (a + 1) {capO U.U i} ≤ KS q (a + 1) {capO U.U (i ∘ θ)} := by
      rintro T ⟨h1, V', rfl, h2⟩
      exact ⟨h1, _, rfl, inU_mono q (capO_comp U.U i θ) T h2⟩
    have hG : ∀ T, KS q (a + 1) {capO U.U i} T → KS q (a + 1) {capO U.U (i ∘ θ)} ((pullM (𝟙 X) (Category.id_comp q) a).G.obj T) :=
      fun T hT => ks_pull (𝟙 X) (Category.id_comp q) (capO_comp U.U i θ) (a + 1) a T hT
    have e1 := capM_res U a m n i θ x
    have e2 := morU_id (Category.id_comp q) a _ _ hG hle a ((capM q U a m (i ∘ θ)).pull a x)
    have e3 := h0 q q (𝟙 X) (Category.id_comp q) (capO U.U i) (capO U.U (i ∘ θ)) (capO_isAffineOpen q U i)
      (capO_isAffineOpen q U (i ∘ θ)) (capO_comp U.U i θ) a hG ((capM q U a m (i ∘ θ)).pull a x)
    have e4 := formPull_id q a (capO U.U (i ∘ θ)) (t0 q (capO U.U (i ∘ θ)) (capO_isAffineOpen q U (i ∘ θ)) a ((capM q U a m (i ∘ θ)).pull a x))
    change t0 q (capO U.U i) _ a ((capM q U a n i).pull a _) = formRes q _ a (t0 q (capO U.U (i ∘ θ)) _ a ((capM q U a m (i ∘ θ)).pull a x))
    rw [e1, ← e2, e3]
    exact congrArg (formRes q (capO_comp U.U i θ) a) e4
  · intro X Y q p _ _ u hu U W τ hτ a hG n i hG' x
    have h : ∀ T, KS q (a + 1) {capO U.U i} T → KS p (a + 1) {capO W.U (τ ∘ i)} ((pullM u hu a).G.obj T) :=
      fun T hT => ks_pull u hu (hτ n i) (a + 1) a T hT
    have e1 := capM_pull u hu U W τ a hG n i hG' h x
    have e3 := h0 q p u hu (capO U.U i) (capO W.U (τ ∘ i)) (capO_isAffineOpen q U i)
      (capO_isAffineOpen p W (τ ∘ i)) (hτ n i) a h ((capM p W a n (τ ∘ i)).pull a x)
    change t0 q (capO U.U i) _ a ((capM q U a n i).pull a _) = formRes q _ a (formPull hu _ a (t0 p (capO W.U (τ ∘ i)) _ a ((capM p W a n (τ ∘ i)).pull a x)))
    rw [e1, e3]

end GlobalTheory.CompanionTheory.OmGlobTerm.AssemblyHe1
