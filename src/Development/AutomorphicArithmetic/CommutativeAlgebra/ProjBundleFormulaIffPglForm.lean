module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOneIffTwistEquiv
public import Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineActionFstTwistEquiv
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfMayerVietorisCover

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ProjBundleFormulaIffPglForm
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section

namespace UpperTheory.PullPf

private def unitOf {M : ℕ} {A : CommRingCat.{0}} {x y : Ob (XC M) A} (f : x ⟶ y) : (A : Type)ˣ := f.1

private def vec {M : ℕ} {A : CommRingCat.{0}} (x : Ob (XC M) A) : Fin M → A := (show Um M A from x.pt).1

private theorem unitOf_spec {M : ℕ} {A : CommRingCat.{0}} {x y : Ob (XC M) A} (f : x ⟶ y) (i : Fin M) :
    vec x i = (unitOf f : A) * vec y i :=
  congrFun (congrArg Subtype.val f.2) i

private def tauF (M : ℕ) (A : CommRingCat.{0}) : Ob (XC M) A ⥤ Um M A where
  obj x := x.pt
  map {x y} f := ⟨(1, unitOf f), by
    change ((1 : GL (Fin M) A) : Matrix (Fin M) (Fin M) A).mulVec (vec x) = (unitOf f : A) • vec y
    funext i
    simpa using unitOf_spec f i⟩
  map_id x := Subtype.ext rfl
  map_comp {x y z} f g := Subtype.ext (Prod.ext (mul_one _).symm (mul_comm _ _))

private def tau (M : ℕ) : (XC M).cat ⟶ pglCat M where
  app A := (tauF M A).toCatHom
  naturality {A B} f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
    refine Subtype.ext (Prod.ext ?_ rfl)
    exact (map_one (Matrix.GeneralLinearGroup.map f.hom)).symm

private def tauS (M : ℕ) : spc (XC M) ⟶ PGL M := ofCatMap (tau M)

private theorem sq (S : Spc) (M : ℕ) :
    Sp.fst S (XC M) ≫ triv S M = (Sp.snd S (XC M) ≫ tauS M) ≫ PGL.pr M := by
  ext k T x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun a b h => ?_)
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private theorem um_hom_val {M : ℕ} {A : Type} [CommRing A] {v v' w w' : Um M A} (hv : v = v') (hw : w = w')
    (f : v ⟶ w) (f' : v' ⟶ w') (h : HEq f f') : f.1 = f'.1 := by
  subst hv hw
  rw [eq_of_heq h]

private theorem tau_inj {M k : ℕ} {A : CommRingCat.{0}} (w w' : Fin (k + 1) ⥤ Ob (XC M) A)
    (h : w ⋙ tauF M A = w' ⋙ tauF M A) : w = w' := by
  have ho : ∀ i, w.obj i = w'.obj i := fun i => by
    have := congrArg (fun F : Fin (k + 1) ⥤ Um M A => F.obj i) h
    exact congrArg Ob.mk this
  refine CategoryTheory.Functor.hext ho (fun a b f => Ob.hom_heq (ho a) (ho b) _ _ ?_)
  have hh : HEq ((w ⋙ tauF M A).map f) ((w' ⋙ tauF M A).map f) := by rw [h]
  have := um_hom_val (congrArg Ob.pt (ho a)) (congrArg Ob.pt (ho b)) _ _ hh
  exact congrArg Prod.snd this

private theorem tau_surj {M k : ℕ} {A : CommRingCat.{0}} (y : Fin (k + 1) ⥤ Um M A)
    (hy : y ⋙ Um.toGL M A = (Functor.const _).obj (SingleObj.star _)) :
    ∃ w : Fin (k + 1) ⥤ Ob (XC M) A, w ⋙ tauF M A = y := by
  have h1 : ∀ {a b : Fin (k + 1)} (f : a ⟶ b), (y.map f).1.1 = 1 := fun {a b} f => by
    have := Functor.congr_hom hy f
    erw [eqToHom_refl, Category.id_comp, Category.comp_id] at this
    exact this
  refine ⟨{ obj := fun i => ⟨y.obj i⟩
            map := fun {a b} f => ⟨show (XC M).G.obj A from (y.map f).1.2, ?_⟩
            map_id := fun a => ?_
            map_comp := fun {a b c} f g => ?_ }, ?_⟩
  · refine Subtype.ext (funext fun i => ?_)
    have := congrFun (y.map f).2 i
    rw [h1 f] at this
    have h2 : (y.obj a).1 i = ((y.map f).1.2 : A) * (y.obj b).1 i := by simpa using this
    exact h2
  · refine Subtype.ext ?_
    change (y.map (𝟙 a)).1.2 = 1
    rw [y.map_id]
    rfl
  · refine Subtype.ext ?_
    change (y.map (f ≫ g)).1.2 = (y.map f).1.2 * (y.map g).1.2
    rw [y.map_comp, mul_comm]
    rfl
  · refine CategoryTheory.Functor.hext (fun _ => rfl) (fun a b f => heq_of_eq ?_)
    exact Subtype.ext (Prod.ext (h1 f).symm rfl)

private def uMap (S : Spc) (M : ℕ) : Sp S (XC M) ⟶ pullback (triv S M) (PGL.pr M) :=
  pullback.lift (Sp.fst S (XC M)) (Sp.snd S (XC M) ≫ tauS M) (sq S M)

private theorem sx_comp {X Y Z : Spc} (f : X ⟶ Y) (g : Y ⟶ Z) {k : ℕ} {T : Scheme.{0}} (x : Sx X k T) :
    Sx.map g (Sx.map f x) = Sx.map (f ≫ g) x := rfl

private theorem u_fst (S : Spc) (M : ℕ) {k : ℕ} {T : Scheme.{0}} (c : Sx (Sp S (XC M)) k T) :
    Sx.map (pullback.fst _ _) (Sx.map (uMap S M) c) = c.1 := by
  rw [sx_comp, uMap, pullback.lift_fst]
  rfl

private theorem u_snd (S : Spc) (M : ℕ) {k : ℕ} {T : Scheme.{0}} (c : Sx (Sp S (XC M)) k T) :
    Sx.map (pullback.snd _ _) (Sx.map (uMap S M) c) = Sx.map (tauS M) c.2 := by
  rw [sx_comp, uMap, pullback.lift_snd]
  rfl

private instance isIso_u (S : Spc) (M : ℕ) : IsIso (uMap S M) := by
  refine UpperTheory.isIso_of_bijective_on_simplices _ fun k T => ⟨fun a b h => ?_, fun z => ?_⟩
  · have h1 := congrArg (Sx.map (pullback.fst _ _)) h
    have h2 := congrArg (Sx.map (pullback.snd _ _)) h
    rw [u_fst, u_fst] at h1
    rw [u_snd, u_snd] at h2
    exact Prod.ext h1 (tau_inj _ _ h2)
  · have hc : Sx.map (triv S M) (Sx.map (pullback.fst _ _) z) = Sx.map (PGL.pr M) (Sx.map (pullback.snd _ _) z) := by
      rw [sx_comp, sx_comp, pullback.condition]
    obtain ⟨w, hw⟩ := tau_surj (M := M) (k := k) (A := Scheme.Γ.obj (op T))
      (Sx.map (pullback.snd (triv S M) (PGL.pr M)) z) hc.symm
    refine ⟨(Sx.map (pullback.fst _ _) z, w), ?_⟩
    obtain ⟨z0, -, hu⟩ := UpperTheory.simplices_pullback_existsUnique_of_map_eq (triv S M) (PGL.pr M) k T _ _ hc
    exact (hu _ ⟨u_fst S M (Sx.map (pullback.fst _ _) z, w), (u_snd S M (Sx.map (pullback.fst _ _) z, w)).trans hw⟩).trans
      (hu z ⟨rfl, rfl⟩).symm

private theorem tau_line (M : ℕ) : tauS M ≫ PGL.line M = lineOf (chiX M) := rfl

private theorem u_line (S : Spc) (M : ℕ) :
    uMap S M ≫ pullback.snd (triv S M) (PGL.pr M) ≫ PGL.line M = Sp.line S (chiX M) := by
  rw [← Category.assoc, uMap, pullback.lift_snd, Category.assoc, tau_line]

end UpperTheory.PullPf

open UpperTheory.PullPf in
theorem UpperTheory.projBundleFormula_iff_pglForm :
    ∀ (q : ℕ) [NeZero q] (S : Spc) (M : ℕ), Inv q S → (PBF q S M ↔ Pbf q S M) := by
  intro q _ S M hS
  have hP : Inv q (pullback (triv S M) (PGL.pr M)) :=
    fun U ⟨x⟩ => hS U ⟨Sx.map (pullback.fst (triv S M) (PGL.pr M)) x⟩
  have hX : Inv q (Sp S (XC M)) := fun U ⟨x⟩ => hS U ⟨x.1⟩
  have hf : uMap S M ≫ pullback.fst _ _ = Sp.fst S (XC M) := pullback.lift_fst _ _ _
  constructor
  · intro h
    have h1 := UpperTheory.lerayHirsch_of_iso_square q (pullback.fst _ _) (Sp.fst S (XC M)) (uMap S M) (𝟙 S)
      (by rw [hf, Category.comp_id]) _ _ _ h
    have e : ∀ j : ℕ, pull _ (uMap S M) (tw q (j : ℤ)) (2 * (j : ℤ))
        (cpow q (c1 q (pullback.snd (triv S M) (PGL.pr M) ≫ PGL.line M)) j) =
        cpow q (c1 q (Sp.line S (chiX M))) j := fun j => by
      rw [UpperTheory.pull_cupPow_eq_cupPow_pull q _ _ j hP, (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hP, u_line]
    unfold Pbf
    simpa only [e] using h1
  · intro h
    have h1 := UpperTheory.lerayHirsch_of_iso_square q (Sp.fst S (XC M)) (pullback.fst _ _) (inv (uMap S M)) (𝟙 S)
      (by rw [Category.comp_id, IsIso.inv_comp_eq, hf]) _ _ _ h
    have e : ∀ j : ℕ, pull _ (inv (uMap S M)) (tw q (j : ℤ)) (2 * (j : ℤ))
        (cpow q (c1 q (Sp.line S (chiX M))) j) =
        cpow q (c1 q (pullback.snd (triv S M) (PGL.pr M) ≫ PGL.line M)) j := fun j => by
      rw [UpperTheory.pull_cupPow_eq_cupPow_pull q _ _ j hX, (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hX, ← u_line, IsIso.inv_hom_id_assoc]
    unfold UpperTheory.Pbf.PBF
    simpa only [e] using h1

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFunctionFieldStatementOne
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

set_option autoImplicit false

private theorem isIntegral_map_iff {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (B : Subalgebra ℂ K) (y : L) :
    IsIntegral (B.map (IsScalarTower.toAlgHom ℂ K L)) y ↔ IsIntegral B y := by
  let j := IsScalarTower.toAlgHom ℂ K L
  let e : B →+* B.map j := (B.equivMapOfInjective j j.toRingHom.injective).toAlgHom.toRingHom
  letI : Algebra B (B.map j) := e.toAlgebra
  haveI : IsScalarTower B (B.map j) L := .of_algebraMap_eq fun a => rfl
  haveI : Algebra.IsIntegral B (B.map j) := ⟨fun b => by
    obtain ⟨a, rfl⟩ := (B.equivMapOfInjective j j.toRingHom.injective).surjective b
    exact isIntegral_algebraMap (x := a)⟩
  exact ⟨fun h => isIntegral_trans y h, fun h => h.tower_top⟩

private theorem dualNumberPoint_preimage_top_of_reduction {d : ℕ} {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ}
    [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] {c : Y ⟶ Z} (hc : c ≫ s = s') [IsFinite c] [Etale c]
    [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s')
    (j : Z.functionField →ₐ[ℂ] Y.functionField)
    (hj : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
      j ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g))
    {F : Type} [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [IsScalarTower ℂ F Z.functionField]
    (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x)
    (hU : IsAffCover s U (rB ℂ Z.functionField x)) :
    IsAffCover s' (fun i => c ⁻¹ᵁ U i) (R2 x j) := by
  letI : Algebra Z.functionField Y.functionField := j.toRingHom.toAlgebra
  letI : Algebra F Y.functionField :=
    ((algebraMap Z.functionField Y.functionField).comp (algebraMap F Z.functionField)).toAlgebra
  haveI : IsScalarTower ℂ Z.functionField Y.functionField := .of_algebraMap_eq fun r => (j.commutes r).symm
  haveI : IsScalarTower F Z.functionField Y.functionField := .of_algebraMap_eq fun r => rfl
  haveI : IsScalarTower ℂ F Y.functionField := .of_algebraMap_eq fun r => by
    change algebraMap ℂ Y.functionField r = j (algebraMap F Z.functionField (algebraMap ℂ F r))
    rw [← IsScalarTower.algebraMap_apply ℂ F Z.functionField, j.commutes]
  have hjeq : IsScalarTower.toAlgHom ℂ Z.functionField Y.functionField = j := AlgHom.ext fun _ => rfl
  have e : rB ℂ Y.functionField x = R2 x j := by
    funext I
    ext y
    change IsIntegral (rA ℂ x I) y ↔ IsIntegral ((rB ℂ Z.functionField x I).map j) y
    rw [UpperTheory.A.isIntegral_rB_iff (K := Z.functionField) x I y, ← hjeq, isIntegral_map_iff]
  rw [← e]
  exact (UpperTheory.A.isFinCover_pull hc hK hL (fun V hV hV' g => (hj V hV hV' g).symm) hx hU).2

theorem UpperTheory.etaleCorrespondence_functionField_statement_one :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)), IsAffCover s' (fun i => c2 ⁻¹ᵁ U i) (R2 x j2) := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU
  exact dualNumberPoint_preimage_top_of_reduction h2 hK hL j2 g2 x U hx hU
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ComplexPointsBijectiveAlgHomAffineOpen
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.TopForm ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi in
private theorem germ_algX {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (V : X.Opens) (hg : genericPoint X ∈ V) (a : ℂ) :
    (X.presheaf.germ V (genericPoint X) hg).hom (algX p V a) = @algebraMap ℂ X.functionField _ _ (ffAlg p) a := by
  have h := congrArg (fun φ => φ a) (GlobalTheory.TopForm.resG_comp_algX p (le_top : V ≤ ⊤))
  simp only [RingHom.comp_apply] at h
  rw [← h]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG, TopCat.Presheaf.germ_res_apply]
  simp only [algX, GlobalTheory.PD.ffAlg, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, Scheme.Hom.appLE]
  simp only [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  rfl

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue in
theorem UpperTheory.complexPoints_bijective_algHom_affineOpen :
    ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) [inst : Algebra ℂ X.functionField], inst = ffAlg p → ∀ (V : X.Opens), IsAffineOpen V → ∀ (hg : genericPoint X ∈ V) (B : Subalgebra ℂ X.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hg).hom f = y) → (∀ e : B →ₐ[ℂ] ℂ, ∃! y : CxPts p (RingHom.id ℂ), UpperTheory.A.Mt p V hg B e y) ∧ (∀ y ∈ CxPts.ptsIn p (RingHom.id ℂ) V, ∃! e : B →ₐ[ℂ] ℂ, UpperTheory.A.Mt p V hg B e y) := by
  intro X _ p inst hinst V hV hg B hB
  subst hinst
  set g := (X.presheaf.germ V (genericPoint X) hg).hom with hgdef
  have ginj : Function.Injective g := germ_injective_of_isIntegral X (genericPoint X) hg
  have gB : ∀ f, g f ∈ B := fun f => (hB _).2 ⟨f, rfl⟩
  let gr : Γ(X, V) →+* B := g.codRestrict B gB
  have grbij : Function.Bijective gr := by
    refine ⟨fun x y hxy => ginj (congrArg Subtype.val hxy), fun b => ?_⟩
    obtain ⟨f, hf⟩ := (hB b.1).1 b.2
    exact ⟨f, Subtype.ext hf⟩
  let eqv : Γ(X, V) ≃+* B := RingEquiv.ofBijective gr grbij
  have eqv_apply : ∀ f, eqv f = ⟨g f, gB f⟩ := fun f => rfl
  have alg_eq : ∀ a : ℂ, (algebraMap ℂ B a) = eqv (algX p V a) := by
    intro a
    apply Subtype.ext
    rw [eqv_apply]
    exact (germ_algX p V hg a).symm
  constructor
  · intro e
    let φ : Γ(X, V) →+* ℂ := (e : B →+* ℂ).comp (eqv : Γ(X, V) →+* B)
    have hφ : ∀ a : ℂ, φ (algX p V a) = RingHom.id ℂ a := by
      intro a
      change e (eqv (algX p V a)) = a
      rw [← alg_eq]
      exact e.commutes a
    refine ⟨CxPts.ofHom hV φ hφ, ⟨CxPts.ofHom_mem hV φ hφ, fun f hf => ?_⟩, ?_⟩
    · rw [CxPts.ev_ofHom]
      rfl
    · rintro y ⟨hy, hye⟩
      apply Subtype.ext
      apply GlobalTheory.Points.ext_of_valR hV hy (CxPts.ofHom_mem hV φ hφ)
      intro f
      change CxPts.ev p (RingHom.id ℂ) V f y = CxPts.ev p (RingHom.id ℂ) V f (CxPts.ofHom hV φ hφ)
      rw [CxPts.ev_ofHom, ← hye f (gB f)]
      rfl
  · intro y hy
    let e0 : B →+* ℂ := (CxPts.evHom hy).comp (eqv.symm : B →+* Γ(X, V))
    have he0 : ∀ a : ℂ, e0 (algebraMap ℂ B a) = algebraMap ℂ ℂ a := by
      intro a
      change CxPts.evHom hy (eqv.symm (algebraMap ℂ B a)) = a
      rw [alg_eq, RingEquiv.symm_apply_apply, ← CxPts.ev_eq hy, CxPts.ev_algX hy]
      rfl
    let e : B →ₐ[ℂ] ℂ := { e0 with commutes' := he0 }
    refine ⟨e, ⟨hy, fun f hf => ?_⟩, ?_⟩
    · change CxPts.evHom hy (eqv.symm ⟨g f, hf⟩) = _
      rw [show (⟨g f, hf⟩ : B) = eqv f from rfl, RingEquiv.symm_apply_apply, CxPts.ev_eq hy]
    · rintro e' ⟨_, he'⟩
      apply AlgHom.ext
      intro b
      obtain ⟨f, hf⟩ := (hB b.1).1 b.2
      have hb : b = ⟨g f, gB f⟩ := Subtype.ext hf.symm
      subst hb
      rw [he' f (gB f)]
      change _ = CxPts.evHom hy (eqv.symm (eqv f))
      rw [RingEquiv.symm_apply_apply, CxPts.ev_eq hy]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LeraHirschOfLocalCoverOfInf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.Glue

private theorem map_incl (E : Spc) {a : Act} {Q R : Pred a} (h : Q.Le R) :
    Sp.map E (inclLe h) ≫ Sp.map E (incl R) = Sp.map E (incl Q) := by
  rfl

private theorem map_inclLe (E : Spc) {a : Act} {Q R S : Pred a} (h : Q.Le R) (h' : R.Le S) (h'' : Q.Le S) :
    Sp.map E (inclLe h) ≫ Sp.map E (inclLe h') = Sp.map E (inclLe h'') := by
  rfl

private theorem comap_le {c a : Act} (π : Act.Hom c a) {Q' Q : Pred a} (h : Q'.Le Q) : (Q'.comap π).Le (Q.comap π) :=
  fun A _ hx => h A _ hx

private theorem sq (E : Spc) {c a : Act} (π : Act.Hom c a) {Q' Q : Pred a} (h : Q'.Le Q) :
    IsPullback (Sp.map E (inclLe (comap_le π h))) (Sp.map E (π.sub Q')) (Sp.map E (π.sub Q)) (Sp.map E (inclLe h)) := by
  refine UpperTheory.stackProduct_isPullback_of_actionPullback E _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · intro A x y hxy
    have e : π.d.app A x.1 = y.1 := congrArg Subtype.val hxy
    have hx : Q'.P A (π.d.app A x.1) := by
      rw [e]
      exact y.2
    refine ⟨⟨x.1, hx⟩, ⟨rfl, Subtype.ext e⟩, ?_⟩
    rintro z ⟨h1, -⟩
    have e1 : z.1 = x.1 := congrArg Subtype.val h1
    exact Subtype.ext e1
  · intro A g g' hg
    exact ⟨g, ⟨rfl, hg⟩, fun z hz => hz.1⟩

private theorem sq_inf (E : Spc) {a : Act} {Q Q₁ Q₂ : Pred a} (h₁ : Q₁.Le Q) (h₂ : Q₂.Le Q) :
    IsPullback (Sp.map E (inclLe (show (Q₁.inf Q₂).Le Q₁ from fun _ _ h => h.1)))
      (Sp.map E (inclLe (show (Q₁.inf Q₂).Le Q₂ from fun _ _ h => h.2)))
      (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) := by
  refine UpperTheory.stackProduct_isPullback_of_actionPullback E _ _ _ _ (fun A z => rfl) (fun A z => rfl) ?_ ?_
  · intro A x y hxy
    have hv : x.1 = y.1 := congrArg Subtype.val hxy
    refine ⟨⟨x.1, x.2, ?_⟩, ⟨rfl, ?_⟩, ?_⟩
    · rw [hv]
      exact y.2
    · apply Subtype.ext
      exact hv
    · rintro z ⟨hz, -⟩
      have hz' : z.1 = x.1 := congrArg Subtype.val hz
      apply Subtype.ext
      exact hz'
  · intro A g k hgk
    exact ⟨g, ⟨rfl, hgk⟩, fun z hz => hz.1⟩

private theorem cover_tr {R : Type} [CommRing R] {U U' V V' E : Spc} (u : U ⟶ E) (v : V ⟶ E) (u' : U' ⟶ E) (v' : V' ⟶ E)
    (e : U ⟶ U') (e' : V ⟶ V') [IsIso e] [IsIso e'] (hu : e ≫ u' = u) (hv : e' ≫ v' = v) (h : Cover2 R u v) :
    Cover2 R u' v' := by
  subst hu hv
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun n => ?_⟩
  · have : u' = inv e ≫ e ≫ u' := by simp
    rw [this]
    letI : Mono (e ≫ u') := h1
    exact mono_comp (inv e) (e ≫ u')
  · have : v' = inv e' ≫ e' ≫ v' := by simp
    rw [this]
    letI : Mono (e' ≫ v') := h2
    exact mono_comp (inv e') (e' ≫ v')
  · have h4 := h3 n
    have : biprod.desc ((free R).map ((e ≫ u').app n)) ((free R).map ((e' ≫ v').app n)) =
        biprod.map ((free R).map (e.app n)) ((free R).map (e'.app n)) ≫
          biprod.desc ((free R).map (u'.app n)) ((free R).map (v'.app n)) := by
      apply biprod.hom_ext' <;> simp
    rw [this] at h4
    exact epi_of_epi (biprod.map ((free R).map (e.app n)) ((free R).map (e'.app n))) _

private theorem cov (R : Type) [CommRing R] (E : Spc) {a : Act} {Q Q₁ Q₂ : Pred a} (h₁ : Q₁.Le Q) (h₂ : Q₂.Le Q)
    (hloc : ∀ (T : Scheme.{0}) (x : a.D.obj Γ(T, ⊤)), Q.P _ x →
      Loc T fun V g => Q₁.P _ (a.D.map g.appTop x) ∨ Q₂.P _ (a.D.map g.appTop x)) :
    Cover2 R (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) := by
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E _ _ ?_ ?_ (fun _ => Function.bijective_id) (fun _ => Function.bijective_id) ?_
  · intro A x y h
    have e := congrArg (fun w : {z // Q.P A z} => w.1) h
    exact Subtype.ext e
  · intro A x y h
    have e := congrArg (fun w : {z // Q.P A z} => w.1) h
    exact Subtype.ext e
  · intro T x
    obtain ⟨S, hS, hP⟩ := hloc T x.1 x.2
    refine ⟨S, hS, fun V g hg => ?_⟩
    rcases hP V g hg with h | h
    · exact Or.inl ⟨⟨_, h⟩, rfl⟩
    · exact Or.inr ⟨⟨_, h⟩, rfl⟩

private theorem tr (q : ℕ) [NeZero q] (E : Spc) {c a : Act} (π : Act.Hom c a) {m : ℕ} (d e : Fin m → ℤ)
    (cl : ∀ j, Ht q (Sp E c) (d j) (e j)) {Q' Q : Pred a} (h : Q'.Le Q) {P B' : Spc}
    (fs : P ⟶ Sp E (c.sub (Q.comap π))) (sn : P ⟶ B') (u : P ⟶ Sp E (c.sub (Q'.comap π))) (b : B' ⟶ Sp E (a.sub Q'))
    [IsIso u] [IsIso b] (hu : u ≫ Sp.map E (inclLe (comap_le π h)) = fs) (hb : u ≫ Sp.map E (π.sub Q') = sn ≫ b)
    (L : LHQ q E π d e cl Q') :
    LH q sn d e (fun j => pull _ fs _ _ (pull _ (Sp.map E (incl (Q.comap π))) _ _ (cl j))) := by
  have h1 := UpperTheory.lerayHirsch_of_iso_square q (Sp.map E (π.sub Q')) sn u b hb d e _ L
  have h2 : (fun j => pull _ fs _ _ (pull _ (Sp.map E (incl (Q.comap π))) _ _ (cl j))) =
      fun j => pull _ u _ _ (pull _ (Sp.map E (incl (Q'.comap π))) _ _ (cl j)) := by
    funext j
    rw [← pull_comp, ← pull_comp, ← hu, Category.assoc, map_incl]
  rw [h2]
  exact h1

end UpperTheory.Glue

theorem UpperTheory.leraHirsch_of_local_cover_of_inf :
    ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∀ {c a : Act} (π : Act.Hom c a) {m : ℕ} (d e : Fin m → ℤ) (cl : ∀ j, Ht q (Sp E c) (d j) (e j))
        (Q Q₁ Q₂ : Pred a) (_ : Q₁.Le Q) (_ : Q₂.Le Q),
        (∀ (T : Scheme.{0}) (x : a.D.obj Γ(T, ⊤)), Q.P _ x → Loc T fun V g => Q₁.P _ (a.D.map g.appTop x) ∨ Q₂.P _ (a.D.map g.appTop x)) →
        LHQ q E π d e cl Q₁ → LHQ q E π d e cl Q₂ → LHQ q E π d e cl (Q₁.inf Q₂) → LHQ q E π d e cl Q := by
  intro q _ E _ c a π m d e cl Q Q₁ Q₂ h₁ h₂ hloc L₁ L₂ L₁₂
  have hinf : (Q₁.inf Q₂).Le Q := fun A x hx => h₁ A x hx.1
  have sq1 := UpperTheory.Glue.sq E π h₁
  have sq2 := UpperTheory.Glue.sq E π h₂
  have sqi := UpperTheory.Glue.sq_inf E h₁ h₂
  letI := sq1.hasPullback
  letI := sq2.hasPullback
  letI := sqi.hasPullback
  have hloc' : ∀ (T : Scheme.{0}) (x : c.D.obj Γ(T, ⊤)), (Q.comap π).P _ x →
      Loc T fun V g => (Q₁.comap π).P _ (c.D.map g.appTop x) ∨ (Q₂.comap π).P _ (c.D.map g.appTop x) := by
    intro T x hx
    obtain ⟨S, hS, hP⟩ := hloc T _ hx
    refine ⟨S, hS, fun V g hg => ?_⟩
    show Q₁.P _ _ ∨ Q₂.P _ _
    rw [NatTrans.naturality_apply]
    exact hP V g hg
  have sq' : IsPullback (Sp.map E (inclLe (UpperTheory.Glue.comap_le π hinf)))
      (Sp.map E (π.sub (Q₁.inf Q₂)) ≫ sqi.isoPullback.hom) (Sp.map E (π.sub Q))
      (pullback.fst (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) ≫ Sp.map E (inclLe h₁)) := by
    refine (UpperTheory.Glue.sq E π hinf).of_iso (Iso.refl _) (Iso.refl _) sqi.isoPullback (Iso.refl _)
      (by simp) (by simp) (by simp) ?_
    rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      UpperTheory.Glue.map_inclLe]
  letI := sq'.hasPullback
  refine UpperTheory.lerayHirsch_of_mayerVietoris_cover q (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) (Sp.map E (π.sub Q)) d e _
    (UpperTheory.Glue.cov _ E h₁ h₂ hloc) ?_ ?_ ?_ ?_
  · exact UpperTheory.Glue.cover_tr (Sp.map E (inclLe (UpperTheory.Glue.comap_le π h₁)))
      (Sp.map E (inclLe (UpperTheory.Glue.comap_le π h₂))) _ _ sq1.isoPullback.hom sq2.isoPullback.hom
      sq1.isoPullback_hom_fst sq2.isoPullback_hom_fst
      (UpperTheory.Glue.cov _ E (UpperTheory.Glue.comap_le π h₁) (UpperTheory.Glue.comap_le π h₂) hloc')
  · exact UpperTheory.Glue.tr q E π d e cl h₁ _ _ sq1.isoPullback.inv (𝟙 _) sq1.isoPullback_inv_fst
      (by rw [sq1.isoPullback_inv_snd, Category.comp_id]) L₁
  · exact UpperTheory.Glue.tr q E π d e cl h₂ _ _ sq2.isoPullback.inv (𝟙 _) sq2.isoPullback_inv_fst
      (by rw [sq2.isoPullback_inv_snd, Category.comp_id]) L₂
  · exact UpperTheory.Glue.tr q E π d e cl hinf _ _ sq'.isoPullback.inv sqi.isoPullback.inv
      sq'.isoPullback_inv_fst
      (by rw [← sq'.isoPullback_inv_snd, Category.assoc, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]) L₁₂
end
