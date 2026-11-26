module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CoeffLgPcurveTop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.GeomSumRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.PicSpec

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  Eq.symm (NatTrans.naturality_apply φ.hom g.op x)

theorem sec_map_comp {R : Type} [CommRing R] {F G K : Shv R} (ψ : F ⟶ G) (φ : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map φ (Sec.map ψ x) = Sec.map (ψ ≫ φ) x := rfl

theorem sec_eq_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have : Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a := by rw [h]
  simpa [Sec.map] using this

theorem res_isZero {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) :=
  CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 s hs

theorem resι_d {R : Type} [CommRing R] (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  unfold resι res
  rw [Category.assoc, (injectiveResolution F).ι'.comm 0 1]
  simp

theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec ofRings.sec
  exact map_add (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom)
    (show (Scheme.Γ ⋙ unitsF).obj (op U) from ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op
  have h2 := congrArg (fun f => f.hom (show (Scheme.Γ ⋙ unitsF).obj (op U) from ULift.up (Additive.ofMul u))) this
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.symm

theorem glMat_map {U V : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    glMat (((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op y) =
      Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := rfl

theorem generalLinearGroup_det_map_fin_one {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : GL (Fin 1) A) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f M) =
      Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det M) := by
  ext
  simp

theorem glMat_δ1 {U : Scheme.{0}} (y : Sx (ofCat (glCat 1)) 2 U) :
    glMat (((ofCat (glCat 1)).δ 1).app (op U) y) =
      glMat (((ofCat (glCat 1)).δ 0).app (op U) y) * glMat (((ofCat (glCat 1)).δ 2).app (op U) y) := by
  have h : ((show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 0 2) =
      (show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 0 1 ≫
        (show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 1 2 :=
    ComposableArrows.map'_comp _ 0 1 2
  exact h

theorem face_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) (i : Fin 3) :
    (L.app (op (SimplexCategory.mk 1))).app (op U) ((E.δ i).app (op U) x) =
      ((ofCat (glCat 1)).δ i).app (op U) ((L.app (op (SimplexCategory.mk 2))).app (op U) x) := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (SimplicialObject.δ_naturality L i) (op U)) x
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  exact this

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit Sx.res
  rw [NatTrans.naturality_apply (L.app (op (SimplexCategory.mk 1))) g.op x, glMat_map, generalLinearGroup_det_map_fin_one]

theorem lineUnit_face {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) :
    lineUnit L (x.face 1) = lineUnit L (x.face 0) * lineUnit L (x.face 2) := by
  unfold lineUnit Sx.face
  rw [face_nat, face_nat, face_nat, glMat_δ1, map_mul]

def fam {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res ℤ Gm).X s) U
  | 1, s, h, _, x => Sec.map ((res ℤ Gm).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)))
  | _, _, _, _, _ => 0

theorem fam_zero {E : Spc} (L : E ⟶ ofCat (glCat 1)) (s : ℤ) (h : -((0 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0})
    (x : Sx E 0 U) : fam L 0 s h U x = 0 := rfl

theorem fam_add_two {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ) (h : -((p + 2 : ℕ) : ℤ) + 1 = s)
    (U : Scheme.{0}) (x : Sx E (p + 2) U) : fam L (p + 2) s h U x = 0 := rfl

theorem fam_one {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0})
    (x : Sx E 1 U) : fam L 1 0 h U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  simp [fam, Sec.map]

theorem fam_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0})
    (g : V ⟶ U) (x : Sx E p U) : Sec.res g (fam L p s h U x) = fam L p s h V (x.res g) := by
  match p with
  | 0 => simp [fam_zero]
  | 1 =>
    simp only [fam]
    rw [sec_map_res, sec_map_res, unitSec_res, lineUnit_res]
  | p + 2 => simp [fam_add_two]

theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem sec_map_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _

theorem ev_zero_cochain {E : Spc} {I : Cx ℤ} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (0 : Cochain ((chains ℤ).obj E) I n) p s h U x = 0 := by
  have hZero := CupSpec.ev_zero (I := I) p s h U x
  exact hZero

theorem fam_cocycle {E : Spc} (L : E ⟶ ofCat (glCat 1)) (α : Cochain ((chains ℤ).obj E) (res ℤ Gm) 1)
    (hα : ∀ p s h U x, ev α p s h U x = fam L p s h U x) : δ 1 2 α = 0 := by
  have hExt := CupSpec.ev_ext (δ 1 2 α) 0
  apply hExt
  intro p t ht U x
  rw [ev_zero_cochain]
  have hDeltaSucc := CupSpec.ev_δ_succ (m := 2) (by norm_num) α U
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    have hDeltaZero := CupSpec.ev_δ_zero (m := 2) (by norm_num) α U 1 2 (by simp) ht x
    rw [hDeltaZero, hα, fam_zero, sec_map_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key : ev (δ 1 2 α) 1 1 ht U x = Sec.map ((res ℤ Gm).d 0 1) (ev α 1 0 (by simp) U x) +
        (2 : ℤ).negOnePow • ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ev α 0 1 (by simp) U (x.face i) :=
      hDeltaSucc 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, fam_zero, fam_one, smul_zero, Finset.sum_const_zero, add_zero, sec_map_comp, resι_d]
    rfl
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key : ev (δ 1 2 α) 2 0 ht U x = Sec.map ((res ℤ Gm).d (-1) 0) (ev α 2 (-1) (by simp) U x) +
        (2 : ℤ).negOnePow • ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ev α 1 0 (by simp) U (x.face i) :=
      hDeltaSucc 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, fam_one]
    rw [show fam L 2 (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three, lineUnit_face,
      unitSec_mul, sec_map_add]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    simp
  | p + 3 =>
    have key := hDeltaSucc (p + 2) (t - 1) t (by omega) ht x
    rw [key]
    simp only [hα, fam_add_two, sec_map_zero, zero_add, smul_zero, Finset.sum_const_zero]

theorem exists_cocycle {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  have hExists := GlobalTheory.EtC.exists_cochain_ev_eq_of_natural ℤ (fam L) (fam_nat L)
  obtain ⟨α, hα⟩ := hExists
  refine ⟨Cocycle.mk α 2 (by norm_num) (fam_cocycle L α hα), fun U x => ?_, fun U x => ?_⟩
  · exact (hα 0 1 _ U x).trans (fam_zero L 1 _ U x)
  · exact (hα 1 0 _ U x).trans (fam_one L _ U x)

theorem spec {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = picClass L ∧
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  obtain ⟨γ, h0, h1⟩ := exists_cocycle L
  exact pick_spec (P := fun c => ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)))
    ⟨_, γ, rfl, h0, h1⟩

theorem cocycle_ext {E : Spc} (γ γ' : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = ev γ'.1 0 1 (by simp) U x)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = ev γ'.1 1 0 (by simp) U x) : γ = γ' := by
  have hExt := CupSpec.ev_ext γ.1 γ'.1
  refine Cocycle.ext (hExt fun p s h U x => ?_)
  match p with
  | 0 =>
    obtain rfl : s = 1 := by omega
    exact h0 U x
  | 1 =>
    obtain rfl : s = 0 := by omega
    exact h1 U x
  | p + 2 =>
    have hZ := res_isZero Gm s (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.PicSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeRankOneEtaleSheafEquivLocallyConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeRankOneEtaleSheafEquivLocallyConstant
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

theorem res_comp {W V U : Scheme.{0}} (k : W ⟶ V) (j : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ j) x = Sec.res k (Sec.res j x) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_smul {V U : Scheme.{0}} (j : V ⟶ U) (c : R) (x : Sec F U) :
    Sec.res j ((ULift.up c : ULift.{1} R) • x) = (ULift.up c : ULift.{1} R) • Sec.res j x :=
  map_smul _ _ _

theorem res_add {V U : Scheme.{0}} (j : V ⟶ U) (x y : Sec F U) :
    Sec.res j (x + y) = Sec.res j x + Sec.res j y := map_add _ _ _

theorem res_sub {V U : Scheme.{0}} (j : V ⟶ U) (x y : Sec F U) :
    Sec.res j (x - y) = Sec.res j x - Sec.res j y := map_sub _ _ _

theorem sep {U : Scheme.{0}} (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U) (he : ∀ i, Etale (j i))
    (hc : ∀ u : U, ∃ i v, j i v = u) (x y : Sec F U) (h : ∀ i, Sec.res (j i) x = Sec.res (j i) y) : x = y :=
  sub_eq_zero.1 ((GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family R F U ι V j he hc).1 (x - y) (fun i => by rw [res_sub, h i, sub_self]))

theorem sec_empty {V : Scheme.{0}} [IsEmpty V] (x y : Sec F V) : x = y :=
  sep PEmpty (fun _ => V) (fun _ => 𝟙 V) (fun _ => inferInstance) (fun u => isEmptyElim u) x y (fun i => i.elim)

def fib {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (v : V) : V.Opens :=
  ⟨ψ ⁻¹' {ψ v}, ψ.isLocallyConstant.isOpen_fiber _⟩

theorem fib_apply {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (v : V) (w : (fib ψ v).toScheme) :
    ψ ((fib ψ v).ι w) = ψ v := by
  have h := (Scheme.Opens.range_ι (fib ψ v)).subset ⟨w, rfl⟩
  exact h

theorem fib_cov {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (u : V) :
    ∃ (i : V) (w : (fib ψ i).toScheme), (fib ψ i).ι w = u := by
  have h : u ∈ Set.range (fib ψ u).ι := by rw [Scheme.Opens.range_ι]; exact rfl
  obtain ⟨w, hw⟩ := h
  exact ⟨u, w, hw⟩

end GlobalTheory.EtC.GenLC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

def IsMul {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x : Sec F U) : Prop :=
  ∀ (V : Scheme.{0}) (j : V ⟶ U) (c : R), (∀ v, φ (j v) = c) →
    Sec.res j x = (ULift.up c : ULift.{1} R) • Sec.res (j ≫ s) g

theorem isMul_of_fib {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x : Sec F U)
    (h : ∀ u, Sec.res (fib φ u).ι x = (ULift.up (φ u) : ULift.{1} R) • Sec.res ((fib φ u).ι ≫ s) g) : IsMul s g φ x := by
  intro V j c hc
  by_cases hV : IsEmpty V
  · exact sec_empty _ _
  obtain ⟨v⟩ := not_isEmpty_iff.1 hV
  have H : Set.range j ⊆ Set.range (fib φ (j v)).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    change φ (j w) = φ (j v)
    rw [hc w, hc v]
  have hf := IsOpenImmersion.lift_fac (fib φ (j v)).ι j H
  rw [← hf, res_comp, h, res_smul, ← res_comp, hc v, Category.assoc]

theorem isMul_unique {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x y : Sec F U)
    (hx : IsMul s g φ x) (hy : IsMul s g φ y) : x = y :=
  sep U (fun u => (fib φ u).toScheme) (fun u => (fib φ u).ι) (fun _ => inferInstance) (fib_cov φ) x y
    (fun u => by rw [hx _ _ (φ u) (fib_apply φ u), hy _ _ (φ u) (fib_apply φ u)])

theorem isMul_exists {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) :
    ∃ x, IsMul s g φ x := by
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family R F U U (fun u => (fib φ u).toScheme) (fun u => (fib φ u).ι) (fun _ => inferInstance)
    (fib_cov φ)).2 (fun u => (ULift.up (φ u) : ULift.{1} R) • Sec.res ((fib φ u).ι ≫ s) g) (by
      intro i k
      rw [res_smul, res_smul, ← res_comp, ← res_comp, ← Category.assoc, ← Category.assoc, pullback.condition]
      by_cases hP : IsEmpty (pullback (fib φ i).ι (fib φ k).ι : Scheme.{0})
      · exact sec_empty _ _
      obtain ⟨p⟩ := not_isEmpty_iff.1 hP
      have e : φ i = φ k := by
        rw [← fib_apply φ i (pullback.fst (fib φ i).ι (fib φ k).ι p), ← fib_apply φ k (pullback.snd (fib φ i).ι (fib φ k).ι p),
          ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      rw [e])
  exact ⟨x, isMul_of_fib s g φ x hx⟩

theorem isMul_add {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ ψ : LocallyConstant U R) (x y : Sec F U)
    (hx : IsMul s g φ x) (hy : IsMul s g ψ y) : IsMul s g (φ + ψ) (x + y) := by
  intro V j c hc
  let χ : LocallyConstant V (R × R) :=
    ⟨fun v => (φ (j v), ψ (j v)), ((φ.comap j.base.hom).isLocallyConstant.comp₂ (ψ.comap j.base.hom).isLocallyConstant Prod.mk)⟩
  refine sep V (fun v => (fib χ v).toScheme) (fun v => (fib χ v).ι) (fun _ => inferInstance) (fib_cov χ) _ _ (fun v => ?_)
  have h1 : ∀ w, φ (((fib χ v).ι ≫ j) w) = φ (j v) := fun w => congrArg Prod.fst (fib_apply χ v w)
  have h2 : ∀ w, ψ (((fib χ v).ι ≫ j) w) = ψ (j v) := fun w => congrArg Prod.snd (fib_apply χ v w)
  rw [← res_comp, res_add, hx _ _ _ h1, hy _ _ _ h2, res_smul, ← res_comp, ← add_smul, ← hc v]
  rfl

end GlobalTheory.EtC.GenLC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

noncomputable def mulSec {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) : Sec F U :=
  (isMul_exists s g φ).choose

theorem mulSec_spec {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) :
    IsMul s g φ (mulSec s g φ) := (isMul_exists s g φ).choose_spec

theorem mulSec_add {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ ψ : LocallyConstant U R) :
    mulSec s g (φ + ψ) = mulSec s g φ + mulSec s g ψ :=
  isMul_unique s g _ _ _ (mulSec_spec s g _) (isMul_add s g φ ψ _ _ (mulSec_spec s g φ) (mulSec_spec s g ψ))

theorem coeff_eq {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (x : Sec F U)
    {V₁ V₂ : Scheme.{0}} (j₁ : V₁ ⟶ U) (j₂ : V₂ ⟶ U) (c₁ c₂ : R)
    (h₁ : Sec.res j₁ x = (ULift.up c₁ : ULift.{1} R) • Sec.res (j₁ ≫ s) g)
    (h₂ : Sec.res j₂ x = (ULift.up c₂ : ULift.{1} R) • Sec.res (j₂ ≫ s) g) (v₁ : V₁) (v₂ : V₂) (hv : j₁ v₁ = j₂ v₂) :
    c₁ = c₂ := by
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v₁ v₂ hv
  have e : Sec.res (pullback.fst j₁ j₂) (Sec.res j₁ x) = Sec.res (pullback.snd j₁ j₂) (Sec.res j₂ x) := by
    rw [← res_comp, ← res_comp, pullback.condition]
  rw [h₁, h₂, res_smul, res_smul, ← res_comp, ← res_comp, ← Category.assoc, ← Category.assoc, ← pullback.condition] at e
  have h0 : (ULift.up (c₁ - c₂) : ULift.{1} R) • Sec.res ((pullback.fst j₁ j₂ ≫ j₁) ≫ s) g = 0 := by
    have hu : (ULift.up (c₁ - c₂) : ULift.{1} R) = ULift.up c₁ - ULift.up c₂ := rfl
    rw [hu, sub_smul, e, sub_self]
  exact sub_eq_zero.1 ((hg _ _).2 (c₁ - c₂) ⟨p⟩ h0)

theorem mulSec_inj {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (φ : LocallyConstant U R)
    (h : mulSec s g φ = 0) : φ = 0 := by
  ext u
  have e := mulSec_spec s g φ _ (fib φ u).ι (φ u) (fib_apply φ u)
  rw [h] at e
  have hu : u ∈ Set.range (fib φ u).ι := by rw [Scheme.Opens.range_ι]; exact rfl
  obtain ⟨w, -⟩ := hu
  exact (hg (fib φ u).toScheme ((fib φ u).ι ≫ s)).2 (φ u) ⟨w⟩ (by rw [← e]; exact map_zero _)

theorem mulSec_surj {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (x : Sec F U) :
    ∃ φ, mulSec s g φ = x := by
  choose V j v c he hv hx₀ using (hg U s).1 x
  have hx : ∀ u, Sec.res (j u) x = (ULift.up (c u) : ULift.{1} R) • Sec.res (j u ≫ s) g := hx₀
  have hconst : ∀ u, ∀ u' ∈ Set.range (j u), c u' = c u := by
    rintro u _ ⟨w, rfl⟩
    exact coeff_eq s g hg x (j (j u w)) (j u) _ _ (hx _) (hx u) _ w (hv _)
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_exists_open c).2 fun u =>
    ⟨Set.range (j u), (j u).isOpenMap.isOpen_range, ⟨v u, hv u⟩, hconst u⟩
  refine ⟨⟨c, hlc⟩, isMul_unique s g _ _ _ (mulSec_spec s g _) ?_⟩
  intro W k a ha
  refine sep W (fun w => (pullback (j (k w)) k : Scheme.{0})) (fun w => pullback.snd (j (k w)) k)
    (fun _ => inferInstance) (fun w => ?_) _ _ (fun w => ?_)
  · obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback (v (k w)) w (hv (k w))
    exact ⟨w, p, hp⟩
  · have hc : c (k w) = a := ha w
    rw [← res_comp, ← pullback.condition, res_comp, hx, res_smul, ← res_comp, res_smul, ← res_comp, hc,
      ← Category.assoc, ← Category.assoc, pullback.condition]

end GlobalTheory.EtC.GenLC


open GlobalTheory.EtC.GenLC in
theorem GlobalTheory.EtC.gen_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g → ∃ e : ∀ (U : Scheme.{0}) (s : U ⟶ S), LocallyConstant U R ≃+ Sec F U, (∀ U s (c : R), e U s (LocallyConstant.const U c) = (ULift.up c : ULift.{1} R) • Sec.res s g) ∧ ∀ (V U : Scheme.{0}) (j : V ⟶ U) (s : U ⟶ S) (φ : LocallyConstant U R), Sec.res j (e U s φ) = e V (j ≫ s) (φ.comap j.base.hom) := by
  intro R _ F S g hg
  let m : ∀ (U : Scheme.{0}) (s : U ⟶ S), LocallyConstant U R →+ Sec F U := fun U s =>
    AddMonoidHom.mk' (mulSec s g) (mulSec_add s g)
  refine ⟨fun U s => AddEquiv.ofBijective (m U s)
    ⟨(injective_iff_map_eq_zero (m U s)).2 (fun φ h => mulSec_inj s g hg φ h), mulSec_surj s g hg⟩, ?_, ?_⟩
  · intro U s c
    show mulSec s g (LocallyConstant.const U c) = _
    refine isMul_unique s g _ _ _ (mulSec_spec s g _) ?_
    intro V j a ha
    rw [res_smul, ← res_comp]
    by_cases hV : IsEmpty V
    · exact sec_empty _ _
    obtain ⟨v⟩ := not_isEmpty_iff.1 hV
    have hca : c = a := ha v
    rw [hca]
  · intro V U j s φ
    show Sec.res j (mulSec s g φ) = mulSec (j ≫ s) g (φ.comap j.base.hom)
    refine isMul_unique (j ≫ s) g _ _ _ ?_ (mulSec_spec (j ≫ s) g _)
    intro W k a ha
    rw [← res_comp, mulSec_spec s g φ W (k ≫ j) a ha, Category.assoc]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeRankOneEtaleSheafEquivLocallyConstantStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeRankOne_etaleSheaf_equiv_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g → ∃ e : ∀ (U : Scheme.{0}) (s : U ⟶ S), LocallyConstant U R ≃+ Sec F U, (∀ U s (c : R), e U s (LocallyConstant.const U c) = (ULift.up c : ULift.{1} R) • Sec.res s g) ∧ ∀ (V U : Scheme.{0}) (j : V ⟶ U) (s : U ⟶ S) (φ : LocallyConstant U R), Sec.res j (e U s φ) = e V (j ≫ s) (φ.comap j.base.hom) := by
  first | exact @GlobalTheory.EtC.gen_locallyConstant | exact GlobalTheory.EtC.gen_locallyConstant | (intros; apply GlobalTheory.EtC.gen_locallyConstant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFunctorDegreeTermAugmentedExactResolution
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingCofaceMapComplexPreadditiveYonedaDApp
open CategoryTheory Limits AlgebraicGeometry Opposite Abelian Simplicial GlobalTheory.Et
universe v u

namespace GlobalTheory

theorem alternatingCofaceMapComplex_preadditiveYoneda_d_apply {C : Type u} [Category.{v} C] [Abelian C] (X : SimplicialObject C) (I : C) (m : ℕ)
  (x : ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).X m) :
  ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d m (m+1) x
   = (show X _⦋m+1⦌ ⟶ I from AlgebraicTopology.AlternatingFaceMapComplex.objD X m ≫ (show X _⦋m⦌ ⟶ I from x)) := by
  have hd : ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d m (m+1)
      = AlgebraicTopology.AlternatingCofaceMapComplex.objD (X.rightOp ⋙ preadditiveYoneda.obj I) m := by
    exact CochainComplex.of_d (fun n => (X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋n⦌)
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD (X.rightOp ⋙ preadditiveYoneda.obj I)) m
  rw [hd]
  let φ : (((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m⦌) ⟶ ((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m+1⦌)) →+ ((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m+1⦌) :=
    AddMonoidHom.mk' (fun f => f x) (fun f g => rfl)
  change φ (AlgebraicTopology.AlternatingCofaceMapComplex.objD _ m) = _
  have h2 : (AlgebraicTopology.AlternatingFaceMapComplex.objD X m ≫ (show X _⦋m⦌ ⟶ I from x)) =
      ∑ i : Fin (m+2), (-1 : ℤ) ^ (i : ℕ) • (X.δ i ≫ (show X _⦋m⦌ ⟶ I from x)) := by
    rw [AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun i _ => Preadditive.zsmul_comp _ _ _
  refine Eq.trans ?_ h2.symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, map_sum, map_zsmul]
  rfl

theorem alternatingCofaceMapComplex_preadditiveYoneda_exactAt_succ : ∀ {C : Type u} [Category.{v} C] [Abelian C] (X : SimplicialObject C) (I : C) [Injective I] (n : ℕ), ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).ExactAt (n + 1) → ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).ExactAt (n + 1) := by
  intro C _ _ X I _ n h
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro x hx
  let S := ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).sc' (n+2) (n+1) n
  have hS1 : S.f = AlgebraicTopology.AlternatingFaceMapComplex.objD X (n+1) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq X (n+1)
  have hS2 : S.g = AlgebraicTopology.AlternatingFaceMapComplex.objD X n :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq X n
  let f : S.X₂ ⟶ I := x
  have hf : S.f ≫ f = 0 := by
    have h1 := alternatingCofaceMapComplex_preadditiveYoneda_d_apply X I (n+1) x
    rw [hS1]
    exact h1.symm.trans hx
  have hm : Mono (cokernel.desc S.f S.g S.zero) := h.mono_cokernelDesc
  let g : S.X₃ ⟶ I := @Injective.factorThru _ _ _ _ _ _ (cokernel.desc S.f f hf) (cokernel.desc S.f S.g S.zero) hm
  refine ⟨g, ?_⟩
  change ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d n (n+1) g = x
  refine (alternatingCofaceMapComplex_preadditiveYoneda_d_apply X I n g).trans ?_
  rw [← hS2]
  change S.g ≫ g = f
  have e2 : cokernel.desc S.f S.g S.zero ≫ g = cokernel.desc S.f f hf :=
    @Injective.comp_factorThru _ _ _ _ _ _ _ _ hm
  rw [← cokernel.π_desc S.f S.g S.zero, Category.assoc, e2, cokernel.π_desc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactPreadditiveYonedaOfInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentedExactIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentedExactIff
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.AugExact

theorem augmented_exact_iff (C : Type 2) [Category.{1} C] [Abelian C] (K : SimplicialObject C) (B : C)
    (f : K ⟶ (SimplicialObject.const C).obj B) :
    QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map f) ↔
      (Epi (f.app (op (SimplexCategory.mk (0)))) ∧
        (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0,
          (ShortComplex.mk _ _ w).Exact) ∧
        ∀ n : ℕ, ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1)) := by
  let e := (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv
  let g : (AlgebraicTopology.alternatingFaceMapComplex C).obj ((SimplicialObject.const C).obj B) ⟶
      (ChainComplex.single₀ C).obj B := e.hom
  haveI : QuasiIso g := e.quasiIso_hom
  have hg : g.f 0 = 𝟙 B := AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero _
  rw [← quasiIso_iff_comp_right _ g, quasiIso_iff]
  set φ := (AlgebraicTopology.alternatingFaceMapComplex C).map f ≫ g with hφ
  have h0 : φ.f 0 = f.app (op (SimplexCategory.mk 0)) := by
    rw [hφ, HomologicalComplex.comp_f, hg]
    exact Category.comp_id _
  have hd : ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).d 1 0 =
      K.δ (n := 0) 0 - K.δ (n := 0) 1 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj K).d (0 + 1) 0 = _
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  have w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0 := by
    simp [Preadditive.sub_comp, SimplicialObject.δ_naturality, SimplicialObject.δ]
  have he : Epi (φ.f 0) ↔ Epi (f.app (op (SimplexCategory.mk (0)))) := h0 ▸ Iff.rfl
  have hz : QuasiIsoAt φ 0 ↔ (Epi (f.app (op (SimplexCategory.mk (0)))) ∧
      (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0,
        (ShortComplex.mk _ _ w).Exact)) := by
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨he.1 h2, w, (ShortComplex.exact_iff_of_iso ?_).1 h1⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (hd.symm.trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (h0.symm.trans (Category.comp_id _).symm))
    · rintro ⟨h1, _, h2⟩
      refine ⟨(ShortComplex.exact_iff_of_iso ?_).1 h2, he.2 h1⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (hd.trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (h0.trans (Category.comp_id _).symm))
  have hs : ∀ n : ℕ, QuasiIsoAt φ (n + 1) ↔
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1) :=
    fun n => quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)
  constructor
  · intro h
    exact ⟨(hz.1 (h 0)).1, (hz.1 (h 0)).2, fun n => (hs n).1 (h (n + 1))⟩
  · rintro ⟨h1, h2, h3⟩ i
    cases i with
    | zero => exact hz.2 ⟨h1, h2⟩
    | succ n => exact (hs n).2 (h3 n)

end GlobalTheory.EtC.AugExact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentedExactIffStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact : ∀ (C : Type 2) [Category.{1} C] [Abelian C] (K : SimplicialObject C) (B : C) (f : K ⟶ (SimplicialObject.const C).obj B), QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map f) ↔ (Epi (f.app (op (SimplexCategory.mk (0)))) ∧ (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0, (ShortComplex.mk _ _ w).Exact) ∧ ∀ n : ℕ, ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1)) := by
  first | (exact @GlobalTheory.EtC.AugExact.augmented_exact_iff) | (exact GlobalTheory.EtC.AugExact.augmented_exact_iff) | (intros; apply GlobalTheory.EtC.AugExact.augmented_exact_iff  <;> assumption)
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem wExact_preadditiveYoneda_of_injective (R : Type) [CommRing R] (T : Type 1) [Category.{0} T]
    (Ψ : T ⥤ PShᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (J : Shv R) (hJ : Injective J) (hq : QuasiIso ((chains R).map (lev Ψ a))) :
    WExact (Ψ ⋙ (free R).op ⋙ preadditiveYoneda.obj J) a := by
  let K : SimplicialObject (Shv R) := ((SimplicialObject.whiskering _ _).obj (free R)).obj ((X ⋙ Ψ).leftOp)
  let B : Shv R := (free R).obj (Ψ.obj U).unop
  let f : K ⟶ (SimplicialObject.const (Shv R)).obj B :=
    ((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a) ≫ (Functor.constComp _ _ _).hom
  haveI h1 : QuasiIso ((chainsN R).map (lev Ψ a)) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).1 hq
  have hq' : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f) := by
    have e : (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f =
        (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a)) ≫
        (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp _ _ _).hom :=
      Functor.map_comp _ _ _
    rw [e]
    haveI : IsIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) :=
      Functor.map_isIso _ _
    haveI h2 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a))) := h1
    haveI h3 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) :=
      quasiIso_of_isIso _
    exact quasiIso_comp (hφ := h2) (hφ' := h3) _ _
  obtain ⟨hepi, ⟨w, hex⟩, hn⟩ := (GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact _ K B f).1 hq'
  have hepi' : Epi ((free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop) := by
    have e : f.app (op (SimplexCategory.mk 0)) = (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop :=
      Category.comp_id _
    rw [← e]; exact hepi
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    change (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ x =
      (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ y at hxy
    exact (cancel_epi _).1 hxy
  · intro y hy
    change (free R).map (Ψ.map (X.δ (n := 0) 0)).unop ≫ y = (free R).map (Ψ.map (X.δ (n := 0) 1)).unop ≫ y at hy
    let y' : K.obj (op (SimplexCategory.mk 0)) ⟶ J := y
    have hy' : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ y' = 0 := by
      refine (Preadditive.sub_comp _ _ _).trans (sub_eq_zero.2 ?_)
      exact hy
    refine ⟨hex.descToInjective (J := J) y' hy', ?_⟩
    exact hex.comp_descToInjective (J := J) y' hy'
  · intro n
    exact GlobalTheory.alternatingCofaceMapComplex_preadditiveYoneda_exactAt_succ K J n (hn n)

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFunctorDegreeTermAugmentedExactResolution
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem wExact_term_HC (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T]
    (Φ : T ⥤ Spcᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (h : Hyp R Φ a) (n : ℤ) : WExact (term (Φ ⋙ HC R F) n) a := by
  obtain ⟨π, hπ⟩ := GlobalTheory.T.bijective_HC_component_eval_of_maps R F n
  exact GlobalTheory.EtC.WExactProd.wexact_of_prod T U X a ℕ
    (fun k => Φ ⋙ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op ⋙ (free R).op ⋙
      preadditiveYoneda.obj ((res R F).X (n - k)))
    (term (Φ ⋙ HC R F) n) (fun k => Functor.whiskerLeft Φ (π k)) (fun V => hπ (Φ.obj V))
    (fun k => wExact_preadditiveYoneda_of_injective R T (Φ ⋙ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op)
      U X a ((res R F).X (n - k)) ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F).1 (n - k)) (h (op (SimplexCategory.mk k))))

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFunctorDegreeTermAugmentedExactResolutionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Φ : T ⥤ Spcᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X), Hyp R Φ a → ∀ n, WExact (term (Φ ⋙ HC R F) n) a := by
  first | exact @GlobalTheory.EtC.wExact_term_HC | exact GlobalTheory.EtC.wExact_term_HC | (intros; apply GlobalTheory.EtC.wExact_term_HC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootExtractionLemmaSheaf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMatrixForDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMatrixForDepth
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory

noncomputable section

variable {C : Type} [Field C]

theorem powRow_nonneg_of_nsmul {a : WithTop ℝ} {N : ℕ} (hN : N ≠ 0) (h : 0 ≤ N • a) : 0 ≤ a := by
  cases a with
  | top => exact le_top
  | coe r =>
    have e : ((N • r : ℝ) : WithTop ℝ) = N • (r : WithTop ℝ) := WithTop.coe_nsmul _ _
    rw [← e] at h
    have h' : (0 : ℝ) ≤ N • r := by exact_mod_cast h
    rw [nsmul_eq_mul] at h'
    have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have : 0 ≤ r := by
      by_contra hr
      push Not at hr
      nlinarith
    exact_mod_cast this

theorem powRow_int_root [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) {N : ℕ} (hN : 0 < N)
    (y : C) (hy : IsIntV v y) : ∃ x, x ^ N = y ∧ IsIntV v x := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hN
  refine ⟨x, hx, powRow_nonneg_of_nsmul hN.ne' ?_⟩
  rw [← AddValuation.map_pow, hx]
  exact hy

theorem powRow_int_of_le (v : AddValuation C (WithTop ℝ)) {a b : C} (hb : b ≠ 0)
    (h : v b ≤ v (a * b)) : IsIntV v a := by
  unfold IsIntV
  rw [AddValuation.map_mul] at h
  have hb' : v b ≠ ⊤ := (v.ne_top_iff).2 hb
  cases hvb : v b with
  | top => exact absurd hvb hb'
  | coe r =>
    rw [hvb] at h
    cases hva : v a with
    | top => exact le_top
    | coe s =>
      rw [hva] at h
      have h2 : r ≤ s + r := by exact_mod_cast h
      exact_mod_cast (by linarith : (0 : ℝ) ≤ s)

theorem powRow_v_neg_one_pow (v : AddValuation C (WithTop ℝ)) (k : ℕ) : v ((-1 : C) ^ k) = 0 := by
  rw [AddValuation.map_pow, AddValuation.map_neg, AddValuation.map_one, smul_zero]

theorem powRow_exists [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) {V : Type} [AddCommGroup V]
    [Module C V] (N : ℕ) (hN : 0 < N) (j : ℕ) : ∀ (m : ℕ) (z : Fin m → V),
    Module.finrank C (Submodule.span C (Set.range z)) ≤ j →
    ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧
      ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  intro m
  induction m with
  | zero =>
    intro z _
    exact ⟨1, fun w => w.elim0, by simp, fun w => w.elim0⟩
  | succ m ih =>
    intro z hz
    by_cases hli : LinearIndependent C z
    · have hmj : m + 1 ≤ j := by
        have := finrank_span_eq_card hli
        simp only [Fintype.card_fin] at this
        omega
      refine ⟨1, ?_, by simp [AddValuation.map_one], fun w hw => absurd hw (by omega)⟩
      intro w u
      unfold IsIntV
      rw [Matrix.one_apply]
      split_ifs <;> simp
    · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
      obtain ⟨u0, -, hu0⟩ := Finset.exists_min_image Finset.univ (fun u => v (g u))
        ⟨i, Finset.mem_univ _⟩
      have hg0 : g u0 ≠ 0 := by
        intro h0
        apply hi
        have := hu0 i (Finset.mem_univ _)
        rw [h0, AddValuation.map_zero] at this
        exact (v.top_iff).1 (top_le_iff.1 this)
      set c : Fin (m + 1) → C := fun u => g u / g u0 with hc
      have hc0 : c u0 = 1 := div_self hg0
      have hcint : ∀ u, IsIntV v (c u) := by
        intro u
        apply powRow_int_of_le v hg0
        have : c u * g u0 = g u := div_mul_cancel₀ _ hg0
        rw [this]
        exact hu0 u (Finset.mem_univ _)
      have hcz : ∑ u, c u • z u = 0 := by
        have : ∑ u, c u • z u = (g u0)⁻¹ • ∑ u, g u • z u := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [smul_smul, hc]
          simp only [div_eq_mul_inv, mul_comm]
        rw [this, hg, smul_zero]
      choose r hr hrint using fun u => powRow_int_root v hN (c u) (hcint u)
      set r' : Fin (m + 1) → C := Function.update r u0 1 with hr'
      have hr'N : ∀ u, r' u ^ N = c u := by
        intro u
        by_cases hu : u = u0
        · subst hu; rw [hr', Function.update_self, one_pow, hc0]
        · rw [hr', Function.update_of_ne hu, hr]
      have hr'int : ∀ u, IsIntV v (r' u) := by
        intro u
        by_cases hu : u = u0
        · subst hu; rw [hr', Function.update_self]; unfold IsIntV; rw [AddValuation.map_one]
        · rw [hr', Function.update_of_ne hu]; exact hrint u
      have hz' : Module.finrank C (Submodule.span C (Set.range (z ∘ u0.succAbove))) ≤ j := by
        have : Module.Finite C (Submodule.span C (Set.range z)) :=
          Module.Finite.span_of_finite C (Set.finite_range z)
        refine le_trans (Submodule.finrank_mono (Submodule.span_mono ?_)) hz
        rintro _ ⟨k, rfl⟩
        exact ⟨_, rfl⟩
      obtain ⟨x', hx'int, hx'det, hx'k⟩ := ih (z ∘ u0.succAbove) hz'
      let A : Matrix (Fin (m + 1)) (Fin (m + 1)) C :=
        Matrix.of (Fin.snoc (fun w' => Fin.insertNth (α := fun _ => C) u0 0 (x' w')) r')
      have hAlast : ∀ u, A (Fin.last m) u = r' u := by
        intro u; simp [A, Fin.snoc_last]
      have hAcs : ∀ w' u, A w'.castSucc u = Fin.insertNth (α := fun _ => C) u0 0 (x' w') u := by
        intro w' u; simp [A, Fin.snoc_castSucc]
      refine ⟨A, ?_, ?_, ?_⟩
      · intro w u
        induction w using Fin.lastCases with
        | last => rw [hAlast]; exact hr'int u
        | cast w' =>
          rw [hAcs]
          induction u using Fin.succAboveCases u0 with
          | x =>
            rw [Fin.insertNth_apply_same]; unfold IsIntV; rw [AddValuation.map_zero]; exact le_top
          | p k => rw [Fin.insertNth_apply_succAbove]; exact hx'int w' k
      · rw [Matrix.det_succ_column A u0]
        rw [Fintype.sum_eq_single (Fin.last m)]
        · have hsub : A.submatrix (Fin.last m).succAbove u0.succAbove = x' := by
            ext w' k
            simp only [Matrix.submatrix_apply, Fin.succAbove_last]
            rw [hAcs, Fin.insertNth_apply_succAbove]
          rw [hsub, hAlast]
          rw [AddValuation.map_mul, AddValuation.map_mul, powRow_v_neg_one_pow, hx'det]
          have : r' u0 = 1 := by rw [hr', Function.update_self]
          rw [this, AddValuation.map_one]
          simp
        · intro w hw
          induction w using Fin.lastCases with
          | last => exact absurd rfl hw
          | cast w' => rw [hAcs, Fin.insertNth_apply_same]; simp
      · intro w hw
        induction w using Fin.lastCases with
        | last =>
          simp only [hAlast, hr'N]
          exact hcz
        | cast w' =>
          simp only [hAcs]
          rw [Fin.sum_univ_succAbove _ u0, Fin.insertNth_apply_same, zero_pow hN.ne', zero_smul,
            zero_add]
          simp only [Fin.insertNth_apply_succAbove]
          exact hx'k w' (by simpa using hw)

theorem powRow_matrix : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) (V : Type) [AddCommGroup V] [Module C V] (N : ℕ), 0 < N → ∀ (j m : ℕ) (z : Fin m → V), Module.finrank C (Submodule.span C (Set.range z)) ≤ j → ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧ ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  intro C _ _ v V _ _ N hN j m z hz
  exact powRow_exists v N hN j m z hz

end

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMatrixForDepthStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unimodular_matrix_for_depth : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) (V : Type) [AddCommGroup V] [Module C V] (N : ℕ), 0 < N → ∀ (j m : ℕ) (z : Fin m → V), Module.finrank C (Submodule.span C (Set.range z)) ≤ j → ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧ ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  first | exact @GlobalTheory.powRow_matrix | exact GlobalTheory.powRow_matrix | (intros; apply GlobalTheory.powRow_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootExtractionLemmaSheaf
namespace GlobalTheory.RootTrick

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem root_statement : RootStatement := by
  intro C _ _ _ v p hp hv d h m ty i G γ hγ hty n j _hn V _ _ La hdim
  obtain ⟨x, hxi, hxd, hxk⟩ := GlobalTheory.T.exists_integral_unimodular_matrix_for_depth C v V (p ^ n) (pow_pos hp.pos n) j m
    (fun u => La (G.lc p (γ u) n)) hdim
  refine ⟨x, hxi, hxd, ?_⟩
  have h6 := fun w => pt6' C v p hp hv d m G γ (x w) hγ (hxi w)
  dsimp only at h6 ⊢
  refine ⟨fun w => (h6 w).2.1, fun w => ⟨(h6 w).2.2.2 (fun u => (hty u).1), fun k a hk => ?_⟩,
    fun w hw => ?_⟩
  · rw [(h6 w).2.2.1 k]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, (hty _).2 k a hk, mul_zero,
      Finset.sum_const_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [(h6 w).2.2.1 n, map_sum]
      simp only [map_smul]
      exact hxk w hw

end GlobalTheory.RootTrick
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootExtractionLemmaSheafStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_extraction_lemma_sheaf : RootStatement := by
  first | exact @GlobalTheory.RootTrick.root_statement | exact GlobalTheory.RootTrick.root_statement | (intros; apply GlobalTheory.RootTrick.root_statement <;> assumption)
end
end
