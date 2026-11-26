module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

def fourfoldProductLift {X G : Over S} (c : Fin 4 → (X ⟶ G)) : X ⟶ G4 G := lift (c 0) (lift (c 1) (lift (c 2) (c 3)))

variable {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def eMap (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) : G4 (A ⊗ B) ⟶ G4 (A ⊗ B) :=
  fourfoldProductLift fun i => lift ((prj _ i ≫ fst A B) * (∏ j, (prj _ j ≫ snd A B ≫ mu) ^ (α i j))⁻¹)
    ((prj _ i ≫ snd A B) ^ (2 * m))

def eMap' (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) : G4 (A ⊗ B) ⟶ G4 (A ⊗ B) :=
  fourfoldProductLift fun i => lift ((prj _ i ≫ fst A B) ^ (2 * m) * ∏ j, (prj _ j ≫ snd A B ≫ mu) ^ (α i j))
    (prj _ i ≫ snd A B)

def lPart (mu : B ⟶ A) {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) :
    LB ((Over.pullback s).obj (G4 (A ⊗ B))).left :=
  LB.LinComb L (phiL mu s) fun _ => 1

end PositivityTheory.PrwZar
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamC
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamB
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamA
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

instance isMonHom_prj (G : Over S) [GrpObj G] (i : Fin 4) : IsMonHom (prj G i) := by
  fin_cases i <;> dsimp [prj] <;> infer_instance

section Base

variable {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

theorem toBase_injective (G : Over S) {T : Over (Sp Ω)} {x y : T ⟶ (Over.pullback s).obj G}
    (h : toBase G s x = toBase G s y) : x = y := by
  have hl := congrArg CommaMorphism.left h
  have hx := Over.w x
  have hy := Over.w y
  ext1
  apply pullback.hom_ext
  · exact hl
  · dsimp at hx hy
    rw [hx, hy]

theorem toBase_mul (G : Over S) [GrpObj G] {T : Over (Sp Ω)} (x y : T ⟶ (Over.pullback s).obj G) :
    toBase G s (x * y) = toBase G s x * toBase G s y := GlobalTheory.UU.toBase_mul_pullback G s T x y

set_option synthInstance.maxHeartbeats 200000 in
theorem toBase_one (G : Over S) [GrpObj G] {T : Over (Sp Ω)} :
    toBase G s (1 : T ⟶ (Over.pullback s).obj G) = 1 := by
  have h := toBase_mul s G (1 : T ⟶ (Over.pullback s).obj G) 1
  rw [_root_.mul_one] at h
  simpa using h

theorem toBase_inv (G : Over S) [GrpObj G] {T : Over (Sp Ω)} (x : T ⟶ (Over.pullback s).obj G) :
    toBase G s x⁻¹ = (toBase G s x)⁻¹ := by
  have h := toBase_mul s G x⁻¹ x
  rw [inv_mul_cancel, toBase_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem toBase_map {G G' : Over S} (f : G ⟶ G') {T : Over (Sp Ω)} (x : T ⟶ (Over.pullback s).obj G) :
    toBase G' s (x ≫ (Over.pullback s).map f) = toBase G s x ≫ f := by
  ext
  simp [toBase, Over.pullback, pullback.lift_fst]

theorem toBase_comp (G : Over S) {T T' : Over (Sp Ω)} (v : T' ⟶ T) (x : T ⟶ (Over.pullback s).obj G) :
    toBase G s (v ≫ x) = (Over.homMk v.left (by dsimp; rw [← Category.assoc, Over.w v]) : Over.mk (T'.hom ≫ s) ⟶ Over.mk (T.hom ≫ s)) ≫
      toBase G s x := by
  apply Over.OverMorphism.ext
  simp [toBase]

end Base

end PositivityTheory.PrwZar
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

section Biadd

variable {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hD : IsDual A B P)
  (hD' : IsDual B A (swap P)) {Y : Over S}

include hD in
theorem evc_mul_left (a a' : Y ⟶ A) (b : Y ⟶ B) :
    evc hD.isLB (a * a') b = evc hD.isLB a b + evc hD.isLB a' b :=
  (isAdditive_iff hD.isLB).1 hD.additive Y a a' b

include hD hD' in
theorem evc_mul_right (a : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hD.isLB a (b * b') = evc hD.isLB a b + evc hD.isLB a b' := by
  rw [← evc_swap hD.isLB hD'.isLB, (isAdditive_iff hD'.isLB).mp hD'.additive Y b b' a, evc_swap, evc_swap]

include hD in
theorem evc_one_l (b : Y ⟶ B) : evc hD.isLB (1 : Y ⟶ A) b = 0 := hD.additive.evc_one hD.isLB b

include hD in
theorem evc_one_r (a : Y ⟶ A) : evc hD.isLB a (1 : Y ⟶ B) = 0 := evc_one_right hD.isLB hD.zero a

include hD hD' in
theorem evc_inv_inv (a : Y ⟶ A) (b : Y ⟶ B) : evc hD.isLB a⁻¹ b⁻¹ = evc hD.isLB a b := by
  have hl : evc hD.isLB a⁻¹ b⁻¹ = - evc hD.isLB a b⁻¹ := by
    have h := evc_mul_left hD a⁻¹ a b⁻¹
    rw [_root_.inv_mul_cancel, evc_one_l hD] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hr : evc hD.isLB a b⁻¹ = - evc hD.isLB a b := by
    have h := evc_mul_right hD hD' a b⁻¹ b
    rw [_root_.inv_mul_cancel, evc_one_r hD] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  rw [hl, hr, neg_neg]

end Biadd

section abelian₂

variable {S' : Scheme.{0}} {G G' T : Over S'} [GrpObj G] [GrpObj G']

def lamHom (x y : T ⟶ G) : Pic G.left →+ Pic T.left :=
  pull (x * y).left - pull x.left - pull y.left + pull (1 : T ⟶ G).left

theorem lam_eq_lamHom (c : Pic G.left) (x y : T ⟶ G) : lam c x y = lamHom x y c := by
  simp [lam, lamHom]

theorem lam_pull_pt (φ : G ⟶ G') (c : Pic G'.left) (x y : T ⟶ G) (hm : (x * y) ≫ φ = (x ≫ φ) * (y ≫ φ))
    (h1 : (1 : T ⟶ G) ≫ φ = 1) : lam (pull φ.left c) x y = lam c (x ≫ φ) (y ≫ φ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, hm, h1]

end abelian₂

section Fib

variable {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

theorem map_mul_pt {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {T : Over (Sp Ω)}
    (x y : T ⟶ (Over.pullback s).obj G) :
    (x * y) ≫ (Over.pullback s).map f = (x ≫ (Over.pullback s).map f) * (y ≫ (Over.pullback s).map f) := by
  apply toBase_injective s
  rw [toBase_map, toBase_mul, toBase_mul, toBase_map, toBase_map, MonObj.mul_comp]

set_option synthInstance.maxHeartbeats 200000 in
theorem map_one_pt {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {T : Over (Sp Ω)} :
    (1 : T ⟶ (Over.pullback s).obj G) ≫ (Over.pullback s).map f = 1 := by
  apply toBase_injective s G'
  rw [toBase_map, toBase_one, toBase_one, MonObj.one_comp]

end Fib

end PositivityTheory.PrwZar
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)


omit [GrpObj B] in
theorem lam_cL_pt {P : LB (A ⊗ B).left} (hP : P.IsLB) (l : A ⟶ B) (L : LB ((Over.pullback s).obj A).left)
    (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {T : Over (Sp Ω)} (p q : T ⟶ (Over.pullback s).obj A) :
    lam (cls L hL) p q = evc hP (toBase A s p) (toBase A s q ≫ l) := by
  have hLam := GlobalTheory.FullSiegel.isLB_lam (G := (Over.pullback s).obj A) hL
  have hE : (ev P (fst A A) (snd A A ≫ l)).IsLB := LB.isLB_pull hP _
  have hM := LB.isLB_pull hE (sqToBase A s)
  have hc : cls (abelian₂ ((Over.pullback s).obj A) L) hLam = cls _ hM := (cls_eq_iff hLam hM).mpr (LBIso.symm e)
  rw [← GlobalTheory.FullSiegel.cls_lam_pull hL p q, cls_pull hLam, hc, cls_pull hE, cls_ev hP]
  have hw : sqToBase A s = Over.Hom.left (lift (toBase A s (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)))
      (toBase A s (snd ((Over.pullback s).obj A) ((Over.pullback s).obj A)))) := rfl
  rw [hw, pull_evc, lift_fst, lift_snd_assoc]
  have e1 := toBase_comp s A (lift p q) (fst _ _)
  have e2 := toBase_comp s A (lift p q) (snd _ _)
  rw [lift_fst] at e1
  rw [lift_snd] at e2
  rw [e1, e2, Category.assoc (Over.homMk _ _) _ l, ← pull_evc]
  rfl

theorem pull_phiP {P : LB (A ⊗ B).left} (hP : P.IsLB) {T : Over (Sp Ω)}
    (v : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) (ij : Fin 4 × Fin 4) :
    pull v.left (pull (phiP s ij) (cls P hP)) =
      evc hP (toBase _ s v ≫ prj _ ij.1 ≫ fst A B) (toBase _ s v ≫ prj _ ij.2 ≫ snd A B) := by
  have e1 := toBase_comp s (G4 (A ⊗ B)) v (𝟙 _)
  rw [Category.comp_id] at e1
  rw [evc, e1, ← comp_lift, Category.assoc, Over.comp_left, pull_comp]
  rfl

end PositivityTheory.PrwZar
end
end
