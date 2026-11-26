module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FourfoldProductExt
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem g4lift_prj {X G : Over S} (c : Fin 4 → (X ⟶ G)) (i : Fin 4) : fourfoldProductLift c ≫ prj G i = c i := by
  fin_cases i <;> simp [fourfoldProductLift, prj]

@[reassoc] theorem g4lift_prj' {X G : Over S} (c : Fin 4 → (X ⟶ G)) (i : Fin 4) : fourfoldProductLift c ≫ prj G i = c i :=
  g4lift_prj c i

theorem fourfold_product_ext {X G : Over S} {f f' : X ⟶ G4 G} (h : ∀ i, f ≫ prj G i = f' ≫ prj G i) : f = f' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [prj] at h0 h1 h2 h3
  refine CartesianMonoidalCategory.hom_ext _ _ h0 (CartesianMonoidalCategory.hom_ext _ _ ?_
    (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)) <;> simpa only [Category.assoc] using ‹_›

instance prj.isMonHom (G : Over S) [GrpObj G] (i : Fin 4) : IsMonHom (prj G i) := by
  fin_cases i <;> simp only [prj] <;> infer_instance

def precompMH {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) : (Y ⟶ G) →* (X ⟶ G) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' a b := MonObj.comp_mul f a b

theorem comp_zpow' {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (k : ℤ) : f ≫ g ^ k = (f ≫ g) ^ k :=
  map_zpow (precompMH f) g k

theorem comp_inv' {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) : f ≫ g⁻¹ = (f ≫ g)⁻¹ :=
  map_inv (precompMH f) g

theorem comp_pow' {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (k : ℕ) : f ≫ g ^ k = (f ≫ g) ^ k :=
  map_pow (precompMH f) g k

def postcompMH {X G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] : (X ⟶ G) →* (X ⟶ H) where
  toFun g := g ≫ f
  map_one' := MonObj.one_comp f
  map_mul' a b := MonObj.mul_comp a b f

theorem pow_comp' {X G H : Over S} [GrpObj G] [GrpObj H] (g : X ⟶ G) (f : G ⟶ H) [IsMonHom f] (k : ℕ) :
    (g ^ k) ≫ f = (g ≫ f) ^ k :=
  map_pow (postcompMH f) g k

theorem comp_prod_zpow {X Y G : Over S} [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) (c : Fin 4 → (Y ⟶ G))
    (k : Fin 4 → ℤ) : f ≫ (∏ j, c j ^ k j) = ∏ j, (f ≫ c j) ^ k j := by
  simp [Fin.prod_univ_four, MonObj.comp_mul, comp_zpow']

theorem eMap'_comp_eMap (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) :
    eMap' mu α m ≫ eMap mu α m = 𝟙 (G4 (A ⊗ B)) ^ (2 * m) := by
  apply fourfold_product_ext
  intro i
  rw [Category.assoc, eMap, g4lift_prj]
  ext1
  · rw [Category.assoc, lift_fst, Category.assoc, pow_comp', Category.id_comp, MonObj.comp_mul, comp_inv',
      comp_prod_zpow]
    simp only [← Category.assoc, eMap', g4lift_prj, lift_fst, lift_snd]
    simp only [mul_inv_cancel_right]
  · rw [Category.assoc, lift_snd, Category.assoc, pow_comp', Category.id_comp, comp_pow', ← Category.assoc, eMap',
      g4lift_prj, lift_snd]

end PositivityTheory.PrwZar
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamD
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]


omit [GrpObj A] [GrpObj B] in
theorem pull_zcPair {P : LB (A ⊗ B).left} (hP : P.IsLB) (lm : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ)
    {Y Z : Over S} (w : Z ⟶ Y) (u u' : Y ⟶ G4 (A ⊗ B)) :
    pull w.left (zcPair hP lm mu α u u') = zcPair hP lm mu α (w ≫ u) (w ≫ u') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zcPair, map_add (f := _), map_sum, map_nsmul, map_zsmul, pull_evc, Category.assoc]

section Pieces

variable {P : LB (A ⊗ B).left} (hD : IsDual A B P) (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l]
  (mu : B ⟶ A) [IsMonHom mu] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left)
  (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
  {T : Over (Sp Ω)} (u u' : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B)))

include e in
theorem line_bundle_pairing_zeroth (i : Fin 4) :
    lam (pull (phiL mu s (0, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ fst A B) (toBase _ s u' ≫ prj _ i ≫ fst A B ≫ l) := by
  have hm := map_mul_pt s (prj (A ⊗ B) i ≫ fst A B) u u'
  have h1 := map_one_pt s (prj (A ⊗ B) i ≫ fst A B) (T := T)
  show lam (pull (pA s i).left (cls L hL)) u u' = _
  rw [lam_pull_pt (pA s i) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e]
  simp only [pA, toBase_map, Category.assoc]

private theorem lam_pull_inv {Ω : Type} [Field Ω] {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    (φ : G ⟶ G') (c : Pic G'.left) {T : Over (Sp Ω)} (u u' : T ⟶ G)
    (hm0 : (u * u') ≫ φ = (u ≫ φ) * (u' ≫ φ)) (h10 : (1 : T ⟶ G) ≫ φ = 1) :
    lam (pull φ⁻¹.left c) u u' = lam c (u ≫ φ⁻¹) (u' ≫ φ⁻¹) := by
  refine lam_pull_pt φ⁻¹ c u u' ?_ ?_
  · rw [GrpObj.comp_inv, GrpObj.comp_inv, GrpObj.comp_inv, hm0, mul_inv]
  · rw [GrpObj.comp_inv, h10, inv_one]

include e hD' in
theorem line_bundle_pairing_first [IsCommMonObj A] (i : Fin 4) :
    lam (pull (phiL mu s (1, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ fst A B) (toBase _ s u' ≫ prj _ i ≫ fst A B ≫ l) := by
  show lam (pull ((pA (B := B) s i)⁻¹).left (cls L hL)) u u' = _
  rw [lam_pull_inv (pA s i) _ u u' (map_mul_pt s (prj (A ⊗ B) i ≫ fst A B) u u')
      (map_one_pt s (prj (A ⊗ B) i ≫ fst A B) (T := T)),
    lam_cL_pt s hD.isLB l L hL e, GrpObj.comp_inv, GrpObj.comp_inv, toBase_inv, toBase_inv, GrpObj.inv_comp]
  simp only [pA, toBase_map, Category.assoc]
  exact evc_inv_inv hD hD' _ _

include e in
theorem line_bundle_pairing_second (i : Fin 4) :
    lam (pull (phiL mu s (2, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ snd A B ≫ mu) (toBase _ s u' ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
  have hm := map_mul_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) u u'
  have h1 := map_one_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) (T := T)
  show lam (pull (pM mu s i).left (cls L hL)) u u' = _
  rw [lam_pull_pt (pM mu s i) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e]
  simp only [pM, toBase_map, Category.assoc]

include e hD' in
theorem line_bundle_pairing_third [IsCommMonObj A] (i : Fin 4) :
    lam (pull (phiL mu s (3, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ snd A B ≫ mu) (toBase _ s u' ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
  show lam (pull ((pM mu s i)⁻¹).left (cls L hL)) u u' = _
  rw [lam_pull_inv (pM mu s i) _ u u' (map_mul_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) u u')
      (map_one_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) (T := T)),
    lam_cL_pt s hD.isLB l L hL e, GrpObj.comp_inv, GrpObj.comp_inv, toBase_inv, toBase_inv, GrpObj.inv_comp]
  simp only [pM, toBase_map, Category.assoc]
  exact evc_inv_inv hD hD' _ _

include hD hD' in
theorem evc_lam_key {Y : Over S} (a a' : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hD.isLB (a * a') (b * b') - evc hD.isLB a b - evc hD.isLB a' b' + evc hD.isLB (1 : Y ⟶ A) (1 : Y ⟶ B) =
      evc hD.isLB a b' + evc hD.isLB a' b := by
  rw [evc_mul_left hD, evc_mul_right hD hD', evc_mul_right hD hD',
    IsAdditive.evc_one hD.isLB hD.additive]
  abel

private theorem pull_pull_phiP_eq_evc (ij : Fin 4 × Fin 4) (v : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) :
    pull v.left (pull (phiP s ij) (cls P hD.isLB)) =
      evc hD.isLB (toBase _ s v ≫ prj _ ij.1 ≫ fst A B) (toBase _ s v ≫ prj _ ij.2 ≫ snd A B) := by
  have hv := toBase_comp s (G4 (A ⊗ B)) v (𝟙 _)
  rw [Category.comp_id] at hv
  rw [evc, ← pull_comp, hv]
  congr 2
  simp only [phiP, ← comp_lift, Over.comp_left]
  rfl

include hD' in
theorem lam_phiP (ij : Fin 4 × Fin 4) :
    lam (pull (phiP s ij) (cls P hD.isLB)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ ij.1 ≫ fst A B) (toBase _ s u' ≫ prj _ ij.2 ≫ snd A B) +
        evc hD.isLB (toBase _ s u' ≫ prj _ ij.1 ≫ fst A B) (toBase _ s u ≫ prj _ ij.2 ≫ snd A B) := by
  simp only [GlobalTheory.CechPic.lam, pull_pull_phiP_eq_evc hD, toBase_mul, toBase_one, MonObj.mul_comp, MonObj.one_comp]
  exact evc_lam_key hD hD' _ _ _ _

end Pieces

end PositivityTheory.PrwZar
end
end
