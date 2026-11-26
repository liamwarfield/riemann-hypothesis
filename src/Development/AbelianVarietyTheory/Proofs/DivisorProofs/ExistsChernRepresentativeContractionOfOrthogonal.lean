module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContrCupFormEqZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem contr_cup_form_eq_zero (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (v : epsR R ⟶ B) (hv : IsTangent v) (α : Form (A.hom ≫ 𝟙 _))
    (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (κ : Fn1 A)
    (hκ : IsContr (cupZ _ (m₁.coef.pullbackOneCocycle α.1) (m₂.coef.pullbackOneCocycle b)).1 v κ)
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) : κ D D' φ x = 0 := by
  obtain ⟨s, i, s', i', a, b', τ, hs, hi, hs', hi', ha, hb, hτ⟩ :=
    (ContrMor.exists_contr R A B v hv).1 D D' φ x
  rw [hκ D D' φ x s i s' i' a b' τ hs hi hs' hi' ha hb hτ]
  have ha0 : (m₁.coef.pullbackOneCocycle α.1).1 _ _ a = 0 := α.2 (m₁.functor.map a) rfl rfl
  have hb0 : (m₁.coef.pullbackOneCocycle α.1).1 _ _ b' = 0 := α.2 (m₁.functor.map b') rfl rfl
  let e : m₁.functor.obj (trivAt (pt0 B x)) ⟶ m₁.functor.obj (trivAt (ptV v x)) :=
    { φ := { toRingHom := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D),
             commutes' := fun r ↦ (TrivSqZeroExt.inlAlgHom R D D).commutes r }
      φ₀ := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D)
      comm := fun _ ↦ rfl
      dp := isDPMorphism_of_eq_bot _ rfl _ _
      pt := by
        have h1 : pt0 B x ≫ fst A B = x := lift_fst _ _
        have h2 : ptV v x ≫ fst A B =
            (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ x : Pt A (DualNumber D)) := lift_fst _ _
        change spMap (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) ≫
          (pt0 B x).left ≫ (fst A B).left = (ptV v x).left ≫ (fst A B).left
        rw [← Over.comp_left, h1, ← Over.comp_left, h2, Over.comp_left]
        rfl }
  have he0 : α.1.1 _ _ e = 0 := α.2 e rfl rfl
  have hes : e ≫ m₁.functor.map i = m₁.functor.map s := Thick.Hom.ext' (AlgHom.ext fun c ↦ by
    change i.φ (TrivSqZeroExt.inl c) = s.φ c
    rw [hi]
    exact (hs c).symm)
  have hsi : (m₁.coef.pullbackOneCocycle α.1).1 _ _ s = (m₁.coef.pullbackOneCocycle α.1).1 _ _ i := by
    change α.1.1 _ _ (m₁.functor.map s) = α.1.1 _ _ (m₁.functor.map i)
    rw [← hes]
    have h := GlobalTheory.Cris.ev_comp α.1 e (m₁.functor.map i)
    simp only [GlobalTheory.Cris.ev] at h
    rw [h, he0, map_zero, zero_add]
  simp only [cupZ_apply]
  rw [ha0, hb0, hsi]
  simp

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointWithZeroSecondCoordLeftCompSnd
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.CupA

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem spOver_left {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (spOver (R := R) φ).left = spMap (φ : D →+* D') := rfl

theorem pointWithZeroSecondCoord_left_comp_fst {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (pt0 B x).left ≫ (fst A B).left = x.left := by
  rw [← Over.comp_left]; unfold pt0; rw [lift_fst]

theorem ptV_fst (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (ptV v x).left ≫ (fst A B).left = spMap (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) ≫ x.left := by
  rw [← Over.comp_left]; unfold ptV; rw [lift_fst]; rfl

theorem ptV_snd (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (ptV v x).left ≫ (snd A B).left = spMap (EpsWeil.epsMap R D : DualNumber R →+* DualNumber D) ≫ v.left := by
  rw [← Over.comp_left]; unfold ptV; rw [lift_snd]; rfl

theorem pointWithZeroSecondCoord_left_comp_snd (v : epsR R ⟶ B) (hv : IsTangent v) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (pt0 B x).left ≫ (snd A B).left =
      spMap (TrivSqZeroExt.fstHom R D D : DualNumber D →+* D) ≫ spMap (EpsWeil.epsMap R D : DualNumber R →+* DualNumber D) ≫ v.left := by
  have h := congrArg (fun p : Pt (A ⊗ B) D ↦ (p ≫ snd A B).left)
    (ContrMor.spOver_fst_ptV v hv x).symm
  simpa only [Over.comp_left, spOver_left, Category.assoc, ptV_snd] using h

theorem epsMap_fst {D : Type} [CommRing D] [Algebra R D] (c : DualNumber R) :
    (EpsWeil.epsMap R D c).fst = algebraMap R D c.fst := by
  simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem epsMap_inl {D : Type} [CommRing D] [Algebra R D] (b : R) :
    EpsWeil.epsMap R D (TrivSqZeroExt.inl b) = TrivSqZeroExt.inl (algebraMap R D b) := by
  simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem epsMap_inr {D : Type} [CommRing D] [Algebra R D] (b : R) :
    EpsWeil.epsMap R D (TrivSqZeroExt.inr b) = TrivSqZeroExt.inr (algebraMap R D b) := by
  ext <;> simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl', Algebra.smul_def]

theorem snd_epsHom' {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z : DualNumber D) : (epsHom φ z).snd = φ z.snd := by
  simp [epsHom, DualNumber.lift_apply_apply]

theorem epsHom_inl' {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (r : D) : epsHom φ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r) := by
  ext
  · simp [epsHom, DualNumber.lift_apply_apply]
  · simp [snd_epsHom']

theorem dualVal_eq (v : epsR R ⟶ B) (β : Form (B.hom ≫ 𝟙 _)) :
    (SqExt.dual R).val v.left (pt_w v) β.1 = TrivSqZeroExt.inr (tanVal v β) := by
  ext
  · exact (SqExt.dual R).π_val v.left (pt_w v) β
  · exact (tanVal_apply v β).symm

def eA (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    m₁.functor.obj (trivAt (pt0 B x)) ⟶ m₁.functor.obj (trivAt (ptV v x)) where
  φ := { (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) with
    commutes' := fun r ↦ (TrivSqZeroExt.inlAlgHom R D D).commutes r }
  φ₀ := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D)
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) ≫ (pt0 B x).left ≫ (fst A B).left =
      (ptV v x).left ≫ (fst A B).left
    rw [pointWithZeroSecondCoord_left_comp_fst, ptV_fst]

def uA (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    trivAt x ⟶ m₁.functor.obj (trivAt (pt0 B x)) where
  φ := { RingHom.id D with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id D
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (RingHom.id D) ≫ x.left = (pt0 B x).left ≫ (fst A B).left
    rw [pointWithZeroSecondCoord_left_comp_fst, spMap_id]
    exact Category.id_comp _

abbrev yV (v : epsR R ⟶ B) (D : Type) [CommRing D] [Algebra R D] : Sp (DualNumber D) ⟶ B.left :=
  spMap (EpsWeil.epsMap R D : DualNumber R →+* DualNumber D) ≫ v.left

theorem yV_w (v : epsR R ⟶ B) (D : Type) [CommRing D] [Algebra R D] :
    yV v D ≫ B.hom ≫ 𝟙 _ = spMap (algebraMap R (epsExt R D).C) :=
  pt_w (spOver (EpsWeil.epsMap R D) ≫ v)

section Bside

variable (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
  (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D)

def cB (hv : IsTangent v) : (epsExt R D).thick _ ((epsExt R D).red_w (yV_w v D)) ⟶ m₂.functor.obj (thickAt B x) where
  φ := { RingHom.id (DualNumber D) with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id D
  comm := fun _ ↦ rfl
  dp := (DividedPowers.DPMorphism.id _).isDPMorphism
  pt := by
    change spMap (RingHom.id D) ≫ spMap (TrivSqZeroExt.fstHom R D D : DualNumber D →+* D) ≫ yV v D =
      (pt0 B x).left ≫ (snd A B).left
    rw [pointWithZeroSecondCoord_left_comp_snd v hv, spMap_id]
    exact Category.id_comp _

def u0B (hv : IsTangent v) : Thick.triv (epsExt R D).B _ ((epsExt R D).red_w (yV_w v D)) ⟶ m₂.functor.obj (trivAt (pt0 B x)) where
  φ := { RingHom.id D with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id D
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (RingHom.id D) ≫ spMap (TrivSqZeroExt.fstHom R D D : DualNumber D →+* D) ≫ yV v D =
      (pt0 B x).left ≫ (snd A B).left
    rw [pointWithZeroSecondCoord_left_comp_snd v hv, spMap_id]
    exact Category.id_comp _

def u1B : Thick.triv (epsExt R D).C (yV v D) (yV_w v D) ⟶ m₂.functor.obj (trivAt (ptV v x)) where
  φ := { RingHom.id (DualNumber D) with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id (DualNumber D)
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (RingHom.id (DualNumber D)) ≫ yV v D = (ptV v x).left ≫ (snd A B).left
    rw [ptV_snd, spMap_id]
    exact Category.id_comp _

theorem bval (hv : IsTangent v) (β : Form (B.hom ≫ 𝟙 _)) (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
    (hs : ∀ r, s.φ r = TrivSqZeroExt.inl r) (hi : ∀ r, i.φ r = r) :
    ev β.1 (m₂.functor.map s) - ev β.1 (m₂.functor.map i) =
      TrivSqZeroExt.inr (algebraMap R D (tanVal v β)) := by
  let E := epsExt R D
  have k1 := Form.ev_sq β (u0B m₂ v x hv) (m₂.functor.map s) (E.secHom (E.red_w (yV_w v D)) E.i E.π_i)
    (cB m₂ v x hv) rfl rfl (fun r ↦ by
      change s.φ r = TrivSqZeroExt.inl r
      exact hs r)
  have k2 := Form.ev_sq β (u1B m₂ v x) (m₂.functor.map i) (E.idHom (yV_w v D))
    (cB m₂ v x hv) rfl rfl (fun r ↦ by
      change i.φ r = r
      exact hi r)
  rw [k1, k2]
  rw [add_sub_add_right_eq_sub, ← map_sub]
  have vm := (SqExt.dual R).val_map E (EpsWeil.epsMap R D) (Algebra.ofId R D)
    (fun c ↦ (epsMap_fst c).symm) (fun b ↦ epsMap_inl b) v.left (pt_w v) (yV v D) (yV_w v D) rfl β
  calc _ = E.val (yV v D) (yV_w v D) β.1 := rfl
    _ = _ := by rw [vm, dualVal_eq]; exact epsMap_inr _

end Bside

theorem alg {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (t : R)
    (Ae Ai As Bi : DualNumber D) (Bτ Bi' Bs' Ab Ae' X1 X2 X3 X4 Y1 Y2 W : DualNumber D') (Aa fvv fvt C' Z : D') (C : D)
    (hX1 : X1 = epsHom φ As) (hX2 : X2 = TrivSqZeroExt.inl Aa) (hX3 : X3 = epsHom φ Ai) (hX4 : Ab = X4)
    (hY1 : Y1 = TrivSqZeroExt.inl Aa) (hY2 : Y2 = epsHom φ Ae) (hW : W = epsHom φ Bi) (hZ : Z = φ C)
    (hfvt : fvt = (-t) • fvv)
    (hAs : As = Ae + Ai) (hAb : Y1 + Ae' = Y2 + Ab) (hAa : fvv + C' = Z + Aa)
    (hBτ : Bi' = W + Bτ) (hBs : Bs' - Bi' = TrivSqZeroExt.inr (algebraMap R D' t)) :
    (X1 * Bτ - X2 * Bs' - X3 * Bτ + X4 * Bi').snd + -fvt =
      ((Ae' * Bi').snd - algebraMap R D' t * C') - φ ((Ae * Bi).snd - algebraMap R D t * C) := by
  subst hX1 hX2 hX3 hX4 hY1 hY2 hW hZ hfvt
  have h1 : epsHom φ As = epsHom φ Ae + epsHom φ Ai := by rw [hAs, map_add (f := _)]
  have key : epsHom φ As * Bτ - TrivSqZeroExt.inl Aa * Bs' - epsHom φ Ai * Bτ + Ab * Bi' =
      Ae' * Bi' - epsHom φ (Ae * Bi) - TrivSqZeroExt.inl Aa * TrivSqZeroExt.inr (algebraMap R D' t) := by
    rw [map_mul]
    linear_combination Bτ * h1 - Bi' * hAb - epsHom φ Ae * hBτ - TrivSqZeroExt.inl Aa * hBs
  rw [key, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_sub, snd_epsHom', TrivSqZeroExt.inl_mul_inr,
    TrivSqZeroExt.snd_inr, smul_eq_mul, map_sub, map_mul, AlgHom.commutes, Algebra.smul_def, map_neg]
  linear_combination (algebraMap R D' t) * hAa


open Classical in
def kFn (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (v : epsR R ⟶ B) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Form (B.hom ≫ 𝟙 _)) : Fn0 A := fun D _ _ x ↦
  if h : ∃ i : trivAt (ptV v x) ⟶ thickAt B x, ∀ r, i.φ r = r then
    ((show DualNumber D from ev a (eA m₁ v x)) * (show DualNumber D from ev β.1 (m₂.functor.map h.choose))).snd -
      algebraMap R D (tanVal v β) * (show D from ev a (uA m₁ x))
  else 0

theorem kFn_eq (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (v : epsR R ⟶ B) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Form (B.hom ≫ 𝟙 _)) {D : Type} [CommRing D]
    [Algebra R D] (x : Pt A D) (i : trivAt (ptV v x) ⟶ thickAt B x) (hi : ∀ r, i.φ r = r) :
    kFn m₁ m₂ v a β D x =
      ((show DualNumber D from ev a (eA m₁ v x)) * (show DualNumber D from ev β.1 (m₂.functor.map i))).snd -
        algebraMap R D (tanVal v β) * (show D from ev a (uA m₁ x)) := by
  have h : ∃ i : trivAt (ptV v x) ⟶ thickAt B x, ∀ r, i.φ r = r := ⟨i, hi⟩
  unfold kFn
  rw [dite_eq_left h]
  congr 3
  have he : h.choose = i := Thick.Hom.ext' (AlgHom.ext fun r ↦ (h.choose_spec r).trans (hi r).symm)
  exact congrArg (fun j ↦ ev β.1 (m₂.functor.map j)) he

end GlobalTheory.PtExt.CupA

open GlobalTheory.PtExt.CupA in
theorem GlobalTheory.PtExt.cohom_contr_cupA : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (v : epsR R ⟶ B), IsTangent v → ∀ (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Form (B.hom ≫ 𝟙 _)) (κ : Fn1 A), IsContr (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle β.1)).1 v κ → Cohom (whole A) κ (fv ((-tanVal v β) • a)) := by
  intro R _ A B _ _ m₁ m₂ v hv a β κ hκ
  refine ⟨kFn m₁ m₂ v a β, ?_⟩
  intro D _ _ D' _ _ φ x _
  obtain ⟨s, i, s', i', a', b, τ, hs, hi, hs', hi', ha, hb, hτ⟩ := (GlobalTheory.T.exists_tangentVector_contraction_twoCochain_product R A B v hv).1 D D' φ x
  have hK := hκ D D' φ x s i s' i' a' b τ hs hi hs' hi' ha hb hτ
  change κ D D' φ x = TrivSqZeroExt.snd (R := D') (M := D')
    ((show DualNumber D' from τ.φ (ev a (m₁.functor.map s))) * (show DualNumber D' from ev β.1 (m₂.functor.map τ)) -
      (show DualNumber D' from s'.φ (ev a (m₁.functor.map a'))) * (show DualNumber D' from ev β.1 (m₂.functor.map s')) -
      (show DualNumber D' from τ.φ (ev a (m₁.functor.map i))) * (show DualNumber D' from ev β.1 (m₂.functor.map τ)) +
      (show DualNumber D' from i'.φ (ev a (m₁.functor.map b))) * (show DualNumber D' from ev β.1 (m₂.functor.map i'))) at hK
  have fAs : (show DualNumber D from ev a (m₁.functor.map s)) = (show DualNumber D from ev a (eA m₁ v x)) + (show DualNumber D from ev a (m₁.functor.map i)) := by
    rw [show m₁.functor.map s = eA m₁ v x ≫ m₁.functor.map i from Thick.Hom.ext' (AlgHom.ext fun r ↦ by
      change s.φ r = i.φ (TrivSqZeroExt.inl r)
      exact (hs r).trans (hi _).symm), ev_comp]
    change i.φ _ + _ = _
    erw [hi]
  have fAb := ev_sq a (m₁.functor.map a') (eA m₁ v (spOver φ ≫ x)) (eA m₁ v x) (m₁.functor.map b) (fun r ↦ by
    change TrivSqZeroExt.inl (a'.φ r) = b.φ (TrivSqZeroExt.inl r)
    exact (congrArg TrivSqZeroExt.inl (ha r)).trans ((hb _).trans (epsHom_inl' φ r)).symm)
  have fAa := ev_sq a (trivMap φ x) (uA m₁ (spOver φ ≫ x)) (uA m₁ x) (m₁.functor.map a') (fun r ↦ by
    change φ r = a'.φ r
    exact (ha r).symm)
  have fBτ := Form.ev_sq β (m₂.functor.map b) (m₂.functor.map i') (m₂.functor.map i) (m₂.functor.map τ) rfl rfl
    (fun r ↦ by
      change i'.φ (b.φ r) = τ.φ (i.φ r)
      exact (hi' _).trans ((hb r).trans (((congrArg τ.φ (hi r)).trans (hτ r)).symm)))
  have fBs := bval m₂ v (spOver φ ≫ x) hv β s' i' hs' hi'
  have e1 := kFn_eq m₁ m₂ v a β x i hi
  have e2 := kFn_eq m₁ m₂ v a β (spOver φ ≫ x) i' hi'
  change (Fn1.add κ (fv ((-tanVal v β) • a)).neg) D D' φ x = _
  unfold Fn1.add Fn1.neg
  rw [hK, e1, e2]
  exact alg φ (tanVal v β) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fv a D D' φ x) _ _ _ _ (hτ _) (hs' _) (hτ _) (hi' _).symm
    rfl (hb _) (hτ _) (ha _) rfl fAs fAb fAa fBτ fBs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorEqZeroOfForallDualPairing
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tensor_eq_zero_of_forall_dual_pairing {R : Type} [CommRing R] {M N : Type 1}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R M] [Module.Projective R N] (u : M ⊗[R] N)
    (h : ∀ (x : Module.Dual R M) (y : Module.Dual R N),
      TensorProduct.lift ((LinearMap.mul R R).compl₁₂ x y) u = 0) : u = 0 := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := R) (P := M)
  obtain ⟨s', hs'⟩ := Module.Projective.out (R := R) (P := N)
  have key : ∀ (w : M ⊗[R] N) (c : M) (c' : N),
      finsuppTensorFinsupp' R M N (TensorProduct.map s s' w) (c, c') =
        TensorProduct.lift ((LinearMap.mul R R).compl₁₂ ((Finsupp.lapply c).comp s)
          ((Finsupp.lapply c').comp s')) w := by
    intro w c c'
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [finsuppTensorFinsupp'_apply_apply]
    | add v w hv hw => simp only [map_add (f := _), Finsupp.add_apply, hv, hw]
  have h0 : TensorProduct.map s s' u = 0 := by
    apply (finsuppTensorFinsupp' R M N).injective
    rw [map_zero]
    ext ⟨c, c'⟩
    rw [key]
    exact h _ _
  have hl : (Finsupp.linearCombination R id).comp s = LinearMap.id := LinearMap.ext hs
  have hl' : (Finsupp.linearCombination R id).comp s' = LinearMap.id := LinearMap.ext hs'
  have : u = TensorProduct.map (Finsupp.linearCombination R id) (Finsupp.linearCombination R id)
      (TensorProduct.map s s' u) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hl, hl', TensorProduct.map_id,
      LinearMap.id_apply]
  rw [this, h0, map_zero]

theorem tensor_mem_of_dualAnnihilator : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Projective R M] [Module.Projective R N] (F : Submodule R M) (F' : Submodule R N), (∃ C, IsCompl F C) → (∃ C, IsCompl F' C) → (∀ c : M, (∀ h ∈ F.dualAnnihilator, h c = 0) → c ∈ F) ∧ ∀ (n : ℕ) (a : Fin n → M) (b : Fin n → N), (∀ x ∈ F.dualAnnihilator, ∀ y ∈ F'.dualAnnihilator, ∑ k, x (a k) * y (b k) = 0) → ∃ (a₁ : Fin n → M) (b₁ : Fin n → N), (∀ k, a₁ k ∈ F) ∧ (∀ k, b₁ k ∈ F') ∧ ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0 := by
  intro R _ M N _ _ _ _ _ _ F F' ⟨C, hC⟩ ⟨C', hC'⟩
  set e : M →ₗ[R] M := C.subtype.comp (C.linearProjOfIsCompl F hC.symm) with he
  set e' : N →ₗ[R] N := C'.subtype.comp (C'.linearProjOfIsCompl F' hC'.symm) with he'
  have eF : ∀ f ∈ F, e f = 0 := fun f hf => by
    rw [he, LinearMap.comp_apply, show C.linearProjOfIsCompl F hC.symm f = 0 from
      Submodule.linearProjOfIsCompl_apply_right hC.symm ⟨f, hf⟩, map_zero]
  have eF' : ∀ f ∈ F', e' f = 0 := fun f hf => by
    rw [he', LinearMap.comp_apply, show C'.linearProjOfIsCompl F' hC'.symm f = 0 from
      Submodule.linearProjOfIsCompl_apply_right hC'.symm ⟨f, hf⟩, map_zero]
  have sub : ∀ m, m - e m ∈ F := fun m => by
    rw [← Submodule.linearProjOfIsCompl_ker hC.symm, LinearMap.mem_ker, map_sub, he,
      LinearMap.comp_apply, Submodule.subtype_apply, Submodule.linearProjOfIsCompl_apply_left]
    exact sub_self _
  have sub' : ∀ m, m - e' m ∈ F' := fun m => by
    rw [← Submodule.linearProjOfIsCompl_ker hC'.symm, LinearMap.mem_ker, map_sub, he',
      LinearMap.comp_apply, Submodule.subtype_apply, Submodule.linearProjOfIsCompl_apply_left]
    exact sub_self _
  have ann : ∀ x : Module.Dual R M, x.comp e ∈ F.dualAnnihilator := fun x => by
    rw [Submodule.mem_dualAnnihilator]; intro f hf; simp [eF f hf]
  have ann' : ∀ y : Module.Dual R N, y.comp e' ∈ F'.dualAnnihilator := fun y => by
    rw [Submodule.mem_dualAnnihilator]; intro f hf; simp [eF' f hf]
  refine ⟨fun c hc => ?_, fun n a b hab => ?_⟩
  · have : e c = 0 := (Module.forall_dual_apply_eq_zero_iff R (e c)).mp fun x => hc _ (ann x)
    simpa [this] using sub c
  · refine ⟨fun k => a k - e (a k), fun k => b k - e' (b k), fun k => sub _, fun k => sub' _, ?_⟩
    simp only [sub_sub_cancel]
    apply tensor_eq_zero_of_forall_dual_pairing
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
    exact hab _ (ann x) _ (ann' y)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernRepresentativeContractionOfOrthogonal
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ChernRep

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem isContr_add {z z' : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B} {κ κ' : Fn1 A}
    (h : IsContr z v κ) (h' : IsContr z' v κ') : IsContr (z + z') v (κ.add κ') := by
  unfold IsContr at h h' ⊢
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  simp only [Fn1.add, Pi.add_apply, h D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ,
    h' D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub]
  abel

theorem isContr_sum {n : ℕ} {z : Fin n → C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B}
    {κ : Fin n → Fn1 A} (h : ∀ k, IsContr (z k) v (κ k)) :
    IsContr (∑ k, z k) v (fun D _ _ D' _ _ φ x ↦ ∑ k, κ k D D' φ x) := by
  unfold IsContr at h ⊢
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun k _ ↦ h k D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have key : ∀ g : Fin n → TrivSqZeroExt D' D', ∑ k, (g k).snd = (∑ k, g k).snd := fun g ↦
    (map_sum (TrivSqZeroExt.sndHom D' D') g Finset.univ).symm
  exact key fun k ↦ z k _ _ _ s τ - z k _ _ _ a s' - z k _ _ _ i τ + z k _ _ _ b i'

theorem isContr_eq {z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B} (hv : IsTangent v)
    {κ κ' : Fn1 A} (h : IsContr z v κ) (h' : IsContr z v κ') (D : Type) [CommRing D] [Algebra R D]
    (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    κ D D' φ x = κ' D D' φ x := by
  obtain ⟨s, i, s', i', a, b, τ, hs, hi, hs', hi', ha, hb, hτ⟩ :=
    (GlobalTheory.PtExt.ContrMor.exists_contr R A B v hv).1 D D' φ x
  exact (h D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ).trans
    (h' D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ).symm

theorem sum_split {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (Φ : M →ₗ[R] N →ₗ[R] P) {n : ℕ} (a a₁ : Fin n → M) (b b₁ : Fin n → N)
    (h : ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0) :
    ∑ k, Φ (a k) (b k) = ∑ k, Φ (a₁ k) (b k) + ∑ k, Φ (a k - a₁ k) (b₁ k) := by
  have h0 : ∑ k, Φ (a k - a₁ k) (b k - b₁ k) = 0 := by
    have := congrArg (TensorProduct.lift Φ) h
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, TensorProduct.lift.tmul, map_zero] using this
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [map_sub, LinearMap.sub_apply]
  abel

theorem fv_sub_sum {X : Over (Sp R)} {n : ℕ} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (t : Fin n → R)
    (u : Fin n → Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [Algebra R D] (D' : Type)
    [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (f - ∑ k, t k • u k) D D' φ x = fv f D D' φ x - ∑ k, algebraMap R D' (t k) * fv (u k) D D' φ x := by
  simp only [fv, ev, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
  rfl

theorem fv_smul {X : Over (Sp R)} (t : R) (u : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D]
    [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (t • u) D D' φ x = algebraMap R D' t * fv u D D' φ x := by
  simp only [fv, ev, Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]

section Rep

variable (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
  (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)


omit [GrpObj A] [GrpObj B] in
def cupPr (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)


omit [GrpObj A] [GrpObj B] in
theorem mk_cupPr (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    CatCoh.H2.mk _ (cupPr m₁ m₂ a b) = cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ a))
      (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ b)) := rfl

def cupPrim (A B : Over (Sp R)) [GrpObj A] [GrpObj B] :
    primDR A →ₗ[R] primDR B →ₗ[R] CatCoh.H2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  (cup _).compl₁₂ (pullOver (dp0 R) (𝟙 _) (fst A B) ∘ₗ (primDR A).subtype)
    (pullOver (dp0 R) (𝟙 _) (snd A B) ∘ₗ (primDR B).subtype)

theorem cupPrim_apply (a : primDR A) (b : primDR B) : cupPrim A B a b =
    cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) a.1) (pullOver (dp0 R) (𝟙 _) (snd A B) b.1) := rfl

theorem mk_cupPr_prim {a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))} {x : primDR A}
    {y : primDR B} (ha : CatCoh.H1.mk _ a = x.1) (hb : CatCoh.H1.mk _ b = y.1) :
    CatCoh.H2.mk _ (cupPr m₁ m₂ a b) = cupPrim A B x y := by
  rw [mk_cupPr, cupPrim_apply, ha, hb]

variable {n : ℕ} (α : Fin n → Form (A.hom ≫ 𝟙 _)) (β : Fin n → Form (B.hom ≫ 𝟙 _))
  (a' : Fin n → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b' : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))


omit [GrpObj A] [GrpObj B] in
def rep : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  ∑ k, cupPr m₁ m₂ (α k).1 (b' k) + ∑ k, cupPr m₁ m₂ (a' k) (β k).1


omit [GrpObj A] [GrpObj B] in
theorem rep_val : (rep m₁ m₂ α β a' b').1 =
    ∑ k, (cupPr m₁ m₂ (α k).1 (b' k)).1 + ∑ k, (cupPr m₁ m₂ (a' k) (β k).1).1 := by
  rw [rep, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_sum]


omit [GrpObj A] [GrpObj B] in
theorem mk_rep : CatCoh.H2.mk _ (rep m₁ m₂ α β a' b') =
    ∑ k, CatCoh.H2.mk _ (cupPr m₁ m₂ (α k).1 (b' k)) + ∑ k, CatCoh.H2.mk _ (cupPr m₁ m₂ (a' k) (β k).1) :=
  ((CatCoh.H2.mk _).map_add _ _).trans (congrArg₂ (· + ·) (map_sum _ _ _) (map_sum _ _ _))


omit [GrpObj A] [GrpObj B] in
theorem rep_triv (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (p : T ⟶ T') (q : T' ⟶ T'') (hT : T.J = ⊥)
    (hT' : T'.J = ⊥) (hT'' : T''.J = ⊥) : (rep m₁ m₂ α β a' b').1 T T' T'' p q = 0 := by
  have h1 : ∀ k, (cupPr m₁ m₂ (α k).1 (b' k)).1 T T' T'' p q = 0 := fun k ↦ by
    rw [cupPr, cupZ_apply,
      show (m₁.coef.pullbackOneCocycle (α k).1).1 T T' p = 0 from (α k).2 (m₁.functor.map p) hT hT', map_zero, zero_mul]
  have h2 : ∀ k, (cupPr m₁ m₂ (a' k) (β k).1).1 T T' T'' p q = 0 := fun k ↦ by
    rw [cupPr, cupZ_apply,
      show (m₂.coef.pullbackOneCocycle (β k).1).1 T' T'' q = 0 from (β k).2 (m₂.functor.map q) hT' hT'', mul_zero]
  rw [rep_val]
  simp only [Pi.add_apply, Finset.sum_apply, h1, h2, Finset.sum_const_zero, add_zero]

theorem rep_contr {v : epsR R ⟶ B} (hv : IsTangent v) (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)))
    (hcl : CatCoh.H1.mk _ (f - ∑ k, tanVal v (β k) • a' k) ∈ F1 (A.hom ≫ 𝟙 _)) (κ : Fn1 A)
    (hκ : IsContr (rep m₁ m₂ α β a' b').1 v κ) : Cohom (whole A) κ (fv f).neg := by
  obtain ⟨-, hex⟩ := GlobalTheory.PtExt.ContrMor.exists_contr R A B v hv
  choose κX hκX using fun k ↦ hex (cupPr m₁ m₂ (α k).1 (b' k)).1
  choose κY hκY using fun k ↦ hex (cupPr m₁ m₂ (a' k) (β k).1).1
  rw [rep_val] at hκ
  have hsC := isContr_add (isContr_sum hκX) (isContr_sum hκY)
  have hX0 := fun k ↦ GlobalTheory.PtExt.contr_cup_form_eq_zero R A B m₁ m₂ v hv (α k) (b' k) (κX k) (hκX k)
  have hYc := fun k ↦ GlobalTheory.PtExt.cohom_contr_cupA R A B m₁ m₂ v hv (a' k) (β k) (κY k) (hκY k)
  unfold Cohom at hYc
  choose cY hcY using hYc
  obtain ⟨k₀, hk₀⟩ := (GlobalTheory.PtExt.mem_hodgeFiltration_iff_pointwiseCoboundary R A _).1 hcl
  refine ⟨fun D _ _ x ↦ k₀ D x + ∑ k, cY k D x, ?_⟩
  intro D _ _ D' _ _ φ x _
  have e1 := isContr_eq hv hκ hsC D D' φ x
  have e2 := hk₀ D D' φ x (sm_whole x)
  have e3 : ∀ k, κY k D D' φ x = cY k D' (spOver φ ≫ x) - φ (cY k D x) -
      algebraMap R D' (tanVal v (β k)) * fv (a' k) D D' φ x := fun k ↦ by
    have h3 := hcY k D D' φ x (sm_whole x)
    simp only [Fn1.add, Fn1.neg, fv_smul, map_neg] at h3
    linear_combination h3
  rw [fv_sub_sum] at e2
  simp only [Fn1.add, Fn1.neg, hX0, Finset.sum_const_zero, zero_add] at e1 ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_add (f := _), map_sum]
  simp only [e3, Finset.sum_sub_distrib]
  linear_combination e2

end Rep

theorem apply_sub_sum {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {n : ℕ}
    (a a₁ : Fin n → M) (b b₁ : Fin n → N) (h : ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0) (x : M →ₗ[R] R)
    (y : N →ₗ[R] R) (hx : ∀ k, x (a₁ k) = 0) (c : M) (hc : x c = ∑ k, x (a k) * y (b k)) :
    x (c - ∑ k, y (b₁ k) • (a k - a₁ k)) = 0 := by
  have e := sum_split ((LinearMap.mul R R).compl₁₂ x y) a a₁ b b₁ h
  simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at e
  simp only [map_sub, hx, sub_zero, zero_mul, Finset.sum_const_zero, zero_add] at e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, hc, e]
  simp only [map_smul, map_sub, hx, sub_zero, smul_eq_mul, mul_comm, sub_self]

theorem mk_sub_sum {n : ℕ} {f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {c : primDR A} (hf : CatCoh.H1.mk _ f = c.1)
    {a' : Fin n → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {a : Fin n → primDR A} (ha : ∀ k, CatCoh.H1.mk _ (a' k) = (a k).1)
    (t : Fin n → R) : CatCoh.H1.mk _ (f - ∑ k, t k • a' k) = (c - ∑ k, t k • a k : primDR A).1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, hf, Submodule.coe_sub, Submodule.coe_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, ha k, Submodule.coe_smul]

end GlobalTheory.PtExt.ChernRep


open GlobalTheory.PtExt.ChernRep in
theorem GlobalTheory.PtExt.exists_chernRep_contr_of_orth : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∃ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) ∧ (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) ∧ ∀ κ : Fn1 A, IsContr w.1 v κ → Cohom (whole A) κ (fv f).neg := by
  intro hHDR R _ A B _ _ g hA hB hgA hgB P hP pf hpf horth h' v hv c hc f hf
  obtain ⟨hFree, hHodge, -⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange hHDR
  obtain ⟨-, hprA, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hFree hA hgA
  obtain ⟨-, hprB, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hFree hB hgB
  obtain ⟨-, hCA, -⟩ := hHodge R A g hA hgA
  obtain ⟨-, hCB, -⟩ := hHodge R B g hB hgB
  obtain ⟨n, a, b, hch, hab⟩ := hpf
  have L := GlobalTheory.tensor_mem_of_dualAnnihilator R (primDR A) (primDR B) (PrimitiveSubmodule A) (PrimitiveSubmodule B) hCA hCB
  obtain ⟨a₁, b₁, ha₁, hb₁, hsum⟩ := L.2 n a b fun x hx y hy ↦ (hab x y).symm.trans (horth x hx y hy)
  have eα : ∀ k, ∃ α : Form (A.hom ≫ 𝟙 _), Form.cl _ α = (a₁ k).1 := fun k ↦ by
    have h := ha₁ k
    rw [PrimitiveSubmodule, Submodule.mem_comap, hodgeFiltration_eq_range] at h
    exact h
  choose α hα using eα
  have eβ : ∀ k, ∃ β : Form (B.hom ≫ 𝟙 _), Form.cl _ β = (b₁ k).1 := fun k ↦ by
    have h := hb₁ k
    rw [PrimitiveSubmodule, Submodule.mem_comap, hodgeFiltration_eq_range] at h
    exact h
  choose β hβ using eβ
  choose b' hb' using fun k ↦ CatCoh.H1.mk_surjective (O (dp0 R) (B.hom ≫ 𝟙 _)) (b k).1
  choose a' ha' using fun k ↦ CatCoh.H1.mk_surjective (O (dp0 R) (A.hom ≫ 𝟙 _)) (a k - a₁ k).1
  have m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  refine ⟨rep m₁ m₂ α β a' b', ?_, rep_triv m₁ m₂ α β a' b', rep_contr m₁ m₂ α β a' b' hv.1 f ?_⟩
  · have hz : CatCoh.H2.mk _ (rep m₁ m₂ α β a' b') = ∑ k, cupPrim A B (a k) (b k) :=
      ((mk_rep m₁ m₂ α β a' b').trans (congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun k _ ↦ mk_cupPr_prim m₁ m₂ (hα k) (hb' k))
        (Finset.sum_congr rfl fun k _ ↦ mk_cupPr_prim m₁ m₂ (ha' k) (hβ k)))).trans
        (sum_split (cupPrim A B) a a₁ b b₁ hsum).symm
    exact hz ▸ hch
  · have ht : (fun k ↦ tanVal v (β k)) = fun k ↦ h' (b₁ k) := funext fun k ↦ by
      have hm : Form.cl _ (β k) ∈ primDR B := (hβ k).symm ▸ (b₁ k).2
      exact (hv.2 (β k) hm).symm.trans (congrArg h' (Subtype.ext (hβ k)))
    have hd : c - ∑ k, h' (b₁ k) • (a k - a₁ k) ∈ PrimitiveSubmodule A := L.1 _ fun x hx ↦
      apply_sub_sum a a₁ b b₁ hsum x h' (fun k ↦ (Submodule.mem_dualAnnihilator _).1 hx _ (ha₁ k)) c
        ((hc x hx).symm.trans (hab x h'))
    rw [mk_sub_sum hf ha' fun k ↦ tanVal v (β k)]
    simp only [fun k ↦ congrFun ht k]
    exact hd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernRepresentativeContractionOfOrthogonalStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chernRepresentative_contraction_of_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∃ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) ∧ (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) ∧ ∀ κ : Fn1 A, IsContr w.1 v κ → Cohom (whole A) κ (fv f).neg := by
  first | exact @GlobalTheory.PtExt.exists_chernRep_contr_of_orth | exact GlobalTheory.PtExt.exists_chernRep_contr_of_orth | (intros; apply GlobalTheory.PtExt.exists_chernRep_contr_of_orth <;> assumption)
end
