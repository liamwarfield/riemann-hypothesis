module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

section Defs
variable {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left)

abbrev bc : Over (Sp V) := (Over.pullback (φ ≫ T.hom)).obj A

abbrev bcR : Over (Sp R) := Over.mk ((bc A φ).hom ≫ φ ≫ T.hom)

def pa : bcR A φ ⟶ A := Over.homMk (pullback.fst A.hom (φ ≫ T.hom)) (by
  show pullback.fst A.hom (φ ≫ T.hom) ≫ A.hom = pullback.snd A.hom (φ ≫ T.hom) ≫ φ ≫ T.hom
  exact pullback.condition)

def pt : bcR A φ ⟶ T := Over.homMk ((bc A φ).hom ≫ φ) (Category.assoc _ _ _)

def twist (N : LB (A ⊗ T).left) : LB (bcR A φ).left := N.pull (lift (pa A φ) (pt A φ)).left

abbrev ker {H : Over (Sp R)} (h : H ⟶ A ⊗ T) : Over (Sp V) := Over.mk (pullback.snd (h ≫ snd A T).left φ)

def kerι {H : Over (Sp R)} (h : H ⟶ A ⊗ T) : ker A φ h ⟶ bc A φ :=
  Over.homMk (pullback.lift (pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left) (pullback.snd _ _) (by
    have w : (h ≫ fst A T).left ≫ A.hom = (h ≫ snd A T).left ≫ T.hom := by rw [Over.w, Over.w]
    rw [Category.assoc, w, pullback.condition_assoc])) (pullback.lift_snd _ _ _)

variable {A}

abbrev up (Y : Over (Sp V)) : Over (Sp R) := Over.mk (Y.hom ≫ φ ≫ T.hom)

def upa {Y : Over (Sp V)} (x : Y ⟶ bc A φ) : up φ Y ⟶ A :=
  Over.homMk (x.left ≫ pullback.fst A.hom (φ ≫ T.hom)) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ φ ≫ T.hom) (Over.w x))

def upt (Y : Over (Sp V)) : up φ Y ⟶ T := Over.homMk (Y.hom ≫ φ) (Category.assoc _ _ _)

end Defs
end GlobalTheory.TwistFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoFamilyIffLocallyTrivialTranslati
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoFamilyIffLocallyTrivialTranslati
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistFlat

theorem pull_cls_translDiff_div {S : Scheme.{0}} {A T Y Z : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hL : L.IsLB) (hP : (abelian₂ A L).IsLB) {N : LB (A ⊗ T).left} (hN : N.IsLB) (a : Y ⟶ A) (t : Y ⟶ T)
    (hD : (LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).IsLB) (s : Z ⟶ Y) (u : Z ⟶ A) :
    CechPic.pull (lift s u).left (cls _ hD) = evc hP u (s ≫ a) - evc hN u (s ≫ t) +
      CechPic.pull s.left (CechPic.pull a.left (cls L hL) - CechPic.pull (1 : Y ⟶ A).left (cls L hL)) := by
  have hT : (translDiff A L a).IsLB := LB.isLB_linComb hL _ _
  rw [cls_div hT (pull_isLB hN _) hD, map_sub, GlobalTheory.AbDual.pull_translDiff hL a hT, cls_ev hN, pull_evc, lift_snd,
    lift_fst_assoc, GlobalTheory.CubeDual.evc_lam hL, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left,
    MonObj.comp_one, lam, _root_.mul_comm u (s ≫ a)]
  abel_nf

theorem same_lam_iff_locally_triv : ∀ {S : Scheme.{0}} (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), Fam A N → ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∀ p : Y.left, ∃ U : Y.left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).pull ((fst Y A).left ⁻¹ᵁ U).ι) := by
  intro S A T _ hA L hL N hN Y a t
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hF : Fam A (abelian₂ A L) := ⟨hP, (GlobalTheory.CubeDual.isAdditive_lam GlobalTheory.CubeTop.cubeTheorem hA hL hP).1⟩
  have hT : (translDiff A L a).IsLB := LB.isLB_linComb hL _ _
  have hD : (LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).IsLB :=
    LB.isLB_div hT (pull_isLB hN.isLB _)
  constructor
  · intro h p
    obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
      (CechPic.pull a.left (cls L hL) - CechPic.pull (1 : Y ⟶ A).left (cls L hL)) p
    refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
    have e₁ := pull_cls_translDiff_div hL hP hN.isLB a t hD (fst Y A) (snd Y A)
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have e₂ := congrArg (CechPic.pull (lift (snd Y A) (fst Y A)).left) ((same_iff hP hN.isLB a t).1 h)
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e₂
    rw [cls_pull hD, e₁, e₂, sub_self, zero_add, ← pull_comp]
    exact pull_eq_zero_of_mem V (((fst Y A).left ⁻¹ᵁ V).ι ≫ (fst Y A).left) (fun z ↦ z.2) hc
  · intro h
    refine same_of_local S A A T hA _ N hF hN Y a t fun p ↦ ?_
    obtain ⟨U, hU, hU'⟩ := h p
    obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
      (CechPic.pull a.left (cls L hL) - CechPic.pull (1 : Y ⟶ A).left (cls L hL)) p
    let Z : Over S := Over.mk ((U ⊓ V).ι ≫ Y.hom)
    let z : Z ⟶ Y := Over.homMk (U ⊓ V).ι rfl
    refine ⟨Z, z, inferInstanceAs (IsOpenImmersion (U ⊓ V).ι), ⟨⟨p, hU, hV⟩, rfl⟩, ?_⟩
    rw [same_iff hP hN.isLB, ← sub_eq_zero]
    have hm : ∀ w, (snd A Z ≫ z).left w ∈ U ⊓ V := fun w ↦ ((snd A Z).left w).2
    have e₁ := pull_cls_translDiff_div hL hP hN.isLB a t hD (snd A Z ≫ z) (fst A Z)
    have z₀ : CechPic.pull ((fst Y A).left ⁻¹ᵁ U).ι (cls _ hD) = 0 := (cls_eq_zero_iff (pull_isLB hD _)).2 hU'
    have e : (lift (snd A Z ≫ z) (fst A Z)).left ≫ (fst Y A).left = (snd A Z ≫ z).left := by
      rw [← Over.comp_left, lift_fst]
    rw [pull_eq_zero_of_mem _ _ (fun w ↦ (congrArg (fun q ↦ q w ∈ U) e).mpr (hm w).1) z₀,
      pull_eq_zero_of_mem V _ (fun w ↦ (hm w).2) hc, add_zero, Category.assoc, Category.assoc] at e₁
    exact e₁.symm

end GlobalTheory.TwistFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoFamilyIffLocallyTrivialTranslatiStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_iso_family_iff_locally_trivial_translationDiff : ∀ {S : Scheme.{0}} (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), Fam A N → ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∀ p : Y.left, ∃ U : Y.left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).pull ((fst Y A).left ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.TwistFlat.same_lam_iff_locally_triv | exact GlobalTheory.TwistFlat.same_lam_iff_locally_triv | (intros; apply GlobalTheory.TwistFlat.same_lam_iff_locally_triv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyAtPointLambdaTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyAtPointLambdaTrivial
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V]
  (φ : Sp V ⟶ T.left)

theorem upa_mul {Y : Over (Sp V)} (x y : Y ⟶ bc A φ) : upa φ (x * y) = upa φ x * upa φ y := by
  have h := (isGrpPullback_pullback A (φ ≫ T.hom)).2 Y x y (upa φ x) (upa φ y) rfl rfl
  exact Over.OverMorphism.ext h.symm

theorem upa_one {Y : Over (Sp V)} : upa φ (1 : Y ⟶ bc A φ) = 1 := by
  have e := upa_mul φ (1 : Y ⟶ bc A φ) 1
  rw [_root_.mul_one] at e
  exact left_eq_mul.1 e

theorem pull_cls_twist {N : LB (A ⊗ T).left} (hN : N.IsLB) (h : (twist A φ N).IsLB) {Y : Over (Sp V)}
    (x : Y ⟶ bc A φ) : CechPic.pull x.left (cls _ h) = evc hN (upa φ x) (upt φ Y) := by
  let u : up φ Y ⟶ bcR A φ := Over.homMk x.left (by
    show x.left ≫ (bc A φ).hom ≫ φ ≫ T.hom = Y.hom ≫ φ ≫ T.hom
    rw [← Category.assoc, Over.w x])
  have ha : u ≫ pa A φ = upa φ x := Over.OverMorphism.ext rfl
  have ht : u ≫ pt A φ = upt φ Y := Over.OverMorphism.ext (by
    show x.left ≫ (bc A φ).hom ≫ φ = Y.hom ≫ φ
    rw [← Category.assoc, Over.w x])
  have e := pull_evc hN u (pa A φ) (pt A φ)
  rw [ha, ht] at e
  exact e


variable (A) in
theorem triv_lam_twist (N : LB (A ⊗ T).left) (hF : Fam A N) : Triv (abelian₂ (bc A φ) (twist A φ N)) := by
  have hO : (twist A φ N).IsLB := pull_isLB hF.isLB _
  have hP : (abelian₂ (bc A φ) (twist A φ N)).IsLB := LB.isLB_linComb hO _ _
  refine (cls_eq_zero_iff hP).1 ?_
  have e : cls _ hP = lam (G := bc A φ) (cls (X := (bc A φ).left) _ hO) (fst (bc A φ) (bc A φ)) (snd (bc A φ) (bc A φ)) := cls_cube_two (G := bc A φ) (L := twist A φ N) hO _ _ hP
  rw [e, lam, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO,
    pull_cls_twist φ hF.isLB hO, upa_mul, upa_one, (isAdditive_iff hF.isLB).1 hF.add, hF.add.evc_one hF.isLB]
  simp only [add_sub_cancel_left, sub_self, add_zero]

end GlobalTheory.TwistFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyAtPointLambdaTrivialStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleFamilyAtPoint_lambda_trivial : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) (N : LB (A ⊗ T).left), Fam A N → Triv (abelian₂ (GlobalTheory.TwistFlat.bc A φ) (GlobalTheory.TwistFlat.twist A φ N)) := by
  first | exact @GlobalTheory.TwistFlat.triv_lam_twist | exact GlobalTheory.TwistFlat.triv_lam_twist | (intros; apply GlobalTheory.TwistFlat.triv_lam_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionFibreOverPointToBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionFibreOverPointToBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem isClosedImmersion_kerι : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  intro R _ A T V _ φ H h hh
  have hP : IsPullback (fst A T).left (snd A T).left A.hom T.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom T.hom
  have w : pullback.fst A.hom (φ ≫ T.hom) ≫ A.hom = (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) ≫ T.hom := by
    rw [Category.assoc]; exact pullback.condition
  let g : pullback A.hom (φ ≫ T.hom) ⟶ (A ⊗ T).left :=
    hP.lift (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) w
  have hg1 : g ≫ (fst A T).left = pullback.fst A.hom (φ ≫ T.hom) := hP.lift_fst _ _ _
  have hg2 : g ≫ (snd A T).left = pullback.snd A.hom (φ ≫ T.hom) ≫ φ := hP.lift_snd _ _ _
  have ht : IsPullback g (pullback.snd A.hom (φ ≫ T.hom)) (snd A T).left φ := by
    refine IsPullback.of_right (h₁₂ := (fst A T).left) (h₂₂ := T.hom) ?_ hg2 hP
    rw [hg1]
    exact IsPullback.of_hasPullback A.hom (φ ≫ T.hom)
  have hs : IsPullback (pullback.fst (h ≫ snd A T).left φ)
      ((kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)) (h.left ≫ (snd A T).left) φ := by
    have e1 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom) = pullback.snd (h ≫ snd A T).left φ :=
      pullback.lift_snd _ _ _
    rw [e1, ← Over.comp_left]
    exact IsPullback.of_hasPullback _ _
  have hsq : pullback.fst (h ≫ snd A T).left φ ≫ h.left = (kerι A φ h).left ≫ g := by
    apply hP.hom_ext
    · rw [Category.assoc, Category.assoc, hg1]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Category.assoc, hg2, ← Over.comp_left, pullback.condition]
      exact congrArg (· ≫ φ) (pullback.lift_snd _ _ _).symm
  have hpb : IsPullback (pullback.fst (h ≫ snd A T).left φ) (kerι A φ h).left h.left g :=
    IsPullback.of_bot hs hsq ht
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb hh

end GlobalTheory.TwistFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionFibreOverPointToBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_fibreOverPointToBaseChange : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  first | exact @GlobalTheory.TwistFlat.isClosedImmersion_kerι | exact GlobalTheory.TwistFlat.isClosedImmersion_kerι | (intros; apply GlobalTheory.TwistFlat.isClosedImmersion_kerι <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsFibreOverPointIffFactorsProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsFibreOverPointIffFactorsProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem factor_ker_iff {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V]
    (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T) (Y : Over (Sp V)) (x : Y ⟶ bc A φ) :
    (∃ y : Y ⟶ ker A φ h, y ≫ kerι A φ h = x) ↔
      ∃ z : up φ Y ⟶ H, z ≫ h = lift (upa φ x) (upt φ Y) := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y.left ≫ pullback.snd (h ≫ snd A T).left φ = Y.hom := Over.w y
    have hT : (h ≫ snd A T).left ≫ T.hom = H.hom := Over.w _
    have hc : (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ≫ (h ≫ snd A T).left = Y.hom ≫ φ := by
      rw [← hy]
      exact (Category.assoc _ _ _).trans
        ((congrArg (y.left ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    refine ⟨Over.homMk (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ?_, ?_⟩
    · show (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ≫ H.hom = Y.hom ≫ φ ≫ T.hom
      rw [← hT, ← Category.assoc, hc, Category.assoc]
    · apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc]
        apply Over.OverMorphism.ext
        have e : (kerι A φ h).left ≫ pullback.fst A.hom (φ ≫ T.hom)
            = pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left := pullback.lift_fst _ _ _
        exact (Category.assoc _ _ _).trans
          ((congrArg (y.left ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)
      · rw [lift_snd, Category.assoc]
        apply Over.OverMorphism.ext
        exact hc
  · rintro ⟨z, hz⟩
    have h1 : z ≫ h ≫ fst A T = upa φ x := by rw [← Category.assoc, hz, lift_fst]
    have h2 : z ≫ h ≫ snd A T = upt φ Y := by rw [← Category.assoc, hz, lift_snd]
    have h1' : z.left ≫ (h ≫ fst A T).left = x.left ≫ pullback.fst A.hom (φ ≫ T.hom) :=
      congrArg (·.left) h1
    have h2' : z.left ≫ (h ≫ snd A T).left = Y.hom ≫ φ := congrArg (·.left) h2
    let l : Y.left ⟶ pullback (h ≫ snd A T).left φ := pullback.lift z.left Y.hom h2'
    have l1 : l ≫ pullback.fst _ _ = z.left := pullback.lift_fst _ _ _
    have l2 : l ≫ pullback.snd _ _ = Y.hom := pullback.lift_snd _ _ _
    refine ⟨Over.homMk l l2, ?_⟩
    apply Over.OverMorphism.ext
    have e1 : (kerι A φ h).left ≫ pullback.fst A.hom (φ ≫ T.hom)
        = pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left := pullback.lift_fst _ _ _
    have e2 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)
        = pullback.snd (h ≫ snd A T).left φ := pullback.lift_snd _ _ _
    have hx : x.left ≫ pullback.snd A.hom (φ ≫ T.hom) = Y.hom := Over.w x
    apply pullback.hom_ext (f := A.hom) (g := φ ≫ T.hom)
    · refine (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) e1).trans ?_)
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (h ≫ fst A T).left) l1).trans h1')
    · exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) e2).trans (l2.trans hx.symm))

end GlobalTheory.TwistFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsFibreOverPointIffFactorsProductStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factors_fibreOverPoint_iff_factors_product : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T) (Y : Over (Sp V)) (x : Y ⟶ GlobalTheory.TwistFlat.bc A φ), (∃ y : Y ⟶ GlobalTheory.TwistFlat.ker A φ h, y ≫ GlobalTheory.TwistFlat.kerι A φ h = x) ↔ ∃ z : GlobalTheory.TwistFlat.up φ Y ⟶ H, z ≫ h = lift (GlobalTheory.TwistFlat.upa φ x) (GlobalTheory.TwistFlat.upt φ Y) := by
  first | exact @GlobalTheory.TwistFlat.factor_ker_iff | exact GlobalTheory.TwistFlat.factor_ker_iff | (intros; apply GlobalTheory.TwistFlat.factor_ker_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDifferenceTrivialBaseChangeIffOverA
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDifferenceTrivialBaseChangeIffOverA
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistFlat

theorem pull_restrict_eq_zero_iff {X₁ X₂ Z : Scheme.{0}} (f₁ : X₁ ⟶ Z) (f₂ : X₂ ⟶ Z) (h : X₁ ⟶ X₂) (k : X₂ ⟶ X₁)
    (hk : k ≫ h = 𝟙 X₂) (hf : h ≫ f₂ = f₁) (hf' : k ≫ f₁ = f₂) (U : Z.Opens) (c : Pic X₂) :
    CechPic.pull (f₁ ⁻¹ᵁ U).ι (CechPic.pull h c) = 0 ↔ CechPic.pull (f₂ ⁻¹ᵁ U).ι c = 0 := by
  constructor
  · intro e
    have e' := pull_eq_zero_of_mem (f₁ ⁻¹ᵁ U) ((f₂ ⁻¹ᵁ U).ι ≫ k) (fun z ↦ by
      show f₁ (k ((f₂ ⁻¹ᵁ U).ι z)) ∈ U
      rw [← Scheme.Hom.comp_apply, hf']
      exact z.2) (c := CechPic.pull h c) e
    rwa [← pull_comp, Category.assoc, hk, Category.comp_id] at e'
  · intro e
    rw [← pull_comp]
    exact pull_eq_zero_of_mem (f₂ ⁻¹ᵁ U) ((f₁ ⁻¹ᵁ U).ι ≫ h) (fun z ↦ by
      show f₂ (h ((f₁ ⁻¹ᵁ U).ι z)) ∈ U
      rw [← Scheme.Hom.comp_apply, hf]
      exact z.2) e

section Iso
variable {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left)
  (Y : Over (Sp V))

def cmpHom : pullback Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ⟶ pullback (Y.hom ≫ φ ≫ T.hom) A.hom :=
  pullback.lift (pullback.fst Y.hom _) (pullback.snd Y.hom _ ≫ pullback.fst A.hom (φ ≫ T.hom)) (by
    rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc, pullback.condition])

def cmpInv : pullback (Y.hom ≫ φ ≫ T.hom) A.hom ⟶ pullback Y.hom (pullback.snd A.hom (φ ≫ T.hom)) :=
  pullback.lift (pullback.fst _ A.hom)
    (pullback.lift (pullback.snd _ A.hom) (pullback.fst _ A.hom ≫ Y.hom) (by
      rw [Category.assoc]; exact pullback.condition.symm)) (pullback.lift_snd _ _ _).symm

theorem cmpInv_hom : cmpInv A φ Y ≫ cmpHom A φ Y = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [cmpHom, cmpInv, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.id_comp]

theorem cmpHom_fst : cmpHom A φ Y ≫ pullback.fst _ A.hom = pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) :=
  pullback.lift_fst _ _ _

theorem cmpInv_fst : cmpInv A φ Y ≫ pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) = pullback.fst _ A.hom :=
  pullback.lift_fst _ _ _

theorem cmpHom_snd : cmpHom A φ Y ≫ pullback.snd (Y.hom ≫ φ ≫ T.hom) A.hom =
    pullback.snd Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ pullback.fst A.hom (φ ≫ T.hom) :=
  pullback.lift_snd _ _ _

end Iso

section Main
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V]
  (φ : Sp V ⟶ T.left)

def cmpOver (Y : Over (Sp V)) : Over.mk ((Y ⊗ bc A φ).hom ≫ φ ≫ T.hom) ⟶ up φ Y ⊗ A :=
  Over.homMk (cmpHom A φ Y) (by
    show cmpHom A φ Y ≫ (up φ Y ⊗ A).hom = (Y ⊗ bc A φ).hom ≫ φ ≫ T.hom
    rw [← Over.w (fst (up φ Y) A), ← Over.w (fst Y (bc A φ))]
    show cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ (Y.hom ≫ φ ≫ T.hom) =
      (pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ Y.hom) ≫ φ ≫ T.hom
    rw [← Category.assoc, cmpHom_fst, Category.assoc])

theorem mul_left_fst {Y : Over (Sp V)} (x : Y ⟶ bc A φ) :
    ((fst Y (bc A φ) ≫ x) * snd Y (bc A φ)).left ≫ pullback.fst A.hom (φ ≫ T.hom) =
      cmpHom A φ Y ≫ ((fst (up φ Y) A ≫ upa φ x) * snd (up φ Y) A).left := by
  have hG := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (φ ≫ T.hom)).2 (Y ⊗ bc A φ)
    (fst Y (bc A φ) ≫ x) (snd Y (bc A φ)) (cmpOver A φ Y ≫ fst (up φ Y) A ≫ upa φ x)
    (cmpOver A φ Y ≫ snd (up φ Y) A) (by
      show cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ x.left ≫ pullback.fst A.hom (φ ≫ T.hom) =
        (pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ x.left) ≫ pullback.fst A.hom (φ ≫ T.hom)
      rw [← Category.assoc, cmpHom_fst, Category.assoc]) (cmpHom_snd A φ Y)
  rw [← MonObj.comp_mul] at hG
  exact hG.symm

theorem snd_lift_pa_pt (Y : Over (Sp V)) :
    (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ)).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y)).left := by
  apply pullback.hom_ext
  · show (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ) ≫ fst A T).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y) ≫ fst A T).left
    rw [lift_fst, lift_fst]
    exact (cmpHom_snd A φ Y).symm
  · show (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ) ≫ snd A T).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y) ≫ snd A T).left
    rw [lift_snd, lift_snd]
    show pullback.snd Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ pullback.snd A.hom (φ ≫ T.hom) ≫ φ =
      cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ Y.hom ≫ φ
    rw [← Category.assoc (cmpHom A φ Y), cmpHom_fst, ← Category.assoc, ← pullback.condition, Category.assoc]

theorem triv_pull_iff {X : Scheme.{0}} {D : LB X} (hD : D.IsLB) (W : X.Opens) :
    Triv (D.pull W.ι) ↔ CechPic.pull W.ι (cls D hD) = 0 := by
  unfold Triv
  rw [← cls_eq_zero_iff (pull_isLB hD _), cls_pull hD]

theorem triv_twist_iff (L : LB A.left) (hL : L.IsLB) (N : LB (A ⊗ T).left) (hN : N.IsLB) (Y : Over (Sp V))
    (x : Y ⟶ bc A φ) (U : Y.left.Opens) :
    Triv ((LB.div (translDiff (bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x)
        ((twist A φ N).pull (snd Y (bc A φ)).left)).pull ((fst Y (bc A φ)).left ⁻¹ᵁ U).ι) ↔
      Triv ((LB.div (translDiff A L (upa φ x)) (ev N (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y))).pull
        ((fst (up φ Y) A).left ⁻¹ᵁ U).ι) := by
  have hL' : (L.pull (pullback.fst A.hom (φ ≫ T.hom))).IsLB := pull_isLB hL _
  have h₁ : (translDiff (bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x).IsLB := LB.isLB_linComb hL' _ _
  have hO : (twist A φ N).IsLB := pull_isLB hN _
  have h₂ : ((twist A φ N).pull (snd Y (bc A φ)).left).IsLB := pull_isLB hO _
  have h₃ : (translDiff A L (upa φ x)).IsLB := LB.isLB_linComb hL _ _
  have h₄ : (ev N (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y)).IsLB := pull_isLB hN _
  have hc : cls _ (LB.isLB_div h₁ h₂) = CechPic.pull (cmpHom A φ Y) (cls _ (LB.isLB_div h₃ h₄)) := by
    rw [cls_div h₁ h₂, cls_div h₃ h₄, map_sub]
    have e₁ := pull_translDiff hL' x h₁ (fst Y (bc A φ)) (snd Y (bc A φ))
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have e₂ := pull_translDiff hL (upa φ x) h₃ (fst (up φ Y) A) (snd (up φ Y) A)
    rw [lift_fst_snd, Over.id_left, pull_id] at e₂
    rw [e₁, e₂, map_sub, cls_pull hL, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, mul_left_fst]
    have e₅ : (snd Y (bc A φ)).left ≫ pullback.fst A.hom (φ ≫ T.hom) = cmpHom A φ Y ≫ (snd (up φ Y) A).left :=
      (cmpHom_snd A φ Y).symm
    rw [e₅, cls_pull hO _ h₂,
      show cls (twist A φ N) hO = CechPic.pull (lift (pa A φ) (pt A φ)).left (cls N hN) from cls_pull hN _ hO,
      cls_pull hN, ← pull_comp, ← pull_comp, snd_lift_pa_pt]
  rw [triv_pull_iff (LB.isLB_div h₁ h₂), triv_pull_iff (LB.isLB_div h₃ h₄), hc]
  exact pull_restrict_eq_zero_iff _ _ (cmpHom A φ Y) (cmpInv A φ Y) (cmpInv_hom A φ Y) (cmpHom_fst A φ Y)
    (cmpInv_fst A φ Y) U _

end Main

end GlobalTheory.TwistFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDifferenceTrivialBaseChangeIffOverAStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), N.IsLB → ∀ (Y : Over (Sp V)) (x : Y ⟶ GlobalTheory.TwistFlat.bc A φ) (U : Y.left.Opens), Triv ((LB.div (translDiff (GlobalTheory.TwistFlat.bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x) ((GlobalTheory.TwistFlat.twist A φ N).pull (snd Y (GlobalTheory.TwistFlat.bc A φ)).left)).pull ((fst Y (GlobalTheory.TwistFlat.bc A φ)).left ⁻¹ᵁ U).ι) ↔ Triv ((LB.div (translDiff A L (GlobalTheory.TwistFlat.upa φ x)) (ev N (snd (GlobalTheory.TwistFlat.up φ Y) A) (fst (GlobalTheory.TwistFlat.up φ Y) A ≫ GlobalTheory.TwistFlat.upt φ Y))).pull ((fst (GlobalTheory.TwistFlat.up φ Y) A).left ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.TwistFlat.triv_twist_iff | exact GlobalTheory.TwistFlat.triv_twist_iff | (intros; apply GlobalTheory.TwistFlat.triv_twist_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFiniteTwistedKernelOverAffineParameter
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat
open GlobalTheory.StabFlatLocal GlobalTheory.StabFlat GlobalTheory.UU

theorem flat_of_isFinite_twist : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB →
    (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ O : LB B.left, O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) →
    ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left →
    (∀ (T : Over (Sp V)) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  intro hG V _ _ _ B _ _ hB hp L hL hΘ O hO hu H j hj hH hf
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V B hB
  rw [← Over.w j]
  refine GlobalTheory.T.flat_closedSubscheme_finite_over_localRing V B.left H.left B.hom j.left hj (by rw [Over.w j]; exact hf) fun h σ hσ hn => ?_
  have cl : ∀ (z : H.left) (p : Spec (B.left.presheaf.stalk (j.left h))),
      (IsLocalRing.maximalIdeal V).map σ ≤ p.asIdeal →
      j.left z = B.left.fromSpecStalk (j.left h) p → IsClosed ({j.left z} : Set B.left) := by
    intro z p hp e
    have hz : H.hom z = IsLocalRing.closedPoint V := by
      rw [← Over.w j, Scheme.Hom.comp_apply, e, ← Scheme.Hom.comp_apply, hσ]
      refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top ?_))
      exact Ideal.map_le_iff_le_comap.1 hp
    have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom z hz)
    rwa [Set.image_singleton] at this
  have hm : (IsLocalRing.maximalIdeal V).map σ ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit σ v hv
  obtain ⟨h₀, h₁, h₂, h₃⟩ := GlobalTheory.T.stalk_regular_flat_of_smooth V B.left B.hom g hg (j.left h)
    (cl h (IsLocalRing.closedPoint _) hm Scheme.fromSpecStalk_closedPoint.symm) σ hσ hn
  refine @exists_ideal hG V _ _ _ B _ _ hB hp g hg L O hL hO hΘ hu H j hH
    (B.left.presheaf.stalk (j.left h)) _ h₀ _
    (B.left.fromSpecStalk (j.left h)) σ hn h₁ h₂ h₃ (H.left.residueField h) _
    (j.left.stalkMap h ≫ H.left.residue h).hom
    (RingHom.isLocalHom_comp (IsLocalRing.residue (H.left.presheaf.stalk h)) (j.left.stalkMap h).hom) ⟨H.left.fromSpecResidueField h, ?_⟩ ?_
  · rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    rfl
  · rintro K _ φ hφ ⟨y, hy⟩
    let p := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)
    have hk : p.asIdeal = RingHom.ker φ := by
      show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K)) = B.left.fromSpecStalk (j.left h) p :=
      congrArg (fun q => q (IsLocalRing.closedPoint K)) hy
    have hc := cl _ p (hφ.trans hk.ge) e
    have hs : B.left.fromSpecStalk (j.left h) p ⤳ j.left h := by
      have : B.left.fromSpecStalk (j.left h) p ∈ Set.range (B.left.fromSpecStalk (j.left h)) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : j.left h = B.left.fromSpecStalk (j.left h) p := (hs.mem_closed hc e.symm).trans e
    have hp' : p = IsLocalRing.closedPoint _ := (B.left.fromSpecStalk (j.left h)).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, hp']
    rfl

end GlobalTheory.TwistFlat

namespace GlobalTheory.TwistFlat

theorem flat_local : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left,
    L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N →
    ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left →
    (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) →
    ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (φ : Sp V ⟶ T.left),
    IsFinite (pullback.snd (h ≫ snd A T).left φ) → Flat (pullback.snd (h ≫ snd A T).left φ) := by
  intro R _ A _ hA L hL ha T N hN H h hh hH V _ _ _ φ hfin
  have hB : IsAbelianScheme (bc A φ) := GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  have : IsCommMonObj (bc A φ) := hB.comm
  have hP : IsProjBy (bc A φ).hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A L hA hL ha V (φ ≫ T.hom)
      _ (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom)) (IsPullback.of_hasPullback _ _)).1
  have hL' : (L.pull (pullback.fst A.hom (φ ≫ T.hom))).IsLB := LB.isLB_pull hL _
  have hO : (twist A φ N).IsLB := pull_isLB hN.isLB _
  refine flat_of_isFinite_twist GlobalTheory.T.abelianScheme_laws_unconditional.1.globalFns V (bc A φ) hB hP _ hL'
    (GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy GlobalTheory.T.abelianScheme_laws_unconditional.1 _ _ hB hP _ hL') (twist A φ N) hO
    (GlobalTheory.T.lineBundleFamilyAtPoint_lambda_trivial A φ N hN) (ker A φ h) (kerι A φ h) (GlobalTheory.T.isClosedImmersion_fibreOverPointToBaseChange A φ h hh) (fun Y x => ?_) hfin
  rw [GlobalTheory.T.factors_fibreOverPoint_iff_factors_product A φ h Y x, ← hH, GlobalTheory.T.mumfordBundle_iso_family_iff_locally_trivial_translationDiff A T hA L hL N hN]
  exact forall_congr' fun p => exists_congr fun U => and_congr_right' (GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A A φ L hL N hN.isLB Y x U)

end GlobalTheory.TwistFlat

namespace GlobalTheory.TwistFlat

theorem isNoetherianRing_top (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsAffine X]
    (f : X ⟶ Sp R) (hf : LocallyOfFiniteType f) : IsNoetherianRing Γ(X, ⊤) := by
  have h1 : (f.appTop).hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 hf
  have : IsNoetherianRing Γ(Sp R, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI := (f.appTop).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp R, ⊤) Γ(X, ⊤) := h1
  exact Algebra.FiniteType.isNoetherianRing Γ(Sp R, ⊤) Γ(X, ⊤)

theorem flat_twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left → Flat (h ≫ snd A T).left := by
  intro R _ _ A _ hA L hL ha T _ hT N hN H h hh hH hfin
  have : IsNoetherianRing Γ(T.left, ⊤) := isNoetherianRing_top R T.left T.hom hT
  let e := T.left.isoSpec
  let f := (h ≫ snd A T).left
  haveI : IsFinite f := hfin
  let H' : Over (Sp Γ(T.left, ⊤)) := Over.mk (f ≫ e.hom)
  have hfin' : IsFinite H'.hom := by
    show IsFinite (f ≫ e.hom)
    infer_instance
  have hflat : Flat (f ≫ e.hom) := by
    refine GlobalTheory.flat_of_isFinite_of_flat_localization_maximal Γ(T.left, ⊤) H' hfin' fun m _ => ?_
    let φ : Sp (Localization.AtPrime m) ⟶ T.left := spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m)) ≫ e.inv
    have hf : IsFinite (pullback.snd f φ) := MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback f φ) hfin
    haveI := flat_local R A hA L hL ha T N hN H h hh hH (Localization.AtPrime m) φ hf
    have sq : IsPullback (pullback.fst f φ) (pullback.snd f φ) (f ≫ e.hom)
        (spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m))) :=
      (IsPullback.of_hasPullback f φ).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
        (by simp) (by simp [φ])
    show Flat (pullback.snd (f ≫ e.hom) _)
    rw [← sq.isoPullback_inv_snd]
    infer_instance
  have hfe : f = (f ≫ e.hom) ≫ e.inv := by simp
  show Flat f
  rw [hfe]
  infer_instance

end GlobalTheory.TwistFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFiniteTwistedKernelOverAffineParameterStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_finiteTwistedKernel_over_affineParameter : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left → Flat (h ≫ snd A T).left := by
  first | exact @GlobalTheory.TwistFlat.flat_twisted_kernel | exact GlobalTheory.TwistFlat.flat_twisted_kernel | (intros; apply GlobalTheory.TwistFlat.flat_twisted_kernel <;> assumption)
end
