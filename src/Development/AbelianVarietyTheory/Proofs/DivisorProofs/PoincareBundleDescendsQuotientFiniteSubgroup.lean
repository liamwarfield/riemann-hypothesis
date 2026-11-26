module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentFiniteFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorSquare
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PoincareDescent

theorem torsor_square {C : Type*} [Category C] [CartesianMonoidalCategory C] {A A' N : C} [GrpObj A] [GrpObj A']
    [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (h : IsPullback i (toUnit N) q η[A']) :
    IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q := by
  have hiq : i ≫ q = 1 := by
    rw [h.w]; rfl
  have hdiff : ∀ {W : C} (x y : W ⟶ A), x ≫ q = y ≫ q → (x⁻¹ * y) ≫ q = toUnit W ≫ η[A'] := by
    intro W x y e
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, inv_mul_cancel]; rfl
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ lift s.fst (h.lift (s.fst⁻¹ * s.snd) (toUnit _)
      (hdiff _ _ s.condition))) (fun s ↦ lift_fst _ _) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.mul_one]
  · rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, h.lift_fst, mul_inv_cancel_left]
  · have e₁ : m ≫ fst A N = s.fst := h₁
    refine CartesianMonoidalCategory.hom_ext _ _ (by rw [e₁, lift_fst]) ?_
    rw [lift_snd]
    refine h.hom_ext ?_ (toUnit_unique _ _)
    rw [h.lift_fst, ← h₂, MonObj.comp_mul, e₁, Category.assoc, inv_mul_cancel_left]

end GlobalTheory.PoincareDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleDescendsAlongIsogenyTorsor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumAdditiveLineBundleIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalUnitTripleFibreProductInvariantSetGroupCoo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalUnitTripleFibreProductInvariantSetGroupCoo
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm.RigidW

theorem triple_ext {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g h : Z ⟶ Triple f)
    (h1 : g ≫ pullback.fst _ _ ≫ pullback.fst f f = h ≫ pullback.fst _ _ ≫ pullback.fst f f)
    (h2 : g ≫ pullback.fst _ _ ≫ pullback.snd f f = h ≫ pullback.fst _ _ ≫ pullback.snd f f)
    (h3 : g ≫ pullback.snd _ _ ≫ pullback.snd f f = h ≫ pullback.snd _ _ ≫ pullback.snd f f) : g = h := by
  have c := pullback.condition (f := pullback.snd f f) (g := pullback.fst f f)
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h1
    · simpa only [Category.assoc] using h2
  · apply pullback.hom_ext
    · simp only [Category.assoc, ← c]
      simpa only [Category.assoc] using h2
    · simpa only [Category.assoc] using h3

theorem appTop_comp {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom x = g.appTop.hom (h.appTop.hom x) := by
  rw [Scheme.Hom.comp_appTop]; rfl

section
variable {K : Type} [Field K] {A A' B : Over (Sp K)} [GrpObj B] (q : A ⟶ A')

theorem snd_hom : pullback.snd (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom := by
  rw [← Over.w (q ▷ B), pullback.condition_assoc]


variable (B) in
def W0 : Over (Sp K) :=
  Over.mk (pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom : Triple (q ▷ B).left ⟶ Sp K)

def p1 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.fst _ _ ≫ pullback.fst _ _) (by simp [W0])

def p2 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.fst _ _ ≫ pullback.snd _ _) (by
  simp only [W0, Over.mk_hom]; rw [Category.assoc, snd_hom])

def p3 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.snd _ _ ≫ pullback.snd _ _) (by
  simp only [W0, Over.mk_hom]; rw [Category.assoc, snd_hom, ← pullback.condition_assoc, snd_hom])

theorem rigidityTripleFibreProductFirstCoord_left : (p1 q).left = pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left := rfl
theorem rigidityTripleFibreProductSecondCoord_left : (p2 q).left = pullback.fst _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left := rfl
theorem rigidityTripleFibreProductThirdCoord_left : (p3 q).left = pullback.snd _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left := rfl

theorem p12 : p1 q ≫ q ▷ B = p2 q ≫ q ▷ B := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, rigidityTripleFibreProductFirstCoord_left, rigidityTripleFibreProductSecondCoord_left]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

theorem p23 : p2 q ≫ q ▷ B = p3 q ≫ q ▷ B := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, rigidityTripleFibreProductThirdCoord_left, rigidityTripleFibreProductSecondCoord_left]
  exact (congrArg (· ≫ _) pullback.condition).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm))

end
end GlobalTheory.DescNorm.RigidW

namespace GlobalTheory.DescNorm.RigidW
section
variable {K : Type} [Field K] {A A' B : Over (Sp K)} [GrpObj B] (q : A ⟶ A')

def beta : W0 B q ⟶ B := p1 q ≫ snd A B

theorem rigidityTripleSecondCoord_snd_eq_groupCoord : p2 q ≫ snd A B = beta q := by
  rw [beta, ← whiskerRight_snd q B, ← Category.assoc, ← Category.assoc, p12]

theorem rigidityTripleThirdCoord_snd_eq_groupCoord : p3 q ≫ snd A B = beta q := by
  rw [← rigidityTripleSecondCoord_snd_eq_groupCoord, ← whiskerRight_snd q B, ← Category.assoc, ← Category.assoc, p23]

def E (u : W0 B q ⟶ A ⊗ B) : B ⊗ W0 B q ⟶ A ⊗ B := lift (snd B (W0 B q) ≫ u ≫ fst A B) (fst B (W0 B q))

theorem E_eq {u v : W0 B q ⟶ A ⊗ B} (h : u ≫ q ▷ B = v ≫ q ▷ B) : E q u ≫ q ▷ B = E q v ≫ q ▷ B := by
  have h' : u ≫ fst A B ≫ q = v ≫ fst A B ≫ q := by
    have := congrArg (· ≫ fst A' B) h
    simpa using this
  apply CartesianMonoidalCategory.hom_ext
  · simp [E, h']
  · simp [E]

theorem E_left_eq {u v : W0 B q ⟶ A ⊗ B} (h : u ≫ q ▷ B = v ≫ q ▷ B) :
    (E q u).left ≫ (q ▷ B).left = (E q v).left ≫ (q ▷ B).left := by
  rw [← Over.comp_left, ← Over.comp_left, E_eq q h]

theorem lift_E (x : W0 B q ⟶ B) (u : W0 B q ⟶ A ⊗ B) : lift x (𝟙 _) ≫ E q u = lift (u ≫ fst A B) x := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [E]

def eL : (B ⊗ W0 B q).left ⟶ Triple (q ▷ B).left :=
  pullback.lift (pullback.lift (E q (p1 q)).left (E q (p2 q)).left (E_left_eq q (p12 q)))
    (pullback.lift (E q (p2 q)).left (E q (p3 q)).left (E_left_eq q (p23 q)))
    ((pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm)

theorem eL_1 : eL q ≫ pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left = (E q (p1 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
theorem eL_2 : eL q ≫ pullback.fst _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left = (E q (p2 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
theorem eL_3 : eL q ≫ pullback.snd _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left = (E q (p3 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_snd, pullback.lift_snd]

theorem sec_beta : (lift (beta q) (𝟙 (W0 B q))).left ≫ eL q = 𝟙 _ := by
  apply triple_ext
  · rw [Category.assoc, eL_1, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p1 q ≫ fst A B) (beta q) = p1 q)).trans
      ((rigidityTripleFibreProductFirstCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [beta]
  · rw [Category.assoc, eL_2, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p2 q ≫ fst A B) (beta q) = p2 q)).trans
      ((rigidityTripleFibreProductSecondCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [rigidityTripleSecondCoord_snd_eq_groupCoord]
  · rw [Category.assoc, eL_3, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p3 q ≫ fst A B) (beta q) = p3 q)).trans
      ((rigidityTripleFibreProductThirdCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [rigidityTripleThirdCoord_snd_eq_groupCoord]

theorem lift_one (u : W0 B q ⟶ A ⊗ B) : lift (u ≫ fst A B) (1 : W0 B q ⟶ B) = u ≫ zb A B := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [zb]
  · simp [zb, MonObj.comp_one]

theorem sec_one : (lift (1 : W0 B q ⟶ B) (𝟙 (W0 B q))).left ≫ eL q = rhoW q := by
  apply triple_ext
  · rw [Category.assoc, eL_1, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductFirstCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_fst q).symm)).trans (rhoW_fst_assoc q _).symm
  · rw [Category.assoc, eL_2, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductSecondCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_snd q).symm)).trans (rhoW_fst_assoc q _).symm
  · rw [Category.assoc, eL_3, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductThirdCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_snd q).symm)).trans (rhoW_snd_assoc q _).symm

theorem rhoW_appTop (hB : IsAbelianScheme B) (D : Γ(Triple (q ▷ B).left, ⊤)) : (rhoW q).appTop.hom D = D := by
  have hs : Function.Surjective ((snd B (W0 B q)).left.appTop).hom :=
    surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns _ (Out.TLinPf.isAb_pullback (W0 B q).hom B hB) ⊤
  obtain ⟨F, hF⟩ := hs ((eL q).appTop.hom D)
  have hsnd : ∀ x : W0 B q ⟶ B, (lift x (𝟙 (W0 B q))).left ≫ (snd B (W0 B q)).left = 𝟙 _ := fun x => by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have key : ∀ x : W0 B q ⟶ B, ((lift x (𝟙 (W0 B q))).left ≫ eL q).appTop.hom D = F := by
    intro x
    calc ((lift x (𝟙 (W0 B q))).left ≫ eL q).appTop.hom D
        = (lift x (𝟙 (W0 B q))).left.appTop.hom ((eL q).appTop.hom D) := appTop_comp _ _ _
      _ = (lift x (𝟙 (W0 B q))).left.appTop.hom ((snd B (W0 B q)).left.appTop.hom F) := by rw [hF]
      _ = ((lift x (𝟙 (W0 B q))).left ≫ (snd B (W0 B q)).left).appTop.hom F := (appTop_comp _ _ _).symm
      _ = F := by rw [hsnd x, Scheme.Hom.id_appTop]; rfl
  have h1 : D = F := by
    have h := key (beta q)
    rw [sec_beta] at h
    exact h
  have h0 := key 1
  rw [sec_one] at h0
  exact h0.trans h1.symm

end

theorem gm_rhoW_eq_gm_id_of_abelian : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj B] (q : A ⟶ A'), IsAbelianScheme B →
    ∀ (D : Γ(Triple (q ▷ B).left, ⊤)ˣ) (w : Triple (q ▷ B).left), gm (rhoW q) w ⊤ D = gm (𝟙 _) w ⊤ D := by
  intro K _ A A' B _ q hB D w
  have := gm_comp_top (𝟙 _) (rhoW q) w D D (rhoW_appTop q hB D.val)
  rwa [Category.id_comp] at this

end GlobalTheory.DescNorm.RigidW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalUnitTripleFibreProductInvariantSetGroupCooStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalUnit_tripleFibreProduct_invariant_setGroupCoordZero : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj B] (q : A ⟶ A'), IsAbelianScheme B → ∀ (D : Γ(Triple (q ▷ B).left, ⊤)ˣ) (w : Triple (q ▷ B).left), gm (rhoW q) w ⊤ D = gm (𝟙 _) w ⊤ D := by
  first | exact @GlobalTheory.DescNorm.RigidW.gm_rhoW_eq_gm_id_of_abelian | exact GlobalTheory.DescNorm.RigidW.gm_rhoW_eq_gm_id_of_abelian | (intros; apply GlobalTheory.DescNorm.RigidW.gm_rhoW_eq_gm_id_of_abelian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackFstSndOfAdditiveTrivialKern
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackFstSndOfAdditiveTrivialKern
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescIsoExists

theorem lbIso_pull_fst_snd : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → P.IsLB → IsAdditive P → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → LBIso (P.pull (pullback.fst (q ▷ B).left (q ▷ B).left)) (P.pull (pullback.snd (q ▷ B).left (q ▷ B).left)) := by
  intro K _ _ A A' B _ _ _ q P _ _ _ hq hP hadd hker
  let f := (q ▷ B).left
  have hw : f ≫ (A' ⊗ B).hom = (A ⊗ B).hom := Over.w (q ▷ B)
  let Z : Over (Sp K) := Over.mk (pullback.fst f f ≫ (A ⊗ B).hom)
  have hsnd : pullback.snd f f ≫ (A ⊗ B).hom = pullback.fst f f ≫ (A ⊗ B).hom := by
    rw [← hw, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hB : (q ▷ B) ≫ snd A' B = snd A B := whiskerRight_snd q B
  have hA : (q ▷ B) ≫ fst A' B = fst A B ≫ q := whiskerRight_fst q B
  have hBl : f ≫ (snd A' B).left = (snd A B).left := by rw [← Over.comp_left, hB]
  have hAl : f ≫ (fst A' B).left = (fst A B).left ≫ q.left := by
    rw [← Over.comp_left, hA, Over.comp_left]
  let a : Z ⟶ A := Over.homMk (pullback.fst f f ≫ (fst A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w])
  let a' : Z ⟶ A := Over.homMk (pullback.snd f f ≫ (fst A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w]; exact hsnd)
  let b : Z ⟶ B := Over.homMk (pullback.fst f f ≫ (snd A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w])
  let u : Z ⟶ A ⊗ B := Over.homMk (pullback.fst f f) rfl
  let u' : Z ⟶ A ⊗ B := Over.homMk (pullback.snd f f) hsnd
  have hu : lift a b = u := by
    ext1
    · ext; simp [a, u]
    · ext; simp [b, u]
  have hu' : lift a' b = u' := by
    ext1
    · ext; simp [a', u']
    · ext
      simp only [b, u', lift_snd, Over.homMk_left, Over.comp_left]
      rw [← hBl, ← Category.assoc, pullback.condition, Category.assoc]
  have hq' : a ≫ q = a' ≫ q := by
    ext
    simp only [a, a', Over.comp_left, Over.homMk_left, Category.assoc]
    rw [← hAl, ← Category.assoc, pullback.condition, Category.assoc]

  have e1 : (pullback.fst f f : pullback f f ⟶ _) = (lift a b).left := by rw [hu]; rfl
  have e2 : (pullback.snd f f : pullback f f ⟶ _) = (lift a' b).left := by rw [hu']; rfl
  refine (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).1 ?_
  have c1 : cls _ (pull_isLB hP (pullback.fst f f)) = evc hP a b := by
    rw [cls_pull hP]; simp only [evc]; rw [e1]
  have c2 : cls _ (pull_isLB hP (pullback.snd f f)) = evc hP a' b := by
    rw [cls_pull hP]; simp only [evc]; rw [e2]
  rw [c1, c2]
  let k : Z ⟶ A := a' * a⁻¹
  have hinv : a⁻¹ ≫ q = (a ≫ q)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  have hk : k ≫ q = 1 := by
    simp only [k]
    rw [MonObj.mul_comp, hinv, ← hq', mul_inv_cancel]
  have h0 : evc hP k b = 0 := by
    have e := congrArg (CechPic.pull (lift (𝟙 Z) b).left) ((triv_ev_iff hP _ _).1 (hker Z k hk))
    rwa [pull_evc, map_zero, lift_fst_assoc, Category.id_comp, lift_snd] at e
  have ha : a' = k * a := by simp only [k, inv_mul_cancel_right]
  rw [ha, (isAdditive_iff hP).1 hadd, h0, zero_add]

end GlobalTheory.DescIsoExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackFstSndOfAdditiveTrivialKernStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_iso_pullback_fst_snd_of_additive_trivial_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → P.IsLB → IsAdditive P → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → LBIso (P.pull (pullback.fst (q ▷ B).left (q ▷ B).left)) (P.pull (pullback.snd (q ▷ B).left (q ▷ B).left)) := by
  first | exact @GlobalTheory.DescIsoExists.lbIso_pull_fst_snd | exact GlobalTheory.DescIsoExists.lbIso_pull_fst_snd | (intros; apply GlobalTheory.DescIsoExists.lbIso_pull_fst_snd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectNormalisedEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectNormalisedEqOne
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm

theorem tripleFibreProductProjOneThree_comp_fst {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pr13 f ≫ pullback.fst f f = pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

theorem tripleFibreProductProjOneThree_comp_snd {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pr13 f ≫ pullback.snd f f = pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f :=
  pullback.lift_snd _ _ _

theorem defect_eq_one_of_coboundary {X Y Z : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (hL : L.IsLB)
    (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (z : X ⟶ X)
    (ρ : pullback f f ⟶ pullback f f) (σ : Triple f ⟶ Triple f)
    (h₁ : ρ ≫ pullback.fst f f = pullback.fst f f ≫ z) (h₂ : ρ ≫ pullback.snd f f = pullback.snd f f ≫ z)
    (k₁ : σ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) =
      pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ ρ)
    (k₂ : σ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ ρ)
    (g : X ⟶ Z) (U : L.ι → Z.Opens) (s : ∀ i, Γ(Z, U i)ˣ)
    (hN : ∀ (T : Scheme.{0}) (r : T ⟶ pullback f f) (t : T) (i j : L.ι),
      pullback.fst f f (ρ (r t)) ∈ L.U i → pullback.snd f f (ρ (r t)) ∈ L.U j →
      gm (r ≫ ρ) t _ (φ i j) =
        (gm (r ≫ pullback.fst f f ≫ g) t _ (s i))⁻¹ * gm (r ≫ pullback.snd f f ≫ g) t _ (s j))
    (hD : Defect f L φ D) (w : Triple f) : gm σ w ⊤ D = 1 := by
  have c : pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f := pullback.condition
  have k₃ : σ ≫ pr13 f = pr13 f ≫ ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, tripleFibreProductProjOneThree_comp_fst, h₁, ← Category.assoc, k₁, Category.assoc, h₁,
        ← Category.assoc, ← Category.assoc, tripleFibreProductProjOneThree_comp_fst]
    · rw [Category.assoc, Category.assoc, tripleFibreProductProjOneThree_comp_snd, h₂, ← Category.assoc, k₂, Category.assoc, h₂,
        ← Category.assoc, ← Category.assoc, tripleFibreProductProjOneThree_comp_snd]
  obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)))
  obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)))
  obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)))
  have e := hD _ σ w i j k hi hj hk
  have p₁ : ρ (pullback.fst (pullback.snd f f) (pullback.fst f f) w) =
      pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w) := congrArg (fun m => m w) k₁.symm
  have p₂ : ρ (pullback.snd (pullback.snd f f) (pullback.fst f f) w) =
      pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w) := congrArg (fun m => m w) k₂.symm
  have p₃ : ρ (pr13 f w) = pr13 f (σ w) := congrArg (fun m => m w) k₃.symm
  have pc : pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)) =
      pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) c.symm
  have q₁ : pullback.fst f f (pr13 f (σ w)) =
      pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) (tripleFibreProductProjOneThree_comp_fst f)
  have q₂ : pullback.snd f f (pr13 f (σ w)) =
      pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) (tripleFibreProductProjOneThree_comp_snd f)
  have a := hN _ (pullback.fst (pullback.snd f f) (pullback.fst f f)) w i j (by rw [p₁]; exact hi)
    (by rw [p₁]; exact hj)
  have b := hN _ (pullback.snd (pullback.snd f f) (pullback.fst f f)) w j k (by rw [p₂, pc]; exact hj)
    (by rw [p₂]; exact hk)
  have d := hN _ (pr13 f) w i k (by rw [p₃, q₁]; exact hi) (by rw [p₃, q₂]; exact hk)
  simp only [← Category.assoc] at a b d
  rw [tripleFibreProductProjOneThree_comp_fst, tripleFibreProductProjOneThree_comp_snd] at d
  rw [← c] at b
  rw [k₁, k₂, k₃, a, b, d, _root_.mul_assoc, mul_inv_cancel_left] at e
  exact mul_eq_right.1 e

theorem defect_normalised : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → ∀ (φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ) (D : Γ(Triple (q ▷ B).left, ⊤)ˣ), NormAlong q P τ φ → Defect (q ▷ B).left P φ D → ∀ w : Triple (q ▷ B).left, gm (rhoW q) w ⊤ D = 1 := by
  intro K _ A A' B _ _ q P τ hP φ D hN hD w
  exact defect_eq_one_of_coboundary (q ▷ B).left P hP φ D (zb A B).left (rhoZ q) (rhoW q) (rhoZ_fst q) (rhoZ_snd q)
    (rhoW_fst q) (rhoW_snd q) (fst A B).left _ (fun i => τ.s fun _ => i) hN hD w

end GlobalTheory.DescNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectNormalisedEqOneStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentCocycleDefect_normalised_eq_one : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → ∀ (φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ) (D : Γ(Triple (q ▷ B).left, ⊤)ˣ), NormAlong q P τ φ → Defect (q ▷ B).left P φ D → ∀ w : Triple (q ▷ B).left, gm (rhoW q) w ⊤ D = 1 := by
  first | exact @GlobalTheory.DescNorm.defect_normalised | exact GlobalTheory.DescNorm.defect_normalised | (intros; apply GlobalTheory.DescNorm.defect_normalised <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitTwistNormaliseDescentFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitTwistNormaliseDescentFamily
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNormU

theorem germ_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens)
    (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  apply Units.ext
  rw [gm_val (r ≫ q) z U h]
  show _ = (r.stalkMap z).hom (gm q (r z) U a).val
  rw [gm_val q (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (q ⁻¹ᵁ U) z h _).symm

variable {S : Scheme.{0}} {A A' B : Over S} [GrpObj A] [GrpObj B]

theorem zb_zb : zb A B ≫ zb A B = zb A B := by ext <;> simp [zb]
theorem zb_fst' : zb A B ≫ fst A B = fst A B := by simp [zb]
theorem fst_comp_lift_id_one_eq_prodSetSecondCoordZero : fst A B ≫ lift (𝟙 A) (1 : A ⟶ B) = zb A B := by ext <;> simp [zb]

theorem rhoZ_rhoZ (q : A ⟶ A') : rhoZ (B := B) q ≫ rhoZ q = rhoZ q := by
  have e : (zb A B).left ≫ (zb A B).left = (zb A B).left := by rw [← Over.comp_left, zb_zb]
  apply pullback.hom_ext <;> simp [e]

theorem rhoZ_a (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left := by
  rw [rhoZ_fst_assoc, ← Over.comp_left, zb_fst']

theorem rhoZ_a' (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left =
    pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left := by
  rw [rhoZ_snd_assoc, ← Over.comp_left, zb_fst']

theorem a_s (q : A ⟶ A') : (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ≫ (lift (𝟙 A) (1 : A ⟶ B)).left =
    rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left := by
  rw [rhoZ_fst, Category.assoc, ← Over.comp_left, fst_comp_lift_id_one_eq_prodSetSecondCoordZero]

theorem pullbackSnd_fst_comp_lift_id_one (q : A ⟶ A') : (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ≫ (lift (𝟙 A) (1 : A ⟶ B)).left =
    rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left := by
  rw [rhoZ_snd, Category.assoc, ← Over.comp_left, fst_comp_lift_id_one_eq_prodSetSecondCoordZero]

end GlobalTheory.DescNormU

namespace GlobalTheory.DescNormU

theorem germ_gen {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (τ : LB.Gen (L.pull F)) (hτ : τ.IsGen)
    (g : Y ⟶ X') (y : Y) (i i' : L.ι) (hi : F (g y) ∈ L.U i) (hi' : F (g y) ∈ L.U i') :
    gm g y _ (τ.s fun _ => i) = gm (g ≫ F) y _ (L.g i i') * gm g y _ (τ.s fun _ => i') := by
  have hp : g y ∈ (L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i') := ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
  have e : gm g y ((L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i')) ((L.pull F).g (fun _ => i) (fun _ => i')) =
      gm (g ≫ F) y _ (L.g i i') := by
    show gm g y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g i i'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res g y _ hp _).trans (gm_pull g F y (L.U i ⊓ L.U i') ⟨hi, hi'⟩ _)
  have := congrArg (gm g y ((L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i'))) (hτ (fun _ => i) (fun _ => i'))
  rw [map_mul, gm_res g y _ hp, gm_res g y _ hp, e] at this
  exact this

end GlobalTheory.DescNormU

namespace GlobalTheory.DescNormU

theorem pt_eq {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) : g (f x) = h x := by
  rw [← e]; rfl

theorem rhoZ_rhoZ_apply {S : Scheme.{0}} {A A' B : Over S} [GrpObj A] [GrpObj B] (q : A ⟶ A') (z) :
    rhoZ (B := B) q (rhoZ q z) = rhoZ q z := pt_eq (rhoZ_rhoZ q) z


set_option maxHeartbeats 800000 in
theorem normalise : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → τ.IsGen → ∀ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ, DescCompat (q ▷ B).left P φ → ∃ u : Γ(pullback (q ▷ B).left (q ▷ B).left, ⊤)ˣ, NormAlong q P τ (GlobalTheory.DescNorm.twist (q ▷ B).left P φ u) := by
  intro K _ A A' B _ _ q P τ hP hτ φ hφ
  let W : P.ι × P.ι → (pullback (q ▷ B).left (q ▷ B).left).Opens := fun p => rhoZ q ⁻¹ᵁ chart (q ▷ B).left P p.1 p.2
  have h2 : ∀ p, W p ≤ (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ⁻¹ᵁ
      (P.pull (lift (𝟙 A) (1 : A ⟶ B)).left).U (fun _ => p.1) := fun p z hz =>
    mem_pull.2 (by rw [pt_eq (a_s q) z]; exact hz.1)
  have h3 : ∀ p, W p ≤ (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ⁻¹ᵁ
      (P.pull (lift (𝟙 A) (1 : A ⟶ B)).left).U (fun _ => p.2) := fun p z hz =>
    mem_pull.2 (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz.2)
  let v : ∀ p, Γ(pullback (q ▷ B).left (q ▷ B).left, W p)ˣ := fun p =>
    (pullU (rhoZ q) _ (φ p.1 p.2))⁻¹ *
      (res (h2 p) (pullU (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) _ (τ.s fun _ => p.1)))⁻¹ *
      res (h3 p) (pullU (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) _ (τ.s fun _ => p.2))
  have hv : ∀ (Y : Scheme.{0}) (g : Y ⟶ pullback (q ▷ B).left (q ▷ B).left) (y : Y) (p : P.ι × P.ι), g y ∈ W p →
      gm g y (W p) (v p) = (gm (g ≫ rhoZ q) y _ (φ p.1 p.2))⁻¹ *
        (gm (g ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (τ.s fun _ => p.1))⁻¹ *
        gm (g ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (τ.s fun _ => p.2) := by
    intro Y g y p hy
    simp only [v, map_mul, map_inv]
    rw [gm_pull g (rhoZ q) y _ hy, gm_res g y (h2 p) hy, gm_pull g (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (h2 p hy),
      gm_res g y (h3 p) hy, gm_pull g (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (h3 p hy)]

  have indep : ∀ p p', ∀ z ∈ W p ⊓ W p', gm (𝟙 _) z (W p) (v p) = gm (𝟙 _) z (W p') (v p') := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ z ⟨hz, hz'⟩
    rw [hv _ (𝟙 _) z _ hz, hv _ (𝟙 _) z _ hz']
    simp only [Category.id_comp]
    have hz1 : pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U i := hz.1
    have hz2 : pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U j := hz.2
    have hz1' : pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U i' := hz'.1
    have hz2' : pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U j' := hz'.2
    have c1 : gm (rhoZ q) z _ (φ i' j') = gm (rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left) z _ (P.g i i') *
        gm (rhoZ q) z _ (φ i j) * gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j' j) := by
      have e := congrArg (Units.map ((rhoZ q).stalkMap z).hom.toMonoidHom) (hφ (rhoZ q z) i i' j j' hz1 hz1' hz2 hz2')
      rw [map_mul, map_mul] at e
      have k1 := germ_comp (rhoZ q) (𝟙 _) z (chart (q ▷ B).left P i' j') ⟨hz1', hz2'⟩ (φ i' j')
      have k2 := germ_comp (rhoZ q) (𝟙 _) z (chart (q ▷ B).left P i j) ⟨hz1, hz2⟩ (φ i j)
      have k3 := germ_comp (rhoZ q) (pullback.fst (q ▷ B).left (q ▷ B).left) z (P.U i ⊓ P.U i') ⟨hz1, hz1'⟩ (P.g i i')
      have k4 := germ_comp (rhoZ q) (pullback.snd (q ▷ B).left (q ▷ B).left) z (P.U j' ⊓ P.U j) ⟨hz2', hz2⟩ (P.g j' j)
      rw [Category.comp_id] at k1 k2
      rw [k1, k2, k3, k4]
      exact e
    have t1 := germ_gen τ hτ (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z i i'
      (by rw [pt_eq (a_s q) z]; exact hz1) (by rw [pt_eq (a_s q) z]; exact hz1')
    have t2 := germ_gen τ hτ (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z j j'
      (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz2) (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz2')
    rw [a_s] at t1
    rw [pullbackSnd_fst_comp_lift_id_one] at t2
    have cc := gm_cocycle hP (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z hz2 hz2' hz2
    rw [gm_self hP _ z hz2] at cc
    rw [c1, t1, t2]
    generalize gm (rhoZ q) z _ (φ i j) = Φ
    generalize gm (rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left) z _ (P.g i i') = G₁
    generalize gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j' j) = G₂ at cc ⊢
    generalize gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j j') = H at cc ⊢
    generalize gm (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z _ (τ.s fun _ => i') = T₁
    generalize gm (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z _ (τ.s fun _ => j') = T₂
    rw [eq_inv_of_mul_eq_one_left cc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hc : (⊤ : (pullback (q ▷ B).left (q ▷ B).left).Opens) ≤ iSup W := fun z _ => by
    obtain ⟨i, hi⟩ := exists_chart hP (pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z))
    obtain ⟨j, hj⟩ := exists_chart hP (pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩
  obtain ⟨u, hu⟩ := glue_unit ⊤ W (fun _ => le_top) hc v indep
  refine ⟨u, fun T r t i j hi hj => ?_⟩
  have hm : (r ≫ rhoZ q) t ∈ chart (q ▷ B).left P i j := ⟨hi, hj⟩
  have hw : (r ≫ rhoZ q) t ∈ W (i, j) := by
    show rhoZ q (rhoZ q (r t)) ∈ chart (q ▷ B).left P i j
    rw [rhoZ_rhoZ_apply]; exact hm
  show gm _ t _ (φ i j * res le_top u) = _
  rw [map_mul, gm_res _ t le_top hm, ← gm_res _ t (le_top : W (i, j) ≤ ⊤) hw u, hu (i, j), hv T (r ≫ rhoZ q) t (i, j) hw]
  simp only [Category.assoc, rhoZ_rhoZ, rhoZ_a, rhoZ_a']
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]

end GlobalTheory.DescNormU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitTwistNormaliseDescentFamilyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalUnit_twist_normalise_descent_family : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → τ.IsGen → ∀ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ, DescCompat (q ▷ B).left P φ → ∃ u : Γ(pullback (q ▷ B).left (q ▷ B).left, ⊤)ˣ, NormAlong q P τ (twist (q ▷ B).left P φ u) := by
  first | exact @GlobalTheory.DescNormU.normalise | exact GlobalTheory.DescNormU.normalise | (intros; apply GlobalTheory.DescNormU.normalise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumAdditiveLineBundleIsogeny
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DescNorm

theorem twist_descCompat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (u : Γ(pullback f f, ⊤)ˣ), DescCompat f L φ → DescCompat f L (twist f L φ u) := by
  intro X Y f L φ u hφ z i i' j j' hi hi' hj hj'
  have m : ∀ a b, pullback.fst f f z ∈ L.U a → pullback.snd f f z ∈ L.U b → (𝟙 (pullback f f)) z ∈ chart f L a b :=
    fun a b ha hb => ⟨ha, hb⟩
  simp only [twist, map_mul]
  rw [gm_res (𝟙 _) z le_top (m i' j' hi' hj'), gm_res (𝟙 _) z le_top (m i j hi hj), hφ z i i' j j' hi hi' hj hj']
  ac_rfl

theorem descentDatum_of_additive : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → ∃ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, GlobalTheory.LBDescent.chart (q ▷ B).left P i j)ˣ, GlobalTheory.LBDescent.DescCompat (q ▷ B).left P φ ∧ GlobalTheory.LBDescent.DescCocycle (q ▷ B).left P φ := by
  intro K _ _ A A' B _ _ _ q P hA hA' hB hq _ _ _ hP hadd hzero hker
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.T.exists_descentDatumCompatible_of_lineBundle_iso _ P hP (GlobalTheory.T.lineBundle_iso_pullback_fst_snd_of_additive_trivial_kernel K A A' B q P hA hA' hB hq hP hadd hker)
  obtain ⟨τ, hτ⟩ := hzero
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_globalUnit_twist_normalise_descent_family K A A' B q P τ hP hτ φ₀ hφ₀
  have hc : DescCompat (q ▷ B).left P (twist (q ▷ B).left P φ₀ u) := twist_descCompat _ P φ₀ u hφ₀
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_descentCocycleDefect_of_compatible _ P _ hP hc
  have h1 := GlobalTheory.T.descentCocycleDefect_normalised_eq_one K A A' B q P τ hP _ D hu hD
  have h2 := GlobalTheory.T.globalUnit_tripleFibreProduct_invariant_setGroupCoordZero K A A' B q hB D
  refine ⟨twist (q ▷ B).left P φ₀ u, hc, fun w i j k hi hj hk => ?_⟩
  have e := hD _ (𝟙 _) w i j k hi hj hk
  rw [← h2 w, h1 w, _root_.one_mul, Category.id_comp, Category.id_comp, Category.id_comp] at e
  exact e.symm

end GlobalTheory.DescNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumAdditiveLineBundleIsogenyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descentDatum_additive_lineBundle_isogeny : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → ∃ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, GlobalTheory.LBDescent.chart (q ▷ B).left P i j)ˣ, GlobalTheory.LBDescent.DescCompat (q ▷ B).left P φ ∧ GlobalTheory.LBDescent.DescCocycle (q ▷ B).left P φ := by
  first | exact @GlobalTheory.DescNorm.descentDatum_of_additive | exact GlobalTheory.DescNorm.descentDatum_of_additive | (intros; apply GlobalTheory.DescNorm.descentDatum_of_additive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleDescendsAlongIsogenyTorsor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PoincareDescent

theorem descend_torsor : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q → Triv (ev P (fst N B ≫ i) (snd N B)) → ∃ P₀ : LB (A' ⊗ B).left, P₀.IsLB ∧ LBIso (ev P₀ (fst A B ≫ q) (snd A B)) P := by
  intro K _ _ A A' B N _ _ _ _ P i q hA hA' hB hP hadd hzero hi hq hfin hflat hsurj hsq hN
  haveI : IsFinite q.left := hfin
  haveI : Flat q.left := hflat
  haveI : Surjective q.left := hsurj
  have hpb := GlobalTheory.AbLaw.SecBC.isPullback_whisker (A := B) q
  haveI : IsFinite (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hfin
  haveI : Flat (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hflat
  haveI : Surjective (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hsurj
  haveI : IsLocallyNoetherian (A' ⊗ B).left := by
    haveI := hA'.smooth
    haveI := hB.smooth
    haveI : LocallyOfFiniteType (A' ⊗ B).hom := by
      show LocallyOfFiniteType (pullback.fst A'.hom B.hom ≫ A'.hom)
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian (A' ⊗ B).hom
  have hker : ∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B)) := by
    intro T x hx
    have e : (1 : T ⟶ A) ≫ q = x ≫ q := by rw [hx, MonObj.one_comp]
    have hx' : x = (hsq.lift 1 x e ≫ snd A N) ≫ i := by
      have h2 := hsq.lift_snd 1 x e
      rw [MonObj.comp_mul, hsq.lift_fst, _root_.one_mul, ← Category.assoc] at h2
      exact h2.symm
    obtain ⟨n, rfl⟩ : ∃ n : T ⟶ N, x = n ≫ i := ⟨_, hx'⟩
    rw [triv_ev_iff hP]
    have z := congrArg (CechPic.pull (lift (fst T B ≫ n) (snd T B)).left) ((triv_ev_iff hP _ _).1 hN)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd, Category.assoc] at z
    exact z
  obtain ⟨φ, hc, hco⟩ := GlobalTheory.T.exists_descentDatum_additive_lineBundle_isogeny K A A' B q P hA hA' hB hq hfin hflat hsurj hP hadd hzero hker
  obtain ⟨P₀, hP₀, hiso⟩ := GlobalTheory.T.exists_lineBundle_descent_finiteFlat _ _ (q ▷ B).left P hP φ hc hco
  refine ⟨P₀, hP₀, (cls_eq_iff (pull_isLB hP₀ _) hP).1 ?_⟩
  refine Eq.trans ?_ ((cls_eq_iff hP (pull_isLB hP₀ _)).2 hiso).symm
  rw [cls_ev hP₀, evc, cls_pull hP₀, ← lift_whiskerRight, lift_fst_snd, Category.id_comp]

end GlobalTheory.PoincareDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleDescendsAlongIsogenyTorsorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_lineBundle_descends_along_isogeny_torsor : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q → Triv (ev P (fst N B ≫ i) (snd N B)) → ∃ P₀ : LB (A' ⊗ B).left, P₀.IsLB ∧ LBIso (ev P₀ (fst A B ≫ q) (snd A B)) P := by
  first | exact @GlobalTheory.PoincareDescent.descend_torsor | exact GlobalTheory.PoincareDescent.descend_torsor | (intros; apply GlobalTheory.PoincareDescent.descend_torsor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleDescendsQuotientFiniteSubgroup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareDescent

theorem descends : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A']
    [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A →
    IsAbelianScheme A' → IsAbelianScheme B → IsDual A B P → IsMonHom i → IsMonHom q → IsFinite q.left →
    Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → Triv (ev P (fst N B ≫ i) (snd N B)) →
    ∃ P' : LB (A' ⊗ B).left, P'.IsLB ∧ IsAdditive P' ∧ LBIso (ev P' (fst A B ≫ q) (snd A B)) P := by
  intro K _ _ A A' B N _ _ _ _ P i q hA hA' hB hD hi hq hfin hfl hsurj hker hN
  obtain ⟨P₀, hP₀, e⟩ := GlobalTheory.T.additive_lineBundle_descends_along_isogeny_torsor K A A' B N P i q hA hA' hB hD.isLB hD.additive hD.zero hi hq hfin hfl
    hsurj (torsor_square i q hker) hN
  have key : ∀ (Y : Over (Sp K)) (a : Y ⟶ A) (b : Y ⟶ B), evc hP₀ (a ≫ q) b = evc hD.isLB a b := by
    intro Y a b
    have c := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff (pull_isLB hP₀ _) hD.isLB).2 e)
    rw [cls_ev hP₀, pull_evc, lift_fst_assoc, lift_snd] at c
    exact c
  let φ : Fin 2 → ((A' ⊗ B).left ⟶ (A' ⊗ B).left) :=
    ![(lift (fst A' B) (snd A' B)).left, (lift (fst A' B) (1 : A' ⊗ B ⟶ B)).left]
  have hP' : (LB.LinComb P₀ φ ![1, -1]).IsLB := LB.isLB_linComb hP₀ _ _
  have ev' : ∀ (Y : Over (Sp K)) (a : Y ⟶ A') (b : Y ⟶ B), evc hP' a b = evc hP₀ a b - evc hP₀ a 1 := by
    intro Y a b
    rw [evc, cls_linComb hP₀, Fin.sum_univ_two, map_add (f := _), map_zsmul, map_zsmul, ← pull_comp, ← pull_comp]
    simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd, MonObj.comp_one, one_smul, neg_smul, evc, sub_eq_add_neg]
  have one : ∀ (Y : Over (Sp K)) (b : Y ⟶ B), evc hP₀ (1 : Y ⟶ A') b = 0 := fun Y b ↦ by
    have : (1 : Y ⟶ A) ≫ q = 1 := by simp
    rw [← this, key]
    exact hD.additive.evc_one hD.isLB b
  refine ⟨_, hP', CubeNoeth.isAdditive_of_triv_axes hA' hB hP' ?_ ?_, ?_⟩
  · rw [triv_ev_iff hP', ev', one, one, sub_self]
  · rw [triv_ev_iff hP', ev', sub_self]
  · refine (cls_eq_iff (pull_isLB hP' _) hD.isLB).1 ?_
    rw [cls_ev hP', ev', key, key, evc_one_right hD.isLB hD.zero, sub_zero, evc, lift_fst_snd, Over.id_left,
      pull_id]

end GlobalTheory.PoincareDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleDescendsQuotientFiniteSubgroupStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareBundle_descends_quotient_finiteSubgroup : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsDual A B P → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → Triv (ev P (fst N B ≫ i) (snd N B)) → ∃ P' : LB (A' ⊗ B).left, P'.IsLB ∧ IsAdditive P' ∧ LBIso (ev P' (fst A B ≫ q) (snd A B)) P := by
  first | exact @GlobalTheory.PoincareDescent.descends | exact GlobalTheory.PoincareDescent.descends | (intros; apply GlobalTheory.PoincareDescent.descends <;> assumption)
end
