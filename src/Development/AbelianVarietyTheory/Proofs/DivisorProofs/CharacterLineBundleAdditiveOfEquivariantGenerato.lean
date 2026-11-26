module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentitySnd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

def pmap2 {A A' : Over S} (q : A ⟶ A') (T : Over S) : A ⊗ (A ⊗ T) ⟶ A' ⊗ (A' ⊗ T) :=
  lift (fst A (A ⊗ T) ≫ q) (snd A (A ⊗ T) ≫ pmap q T)

def ptFst (A T : Over S) : A ⊗ (A ⊗ T) ⟶ A ⊗ T := lift (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T)

def ptSnd (A T : Over S) : A ⊗ (A ⊗ T) ⟶ A ⊗ T := lift (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)

def ptMul (A T : Over S) [MonObj A] : A ⊗ (A ⊗ T) ⟶ A ⊗ T :=
  lift (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T)

def addBundle {A T : Over S} [MonObj A] (M : LB (A ⊗ T).left) : LB (A ⊗ (A ⊗ T)).left :=
  LB.div (tens (ev M (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
      (ev M (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)))
    (ev M (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T))

theorem preimage_le_of_comp {X Y Z W : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ W} {f' : X ⟶ Z} {g' : Z ⟶ W}
    (h : f ≫ g = f' ≫ g') (U : W.Opens) : f ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ f' ⁻¹ᵁ (g' ⁻¹ᵁ U) := by
  intro x hx
  have e : g.base (f.base x) = g'.base (f'.base x) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  show g'.base (f'.base x) ∈ U
  rw [← e]
  exact hx

theorem prodMapPairTimesIdentity_fst {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    (pmap2 q T).left ≫ (lift (fst A' (A' ⊗ T)) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptFst A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptFst, pmap]

theorem prodMapPairTimesIdentity_snd {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    (pmap2 q T).left ≫ (lift (snd A' (A' ⊗ T) ≫ fst A' T) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptSnd A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptSnd, pmap]

theorem prodMapPairTimesIdentity_mul {A A' : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (T : Over S) :
    (pmap2 q T).left ≫ (lift (fst A' (A' ⊗ T) * (snd A' (A' ⊗ T) ≫ fst A' T)) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptMul A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptMul, pmap, MonObj.comp_mul, MonObj.mul_comp]

theorem addGen_le₁ {A A' T : Over S} [MonObj A'] (q : A ⟶ A') (M : LB (A' ⊗ T).left) (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptFst A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.1.1 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_fst q T) _)
  intro x hx
  exact LB.wchart_le M _ k.1.1 PUnit.unit hx.1.1

theorem addGen_le₂ {A A' T : Over S} [MonObj A'] (q : A ⟶ A') (M : LB (A' ⊗ T).left) (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptSnd A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.1.2 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_snd q T) _)
  intro x hx
  exact LB.wchart_le M _ k.1.2 PUnit.unit hx.1.2

theorem addGen_le₃ {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left)
    (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptMul A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.2 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_mul q T) _)
  intro x hx
  exact LB.wchart_le M _ k.2 PUnit.unit hx.2

def addGen {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left)
    (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (k : (addBundle M).ι) :
    Γ((A ⊗ (A ⊗ T)).left, (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)ˣ :=
  res (addGen_le₁ q M k) (pullU (ptFst A T).left _ (e (k.1.1 PUnit.unit))) *
    res (addGen_le₂ q M k) (pullU (ptSnd A T).left _ (e (k.1.2 PUnit.unit))) *
    (res (addGen_le₃ q M k) (pullU (ptMul A T).left _ (e (k.2 PUnit.unit))))⁻¹

end GlobalTheory.CharKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivityDefectGeneratorInvariantSameImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivityDefectGeneratorInvariantSameImage
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

private theorem coe_gm_eq_stalkMap_germ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U)
    (a : Γ(X, U)ˣ) :
    ((gm f y U a : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) =
      f.stalkMap y (X.presheaf.germ U (f y) h (a : Γ(X, U))) := by
  unfold gm
  rw [dite_eq_left h]
  simp only [pullU, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact (Scheme.Hom.germ_stalkMap_apply f U y h _).symm

private theorem gm_res_pullU_lemma_2 {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (ψ : Z ⟶ Y) (z : Z) (U : X.Opens)
    {V : Y.Opens} (hle : V ≤ φ ⁻¹ᵁ U) (hz : ψ z ∈ V) (a : Γ(X, U)ˣ) :
    gm ψ z V (res hle (pullU φ U a)) = gm (ψ ≫ φ) z U a := by
  have h1 : φ (ψ z) ∈ U := hle hz
  apply Units.ext
  rw [coe_gm_eq_stalkMap_germ ψ z V hz, coe_gm_eq_stalkMap_germ (ψ ≫ φ) z U h1]
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [Scheme.Hom.stalkMap_comp]
  erw [TopCat.Presheaf.germ_res_apply]
  exact congrArg (Scheme.Hom.stalkMap ψ z) (Scheme.Hom.germ_stalkMap_apply φ U (ψ z) h1 _).symm

private theorem gm_pullTop_inv {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (a : Γ(X, ⊤)ˣ) :
    gm f z ⊤ (pullTop g a) = gm (f ≫ g) z ⊤ a := by
  apply Units.ext
  rw [coe_gm_eq_stalkMap_germ f z ⊤ trivial, coe_gm_eq_stalkMap_germ (f ≫ g) z ⊤ trivial]
  rw [Scheme.Hom.stalkMap_comp]
  exact congrArg (Scheme.Hom.stalkMap f z) (Scheme.Hom.germ_stalkMap_apply g ⊤ (f z) trivial _).symm

theorem gm_character_mul {S : Scheme.{0}} {N T Z : Over S} [GrpObj N] {χ : Γ((N ⊗ T).left, ⊤)ˣ}
    (hχ : IsCharacter χ) (ν₁ ν₂ : Z ⟶ N) (t : Z ⟶ T) (z : Z.left) :
    gm (lift (ν₁ * ν₂) t).left z ⊤ χ = gm (lift ν₁ t).left z ⊤ χ * gm (lift ν₂ t).left z ⊤ χ := by
  have hy1 : lift ν₁ (lift ν₂ t) ≫ lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T) =
      lift (ν₁ * ν₂) t := by
    simp [comp_lift, MonObj.comp_mul]
  have hy2 : lift ν₁ (lift ν₂ t) ≫ lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T) = lift ν₁ t := by
    simp [comp_lift]
  have hy3 : lift ν₁ (lift ν₂ t) ≫ snd N (N ⊗ T) = lift ν₂ t := by simp
  have hc : IsCharacter χ := hχ
  unfold IsCharacter at hc
  rw [← hy1, Over.comp_left, ← gm_pullTop_inv, hc, map_mul, gm_pullTop_inv, gm_pullTop_inv,
    ← Over.comp_left, ← Over.comp_left, hy2, hy3]

theorem gm_equivGen {S : Scheme.{0}} {A A' N T Z : Over S} [GrpObj A] {i : N ⟶ A} {q : A ⟶ A'}
    {χ : Γ((N ⊗ T).left, ⊤)ˣ} {M : LB (A' ⊗ T).left} {e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ}
    (he : IsEquivGen i q χ M e) (a b : Z ⟶ A) (ν : Z ⟶ N) (t : Z ⟶ T) (hb : b = a * (ν ≫ i)) (z : Z.left)
    (k : M.ι) (h₁ : (lift b t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U k)
    (h₂ : (lift a t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U k) :
    gm (lift b t).left z _ (e k) = gm (lift ν t).left z ⊤ χ * gm (lift a t).left z _ (e k) := by
  set y : Z ⟶ A ⊗ (N ⊗ T) := lift a (lift ν t) with hy
  have e1 : y.left ≫ (actMap i T).left = (lift b t).left := by
    rw [← Over.comp_left, hb, hy]
    unfold actMap
    simp [comp_lift, MonObj.comp_mul]
  have e2 : y.left ≫ (prMap A N T).left = (lift a t).left := by
    rw [← Over.comp_left, hy]
    unfold prMap
    simp [comp_lift]
  have e3 : y.left ≫ (snd A (N ⊗ T)).left = (lift ν t).left := by
    rw [← Over.comp_left, hy]
    simp
  have w1 : y.left z ∈ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) := by
    rw [← e1] at h₁
    exact h₁
  have w2 : y.left z ∈ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) := by
    rw [← e2] at h₂
    exact h₂
  have key := congrArg (gm y.left z ((actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) ⊓
    (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k))) (he.2 k _ inf_le_left inf_le_right)
  have hw : y.left z ∈ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) ⊓
      (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) := ⟨w1, w2⟩
  rw [map_mul, gm_res_pullU_lemma_2 _ _ _ _ _ hw, gm_res_pullU_lemma_2 _ _ _ _ _ hw, e1, e2] at key
  have hχ' : gm y.left z ((actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) ⊓
      (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k)) (res le_top (pullTop (snd A (N ⊗ T)).left χ)) =
      gm (lift ν t).left z ⊤ χ := by
    have := gm_res_pullU_lemma_2 (snd A (N ⊗ T)).left y.left z ⊤ (V := _) le_top hw χ
    rw [e3] at this
    exact this
  rw [hχ'] at key
  exact key

theorem gm_addGen {S : Scheme.{0}} {A A' T Z : Over S} [GrpObj A] [GrpObj A'] (q : A ⟶ A') [IsMonHom q]
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (a a' : Z ⟶ A) (t : Z ⟶ T)
    (z : Z.left) (k : (addBundle M).ι)
    (h : (lift a (lift a' t)).left z ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k) :
    ((lift a t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U (k.1.1 PUnit.unit) ∧
      (lift a' t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U (k.1.2 PUnit.unit) ∧
      (lift (a * a') t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U (k.2 PUnit.unit)) ∧
    gm (lift a (lift a' t)).left z _ (addGen q M e k) =
      gm (lift a t).left z _ (e (k.1.1 PUnit.unit)) * gm (lift a' t).left z _ (e (k.1.2 PUnit.unit)) *
        (gm (lift (a * a') t).left z _ (e (k.2 PUnit.unit)))⁻¹ := by
  set y : Z ⟶ A ⊗ (A ⊗ T) := lift a (lift a' t) with hy
  have eF : y.left ≫ (ptFst A T).left = (lift a t).left := by
    rw [← Over.comp_left, hy]
    unfold ptFst
    simp [comp_lift]
  have eS : y.left ≫ (ptSnd A T).left = (lift a' t).left := by
    rw [← Over.comp_left, hy]
    unfold ptSnd
    simp [comp_lift]
  have eM : y.left ≫ (ptMul A T).left = (lift (a * a') t).left := by
    rw [← Over.comp_left, hy]
    unfold ptMul
    simp [comp_lift, MonObj.comp_mul]
  have m1 := addGen_le₁ q M k h
  have m2 := addGen_le₂ q M k h
  have m3 := addGen_le₃ q M k h
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← eF]
    exact m1
  · rw [← eS]
    exact m2
  · rw [← eM]
    exact m3
  · unfold addGen
    rw [map_mul, map_mul, map_inv, gm_res_pullU_lemma_2 _ _ _ _ _ h, gm_res_pullU_lemma_2 _ _ _ _ _ h,
      gm_res_pullU_lemma_2 _ _ _ _ _ h, eF, eS, eM]

private theorem germ_eq_gm_coe {Z : Scheme.{0}} (W : Z.Opens) (w : Z) (hw : w ∈ W) (x : Γ(Z, W)ˣ) :
    Z.presheaf.germ W w hw (x : Γ(Z, W)) = ((gm (𝟙 Z) w W x : (Z.presheaf.stalk w)ˣ) : Z.presheaf.stalk w) := by
  rw [coe_gm_eq_stalkMap_germ (𝟙 Z) w W hw]
  erw [Scheme.Hom.stalkMap_id]
  rfl

private theorem mul_mul_mul_inv_cancel_left_factors {G : Type*} [CommGroup G] (c₁ c₂ E₁ E₂ E₃ : G) :
    c₁ * E₁ * (c₂ * E₂) * (c₁ * c₂ * E₃)⁻¹ = E₁ * E₂ * E₃⁻¹ := by
  rw [mul_inv (c₁ * c₂) E₃, _root_.mul_mul_mul_comm c₁ E₁ c₂ E₂, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]

theorem addGen_invariant : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsMonHom i → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → IsEquivGen i q χ M e → ∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ (A ⊗ (A ⊗ T)).left), y₁ ≫ (pmap2 q T).left = y₂ ≫ (pmap2 q T).left → ∀ (k : (addBundle M).ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)), res h₁ (pullU y₁ _ (addGen q M e k)) = res h₂ (pullU y₂ _ (addGen q M e k)) := by
  intro S A A' N T _i1 _i2 _i3 _i4 i q _i5 χ M e hi hpb hχ he Z y₁ y₂ hy k W h₁ h₂
  haveI := hi
  apply Units.ext
  apply TopCat.Presheaf.section_ext Z.sheaf W
  intro w hw
  erw [germ_eq_gm_coe W w hw, germ_eq_gm_coe W w hw]
  rw [gm_res_pullU_lemma_2 y₁ (𝟙 Z) w _ h₁ hw, gm_res_pullU_lemma_2 y₂ (𝟙 Z) w _ h₂ hw, Category.id_comp,
    Category.id_comp]
  have m₁ : y₁ w ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k := h₁ hw
  have m₂ : y₂ w ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k := h₂ hw
  have hyS : y₂ ≫ (A ⊗ (A ⊗ T)).hom = y₁ ≫ (A ⊗ (A ⊗ T)).hom := by
    have h := congrArg (· ≫ (A' ⊗ (A' ⊗ T)).hom) hy
    simp only [Category.assoc, Over.w] at h
    exact h.symm
  let Z' : Over S := Over.mk (y₁ ≫ (A ⊗ (A ⊗ T)).hom)
  let Y₁ : Z' ⟶ A ⊗ (A ⊗ T) := Over.homMk y₁ rfl
  let Y₂ : Z' ⟶ A ⊗ (A ⊗ T) := Over.homMk y₂ hyS
  have hY : Y₁ ≫ pmap2 q T = Y₂ ≫ pmap2 q T := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    exact hy
  have h_a : Y₁ ≫ fst A (A ⊗ T) ≫ q = Y₂ ≫ fst A (A ⊗ T) ≫ q := by
    have h := congrArg (· ≫ fst A' (A' ⊗ T)) hY
    simpa [pmap2] using h
  have h_b : Y₁ ≫ snd A (A ⊗ T) ≫ fst A T ≫ q = Y₂ ≫ snd A (A ⊗ T) ≫ fst A T ≫ q := by
    have h := congrArg (· ≫ snd A' (A' ⊗ T) ≫ fst A' T) hY
    simpa [pmap2, pmap] using h
  have h_t : Y₁ ≫ snd A (A ⊗ T) ≫ snd A T = Y₂ ≫ snd A (A ⊗ T) ≫ snd A T := by
    have h := congrArg (· ≫ snd A' (A' ⊗ T) ≫ snd A' T) hY
    simpa [pmap2, pmap] using h
  have eY₁ : lift (Y₁ ≫ fst A (A ⊗ T)) (lift (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T)) = Y₁ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply CartesianMonoidalCategory.hom_ext <;> simp
  have eY₂ : lift (Y₂ ≫ fst A (A ⊗ T)) (lift (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T)) = Y₂ := by
    rw [h_t]
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply CartesianMonoidalCategory.hom_ext <;> simp
  have hP := pmap_isPullback_actMap S A A' N T i q hi inferInstance hpb
  have wa : lift (Y₁ ≫ fst A (A ⊗ T)) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T =
      lift (Y₂ ≫ fst A (A ⊗ T)) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T := by
    simp [pmap, comp_lift, h_a]
  have wb : lift (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T =
      lift (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T := by
    simp [pmap, comp_lift, h_b]
  have key : ∀ (a₁ a₂ : Z' ⟶ A) (t : Z' ⟶ T), lift a₁ t ≫ pmap q T = lift a₂ t ≫ pmap q T →
      ∃ ν : Z' ⟶ N, a₂ = a₁ * (ν ≫ i) := by
    intro a₁ a₂ t hw'
    have e1 := congrArg (· ≫ fst A T) (hP.lift_snd (lift a₁ t) (lift a₂ t) hw')
    have e2 := congrArg (· ≫ fst A T) (hP.lift_fst (lift a₁ t) (lift a₂ t) hw')
    generalize hP.lift (lift a₁ t) (lift a₂ t) hw' = u at e1 e2
    refine ⟨u ≫ snd A (N ⊗ T) ≫ fst N T, ?_⟩
    simp only [actMap, prMap, Category.assoc, lift_fst, MonObj.comp_mul] at e1 e2
    rw [← e1, e2]
    simp [Category.assoc]
  obtain ⟨ν, hν⟩ := key _ _ _ wa
  obtain ⟨ν', hν'⟩ := key _ _ _ wb
  have hνν : Y₂ ≫ fst A (A ⊗ T) * (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T) =
      Y₁ ≫ fst A (A ⊗ T) * (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T) * ((ν * ν') ≫ i) := by
    rw [hν, hν', MonObj.mul_comp, _root_.mul_mul_mul_comm]
  have M₁ := (gm_addGen q M e (Y₁ ≫ fst A (A ⊗ T)) (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T)
    (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) w k (by rw [eY₁]; exact m₁))
  have M₂ := (gm_addGen q M e (Y₂ ≫ fst A (A ⊗ T)) (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T)
    (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) w k (by rw [eY₂]; exact m₂))
  have G₁ := M₁.2
  have G₂ := M₂.2
  rw [eY₁] at G₁
  rw [eY₂] at G₂
  refine congrArg Units.val ?_
  change gm Y₁.left w _ (addGen q M e k) = gm Y₂.left w _ (addGen q M e k) at ⊢
  rw [G₁, G₂, gm_equivGen he _ _ ν _ hν w _ M₂.1.1 M₁.1.1, gm_equivGen he _ _ ν' _ hν' w _ M₂.1.2.1 M₁.1.2.1,
    gm_equivGen he _ _ (ν * ν') _ hνν w _ M₂.1.2.2 M₁.1.2.2, gm_character_mul hχ ν ν', mul_mul_mul_inv_cancel_left_factors]

end GlobalTheory.CharKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivityDefectGeneratorInvariantSameImageStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additivityDefect_generator_invariant_same_image : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsMonHom i → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → IsEquivGen i q χ M e → ∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ (A ⊗ (A ⊗ T)).left), y₁ ≫ (pmap2 q T).left = y₂ ≫ (pmap2 q T).left → ∀ (k : (addBundle M).ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)), res h₁ (pullU y₁ _ (addGen q M e k)) = res h₂ (pullU y₂ _ (addGen q M e k)) := by
  first | exact @GlobalTheory.CharKer.addGen_invariant | exact GlobalTheory.CharKer.addGen_invariant | (intros; apply GlobalTheory.CharKer.addGen_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfInvariantPullbackGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfInvariantPullbackGenerator
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

section Descent

variable {X Y : Scheme.{0}}

lemma appLE_eq_of_eq_hom {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

lemma opens_toTop_bijective (U : X.Opens) : Function.Bijective (U.ι.appLE U ⊤ U.ι_preimage_self.ge) := by
  have e : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]; rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso U.topIso.inv

lemma restrict_appTop_toTop (p : X ⟶ Y) (V : Y.Opens) (a : Γ(Y, V)) :
    (p ∣_ V).appTop (V.ι.appLE V ⊤ V.ι_preimage_self.ge a) =
      (p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge (p.app V a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg _ (appLE_eq_of_eq_hom (morphismRestrict_ι p V) _ _ _)

lemma restrict_props (p : X ⟶ Y) [Flat p] [Surjective p] [IsAffineHom p] (V : Y.Opens) :
    Flat (p ∣_ V) ∧ Surjective (p ∣_ V) ∧ IsAffineHom (p ∣_ V) :=
  ⟨inferInstance, IsZariskiLocalAtTarget.restrict ‹_› V, by first | exact HasAffineProperty.restrict ‹_› V | exact IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) ‹_› V | exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict p V).flip ‹_›) | exact (inferInstance : IsAffineHom (p.resLE V (p ⁻¹ᵁ V) le_rfl))⟩

lemma appTop_toTop (V : X.Opens) {Z : Scheme.{0}} (y : Z ⟶ V.toScheme) (s : Γ(X, V)) :
    y.appTop (V.ι.appLE V ⊤ V.ι_preimage_self.ge s) =
      (y ≫ V.ι).appLE V ⊤ (fun z _ => (y z).2) s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  rfl

theorem exists_app_eq_of_invariant (p : X ⟶ Y) [Flat p] [Surjective p] [IsAffineHom p] (V : Y.Opens)
    (s : Γ(X, p ⁻¹ᵁ V))
    (hs : ∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (h₁ : ⊤ ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ V))
      (h₂ : ⊤ ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ V)), y₁.appLE _ ⊤ h₁ s = y₂.appLE _ ⊤ h₂ s) :
    ∃ a : Γ(Y, V), p.app V a = s := by
  obtain ⟨h1, h2, h3⟩ := restrict_props p V
  obtain ⟨v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.descend_gen (p ∣_ V)
    ((p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge s) (fun y₁ y₂ h => by
      rw [appTop_toTop, appTop_toTop]
      refine hs _ _ _ ?_ _ _
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, h, Category.assoc])
  obtain ⟨a, rfl⟩ := (opens_toTop_bijective V).2 v
  refine ⟨a, (opens_toTop_bijective (p ⁻¹ᵁ V)).1 ?_⟩
  rw [← restrict_appTop_toTop]
  exact hv

lemma app_map_homOfLE (p : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    p.app V (Y.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (fun _ hx => h hx : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U)).op (p.app U a) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

end Descent


open ReciprocityTheory.ChartRestriction.G.DVR.TG in
theorem triv_of_isPullGen_of_invariant : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y), Flat p → Surjective p → IsAffineHom p → ∀ (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → (∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (k : M.ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)), res h₁ (pullU y₁ _ (e k)) = res h₂ (pullU y₂ _ (e k))) → Triv M := by
  intro X Y p _ _ _ M e he hinv
  have hval : ∀ (k : M.ι) (u : Γ(X, p ⁻¹ᵁ M.U k)ˣ), (u = e k ∨ u = (e k)⁻¹) →
      ∃ a : Γ(Y, M.U k), p.app _ a = u := by
    intro k u hu
    refine exists_app_eq_of_invariant p (M.U k) u ?_
    intro Z y₁ y₂ hy h₁ h₂
    have H := hinv Z y₁ y₂ hy k ⊤ h₁ h₂
    rcases hu with rfl | rfl
    · exact congrArg Units.val H
    · have H' := congrArg (fun x => x⁻¹) H
      simp only [← map_inv] at H'
      exact congrArg Units.val H'
  choose f hf using fun k => hval k (e k) (Or.inl rfl)
  choose f' hf' using fun k => hval k (e k)⁻¹ (Or.inr rfl)
  have inj := fun V => app_injective_of_flat_surj p V
  have hmul : ∀ k, f k * f' k = 1 := fun k =>
    inj _ (by rw [map_mul, map_one, hf, hf', Units.mul_inv])
  let fu : ∀ k, Γ(Y, M.U k)ˣ := fun k => ⟨f k, f' k, hmul k, by rw [mul_comm]; exact hmul k⟩
  refine ⟨⟨fu⟩, fun i j => Units.ext (inj _ ?_)⟩
  have H := congrArg Units.val
    (he i j (p ⁻¹ᵁ (M.U i ⊓ M.U j)) (fun _ hx => hx.1) (fun _ hx => hx.2) le_rfl)
  have eX : ∀ {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ),
      ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = X.presheaf.map (homOfLE h).op a := fun _ _ => rfl
  have eY : ∀ {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)ˣ),
      ((res h a : Γ(Y, V)ˣ) : Γ(Y, V)) = Y.presheaf.map (homOfLE h).op a := fun _ _ => rfl
  have eP : ((pullU p (M.U i ⊓ M.U j) (M.g i j) : Γ(X, p ⁻¹ᵁ (M.U i ⊓ M.U j))ˣ) : Γ(X, p ⁻¹ᵁ (M.U i ⊓ M.U j))) =
      p.app _ (M.g i j) := rfl
  have eid : X.presheaf.map (homOfLE (le_rfl : p ⁻¹ᵁ (M.U i ⊓ M.U j) ≤ p ⁻¹ᵁ (M.U i ⊓ M.U j))).op =
      𝟙 _ := by
    rw [show homOfLE (le_rfl : p ⁻¹ᵁ (M.U i ⊓ M.U j) ≤ _) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  simp only [Units.val_mul, eX, eP] at H
  rw [eid, CommRingCat.id_apply] at H
  simp only [Units.val_mul, map_mul, eY, app_map_homOfLE]
  show X.presheaf.map _ (p.app _ (f i)) = _ * X.presheaf.map _ (p.app _ (f j))
  rw [hf, hf]
  exact H

end GlobalTheory.CharKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfInvariantPullbackGeneratorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_trivial_of_invariant_pullback_generator : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y), Flat p → Surjective p → IsAffineHom p → ∀ (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → (∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (k : M.ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)), res h₁ (pullU y₁ _ (e k)) = res h₂ (pullU y₂ _ (e k))) → Triv M := by
  first | exact @GlobalTheory.CharKer.triv_of_isPullGen_of_invariant | exact GlobalTheory.CharKer.triv_of_isPullGen_of_invariant | (intros; apply GlobalTheory.CharKer.triv_of_isPullGen_of_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackLineBundleGeneratorAdditivityDefect
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackLineBundleGeneratorAdditivityDefect
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem gm_of_isPullGen {X Y Z : Scheme.{0}} {p : X ⟶ Y} {M : LB Y} {e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ}
    (he : IsPullGen p M e) (ψ : Z ⟶ X) (z : Z) (k l : M.ι) (hk : p (ψ z) ∈ M.U k) (hl : p (ψ z) ∈ M.U l) :
    gm ψ z (p ⁻¹ᵁ M.U k) (e k) = gm (ψ ≫ p) z (M.U k ⊓ M.U l) (M.g k l) * gm ψ z (p ⁻¹ᵁ M.U l) (e l) := by
  have hm : ψ z ∈ p ⁻¹ᵁ (M.U k ⊓ M.U l) := ⟨hk, hl⟩
  have h := congrArg (gm ψ z (p ⁻¹ᵁ (M.U k ⊓ M.U l)))
    (he k l (p ⁻¹ᵁ (M.U k ⊓ M.U l)) (fun _ hy => hy.1) (fun _ hy => hy.2) le_rfl)
  exact (gm_res _ _ _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ((gm_res _ _ _ hm _).trans (gm_pull ψ p z _ hm _)) (gm_res _ _ _ hm _))))

theorem gm_pull_of_isPullGen {X Y X₂ Y₂ : Scheme.{0}} {p : X ⟶ Y} {M : LB Y} {e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ}
    (he : IsPullGen p M e) {P : X₂ ⟶ Y₂} {φ : Y₂ ⟶ Y} {ψ : X₂ ⟶ X} (h : P ≫ φ = ψ ≫ p) (x : X₂)
    (J J' : PUnit → M.ι) (hJ : P x ∈ (M.pull φ).U J) (hJ' : P x ∈ (M.pull φ).U J') :
    gm ψ x (p ⁻¹ᵁ M.U (J PUnit.unit)) (e (J PUnit.unit)) =
      gm P x ((M.pull φ).U J ⊓ (M.pull φ).U J') ((M.pull φ).g J J') *
        gm ψ x (p ⁻¹ᵁ M.U (J' PUnit.unit)) (e (J' PUnit.unit)) := by
  rw [gm_pull_g M φ P x J J' hJ hJ', h]
  exact gm_of_isPullGen he ψ x _ _ (preimage_le_of_comp h _ (mem_pull.1 hJ)) (preimage_le_of_comp h _ (mem_pull.1 hJ'))

theorem gm_res_pullU {X Z : Scheme.{0}} (ψ : Z ⟶ X) (z : Z) (U : X.Opens) {V : Z.Opens} (hle : V ≤ ψ ⁻¹ᵁ U)
    (hz : z ∈ V) (a : Γ(X, U)ˣ) : gm (𝟙 Z) z V (res hle (pullU ψ U a)) = gm ψ z U a :=
  (gm_res (𝟙 Z) z hle hz _).trans ((gm_pull (𝟙 Z) ψ z U (hle hz) a).trans (by rw [Category.id_comp]))

theorem germ_addGen_pullGen {S : Scheme.{0}} {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q]
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (k : (addBundle M).ι)
    (x : (A ⊗ (A ⊗ T)).left) (hx : x ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k) :
    gm (𝟙 _) x _ (addGen q M e k) =
      gm (ptFst A T).left x _ (e (k.1.1 PUnit.unit)) * gm (ptSnd A T).left x _ (e (k.1.2 PUnit.unit)) *
        (gm (ptMul A T).left x _ (e (k.2 PUnit.unit)))⁻¹ := by
  rw [addGen, map_mul, map_mul, map_inv, gm_res_pullU _ _ _ _ hx, gm_res_pullU _ _ _ _ hx, gm_res_pullU _ _ _ _ hx]

theorem isPullGen_addGen : ∀ (S : Scheme.{0}) (A A' T : Over S) [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsPullGen (pmap q T).left M e → IsPullGen (pmap2 q T).left (addBundle M) (addGen q M e) := by
  intro S A A' T _ _ q _ M e he k l W h₁ h₂ h₃
  refine unit_ext fun x hx => ?_
  have hk := h₁ hx
  have hl := h₂ hx
  have e₁ := gm_pull_of_isPullGen he (prodMapPairTimesIdentity_fst q T) x k.1.1 l.1.1 hk.1.1 hl.1.1
  have e₂ := gm_pull_of_isPullGen he (prodMapPairTimesIdentity_snd q T) x k.1.2 l.1.2 hk.1.2 hl.1.2
  have e₃ := gm_pull_of_isPullGen he (prodMapPairTimesIdentity_mul q T) x k.2 l.2 hk.2 hl.2
  have g := (gm_div _ _ (pmap2 q T).left x k l ⟨hk, hl⟩).trans
    (congrArg (· * _) (gm_tens _ _ (pmap2 q T).left x k.1 l.1 hk.1 hl.1))
  refine ((gm_res (𝟙 _) x h₁ hx _).trans (germ_addGen_pullGen q M e k x hk)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res_pullU _ x _ h₃ hx _).trans g)
    ((gm_res (𝟙 _) x h₂ hx _).trans (germ_addGen_pullGen q M e l x hl)))).trans ?_
  rw [e₁, e₂, e₃, mul_inv]
  have alg : ∀ {G : Type} [CommGroup G] (a b c u v w : G),
      a * b * c⁻¹ * (u * v * w⁻¹) = a * u * (b * v) * (c⁻¹ * w⁻¹) := by
    intro G _ a b c u v w
    ac_rfl
  exact alg _ _ _ _ _ _

end GlobalTheory.CharKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackLineBundleGeneratorAdditivityDefectStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullbackLineBundleGenerator_additivityDefect : ∀ (S : Scheme.{0}) (A A' T : Over S) [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsPullGen (pmap q T).left M e → IsPullGen (pmap2 q T).left (addBundle M) (addGen q M e) := by
  first | exact @GlobalTheory.CharKer.isPullGen_addGen | exact GlobalTheory.CharKer.isPullGen_addGen | (intros; apply GlobalTheory.CharKer.isPullGen_addGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentityFlatSurjectiveAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentityFlatSurjectiveAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer.PmapTwo

variable {S : Scheme.{0}}

theorem isPullback_whiskerLeft_left (W : Over S) {G B : Over S} (p : G ⟶ B) :
    IsPullback (W ◁ p).left (snd W G).left (snd W B).left p.left := by
  have h1 : IsPullback (fst W B).left (snd W B).left W.hom B.hom := IsPullback.of_hasPullback W.hom B.hom
  have h2 : IsPullback (fst W G).left (snd W G).left W.hom G.hom := IsPullback.of_hasPullback W.hom G.hom
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerLeft_fst, Over.w p]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

theorem isPullback_whiskerRight_left {G B : Over S} (p : G ⟶ B) (W : Over S) :
    IsPullback (p ▷ W).left (fst G W).left (fst B W).left p.left := by
  have h1 : IsPullback (snd B W).left (fst B W).left W.hom B.hom :=
    (IsPullback.of_hasPullback B.hom W.hom).flip
  have h2 : IsPullback (snd G W).left (fst G W).left W.hom G.hom := (IsPullback.of_hasPullback G.hom W.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w p]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem prodMapPairTimesIdentity_eq_comp_whiskers {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    pmap2 q T = (q ▷ (A ⊗ T)) ≫ (A' ◁ (q ▷ T)) := by
  ext <;> simp [pmap2, pmap]

end GlobalTheory.CharKer.PmapTwo


open GlobalTheory.CharKer.PmapTwo in
theorem GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom :
    ∀ (S : Scheme.{0}) (A A' T : Over S) (q : A ⟶ A'), Flat q.left → Surjective q.left → IsAffineHom q.left →
      Flat (pmap2 q T).left ∧ Surjective (pmap2 q T).left ∧ IsAffineHom (pmap2 q T).left := by
  intro S A A' T q h1 h2 h3
  have hR := (isPullback_whiskerRight_left q (A ⊗ T)).flip
  have hL := (isPullback_whiskerLeft_left A' (q ▷ T)).flip
  have hR' := (isPullback_whiskerRight_left q T).flip
  have a1 : Flat (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h1
  have a2 : Surjective (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h2
  have a3 : IsAffineHom (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h3
  have b1 : Flat (q ▷ T).left := MorphismProperty.of_isPullback hR' h1
  have b2 : Surjective (q ▷ T).left := MorphismProperty.of_isPullback hR' h2
  have b3 : IsAffineHom (q ▷ T).left := MorphismProperty.of_isPullback hR' h3
  have c1 : Flat (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b1
  have c2 : Surjective (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b2
  have c3 : IsAffineHom (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b3
  rw [prodMapPairTimesIdentity_eq_comp_whiskers, Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentityFlatSurjectiveAffineStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodMapPairTimesIdentity_flat_surjective_affine : ∀ (S : Scheme.{0}) (A A' T : Over S) (q : A ⟶ A'), Flat q.left → Surjective q.left → IsAffineHom q.left → Flat (pmap2 q T).left ∧ Surjective (pmap2 q T).left ∧ IsAffineHom (pmap2 q T).left := by
  first | exact @GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom | exact GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom | (intros; apply GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLineBundleAdditiveOfEquivariantGenerato
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem isAdditive_of_isEquivGen : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → M.IsLB → IsEquivGen i q χ M e → IsAdditive M := by
  intro K _ _ A A' N T _ _ _ i q χ M e hA hA' hi hq hfin hflat hsurj hker hχ hM he
  haveI := hA
  haveI := hq
  haveI : IsCommMonObj A := IsAbelianScheme.comm
  obtain ⟨h₁, h₂, h₃⟩ := GlobalTheory.T.prodMapPairTimesIdentity_flat_surjective_affine _ A A' T q hflat hsurj inferInstance
  exact isAdditive_of_universal hM (GlobalTheory.T.lineBundle_trivial_of_invariant_pullback_generator _ _ (pmap2 q T).left h₁ h₂ h₃ (addBundle M) (addGen q M e)
    (GlobalTheory.T.isPullbackLineBundleGenerator_additivityDefect _ A A' T q M e he.1) (GlobalTheory.T.additivityDefect_generator_invariant_same_image _ A A' N T i q χ M e hi hker hχ he))

end GlobalTheory.CharKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLineBundleAdditiveOfEquivariantGeneratoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterLineBundle_additive_of_equivariantGenerator : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → M.IsLB → IsEquivGen i q χ M e → IsAdditive M := by
  first | exact @GlobalTheory.CharKer.isAdditive_of_isEquivGen | exact GlobalTheory.CharKer.isAdditive_of_isEquivGen | (intros; apply GlobalTheory.CharKer.isAdditive_of_isEquivGen <;> assumption)
end
