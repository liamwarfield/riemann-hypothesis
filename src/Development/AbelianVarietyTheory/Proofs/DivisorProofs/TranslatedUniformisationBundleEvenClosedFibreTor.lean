module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedCubicalBundleClosedFibreUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedCubicalBundleClosedFibreUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TranslateLevel
open GlobalTheory.UU

section Iso
variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {τ : X ⟶ X} {τ' : X' ⟶ X'}

theorem exists_translate (h : τ' ≫ F = F ≫ τ) (w₁ : LB.Iso L' (L.pull F)) (hw₁ : w₁.IsGen) :
    ∃ w : LB.Iso (L'.pull τ') ((L.pull τ).pull F), w.IsGen ∧
      ∀ (Y : Scheme.{0}) (r : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), τ (F (r y)) ∈ L.U j → τ' (r y) ∈ L'.U k →
        gw w r y (fun _ => j) (fun _ => k) = gw w₁ (r ≫ τ') y j k := by
  have e : ∀ x : X', F (τ' x) = τ (F x) := fun x => congrArg (fun g => g x) h
  have le : ∀ (j : L.ι) (k : L'.ι), ((L.pull τ).pull F).U (fun _ _ => j) ⊓ (L'.pull τ').U (fun _ => k) ≤
      τ' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k) := fun j k x hx =>
    ⟨mem_pull.2 (by rw [e]; exact mem_pull.1 (mem_pull.1 hx.1)), mem_pull.1 hx.2⟩
  let w : LB.Iso (L'.pull τ') ((L.pull τ).pull F) :=
    ⟨fun p => res (le (p.1 PUnit.unit PUnit.unit) (p.2 PUnit.unit))
      (pullU τ' _ (w₁.s (fun _ => p.1 PUnit.unit PUnit.unit, p.2 PUnit.unit)))⟩
  have key : ∀ (Y : Scheme.{0}) (r : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), τ (F (r y)) ∈ L.U j → τ' (r y) ∈ L'.U k →
      gw w r y (fun _ => j) (fun _ => k) = gw w₁ (r ≫ τ') y j k := fun Y r y j k hj hk => by
    have hm : r y ∈ ((L.pull τ).pull F).U (fun _ _ => j) ⊓ (L'.pull τ').U (fun _ => k) :=
      ⟨mem_pull.2 (mem_pull.2 hj), mem_pull.2 hk⟩
    exact (gm_res r y (le j k) hm _).trans (gm_pull r τ' y _ (@le j k (r y) hm) _)
  refine ⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_, key⟩
  have a := (isGen_iff w₁).1 hw₁ Y (r ≫ τ') y (j PUnit.unit) (j' PUnit.unit) (k PUnit.unit) (k' PUnit.unit)
    (by show F (τ' (r y)) ∈ _; rw [e]; exact mem_pull.1 hj) (by show F (τ' (r y)) ∈ _; rw [e]; exact mem_pull.1 hj')
    ((mem_pull (F := τ')).1 hk) ((mem_pull (F := τ')).1 hk')
  rw [Category.assoc, h, ← Category.assoc] at a
  refine (key Y r y _ _ (mem_pull.1 hj) (mem_pull.1 hk)).trans (a.trans ?_)
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pull_g L τ (r ≫ F) y j j' hj hj').symm
    (congrArg (·⁻¹) (gm_pull_g L' τ' r y k k' hk hk').symm))
    (key Y r y _ _ (mem_pull.1 hj') (mem_pull.1 hk')).symm

end Iso

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']


omit [IsCommMonObj G] in
theorem left_translate (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (x : T ⟶ G) :
    x.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * x).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]


set_option maxHeartbeats 1000000 in
theorem exists_translate_pull {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
    (Q P : CP G) (P₁ : CP G') (a : 𝟙_ (Over S) ⟶ G) (a' : 𝟙_ (Over S') ⟶ G') (ha : a'.left ≫ F = f ≫ a.left)
    (h2 : a' ^ 2 = 1) (hP : P.L.L = Q.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left)
    (hs : ∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → Q.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good Q.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val Q.sym ((toUnit T ≫ a) * x).left z J * (val Q.sym (toUnit T ≫ a).left z J)⁻¹)
    (hc : ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → Q.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good Q.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV Q.c z J x y ((toUnit T ≫ a) * u) * (cubV Q.c z J x y (toUnit T ≫ a))⁻¹)
    {w₁ : LB.Iso P₁.L.L (Q.L.L.pull F)} (h₁ : IsCPMap P₁ Q f F hw w₁) :
    ∃ P₀ : CP G', (∃ w, IsCPMap P₀ P f F hw w) ∧ P₀.L.L = P₁.L.L.pull ((toUnit G' ≫ a') * 𝟙 G').left ∧
      (∀ (T : Over S') (x : T ⟶ G') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G'.left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a') * x).left z J * (val P₁.sym (toUnit T ≫ a').left z J)⁻¹) ∧
      (∀ (T : Over S') (x y u : T ⟶ G') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G'.left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a') * u) * (cubV P₁.c z J x y (toUnit T ≫ a'))⁻¹) := by
  obtain ⟨⟨L, rg, hL, hrg⟩, c, sy, g₁, g₂, g₃⟩ := P
  dsimp only at hP hs hc
  subst hP
  have hβ : ∀ T : Over S', toBase hw (toUnit T ≫ a') = toUnit (Over.mk (T.hom ≫ f)) ≫ a := fun T =>
    Over.OverMorphism.ext (by
      show ((toUnit T).left ≫ a'.left) ≫ F = (toUnit (Over.mk (T.hom ≫ f))).left ≫ a.left
      rw [Rosenlicht.toUnit_left, Rosenlicht.toUnit_left, Category.assoc, ha, ← Category.assoc]; rfl)
  have hpt : ∀ {T : Over S'} (x : T ⟶ G'), (x.left ≫ F) ≫ ((toUnit G ≫ a) * 𝟙 G).left =
      ((toUnit T ≫ a') * x).left ≫ F := fun {T} x => by
    refine (left_translate a (toBase hw x)).trans ?_
    rw [← hβ, ← h₁.mul]; rfl
  have hτ : ((toUnit G' ≫ a') * 𝟙 G').left ≫ F = F ≫ ((toUnit G ≫ a) * 𝟙 G).left :=
    (hpt (𝟙 G')).symm.trans (congrArg (· ≫ _) (Category.id_comp F))
  obtain ⟨w, hg, hv⟩ := exists_translate hτ w₁ h₁.gen
  obtain ⟨rig, hr, c₀, s₀, k₁, k₂, k₃, H⟩ := exists_isCPMap (hw := hw) ⟨⟨_, rg, hL, hrg⟩, c, sy, g₁, g₂, g₃⟩ h₁.mul _
    (pull_isLB P₁.L.isLB _) w hg
  have main : ∀ (T : Over S') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι), Good P₁.L.L z J →
      (∀ x : T ⟶ G', val s₀ x.left z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) =
          val P₁.sym ((toUnit T ≫ a') * x).left z J * (val P₁.sym (toUnit T ≫ a').left z J)⁻¹) ∧
      ∀ x y u : T ⟶ G', cubV c₀ z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) x y u =
        cubV P₁.c z J x y ((toUnit T ≫ a') * u) * (cubV P₁.c z J x y (toUnit T ≫ a'))⁻¹ := by
    intro T z J hJ
    obtain ⟨I, hI⟩ := exists_good_pt Q.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w₁ x.left z (I (x.left ≫ F)) (J x.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨-, a₂, a₃⟩ := h₁.vals T z J I hJ hI W hW
    obtain ⟨b, hb⟩ : ∃ b, b = toUnit T ≫ a' := ⟨_, rfl⟩
    have hbb : b⁻¹ = b := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← sq, hb, ← MonObj.comp_pow, h2, MonObj.comp_one]
    obtain ⟨-, b₂, b₃⟩ := H.vals T z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))
      (fun r _ => I (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (fun r => mem_pull.2 (hJ (r ≫ _)))
      (fun r => mem_pull.2 (hI (r ≫ _))) (fun x => W (b * x)) (fun x => by
        refine Eq.trans ?_ (hv _ x.left z _ _ (hI ((x.left ≫ F) ≫ _)) (hJ (x.left ≫ _))).symm
        rw [hW, hpt, left_translate, hb])
    rw [← hb]
    refine ⟨fun x => ?_, fun x y u => ?_⟩
    · have e₀ := hs (Over.mk (T.hom ≫ f)) (toBase hw x) z I _ hI (fun _ => HEq.rfl)
      rw [← hβ, ← h₁.mul, ← hb] at e₀
      have e₁ : val Q.sym ((b * x).left ≫ F) z I * (val Q.sym (b.left ≫ F) z I)⁻¹ * W (b * x) =
          W (b * x⁻¹) * val s₀ x.left z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) :=
        (congrArg (· * W (b * x)) e₀).symm.trans (b₂ x)
      have e₂ := a₂ (b * x)
      have e₃ := a₂ b
      rw [mul_inv, hbb] at e₂
      rw [hbb] at e₃
      apply Additive.ofMul.injective
      have f₁ := congrArg Additive.ofMul e₁
      have f₂ := congrArg Additive.ofMul e₂
      have f₃ := congrArg Additive.ofMul e₃
      simp only [ofMul_mul, ofMul_inv] at f₁ f₂ f₃ ⊢
      linear_combination (norm := abel) f₂ - f₁ - f₃
    · have e₀ := hc (Over.mk (T.hom ≫ f)) (toBase hw x) (toBase hw y) (toBase hw u) z I _ hI (fun _ => HEq.rfl)
      rw [← hβ, ← h₁.mul, ← hb] at e₀
      obtain ⟨C, hC⟩ : ∃ C : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, ∀ v, C v =
        cubV Q.c (T := Over.mk (T.hom ≫ f)) z I (toBase hw x) (toBase hw y) (toBase hw v) := ⟨_, fun _ => rfl⟩
      have e₁ : C (b * u) * (C b)⁻¹ * W (b * (x * y)) * W (b * (x * u)) * W (b * (y * u)) * W (b * 1) =
          W (b * (x * y * u)) * W (b * x) * W (b * y) * W (b * u) *
            cubV c₀ z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) x y u := by
        rw [hC, hC]
        exact (congrArg (· * W (b * (x * y)) * W (b * (x * u)) * W (b * (y * u)) * W (b * 1)) e₀).symm.trans (b₃ x y u)
      have e₂ : ∀ v, C v * W (x * y) * W (x * v) * W (y * v) * W 1 =
          W (x * y * v) * W x * W y * W v * cubV P₁.c z J x y v := fun v => by rw [hC]; exact a₃ x y v
      have e₃ := e₂ (b * u)
      have e₄ := e₂ b
      rw [mul_left_comm x b, mul_left_comm y b, mul_left_comm (x * y) b] at e₃
      rw [mul_comm x b, mul_comm y b, mul_comm (x * y) b] at e₄
      rw [_root_.mul_one] at e₁
      apply Additive.ofMul.injective
      have f₁ := congrArg Additive.ofMul e₁
      have f₂ := congrArg Additive.ofMul e₃
      have f₃ := congrArg Additive.ofMul e₄
      simp only [ofMul_mul, ofMul_inv] at f₁ f₂ f₃ ⊢
      linear_combination (norm := abel) f₂ - f₁ - f₃
  refine ⟨⟨⟨_, rig, _, hr⟩, c₀, s₀, k₁, k₂, k₃⟩, ⟨w, H⟩, rfl, fun T x z J J' hJ h => ?_, fun T x y u z J J' hJ h => ?_⟩
  · obtain rfl : J' = fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left) := funext fun r => eq_of_heq (h r)
    exact (main T z J hJ).1 x
  · obtain rfl : J' = fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left) := funext fun r => eq_of_heq (h r)
    exact (main T z J hJ).2 x y u

theorem exists_section_pullback (f : S' ⟶ S) (a : 𝟙_ (Over S) ⟶ G) (h2 : a ^ 2 = 1) :
    ∃ a' : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G, a'.left ≫ pullback.fst G.hom f = f ≫ a.left ∧ a' ^ 2 = 1 := by
  have h0 : (f ≫ a.left) ≫ G.hom = 𝟙 S' ≫ f := by
    rw [Category.assoc, Over.w a]; simp
  let a' : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G :=
    Over.homMk (pullback.lift (f ≫ a.left) (𝟙 S') h0) (pullback.lift_snd _ _ _)
  have ha : a'.left ≫ pullback.fst G.hom f = f ≫ a.left := pullback.lift_fst _ _ _
  refine ⟨a', ha, ?_⟩
  let β := toBaseHom (toBase_mul_pullback G f) (𝟙_ (Over S'))
  have e : β a' = toUnit _ ≫ a := Over.OverMorphism.ext (by
    refine ha.trans ?_
    rw [Over.comp_left, Rosenlicht.toUnit_left]
    exact congrArg (· ≫ a.left) (Category.id_comp f).symm)
  have e' : β (a' ^ 2) = β 1 := by rw [map_pow, map_one, e, ← MonObj.comp_pow, h2, MonObj.comp_one]
  exact Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e')
    ((Over.w (a' ^ 2)).trans (Over.w (1 : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G)).symm))

theorem exists_level_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G), a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
    ∀ P₁ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G),
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₁ (GlobalTheory.ValueForm.modelCP U.toUnifPre GlobalTheory.firstFiveLaws.1.globalFns) →
    ∃ (a₀ : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) ⟶ thickObj R (maximalIdeal R) 0 G)
      (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)),
      a₀.left ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) = thick R (maximalIdeal R) 0 ≫ a.left ∧ a₀ ^ 2 = 1 ∧
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P ∧
      P₀.L.L = P₁.L.L.pull ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a₀) * x).left z J * (val P₁.sym (toUnit T ≫ a₀).left z J)⁻¹) ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x y u : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a₀) * u) * (cubV P₁.c z J x y (toUnit T ≫ a₀))⁻¹) := by
  intro R _ _ _ D A G _ _ U a h2 P hP hs hc P₁ h₁
  obtain ⟨w₁, h₁⟩ := h₁
  obtain ⟨a₀, ha, h₀⟩ := exists_section_pullback (thick R (maximalIdeal R) 0) a h2
  obtain ⟨P₀, k⟩ := exists_translate_pull _ P P₁ a a₀ ha h₀ hP hs hc h₁
  exact ⟨a₀, P₀, ha, h₀, k⟩

end GlobalTheory.Mum.TranslateLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedCubicalBundleClosedFibreUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedCubicalBundle_closedFibre_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G), a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
    ∀ P₁ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G),
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₁ (GlobalTheory.ValueForm.modelCP U.toUnifPre GlobalTheory.firstFiveLaws.1.globalFns) →
    ∃ (a₀ : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) ⟶ thickObj R (maximalIdeal R) 0 G)
      (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)),
      a₀.left ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) = thick R (maximalIdeal R) 0 ≫ a.left ∧ a₀ ^ 2 = 1 ∧
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P ∧
      P₀.L.L = P₁.L.L.pull ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a₀) * x).left z J * (val P₁.sym (toUnit T ≫ a₀).left z J)⁻¹) ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x y u : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a₀) * u) * (cubV P₁.c z J x y (toUnit T ≫ a₀))⁻¹) := by
  first | exact @GlobalTheory.Mum.TranslateLevel.exists_level_translate | exact GlobalTheory.Mum.TranslateLevel.exists_level_translate | (intros; apply GlobalTheory.Mum.TranslateLevel.exists_level_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivTranslateOrderTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivTranslateOrderTwo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.TranslateEvenTriv
open GlobalTheory.UU

theorem exists_gen_pull {X X' Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X' ⟶ X} {L' : LB X'} (e : L' = L.pull F)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε))
    (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J →
        (∀ q, HEq (J' q) (fun _ : PUnit.{1} => J (q ≫ F))) → val a r z J' = val t r z J := by
  subst e
  have h := pull_isLB hL F
  have hc : ∀ k, φ k ≫ F = 𝟙 Y ≫ (fun k => φ k ≫ F) k := fun k => (Category.id_comp _).symm
  obtain ⟨a, ha, Ha⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 (pullIso_isGen hL F)) hL h (𝟙 Y) hc t ht
  refine ⟨a, ha, fun Z r z J J' hJ hJ' => ?_⟩
  obtain rfl : J' = fun q _ => J (q ≫ F) := funext fun q => eq_of_heq (hJ' q)
  have hg : Good (L.pull F) z (fun q _ => J (q ≫ F)) := fun q => mem_pull.2 (hJ (q ≫ F))
  have := CubTransport.val_pmaps hc Ha r hJ hg
  rw [Category.comp_id, Finset.prod_eq_one, _root_.one_mul] at this
  · exact this.symm
  · intro k _
    have : gw (pullIso L F) (r ≫ φ k) z (J ((r ≫ φ k) ≫ F)) (fun _ => J ((r ≫ φ k) ≫ F)) = 1 :=
      gm_self h (r ≫ φ k) z (hg (r ≫ φ k))
    rw [this, one_zpow]

theorem exists_good_of_pull {X Z : Scheme.{0}} {L L' : LB X} {F : X ⟶ X} (hF : F ≫ F = 𝟙 X) (e : L' = L.pull F)
    {z : Z} {J' : (Z ⟶ X) → L'.ι} (hJ' : Good L' z J') :
    ∃ J : (Z ⟶ X) → L.ι, Good L z J ∧ ∀ q, HEq (J' q) (fun _ : PUnit.{1} => J (q ≫ F)) := by
  subst e
  refine ⟨fun q => J' (q ≫ F) PUnit.unit, fun q => ?_, fun q => heq_of_eq ?_⟩
  · have : ((q ≫ F) ≫ F) z ∈ L.U (J' (q ≫ F) PUnit.unit) := (mem_pull (F := F)).1 (hJ' (q ≫ F))
    rwa [Category.assoc, hF, Category.comp_id] at this
  · show J' q = J' ((q ≫ F) ≫ F)
    rw [Category.assoc, hF, Category.comp_id]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]


omit [IsCommMonObj G] in
theorem comp_translate (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (g : T ⟶ G) :
    g ≫ ((toUnit G ≫ a) * 𝟙 G) = (toUnit T ≫ a) * g := by
  rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]

variable {X : Type} [AddCommGroup X] (Q : TQ G X)


omit [IsCommMonObj G] in
theorem mul_torus_comp {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X) : (g * (x ≫ Q.i)) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  have e : Q.i ≫ Q.q = 1 := Q.isKernel.w
  rw [MonObj.mul_comp, Category.assoc, e, MonObj.comp_one, _root_.mul_one]

theorem exists_gen_torus {P₁ : CP G} (D : Q.Desc P₁) (a : 𝟙_ (Over S) ⟶ G) :
    ∃ s : LB.Gen (LB.LinComb P₁.L.L (K := Fin 2) (fun k => ![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫
      ((toUnit G ≫ a) * 𝟙 G).left) ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (N) (J), Good D.M.L.L z N → Good P₁.L.L z J →
        ∀ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
          (∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left)) →
          val s x.left z J = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (x ≫ Q.i)))⁻¹ := by
  obtain ⟨t, ht, v⟩ := exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left)))
    (ε := PEmpty.elim) (K' := Fin 2) (φ' := fun _ => ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left)
    (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have hc : ∀ k : Fin 2, (![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left =
      𝟙 _ ≫ ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left := fun k => by
    rw [Category.id_comp]
    fin_cases k
    · refine congrArg (fun q => q.left) (show (Q.i ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)
      have := mul_torus_comp Q (toUnit (splitTorus S X) ≫ a) (𝟙 _)
      rw [Category.id_comp] at this
      rw [comp_translate, this]
    · refine congrArg (fun q => q.left) (show ((1 : splitTorus S X ⟶ G) ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)
      rw [comp_translate, _root_.mul_one]
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 D.map.gen) D.M.L.isLB P₁.L.isLB (𝟙 _) hc t ht
  refine ⟨s, hs, fun T x z N J hN hJ W hW => ?_⟩
  have e := CubTransport.val_pmaps hc Hs x.left hN hJ
  rw [v _ _ z N hN, val_one] at e
  have hτ : ∀ g : T ⟶ G, g.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * g).left := fun g =>
    congrArg (fun q => q.left) (comp_translate a g)
  have e₂ := CubTrivTorus.prod_cubTriv Q.i x (fun q => gw D.w (q ≫ ((toUnit G ≫ a) * 𝟙 G).left) z
    (N ((q ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left)) (J (q ≫ ((toUnit G ≫ a) * 𝟙 G).left)))
  rw [hτ, hτ, _root_.mul_one, ← hW, ← hW] at e₂
  simp only [← Category.assoc x.left] at e
  have e₃ := e.trans (congrArg₂ (· * ·) e₂ rfl)
  apply Additive.ofMul.injective
  have e₄ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₄ ⊢
  linear_combination (norm := abel) -e₄

theorem exists_even_cubTriv : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X]
    (Q : GlobalTheory.UU.TQ G X) (P₁ : GlobalTheory.UU.CP G), Nonempty (Q.Desc P₁) → ∀ a : 𝟙_ (Over S) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = P₁.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
    (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a) * x).left z J * (val P₁.sym (toUnit T ≫ a).left z J)⁻¹) →
    (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a) * u) * (cubV P₁.c z J x y (toUnit T ≫ a))⁻¹) →
    ∃ σ : GlobalTheory.UU.CubTriv P.c Q.i, σ.Even := by
  rintro S G _ _ X _ Q P₁ ⟨D⟩ a ha P hP hsym hcub
  have := Q.i_hom
  have hinv : ∀ T : Over S, (toUnit T ≫ a)⁻¹ = toUnit T ≫ a := fun T => by
    rw [inv_eq_iff_mul_eq_one, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one]
  have hF : ((toUnit G ≫ a) * 𝟙 G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left = 𝟙 G.left := by
    refine congrArg (fun q => q.left) (show ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G from ?_)
    rw [comp_translate, ← _root_.mul_assoc, (inv_eq_iff_mul_eq_one.1 (hinv G)), _root_.one_mul]
  obtain ⟨s, hs, vs⟩ := exists_gen_torus Q D a
  obtain ⟨σ, hσ, vσ⟩ := exists_gen_pull P₁.L.isLB hP _ _ s hs
  have hq : ∀ {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X), (g * (x ≫ Q.i)).left ≫ Q.q.left = g.left ≫ Q.q.left :=
    fun g x => congrArg (fun q => q.left) (mul_torus_comp Q g x)
  refine ⟨⟨σ, hσ, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
  all_goals
    obtain ⟨J, hJ, hJJ⟩ := exists_good_of_pull hF hP hJ'
    obtain ⟨N, hN⟩ := exists_good_pt D.M.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
      ∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left) := ⟨_, fun _ => rfl⟩
    have v : ∀ t : T ⟶ splitTorus S X, val σ t.left z J' = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (t ≫ Q.i)))⁻¹ :=
      fun t => (vσ _ t.left z J J' hJ hJJ).trans (vs T t z N J hN hJ W hW)
    obtain ⟨-, a₂, a₃⟩ := D.map.vals T z J N hJ hN W hW
  · have b₁ := a₃ (x ≫ Q.i) (y ≫ Q.i) ((toUnit T ≫ a) * (u ≫ Q.i))
    have b₂ := a₃ (x ≫ Q.i) (y ≫ Q.i) (toUnit T ≫ a)
    have e : toBase (f := 𝟙 S) (g := Q.q.left) (by simp) ((toUnit T ≫ a) * (u ≫ Q.i)) =
        toBase (f := 𝟙 S) (g := Q.q.left) (by simp) (toUnit T ≫ a) := Over.OverMorphism.ext (hq _ u)
    rw [e] at b₁
    rw [hcub T _ _ _ z J J' hJ hJJ]
    simp only [v, MonObj.mul_comp]
    generalize x ≫ Q.i = x' at *
    generalize y ≫ Q.i = y' at *
    generalize u ≫ Q.i = u' at *
    generalize toUnit T ≫ a = A at *
    rw [mul_left_comm x' A, mul_left_comm y' A, mul_left_comm (x' * y') A] at b₁
    rw [mul_comm x' A, mul_comm y' A, mul_comm (x' * y') A] at b₂
    apply Additive.ofMul.injective
    have c₁ := congrArg Additive.ofMul b₁
    have c₂ := congrArg Additive.ofMul b₂
    simp only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢
    linear_combination (norm := abel) c₁ - c₂
  · have b₁ := a₂ ((toUnit T ≫ a) * (x ≫ Q.i))
    have b₂ := a₂ (toUnit T ≫ a)
    rw [hq, mul_inv, hinv] at b₁
    rw [hinv] at b₂
    show val σ _ z J' = _ * val σ _ z J'
    rw [hsym T _ z J J' hJ hJJ, v, v, GrpObj.inv_comp]
    apply Additive.ofMul.injective
    have c₁ := congrArg Additive.ofMul b₁
    have c₂ := congrArg Additive.ofMul b₂
    simp only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢
    linear_combination (norm := abel) c₁ - c₂

end GlobalTheory.TranslateEvenTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivTranslateOrderTwoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubicalTriv_translate_order_two : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X]
    (Q : GlobalTheory.UU.TQ G X) (P₁ : GlobalTheory.UU.CP G), Nonempty (Q.Desc P₁) → ∀ a : 𝟙_ (Over S) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = P₁.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
    (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a) * x).left z J * (val P₁.sym (toUnit T ≫ a).left z J)⁻¹) →
    (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a) * u) * (cubV P₁.c z J x y (toUnit T ≫ a))⁻¹) →
    ∃ σ : GlobalTheory.UU.CubTriv P.c Q.i, σ.Even := by
  first | exact @GlobalTheory.TranslateEvenTriv.exists_even_cubTriv | exact GlobalTheory.TranslateEvenTriv.exists_even_cubTriv | (intros; apply GlobalTheory.TranslateEvenTriv.exists_even_cubTriv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedUniformisationBundleEvenClosedFibreTor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TransEven
open GlobalTheory.UU


set_option maxHeartbeats 1000000 in
theorem evenOn_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
      EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U a ha P hP hsym hcub
  have hG := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨wA, hwA⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre hG hS wA hwA
  set g := U.gt 0 with hg
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  have := hB.comm
  obtain ⟨O, h₁, h₂, h₃, hd⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ D.toPre.X (thickObj R (maximalIdeal R) 0 G)
    (thickObj R (maximalIdeal R) 0 D.toPre.P.A) hB g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj inferInstance g.isKernel
  obtain ⟨d, hdq, hdi⟩ := hd hB
  let Q : TQ (thickObj R (maximalIdeal R) 0 G) D.toPre.X :=
    { B := thickObj R (maximalIdeal R) 0 D.toPre.P.A
      isAb := hB
      q := g.q
      i := g.i
      q_hom := g.q_hom
      i_hom := g.i_hom
      q_flat := g.q_flat
      q_surj := g.q_surj
      q_affine := g.q_affine
      isKernel := g.isKernel
      loc := by
        have l := (TQ.ofGtDatum d).loc
        rw [show (TQ.ofGtDatum d).q = g.q from hdq, show (TQ.ofGtDatum d).i = g.i from hdi] at l
        exact l }
  obtain ⟨P₀, hlev⟩ := exists_isLevelCP (maximalIdeal R) 0 U'.P
  have hlev' := hlev
  obtain ⟨w₀, h₀⟩ := hlev
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U'.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U'.P.L.isLB _) _ (pullIso_isGen U'.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := GlobalTheory.ClosedPol.isCPMap_w hG U' 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U'.gt 0).pG)
  obtain ⟨M, wM, hM⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hG D.toPre)
  obtain ⟨w₄, k₄⟩ := GlobalTheory.ClosedPol.cpMap_congr rfl (Category.id_comp _) k₃
    (by rw [Category.assoc, pullback.condition, Category.id_comp]; simpa using Over.w (U'.gt 0).pG)
  obtain ⟨w₅, k₅, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M P₀ _ _ _ g.q.left
    ((Over.w g.q).trans (Category.comp_id _).symm) _ hM).2
    (toBase_mul_of_isMonHom g.q _) w₄ k₄
  have De : Q.Desc P₀ := ⟨M, w₅, k₅⟩
  obtain ⟨a₀, P', -, ha₀, hl', hL', hs', hc'⟩ := GlobalTheory.T.translatedCubicalBundle_closedFibre_uniformisation R D A G U a ha P hP hsym hcub P₀ hlev'
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_even_cubicalTriv_translate_order_two _ _ D.toPre.X Q P₀ ⟨De⟩ a₀ ha₀ P' hL' hs' hc'
  exact ⟨D.toPre.X, inferInstance, inferInstance, inferInstance, Q, P', hl', σ', hσ'⟩

end GlobalTheory.Mum.TransEven
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedUniformisationBundleEvenClosedFibreTorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedUniformisationBundle_even_closedFibreTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
      EvenOn P := by
  first | exact @GlobalTheory.Mum.TransEven.evenOn_translate | exact GlobalTheory.Mum.TransEven.evenOn_translate | (intros; apply GlobalTheory.Mum.TransEven.evenOn_translate <;> assumption)
end
