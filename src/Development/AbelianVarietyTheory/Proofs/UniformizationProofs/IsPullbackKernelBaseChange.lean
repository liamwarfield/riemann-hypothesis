module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem isPullback_kernel_baseChange {S S' : Scheme.{0}} (f : S' ⟶ S) {T G B : Over S} [GrpObj B]
    {i : T ⟶ G} {q : G ⟶ B} (h : IsPullback i (toUnit _) q (η[B])) :
    IsPullback ((Over.pullback f).map i) (toUnit _) ((Over.pullback f).map q) (η[(Over.pullback f).obj B]) := by
  refine (h.map (Over.pullback f)).of_iso (Iso.refl _) (Iso.refl _)
    (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp) ?_
  simp [Functor.obj.η_def]

theorem isPullback_pullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {G B : Over S} (q : G ⟶ B) :
    IsPullback (pullback.fst G.hom f) ((Over.pullback f).map q).left q.left (pullback.fst B.hom f) := by
  have h₁ : IsPullback (pullback.fst G.hom f) (((Over.pullback f).map q).left ≫ pullback.snd B.hom f)
      (q.left ≫ B.hom) f := by
    have : ((Over.pullback f).map q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f :=
      Over.w ((Over.pullback f).map q)
    rw [this, Over.w]
    exact IsPullback.of_hasPullback _ _
  exact h₁.of_bot (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)

theorem TQ.exists_isGrpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S)
    [GrpObj G] (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ (Q : TQ G X) (Q' : TQ G' X), TorusCompat f F Q'.i Q.i →
    ∃ β : Q'.B.left ⟶ Q.B.left, Q'.q.left ≫ β = F ≫ Q.q.left ∧ IsGrpPullback Q'.B Q.B f β := by
  intro S S' f X _ G _ G' _ F hF Q Q' hT
  obtain ⟨e, he, heF⟩ := grpPullback_iso hF (isGrpPullback_pullback G f)
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have := Q'.q_affine
  have sq := isPullback_pullback_map_left f Q.q
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hi : Q'.i ≫ e.hom = (SplitTorus.bcIso f X).hom ≫ (Over.pullback f).map Q.i := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have a := (isPullback_pullback_map_left f Q.i).w
    have b := SplitTorus.bcIso_hom_fst f X
    exact ((Category.assoc _ _ _).trans ((congrArg (Q'.i.left ≫ ·) heF).trans (torusCompat_iff.1 hT).symm)).trans
      ((congrArg (· ≫ Q.i.left) b.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a).trans (Category.assoc _ _ _).symm)))
  have hk : IsPullback Q'.i (toUnit _) (e.hom ≫ (Over.pullback f).map Q.q) (η[(Over.pullback f).obj Q.B]) := by
    refine (isPullback_kernel_baseChange f Q.isKernel).of_iso (SplitTorus.bcIso f X).symm e.symm (Iso.refl _)
      (Iso.refl _) ?_ (toUnit_unique _ _) (by simp) (by simp)
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hi, Iso.inv_hom_id_assoc]
  have h₁ : Flat ((Over.pullback f).map Q.q).left := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  have h₂ : Surjective ((Over.pullback f).map Q.q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
  have h₃ : QuasiCompact ((Over.pullback f).map Q.q).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  obtain ⟨β, hβ, hq⟩ := flatQuotient_iso_of_same_kernel S' G' ((Over.pullback f).obj Q.B) Q'.B _ _
    (e.hom ≫ (Over.pullback f).map Q.q) Q'.i Q'.q Q'.i inferInstance Q'.i_hom
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hk Q'.q_hom Q'.i_hom Q'.q_flat Q'.q_surj inferInstance Q'.isKernel
    hk.w Q'.isKernel.w
  refine ⟨β.hom.left ≫ pullback.fst Q.B.hom f, ?_,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback Q.B f)).congr (Category.id_comp f) rfl⟩
  rw [← Category.assoc, ← Over.comp_left, hq, Over.comp_left, Category.assoc, ← heF, Category.assoc]
  exact congrArg (_ ≫ ·) sq.w.symm

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

theorem IsCPMap.cancel {P : CP G} {P' : CP G'} {P'' : CP G''} {f' : S'' ⟶ S'} {F' : G''.left ⟶ G'.left}
    {hw' : F' ≫ G'.hom = G''.hom ≫ f'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    {hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f} {w'' : LB.Iso P''.L.L (P.L.L.pull (F' ≫ F))}
    (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'')
    (mul : ∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y)
    (Tw : Tri w w' w'') : IsCPMap P'' P' f' F' hw' w' := by
  have key : ∀ (T : Over S''), ∃ ρ : Over.mk (T.hom ≫ f' ≫ f) ⟶ Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f),
      ρ.left = 𝟙 T.left ∧ ∀ x : T ⟶ G'', toBase hw'' x = ρ ≫ toBase hw (toBase hw' x) := fun T =>
    ⟨Over.homMk (𝟙 T.left) (by simp), rfl, fun x => Over.OverMorphism.ext
      ((Category.assoc _ _ _).symm.trans (Category.id_comp _).symm)⟩
  refine ⟨mul, (isGen_iff _).2 (Tw.pgen_cancel P.L.isLB ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h''.gen)),
    fun T z J'' J' hJ'' hJ' B hB => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
  obtain ⟨ρ, hρ, e⟩ := key T
  obtain ⟨a₁, a₂, a₃⟩ := h.vals (Over.mk (T.hom ≫ f')) z J' J hJ' hJ _ (fun _ => rfl)
  let β := toBaseHom mul T
  let A : (Over.mk (T.hom ≫ f') ⟶ G') → (T.left.presheaf.stalk z)ˣ :=
    fun x => gw w x.left z (J (x.left ≫ F)) (J' x.left)
  have hAB : ∀ x : T ⟶ G'', A (β x) * B x = gw w'' x.left z (J (x.left ≫ F' ≫ F)) (J'' x.left) := fun x => by
    rw [hB, ← Category.assoc]
    exact (Tw _ x.left z _ _ _ (hJ ((x.left ≫ F') ≫ F)) (hJ' (x.left ≫ F')) (hJ'' x.left)).symm
  obtain ⟨b₁, b₂, b₃⟩ := h''.vals T z J'' J hJ'' hJ (fun x => A (β x) * B x) hAB
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · rw [map_one, ← Category.assoc, _root_.mul_assoc] at b₁
    exact mul_left_cancel (a := A 1) (a₁.symm.trans b₁)
  · have a : val P.sym ((x.left ≫ F') ≫ F) z J * A (β x) = A (β x)⁻¹ * val P'.sym (x.left ≫ F') z J' := a₂ (β x)
    have b := b₂ x
    rw [map_inv, ← Category.assoc, ← _root_.mul_assoc, a, _root_.mul_assoc, _root_.mul_assoc] at b
    exact mul_left_cancel b
  · have c : @_root_.id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ f' ≫ f)) z J (toBase hw'' x)
        (toBase hw'' y) (toBase hw'' u)) = cubV P.c (T := Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) z J
        (toBase hw (β x)) (toBase hw (β y)) (toBase hw (β u)) := by
      have e' : (lift (toBase hw'' x) (lift (toBase hw'' y) (toBase hw'' u))).left =
          (lift (toBase hw (β x)) (lift (toBase hw (β y)) (toBase hw (β u)))).left := by
        rw [e, e, e, ← comp_lift, ← comp_lift, Over.comp_left, hρ]; exact Category.id_comp _
      exact congrArg (fun r => val (L := P.L.L) (φ := thφ G (x3 G)) (ε := thε) P.c.t r z J) e'
    obtain ⟨C, hC⟩ : ∃ C : (T.left.presheaf.stalk z)ˣ, C = cubV P.c (T := Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) z J
        (toBase hw (β x)) (toBase hw (β y)) (toBase hw (β u)) := ⟨_, rfl⟩
    obtain ⟨C', hC'⟩ : ∃ C' : (T.left.presheaf.stalk z)ˣ, C' = cubV P'.c (T := Over.mk (T.hom ≫ f')) z J'
        (β x) (β y) (β u) := ⟨_, rfl⟩
    have a : C * A (β x * β y) * A (β x * β u) * A (β y * β u) * A 1 =
        A (β x * β y * β u) * A (β x) * A (β y) * A (β u) * C' := by
      rw [hC, hC']; exact a₃ (β x) (β y) (β u)
    have b := b₃ x y u
    rw [c.trans hC.symm] at b
    simp only [map_mul, map_one] at b
    have g : C' * B (x * y) * B (x * u) * B (y * u) * B 1 =
        B (x * y * u) * B x * B y * B u * cubV P''.c z J'' x y u := by
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have b' := congrArg Additive.ofMul b
      simp only [ofMul_mul] at a' b' ⊢
      linear_combination (norm := abel) b' - a'
    rw [hC'] at g
    exact g

theorem isCPMap_comp_cancel :
    (∀ (S S' S'' : Scheme.{0}) (f : S' ⟶ S) (f' : S'' ⟶ S') (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (G'' : Over S'') [GrpObj G''] [IsCommMonObj G''] (P : CP G) (P' : CP G') (P'' : CP G'') (F : G'.left ⟶ G.left) (hw) (w) (F' : G''.left ⟶ G'.left) (hw' : F' ≫ G'.hom = G''.hom ≫ f') (hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f), IsCPMap P' P f F hw w → (∀ w', IsCPMap P'' P' f' F' hw' w' → ∃ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' ∧ Tri w w' w'') ∧ ((∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y) → ∀ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' → ∃ w', IsCPMap P'' P' f' F' hw' w' ∧ Tri w w' w'')) := by
  intro S S' S'' f f' G _ _ G' _ _ G'' _ _ P P' P'' F hw w F' hw' hw'' h
  refine ⟨fun w' h' => ?_, fun mul w'' h'' => ?_⟩
  · obtain ⟨w'', Tw, H⟩ := h.exists_comp h' hw''
    exact ⟨w'', H, Tw⟩
  · obtain ⟨w', Tw⟩ := Geo.Tor.exists_cancel P.L.isLB w w'' ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h''.gen)
      P'.L.isLB P''.L.isLB
    exact ⟨w', h.cancel h'' mul Tw, Tw⟩

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory
namespace TorusGrading

theorem toSpecΓ_appLE_fromSpec {Y Z : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) (g : Z ⟶ Y)
    (h : ⊤ ≤ g ⁻¹ᵁ V) : Z.toSpecΓ ≫ Spec.map (g.appLE V ⊤ h) ≫ hV.fromSpec = g := by
  have : IsIso (⊤ : Z.Opens).ι := inferInstanceAs (IsIso Z.topIso.hom)
  rw [← cancel_epi (⊤ : Z.Opens).ι, ← Category.assoc, ← Scheme.Opens.toSpecΓ_top,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]

theorem appLE_comp_top {Y Z W : Scheme.{0}} {V : Y.Opens} (s : W ⟶ Z) (g : Z ⟶ Y) (h : ⊤ ≤ g ⁻¹ᵁ V)
    {g' : W ⟶ Y} (e : s ≫ g = g') (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(Y, V)) :
    (g'.appLE V ⊤ h').hom u = s.appTop.hom ((g.appLE V ⊤ h).hom u) := by
  subst e
  have e : s.appTop = s.appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [e]
  exact (congrArg (fun q => q.hom u) (Scheme.Hom.appLE_comp_appLE s g V ⊤ ⊤ h le_top)).symm

theorem top_le_comp {Y Z W : Scheme.{0}} {V : Y.Opens} (s : W ⟶ Z) {g : Z ⟶ Y} (h : ⊤ ≤ g ⁻¹ᵁ V) :
    ⊤ ≤ (s ≫ g) ⁻¹ᵁ V := fun _ _ => h trivial

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem chV_comp {W Z : Over S} (s : W ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (s ≫ t) χ).val = s.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

theorem chV_one {Z : Over S} (χ : X) : chV (1 : Z ⟶ splitTorus S X) χ = 1 := by
  rw [chV, map_one]; rfl

theorem eq_zero_of_sum_chV (Z : Over S) (s : Finset X) (h : X → Γ(Z.left, ⊤))
    (hs : ∑ χ ∈ s, (chV (fst (splitTorus S X) Z) χ).val * (snd (splitTorus S X) Z).left.appTop.hom (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by
  refine TorusInj.eq_zero_of_sum X Z s h (Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) hs)
  refine congrArg₂ (· * ·) ?_ rfl
  rw [chV_val]
  exact congrArg (fun q => q.hom (TorusInj.chiP X Z χ))
    ((splitTorus S X ⊗ Z).left.presheaf.map_id (Opposite.op ⊤))

variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V : G.left.Opens}

theorem top_le_act
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {Z : Over S} (t : Z ⟶ splitTorus S X) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V := by
  have e : (t ≫ i) * g = lift t g ≫ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G) := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  rw [e, Over.comp_left, Scheme.Hom.comp_preimage]
  refine le_trans ?_ ((lift t g).left.preimage_mono hst)
  rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, lift_snd]
  exact h

theorem exists_expansion (hV : IsAffineOpen V)
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : ∃ a : X →₀ Γ(G.left, V), ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ a.support, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ) := by
  let B : CommRingCat.{0} := TorusInj.GA (X := X) (V := V)
  let P : Over S := Over.mk (TorusInj.ptY (X := X) hV ≫ G.hom)
  let g₀ : P ⟶ G := Over.homMk (TorusInj.ptY (X := X) hV) rfl
  let ε : Γ(P.left, ⊤) ≅ B := Scheme.ΓSpecIso B
  let t₀ : P ⟶ splitTorus S X := (splitTorusPointsEquiv S X P).symm
    (ε.inv.hom.toMonoidHom.comp (AddMonoidAlgebra.of Γ(G.left, V) X)).toHomUnits
  have ht₀ : ∀ χ, (chV t₀ χ).val = ε.inv.hom (AddMonoidAlgebra.single χ 1) := fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; rfl
  have hg₀ : ⊤ ≤ g₀.left ⁻¹ᵁ V := (TorusInj.ptY_preimage hV).ge
  let f : AddMonoidAlgebra Γ(G.left, V) X :=
    ε.hom.hom ((((t₀ ≫ i) * g₀).left.appLE V ⊤ (top_le_act hst t₀ hg₀)).hom u)
  refine ⟨f.coeff, fun Z t g h₁ h₂ => ?_⟩
  letI : Algebra Γ(G.left, V) Γ(Z.left, ⊤) := (g.left.appLE V ⊤ h₂).hom.toAlgebra
  let φ₀ : AddMonoidAlgebra Γ(G.left, V) X →ₐ[Γ(G.left, V)] Γ(Z.left, ⊤) :=
    AddMonoidAlgebra.lift Γ(G.left, V) Γ(Z.left, ⊤) X ((Units.coeHom _).comp (splitTorusPointsEquiv S X Z t))
  let φ : B ⟶ Γ(Z.left, ⊤) := CommRingCat.ofHom φ₀.toRingHom
  have hφ : ∀ χ c, φ.hom (AddMonoidAlgebra.single χ c) = (chV t χ).val * (g.left.appLE V ⊤ h₂).hom c := fun χ c => by
    change φ₀ (AddMonoidAlgebra.single χ c) = _
    rw [AddMonoidAlgebra.lift_single, Algebra.smul_def, mul_comm]; rfl
  have hσ : (Z.left.toSpecΓ ≫ Spec.map φ) ≫ TorusInj.ptY (X := X) hV = g.left := by
    rw [TorusInj.ptY, Category.assoc, ← Spec.map_comp_assoc]
    refine Eq.trans ?_ (toSpecΓ_appLE_fromSpec hV g.left h₂)
    congr 3
    exact CommRingCat.hom_ext (RingHom.ext fun c => φ₀.commutes c)
  let σ : Z ⟶ P := Over.homMk (Z.left.toSpecΓ ≫ Spec.map φ)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) hσ).trans (Over.w g)))
  have hσa : ∀ x : Γ(P.left, ⊤), σ.left.appTop.hom x = φ.hom (ε.hom.hom x) := fun x => by
    have : (Z.left.toSpecΓ ≫ Spec.map φ).appTop = ε.hom ≫ φ := by
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
    exact congrArg (fun q => q.hom x) this
  have hε : ∀ x : B, ε.hom.hom (ε.inv.hom x) = x := fun x => congrArg (fun q => q.hom x) ε.inv_hom_id
  have eg : σ ≫ g₀ = g := Over.OverMorphism.ext hσ
  have et : σ ≫ t₀ = t := (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun χ => Units.ext (by
    change (chV (σ ≫ t₀) χ.toAdd).val = (chV t χ.toAdd).val
    rw [chV_comp, ht₀, hσa, hε, hφ, map_one, _root_.mul_one]))
  have ea : σ ≫ ((t₀ ≫ i) * g₀) = (t ≫ i) * g := by
    rw [MonObj.comp_mul, ← Category.assoc, et, eg]
  rw [appLE_comp_top σ.left _ (top_le_act hst t₀ hg₀) (congrArg (fun q => q.left) ea) h₁ u, hσa]
  change φ.hom f = _
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun χ _ => hφ χ _

theorem exists_point (hV : IsAffineOpen V) : ∃ (Z : Over S) (g : Z ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ V),
    Function.Injective (g.left.appLE V ⊤ h).hom := by
  refine ⟨Over.mk (hV.fromSpec ≫ G.hom), Over.homMk hV.fromSpec rfl, hV.fromSpec_preimage_self.ge, ?_⟩
  have h1 : hV.fromSpec.appLE V ⊤ hV.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  change Function.Injective (hV.fromSpec.appLE V ⊤ hV.fromSpec_preimage_self.ge).hom
  rw [h1]
  exact (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.injective

omit [GrpObj G] in
theorem val_comp {W Z : Over S} (s : W ⟶ Z) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) (h' : ⊤ ≤ (s ≫ g).left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : ((s ≫ g).left.appLE V ⊤ h').hom u = s.left.appTop.hom ((g.left.appLE V ⊤ h).hom u) :=
  appLE_comp_top s.left g.left h (Over.comp_left _ _ _ s g).symm h' u

omit [GrpObj G] in
theorem val_congr {Z : Over S} {g g' : Z ⟶ G} (e : g = g') (h : ⊤ ≤ g.left ⁻¹ᵁ V) (h' : ⊤ ≤ g'.left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : (g.left.appLE V ⊤ h).hom u = (g'.left.appLE V ⊤ h').hom u := by
  subst e; rfl

omit [GrpObj G] in
theorem top_le_comp_left {W Z : Over S} (s : W ⟶ Z) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) :
    ⊤ ≤ (s ≫ g).left ⁻¹ᵁ V := by
  rw [Over.comp_left]; exact top_le_comp s.left h

theorem isWt_of_expansion [IsMonHom i]
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {u : Γ(G.left, V)} {s : Finset X} {a : X → Γ(G.left, V)}
    (ha : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ s, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) {χ : X} (hχ : χ ∈ s) : IsWt i V (a χ) χ := by
  intro Z t g h₁ h₂
  rw [← chV_val, ← sub_eq_zero]
  refine eq_zero_of_sum_chV Z s (fun χ => (((t ≫ i) * g).left.appLE V ⊤ h₁).hom (a χ) -
    (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) ?_ χ hχ
  generalize fst (splitTorus S X) Z = p
  generalize snd (splitTorus S X) Z = q
  have k₁ := top_le_comp_left q h₁
  have k₂ := top_le_comp_left q h₂
  have e : (p ≫ i) * (q ≫ ((t ≫ i) * g)) = ((p * (q ≫ t)) ≫ i) * (q ≫ g) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, _root_.mul_assoc, Category.assoc]
  have a₁ := ha _ p _ (top_le_act hst p k₁) k₁
  have a₂ := ha _ (p * (q ≫ t)) _ (top_le_act hst _ k₂) k₂
  have a₃ := (a₁.symm.trans (val_congr e _ _ u)).trans a₂
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at a₃
  refine Eq.trans (Finset.sum_congr rfl fun ψ _ => ?_) a₃
  rw [val_comp q h₁ k₁, val_comp q h₂ k₂, chV_mul, Units.val_mul, chV_comp, map_sub, map_mul, mul_sub,
    _root_.mul_assoc]

theorem eq_zero_of_sum_isWt (hV : IsAffineOpen V)
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {s : Finset X} {a : X → Γ(G.left, V)} (ha : ∀ χ, IsWt i V (a χ) χ) (hs : ∑ χ ∈ s, a χ = 0) {χ : X}
    (hχ : χ ∈ s) : a χ = 0 := by
  obtain ⟨Z₀, g₀, h₀, inj⟩ := exists_point hV
  refine inj (Eq.trans ?_ (map_zero _).symm)
  refine eq_zero_of_sum_chV Z₀ s (fun χ => (g₀.left.appLE V ⊤ h₀).hom (a χ)) ?_ χ hχ
  generalize fst (splitTorus S X) Z₀ = p
  generalize snd (splitTorus S X) Z₀ = q
  have k := top_le_comp_left q h₀
  have := congrArg (((p ≫ i) * (q ≫ g₀)).left.appLE V ⊤ (top_le_act hst p k)).hom hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at this
  refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) this
  rw [ha χ _ p (q ≫ g₀) _ k, ← chV_val, val_comp q h₀ k]

theorem eq_sum_of_expansion [IsMonHom i] (hV : IsAffineOpen V)
    {u : Γ(G.left, V)} {s : Finset X} {a : X → Γ(G.left, V)}
    (ha : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ s, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) : u = ∑ χ ∈ s, a χ := by
  obtain ⟨Z₀, g₀, h₀, inj⟩ := exists_point hV
  refine inj ?_
  have e : ((1 : Z₀ ⟶ splitTorus S X) ≫ i) * g₀ = g₀ := by rw [MonObj.one_comp, _root_.one_mul]
  have h₁ : ⊤ ≤ (((1 : Z₀ ⟶ splitTorus S X) ≫ i) * g₀).left ⁻¹ᵁ V := by rw [e]; exact h₀
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← val_congr e h₁ h₀ u, ha Z₀ 1 g₀ h₁ h₀]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [chV_one, Units.val_one, _root_.one_mul]

end TorusGrading


open TorusGrading in
theorem functions_graded_by_weights :
    (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V → (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V → (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧ ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0) := by
  intro S G _ X _ i hi V hV hst
  refine ⟨fun u => ?_, fun a ha hs => ?_⟩
  · obtain ⟨a, ha⟩ := exists_expansion hV hst u
    refine ⟨a, fun χ => ?_, eq_sum_of_expansion hV ha⟩
    by_cases hχ : χ ∈ a.support
    · exact isWt_of_expansion hst ha hχ
    · rw [Finsupp.notMem_support_iff.1 hχ]
      exact isWt_zero χ
  · refine Finsupp.ext fun χ => ?_
    by_contra h
    exact h (eq_zero_of_sum_isWt hV hst ha hs (Finsupp.mem_support_iff.2 h))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGradedStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.torusStable_affineOpen_functions_weightGraded : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V → (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V → (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧ ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0) := by
  first | exact @GlobalTheory.functions_graded_by_weights | exact GlobalTheory.functions_graded_by_weights | (intros; apply GlobalTheory.functions_graded_by_weights <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finrank_eq_card_kernel_points_of_etale :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ φ : B ⟶ B, ∀ [IsFinite φ.left] [Etale φ.left], ∀ x : B.left, φ.left.finrank x = Nat.card {y : 𝟙_ _ ⟶ B // y ≫ φ = 1} := by
  intro K _ _ B _ _ hB φ _ _ x
  have := hB.geomConnected
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  let o : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B := 1
  let t : Spec (CommRingCat.of K) ⟶ B.left := o.left
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have ht : t ≫ B.hom = 𝟙 _ := Over.w o
  rw [(Scheme.Hom.isLocallyConstant_finrank φ.left).apply_eq_of_preconnectedSpace x (t z),
    ← (GlobalTheory.FinEt.card_points_eq_finrank φ.left t z).2]
  refine Nat.card_congr
    { toFun := fun y ↦ ⟨Over.homMk y.1 ?_, Over.OverMorphism.ext y.2⟩
      invFun := fun y ↦ ⟨y.1.left, congrArg CommaMorphism.left y.2⟩
      left_inv := fun y ↦ rfl
      right_inv := fun y ↦ Subtype.ext (Over.OverMorphism.ext rfl) }
  change y.1 ≫ B.hom = 𝟙 _
  rw [← Over.w φ, ← Category.assoc, y.2, ht]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullLinear

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusCoord

theorem map_left_fst {S T : Scheme.{0}} (f : S ⟶ T) {A B : Over T} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

theorem ext_of_iso_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {A' Z : Over S'}
    (e : A' ≅ (Over.pullback f).obj A) {a b : Z ⟶ A'}
    (h : a.left ≫ e.hom.left ≫ pullback.fst A.hom f = b.left ≫ e.hom.left ≫ pullback.fst A.hom f) :
    a = b := by
  rw [← cancel_mono e.hom]
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · simpa only [Over.comp_left, Category.assoc] using h
  · exact (Over.w (a ≫ e.hom)).trans (Over.w (b ≫ e.hom)).symm

theorem ext_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {Z : Over S'}
    {a b : Z ⟶ (Over.pullback f).obj A}
    (h : a.left ≫ pullback.fst A.hom f = b.left ≫ pullback.fst A.hom f) : a = b :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w a).trans (Over.w b).symm))

theorem act_proj {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {A' : Over S'}
    (e : A' ⟶ (Over.pullback f).obj A) {u : A ⟶ A} {u' : A' ⟶ A'}
    (h : u' ≫ e = e ≫ (Over.pullback f).map u) :
    u'.left ≫ e.left ≫ pullback.fst A.hom f = (e.left ≫ pullback.fst A.hom f) ≫ u.left := by
  have h1 : u'.left ≫ e.left = e.left ≫ ((Over.pullback f).map u).left := congrArg (·.left) h
  rw [← Category.assoc, h1, Category.assoc, map_left_fst, Category.assoc]

section One

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem pG_left : g.pG.left = g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) := rfl

theorem im_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ WeightPf.Te D I e) :
    im g (τ ≫ g.i) = 1 := by
  have := g.q_hom
  rw [← im_one g]
  refine im_congr g ?_
  rw [Category.assoc, g.isKernel.w, MonObj.one_comp, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem exists_torus_of_im {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y : Z ⟶ thickObj R I e G) (h : im g y = 1) : ∃ τ : Z ⟶ WeightPf.Te D I e, τ ≫ g.i = y := by
  have h1 : y ≫ g.q = (1 : Z ⟶ thickObj R I e G) ≫ g.q := by
    refine ext_of_pullback _ ?_
    have := congrArg (·.left) (h.trans (im_one g).symm)
    exact ((Category.assoc _ _ _).trans this).trans (Category.assoc _ _ _).symm
  obtain ⟨τ, hτ⟩ := exists_torus g y 1 h1
  exact ⟨τ, by rw [hτ, _root_.mul_one]⟩

theorem prod_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ WeightPf.Te D I e)
    (χ : D.X) {U : Type} [CommGroup U] (f : (Z.left ⟶ D.P.A.left) → U) :
    ∏ k, f ((τ ≫ g.i).left ≫ D.Oφ g.pG χ k) ^ Oinvε k = 1 := by
  have e0 : ∀ k, (τ ≫ g.i).left ≫ D.Oφ g.pG χ k = D.Oφ (im g (τ ≫ g.i)) χ k := fun k =>
    WeightPf.Oφ_comp ((Over.map (thick R I e)).map (τ ≫ g.i)) g.pG χ k
  simp only [e0]
  rw [Fin.prod_univ_four, im_torus]
  change f ((1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A) * cPt Z χ).left ^ (-1 : ℤ) *
    f (cPt Z χ).left ^ (1 : ℤ) * f (1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A).left ^ (1 : ℤ) *
    f (1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A).left ^ (-1 : ℤ) = 1
  rw [_root_.one_mul, zpow_neg_one, zpow_neg_one, zpow_one, zpow_one, inv_mul_cancel, _root_.one_mul,
    mul_inv_cancel]

theorem torusEndOf_iff {S : Scheme.{0}} (X : Type) [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) :
    TorusEndOf X h t ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X),
      gm (r ≫ t.left) z ⊤ (charUnit S X χ) = gm r z ⊤ (charUnit S X (h χ)) := by
  constructor
  · intro H Z r z χ
    rw [← H χ]
    exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm
  · intro H χ
    refine unit_ext fun z _ => ?_
    rw [← H]
    exact (gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)

end One

section Two

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} {D : DegPre R} {D' : DegPre R'} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (g : GtCoord I D e G) (g' : GtCoord I' D' e G') {F : D'.P.A.left ⟶ D.P.A.left}
  {h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left}

theorem char_eq (w : LB.Iso D'.P.L (D.P.L.pull F)) {x' : D'.X} {x : D.X}
    (hψ : ∀ κ : Fin 4, D'.Oφ g'.pG x' κ ≫ F = h ≫ D.Oφ g.pG x κ)
    (hm : PMaps w (D'.Oφ g'.pG x') (D.Oφ g.pG x) Oinvε (g'.t x') (g.t x) h)
    {Z' : Over (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))))}
    {s : Z'.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))}
    (τ' : Z' ⟶ WeightPf.Te D' I' e) (τ : Over.mk s ⟶ WeightPf.Te D I e)
    (hτ : (τ ≫ g.i).left = (τ' ≫ g'.i).left ≫ h) (z : Z'.left) :
    gm (Y := Z'.left) τ.left z ⊤ (charUnit _ D.X x) = gm τ'.left z ⊤ (charUnit _ D'.X x') := by
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.P.L D.P.isLB z
  obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB z
  have h₁ := (val_torus_point_and_translate R I D e G g (Over.mk s) τ 1 z J hJ x).1
  have h₂ := (val_torus_point_and_translate R' I' D' e G' g' Z' τ' 1 z J' hJ' x').1
  have h₃ := hm Z'.left (τ' ≫ g'.i).left z
    (fun k => J (((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k) ≫ F))
    (fun k => J' ((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k))
    (fun k => hJ (((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k) ≫ F))
    (fun k => hJ' ((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k))
  rw [prod_torus g' τ' x' (fun ψ => gw w ψ z (J (ψ ≫ F)) (J' ψ)), _root_.one_mul] at h₃
  refine h₁.symm.trans (Eq.trans ?_ (h₃.trans h₂))
  rw [hτ]
  exact val_of (g.t x) ((τ' ≫ g'.i).left ≫ h) z J _ (fun k => by
    rw [Category.assoc, Category.assoc, hψ k])

theorem exists_point {x' : D'.X} {x : D.X} (hp : g'.pG.left ≫ F = h ≫ g.pG.left)
    (hψ : ∀ κ : Fin 4, D'.Oφ g'.pG x' κ ≫ F = h ≫ D.Oφ g.pG x κ)
    {Z' : Over (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))))} (τ' : Z' ⟶ WeightPf.Te D' I' e) :
    ∃ (s : Z'.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (τ : Over.mk s ⟶ WeightPf.Te D I e),
      (τ ≫ g.i).left = (τ' ≫ g'.i).left ≫ h := by
  let y : Over.mk (((τ' ≫ g'.i).left ≫ h) ≫ (thickObj R I e G).hom) ⟶ thickObj R I e G :=
    Over.homMk ((τ' ≫ g'.i).left ≫ h) rfl
  have h1 : (τ' ≫ g'.i).left ≫ g'.pG.left = (τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' 3 := by
    refine (congrArg (·.left) (im_torus g' τ')).trans ?_
    exact (WeightPf.Oφ_comp ((Over.map (thick R' I' e)).map (τ' ≫ g'.i)) g'.pG x' 3).symm
  have h2 : im g y = 1 := by
    refine Over.OverMorphism.ext ?_
    refine Eq.trans ?_ (WeightPf.Oφ_comp ((Over.map (thick R I e)).map y) g.pG x 3)
    change ((τ' ≫ g'.i).left ≫ h) ≫ g.pG.left = ((τ' ≫ g'.i).left ≫ h) ≫ D.Oφ g.pG x 3
    rw [Category.assoc, Category.assoc, ← hp, ← hψ, ← Category.assoc, h1, Category.assoc]
  obtain ⟨τ, hτ⟩ := exists_torus_of_im g y h2
  exact ⟨_, τ, congrArg (·.left) hτ⟩

end Two

theorem oLinear_of_isPullUnif : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → (∀ a, (ιG'.act a) ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf φ)).map (ιG.act a)) → (∀ a, (Over.pullback (jK R')).map (ιG'.act a) ≫ U'.gen.hom = U'.gen.hom ≫ ιA'.act a) → (∀ (a : O) (y : D'.toPre.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) → U'.OLinear O ιD' ιA' ιG' := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ U U' hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    hlin hG hgen hx hB
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  choose h hf hpt _hw using H
  have hact : ∀ (e : ℕ) (a : O), ((Over.pullback (thick R' I' e)).map (ιG'.act a)).left ≫ h e =
      h e ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left := by
    intro e a
    have hf' : h e ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hf e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G.hom (thick R I e)), Category.assoc, Category.assoc, map_left_fst,
      ← Category.assoc (h e), hf', ← Category.assoc, map_left_fst, Category.assoc,
      act_proj _ bc.hom (hG a), Category.assoc, Category.assoc, Category.assoc]
  have hq : ∀ (e : ℕ) (a : O), (Over.pullback (thick R' I' e)).map (ιG'.act a) ≫ (U'.gt e).q =
      (U'.gt e).q ≫ (Over.pullback (thick R' I' e)).map (ιD'.onB.act a) := by
    intro e a
    have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S}
        {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (g : GtCoord J E e K)
        (u : E.P.A ⟶ E.P.A), (g.q ≫ (Over.pullback (thick S J e)).map u).left ≫
          pullback.fst E.P.A.hom (thick S J e) = g.pG.left ≫ u.left := by
      intro S _ _ J E K _ _ g u
      rw [Over.comp_left, Category.assoc, map_left_fst, pG_left, Category.assoc]
    have k₁ : ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ (U.gt e).pG.left =
        (U.gt e).pG.left ≫ (ιD.onB.act a).left := by
      rw [← k, ← hlin.q_lin e a]
      exact (Category.assoc _ _ _).symm
    have k₂ : (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map (ιG'.act a)) ≫
        (U'.gt e).pG = (U'.gt e).pG ≫ ιD'.onB.act a := by
      refine ext_of_iso_pullback _ hD.e ?_
      change (((Over.pullback (thick R' I' e)).map (ιG'.act a)).left ≫ (U'.gt e).pG.left) ≫ _ =
        ((U'.gt e).pG.left ≫ (ιD'.onB.act a).left) ≫ _
      rw [Category.assoc, Category.assoc, act_proj _ hD.e.hom (hB a), (hpt e).1,
        ← Category.assoc (U'.gt e).pG.left, (hpt e).1, ← Category.assoc, hact, Category.assoc,
        Category.assoc, k₁]
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) k₂
  refine ⟨hgen, hq, fun e a => ?_⟩
  obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
  have := ιD'.onB.hom a
  have hk : ((U'.gt e).i ≫ (Over.pullback (thick R' I' e)).map (ιG'.act a)) ≫ (U'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U'.gt e).isKernel.lift_fst _ _ hk
  generalize (U'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U.gt e) (U'.gt e) (hpt e).1 ((hpt e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U.gt e).i).left = (t' ≫ (U'.gt e).i).left ≫ h e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 χ).1 ((hpt e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 (star a • χ)).1 ((hpt e).2 (star a • χ)).2
    (𝟙 _) τ hτ z
  have e₃ := (torusEndOf_iff _ _ t).1 ht _ τ.left z (hD.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.PullLinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionOfIsPullDeg
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_oAct_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] (ιD : D.OAct O), ∃ (_ : Module O D'.X) (ιD' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) ∧ (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) := by
  intro hG R R' _ _ _ _ φ D D' hD O _ _ _ ιD
  have gp := pull_grp hD
  obtain ⟨o', ho'⟩ := polOActPull _ _ _ D.P D'.P _ gp (LBIso.symm ⟨hD.w, hD.w_gen⟩) O ιD.onB
  letI inst : Module O D'.X := hD.xe.module O
  have hs : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y := fun a y =>
    hD.xe.apply_symm_apply _
  have he : ∀ a, o'.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a) := fun a => by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · have := ho' a
      simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst] at this ⊢
      exact this
    · exact (Over.w (o'.act a ≫ hD.e.hom)).trans
        (Over.w (hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))).symm
  refine ⟨inst, ⟨o', fun a y => ?_, fun a => ?_⟩, hs, he⟩
  · refine Over.OverMorphism.ext (gp.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hD.c_pr, hs, ιD.c_lin, Over.comp_left, Over.comp_left, Category.assoc, ho', ← Category.assoc,
      ← Category.assoc (D'.c y).left, hD.c_pr]
  · exact tauBal_of_isPullDeg hG R R' φ D D' hD _ _ _ _ (ιD.onB.hom a) (ιD.onB.hom (star a)) (ιD.onB.rosati a)
      (he a) (he (star a)) _ _ _ _ (hs a) (hs (star a)) (ιD.c_lin a) (ιD.c_lin (star a)) (ιD.tau_bal a)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableOfSurjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem torus_stable_of_surjective {S S' : Scheme.{0}} (f : S' ⟶ S) [Surjective f]
    (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] (G₀ : Over S') [GrpObj G₀]
    (F : G₀.left ⟶ G.left) (hF : IsGrpPullback G₀ G f F)
    (i₀ : splitTorus _ X ⟶ G₀) (i : splitTorus _ X ⟶ G) (hi : TorusCompat f F i₀ i)
    (W : G.left.Opens)
    (hW : (snd (splitTorus _ X) G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) ≤
      ((fst (splitTorus _ X) G₀ ≫ i₀) * snd _ G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W)) :
    (snd (splitTorus _ X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ W := by
  rw [torusCompat_iff] at hi
  let P : Over S := splitTorus S X ⊗ G
  let p : pullback P.hom f ⟶ P.left := pullback.fst P.hom f
  let Z₀ : Over S' := Over.mk (pullback.snd P.hom f)
  have hT := SplitTorus.isPullback_bcMap f X
  have w₁ : (p ≫ (fst (splitTorus S X) G).left) ≫ (splitTorus S X).hom = pullback.snd P.hom f ≫ f := by
    rw [Category.assoc, Over.w]; exact pullback.condition
  have w₂ : (p ≫ (snd (splitTorus S X) G).left) ≫ G.hom = pullback.snd P.hom f ≫ f := by
    rw [Category.assoc, Over.w]; exact pullback.condition
  let t₀ : Z₀ ⟶ splitTorus S' X := Over.homMk (hT.lift _ _ w₁) (hT.lift_snd _ _ w₁)
  let g₀ : Z₀ ⟶ G₀ := Over.homMk (hF.1.lift _ _ w₂) (hF.1.lift_snd _ _ w₂)
  have ht₀ : t₀.left ≫ SplitTorus.bcMap f X = p ≫ (fst (splitTorus S X) G).left := hT.lift_fst _ _ w₁
  have hg₀ : g₀.left ≫ F = p ≫ (snd (splitTorus S X) G).left := hF.1.lift_fst _ _ w₂
  let ρ : Over.mk (Z₀.hom ≫ f) ⟶ P := Over.homMk p pullback.condition
  have h1 : (ρ ≫ fst (splitTorus S X) G ≫ i).left = (t₀ ≫ i₀).left ≫ F := by
    change _ = (t₀.left ≫ i₀.left) ≫ F
    rw [Category.assoc, ← hi, ← Category.assoc t₀.left, ht₀, Category.assoc]; rfl
  have h2 : (ρ ≫ snd (splitTorus S X) G).left = g₀.left ≫ F := hg₀.symm
  have h3 := hF.2 Z₀ (t₀ ≫ i₀) g₀ _ _ h1 h2
  let l : Z₀ ⟶ splitTorus S' X ⊗ G₀ := lift t₀ g₀
  have h4 : p ≫ ((fst (splitTorus S X) G ≫ i) * snd _ G).left =
      l.left ≫ ((fst (splitTorus S' X) G₀ ≫ i₀) * snd _ G₀).left ≫ F := by
    have e : l ≫ ((fst (splitTorus S' X) G₀ ≫ i₀) * snd _ G₀) = (t₀ ≫ i₀) * g₀ := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    rw [← Category.assoc, ← Over.comp_left, e, ← h3, ← MonObj.comp_mul]; rfl
  have h5 : p ≫ (snd (splitTorus S X) G).left = l.left ≫ (snd (splitTorus S' X) G₀).left ≫ F := by
    rw [← Category.assoc, ← Over.comp_left, lift_snd, hg₀]
  have h6 : (p ≫ (snd (splitTorus S X) G).left) ⁻¹ᵁ W ≤
      (p ≫ ((fst (splitTorus S X) G ≫ i) * snd _ G).left) ⁻¹ᵁ W := by
    rw [h4, h5]
    exact fun z hz => hW hz
  intro x hx
  obtain ⟨z, rfl⟩ := p.surjective x
  exact h6 hx

theorem torus_stable_of_red : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ (i₀ : splitTorus _ X ⟶ G₀) (i : splitTorus _ X ⟶ G), TorusCompat (red J) F i₀ i → ∀ W : G.left.Opens, (snd (splitTorus _ X) G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) ≤ ((fst (splitTorus _ X) G₀ ≫ i₀) * snd _ G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) → (snd (splitTorus _ X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ W := by
  intro A _ J hJ X _ G _ G₀ _ F hF i₀ i hi W hW
  haveI := surjective_red hJ
  exact torus_stable_of_surjective (red J) X G G₀ F hF i₀ i hi W hW

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNRatioTwist
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem cubN_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) * W (a * b) * W (a * d) * W (b * d) * W 1 =
      W (a * b * d) * W a * W b * W d * θ' a b d) (x y : A') (k : ℕ) :
    cubN θ k 1 (β x) (β y) * W (x ^ k) * W y * (W (x * y) * W 1) ^ k =
      W (x ^ k * y) * W 1 * (W x * W y) ^ k * cubN θ' k 1 x y := by
  induction k with
  | zero => simp only [cubN, Finset.range_zero, Finset.prod_empty, pow_zero, _root_.one_mul, _root_.mul_one]; exact mul_comm _ _
  | succ k ih =>
    have e₁ : cubN θ (k + 1) 1 (β x) (β y) = cubN θ k 1 (β x) (β y) * θ (β (x ^ k)) (β x) (β y) := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, map_pow]
    have e₂ : cubN θ' (k + 1) 1 x y = cubN θ' k 1 x y * θ' (x ^ k) x y := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have H := hθ (x ^ k) x y
    rw [← pow_succ] at H
    rw [e₁, e₂]
    apply mul_right_cancel (b := W (x ^ k) * W (x ^ k * y))
    calc cubN θ k 1 (β x) (β y) * θ (β (x ^ k)) (β x) (β y) * W (x ^ (k + 1)) * W y *
            (W (x * y) * W 1) ^ (k + 1) * (W (x ^ k) * W (x ^ k * y))
          = (cubN θ k 1 (β x) (β y) * W (x ^ k) * W y * (W (x * y) * W 1) ^ k) *
            (θ (β (x ^ k)) (β x) (β y) * W (x ^ (k + 1)) * W (x ^ k * y) * W (x * y) * W 1) := by
          rw [pow_succ (W (x * y) * W 1) k]; ac_rfl
      _ = (W (x ^ k * y) * W 1 * (W x * W y) ^ k * cubN θ' k 1 x y) *
            (W (x ^ (k + 1) * y) * W (x ^ k) * W x * W y * θ' (x ^ k) x y) := by rw [ih, H]
      _ = W (x ^ (k + 1) * y) * W 1 * (W x * W y) ^ (k + 1) * (cubN θ' k 1 x y * θ' (x ^ k) x y) *
            (W (x ^ k) * W (x ^ k * y)) := by
          rw [pow_succ (W x * W y) k]; ac_rfl

theorem cubN_ratio_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) * W (a * b) * W (a * d) * W (b * d) * W 1 =
      W (a * b * d) * W a * W b * W d * θ' a b d) {x y : A'} {N : ℕ} (hx : x ^ N = 1) (hy : y ^ N = 1) {e : U}
    (h : e * cubN θ' N 1 x y = cubN θ' N 1 y x) :
    e * cubN θ N 1 (β x) (β y) = cubN θ N 1 (β y) (β x) := by
  have h₁ := cubN_twist β W hθ x y N
  have h₂ := cubN_twist β W hθ y x N
  simp only [hx, _root_.one_mul] at h₁
  simp only [hy, _root_.one_mul] at h₂
  rw [mul_comm y x, mul_comm (W y) (W x)] at h₂
  have k₁ : cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N =
      (W x * W y) ^ N * cubN θ' N 1 x y := by
    apply mul_right_cancel (b := W 1 * W y)
    calc cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N * (W 1 * W y)
          = cubN θ N 1 (β x) (β y) * W 1 * W y * (W (x * y) * W 1) ^ N := by ac_rfl
      _ = W y * W 1 * (W x * W y) ^ N * cubN θ' N 1 x y := h₁
      _ = (W x * W y) ^ N * cubN θ' N 1 x y * (W 1 * W y) := by ac_rfl
  have k₂ : cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N =
      (W x * W y) ^ N * cubN θ' N 1 y x := by
    apply mul_right_cancel (b := W 1 * W x)
    calc cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N * (W 1 * W x)
          = cubN θ N 1 (β y) (β x) * W 1 * W x * (W (x * y) * W 1) ^ N := by ac_rfl
      _ = W x * W 1 * (W x * W y) ^ N * cubN θ' N 1 y x := h₂
      _ = (W x * W y) ^ N * cubN θ' N 1 y x * (W 1 * W x) := by ac_rfl
  apply mul_right_cancel (b := (W (x * y) * W 1) ^ N)
  calc e * cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N
        = e * (cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N) := mul_assoc _ _ _
    _ = (W x * W y) ^ N * (e * cubN θ' N 1 x y) := by rw [k₁]; ac_rfl
    _ = cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N := by rw [h, k₂]

theorem cubWeil_map : (∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (P : CP G) (P' : CP G') (F : G'.left ⟶ G.left) (hw) (w), IsCPMap P' P f F hw w → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil P'.c N x y ζ → CubWeil P.c N (toBase hw x) (toBase hw y) ζ) := by
  intro S S' f G _ _ G' _ _ P P' F hw w hP N T x y ζ hζ
  obtain ⟨hx, hy, hr⟩ := hζ
  let β := toBaseHom (hw := hw) hP.mul T
  have hβ : ∀ a : T ⟶ G', β a = toBase hw a := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hβ, ← map_pow, hx, map_one]
  · rw [← hβ, ← map_pow, hy, map_one]
  · intro z J hJ
    obtain ⟨J', hJ'⟩ := exists_good_pt P'.L.isLB z
    have hv := (hP.vals T z J' J hJ' hJ (fun a => gw w a.left z (J (a.left ≫ F)) (J' a.left))
      (fun _ => rfl)).2.2
    exact cubN_ratio_twist β (fun a => gw w a.left z (J (a.left ≫ F)) (J' a.left))
      (θ := cubV P.c (T := Over.mk (T.hom ≫ f)) z J) (θ' := cubV P'.c z J') hv hx hy (hr z J' hJ')

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankFamOfLaws
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem finrank_fam_of_laws : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.P.g + D.rank) :=
  fun h₁ h₂ _ _ _ D hB F _ _ k hk => by
    rw [Nat.add_comm]
    exact GlobalTheory.FamDimension.finrank_fam (D := D) (F := F) h₁.globalFns h₂.secTwist hB hk

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCpPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_cp_pull : (∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f), (∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) → ∀ P : CP G, ∃ (P' : CP G') (w : _), P'.L.L = P.L.L.pull F ∧ IsCPMap P' P f F hw w) := by
  intro S S' f G _ _ G' _ _ F hw mul P
  obtain ⟨_, _, _, _, _, _, _, h⟩ :=
    exists_isCPMap P mul _ (pull_isLB P.L.isLB F) _ (pullIso_isGen P.L.isLB F)
  exact ⟨_, _, rfl, h⟩

end GlobalTheory.UU
end
