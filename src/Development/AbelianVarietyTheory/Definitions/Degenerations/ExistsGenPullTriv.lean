module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

structure TowerR (I : Ideal R) (P : CP G) (X : Type) [AddCommGroup X] where
  l : ∀ e, Lev I P X e
  tor : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (l e).Q.i (l (e + 1)).Q.i
  β : ∀ e, (l e).Q.B.left ⟶ (l (e + 1)).Q.B.left
  β_pb : ∀ e, IsCPPullback (l e).D.M (l (e + 1)).D.M (thickTrans R I e) (β e)
  β_q : ∀ e, (l e).Q.q.left ≫ β e = thickMap R I e G ≫ (l (e + 1)).Q.q.left

structure TowerR.Alg {P : CP G} {X : Type} [AddCommGroup X] (t : TowerR I P X) where
  B : Over (Spec (CommRingCat.of R))
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B
  M : CP B
  ample : RelAmple B M.L.L
  b : ∀ e, (t.l e).Q.B.left ⟶ B.left
  b_pb : ∀ e, IsCPPullback (t.l e).D.M M (thick R I e) (b e)
  b_β : ∀ e, t.β e ≫ b (e + 1) = b e
attribute [instance] TowerR.Alg.grp TowerR.Alg.comm

def TowerR.Alg.RepWt {P : CP G} {X : Type} [AddCommGroup X] {t : TowerR I P X} (a : t.Alg) (c : 𝟙_ _ ⟶ a.B) (χ : X) (e : ℕ) : Prop :=
  ∃ u : LB.Gen ((LB.LinComb a.M.L.L (K := Fin 2) ![((toUnit a.B ≫ c) * 𝟙 a.B).left, 𝟙 a.B.left] ![-1, 1]).pull
      ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ

open GlobalTheory.SplitTorus

theorem isGrpPullback_unit' {S S' : Scheme.{0}} (f : S' ⟶ S) : IsGrpPullback (𝟙_ (Over S')) (𝟙_ (Over S)) f f :=
  ⟨IsPullback.of_vert_isIso (fst := f) (snd := 𝟙 S') (f := 𝟙 S) (g := f) ⟨by simp⟩, fun T x y x₀ y₀ hx _ => by
    rw [toUnit_unique (x₀ * y₀) x₀, toUnit_unique (x * y) x, hx]⟩

theorem isCPPullback_unit {S S' : Scheme.{0}} (f : S' ⟶ S) :
    IsCPPullback (CP.triv (𝟙_ (Over S'))) (CP.triv (𝟙_ (Over S))) f f := by
  refine ⟨isGrpPullback_unit' f, ⟨fun _ => 1⟩, ⟨fun _ _ _ => toUnit_unique _ _, ?_, ?_⟩⟩
  · rw [isGen_iff]
    intro Y r y j j' k k' _ _ _ _
    let w : LB.Iso (CP.triv (𝟙_ (Over S'))).L.L ((CP.triv (𝟙_ (Over S))).L.L.pull f) :=
      ⟨fun _ => 1⟩
    have h : ∀ a b, gw w r y a b = 1 := fun _ _ => map_one _
    have hj : gm (r ≫ f) y _ ((CP.triv (𝟙_ (Over S))).L.L.g j j') = 1 := map_one _
    have hk : gm r y _ ((CP.triv (𝟙_ (Over S'))).L.L.g k k') = 1 := map_one _
    rw [h j k, h j' k', hj, hk, inv_one, _root_.mul_one, _root_.mul_one]
  · intro T z J' J _ _ W hW
    have hW1 : ∀ x, W x = 1 := fun x => (hW x).trans (map_one _)
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · rw [hW1, _root_.one_mul]
      exact (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm
    · rw [hW1, hW1, _root_.mul_one, _root_.one_mul]
      exact (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm
    · simp only [id_eq, hW1, _root_.mul_one, _root_.one_mul]
      trans 1
      · apply cubV_trivCub
      · symm
        apply cubV_trivCub

def torusTQ {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X] :
    TQ ((Over.pullback f).obj (splitTorus S X)) X where
  B := 𝟙_ (Over S')
  isAb := isAbelianScheme_unit S'
  q := toUnit _
  i := (bcIso f X).hom
  q_hom := inferInstance
  i_hom := inferInstance
  q_flat := by
    rw [Rosenlicht.toUnit_left]
    have := Diag.flat_hom S X
    show Flat (pullback.snd (splitTorus S X).hom f); infer_instance
  q_surj := by
    rw [Rosenlicht.toUnit_left]
    have := Diag.surjective_hom S X
    show Surjective (pullback.snd (splitTorus S X).hom f); infer_instance
  q_affine := by
    rw [Rosenlicht.toUnit_left]
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (splitTorus S X).hom f) (Diag.isAffineHom_hom S X)
  isKernel := by
    have : IsIso (η[𝟙_ (Over S')]) := by rw [toUnit_unique η[𝟙_ (Over S')] (𝟙 _)]; infer_instance
    exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
  loc _ χ := ⟨⊤, trivial, chV (bcIso f X).inv χ, isWt_of_retraction (bcIso f X).inv (bcIso f X).hom_inv_id χ⟩

def torusTower (I : Ideal R) (X : Type) [AddCommGroup X] :
    TowerR I (CP.triv (splitTorus (Spec (CommRingCat.of R)) X)) X where
  l e :=
    let Q := torusTQ (thick R I e) X
    ⟨Q, CP.triv _, isLevelCP_triv I e _,
      { M := CP.triv Q.B
        w := ⟨fun _ => 1⟩
        map := by
          have := Q.q_hom
          refine ⟨toBase_mul_of_isMonHom Q.q _, ?_, ?_⟩
          · rw [isGen_iff]
            intro Y r y j j' k k' _ _ _ _
            let w : LB.Iso (CP.triv (thickObj R I e (splitTorus (Spec (CommRingCat.of R)) X))).L.L
                ((CP.triv Q.B).L.L.pull Q.q.left) := ⟨fun _ => 1⟩
            have h : ∀ a b, gw w r y a b = 1 := fun _ _ => map_one _
            have hj : gm (r ≫ Q.q.left) y _ ((CP.triv Q.B).L.L.g j j') = 1 := map_one _
            have hk : gm r y _ ((CP.triv (thickObj R I e (splitTorus (Spec (CommRingCat.of R)) X))).L.L.g k k') = 1 :=
              map_one _
            rw [h j k, h j' k', hj, hk, inv_one, _root_.mul_one, _root_.mul_one]
          · intro T z J' J _ _ W hW
            have hW1 : ∀ x, W x = 1 := fun x => (hW x).trans (map_one _)
            refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
            · rw [hW1, _root_.one_mul]
              exact (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm
            · rw [hW1, hW1, _root_.mul_one, _root_.one_mul]
              exact (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm
            · simp only [id_eq, hW1, _root_.mul_one, _root_.one_mul]
              trans 1
              · apply cubV_trivCub
              · symm
                apply cubV_trivCub }⟩
  tor e := by
    rw [torusCompat_iff]
    refine pullback.hom_ext ?_ ?_
    · show (bcMap _ X ≫ (bcIso (thick R I (e + 1)) X).hom.left) ≫ pullback.fst _ _ =
        ((bcIso (thick R I e) X).hom.left ≫ thickMap R I e _) ≫ pullback.fst _ _
      rw [Category.assoc, bcIso_hom_fst, ← bcMap_comp, thickTrans_comp, Category.assoc]
      erw [pullback.lift_fst]
      rw [Category.comp_id, bcIso_hom_fst]
    · show (bcMap _ X ≫ (bcIso (thick R I (e + 1)) X).hom.left) ≫ pullback.snd _ _ =
        ((bcIso (thick R I e) X).hom.left ≫ thickMap R I e _) ≫ pullback.snd _ _
      rw [Category.assoc, Category.assoc]
      have h₁ : (bcIso (thick R I (e + 1)) X).hom.left ≫ pullback.snd _ _ = _ := Over.w (bcIso (thick R I (e + 1)) X).hom
      have h₂ : (bcIso (thick R I e) X).hom.left ≫ pullback.snd _ _ = _ := Over.w (bcIso (thick R I e) X).hom
      have h₃ : thickMap R I e (splitTorus (Spec (CommRingCat.of R)) X) ≫ pullback.snd _ _ =
          pullback.snd _ _ ≫ thickTrans R I e := pullback.lift_snd _ _ _
      rw [h₁, h₃, ← Category.assoc, h₂, bcMap_hom]
  β e := thickTrans R I e
  β_pb e := isCPPullback_unit _
  β_q e := by
    show (toUnit _ : _ ⟶ 𝟙_ (Over _)).left ≫ _ = _ ≫ (toUnit _ : _ ⟶ 𝟙_ (Over _)).left
    have h₃ : thickMap R I e (splitTorus (Spec (CommRingCat.of R)) X) ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := pullback.lift_snd _ _ _
    exact (congrArg (· ≫ thickTrans R I e) (Rosenlicht.toUnit_left _)).trans
      (h₃.symm.trans (congrArg (thickMap R I e _ ≫ ·)
        (Rosenlicht.toUnit_left (thickObj R I (e + 1) (splitTorus (Spec (CommRingCat.of R)) X))).symm))

def torusAlg (I : Ideal R) (X : Type) [AddCommGroup X] : (torusTower I X).Alg where
  B := 𝟙_ _
  isAb := isAbelianScheme_unit _
  M := CP.triv _
  ample := (Inh.zeroPolAV _).ample
  b e := thick R I e
  b_pb e := isCPPullback_unit (thick R I e)
  b_β e := thickTrans_comp R I e

theorem exists_gen_pull_triv {Y Z : Scheme.{0}} (φ : Fin 2 → (Y ⟶ Y)) (ε : Fin 2 → ℤ) (r : Z ⟶ Y) (u : Γ(Z, ⊤)ˣ) :
    ∃ t : LB.Gen ((LB.LinComb (Inh.trivLB Y) φ ε).pull r), t.IsGen ∧ ∀ j, t.s j = res le_top u := by
  let o : LB.Gen ((LB.LinComb (Inh.trivLB Y) φ ε).pull r) := ⟨fun _ => 1⟩
  have ho : o.IsGen := fun i j => by
    have g1 : ((LB.LinComb (Inh.trivLB Y) φ ε).pull r).g i j = 1 := by
      have key : ∀ (N : LB Y), (∀ a b, N.g a b = 1) → ∀ a b, (N.pull r).g a b = 1 := fun N hN a b => by
        dsimp only [LB.pull, LB.LinComb]
        simp only [hN]
        rw [Fintype.prod_unique, zpow_one]; erw [map_one, map_one]; rfl
      exact key _ (Inh.linComb_triv_g φ ε) i j
    rw [g1, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm
  exact ⟨scaleGen u o, scaleGen_isGen u ho, fun j => _root_.mul_one _⟩


omit [IsLocalRing R] in
theorem torusAlg_repWt (I : Ideal R) (X : Type) [AddCommGroup X] (χ : X) (e : ℕ) :
    (torusAlg I X).RepWt 1 χ e := by
  have hu := isWt_of_retraction (i := (bcIso (thick R I e) X).hom) (bcIso (thick R I e) X).inv
    (bcIso (thick R I e) X).hom_inv_id χ
  obtain ⟨t, ht, hs⟩ := exists_gen_pull_triv
    ![((toUnit (torusAlg I X).B ≫ 1) * 𝟙 (torusAlg I X).B).left, 𝟙 (torusAlg I X).B.left] ![-1, 1]
    (((torusTower I X).l e).Q.q.left ≫ (torusAlg I X).b e) (chV (bcIso (thick R I e) X).inv χ)
  exact ⟨t, ht, fun j => (congrArg (fun a => IsWt _ _ (Units.val a) χ) (hs j)).mpr (hu.res le_top)⟩

end GlobalTheory.LN
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.UU
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G'] [IsCommMonObj G']

structure Cmp (φ : R →+* V) (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) where

  pb : IsGrpPullback G' G (spMap φ) F

  wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)

  wL_map : IsCPMap U'.P U.P (spMap φ) F pb.1.w wL

  β : D'.P.A.left ⟶ D.P.A.left

  pbB : IsGrpPullback D'.P.A D.P.A (spMap φ) β

  v : LB.Iso D'.P.L (D.P.L.pull β)

  v_gen : v.IsGen

  xe : D'.X ≃+ D.X

  c_pr : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left

  lev : ∀ (e : ℕ) (Z : Scheme.{0}) (x' : Z ⟶ (thickObj V I' e G').left) (x : Z ⟶ (thickObj R I e G).left),
    x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F →
    x' ≫ (U'.gt e).pG.left ≫ β = x ≫ (U.gt e).pG.left ∧
    ∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' →
      (∀ χ : D'.X, val ((U.gt e).t (xe χ)) x z J = val ((U'.gt e).t χ) x' z J' *
        ∏ k : Fin 4, gw v (x' ≫ D'.Oφ (U'.gt e).pG χ k) z (J (x' ≫ D'.Oφ (U'.gt e).pG χ k ≫ β))
          (J' (x' ≫ D'.Oφ (U'.gt e).pG χ k)) ^ Oinvε k) ∧
      ∀ (k : U.P.L.L.ι) (k' : U'.P.L.L.ι), (fstG I e G).left (x z) ∈ U.P.L.L.U k → (fstG I' e G').left (x' z) ∈ U'.P.L.L.U k' →
        gw v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) *
            gw (U'.w e) x' z (J' (x' ≫ (U'.gt e).pG.left)) (fun _ => k') =
          gw (U.w e) x z (J (x ≫ (U.gt e).pG.left)) (fun _ => k) * gw wL (x' ≫ (fstG I' e G').left) z k k'

  map_le : I.map φ ≤ I' := by first | assumption | exact (Ideal.map_id _).le

def Under {D₀ : DegData R I} (U : PreU I D₀.toPre A G) (U₀ : UnifPre I D₀ A G) : Prop :=
  U.gen = U₀.gen ∧ U.P.L = U₀.LG ∧ HEq U.P.c U₀.cubG ∧ HEq U.P.sym U₀.symG ∧ U.gt = U₀.gt ∧ HEq U.w U₀.w

abbrev withPsi (D : DegPre R) (psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)))
    (h : ∀ χ, (psi χ).IsGen) : DegPre R := setPsi D psi h

namespace Cmp


omit [IsDomain R] in
theorem spMap_ringHom_id : spMap (RingHom.id R) = 𝟙 _ := by
  simp [spMap]

theorem grpPullback_id {S : Scheme.{0}} (H : Over S) [GrpObj H] {f : S ⟶ S} (hf : f = 𝟙 S) :
    IsGrpPullback H H f (𝟙 H.left) := by
  subst hf
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  have hq : (𝟙 H : H ⟶ H).left ≫ H.hom = H.hom ≫ 𝟙 S := by simp
  have e₁ : x₀ = toBase hq x := Over.OverMorphism.ext hx
  have e₂ : y₀ = toBase hq y := Over.OverMorphism.ext hy
  rw [e₁, e₂, ← toBase_mul_of_isMonHom (𝟙 H) hq]
  rfl

theorem cpMap_id {S : Scheme.{0}} {H : Over S} [GrpObj H] [IsCommMonObj H] (P : CP H) {f : S ⟶ S} (hf : f = 𝟙 S)
    (hw : 𝟙 H.left ≫ H.hom = H.hom ≫ f) : IsCPMap P P f (𝟙 H.left) hw (idIso P.L.L) := by
  subst hf
  exact IsCPMap.id P

theorem mono_fstG (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have hs : Function.Surjective (Ideal.Quotient.mk (I ^ (e + 1))) := Ideal.Quotient.mk_surjective
  have : Epi (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) := ConcreteCategory.epi_of_surjective _ hs
  have : Mono (thick R I e) := Scheme.Spec.map_mono (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))).op
  exact (inferInstance : Mono (pullback.fst G.hom (thick R I e)))

def refl (U : PreU I D A G) : Cmp (RingHom.id R) U U (𝟙 G.left) where
  pb := grpPullback_id G spMap_ringHom_id
  wL := idIso U.P.L.L
  wL_map := cpMap_id U.P spMap_ringHom_id _
  β := 𝟙 _
  pbB := grpPullback_id D.P.A spMap_ringHom_id
  v := idIso D.P.L
  v_gen := idIso_isGen D.P.isLB
  xe := AddEquiv.refl _
  c_pr x := by rw [spMap_ringHom_id]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  lev e Z x' x hx := by
    have := mono_fstG I e G
    rw [Category.comp_id, cancel_mono] at hx
    subst hx
    refine ⟨by rw [Category.comp_id], fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
    · refine (val_change ((U.gt e).t_gen χ) x hJ hJ').trans ((mul_comm _ _).trans (congrArg _ ?_))
      refine Finset.prod_congr rfl fun k _ => congrArg (· ^ _) ?_
      rw [Category.comp_id, gw_idIso _ _ _ (hJ _) (hJ' _)]
    · rw [gw_idIso _ _ _ (hJ _) (hJ' _), gw_idIso U.P.L.L (x ≫ (fstG I e G).left) z hk hk']
      have h := (isGen_iff (U.w e)).1 (U.w_gen e) Z x z (J (x ≫ (U.gt e).pG.left)) (J' (x ≫ (U.gt e).pG.left))
        (fun _ => k) (fun _ => k') (hJ (x ≫ (U.gt e).pG.left)) (hJ' (x ≫ (U.gt e).pG.left))
        (mem_pull.2 hk) (mem_pull.2 hk')
      have g := gm_pull_g U.P.L.L (fstG I e G).left x z (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')
      rw [h, g]
      exact (congrArg (· * _) (inv_mul_cancel_right _ _).symm).trans (mul_right_comm _ _ _)

variable {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}

theorem pow_le (C : Cmp φ U U' F) (e : ℕ) : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono C.map_le _

def baseMap (C : Cmp φ U U' F) (e : ℕ) :
    Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  spMap (Ideal.quotientMap (I' ^ (e + 1)) φ (C.pow_le e))

theorem baseMap_thick (C : Cmp φ U U' F) (e : ℕ) : C.baseMap e ≫ thick R I e = thick V I' e ≫ spMap φ := by
  simp only [baseMap, thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

def levMap (C : Cmp φ U U' F) (e : ℕ) : (thickObj V I' e G').left ⟶ (thickObj R I e G).left :=
  pullback.lift ((fstG I' e G').left ≫ F) (pullback.snd G'.hom (thick V I' e) ≫ C.baseMap e) (by
    simp only [Category.assoc]
    rw [C.pb.1.w, C.baseMap_thick]
    exact pullback.condition_assoc (f := G'.hom) (g := thick V I' e) _)

theorem levMap_fst (C : Cmp φ U U' F) (e : ℕ) : C.levMap e ≫ (fstG I e G).left = (fstG I' e G').left ≫ F :=
  pullback.lift_fst _ _ _

end Cmp

end GlobalTheory.LN
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.UU

def HypW {B : Scheme.{0}} (G : Over B) [GrpObj G] [IsCommMonObj G] (L : LB G.left) : Prop :=
  ∃ w wd : G ⟶ G, IsMonHom w ∧ IsMonHom wd ∧ w * wd = 𝟙 G ∧ LBIso L (cubeLB G ![𝟙 G, w] L) ∧
    LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ wd] L)

def ToATotal {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∀ p : QkPt D.toPre F k, ∃ x, QkToAkU U F k p x

def USt : Prop := AllSet fun {V} _ _ _ {A} {G} _ _ s =>
  ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G),
    U.LG = s.P.L ∧ U.gen = s.gen ∧ ToATotal U.toUnifPre
end GlobalTheory.LN
end
end
