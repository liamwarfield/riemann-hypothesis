module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueRigMulRight
section -- merged from Development.AbelianVarietyTheory.BlockTheory.CMModuli.CubicalSymmetricTriv
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def thirdDiff {A U : Type} [CommGroup A] [CommGroup U] (f : A → U) (x y w : A) : U :=
  f (x * y * w) * (f (x * y))⁻¹ * (f (x * w))⁻¹ * (f (y * w))⁻¹ * f x * f y * f w * (f 1)⁻¹

section Sym

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev symLB (L : LB G.left) : LB G.left :=
  LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]

variable {G}

def rigV (L : RigLB G) {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) :
    (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) L.rig (toUnit T).left z J

def symV {L : LB G.left} (σ : LB.Gen (symLB G L)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (x : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) σ x.left z J

variable (G)

structure CubSym where

  L : RigLB G

  cub : CubicalStr G L

  sym : LB.Gen (symLB G L.L)
  sym_gen : sym.IsGen
  sym_rig : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L)
  sym_cub : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ x y w : T ⟶ G, cubV cub z J x⁻¹ y⁻¹ w⁻¹ = thirdDiff (symV sym z J) x y w * cubV cub z J x y w

variable {G}

end Sym

section Iso

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G']
  [GrpObj G] [IsCommMonObj G]

end Iso

section Triv

variable {S : Scheme.{0}} {H G : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj G] [IsCommMonObj G]

abbrev lamOn (i : H ⟶ G) (L : LB G.left) : LB (H ⊗ G).left :=
  LB.LinComb L (K := Fin 4)
    ![((fst H G ≫ i) * snd H G).left, (fst H G ≫ i).left, (snd H G).left, (1 : H ⊗ G ⟶ G).left]
    ![1, -1, -1, 1]

def lamV {i : H ⟶ G} {L : LB G.left} (s : LB.Gen (lamOn i L)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (t : T ⟶ H) (x : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) s (lift t x).left z J

structure IsBiextTriv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) [IsMonHom i]
    (s : LB.Gen (lamOn i L.L)) : Prop where
  gen : s.IsGen
  law₁ : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ (t t' : T ⟶ H) (x : T ⟶ G), lamV s z J (t * t') x =
      cubV c z J (t ≫ i) (t' ≫ i) x * lamV s z J t x * lamV s z J t' x
  law₂ : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ (t : T ⟶ H) (x x' : T ⟶ G), lamV s z J t (x * x') =
      cubV c z J (t ≫ i) x x' * lamV s z J t x * lamV s z J t x'

def trivV {i : H ⟶ G} {L : LB G.left} (σ : LB.Gen (L.pull i.left)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (t : T ⟶ H) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) σ t.left z J

structure IsCubTriv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) [IsMonHom i]
    (σ : LB.Gen (L.L.pull i.left)) : Prop where
  gen : σ.IsGen
  rig : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    trivV σ z J 1 = rigV L z J
  cub : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ t t' t'' : T ⟶ H,
      thirdDiff (trivV σ z J) t t' t'' = cubV c z J (t ≫ i) (t' ≫ i) (t'' ≫ i)

def IsEven (L : CubSym G) (i : H ⟶ G) [IsMonHom i] (σ : LB.Gen (L.L.L.pull i.left)) : Prop :=
  ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.L.ι), Good L.L.L z J →
    ∀ t : T ⟶ H, trivV σ z J t⁻¹ = symV L.sym z J (t ≫ i) * trivV σ z J t

variable {B : Over S} [GrpObj B] [IsCommMonObj B]

end Triv

section Pairing

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}
  (c : CubicalStr G L)

end Pairing

section Torus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

def charV (χ : X) {T : Over S} (z : T.left) (t : T ⟶ splitTorus S X) : (T.left.presheaf.stalk z)ˣ :=
  gm t.left z ⊤ (charUnit S X χ)

variable {B : Over S} [GrpObj B]

structure IsTorusExt (i : splitTorus S X ⟶ G) (q : G ⟶ B) : Prop where
  free : Module.Free ℤ X
  finite : Module.Finite ℤ X
  comm : IsCommMonObj G
  abelian : IsAbelianScheme B
  i_hom : IsMonHom i
  q_hom : IsMonHom q
  isKernel : IsPullback i (toUnit _) q (η[B])
  locTriv : ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧
    ∃ r : V.toScheme ⟶ G.left, r ≫ q.left = V.ι

end Torus

section Examples

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def trivLB (Y : Scheme.{0}) : LB Y := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

def trivGen {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ Y)) (ε : K → ℤ) :
    LB.Gen (LB.LinComb (trivLB Y) φ ε) := ⟨fun _ => 1⟩

theorem trivGen_isGen {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ Y)) (ε : K → ℤ) :
    (trivGen φ ε).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Finset.prod_eq_one fun _ _ =>
    (congrArg (· ^ _) ((congrArg _ (map_one _)).trans (map_one _))).trans (one_zpow _))
    (map_one _)).trans (_root_.mul_one _)).symm

theorem val_trivGen {Y Z W : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ Y)) (ε : K → ℤ)
    (r : W ⟶ Z) (z : W) (J) : val (trivGen φ ε) r z J = 1 := map_one _

def trivRig : RigLB G where
  L := trivLB _
  rig := trivGen _ _
  isLB := ⟨by simp [trivLB], fun _ => map_one _, fun _ _ _ =>
    ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).trans (map_one _).symm⟩
  rigGen := trivGen_isGen _ _

def trivCubSym : CubSym G where
  L := trivRig G
  cub :=
    { t := trivGen _ _
      isGen := trivGen_isGen _ _
      face := fun _ => corr_of_val (trivRig G).isLB fun _ _ hJ =>
        (val_pull hJ _ _ _).trans ((val_trivGen _ _ _ _ _).trans (val_one _).symm)
      cubeSymmetric_swap_first := corr_of_val (trivRig G).isLB fun _ _ hJ =>
        (val_trivGen _ _ _ _ _).trans ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)).symm
      cubeSymmetric_swap_last := corr_of_val (trivRig G).isLB fun _ _ hJ =>
        (val_trivGen _ _ _ _ _).trans ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)).symm
      cocycle := corr_of_val (trivRig G).isLB fun _ _ hJ =>
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _))
          ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)))).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _))
          ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)))).symm }
  sym := trivGen _ _
  sym_gen := trivGen_isGen _ _
  sym_rig := corr_of_val (trivRig G).isLB fun _ _ hJ =>
    (val_pull hJ _ _ _).trans ((val_trivGen _ _ _ _ _).trans (val_one _).symm)
  sym_cub := fun T z J _ x y w => by
    have a : ∀ x : T ⟶ G, symV (L := (trivRig G).L) (trivGen _ _) z J x = 1 := fun _ => val_trivGen _ _ _ _ _
    simp only [thirdDiff, a, inv_one, _root_.mul_one, _root_.one_mul]
    exact (val_trivGen _ _ _ _ _).trans (val_trivGen _ _ _ _ _).symm

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
end
end

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CubCompare
variable {S S' : Scheme.{0}}

section Gen
variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

end Gen

section Pack
variable {G : Over S} [GrpObj G] [IsCommMonObj G]

end Pack

section Maps
variable {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

end Maps

section Triv
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]


variable {L : RigLB G} {i : H ⟶ G}




variable {c : CubicalStr G L} [IsMonHom i]


end Triv

section Wt
variable {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem gs_appLE {Y Z : Scheme.{0}} (r : Z ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ(Y, V)) (z : Z) :
    gs (𝟙 Z) z ⊤ ((r.appLE V ⊤ h).hom u) = gs r z V u :=
  (gs_res (𝟙 Z) z h trivial _).trans ((gs_pull (𝟙 Z) r z V (h trivial) u).trans (by rw [Category.id_comp]))

theorem gs_comp {Y Z Z' : Scheme.{0}} (ρ : Z' ⟶ Z) (r : Z ⟶ Y) (V : Y.Opens) (z : Z') (h : r (ρ z) ∈ V) (u : Γ(Y, V)) :
    gs (ρ ≫ r) z V u = (ρ.stalkMap z).hom (gs r (ρ z) V u) := by
  rw [gs_eq (ρ ≫ r) z V h, gs_eq r _ V h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ V) z h _).symm

theorem isWt_iff_germ (i : splitTorus S X ⟶ G) (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X) :
    IsWt i V u χ ↔ ∀ (T : Over S) (z : T.left) (t : T ⟶ splitTorus S X) (x : T ⟶ G), x.left z ∈ V →
      ((t ≫ i) * x).left z ∈ V → gs ((t ≫ i) * x).left z V u = (charV χ z t).val * gs x.left z V u := by
  have key : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V) (z : Z.left),
      gs (𝟙 Z.left) z ⊤ (t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u) =
        (charV χ z t).val * gs g.left z V u := fun Z t g h₂ z => by
    rw [gs_mul _ z ⊤ trivial, gs_appLE, ← chV_val, gs_unit _ z ⊤ trivial, charV, gm_charUnit]
  constructor
  · intro h T z t x hx hx'
    let O : T.left.Opens := x.left ⁻¹ᵁ V ⊓ ((t ≫ i) * x).left ⁻¹ᵁ V
    let ρ : Over.mk (O.ι ≫ T.hom) ⟶ T := Over.homMk O.ι rfl
    have e : ((ρ ≫ t) ≫ i) * (ρ ≫ x) = ρ ≫ ((t ≫ i) * x) := by rw [MonObj.comp_mul, Category.assoc]
    have h₁ : ⊤ ≤ (((ρ ≫ t) ≫ i) * (ρ ≫ x)).left ⁻¹ᵁ V := by rw [e]; exact fun y _ => y.2.2
    have h₂ : ⊤ ≤ (ρ ≫ x).left ⁻¹ᵁ V := fun y _ => y.2.1
    have a := congrArg (gs (𝟙 _) (⟨z, hx, hx'⟩ : O) ⊤) (h _ (ρ ≫ t) (ρ ≫ x) h₁ h₂)
    erw [key, gs_appLE] at a
    rw [e] at a
    unfold charV at a
    erw [← gs_unit _ _ ⊤ trivial] at a
    have inj : ∀ y : O.toScheme, Function.Injective (O.ι.stalkMap y).hom := fun y =>
      (ConcreteCategory.bijective_of_isIso _).1
    apply inj ⟨z, hx, hx'⟩
    rw [charV, ← gs_unit _ _ ⊤ trivial]
    exact ((gs_comp O.ι _ V ⟨z, hx, hx'⟩ hx' u).symm.trans a).trans ((congrArg₂ (· * ·)
      (gs_comp O.ι t.left ⊤ ⟨z, hx, hx'⟩ trivial _) (gs_comp O.ι x.left V ⟨z, hx, hx'⟩ hx u)).trans (map_mul _ _ _).symm)
  · intro h Z t g h₁ h₂
    refine fn_ext fun z _ => ?_
    rw [key, gs_appLE]
    exact h Z z t g (h₂ trivial) (h₁ trivial)

end Wt

section Ext
variable {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

variable {B : Over S} [GrpObj B]


end Ext

section Desc
variable {G H B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] [GrpObj B] [IsCommMonObj B]
  {i : H ⟶ G} [IsMonHom i] {q : G ⟶ B} [IsMonHom q] {P : CP G} {M : CP B} {w : LB.Iso P.L.L (M.L.L.pull q.left)}



end Desc

end GlobalTheory.CubCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueWeightDecompositionRaynaudAffine
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtDec

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O}

theorem cv_act (Y : Ray oa) {T : Over (Sp R)} (t : T ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) (x : T ⟶ Y.H) (χ : Q.X)
    (y : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L y J) :
    (GlobalTheory.TorusModel.cv (Y.Φ T ((t ≫ Y.i) * x)) χ y J : T.left.presheaf.stalk y) =
      gs (𝟙 T.left) y ⊤ (t.left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val) *
        GlobalTheory.TorusModel.cv (Y.Φ T x) χ y J := by
  have h := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x (t ≫ Y.i))).2 χ y J hJ
  have C : IsCub (DVR.th Q (T := T) y J) := isCub_cubV Q.cub hJ
  rw [(Y.Φ_i t).1, C.face₃, _root_.mul_one] at h
  rw [mul_comm (t ≫ Y.i) x, h, Units.val_mul, (Y.Φ_i t).2 χ y J hJ, _root_.mul_comm]
  exact congrArg (fun s => gs (𝟙 T.left) y ⊤ s * _) (GlobalTheory.SplitTorusPoints.coord_single t χ)

theorem preimage_stable (Y : Ray oa) (W : Q.P.A.left.Opens) :
    (snd (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H).left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) ≤
      ((fst (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H ≫ Y.i) * snd (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H).left ⁻¹ᵁ
        (Y.q.left ⁻¹ᵁ W) := by
  have := Y.q_linear.isMonHom
  exact fun p hp => GlobalTheory.LevelExpansion.act_mem Y.isKernel _ _ p hp

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec


open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv in
theorem isAffineHom_q : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa), IsAffineHom Y.q.left := by
  intro R _ _ D O _ _ _ oa Y
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem isWt_of_uu : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (V : Y.H.left.Opens) (u : Γ(Y.H.left, V)) (χ : Q.X),
    GlobalTheory.UU.IsWt Y.i V u χ → IsWt Y χ V u := by
  intro R _ _ Q O _ _ _ oa Y V u χ h S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have w : (x' * x⁻¹) ≫ Y.q = toUnit _ ≫ η[Q.P.A] := by
    rw [← Hom.one_def, MonObj.mul_comp, hq, ← MonObj.mul_comp, mul_inv_cancel, MonObj.one_comp]
  let t := Y.isKernel.lift (x' * x⁻¹) (toUnit _) w
  have ht : t ≫ Y.i = x' * x⁻¹ := Y.isKernel.lift_fst _ _ _
  have hx' : (t ≫ Y.i) * x = x' := by rw [ht, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  have key : t.left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c χ) := fn_ext fun y _ => by
    choose J hJ using fun ψ : Sp S ⟶ Q.P.A.left => exists_chart Q.P.isLB (ψ y)
    have e1 := cv_act Y t x χ y J hJ
    rw [hx'] at e1
    have e2 := congrArg Units.val (hc χ y J hJ)
    rw [Units.val_mul, ← gs_unit _ y ⊤ trivial] at e2
    exact (Units.mul_left_inj _).1 (e1.symm.trans e2)
  have h₁ : ⊤ ≤ ((t ≫ Y.i) * x).left ⁻¹ᵁ V := by rw [hx']; exact hV'
  rw [WtAlg.valR_eq' _ _ hV', WtAlg.valR_eq' _ _ hV, ← GlobalTheory.TorusGrading.val_congr hx' h₁ hV' u, h _ t x h₁ hV, map_mul,
    key, Iso.inv_hom_id_apply]

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem uu_of_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (V : Y.H.left.Opens) (u : Γ(Y.H.left, V)) (χ : Q.X),
    IsWt Y χ V u → GlobalTheory.UU.IsWt Y.i V u χ := by
  intro R _ _ Q O _ _ _ oa Y V u χ h
  refine (GlobalTheory.CubCompare.isWt_iff_germ _ _ _ _).2 fun T z t x hx hx' => ?_
  obtain ⟨U, hU, hzU, hUle⟩ := exists_isAffineOpen_mem_and_subset (x := z)
    (U := x.left ⁻¹ᵁ V ⊓ ((t ≫ Y.i) * x).left ⁻¹ᵁ V) ⟨hx, hx'⟩
  let ρ : Sp Γ(T.left, U) ⟶ T.left := hU.fromSpec
  let φ : R →+* Γ(T.left, U) := (Spec.preimage (ρ ≫ T.hom)).hom
  have hφ : ρ ≫ T.hom = spMap φ := by simp [spMap, φ]
  let k : Over.mk (spMap φ) ⟶ T := Over.homMk ρ hφ
  have hr : ∀ p, ρ p ∈ U := fun p => by
    have : ρ p ∈ Set.range ρ := ⟨p, rfl⟩
    rwa [hU.range_fromSpec] at this
  obtain ⟨z', rfl⟩ : z ∈ Set.range ρ := by rw [hU.range_fromSpec]; exact hzU
  have hV₁ : ⊤ ≤ (k ≫ x).left ⁻¹ᵁ V := fun p _ => (hUle (hr p)).1
  have hV₂ : ⊤ ≤ (k ≫ ((t ≫ Y.i) * x)).left ⁻¹ᵁ V := fun p _ => (hUle (hr p)).2
  let c : Q.X → (Γ(T.left, U))ˣ := fun χ' => Units.map (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).hom.hom.toMonoidHom
    (Units.map (k ≫ t).left.appTop.hom.toMonoidHom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ'))
  have hcv : ∀ χ', (unitOn (c χ')).val = (k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ').val := fun χ' => by
    show (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).hom.hom
      ((k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ').val)) = _
    exact Iso.hom_inv_id_apply _ _
  have e : k ≫ ((t ≫ Y.i) * x) = ((k ≫ t) ≫ Y.i) * (k ≫ x) := by rw [MonObj.comp_mul, Category.assoc]
  have hc : ∀ χ' y J, Good Q.P.L y J → val ((Y.Φ _ (k ≫ ((t ≫ Y.i) * x))).s χ') (𝟙 _) y J =
      gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ')) * val ((Y.Φ _ (k ≫ x)).s χ') (𝟙 _) y J := by
    intro χ' y J hJ
    rw [e]
    apply Units.ext
    rw [Units.val_mul, ← gs_unit _ y ⊤ trivial, hcv]
    exact cv_act Y (k ≫ t) (k ≫ x) χ' y J hJ
  have hq : (k ≫ ((t ≫ Y.i) * x)) ≫ Y.q = (k ≫ x) ≫ Y.q := by
    have := Y.q_linear.isMonHom
    exact Over.OverMorphism.ext (by simp only [Over.comp_left, Category.assoc, GlobalTheory.LevelExpansion.act_q Y.isKernel t x])
  have E := h Γ(T.left, U) φ (k ≫ x) (k ≫ ((t ≫ Y.i) * x)) c _ _ rfl rfl hV₁ hV₂ hq hc
  rw [WtAlg.valR_eq' _ _ hV₂, WtAlg.valR_eq' _ _ hV₁] at E
  have E' := congrArg (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom E
  rw [Iso.hom_inv_id_apply, map_mul, Iso.hom_inv_id_apply] at E'
  have E'' := congrArg (gs (𝟙 _) z' ⊤) E'
  rw [GlobalTheory.CubCompare.gs_appLE, gs_mul _ z' ⊤ trivial, GlobalTheory.CubCompare.gs_appLE] at E''
  have hcv' : (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom (c χ : Γ(T.left, U)) =
      (k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val := hcv χ
  have g1 : gs (𝟙 _) z' ⊤ ((k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val) =
      gs (k ≫ t).left z' ⊤ (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val :=
    (gs_pull (𝟙 _) (k ≫ t).left z' ⊤ trivial _).trans (by rw [Category.id_comp])
  rw [hcv', g1] at E''
  apply (ConcreteCategory.bijective_of_isIso (ρ.stalkMap z')).1
  show (ρ.stalkMap z').hom _ = (ρ.stalkMap z').hom _
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv.charV
  rw [map_mul, ← GlobalTheory.CubCompare.gs_comp ρ _ V z' hx' u, ← GlobalTheory.CubCompare.gs_comp ρ _ V z' hx u,
    ← gs_unit _ _ ⊤ trivial, ← GlobalTheory.CubCompare.gs_comp ρ _ ⊤ z' trivial]
  exact E''

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem existsUnique_weights : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (W : Q.P.A.left.Opens), IsAffineOpen W → ∀ f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), ∃! F : Q.X →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), (∀ χ, IsWt Y χ _ (F χ)) ∧ f = F.sum (fun _ t => t) := by
  intro R _ _ Q O _ _ _ oa Y W hW f
  have hi : IsMonHom Y.i := Y.i_linear.isMonHom
  have := isAffineHom_q Y
  obtain ⟨ex, un⟩ := GlobalTheory.functions_graded_by_weights (Sp R) Y.H (GlobalTheory.RayEv.Chr Q) Y.i hi _ (hW.preimage Y.q.left)
    (preimage_stable Y W)
  obtain ⟨a, ha, rfl⟩ := ex f
  refine ⟨a, ⟨fun χ => isWt_of_uu Y _ _ χ (ha χ), rfl⟩, fun F hF => ?_⟩
  let F' : GlobalTheory.RayEv.Chr Q →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W) := F
  have e := un (F' - a) (fun χ => uu_of_isWt Y _ _ χ (WtAlg.isWt_sub (hF.1 χ) (isWt_of_uu Y _ _ χ (ha χ))))
    (by rw [Finsupp.sum_sub_index (fun _ _ _ => rfl)]; exact sub_eq_zero.2 hF.2.symm)
  exact sub_eq_zero.1 e

end GlobalTheory.Heat.WtDec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueWeightDecompositionRaynaudAffineStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_weightDecomposition_raynaud_affine : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (W : Q.P.A.left.Opens), IsAffineOpen W → ∀ f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), ∃! F : Q.X →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), (∀ χ, IsWt Y χ _ (F χ)) ∧ f = F.sum (fun _ t => t) := by
  exact @GlobalTheory.Heat.WtDec.existsUnique_weights
end
