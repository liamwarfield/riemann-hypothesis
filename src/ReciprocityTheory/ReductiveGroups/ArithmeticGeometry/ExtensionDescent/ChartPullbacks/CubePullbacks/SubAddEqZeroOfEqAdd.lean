module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeMapOfThirdFaceEqPushPtLift
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf

open Semi

section Geo

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)

lemma pzero_left {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] (T : Over S₀) :
    (pzero H T).left = T.hom ≫ eSec H := by
  first
    | rfl
    | simp [pzero, eSec]

lemma eSec_hom {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] : eSec H ≫ H.hom = 𝟙 _ := by
  first
    | simp [eSec]
    | (unfold eSec; exact Over.w _)

lemma psum_empty {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀} {n : ℕ}
    (x : Fin n → (T ⟶ H)) : psum H x ∅ = pzero H T := by
  first
    | rfl
    | simp [psum, pzero]

lemma padd_pzero {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀}
    (a : T ⟶ H) : padd H a (pzero H T) = a := by
  first
    | simp [padd, pzero]
    | simp [padd]

lemma psum_single {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀}
    (x : Fin 3 → (T ⟶ H)) (i : Fin 3) : psum H x {i} = x i := by
  fin_cases i <;>
    first
      | exact padd_pzero H _
      | simp [psum, List.finRange, padd_pzero]

lemma cubeMap_lies_over_base : m.F3 ≫ (G3 G).hom = (G3 G').hom ≫ m.e := by
  have h := m.psum_comm ∅
  rw [psum_empty, psum_empty, pzero_left, pzero_left, Category.assoc, m.e_comm] at h
  have h2 := congrArg (· ≫ G.hom) h
  simp only [Category.assoc, eSec_hom, Category.comp_id] at h2
  exact h2.symm

lemma cubeMap_on_coordinates (i : Fin 3) : (x3 G' i).left ≫ m.F = m.F3 ≫ (x3 G i).left := by
  have h := m.psum_comm {i}
  rwa [psum_single, psum_single] at h

theorem m_over : G'.hom ≫ m.e = m.F ≫ G.hom := by
  have key : (x3 G' 0).left ≫ G'.hom ≫ m.e = (x3 G' 0).left ≫ m.F ≫ G.hom := by
    rw [← Category.assoc, Over.w (x3 G' 0), ← cubeMap_lies_over_base, ← Category.assoc, cubeMap_on_coordinates, Category.assoc,
      Over.w (x3 G 0)]
  have hs : (lift (𝟙 G') (lift (𝟙 G') (𝟙 G')) : G' ⟶ G3 G') ≫ x3 G' 0 = 𝟙 G' := by
    simp [x3]
  have hl := congrArg (fun f => f.left) hs
  simp only [Over.comp_left, Over.id_left] at hl
  have h := congrArg (fun f => (lift (𝟙 G') (lift (𝟙 G') (𝟙 G')) : G' ⟶ G3 G').left ≫ f) key
  simp only [← Category.assoc, hl, Category.id_comp] at h
  exact h

def tb {T : Over S'} (y : T ⟶ G') : (Over.map m.e).obj T ⟶ G :=
  Over.homMk (y.left ≫ m.F) (by
    show (y.left ≫ m.F) ≫ G.hom = T.hom ≫ m.e
    rw [Category.assoc, ← m_over, ← Category.assoc, Over.w y])

lemma tb_left {T : Over S'} (y : T ⟶ G') : (tb m y).left = y.left ≫ m.F := rfl

lemma tb_comp {T T' : Over S'} (a : T' ⟶ T) (y : T ⟶ G') :
    tb m (a ≫ y) = (Over.map m.e).map a ≫ tb m y := by
  ext
  simp [tb]

lemma tb_pzero (T : Over S') : tb m (pzero G' T) = pzero G ((Over.map m.e).obj T) := by
  ext
  rw [tb_left, pzero_left, pzero_left, Category.assoc, m.e_comm]
  all_goals first | rfl | simp

lemma psum_01 {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀}
    (x : Fin 3 → (T ⟶ H)) : psum H x {0, 1} = padd H (x 0) (x 1) := by
  first
    | exact congrArg (padd H (x 0)) (padd_pzero H (x 1))
    | (show padd H (x 0) (padd H (x 1) (pzero H T)) = _; rw [padd_pzero])

lemma comp_padd' {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] {T T' : Over S₀} (L : T' ⟶ T)
    (a b : T ⟶ H) : L ≫ padd H a b = padd H (L ≫ a) (L ≫ b) := by
  first
    | (simp only [padd, ← Category.assoc, CartesianMonoidalCategory.comp_lift])
    | (unfold padd; rw [← Category.assoc, CartesianMonoidalCategory.comp_lift])
    | simp [padd]

lemma comp_pzero' {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] {T T' : Over S₀} (L : T' ⟶ T) :
    L ≫ pzero H T = pzero H T' := by
  first
    | simp [pzero]
    | (unfold pzero; simp)

def cubeMapOverAlt : (Over.map m.e).obj (G3 G') ⟶ G3 G := Over.homMk m.F3 (cubeMap_lies_over_base m)

abbrev L3 : (Over.map m.e).obj (G3 G') ⟶ G3 G :=
  lift (tb m (x3 G' 0)) (lift (tb m (x3 G' 1)) (tb m (x3 G' 2)))

lemma cubeMapOver_comp_proj (i : Fin 3) : cubeMapOverAlt m ≫ x3 G i = tb m (x3 G' i) := by
  ext
  first
    | simp [cubeMapOverAlt, tb, cubeMap_on_coordinates]
    | (simp only [cubeMapOverAlt, tb, Over.comp_left, Over.homMk_left]; exact (cubeMap_on_coordinates m i).symm)

lemma cubeMapOver_eq_productMap : cubeMapOverAlt m = L3 m := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa [x3] using cubeMapOver_comp_proj m 0
  · apply CartesianMonoidalCategory.hom_ext
    · simpa [x3] using cubeMapOver_comp_proj m 1
    · simpa [x3] using cubeMapOver_comp_proj m 2

lemma cubeMapOf_thirdFace_eq_pushPt_lift : m.F3 = (L3 m).left := by
  rw [← cubeMapOver_eq_productMap]
  rfl

lemma tb_lift3 {T : Over S'} (a b c : T ⟶ G') :
    (Over.map m.e).map (lift a (lift b c)) ≫ L3 m = lift (tb m a) (lift (tb m b) (tb m c)) := by
  simp only [L3, comp_lift, ← tb_comp]
  simp [x3]

lemma tb_padd {T : Over S'} (y z : T ⟶ G') : tb m (padd G' y z) = padd G (tb m y) (tb m z) := by
  ext
  have hw : lift y (lift z y) ≫ padd G' (x3 G' 0) (x3 G' 1) = padd G' y z := by
    simp [comp_padd', x3]
  have h01 := m.psum_comm {0, 1}
  rw [psum_01, psum_01] at h01
  have h3 := congrArg (fun f => f.left) (tb_lift3 m y z y)
  simp only [Over.comp_left, Over.map_map_left] at h3
  rw [tb_left, ← hw, Over.comp_left, Category.assoc, h01, cubeMapOf_thirdFace_eq_pushPt_lift, ← Category.assoc, h3,
    ← Over.comp_left, comp_padd']
  simp [x3]

lemma lift_triple_comm_pullback {T : Over S'} {T0 : Over S} (L : (Over.map m.e).obj T ⟶ T0) (p q r : T ⟶ G')
    (p0 q0 r0 : T0 ⟶ G) (hp : tb m p = L ≫ p0) (hq : tb m q = L ≫ q0) (hr : tb m r = L ≫ r0) :
    (lift p (lift q r)).left ≫ m.F3 = L.left ≫ (lift p0 (lift q0 r0)).left := by
  rw [cubeMapOf_thirdFace_eq_pushPt_lift]
  have h := congrArg (fun f => f.left) (tb_lift3 m p q r)
  simp only [Over.comp_left, Over.map_map_left] at h
  rw [h, hp, hq, hr, ← comp_lift, ← comp_lift, Over.comp_left]

abbrev L2 : (Over.map m.e).obj (G2 G') ⟶ G2 G := lift (tb m (x2 G' 0)) (tb m (x2 G' 1))

abbrev L4 : (Over.map m.e).obj (G4 G') ⟶ G4 G :=
  lift (tb m (x4 G' 0)) (lift (tb m (x4 G' 1)) (lift (tb m (x4 G' 2)) (tb m (x4 G' 3))))

def pullbackMapSquare : (G2 G').left ⟶ (G2 G).left := (L2 m).left

def pullbackMapFourth : (G4 G').left ⟶ (G4 G).left := (L4 m).left

lemma pullback_proj_square (j : Fin 2) : tb m (x2 G' j) = L2 m ≫ x2 G j := by
  fin_cases j <;> simp [L2, x2]

lemma pullback_proj_cube (j : Fin 3) : tb m (x3 G' j) = L3 m ≫ x3 G j := by
  rw [← cubeMapOver_eq_productMap, cubeMapOver_comp_proj]

lemma pullback_proj_fourth (j : Fin 4) : tb m (x4 G' j) = L4 m ≫ x4 G j := by
  fin_cases j <;> simp [L4, x4]

lemma tb_pzero' {T : Over S'} {T0 : Over S} (L : (Over.map m.e).obj T ⟶ T0) :
    tb m (pzero G' T) = L ≫ pzero G T0 := by
  rw [tb_pzero, comp_pzero']

theorem face_comm (i : Fin 3) :
    (faceMap G' i).left ≫ m.F3 = pullbackMapSquare m ≫ (faceMap G i).left := by
  fin_cases i
  · have h := lift_triple_comm_pullback m (L2 m) (pzero G' (G2 G')) (x2 G' 0) (x2 G' 1) (pzero G (G2 G)) (x2 G 0) (x2 G 1) (tb_pzero' m (L2 m)) (pullback_proj_square m 0) (pullback_proj_square m 1)
    first
      | exact h
      | (simp only [faceMap, pullbackMapSquare]; exact h)
      | simpa [faceMap, pullbackMapSquare] using h
  · have h := lift_triple_comm_pullback m (L2 m) (x2 G' 0) (pzero G' (G2 G')) (x2 G' 1) (x2 G 0) (pzero G (G2 G)) (x2 G 1) (pullback_proj_square m 0) (tb_pzero' m (L2 m)) (pullback_proj_square m 1)
    first
      | exact h
      | (simp only [faceMap, pullbackMapSquare]; exact h)
      | simpa [faceMap, pullbackMapSquare] using h
  · have h := lift_triple_comm_pullback m (L2 m) (x2 G' 0) (x2 G' 1) (pzero G' (G2 G')) (x2 G 0) (x2 G 1) (pzero G (G2 G)) (pullback_proj_square m 0) (pullback_proj_square m 1) (tb_pzero' m (L2 m))
    first
      | exact h
      | (simp only [faceMap, pullbackMapSquare]; exact h)
      | simpa [faceMap, pullbackMapSquare] using h

theorem swap_first_two_comm :
    (lift (x3 G' 1) (lift (x3 G' 0) (x3 G' 2))).left ≫ m.F3 =
      m.F3 ≫ (lift (x3 G 1) (lift (x3 G 0) (x3 G 2))).left := by
  rw [lift_triple_comm_pullback m (L3 m) (x3 G' 1) (x3 G' 0) (x3 G' 2) (x3 G 1) (x3 G 0) (x3 G 2)
    (pullback_proj_cube m 1) (pullback_proj_cube m 0) (pullback_proj_cube m 2), cubeMapOf_thirdFace_eq_pushPt_lift]

theorem swap_last_two_comm :
    (lift (x3 G' 0) (lift (x3 G' 2) (x3 G' 1))).left ≫ m.F3 =
      m.F3 ≫ (lift (x3 G 0) (lift (x3 G 2) (x3 G 1))).left := by
  rw [lift_triple_comm_pullback m (L3 m) (x3 G' 0) (x3 G' 2) (x3 G' 1) (x3 G 0) (x3 G 2) (x3 G 1)
    (pullback_proj_cube m 0) (pullback_proj_cube m 2) (pullback_proj_cube m 1), cubeMapOf_thirdFace_eq_pushPt_lift]

theorem cube_face_comm (a b c : Fin 4) :
    (lift (x4 G' a) (lift (x4 G' b) (x4 G' c))).left ≫ m.F3 =
      pullbackMapFourth m ≫ (lift (x4 G a) (lift (x4 G b) (x4 G c))).left := by
  rw [show pullbackMapFourth m = (L4 m).left from rfl,
    lift_triple_comm_pullback m (L4 m) _ _ _ _ _ _ (pullback_proj_fourth m a) (pullback_proj_fourth m b) (pullback_proj_fourth m c)]

theorem cube_sum_face_comm (a b c d : Fin 4) :
    (lift (padd G' (x4 G' a) (x4 G' b)) (lift (x4 G' c) (x4 G' d))).left ≫ m.F3 =
      pullbackMapFourth m ≫ (lift (padd G (x4 G a) (x4 G b)) (lift (x4 G c) (x4 G d))).left := by
  have hp : tb m (padd G' (x4 G' a) (x4 G' b)) = L4 m ≫ padd G (x4 G a) (x4 G b) := by
    rw [tb_padd, pullback_proj_fourth, pullback_proj_fourth, comp_padd']
  rw [show pullbackMapFourth m = (L4 m).left from rfl,
    lift_triple_comm_pullback m (L4 m) _ _ _ _ _ _ hp (pullback_proj_fourth m c) (pullback_proj_fourth m d)]

theorem c4p'_comm (a b c d : Fin 4) :
    (lift (x4 G' a) (lift (padd G' (x4 G' b) (x4 G' c)) (x4 G' d))).left ≫ m.F3 =
      pullbackMapFourth m ≫ (lift (x4 G a) (lift (padd G (x4 G b) (x4 G c)) (x4 G d))).left := by
  have hq : tb m (padd G' (x4 G' b) (x4 G' c)) = L4 m ≫ padd G (x4 G b) (x4 G c) := by
    rw [tb_padd, pullback_proj_fourth, pullback_proj_fourth, comp_padd']
  rw [show pullbackMapFourth m = (L4 m).left from rfl,
    lift_triple_comm_pullback m (L4 m) _ _ _ _ _ _ (pullback_proj_fourth m a) hq (pullback_proj_fourth m d)]

lemma tb_inv {T : Over S'} (y : T ⟶ G') : tb m (y ≫ ι[G']) = tb m y ≫ ι[G] := by
  have hm : ∀ {T0 : Over S} (a b : T0 ⟶ G), padd G a b = pzero G T0 → b = a ≫ ι[G] := by
    intro T0 a b hab
    have h1 : (a ≫ ι[G]) * a = 1 := by
      change lift (a ≫ ι[G]) a ≫ μ = toUnit _ ≫ η
      simp
    have h2 : a * b = 1 := by
      change lift a b ≫ μ = toUnit _ ≫ η
      exact hab
    exact (left_inv_eq_right_inv h1 h2).symm
  apply hm
  rw [← tb_padd, ← tb_pzero]
  congr 1
  simp [padd, pzero]

theorem inv_comm : (GrpObj.inv (X := G')).left ≫ m.F = m.F ≫ (GrpObj.inv (X := G)).left := by
  have h := congrArg (fun f => f.left) (tb_inv m (𝟙 G'))
  simpa [tb_left] using h

end Geo

end ReciprocityTheory.ChartRestriction.G.Out.CubePf
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf

open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res'
  base_eq germ_pull germ_pull_pull germ_div)

section Sym

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)

lemma eSec_inv {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] :
    eSec H ≫ (GrpObj.inv (X := H)).left = 𝟙 _ ≫ eSec H := by
  have h : η[H] ≫ GrpObj.inv (X := H) = η[H] := by
    first
    | simp
    | exact GrpObj.one_inv
  rw [Category.id_comp]
  show (η[H] ≫ GrpObj.inv (X := H)).left = η[H].left
  rw [h]

private theorem memW_lemma_2 {X Y : Scheme.{0}} (L : LB X) (φ : PUnit.{1} → (Y ⟶ X))
    (j : PUnit.{1} → L.ι) (x : Y) (h : (φ PUnit.unit).base x ∈ L.U (j PUnit.unit)) :
    x ∈ LB.wchart L φ j := by
  show x ∈ (⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X))
  exact Set.mem_iInter.2 fun k => by cases k; exact h

lemma symLe (L : LB G.left)
    (p : (LB.div ((L.pull m.F).pull (GrpObj.inv (X := G')).left) (L.pull m.F)).ι) :
    (LB.div ((L.pull m.F).pull (GrpObj.inv (X := G')).left) (L.pull m.F)).U p ≤
      m.F ⁻¹ᵁ (LB.div (L.pull (GrpObj.inv (X := G)).left) L).U
        ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit) := by
  intro y hy
  have h0 : (GrpObj.inv (X := G')).left.base y ∈ (L.pull m.F).U (p.1 PUnit.unit) :=
    LB.wchart_le (L.pull m.F) (fun _ : PUnit => (GrpObj.inv (X := G')).left) p.1 PUnit.unit hy.1
  have h1 : m.F.base ((GrpObj.inv (X := G')).left.base y) ∈ L.U (p.1 PUnit.unit PUnit.unit) :=
    LB.wchart_le L (fun _ : PUnit => m.F) (p.1 PUnit.unit) PUnit.unit h0
  have h2 : m.F.base y ∈ L.U (p.2 PUnit.unit) :=
    LB.wchart_le L (fun _ : PUnit => m.F) p.2 PUnit.unit hy.2
  have h3 : (GrpObj.inv (X := G)).left.base (m.F.base y) ∈ L.U (p.1 PUnit.unit PUnit.unit) := by
    rw [← base_eq (inv_comm m) y]
    exact h1
  exact (show m.F.base y ∈ LB.wchart L (fun _ : PUnit => (GrpObj.inv (X := G)).left)
      (fun _ => p.1 PUnit.unit PUnit.unit) ⊓ L.U (p.2 PUnit.unit) from
    ⟨memW_lemma_2 L (fun _ : PUnit => (GrpObj.inv (X := G)).left)
      (fun _ => p.1 PUnit.unit PUnit.unit) (m.F.base y) h3, h2⟩)

def symIso (L : LB G.left) (w₀ : LB.Iso L (L.pull (GrpObj.inv (X := G)).left)) :
    LB.Iso (L.pull m.F) ((L.pull m.F).pull (GrpObj.inv (X := G')).left) where
  s := fun p => res (symLe m L p) (pullU m.F _ (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit),
    p.2 PUnit.unit)))

lemma mul_inv_mul_cancel_comm {M N : Type} [CommGroup M] [CommGroup N] (φ : M →* N)
    (w0p gi gl w0q : M) (B A wp wq : N) (h0 : w0p = gi * gl⁻¹ * w0q) (hwp : wp = φ w0p)
    (hwq : wq = φ w0q) (hB : B = φ gi) (hA : A = φ gl) : wp = B * A⁻¹ * wq := by
  subst h0 hwp hwq hB hA
  simp only [map_mul, map_inv]

private theorem pullU_comp_lemma {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens)
    (x : Γ(X, U)ˣ) : pullU (f ≫ g) U x = pullU f (g ⁻¹ᵁ U) (pullU g U x) := by
  first
  | rfl
  | (ext; simp [pullU])

lemma symIso_isGen (L : LB G.left) (w₀ : LB.Iso L (L.pull (GrpObj.inv (X := G)).left))
    (hw₀ : w₀.IsGen) : (symIso m L w₀).IsGen := by
  intro p p'
  apply unit_ext
  intro y hy
  have hz : m.F.base y ∈ (LB.div (L.pull (GrpObj.inv (X := G)).left) L).U
        ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit) ⊓
      (LB.div (L.pull (GrpObj.inv (X := G)).left) L).U
        ((fun _ => p'.1 PUnit.unit PUnit.unit), p'.2 PUnit.unit) :=
    ⟨symLe m L p hy.1, symLe m L p' hy.2⟩
  have h0 := congrArg (gU (m.F.base y) hz)
    (hw₀ ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit)
      ((fun _ => p'.1 PUnit.unit PUnit.unit), p'.2 PUnit.unit))
  rw [map_mul, gU_res, gU_res] at h0
  first
  | rw [germ_div _ _ _ _ (m.F.base y) hz] at h0
  | simp only [germ_div] at h0
  rw [map_mul, gU_res, gU_res]
  first
  | rw [germ_div _ _ p p' y hy]
  | simp only [germ_div]
  apply mul_inv_mul_cancel_comm (Units.map (m.F.stalkMap y).hom) _ _ _ _ _ _ _ _ h0
  · dsimp only [symIso]
    rw [gU_res, gU_pullU]
  · dsimp only [symIso]
    rw [gU_res, gU_pullU]
  · have hmem3 : (GrpObj.inv (X := G)).left.base (m.F.base y) ∈
        L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit) :=
      ⟨LB.wchart_le L (fun _ : PUnit => (GrpObj.inv (X := G)).left)
          (fun _ => p.1 PUnit.unit PUnit.unit) PUnit.unit hz.1.1,
        LB.wchart_le L (fun _ : PUnit => (GrpObj.inv (X := G)).left)
          (fun _ => p'.1 PUnit.unit PUnit.unit) PUnit.unit hz.2.1⟩
    have hmem1 : m.F.base ((GrpObj.inv (X := G')).left.base y) ∈
        L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit) := by
      rw [base_eq (inv_comm m) y]
      exact hmem3
    refine (germ_pull_pull L m.F (GrpObj.inv (X := G')).left p.1 p'.1 y _ hmem1).trans
      ((gU_pullU_congr (inv_comm m) (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit)) y hmem1 hmem3).trans
      ((congrArg (gU (O := (m.F ≫ (GrpObj.inv (X := G)).left) ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit))) y hmem3)
          (pullU_comp_lemma m.F (GrpObj.inv (X := G)).left (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit)))).trans
      ((gU_pullU m.F ((GrpObj.inv (X := G)).left ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit))) y hmem3 (pullU (GrpObj.inv (X := G)).left (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit)))).trans
      ?_)))
    congr 1
    exact (germ_pull L (GrpObj.inv (X := G)).left (fun _ => p.1 PUnit.unit PUnit.unit)
      (fun _ => p'.1 PUnit.unit PUnit.unit) (m.F.base y)
      (⟨hz.1.1, hz.2.1⟩ : m.F.base y ∈
        (L.pull (GrpObj.inv (X := G)).left).U (fun _ => p.1 PUnit.unit PUnit.unit) ⊓
        (L.pull (GrpObj.inv (X := G)).left).U (fun _ => p'.1 PUnit.unit PUnit.unit))
      hmem3).symm
  · exact (germ_pull L m.F p.2 p'.2 y _
      (show m.F.base y ∈ L.U (p.2 PUnit.unit) ⊓ L.U (p'.2 PUnit.unit) from ⟨hz.1.2, hz.2.2⟩)).trans
      (gU_pullU _ _ _ _ _)

lemma gU_pullU_id {X : Scheme.{0}} (U : X.Opens) (y : X) (hy : y ∈ (𝟙 X) ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    gU y hy (pullU (𝟙 X) U u) = gU y hy u := by
  first
  | rfl
  | (rw [gU_pullU]; simp)

lemma sub_add_eq_zero_of_eq_add {M N : Type} [CommGroup M] [CommGroup N] (φ : M →* N) (x0 y0 z0 : M) (X Y Z : N)
    (h0 : x0 = y0 * z0) (hX : X = φ x0) (hY : Y = φ y0) (hZ : Z = φ z0) : X = Y * Z := by
  subst hX hY hZ h0
  exact map_mul φ y0 z0

lemma gU_linCombIso_unit {X Y : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) (φ₀ : Y ⟶ X)
    (p : (LB.LinComb M (K := PUnit) (fun _ => φ₀) (fun _ => 1)).ι ×
      (LB.LinComb L (K := PUnit) (fun _ => φ₀) (fun _ => 1)).ι) (y : Y)
    (hy : y ∈ (LB.div (LB.LinComb M (K := PUnit) (fun _ => φ₀) (fun _ => 1))
      (LB.LinComb L (K := PUnit) (fun _ => φ₀) (fun _ => 1))).U p)
    (hy' : y ∈ φ₀ ⁻¹ᵁ (LB.div M L).U (p.1 PUnit.unit, p.2 PUnit.unit)) :
    gU y hy ((LB.linCombIso w (K := PUnit) (fun _ => φ₀) (fun _ => 1)).s p) =
      gU y hy' (pullU φ₀ _ (w.s (p.1 PUnit.unit, p.2 PUnit.unit))) := by
  dsimp only [LB.linCombIso]
  first
  | erw [Fintype.prod_unique, zpow_one, gU_res]
  | simp only [Fintype.prod_unique, zpow_one, gU_res]
  all_goals rfl

private theorem gU_pullU_id_lemma_3 {X : Scheme.{0}} (U : X.Opens) (y : X) (hy : y ∈ U)
    (hy' : y ∈ (𝟙 X) ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    gU y hy' (pullU (𝟙 X) U u) = gU y hy u :=
  gU_pullU_id U y hy' u

lemma pt1 (y : (𝟙_ (Over S')).left) :
    m.F.base ((GrpObj.inv (X := G')).left.base ((eSec G').base y)) =
      (GrpObj.inv (X := G)).left.base ((eSec G).base (m.e.base y)) := by
  rw [base_eq (eSec_inv G') y, base_eq (eSec_inv G) (m.e.base y)]
  first
  | exact base_eq m.e_comm y
  | simpa using base_eq m.e_comm y

lemma pt2 (y : (𝟙_ (Over S')).left) :
    m.F.base ((eSec G').base y) = (eSec G).base (m.e.base y) := base_eq m.e_comm y

set_option maxHeartbeats 800000 in
lemma sym_maps (L : RigLB G) (he : eSec G ≫ (GrpObj.inv (X := G)).left = 𝟙 _ ≫ eSec G)
    (w₀ : LB.Iso L.L (L.L.pull (GrpObj.inv (X := G)).left))
    (hm : LB.Gen.Maps (LB.linCombIso w₀ (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L.rig
      (rigPullOf (GrpObj.inv (X := G)).left (𝟙 _) he L.L L.rig)) :
    LB.Gen.Maps (LB.linCombIso (symIso m L.L w₀) (K := PUnit) (fun _ => eSec G') (fun _ => 1))
      (m.rigPull L.L L.rig)
      (rigPullOf (GrpObj.inv (X := G')).left (𝟙 _) (eSec_inv G') (L.L.pull m.F)
        (m.rigPull L.L L.rig)) := by
  intro p
  apply unit_ext
  intro y hy
  have b1 : (eSec G').base y ∈ ((L.L.pull m.F).pull (GrpObj.inv (X := G')).left).U (p.1 PUnit.unit) :=
    LB.wchart_le ((L.L.pull m.F).pull (GrpObj.inv (X := G')).left) (fun _ : PUnit => eSec G') p.1
      PUnit.unit hy.1
  have b2 : (GrpObj.inv (X := G')).left.base ((eSec G').base y) ∈
      (L.L.pull m.F).U (p.1 PUnit.unit PUnit.unit) :=
    LB.wchart_le (L.L.pull m.F) (fun _ : PUnit => (GrpObj.inv (X := G')).left) (p.1 PUnit.unit)
      PUnit.unit b1
  have b3 : m.F.base ((GrpObj.inv (X := G')).left.base ((eSec G').base y)) ∈
      L.L.U (p.1 PUnit.unit PUnit.unit PUnit.unit) :=
    LB.wchart_le L.L (fun _ : PUnit => m.F) (p.1 PUnit.unit PUnit.unit) PUnit.unit b2
  have b4 : (GrpObj.inv (X := G)).left.base ((eSec G).base (m.e.base y)) ∈
      L.L.U (p.1 PUnit.unit PUnit.unit PUnit.unit) := by
    rw [← pt1 m y]
    exact b3
  have c1 : (eSec G').base y ∈ (L.L.pull m.F).U (p.2 PUnit.unit) :=
    LB.wchart_le (L.L.pull m.F) (fun _ : PUnit => eSec G') p.2 PUnit.unit hy.2
  have c2 : m.F.base ((eSec G').base y) ∈ L.L.U (p.2 PUnit.unit PUnit.unit) :=
    LB.wchart_le L.L (fun _ : PUnit => m.F) (p.2 PUnit.unit) PUnit.unit c1
  have c3 : (eSec G).base (m.e.base y) ∈ L.L.U (p.2 PUnit.unit PUnit.unit) := by
    rw [← pt2 m y]
    exact c2
  have d0 : (eSec G).base (m.e.base y) ∈
      (L.L.pull (GrpObj.inv (X := G)).left).U (fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit) ⊓
        L.L.U (p.2 PUnit.unit PUnit.unit) :=
    ⟨memW_lemma_2 L.L (fun _ : PUnit => (GrpObj.inv (X := G)).left)
      (fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit) ((eSec G).base (m.e.base y)) b4, c3⟩
  have d0' : m.e.base y ∈ (eSec G) ⁻¹ᵁ
      (LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit) := d0
  have d1 : y ∈ (eSec G') ⁻¹ᵁ (m.F ⁻¹ᵁ
      (LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) := by
    show m.F.base ((eSec G').base y) ∈
      (L.L.pull (GrpObj.inv (X := G)).left).U (fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit) ⊓
        L.L.U (p.2 PUnit.unit PUnit.unit)
    rw [pt2 m y]
    exact d0
  have hz : m.e.base y ∈
      ((L.L.pull (GrpObj.inv (X := G)).left).pull (eSec G)).U
        (fun _ _ => p.1 PUnit.unit PUnit.unit PUnit.unit) ⊓
      (L.L.pull (eSec G)).U (fun _ => p.2 PUnit.unit PUnit.unit) :=
    ⟨memW_lemma_2 (L.L.pull (GrpObj.inv (X := G)).left) (fun _ : PUnit => eSec G)
        (fun _ _ => p.1 PUnit.unit PUnit.unit PUnit.unit) (m.e.base y) d0.1,
      memW_lemma_2 L.L (fun _ : PUnit => eSec G) (fun _ => p.2 PUnit.unit PUnit.unit) (m.e.base y) c3⟩
  have h0 := congrArg (gU (m.e.base y) hz)
    (hm ((fun _ _ => p.1 PUnit.unit PUnit.unit PUnit.unit), (fun _ => p.2 PUnit.unit PUnit.unit)))
  first
  | rw [id_eq] at h0
  | skip
  rw [map_mul, gU_res, gU_res] at h0
  first
  | rw [id_eq]
  | skip
  rw [map_mul, gU_res, gU_res]
  apply sub_add_eq_zero_of_eq_add (Units.map (m.e.stalkMap y).hom) _ _ _ _ _ _ h0
  · dsimp only [rigPullOf, CubeMap.rigPull]
    refine ((gU_res _ y _ _).trans ((gU_pullU_id _ y _ _).trans ((gU_res _ y _ _).trans
      (gU_pullU m.e _ y _ _)))).trans ?_
    exact (congrArg (Units.map (m.e.stalkMap y).hom.toMonoidHom)
      ((gU_res _ _ _ _).trans (gU_pullU_id_lemma_3 _ _ _ _ _))).symm
  · have hyl : (eSec G').base y ∈ ((L.L.pull m.F).pull (GrpObj.inv (X := G')).left).U (p.1 PUnit.unit) ⊓
        (L.L.pull m.F).U (p.2 PUnit.unit) := ⟨b1, c1⟩
    refine (gU_linCombIso_unit (symIso m L.L w₀) (eSec G') p y _ hyl).trans
      ((gU_pullU_res (eSec G') (symLe m L.L (p.1 PUnit.unit, p.2 PUnit.unit))
          (pullU m.F _ (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit))) y hyl d1).trans
      ((congrArg (gU y d1) (pullU_comp_lemma (eSec G') m.F ((LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)))).symm.trans
      ((gU_pullU_congr m.e_comm ((LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) y d1 d0').trans
      ((congrArg (gU (O := (m.e ≫ eSec G) ⁻¹ᵁ (LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) y d0')
          (pullU_comp_lemma m.e (eSec G) ((LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)))).trans
      ((gU_pullU m.e ((eSec G) ⁻¹ᵁ (LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) y d0' (pullU (eSec G) ((LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)))).trans
      ?_)))))
    exact congrArg (Units.map (m.e.stalkMap y).hom.toMonoidHom) (gU_linCombIso_unit w₀ (eSec G)
      ((fun _ _ => p.1 PUnit.unit PUnit.unit PUnit.unit), (fun _ => p.2 PUnit.unit PUnit.unit))
      (m.e.base y) hz d0').symm
  · dsimp only [CubeMap.rigPull, rigPullOf]
    exact (gU_res _ y _ _).trans (gU_pullU m.e _ y _ _)

theorem sym_pull (L : RigLB G) (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen) :
    L.IsSymmetric → (m.rigLB L hL hr).IsSymmetric := by
  intro h
  unfold RigLB.IsSymmetric at h ⊢
  obtain ⟨he, w, hw, hmaps⟩ := h
  exact ⟨eSec_inv G', symIso m L.L w, symIso_isGen m L.L w hw, sym_maps m L he w hmaps⟩

end Sym

end ReciprocityTheory.ChartRestriction.G.Out.CubePf
