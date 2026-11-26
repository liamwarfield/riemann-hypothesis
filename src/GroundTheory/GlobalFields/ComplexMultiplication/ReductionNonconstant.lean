module

public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionEval
public import GroundTheory.GlobalFields.ComplexMultiplication.DualDescent

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.ReductionComp
section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogeny
section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.ReductionRespectsAdd
namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

section Push

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)

def pushField : ResidueField (gaussRing (gaussCurve W W)) →+* univField (W.map (residue 𝒪)) :=
  (ffCongr (gaussCurve_map_residue W W)).toRingHom.comp
    ((ffMap (gaussResidue W) ((gaussCurve W W).map (residue (gaussRing W)))).comp
      (gaussResidue (gaussCurve W W)))

theorem pushField_residue_algebraMap (g : gaussRing W) :
    pushField W (residue _ (algebraMap (gaussRing W) (gaussRing (gaussCurve W W)) g)) =
      algebraMap (W.map (residue 𝒪)).toAffine.FunctionField _ (gaussResidue W (residue _ g)) := by
  rw [pushField, RingHom.comp_apply, RingHom.comp_apply, gaussResidue_residue_algebraMap,
    ffMap_algebraMap]
  exact ffCongr_algebraMap _ _

theorem pushField_gaussX :
    pushField W (residue _ (gaussX (gaussCurve W W))) = genX _ := by
  rw [pushField, RingHom.comp_apply, RingHom.comp_apply, gaussResidue_gaussX, ffMap_genX]
  exact ffCongr_genX _

theorem pushField_gaussY :
    pushField W (residue _ (gaussY (gaussCurve W W))) = genY _ := by
  rw [pushField, RingHom.comp_apply, RingHom.comp_apply, gaussResidue_gaussY, ffMap_genY]
  exact ffCongr_genY _

end Push

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

abbrev liftField : Type _ :=
  ((gaussCurve W W).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.FunctionField

abbrev liftJ : 𝒪 →+* gaussRing (gaussCurve W W) :=
  (algebraMap (gaussRing W) (gaussRing (gaussCurve W W))).comp (algebraMap 𝒪 (gaussRing W))

theorem liftJ_algebraMap (c : 𝒪) :
    algebraMap K (liftField K W) (algebraMap 𝒪 K c) =
      algebraMap (gaussRing (gaussCurve W W)) (liftField K W) (liftJ W c) := by
  rw [RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply (gaussRing W) (gaussRing (gaussCurve W W)) (liftField K W),
    IsScalarTower.algebraMap_apply (gaussRing W) (W.baseChange K).toAffine.FunctionField
      (liftField K W),
    ← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField K W)]

theorem pushField_comp_residueField_map :
    (pushField W).comp (ResidueField.map (liftJ W)) =
      algebraMap (ResidueField 𝒪) (univField (W.map (residue 𝒪))) := by
  refine RingHom.ext fun c => ?_
  obtain ⟨c, rfl⟩ := residue_surjective c
  rw [RingHom.comp_apply, ResidueField.map_residue, RingHom.comp_apply,
    pushField_residue_algebraMap, gaussResidue_residue_algebraMap,
    ← IsScalarTower.algebraMap_apply]

theorem pushCurve_eq (V : WeierstrassCurve 𝒪) :
    ((V.map (liftJ W)).map (residue _)).map (pushField W) =
      (V.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪))) := by
  show V.map (((pushField W).comp (residue _)).comp (liftJ W)) =
    V.map ((algebraMap (ResidueField 𝒪) _).comp (residue 𝒪))
  have h : ((pushField W).comp (residue _)).comp (liftJ W) =
      (algebraMap (ResidueField 𝒪) (univField (W.map (residue 𝒪)))).comp (residue 𝒪) := by
    rw [← pushField_comp_residueField_map, RingHom.comp_assoc, RingHom.comp_assoc,
      ResidueField.map_comp_residue]
  rw [h]

variable [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))]

def pushPt (V : WeierstrassCurve 𝒪) :
    ((V.map (liftJ W)).map (residue _)).toAffine.Point →+
      ((V.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Point :=
  (pointCongr (pushCurve_eq W V)).toAddMonoidHom.comp (pointMapRing (pushField W) _)

def redU (V : WeierstrassCurve 𝒪) [V.IsElliptic] :
    ((V.baseChange K).baseChange (liftField K W)).toAffine.Point →+
      ((V.map (liftJ W)).map (residue _)).toAffine.Point :=
  (reductionHom (liftField K W) (V.map (liftJ W))).comp
    (pointCongr (map_baseChange_eq_map_of K V (liftJ W) (liftField K W)
      (liftJ_algebraMap K W))).toAddMonoidHom

theorem pushPt_redU_some (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    {x y : gaussRing (gaussCurve W W)}
    (h : ((V.baseChange K).baseChange (liftField K W)).toAffine.Nonsingular
      (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y)) :
    ∃ h' : ((V.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Nonsingular
        (pushField W (residue _ x)) (pushField W (residue _ y)),
      pushPt W V (redU K W V (.some _ _ h)) = .some _ _ h' := by
  have h₁ : (curveK (liftField K W) (V.map (liftJ W))).Nonsingular
      (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y) := by
    show ((V.map (liftJ W)).map (algebraMap _ (liftField K W))).toAffine.Nonsingular _ _
    rw [← map_baseChange_eq_map_of K V (liftJ W) (liftField K W) (liftJ_algebraMap K W)]
    exact h
  have n : (curveRed (V.map (liftJ W))).Nonsingular (residue _ x) (residue _ y) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (equation_residue (V.map (liftJ W)) (equation_of_map (liftField K W) _ h₁.1))
  obtain ⟨h', e⟩ := pointMapRing_some (pushField W) ((V.map (liftJ W)).map (residue _)) n
  refine ⟨by rw [← pushCurve_eq W V]; exact h', ?_⟩
  have e₁ : pointCongr (map_baseChange_eq_map_of K V (liftJ W) (liftField K W)
      (liftJ_algebraMap K W)) (Point.some _ _ h) = Point.some _ _ h₁ := pointCongr_some _ h
  have e₂ : redU K W V (.some _ _ h) = .some _ _ n := by
    show reducePoint (liftField K W) (V.map (liftJ W)) (pointCongr _ (.some _ _ h)) = _
    rw [e₁, reducePoint_some_integral _ _ h₁ n]
  rw [e₂]
  exact (congrArg (pointCongr (pushCurve_eq W V)) e).trans (pointCongr_some _ _)

instance isElliptic_baseChange_ring {R : Type*} [CommRing R] (V : WeierstrassCurve R) [V.IsElliptic]
    (A : Type*) [CommRing A] [Algebra R A] : (V.baseChange A).IsElliptic := by
  unfold WeierstrassCurve.baseChange; infer_instance

variable [W.IsElliptic]

def liftPt₁ : ((W.baseChange K).baseChange (liftField K W)).toAffine.Point :=
  Point.map (IsScalarTower.toAlgHom K (W.baseChange K).toAffine.FunctionField (liftField K W))
    (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K))

theorem baseChange_liftField_eq :
    ((gaussCurve W W).baseChange (W.baseChange K).toAffine.FunctionField).baseChange
      (liftField K W) = (W.baseChange K).baseChange (liftField K W) := by
  show W.map (((algebraMap (W.baseChange K).toAffine.FunctionField (liftField K W)).comp
      (algebraMap (gaussRing W) _)).comp (algebraMap 𝒪 (gaussRing W))) =
    W.map ((algebraMap K (liftField K W)).comp (algebraMap 𝒪 K))
  refine congrArg W.map (RingHom.ext fun c => ?_)
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField K W)]

def liftPt₂ : ((W.baseChange K).baseChange (liftField K W)).toAffine.Point :=
  pointCongr (baseChange_liftField_eq K W)
    (GroundTheory.Arith.Abelian.genericPoint
      ((gaussCurve W W).baseChange (W.baseChange K).toAffine.FunctionField))

theorem exists_some_eq {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}
    {a b a' b' : F} (h : V.toAffine.Nonsingular a b) (ha : a = a') (hb : b = b') :
    ∃ h', (Point.some a b h : V.toAffine.Point) = Point.some a' b' h' := by
  subst ha; subst hb; exact ⟨h, rfl⟩

theorem liftPt₁_eq : ∃ h, liftPt₁ K W = Point.some
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussX W)))
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussY W))) h := by
  have hx : algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussX W)) =
        algebraMap (W.baseChange K).toAffine.FunctionField _ (genX (W.baseChange K)) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (gaussRing W)
      (W.baseChange K).toAffine.FunctionField (liftField K W), algebraMap_gaussX]
  have hy : algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussY W)) =
        algebraMap (W.baseChange K).toAffine.FunctionField _ (genY (W.baseChange K)) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (gaussRing W)
      (W.baseChange K).toAffine.FunctionField (liftField K W), algebraMap_gaussY]
  rw [liftPt₁, GroundTheory.Arith.Abelian.genericPoint, Point.map_some]
  exact exists_some_eq _ hx.symm hy.symm

theorem liftPt₂_eq : ∃ h, liftPt₂ K W = Point.some
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W) (gaussX (gaussCurve W W)))
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W) (gaussY (gaussCurve W W))) h := by
  rw [liftPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact exists_some_eq _
    (algebraMap_gaussX (gaussCurve W W) (W.baseChange K).toAffine.FunctionField).symm
    (algebraMap_gaussY (gaussCurve W W) (W.baseChange K).toAffine.FunctionField).symm

theorem pushPt_redU_liftPt₁ :
    pushPt W W (redU K W W (liftPt₁ K W)) = univPt₁ (W.map (residue 𝒪)) := by
  obtain ⟨h, e⟩ := liftPt₁_eq K W
  obtain ⟨h', e'⟩ := pushPt_redU_some K W W h
  rw [e, e', univPt₁, GroundTheory.Arith.Abelian.genericPoint, Point.map_some, Point.some.injEq]
  constructor
  · rw [pushField_residue_algebraMap, gaussResidue_gaussX]; rfl
  · rw [pushField_residue_algebraMap, gaussResidue_gaussY]; rfl

theorem pushPt_redU_liftPt₂ :
    pushPt W W (redU K W W (liftPt₂ K W)) = univPt₂ (W.map (residue 𝒪)) := by
  obtain ⟨h, e⟩ := liftPt₂_eq K W
  obtain ⟨h', e'⟩ := pushPt_redU_some K W W h
  rw [e, e', univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.some.injEq]
  exact ⟨pushField_gaussX W, pushField_gaussY W⟩

theorem isGenPt_liftPt₁ : IsGenPt (W.baseChange K) (liftPt₁ K W) :=
  isGenPt_map _ _ (transcendental_genX _)

theorem transOver_liftPt₂ :
    TransOver (W.baseChange K) (W.baseChange K).toAffine.FunctionField (liftPt₂ K W) := by
  rw [liftPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact transcendental_genX _

theorem isGenPt_liftPt₂ : IsGenPt (W.baseChange K) (liftPt₂ K W) := (transOver_liftPt₂ K W).isGenPt

theorem isGenPt_liftPt₁₂ : IsGenPt (W.baseChange K) (liftPt₁ K W + liftPt₂ K W) :=
  ((transOver_liftPt₂ K W).add_left (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K))).isGenPt

end Main

end

end GroundTheory.Global
end

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))]

theorem redU_apply (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    (P : ((V.baseChange K).baseChange (liftField K W)).toAffine.Point) :
    redU K W V P = reducePoint (liftField K W) (V.map (liftJ W))
      (pointCongr (map_baseChange_eq_map_of K V (liftJ W) (liftField K W)
        (liftJ_algebraMap K W)) P) := by
  simp only [redU, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    reductionHom_apply]

theorem pushPt_apply (V : WeierstrassCurve 𝒪)
    (P : ((V.map (liftJ W)).map (residue (gaussRing (gaussCurve W W)))).toAffine.Point) :
    pushPt W V P = pointCongr (pushCurve_eq W V) (pointMapRing (pushField W) _ P) := by
  simp only [pushPt, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]

variable [W.IsElliptic]

theorem exists_integral_of_reducePoint_ne_zero {𝒪₀ : Type*} [CommRing 𝒪₀] [IsDomain 𝒪₀]
    [IsDiscreteValuationRing 𝒪₀] (K₀ : Type*) [Field K₀] [Algebra 𝒪₀ K₀] [IsFractionRing 𝒪₀ K₀]
    (V : WeierstrassCurve 𝒪₀) {P : (curveK K₀ V).Point} (hP : reducePoint K₀ V P ≠ 0) :
    ∃ (x y : 𝒪₀) (h : (curveK K₀ V).Nonsingular (algebraMap 𝒪₀ K₀ x) (algebraMap 𝒪₀ K₀ y)),
      P = Point.some _ _ h := by
  rcases point_cases K₀ V P with h0 | ⟨X₀, Y₀, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · exact absurd (by rw [h0, reducePoint_zero]) hP
  · exact absurd (reducePoint_some_notMem K₀ V h hX) hP
  · exact ⟨x, y, h, rfl⟩

theorem liftPt₁₂_eq : ∃ (x y : gaussRing (gaussCurve W W)) (h : _),
    liftPt₁ K W + liftPt₂ K W = Point.some (algebraMap _ (liftField K W) x)
      (algebraMap _ (liftField K W) y) h := by
  have hsum : pushPt W W (redU K W W (liftPt₁ K W + liftPt₂ K W)) =
      univPt₁ (W.map (residue 𝒪)) + univPt₂ (W.map (residue 𝒪)) := by
    rw [map_add (f := _), map_add (f := _), pushPt_redU_liftPt₁, pushPt_redU_liftPt₂]
  have hne : redU K W W (liftPt₁ K W + liftPt₂ K W) ≠ 0 := fun h0 =>
    isGenPt_ne_zero _ (isGenPt_univPt₁₂ (W.map (residue 𝒪))) (by rw [← hsum, h0, map_zero])
  rw [redU_apply] at hne
  obtain ⟨x, y, h, hP⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have hP' : liftPt₁ K W + liftPt₂ K W = pointCongr (map_baseChange_eq_map_of K W (liftJ W)
      (liftField K W) (liftJ_algebraMap K W)).symm (Point.some _ _ h) := by
    rw [← hP, pointCongr_pointCongr]; rfl
  rw [hP', pointCongr_some]
  exact ⟨x, y, _, rfl⟩

omit [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))] [W.IsElliptic] in
theorem pointCongr_pointCongr_eq {F : Type*} [Field F] [DecidableEq F]
    {V₁ V₂ V₃ : WeierstrassCurve F} (h₁ : V₁ = V₂) (h₂ : V₂ = V₃) (h₃ : V₁ = V₃)
    (P : V₁.toAffine.Point) : pointCongr h₂ (pointCongr h₁ P) = pointCongr h₃ P := by
  subst h₁; subst h₂; rfl

variable (W' : WeierstrassCurve 𝒪) [W'.IsElliptic]

theorem pushField_comp_fieldEvalRed {x y : gaussRing (gaussCurve W W)}
    (hxy : (W.map (liftJ W)).toAffine.Equation x y)
    (hx : Function.Injective (eval₂RingHom (ResidueField.map (liftJ W)) (residue _ x)))
    {R : ((W.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Point}
    (hR : IsGenPt (W.map (residue 𝒪)) R) (hRx : xOf _ R = pushField W (residue _ x))
    (hRy : yOf _ R = pushField W (residue _ y)) :
    (pushField W).comp (fieldEvalRed W (liftJ W) hxy hx) =
      (genEval (W.map (residue 𝒪)) R hR).toRingHom := by
  apply ringHom_ext_functionField
  · intro c
    rw [RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply,
      pushField_comp_residueField_map]
    exact ((genEval _ R hR).commutes c).symm
  · rw [RingHom.comp_apply, fieldEvalRed_genX, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      genEval_genX, hRx]
  · rw [RingHom.comp_apply, fieldEvalRed_genY, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      genEval_genY, hRy]


set_option maxHeartbeats 1000000 in
theorem pushPt_redU_genEval {x y : gaussRing (gaussCurve W W)}
    (h : ((W.baseChange K).baseChange (liftField K W)).toAffine.Nonsingular
      (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y))
    (hg : IsGenPt (W.baseChange K) (Point.some _ _ h))
    {R : ((W.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Point}
    (hR : IsGenPt (W.map (residue 𝒪)) R)
    (hpush : pushPt W W (redU K W W (Point.some _ _ h)) = R)
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point) :
    pushPt W W' (redU K W W' (Point.map (genEval (W.baseChange K) _ hg) Q)) =
      Point.map (genEval (W.map (residue 𝒪)) R hR) (reduceFF K W W' Q) := by
  obtain ⟨h', e'⟩ := pushPt_redU_some K W W h
  rw [e'] at hpush
  subst hpush
  have hxy : (W.map (liftJ W)).toAffine.Equation x y := by
    have h₁ : ((W.map (liftJ W)).map (algebraMap _ (liftField K W))).toAffine.Equation
        (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y) := by
      rw [← map_baseChange_eq_map_of K W (liftJ W) (liftField K W) (liftJ_algebraMap K W)]
      exact h.1
    exact (WeierstrassCurve.Affine.map_equation (W.map (liftJ W)).toAffine
      (IsFractionRing.injective _ (liftField K W)) x y).mp h₁
  have hx : Function.Injective (eval₂RingHom (ResidueField.map (liftJ W)) (residue _ x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    have hT : Transcendental (ResidueField 𝒪) (pushField W (residue _ x)) := hR
    apply hT
    refine ⟨p, hp0, ?_⟩
    have key : aeval (pushField W (residue _ x)) p =
        pushField W (eval₂RingHom (ResidueField.map (liftJ W)) (residue _ x) p) := by
      rw [aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, pushField_comp_residueField_map]
    rw [key, hp, map_zero]
  have main := reducePoint_genEval (K := K) (W := W) (W' := W') (j := liftJ W)
    (M := liftField K W) (hxy := hxy) (hx := hx) (liftJ_algebraMap K W) h hg Q
  have hring := pushField_comp_fieldEvalRed W hxy hx hR rfl rfl
  rw [redU_apply, main, pushPt_apply, pointMapRing_pointCongr, pointCongr_pointCongr,
    pointMapRing_pointMapRing, pointMapRing_congr hring, map_eq_pointCongr_pointMapRing]
  exact pointCongr_pointCongr_eq _ _ _ _


set_option maxHeartbeats 1000000 in
theorem univAdd_reduceFF
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point)
    (hQ : RespectsAdd (W.baseChange K) (W'.baseChange K) Q) : UnivAdd (reduceFF K W W' Q) := by
  haveI : DecidableEq (ResidueField (gaussRing (gaussCurve W W))) := Classical.decEq _
  obtain ⟨h₁, e₁⟩ := liftPt₁_eq K W
  obtain ⟨h₂, e₂⟩ := liftPt₂_eq K W
  obtain ⟨x₃, y₃, h₃, e₃⟩ := liftPt₁₂_eq K W
  have g₁ : IsGenPt (W.baseChange K) (Point.some _ _ h₁) := by
    rw [← e₁]; exact isGenPt_liftPt₁ K W
  have g₂ : IsGenPt (W.baseChange K) (Point.some _ _ h₂) := by
    rw [← e₂]; exact isGenPt_liftPt₂ K W
  have g₃ : IsGenPt (W.baseChange K) (Point.some _ _ h₃) := by
    rw [← e₃]; exact isGenPt_liftPt₁₂ K W
  have hsum : pushPt W W (redU K W W (liftPt₁ K W + liftPt₂ K W)) =
      univPt₁ (W.map (residue 𝒪)) + univPt₂ (W.map (residue 𝒪)) := by
    rw [map_add (f := _), map_add (f := _), pushPt_redU_liftPt₁, pushPt_redU_liftPt₂]
  have k₁ := pushPt_redU_genEval K W W' h₁ g₁ (isGenPt_univPt₁ _)
    (by rw [← e₁]; exact pushPt_redU_liftPt₁ K W) Q
  have k₂ := pushPt_redU_genEval K W W' h₂ g₂ (isGenPt_univPt₂ _)
    (by rw [← e₂]; exact pushPt_redU_liftPt₂ K W) Q
  have k₃ := pushPt_redU_genEval K W W' h₃ g₃ (isGenPt_univPt₁₂ _)
    (by rw [← e₃]; exact hsum) Q
  have hs : Point.some _ _ h₁ + Point.some _ _ h₂ = Point.some _ _ h₃ := by
    rw [← e₁, ← e₂, e₃]
  have hadd := (respectsAdd_iff Q).mp hQ (liftField K W) _ _ g₁ g₂ (hs ▸ g₃)
  rw [genEval_congr _ hs _ g₃] at hadd
  have := congrArg (fun P => pushPt W W' (redU K W W' P)) hadd
  simp only [map_add (f := _)] at this
  rw [k₁, k₂, k₃] at this
  exact this

theorem respectsAdd_reduceFF
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point)
    (hQ : RespectsAdd (W.baseChange K) (W'.baseChange K) Q) :
    RespectsAdd (W.map (residue 𝒪)) (W'.map (residue 𝒪)) (reduceFF K W W' Q) :=
  respectsAdd_of_univAdd _ (univAdd_reduceFF K W W' Q hQ)

end Main

end

end GroundTheory.Global
end

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

section Generic

variable [W.IsElliptic]


omit [W.IsElliptic] in
theorem reduceFF_some (V : WeierstrassCurve 𝒪) [V.IsElliptic] {x y : gaussRing W}
    (h : ((V.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Nonsingular
      (algebraMap (gaussRing W) _ x) (algebraMap (gaussRing W) _ y)) :
    ∃ h', reduceFF K W V (Point.some _ _ h) =
      Point.some (gaussResidue W (residue _ x)) (gaussResidue W (residue _ y)) h' := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have h₁ : (curveK (W.baseChange K).toAffine.FunctionField (gaussCurve W V)).Nonsingular
      (algebraMap (gaussRing W) _ x) (algebraMap (gaussRing W) _ y) := by
    show ((gaussCurve W V).map (algebraMap _ _)).toAffine.Nonsingular _ _
    rw [gaussCurve_map_functionField]; exact h
  have e₁ : pointCongr (gaussCurve_map_functionField K W V).symm (Point.some _ _ h) =
      Point.some _ _ h₁ := pointCongr_some _ h
  have n₁ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (equation_residue (gaussCurve W V)
      (equation_of_map (W.baseChange K).toAffine.FunctionField (gaussCurve W V) h₁.1))
  obtain ⟨h₂, e₂⟩ := pointMapRing_some (gaussResidue W) ((gaussCurve W V).map (residue _)) n₁
  refine ⟨by rw [← gaussCurve_map_residue W V]; exact h₂, ?_⟩
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [e₁, reducePoint_some_integral _ _ h₁ n₁]
  erw [e₂]
  rw [pointCongr_some]

theorem reduceFF_genericPoint :
    reduceFF K W W (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K)) =
      GroundTheory.Arith.Abelian.genericPoint (W.map (residue 𝒪)) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have hx := algebraMap_gaussX W K
  have hy := algebraMap_gaussY W K
  obtain ⟨h₁, e₁⟩ : ∃ h₁ : (curveK (W.baseChange K).toAffine.FunctionField
      (gaussCurve W W)).Nonsingular (algebraMap (gaussRing W) _ (gaussX W))
        (algebraMap (gaussRing W) _ (gaussY W)),
      pointCongr (gaussCurve_map_functionField K W W).symm
        (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K)) = Point.some _ _ h₁ := by
    rw [GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
    exact exists_some_eq _ hx.symm hy.symm
  have n₁ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (equation_residue (gaussCurve W W)
      (equation_of_map (W.baseChange K).toAffine.FunctionField (gaussCurve W W) h₁.1))
  obtain ⟨h₂, e₂⟩ := pointMapRing_some (gaussResidue W) ((gaussCurve W W).map (residue _)) n₁
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [e₁, reducePoint_some_integral _ _ h₁ n₁]
  erw [e₂]
  rw [pointCongr_some, GroundTheory.Arith.Abelian.genericPoint, Point.some.injEq, gaussResidue_gaussX,
    gaussResidue_gaussY]
  exact ⟨rfl, rfl⟩

theorem reduceFF_zsmul_genericPoint (n : ℤ) :
    reduceFF K W W (n • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K)) =
      n • GroundTheory.Arith.Abelian.genericPoint (W.map (residue 𝒪)) := by
  rw [map_zsmul, reduceFF_genericPoint]

end Generic

section Coordinates

variable {F : Type*} [Field F] [DecidableEq F]

theorem xOf_pointCongr {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    xOf V₂ (pointCongr h P) = xOf V₁ P := by
  subst h; rfl

theorem yOf_pointCongr {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    yOf V₂ (pointCongr h P) = yOf V₁ P := by
  subst h; rfl

theorem pointCongr_eq_zero_iff {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂)
    (P : V₁.toAffine.Point) : pointCongr h P = 0 ↔ P = 0 := by
  subst h; rfl

variable {L : Type*} [Field L] [DecidableEq L]

theorem xOf_pointMapRing (f : F →+* L) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    xOf (V.map f) (pointMapRing f V P) = f (xOf V P) := by
  rcases P with _ | ⟨x, y, h⟩
  · show (0 : L) = f 0; rw [map_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some f V h
    rw [e]; rfl

theorem yOf_pointMapRing (f : F →+* L) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    yOf (V.map f) (pointMapRing f V P) = f (yOf V P) := by
  rcases P with _ | ⟨x, y, h⟩
  · show (0 : L) = f 0; rw [map_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some f V h
    rw [e]; rfl

theorem pointMapRing_eq_zero_iff (f : F →+* L) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    pointMapRing f V P = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · obtain ⟨h', e⟩ := pointMapRing_some f V h
    rw [e]
    exact ⟨fun h0 => absurd h0 (Point.some_ne_zero _), fun h0 => absurd h0 (Point.some_ne_zero _)⟩

theorem point_ext_xy {V : WeierstrassCurve F} {P Q : V.toAffine.Point} (h0 : P = 0 ↔ Q = 0)
    (hx : xOf V P = xOf V Q) (hy : yOf V P = yOf V Q) : P = Q := by
  rcases P with _ | ⟨x, y, h⟩ <;> rcases Q with _ | ⟨x', y', h'⟩
  · rfl
  · exact absurd (h0.1 rfl) (Point.some_ne_zero _)
  · exact absurd (h0.2 rfl) (Point.some_ne_zero _)
  · rw [Point.some.injEq]; exact ⟨hx, hy⟩

end Coordinates

section Composition

omit [IsFractionRing 𝒪 K] in
theorem fieldEvalRed_congr {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    (j : 𝒪 →+* Λ) [IsLocalHom j] {x₁ y₁ x₂ y₂ : Λ} (hxy₁ : (W.map j).toAffine.Equation x₁ y₁)
    (hxy₂ : (W.map j).toAffine.Equation x₂ y₂)
    (hx₁ : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x₁)))
    (hx₂ : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x₂)))
    (ex : residue Λ x₁ = residue Λ x₂) (ey : residue Λ y₁ = residue Λ y₂) :
    fieldEvalRed W j hxy₁ hx₁ = fieldEvalRed W j hxy₂ hx₂ := by
  apply ringHom_ext_functionField
  · intro c; rw [fieldEvalRed_algebraMap, fieldEvalRed_algebraMap]
  · rw [fieldEvalRed_genX, fieldEvalRed_genX, ex]
  · rw [fieldEvalRed_genY, fieldEvalRed_genY, ey]

omit [IsFractionRing 𝒪 K] in
theorem gaussResidue_comp_residueField_map :
    (gaussResidue W).comp (ResidueField.map (algebraMap 𝒪 (gaussRing W))) =
      algebraMap (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.FunctionField := by
  refine RingHom.ext fun c => ?_
  obtain ⟨c, rfl⟩ := residue_surjective c
  rw [RingHom.comp_apply, ResidueField.map_residue, gaussResidue_residue_algebraMap]

variable (W' W'' : WeierstrassCurve 𝒪) [W'.IsElliptic] [W''.IsElliptic]


set_option maxHeartbeats 1000000 in
theorem reduceFF_map_genEval
    {R : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point}
    (hR : IsGenPt (W'.baseChange K) R) (hR' : IsGenPt (W'.map (residue 𝒪)) (reduceFF K W W' R))
    (Q : ((W''.baseChange K).baseChange (W'.baseChange K).toAffine.FunctionField).toAffine.Point) :
    reduceFF K W W'' (Point.map (genEval (W'.baseChange K) R hR) Q) =
      Point.map (genEval (W'.map (residue 𝒪)) _ hR') (reduceFF K W' W'' Q) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have e := gaussCurve_map_functionField K W W'
  have hne : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W')
      (pointCongr e.symm R) ≠ 0 := by
    intro h0
    apply isGenPt_ne_zero _ hR'
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    erw [h0]
    rw [map_zero, map_zero]
  obtain ⟨x, y, h₀, hP⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have hRe : R = pointCongr e (Point.some _ _ h₀) := by
    rw [← hP, pointCongr_pointCongr]; rfl
  obtain ⟨h, hRs⟩ : ∃ h, R = Point.some (algebraMap (gaussRing W) _ x)
      (algebraMap (gaussRing W) _ y) h := by
    rw [hRe, pointCongr_some]; exact ⟨_, rfl⟩
  subst hRs
  obtain ⟨h', e'⟩ := reduceFF_some K W W' h
  have hR'' : IsGenPt (W'.map (residue 𝒪)) (Point.some _ _ h') := e' ▸ hR'
  rw [genEval_congr _ e' hR' hR'']
  set j := algebraMap 𝒪 (gaussRing W)
  have hjM : ∀ c : 𝒪, algebraMap K (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 K c) =
      algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (j c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hxy : (W'.map j).toAffine.Equation x y := by
    have h₁ : ((W'.map j).map (algebraMap _ (W.baseChange K).toAffine.FunctionField)).toAffine.Equation
        (algebraMap _ _ x) (algebraMap _ _ y) := by
      rw [← map_baseChange_eq_map_of K W' j _ hjM]; exact h.1
    exact (WeierstrassCurve.Affine.map_equation (W'.map j).toAffine
      (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) x y).mp h₁
  have hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue _ x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    have hT : Transcendental (ResidueField 𝒪) (gaussResidue W (residue _ x)) := hR''
    apply hT
    refine ⟨p, hp0, ?_⟩
    have key : aeval (gaussResidue W (residue _ x)) p =
        gaussResidue W (eval₂RingHom (ResidueField.map j) (residue _ x) p) := by
      rw [aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, gaussResidue_comp_residueField_map]
    rw [key, hp, map_zero]
  have hring : (gaussResidue W).comp (fieldEvalRed W' j hxy hx) =
      (genEval (W'.map (residue 𝒪)) _ hR'').toRingHom := by
    apply ringHom_ext_functionField
    · intro c
      rw [RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply,
        gaussResidue_comp_residueField_map]
      exact ((genEval _ _ hR'').commutes c).symm
    · rw [RingHom.comp_apply, fieldEvalRed_genX, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        genEval_genX]
      rfl
    · rw [RingHom.comp_apply, fieldEvalRed_genY, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        genEval_genY]
      rfl
  have main := reducePoint_genEval (K := K) (W := W') (W' := W'') (j := j)
    (M := (W.baseChange K).toAffine.FunctionField) (hxy := hxy) (hx := hx) hjM h hR Q
  have main' : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W'')
      (pointCongr (gaussCurve_map_functionField K W W'').symm
        (Point.map (genEval (W'.baseChange K) _ hR) Q)) =
      pointCongr (map_fieldEvalRed_eq W' W'' j hxy hx)
        (pointMapRing (fieldEvalRed W' j hxy hx) _ (reduceFF K W' W'' Q)) := main
  have hL : reduceFF K W W'' (Point.map (genEval (W'.baseChange K) _ hR) Q) =
      pointCongr (gaussCurve_map_residue W W'') (pointMapRing (gaussResidue W) _
        (reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W'')
          (pointCongr (gaussCurve_map_functionField K W W'').symm
            (Point.map (genEval (W'.baseChange K) _ hR) Q)))) := by
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    rfl
  rw [hL, main']
  have hf := DFunLike.congr_fun hring
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
  apply point_ext_xy
  · rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff, pointCongr_eq_zero_iff,
      pointMapRing_eq_zero_iff, map_eq_pointCongr_pointMapRing, pointCongr_eq_zero_iff,
      pointMapRing_eq_zero_iff]
  · rw [xOf_pointCongr, xOf_pointMapRing, xOf_pointCongr, xOf_pointMapRing, hf,
      map_eq_pointCongr_pointMapRing, xOf_pointCongr, xOf_pointMapRing]
    rfl
  · rw [yOf_pointCongr, yOf_pointMapRing, yOf_pointCongr, yOf_pointMapRing, hf,
      map_eq_pointCongr_pointMapRing, yOf_pointCongr, yOf_pointMapRing]
    rfl

end Composition

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddGeneric
namespace GroundTheory.Global

noncomputable section

open Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

theorem exists_algebraMap_eq_of_isAlgebraic_ff (E : WeierstrassCurve F) [E.IsElliptic]
    {u : E.toAffine.FunctionField} (hu : IsAlgebraic F u) :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = u := by
  classical
  have hu' : IsAlgebraic (AlgebraicClosure F) (bcEmb (F' := AlgebraicClosure F) E u) :=
    (hu.algHom (bcEmb (F' := AlgebraicClosure F) E)).tower_top (AlgebraicClosure F)
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic (E.baseChange (AlgebraicClosure F)) hu'
  exact exists_algebraMap_eq_of_bcEmb E hc.symm

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem isGenPt_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsGenPt E' Q := by
  classical
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl h0
  · by_contra hx
    have hx' : IsAlgebraic F x := not_not.mp hx
    obtain ⟨a, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hx'
    have hy' : IsAlgebraic F y := by
      have := isIntegral_y E' F h.1 (mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap a))
      exact mem_algebraicClosure_iff.1 this
    obtain ⟨b, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hy'
    have hc : (E'.baseChange F).toAffine.Nonsingular a b :=
      (E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F E.toAffine.FunctionField)
        (algebraMap F _).injective a b).mp h
    have hQc : (Point.some _ _ h : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) =
        Point.map (Algebra.ofId F E.toAffine.FunctionField) (Point.some _ _ hc) := by
      rw [Point.map_some, Point.some.injEq]; exact ⟨rfl, rfl⟩
    have key := (respectsAdd_iff _).mp hQ (univField E) (univPt₁ E) (univPt₂ E)
      (isGenPt_univPt₁ E) (isGenPt_univPt₂ E) (isGenPt_univPt₁₂ E)
    have hconst : ∀ (σ : E.toAffine.FunctionField →ₐ[F] univField E),
        Point.map σ (Point.some _ _ h) =
          Point.map (Algebra.ofId F (univField E)) (Point.some _ _ hc) := fun σ => by
      rw [hQc, Point.map_map]
      have e : σ.comp (Algebra.ofId F E.toAffine.FunctionField) = Algebra.ofId F (univField E) :=
        AlgHom.ext fun z => by
          rw [AlgHom.comp_apply, Algebra.ofId_apply, Algebra.ofId_apply, σ.commutes]
      rw [e]
    rw [hconst, hconst, hconst, left_eq_add] at key
    have := Point.map_injective (W' := E') (Algebra.ofId F (univField E))
      (key.trans (map_zero _).symm)
    exact Point.some_ne_zero hc this

theorem isIsogeny_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsIsogeny E E' Q :=
  (isIsogeny_iff Q).mpr ⟨isGenPt_of_respectsAdd hQ h0, hQ⟩

end

end GroundTheory.Global
end

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

section Setup

abbrev liftField₂ : Type _ :=
  ((gaussCurve W W').baseChange (W.baseChange K).toAffine.FunctionField).toAffine.FunctionField

abbrev liftJ₂ : 𝒪 →+* gaussRing (gaussCurve W W') :=
  (algebraMap (gaussRing W) (gaussRing (gaussCurve W W'))).comp (algebraMap 𝒪 (gaussRing W))

theorem liftJ₂_algebraMap (c : 𝒪) :
    algebraMap K (liftField₂ K W W') (algebraMap 𝒪 K c) =
      algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W') (liftJ₂ W W' c) := by
  rw [RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply (gaussRing W) (gaussRing (gaussCurve W W')) (liftField₂ K W W'),
    IsScalarTower.algebraMap_apply (gaussRing W) (W.baseChange K).toAffine.FunctionField
      (liftField₂ K W W'),
    ← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField₂ K W W')]

theorem baseChange_liftField₂_eq :
    ((gaussCurve W W').baseChange (W.baseChange K).toAffine.FunctionField).baseChange
      (liftField₂ K W W') = (W'.baseChange K).baseChange (liftField₂ K W W') := by
  rw [baseChange_baseChange]
  show W'.map (((algebraMap (W.baseChange K).toAffine.FunctionField (liftField₂ K W W')).comp
      (algebraMap (gaussRing W) _)).comp (algebraMap 𝒪 (gaussRing W))) =
    W'.map ((algebraMap K (liftField₂ K W W')).comp (algebraMap 𝒪 K))
  refine congrArg W'.map (RingHom.ext fun c => ?_)
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField₂ K W W')]

variable [W'.IsElliptic]

def genPt₂ : ((W'.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point :=
  pointCongr (baseChange_liftField₂_eq K W W')
    (GroundTheory.Arith.Abelian.genericPoint
      ((gaussCurve W W').baseChange (W.baseChange K).toAffine.FunctionField))

theorem genPt₂_eq : ∃ h, genPt₂ K W W' = Point.some
    (algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W') (gaussX (gaussCurve W W')))
    (algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W') (gaussY (gaussCurve W W'))) h := by
  rw [genPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact exists_some_eq _
    (algebraMap_gaussX (gaussCurve W W') (W.baseChange K).toAffine.FunctionField).symm
    (algebraMap_gaussY (gaussCurve W W') (W.baseChange K).toAffine.FunctionField).symm

theorem transOver_genPt₂ :
    TransOver (W'.baseChange K) (W.baseChange K).toAffine.FunctionField (genPt₂ K W W') := by
  rw [genPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact transcendental_genX _

end Setup

section Red

variable [DecidableEq (ResidueField (gaussRing (gaussCurve W W')))]

def red₂ (V : WeierstrassCurve 𝒪)
    (P : ((V.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point) :
    ((V.map (liftJ₂ W W')).map (residue (gaussRing (gaussCurve W W')))).toAffine.Point :=
  reducePoint (liftField₂ K W W') (V.map (liftJ₂ W W'))
    (pointCongr (map_baseChange_eq_map_of K V (liftJ₂ W W') (liftField₂ K W W')
      (liftJ₂_algebraMap K W W')) P)

theorem red₂_add (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    (P Q : ((V.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point) :
    red₂ K W W' V (P + Q) = red₂ K W W' V P + red₂ K W W' V Q := by
  rw [red₂, red₂, red₂, map_add (f := _), reducePoint_add]

theorem red₂_zero (V : WeierstrassCurve 𝒪) : red₂ K W W' V 0 = 0 := by
  rw [red₂, map_zero, reducePoint_zero]

variable [W.IsElliptic] [W'.IsElliptic]

theorem red₂_map_of_reduceFF_eq_zero
    {R : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point}
    (hR : reduceFF K W W' R = 0) :
    red₂ K W W' W' (Point.map (IsScalarTower.toAlgHom K (W.baseChange K).toAffine.FunctionField
      (liftField₂ K W W')) R) = 0 := by
  letI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have e := gaussCurve_map_functionField K W W'
  have h0 : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W')
      (pointCongr e.symm R) = 0 := by
    have := hR
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      reductionHom_apply] at this
    rwa [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff] at this
  rcases point_cases (W.baseChange K).toAffine.FunctionField (gaussCurve W W') (pointCongr e.symm R)
    with hz | ⟨X₀, Y₀, h, hP, hX⟩ | ⟨x, y, h, hP⟩
  · rw [pointCongr_eq_zero_iff] at hz
    rw [hz, map_zero, red₂_zero]
  · have hRe : R = pointCongr e (Point.some _ _ h) := by
      rw [← hP, pointCongr_pointCongr]; rfl
    rw [pointCongr_some] at hRe
    subst hRe
    have hσ : (algebraMap (W.baseChange K).toAffine.FunctionField (liftField₂ K W W')).comp
        (algebraMap (gaussRing W) _) = (algebraMap (gaussRing (gaussCurve W W'))
          (liftField₂ K W W')).comp (algebraMap (gaussRing W) _) := by
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    have hX' := map_notMem_range (W.baseChange K).toAffine.FunctionField (liftField₂ K W W') hσ hX
    rw [red₂, Point.map_some, pointCongr_some]
    exact reducePoint_some_notMem _ _ _ hX'
  · exfalso
    have n := nonsingular_residue_of_isElliptic _ _ h.1
    rw [hP, reducePoint_some_integral _ _ h n] at h0
    exact Point.some_ne_zero n h0

end Red

end

end GroundTheory.Global
