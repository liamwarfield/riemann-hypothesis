module

public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionPoints
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionGauss
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.ReductionTorsion
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.ReductionMap
namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian WeierstrassCurve.Affine

section PointMap

variable {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L] (f : F →+* L)
  (V : WeierstrassCurve F)

def pointMapRing : V.toAffine.Point →+ (V.map f).toAffine.Point :=
  letI := f.toAlgebra
  Point.map (W' := V) (Algebra.ofId F L)

theorem pointMapRing_some {x y : F} (h : V.toAffine.Nonsingular x y) :
    ∃ h' : (V.map f).toAffine.Nonsingular (f x) (f y),
      pointMapRing f V (.some x y h) = .some _ _ h' :=
  ⟨_, rfl⟩

end PointMap

section Functorial

variable {𝒪₁ 𝒪₂ : Type*} [CommRing 𝒪₁] [IsDomain 𝒪₁] [IsDiscreteValuationRing 𝒪₁]
  [CommRing 𝒪₂] [IsDomain 𝒪₂] [IsDiscreteValuationRing 𝒪₂]
  (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra 𝒪₁ K₁] [IsFractionRing 𝒪₁ K₁] [Algebra 𝒪₂ K₂]
  [IsFractionRing 𝒪₂ K₂] {f : 𝒪₁ →+* 𝒪₂} [IsLocalHom f] {σ : K₁ →+* K₂}
  (hσ : σ.comp (algebraMap 𝒪₁ K₁) = (algebraMap 𝒪₂ K₂).comp f) (W : WeierstrassCurve 𝒪₁)

include hσ in
theorem map_curveK_eq :
    (W.map (algebraMap 𝒪₁ K₁)).map σ = (W.map f).map (algebraMap 𝒪₂ K₂) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, hσ]

theorem map_curveRed_eq :
    (W.map (residue 𝒪₁)).map (ResidueField.map f) = (W.map f).map (residue 𝒪₂) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, ResidueField.map_comp_residue]


include hσ in
theorem map_notMem_range {X : K₁} (hX : X ∉ Set.range (algebraMap 𝒪₁ K₁)) :
    σ X ∉ Set.range (algebraMap 𝒪₂ K₂) := by
  rintro ⟨s, hs⟩
  obtain ⟨t, htm, ht⟩ := exists_inv_mem_of_notMem_range K₁ hX
  have hX0 : X ≠ 0 := fun h => hX ⟨0, by rw [h, map_zero]⟩
  have h1 : algebraMap 𝒪₂ K₂ (s * f t) = 1 := by
    rw [map_mul, hs, ← RingHom.comp_apply, ← hσ, RingHom.comp_apply, ht, ← map_mul,
      mul_inv_cancel₀ hX0, map_one]
  have hu : IsUnit (f t) := isUnit_iff_exists_inv.mpr ⟨s,
    IsFractionRing.injective 𝒪₂ K₂ (by rw [mul_comm, h1, map_one])⟩
  exact (mem_maximalIdeal _).1 htm (isUnit_of_map_unit f t hu)

variable [W.IsElliptic] [DecidableEq K₁] [DecidableEq K₂] [DecidableEq (ResidueField 𝒪₁)]
  [DecidableEq (ResidueField 𝒪₂)]

theorem reducePoint_pointMapRing (P : (curveK K₁ W).Point) :
    reducePoint K₂ (W.map f) (pointCongr (map_curveK_eq K₁ K₂ hσ W)
        (pointMapRing σ (W.map (algebraMap 𝒪₁ K₁)) P)) =
      pointCongr (map_curveRed_eq W)
        (pointMapRing (ResidueField.map f) (W.map (residue 𝒪₁)) (reducePoint K₁ W P)) := by
  rcases point_cases K₁ W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · rw [reducePoint_zero, map_zero, map_zero, map_zero, map_zero, reducePoint_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some σ (W.map (algebraMap 𝒪₁ K₁)) h
    rw [e, pointCongr_some, reducePoint_some_notMem K₂ (W.map f) _ (map_notMem_range K₁ K₂ hσ hX),
      reducePoint_some_notMem K₁ W h hX, map_zero, map_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some σ (W.map (algebraMap 𝒪₁ K₁)) h
    have hx : σ (algebraMap 𝒪₁ K₁ x) = algebraMap 𝒪₂ K₂ (f x) := by
      rw [← RingHom.comp_apply, hσ, RingHom.comp_apply]
    have hy : σ (algebraMap 𝒪₁ K₁ y) = algebraMap 𝒪₂ K₂ (f y) := by
      rw [← RingHom.comp_apply, hσ, RingHom.comp_apply]
    have h₂ : (curveK K₂ (W.map f)).Nonsingular (algebraMap 𝒪₂ K₂ (f x))
        (algebraMap 𝒪₂ K₂ (f y)) := by
      have := (map_curveK_eq K₁ K₂ hσ W) ▸ h'
      rwa [hx, hy] at this
    have n₁ := nonsingular_residue_of_isElliptic K₁ W h.1
    have n₂ := nonsingular_residue_of_isElliptic K₂ (W.map f) h₂.1
    obtain ⟨n₁', e₁⟩ := pointMapRing_some (ResidueField.map f) (W.map (residue 𝒪₁)) n₁
    have e₂ : pointCongr (map_curveK_eq K₁ K₂ hσ W) (.some _ _ h') = .some _ _ h₂ := by
      rw [pointCongr_some, Point.some.injEq]
      exact ⟨hx, hy⟩
    rw [e, e₂, reducePoint_some_integral K₂ (W.map f) h₂ n₂, reducePoint_some_integral K₁ W h n₁,
      e₁, pointCongr_some, Point.some.injEq, ResidueField.map_residue, ResidueField.map_residue]
    exact ⟨rfl, rfl⟩

end Functorial

section FF

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

abbrev gaussCurve : WeierstrassCurve (gaussRing W) := W'.map (algebraMap 𝒪 (gaussRing W))

theorem gaussCurve_map_functionField :
    (gaussCurve W W').map (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField) =
      (W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField := by
  show W'.map ((algebraMap (gaussRing W) _).comp (algebraMap 𝒪 (gaussRing W))) =
    W'.map ((algebraMap K _).comp (algebraMap 𝒪 K))
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

theorem gaussCurve_map_residue :
    ((gaussCurve W W').map (residue (gaussRing W))).map (gaussResidue W) =
      (W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField := by
  simp only [gaussCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  ext c
  simp [gaussResidue_residue_algebraMap]

variable [W'.IsElliptic]

def reduceFF : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point →+
    ((W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField).toAffine.Point :=
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  (pointCongr (gaussCurve_map_residue W W')).toAddMonoidHom.comp
    ((pointMapRing (gaussResidue W) _).comp
      ((reductionHom (W.baseChange K).toAffine.FunctionField (gaussCurve W W')).comp
        (pointCongr (gaussCurve_map_functionField K W W').symm).toAddMonoidHom))

end FF

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.ReductionLift
namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (W : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j] in
include hxy in
theorem eval₂_polynomial_of_equation :
    W.toAffine.polynomial.eval₂ (eval₂RingHom j x) y = 0 := by
  have e := (equation_iff _ _).mp hxy
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    coe_eval₂RingHom]
  linear_combination e

def coordEval : W.toAffine.CoordinateRing →+* Λ :=
  AdjoinRoot.lift (eval₂RingHom j x) y (eval₂_polynomial_of_equation W j hxy)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j] in
theorem coordEval_mk (p : 𝒪[X][Y]) :
    coordEval W j hxy (CoordinateRing.mk W p) = p.eval₂ (eval₂RingHom j x) y :=
  AdjoinRoot.lift_mk _ _

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j] in
theorem coordEval_algebraMap (c : 𝒪) :
    coordEval W j hxy (algebraMap 𝒪 W.toAffine.CoordinateRing c) = j c := by
  rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
    coordEval, AdjoinRoot.lift_of]
  simp


include hxy in
theorem equation_residue_of_equation :
    ((W.map (residue 𝒪)).map (ResidueField.map j)).toAffine.Equation (residue Λ x)
      (residue Λ y) := by
  have e := (equation_iff _ _).mp hxy
  rw [equation_iff]
  have := congrArg (residue Λ) e
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_mul, map_pow] at this ⊢
  simp only [← RingHom.comp_apply (ResidueField.map j), ResidueField.map_comp_residue]
  simpa only [RingHom.comp_apply] using this


include hxy in
def coordEvalRed :
    (W.map (residue 𝒪)).toAffine.CoordinateRing →+* ResidueField Λ :=
  AdjoinRoot.lift (eval₂RingHom (ResidueField.map j) (residue Λ x)) (residue Λ y)
    (eval₂_polynomial_of_equation (W.map (residue 𝒪)) (ResidueField.map j)
      (equation_residue_of_equation W j hxy))

theorem coordReduce_of (q : 𝒪[X]) :
    coordReduce W (AdjoinRoot.of _ q) = AdjoinRoot.of _ (q.map (residue 𝒪)) := by
  rw [← AdjoinRoot.mk_C, coordReduce, CoordinateRing.map_mk, Polynomial.map_C, ← AdjoinRoot.mk_C]
  rfl

theorem coordReduce_root :
    coordReduce W (AdjoinRoot.root W.toAffine.polynomial) =
      AdjoinRoot.root (W.map (residue 𝒪)).toAffine.polynomial := by
  rw [← AdjoinRoot.mk_X, coordReduce, CoordinateRing.map_mk, Polynomial.map_X, AdjoinRoot.mk_X]

theorem residue_coordEval (a : W.toAffine.CoordinateRing) :
    residue Λ (coordEval W j hxy a) = coordEvalRed W j hxy (coordReduce W a) := by
  have : (residue Λ).comp (coordEval W j hxy) = (coordEvalRed W j hxy).comp (coordReduce W) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, coordReduce_of, coordEval, coordEvalRed, AdjoinRoot.lift_of,
          Polynomial.map_C, coe_eval₂RingHom, eval₂_C, ResidueField.map_residue]
      · simp only [RingHom.comp_apply, coordReduce_of, coordEval, coordEvalRed, AdjoinRoot.lift_of,
          Polynomial.map_X, coe_eval₂RingHom, eval₂_X]
    · simp only [RingHom.comp_apply, coordReduce_root, coordEval, coordEvalRed,
        AdjoinRoot.lift_root]
  exact congrArg (· a) this


omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem coordinateRing_ringHom_ext {S : Type*} [CommRing S]
    {f g : W.toAffine.CoordinateRing →+* S}
    (h₁ : ∀ c : 𝒪, f (algebraMap 𝒪 _ c) = g (algebraMap 𝒪 _ c))
    (h₂ : f (CoordinateRing.mk W (C X)) = g (CoordinateRing.mk W (C X)))
    (h₃ : f (CoordinateRing.mk W Y) = g (CoordinateRing.mk W Y)) : f = g := by
  have hc : ∀ c : 𝒪, algebraMap 𝒪 W.toAffine.CoordinateRing c =
      AdjoinRoot.of W.toAffine.polynomial (C c) := fun c => by
    rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply, hc] using h₁ c
    · simpa only [RingHom.comp_apply, AdjoinRoot.mk_C] using h₂
  · simpa only [AdjoinRoot.mk_X] using h₃

variable (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))


include hx in
theorem coordEvalRed_injective : Function.Injective (coordEvalRed W j hxy) := by
  let : Module.Finite (ResidueField 𝒪)[X] (W.map (residue 𝒪)).toAffine.CoordinateRing :=
    Module.Finite.of_basis (CoordinateRing.basis (W.map (residue 𝒪)).toAffine)
  let : Algebra.IsIntegral (ResidueField 𝒪)[X] (W.map (residue 𝒪)).toAffine.CoordinateRing :=
    Algebra.IsIntegral.of_finite _ _
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_under_eq_bot (R := (ResidueField 𝒪)[X])
  ext p
  simp only [Ideal.under, Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot,
    AdjoinRoot.algebraMap_eq, coordEvalRed, AdjoinRoot.lift_of]
  exact map_eq_zero_iff _ hx

include hx in
theorem isUnit_coordEval (s : (gaussPrime W).primeCompl) : IsUnit (coordEval W j hxy s) := by
  by_contra hs
  have h0 : residue Λ (coordEval W j hxy s) = 0 :=
    (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hs)
  rw [residue_coordEval] at h0
  exact s.2 (RingHom.mem_ker.2 ((map_eq_zero_iff _ (coordEvalRed_injective W j hxy hx)).1 h0))

def gaussLift : gaussRing W →+* Λ :=
  IsLocalization.lift (M := (gaussPrime W).primeCompl) (S := gaussRing W)
    (isUnit_coordEval W j hxy hx)

theorem gaussLift_algebraMap (a : W.toAffine.CoordinateRing) :
    gaussLift W j hxy hx (algebraMap _ _ a) = coordEval W j hxy a :=
  IsLocalization.lift_eq _ _

theorem gaussLift_algebraMap_base (c : 𝒪) :
    gaussLift W j hxy hx (algebraMap 𝒪 (gaussRing W) c) = j c := by
  rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
    gaussLift_algebraMap, coordEval_algebraMap]

instance isLocalHom_gaussLift : IsLocalHom (gaussLift W j hxy hx) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (gaussPrime W).primeCompl a
  dsimp only at ha ⊢
  have hspec := IsLocalization.mk'_spec (gaussRing W) r s
  have hr : IsUnit (coordEval W j hxy r) := by
    have := congrArg (gaussLift W j hxy hx) hspec
    rw [map_mul, gaussLift_algebraMap, gaussLift_algebraMap] at this
    rw [← this]
    exact ha.mul (isUnit_coordEval W j hxy hx s)
  have hr' : r ∈ (gaussPrime W).primeCompl := by
    intro hP
    have h0 : coordReduce W r = 0 := hP
    have h1 : residue Λ (coordEval W j hxy r) = 0 := by rw [residue_coordEval, h0, map_zero]
    exact (residue_ne_zero_iff_isUnit _).2 hr h1
  have hu : IsUnit (IsLocalization.mk' (gaussRing W) r s *
      algebraMap W.toAffine.CoordinateRing (gaussRing W) (s : W.toAffine.CoordinateRing)) := by
    rw [hspec]; exact IsLocalization.map_units _ ⟨r, hr'⟩
  exact isUnit_of_mul_isUnit_left hu

def fieldEvalRed : (W.map (residue 𝒪)).toAffine.FunctionField →+* ResidueField Λ :=
  IsFractionRing.lift (coordEvalRed_injective W j hxy hx)

theorem residueField_map_gaussLift :
    ResidueField.map (gaussLift W j hxy hx) = (fieldEvalRed W j hxy hx).comp (gaussResidue W) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (W.toAffine.CoordinateRing ⧸ gaussPrime W))
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, Ideal.algebraMap_quotient_residueField_mk]
  have e : algebraMap W.toAffine.CoordinateRing (gaussPrime W).ResidueField a =
      residue (gaussRing W) (algebraMap _ (gaussRing W) a) := by
    rw [IsScalarTower.algebraMap_apply _ (Localization.AtPrime (gaussPrime W))
      (gaussPrime W).ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
  rw [e, ResidueField.map_residue, gaussLift_algebraMap, gaussResidue_residue, fieldEvalRed,
    IsFractionRing.lift_algebraMap, residue_coordEval]

theorem fieldEvalRed_genX : fieldEvalRed W j hxy hx (genX (W.map (residue 𝒪))) = residue Λ x := by
  rw [genX, fieldEvalRed, IsFractionRing.lift_algebraMap, coordEvalRed, AdjoinRoot.lift_mk]
  simp

theorem fieldEvalRed_genY : fieldEvalRed W j hxy hx (genY (W.map (residue 𝒪))) = residue Λ y := by
  rw [genY, fieldEvalRed, IsFractionRing.lift_algebraMap, coordEvalRed, AdjoinRoot.lift_mk]
  simp

theorem fieldEvalRed_algebraMap (c : ResidueField 𝒪) :
    fieldEvalRed W j hxy hx (algebraMap (ResidueField 𝒪) _ c) = ResidueField.map j c := by
  rw [IsScalarTower.algebraMap_apply (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.CoordinateRing,
    fieldEvalRed, IsFractionRing.lift_algebraMap, IsScalarTower.algebraMap_apply (ResidueField 𝒪)
      (ResidueField 𝒪)[X], AdjoinRoot.algebraMap_eq, coordEvalRed, AdjoinRoot.lift_of]
  simp

section Fraction

variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (M : Type*) [Field M]
  [Algebra Λ M]

theorem comp_algebraMap_gaussLift (σ : (W.baseChange K).toAffine.FunctionField →+* M)
    (hσ : ∀ c : 𝒪, σ (algebraMap 𝒪 _ c) = algebraMap Λ M (j c))
    (hX : σ (genX (W.baseChange K)) = algebraMap Λ M x)
    (hY : σ (genY (W.baseChange K)) = algebraMap Λ M y) :
    σ.comp (algebraMap (gaussRing W) _) = (algebraMap Λ M).comp (gaussLift W j hxy hx) := by
  apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
  apply coordinateRing_ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, gaussLift_algebraMap,
      coordEval_algebraMap, hσ, gaussLift_algebraMap_base]
  · simp only [RingHom.comp_apply, gaussLift_algebraMap, coordEval_mk]
    rw [← gaussX, algebraMap_gaussX, hX]
    simp
  · simp only [RingHom.comp_apply, gaussLift_algebraMap, coordEval_mk]
    rw [← gaussY, algebraMap_gaussY, hY]
    simp

end Fraction

end

end GroundTheory.Global
end

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

section Transport

theorem pointCongr_pointCongr {F : Type*} [Field F] [DecidableEq F]
    {V₁ V₂ V₃ : WeierstrassCurve F} (h₁ : V₁ = V₂) (h₂ : V₂ = V₃) (P : V₁.toAffine.Point) :
    pointCongr h₂ (pointCongr h₁ P) = pointCongr (h₁.trans h₂) P := by
  subst h₁; subst h₂; rfl

theorem pointMapRing_pointCongr {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    (f : F →+* L) {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    pointMapRing f V₂ (pointCongr h P) =
      pointCongr (congrArg (fun V => V.map f) h) (pointMapRing f V₁ P) := by
  subst h; rfl

theorem pointMapRing_congr {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    {f g : F →+* L} (h : f = g) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    pointMapRing f V P = pointCongr (by rw [h]) (pointMapRing g V P) := by
  subst h; rfl

theorem pointMapRing_pointMapRing {F L L' : Type*} [Field F] [Field L] [Field L'] [DecidableEq F]
    [DecidableEq L] [DecidableEq L'] (f : F →+* L) (g : L →+* L') (V : WeierstrassCurve F)
    (P : V.toAffine.Point) :
    pointMapRing g (V.map f) (pointMapRing f V P) = pointMapRing (g.comp f) V P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem map_eq_pointCongr_pointMapRing {R F₁ F₂ : Type*} [CommRing R] [Field F₁] [Field F₂]
    [Algebra R F₁] [Algebra R F₂] [DecidableEq F₁] [DecidableEq F₂] (V : WeierstrassCurve R)
    (σ : F₁ →ₐ[R] F₂) (P : (V.baseChange F₁).toAffine.Point) :
    Point.map σ P = pointCongr (by
        show V.map (σ.toRingHom.comp (algebraMap R F₁)) = V.map (algebraMap R F₂)
        exact congrArg V.map σ.comp_algebraMap) (pointMapRing σ.toRingHom (V.baseChange F₁) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero (pointCongr _)).symm
  · rw [Point.map_some]
    obtain ⟨h', e⟩ := pointMapRing_some σ.toRingHom (V.baseChange F₁) h
    rw [e, pointCongr_some, Point.some.injEq]
    exact ⟨rfl, rfl⟩

theorem reducePoint_pointCongr {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (K : Type*) [Field K] [Algebra 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
    {V₁ V₂ : WeierstrassCurve 𝒪} (h : V₁ = V₂) (P : (curveK K V₁).Point) :
    reducePoint K V₂ (pointCongr (congrArg (fun V => V.map (algebraMap 𝒪 K)) h) P) =
      pointCongr (congrArg (fun V => V.map (residue 𝒪)) h) (reducePoint K V₁ P) := by
  subst h; rfl

end Transport

section Eval

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  (M : Type*) [Field M] [Algebra Λ M] [IsFractionRing Λ M] [Algebra K M] [DecidableEq M]
  [DecidableEq (ResidueField Λ)]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] [IsDomain Λ]
  [IsDiscreteValuationRing Λ] [IsLocalHom j] [IsFractionRing Λ M] [DecidableEq M]
  [DecidableEq (ResidueField Λ)] in
theorem map_baseChange_eq_map_of
    (hjM : ∀ c : 𝒪, algebraMap K M (algebraMap 𝒪 K c) = algebraMap Λ M (j c)) :
    (W'.baseChange K).baseChange M = (W'.map j).map (algebraMap Λ M) := by
  show W'.map ((algebraMap K M).comp (algebraMap 𝒪 K)) = W'.map ((algebraMap Λ M).comp j)
  congr 1
  exact RingHom.ext hjM

variable {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)
  (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))

theorem map_fieldEvalRed_eq :
    ((W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField).map
      (fieldEvalRed W j hxy hx) = (W'.map j).map (residue Λ) := by
  show W'.map (((fieldEvalRed W j hxy hx).comp (algebraMap (ResidueField 𝒪) _)).comp
    (residue 𝒪)) = W'.map ((residue Λ).comp j)
  congr 1
  refine RingHom.ext fun c => ?_
  simp [fieldEvalRed_algebraMap, ResidueField.map_residue]

variable [W'.IsElliptic]

theorem reducePoint_genEval
    (hjM : ∀ c : 𝒪, algebraMap K M (algebraMap 𝒪 K c) = algebraMap Λ M (j c))
    (hR : ((W.baseChange K).baseChange M).toAffine.Nonsingular (algebraMap Λ M x)
      (algebraMap Λ M y))
    (hRg : IsGenPt (W.baseChange K) (Point.some _ _ hR))
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point) :
    reducePoint M (W'.map j) (pointCongr (map_baseChange_eq_map_of K W' j M hjM)
        (Point.map (genEval (W.baseChange K) _ hRg) Q)) =
      pointCongr (map_fieldEvalRed_eq W W' j hxy hx)
        (pointMapRing (fieldEvalRed W j hxy hx) _ (reduceFF K W W' Q)) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  set σ := genEval (W.baseChange K) _ hRg
  have hσ : σ.toRingHom.comp (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField) =
      (algebraMap Λ M).comp (gaussLift W j hxy hx) := by
    apply comp_algebraMap_gaussLift
    · intro c
      show σ (algebraMap 𝒪 _ c) = _
      rw [IsScalarTower.algebraMap_apply 𝒪 K, σ.commutes, hjM]
    · exact genEval_genX _ _ hRg
    · exact genEval_genY _ _ hRg
  have c0 : (gaussCurve W W').map (gaussLift W j hxy hx) = W'.map j := by
    show W'.map ((gaussLift W j hxy hx).comp (algebraMap 𝒪 (gaussRing W))) = W'.map j
    exact congrArg W'.map (RingHom.ext (gaussLift_algebraMap_base W j hxy hx))
  set Q₀ := pointCongr (gaussCurve_map_functionField K W W').symm Q with hQ₀
  have hQ : Q = pointCongr (gaussCurve_map_functionField K W W') Q₀ := by
    rw [hQ₀, pointCongr_pointCongr]; rfl
  have key := reducePoint_pointMapRing (W.baseChange K).toAffine.FunctionField M hσ
    (gaussCurve W W') Q₀
  have lhs : pointCongr (map_baseChange_eq_map_of K W' j M hjM) (Point.map σ Q) =
      pointCongr (congrArg (fun V => V.map (algebraMap Λ M)) c0)
        (pointCongr (map_curveK_eq _ M hσ (gaussCurve W W')) (pointMapRing σ.toRingHom _ Q₀)) := by
    rw [map_eq_pointCongr_pointMapRing, hQ, pointMapRing_pointCongr, pointCongr_pointCongr,
      pointCongr_pointCongr, pointCongr_pointCongr]
  rw [lhs, reducePoint_pointCongr, key, pointMapRing_congr (residueField_map_gaussLift W j hxy hx),
    ← pointMapRing_pointMapRing]
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [pointMapRing_pointCongr]
  erw [pointCongr_pointCongr, pointCongr_pointCongr, pointCongr_pointCongr]
  · rfl
  · exact c0

end Eval

end

end GroundTheory.Global
