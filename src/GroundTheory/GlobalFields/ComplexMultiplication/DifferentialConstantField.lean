module

public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialBaseChange
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.SupersingularPowField

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
namespace GroundTheory.Global

open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

section Descent

variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem exists_eq_add_mul_genY (c : E.toAffine.FunctionField) :
    ∃ r s : E.toAffine.FunctionField, r ∈ F⟮genX E⟯ ∧ s ∈ F⟮genX E⟯ ∧ c = r + s * genY E := by
  set F₁ := F⟮genX E⟯
  have hfin : FiniteDimensional F₁ E.toAffine.FunctionField :=
    Module.finite_of_finrank_pos (by rw [finrank_adjoin_genX E]; norm_num)
  have hint : IsIntegral F₁ (genY E) := Algebra.IsIntegral.isIntegral _
  have htop : F₁⟮genY E⟯ = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := F),
      IntermediateField.adjoin_simple_adjoin_simple]
    exact adjoin_genX_genY E
  have hdeg : (minpoly F₁ (genY E)).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top',
      finrank_adjoin_genX E]
  have hc : c ∈ (F₁⟮genY E⟯).toSubalgebra := by rw [htop]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨p, rfl⟩ := hc
  have hm1 : minpoly F₁ (genY E) ≠ 1 := fun h => by rw [h, natDegree_one] at hdeg; omega
  have hq : (p %ₘ minpoly F₁ (genY E)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p (minpoly.monic hint) hm1
    omega
  have hval : aeval (genY E) p = aeval (genY E) (p %ₘ minpoly F₁ (genY E)) :=
    (aeval_modByMonic_eq_self_of_root (minpoly.aeval F₁ (genY E))).symm
  obtain ⟨q, hqdef⟩ : ∃ q, q = p %ₘ minpoly F₁ (genY E) := ⟨_, rfl⟩
  rw [← hqdef] at hq hval
  refine ⟨(q.coeff 0 : E.toAffine.FunctionField), (q.coeff 1 : E.toAffine.FunctionField),
    (q.coeff 0).2, (q.coeff 1).2, ?_⟩
  change aeval (genY E) p = _
  rw [hval, eq_X_add_C_of_natDegree_le_one hq]
  simp only [map_add (f := _), map_mul, aeval_C, aeval_X, coeff_add, coeff_C_mul_X, coeff_C]
  simp
  ring

variable {F' : Type u} [Field F'] [Algebra F F']

theorem exists_algebraMap_eq_of_bcEmb {c : E.toAffine.FunctionField} {a : F'}
    (h : bcEmb (F' := F') E c = algebraMap F' (E.baseChange F').toAffine.FunctionField a) :
    ∃ a₀ : F, algebraMap F E.toAffine.FunctionField a₀ = c := by
  set K' := (E.baseChange F').toAffine.FunctionField
  have hinj : Function.Injective (bcEmb (F' := F') E) := (bcEmb (F' := F') E).toRingHom.injective
  have hmap : ∀ w ∈ F⟮genX E⟯, bcEmb (F' := F') E w ∈ F'⟮genX (E.baseChange F')⟯ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx, bcEmb_genX]; exact mem_adjoin_simple_self F' _
    | algebraMap x =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' K']
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨r, s, hr, hs, rfl⟩ := exists_eq_add_mul_genY E c
  rw [map_add (f := _), map_mul, bcEmb_genY] at h
  have hs0 : bcEmb (F' := F') E s = 0 := by
    by_contra hne
    apply genY_not_mem (E.baseChange F')
    have e : genY (E.baseChange F') =
        (algebraMap F' K' a - bcEmb (F' := F') E r) / bcEmb (F' := F') E s := by
      rw [eq_div_iff hne]; linear_combination h
    rw [e]
    exact div_mem (sub_mem (IntermediateField.algebraMap_mem _ a) (hmap r hr)) (hmap s hs)
  have hs00 : s = 0 := hinj (by rw [hs0, map_zero])
  rw [hs0, zero_mul, add_zero] at h
  rw [hs00, zero_mul, add_zero]
  obtain ⟨p, q, rfl⟩ := (mem_adjoin_simple_iff F r).mp hr
  by_cases hq0 : aeval (genX E) q = 0
  · exact ⟨0, by rw [hq0, div_zero, map_zero]⟩
  have hq : q ≠ 0 := fun h0 => hq0 (by rw [h0, map_zero])
  have hq0' : aeval (genX (E.baseChange F')) q ≠ 0 := by
    rw [← bcEmb_genX, aeval_algHom_apply]
    exact fun h0 => hq0 (hinj (by rw [h0, map_zero]))
  rw [map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, bcEmb_genX, div_eq_iff hq0'] at h
  have key : aeval (genX (E.baseChange F'))
      (p.map (algebraMap F F') - C a * q.map (algebraMap F F')) = 0 := by
    rw [map_sub, map_mul, aeval_C, aeval_map_algebraMap, aeval_map_algebraMap]
    linear_combination h
  rw [aeval_genX_eq_zero_iff] at key
  have hcoeff : ∀ j, algebraMap F F' (p.coeff j) = a * algebraMap F F' (q.coeff j) := by
    intro j
    have := congrArg (fun (f : F'[X]) => f.coeff j) key
    simp only [coeff_sub, coeff_map, coeff_C_mul, coeff_zero] at this
    linear_combination this
  have hqi : q.coeff q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hq
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : F, a₀ = p.coeff q.natDegree / q.coeff q.natDegree := ⟨_, rfl⟩
  have ha : a = algebraMap F F' a₀ := by
    rw [ha₀, map_div₀, hcoeff, mul_div_cancel_right₀ _ ((_root_.map_ne_zero _).mpr hqi)]
  have hp : p = C a₀ * q := by
    ext j
    apply (algebraMap F F').injective
    rw [coeff_C_mul, map_mul, hcoeff j, ← ha]
  refine ⟨a₀, ?_⟩
  rw [hp, map_mul, aeval_C, mul_div_cancel_right₀ _ hq0]

end Descent

section Constant

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem exists_algebraMap_eq_isogCoeff (φ : Isogeny E E') :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = isogCoeff φ := by
  classical
  obtain ⟨b, hb⟩ := exists_isogCoeff_eq_algebraMap
    (isogBaseChange (F' := AlgebraicClosure F) φ)
  rw [isogCoeff_isogBaseChange] at hb
  exact exists_algebraMap_eq_of_bcEmb E hb.symm

noncomputable def invConst (φ : Isogeny E E') : F :=
  (exists_algebraMap_eq_isogCoeff φ).choose

theorem algebraMap_invConst (φ : Isogeny E E') :
    algebraMap F E.toAffine.FunctionField (invConst φ) = isogCoeff φ :=
  (exists_algebraMap_eq_isogCoeff φ).choose_spec

theorem isogenyPullback_eq_invConst_smul (φ : Isogeny E E') :
    isogenyPullback φ (invariantDifferential E') = invConst φ • invariantDifferential E := by
  rw [isogenyPullback_invariantDifferential_eq_smul, ← algebraMap_invConst, algebraMap_smul]


variable (E) in
theorem invConst_mulIsogeny (n : ℤ) (hn : n ≠ 0) : invConst (mulIsogeny E n hn) = n :=
  (algebraMap F E.toAffine.FunctionField).injective (by
    rw [algebraMap_invConst, isogCoeff_mulIsogeny, map_intCast])

theorem invConst_isogBaseChange {F' : Type u} [Field F'] [Algebra F F'] [DecidableEq F']
    (φ : Isogeny E E') :
    invConst (isogBaseChange (F' := F') φ) = algebraMap F F' (invConst φ) :=
  (algebraMap F' (E.baseChange F').toAffine.FunctionField).injective (by
    rw [algebraMap_invConst, isogCoeff_isogBaseChange, ← algebraMap_invConst, AlgHom.commutes,
      IsScalarTower.algebraMap_apply F F' (E.baseChange F').toAffine.FunctionField])

end Constant

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobenius
namespace GroundTheory.Global

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField GroundTheory.Arith.Abelian

universe u

section Twist

variable {F : Type u} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable def frobeniusTwist : WeierstrassCurve F := E.map (frobenius F p)

instance [E.IsElliptic] : (frobeniusTwist E p).IsElliptic := by
  unfold frobeniusTwist; infer_instance

theorem j_frobeniusTwist [E.IsElliptic] : (frobeniusTwist E p).j = E.j ^ p := by
  show (E.map (frobenius F p)).j = _
  rw [map_j, frobenius_def]

variable {L : Type*} [Field L] [Algebra F L] [CharP L p]

theorem baseChange_frobeniusTwist :
    (frobeniusTwist E p).baseChange L = (E.baseChange L).map (frobenius L p) := by
  show (E.map (frobenius F p)).map (algebraMap F L) = (E.map (algebraMap F L)).map (frobenius L p)
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  congr 1
  ext c
  simp [frobenius_def]

theorem nonsingular_pow {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) :
    ((frobeniusTwist E p).baseChange L).toAffine.Nonsingular (x ^ p) (y ^ p) := by
  rw [baseChange_frobeniusTwist]
  have := ((E.baseChange L).toAffine.map_nonsingular (frobenius L p).injective x y).mpr h
  simpa only [frobenius_def] using this

theorem nonsingular_pow_iff {x y : L} :
    ((frobeniusTwist E p).baseChange L).toAffine.Nonsingular (x ^ p) (y ^ p) ↔
      (E.baseChange L).toAffine.Nonsingular x y := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_nonsingular (frobenius L p).injective x y
  simpa only [frobenius_def] using this

theorem negY_pow (x y : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.negY (x ^ p) (y ^ p) =
      (E.baseChange L).toAffine.negY x y ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_negY (frobenius L p) x y
  simpa only [frobenius_def] using this

theorem addX_pow (x₁ x₂ ℓ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.addX (x₁ ^ p) (x₂ ^ p) (ℓ ^ p) =
      (E.baseChange L).toAffine.addX x₁ x₂ ℓ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_addX (frobenius L p) x₁ x₂ ℓ
  simpa only [frobenius_def] using this

theorem addY_pow (x₁ x₂ y₁ ℓ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.addY (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (ℓ ^ p) =
      (E.baseChange L).toAffine.addY x₁ x₂ y₁ ℓ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_addY (frobenius L p) x₁ y₁ x₂ ℓ
  simpa only [frobenius_def] using this

theorem slope_pow [DecidableEq L] (x₁ x₂ y₁ y₂ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.slope (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (y₂ ^ p) =
      (E.baseChange L).toAffine.slope x₁ x₂ y₁ y₂ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_slope (frobenius L p) x₁ x₂ y₁ y₂
  simpa only [frobenius_def] using this

end Twist

section PointMap

variable {F : Type u} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable def frobeniusPoint (L : Type*) [Field L] [Algebra F L] [CharP L p] :
    (E.baseChange L).toAffine.Point → ((frobeniusTwist E p).baseChange L).toAffine.Point
  | .zero => 0
  | .some x y h => .some (x ^ p) (y ^ p) (nonsingular_pow E p h)

variable {L : Type*} [Field L] [Algebra F L] [CharP L p]

theorem frobeniusPoint_some {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) :
    frobeniusPoint E p L (.some x y h) = .some (x ^ p) (y ^ p) (nonsingular_pow E p h) := rfl

theorem frobeniusPoint_add [DecidableEq L] (P Q : (E.baseChange L).toAffine.Point) :
    frobeniusPoint E p L (P + Q) = frobeniusPoint E p L P + frobeniusPoint E p L Q := by
  have hinj : Function.Injective fun z : L => z ^ p := by
    intro a b hab
    exact frobenius_inj L p (by simpa only [frobenius_def] using hab)
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · show frobeniusPoint E p L (0 + Q) = 0 + frobeniusPoint E p L Q
    rw [zero_add, zero_add]
  rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  · show frobeniusPoint E p L (Point.some x₁ y₁ h₁ + 0) = frobeniusPoint E p L (Point.some x₁ y₁ h₁) + 0
    rw [add_zero, add_zero]
  rw [frobeniusPoint_some, frobeniusPoint_some]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (E.baseChange L).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, Point.add_of_Y_eq (congrArg (· ^ p) hxy.1)
      (by rw [negY_pow, hxy.2])]
    rfl
  · have hxy' : ¬(x₁ ^ p = x₂ ^ p ∧
        y₁ ^ p = ((frobeniusTwist E p).baseChange L).toAffine.negY (x₂ ^ p) (y₂ ^ p)) := by
      rintro ⟨hx, hy⟩
      rw [negY_pow] at hy
      exact hxy ⟨hinj hx, hinj hy⟩
    rw [Point.add_some hxy, Point.add_some hxy', frobeniusPoint_some, Point.some.injEq,
      slope_pow, addX_pow, addY_pow]
    exact ⟨rfl, rfl⟩

theorem isGenPt_frobeniusPoint_iff (P : (E.baseChange L).toAffine.Point) :
    IsGenPt (frobeniusTwist E p) (frobeniusPoint E p L P) ↔ IsGenPt E P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · exact Iff.rfl
  · rw [frobeniusPoint_some, isGenPt_some, isGenPt_some]
    exact ⟨fun ht hx => ht (hx.pow p), fun ht => ht.pow hp.out.pos⟩

end PointMap

section FrobeniusIsogeny

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] (p : ℕ) [hp : Fact p.Prime]
  [CharP F p]

omit [E.IsElliptic] in
theorem map_frobeniusPoint {L L' : Type*} [Field L] [Algebra F L] [CharP L p] [Field L']
    [Algebra F L'] [CharP L' p] [DecidableEq L] [DecidableEq L'] (σ : L →ₐ[F] L')
    (P : (E.baseChange L).toAffine.Point) :
    Point.map σ (frobeniusPoint E p L P) = frobeniusPoint E p L' (Point.map σ P) := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [frobeniusPoint_some, Point.map_some, map_pow]

noncomputable def frobeniusGenPt :
    ((frobeniusTwist E p).baseChange E.toAffine.FunctionField).toAffine.Point :=
  frobeniusPoint E p _ (genericPoint E)

theorem map_genEval_frobeniusGenPt {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    Point.map (genEval E P hP) (frobeniusGenPt E p) = frobeniusPoint E p L P := by
  classical
  rw [frobeniusGenPt, map_frobeniusPoint, map_genEval_genericPoint]

theorem isGenPt_frobeniusGenPt : IsGenPt (frobeniusTwist E p) (frobeniusGenPt E p) :=
  (isGenPt_frobeniusPoint_iff E p _).mpr (transcendental_genX E)

theorem respectsAdd_frobeniusGenPt : RespectsAdd E (frobeniusTwist E p) (frobeniusGenPt E p) := by
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  rw [map_genEval_frobeniusGenPt, map_genEval_frobeniusGenPt, map_genEval_frobeniusGenPt,
    frobeniusPoint_add]

noncomputable def frobeniusIsogeny : Isogeny E (frobeniusTwist E p) :=
  ⟨frobeniusGenPt E p, (isIsogeny_iff _).mpr
    ⟨isGenPt_frobeniusGenPt E p, respectsAdd_frobeniusGenPt E p⟩⟩

theorem frobeniusIsogeny_app {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    (frobeniusIsogeny E p).app P hP = frobeniusPoint E p L P :=
  map_genEval_frobeniusGenPt E p P hP

theorem comap_frobeniusIsogeny_genX :
    (frobeniusIsogeny E p).comap (genX (frobeniusTwist E p)) = genX E ^ p :=
  (frobeniusIsogeny E p).comap_genX

theorem comap_frobeniusIsogeny_genY :
    (frobeniusIsogeny E p).comap (genY (frobeniusTwist E p)) = genY E ^ p :=
  (frobeniusIsogeny E p).comap_genY

theorem fieldRange_comap_frobeniusIsogeny :
    (frobeniusIsogeny E p).comap.fieldRange = powField E p := by
  rw [← map_top_eq_fieldRange, ← adjoin_genX_genY (frobeniusTwist E p), adjoin_map, powField]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton, comap_frobeniusIsogeny_genX,
    comap_frobeniusIsogeny_genY]

theorem degree_frobeniusIsogeny [PerfectRing F p] : (frobeniusIsogeny E p).degree = p := by
  have h := congrArg (fun M : IntermediateField F E.toAffine.FunctionField =>
    Module.finrank M E.toAffine.FunctionField) (fieldRange_comap_frobeniusIsogeny E p)
  rw [Isogeny.degree]
  exact h.trans (finrank_powField E p)

end FrobeniusIsogeny

end GroundTheory.Global
end
