module

public import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraic
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso
abbrev periodLatticeEnd (L : PeriodPair) : Subring ℂ where
  carrier := {a | ∀ z ∈ L.lattice, a * z ∈ L.lattice}
  zero_mem' z _ := by rw [zero_mul]; exact zero_mem _
  one_mem' z hz := by simpa only [one_mul] using hz
  add_mem' ha hb z hz := by rw [add_mul]; exact add_mem (ha z hz) (hb z hz)
  neg_mem' ha z hz := by rw [neg_mul]; exact neg_mem (ha z hz)
  mul_mem' ha hb z hz := by rw [mul_assoc]; exact ha _ (hb z hz)

open WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

universe u

section Points

variable {F : Type u} [Field F] (C : VariableChange F) {E E' : WeierstrassCurve F}

theorem baseChange_smul_eq (L : Type*) [Field L] [Algebra F L] (h : C • E = E') :
    C.baseChange L • E.baseChange L = E'.baseChange L := by
  subst h
  exact map_variableChange _ _ _

theorem map_vcPoint {L L' : Type*} [Field L] [Algebra F L] [Field L'] [Algebra F L'] [DecidableEq L]
    [DecidableEq L'] (f : L →ₐ[F] L') (h : C • E = E') (P : (E.baseChange L).toAffine.Point) :
    Point.map f (vcPoint (C.baseChange L) (baseChange_smul_eq C L h) P) =
      vcPoint (C.baseChange L') (baseChange_smul_eq C L' h) (Point.map f P) := by
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rw [vcPoint_some, Point.map_some, Point.map_some, vcPoint_some, Point.some.injEq]
    have hC : (C.baseChange L).map (f : L →+* L') = C.baseChange L' :=
      VariableChange.map_baseChange C f
    constructor
    · have := map_vcX (C.baseChange L) (f : L →+* L') x
      rw [hC] at this
      exact this
    · have := map_vcY (C.baseChange L) (f : L →+* L') x y
      rw [hC] at this
      exact this

theorem vcPoint_vcPoint_of_eq_inv {L : Type*} [Field L] {W W₂ : WeierstrassCurve L}
    (D D' : VariableChange L) (hD : D' = D⁻¹) (h₁ : D • W = W₂) (h₂ : D' • W₂ = W)
    (P : W.toAffine.Point) : vcPoint D' h₂ (vcPoint D h₁ P) = P := by
  subst hD
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rw [vcPoint_some, vcPoint_some, Point.some.injEq]
    have hu := D.u.inv_mul
    simp only [vcX, vcY, VariableChange.inv_def, inv_inv]
    constructor
    · linear_combination x * (((D.u⁻¹ : Lˣ) : L) * D.u + 1) * hu
    · linear_combination y * ((((D.u⁻¹ : Lˣ) : L) * D.u) ^ 2 + ((D.u⁻¹ : Lˣ) : L) * D.u + 1) * hu

theorem vcPoint_eq_zero_iff {L : Type*} [Field L] {W W₂ : WeierstrassCurve L} (D : VariableChange L)
    (h : D • W = W₂) {P : W.toAffine.Point} : vcPoint D h P = 0 ↔ P = 0 := by
  constructor
  · intro e
    exact vcPoint_injective D h (e.trans (vcPoint_zero D h).symm)
  · rintro rfl
    rfl

end Points

section Hom

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] (C : VariableChange F)
  {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

def vcPt (h : C • E = E') : (E'.baseChange E.toAffine.FunctionField).toAffine.Point :=
  vcPoint (C.baseChange _) (baseChange_smul_eq C _ h) (genericPoint E)

theorem respectsAdd_vcPt (h : C • E = E') : RespectsAdd E E' (vcPt C h) := by
  intro L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ h₁ h₂ h₃ t₁ t₂ t₃ hs
  simp only [ratMapValue, vcPt]
  rw [map_vcPoint C _ h, map_vcPoint C _ h, map_vcPoint C _ h, map_liftPoint_genericPoint E h₁ t₁,
    map_liftPoint_genericPoint E h₂ t₂, map_liftPoint_genericPoint E h₃ t₃, ← vcPoint_add, hs]

def vcHom (h : C • E = E') : isogHom E E' := ⟨vcPt C h, respectsAdd_vcPt C h⟩

theorem vcPt_ne_zero (h : C • E = E') : vcPt C h ≠ 0 := by
  rw [vcPt, Ne, vcPoint_eq_zero_iff]
  exact isGenPt_ne_zero E isGenPt_genericPoint

theorem isGenPt_vcHom (h : C • E = E') : IsGenPt E' (vcHom C h).1 :=
  isGenPt_of_mem_isogHom (vcHom C h).2 (vcPt_ne_zero C h)

theorem map_vcHom {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (g : E.toAffine.FunctionField →ₐ[F] L) (h : C • E = E') :
    Point.map g (vcHom C h).1 =
      vcPoint (C.baseChange L) (baseChange_smul_eq C L h) (Point.map g (genericPoint E)) :=
  map_vcPoint C g h (genericPoint E)

omit [IsAlgClosed F] [DecidableEq F] [E.IsElliptic] [E'.IsElliptic] in
theorem inv_smul_eq_of_smul_eq (h : C • E = E') : C⁻¹ • E' = E := by
  rw [← h, inv_smul_smul]

theorem homComp_vcHom_vcHom (D : VariableChange F) (hD : D = C⁻¹) (h : C • E = E')
    (h' : D • E' = E) : homComp (vcHom D h') (vcHom C h) = homId := by
  apply Subtype.ext
  rw [homComp_of_isGenPt _ _ (isGenPt_vcHom C h)]
  rw [map_vcHom, map_genEval_genericPoint]
  have hD' : D.baseChange E.toAffine.FunctionField = (C.baseChange E.toAffine.FunctionField)⁻¹ := by
    subst hD
    exact map_inv (VariableChange.mapHom (algebraMap F E.toAffine.FunctionField)) C
  exact vcPoint_vcPoint_of_eq_inv _ _ hD' (baseChange_smul_eq C _ h) (baseChange_smul_eq D _ h')
    (genericPoint E)

def vcEndEquiv (h : C • E = E') : isogEnd E ≃+* isogEnd E' where
  toFun f := homComp (vcHom C h) (homComp f (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)))
  invFun g := homComp (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)) (homComp g (vcHom C h))
  left_inv f := by
    simp only [homComp_assoc, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h),
      homComp_id_right]
    rw [← homComp_assoc, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h),
      homComp_id_left]
  right_inv g := by
    simp only [homComp_assoc,
      homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h, homComp_id_right]
    rw [← homComp_assoc,
      homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h, homComp_id_left]
  map_mul' f g := by
    simp only [isogEnd_mul_def, homComp_assoc]
    rw [← homComp_assoc (vcHom C⁻¹ _) (vcHom C h),
      homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h), homComp_id_left]
  map_add' f g := by
    rw [homComp_add_left, homComp_add_right]

theorem vcEndEquiv_apply (h : C • E = E') (f : isogEnd E) :
    vcEndEquiv C h f = homComp (vcHom C h) (homComp f (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h))) :=
  rfl

end Hom

section Const

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]
  {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem homConst_homComp (R : isogHom E' E'') (Q : isogHom E E') :
    homConst E E'' (homComp R Q) = homConst E' E'' R * homConst E E' Q := by
  by_cases hQ : IsGenPt E' Q.1
  · set g := genEval E' Q.1 hQ
    have key : algebraMap F E.toAffine.FunctionField (homConst E' E'' R * homConst E E' Q) •
        invariantDifferential E = omegaAt E'' (homComp R Q).1 := by
      rw [homComp_of_isGenPt _ _ hQ, ← kpush_omegaAt, omegaAt_eq_homConst_smul,
        ← algebraMap_smul E'.toAffine.FunctionField (homConst E' E'' R) (invariantDifferential E'),
        kpush_smul, AlgHom.commutes,
        show invariantDifferential E' = omegaAt E' (genericPoint E') from rfl, kpush_omegaAt, map_genEval_genericPoint,
        omegaAt_eq_homConst_smul, ← algebraMap_smul E.toAffine.FunctionField (homConst E E' Q),
        smul_smul, ← map_mul]
    apply (algebraMap F E.toAffine.FunctionField).injective
    rw [algebraMap_homConst]
    have h2 := homCoeff_smul (homComp R Q)
    rw [← key] at h2
    exact smul_left_injective _ (invariantDifferential_ne_zero E) h2
  · rw [eq_zero_of_not_isGenPt Q hQ, homComp_zero_right, map_zero, map_zero, mul_zero]

theorem homConst_homId : homConst E E (homId : isogEnd E) = 1 := by
  apply (algebraMap F E.toAffine.FunctionField).injective
  rw [algebraMap_homConst, map_one]
  exact invCoeff_invariantDifferential E


variable (E) in
def endConst : isogEnd E →+* F where
  toFun := homConst E E
  map_one' := homConst_homId
  map_mul' f g := homConst_homComp f g
  map_zero' := map_zero _
  map_add' := map_add _

theorem endConst_apply (f : isogEnd E) : endConst E f = homConst E E f := rfl

theorem endConst_vcEndEquiv (C : VariableChange F) (h : C • E = E') (f : isogEnd E) :
    endConst E' (vcEndEquiv C h f) = endConst E f := by
  have e := homConst_homComp (vcHom C h) (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h))
  rw [homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h,
    homConst_homId] at e
  rw [endConst_apply, endConst_apply, vcEndEquiv_apply, homConst_homComp, homConst_homComp]
  linear_combination (-(homConst E E f)) * e

end Const

section Complex

variable {E : WeierstrassCurve ℂ} [E.IsElliptic]

theorem endConst_latticeEndEquiv (L : PeriodPair) (α : periodLatticeEnd L) :
    endConst (weierstrassCurve L) (latticeEndEquiv L α) = α :=
  homConst_latticeEndEquiv L α

theorem range_endConst_weierstrassCurve (L : PeriodPair) :
    (endConst (weierstrassCurve L)).range = periodLatticeEnd L := by
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨α, rfl⟩ := (latticeEndEquiv L).surjective f
    exact (endConst_latticeEndEquiv L α).symm ▸ α.2
  · intro hz
    exact ⟨latticeEndEquiv L ⟨z, hz⟩, endConst_latticeEndEquiv L ⟨z, hz⟩⟩

theorem endConst_injective : Function.Injective (endConst E) := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_weierstrassCurve E
  intro f g hfg
  apply (vcEndEquiv C hC).injective
  apply (latticeEndEquiv L).symm.injective
  apply Subtype.ext
  have hf := endConst_latticeEndEquiv L ((latticeEndEquiv L).symm (vcEndEquiv C hC f))
  have hg := endConst_latticeEndEquiv L ((latticeEndEquiv L).symm (vcEndEquiv C hC g))
  rw [RingEquiv.apply_symm_apply, endConst_vcEndEquiv] at hf hg
  rw [← hf, ← hg, hfg]

theorem range_endConst {L : PeriodPair} {C : VariableChange ℂ} (hC : C • E = weierstrassCurve L) :
    (endConst E).range = periodLatticeEnd L := by
  rw [← range_endConst_weierstrassCurve]
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨vcEndEquiv C hC f, endConst_vcEndEquiv C hC f⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨f, rfl⟩ := (vcEndEquiv C hC).surjective g
    exact ⟨f, (endConst_vcEndEquiv C hC f).symm⟩

end Complex

end Elliptic
end GroundTheory.Global
end
end

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.BaseChange
namespace GroundTheory.Global

open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section FF

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F') (E : WeierstrassCurve F)

noncomputable def ffMap : E.toAffine.FunctionField →+* (E.map σ).toAffine.FunctionField :=
  letI := σ.toAlgebra
  (bcEmb (F' := F') E).toRingHom

theorem ffMap_genX : ffMap σ E (genX E) = genX (E.map σ) := by
  let _ := σ.toAlgebra
  exact bcEmb_genX (F' := F') E

theorem ffMap_genY : ffMap σ E (genY E) = genY (E.map σ) := by
  let _ := σ.toAlgebra
  exact bcEmb_genY (F' := F') E

theorem ffMap_algebraMap (a : F) :
    ffMap σ E (algebraMap F E.toAffine.FunctionField a) =
      algebraMap F' (E.map σ).toAffine.FunctionField (σ a) := by
  let _ := σ.toAlgebra
  exact (bcEmb (F' := F') E).commutes a

theorem ringHom_ext_functionField {W : WeierstrassCurve F} {L : Type*} [Field L]
    {f g : W.toAffine.FunctionField →+* L}
    (hc : ∀ a : F, f (algebraMap F _ a) = g (algebraMap F _ a)) (hx : f (genX W) = g (genX W))
    (hy : f (genY W) = g (genY W)) : f = g := by
  let _ : Algebra F L := (f.comp (algebraMap F W.toAffine.FunctionField)).toAlgebra
  let f' : W.toAffine.FunctionField →ₐ[F] L := { f with commutes' := fun a => rfl }
  let g' : W.toAffine.FunctionField →ₐ[F] L := { g with commutes' := fun a => (hc a).symm }
  have e : f' = g' := algHom_ext_gen W hx hy
  ext z
  exact DFunLike.congr_fun e z

noncomputable def ffCongr {C D : WeierstrassCurve F'} (h : C = D) :
    C.toAffine.FunctionField ≃+* D.toAffine.FunctionField := by
  subst h; exact RingEquiv.refl _

theorem ffCongr_genX {C D : WeierstrassCurve F'} (h : C = D) : ffCongr h (genX C) = genX D := by
  subst h; rfl

theorem ffCongr_genY {C D : WeierstrassCurve F'} (h : C = D) : ffCongr h (genY C) = genY D := by
  subst h; rfl

theorem ffCongr_algebraMap {C D : WeierstrassCurve F'} (h : C = D) (a : F') :
    ffCongr h (algebraMap F' C.toAffine.FunctionField a) = algebraMap F' D.toAffine.FunctionField a := by
  subst h; rfl

end FF

section Map

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

omit [E.IsElliptic] [E'.IsElliptic] in
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.val_eq (φ : Isogeny E E') : φ.1 = Point.some φ.x φ.y φ.nonsingular := by
  rcases φ with ⟨Q, ⟨x, y, h, rfl, hx⟩, hr⟩
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.ext_xy {φ ψ : Isogeny E E'} (hx : φ.x = ψ.x) (hy : φ.y = ψ.y) : φ = ψ := by
  apply Isogeny.ext'
  rw [φ.val_eq, ψ.val_eq]
  simp only [Point.some.injEq]
  exact ⟨hx, hy⟩

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.map (φ : Isogeny E E') : Isogeny (E.map σ) (E'.map σ) :=
  letI := σ.toAlgebra
  letI := Classical.decEq F'
  isogBaseChange (F' := F') φ

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_x (φ : Isogeny E E') : (φ.map σ).x = ffMap σ E φ.x := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  show xOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_y (φ : Isogeny E E') : (φ.map σ).y = ffMap σ E φ.y := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  show yOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comap_map (φ : Isogeny E E') (f : E'.toAffine.FunctionField) :
    (φ.map σ).comap (ffMap σ E' f) = ffMap σ E (φ.comap f) := by
  have e : (φ.map σ).comap.toRingHom.comp (ffMap σ E') = (ffMap σ E).comp φ.comap.toRingHom := by
    apply ringHom_ext_functionField
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_algebraMap,
        AlgHom.commutes]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genX,
        Isogeny.comap_genX, Isogeny.map_x]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genY,
        Isogeny.comap_genY, Isogeny.map_y]
  exact DFunLike.congr_fun e f

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comp_alt (ψ : Isogeny E' E'') (φ : Isogeny E E') : (ψ.comp φ).x = φ.comap ψ.x := by
  rw [Isogeny.x, Isogeny.comp_val, ψ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comp_y (ψ : Isogeny E' E'') (φ : Isogeny E E') : (ψ.comp φ).y = φ.comap ψ.y := by
  rw [Isogeny.y, Isogeny.comp_val, ψ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    (ψ.comp φ).map σ = (ψ.map σ).comp (φ.map σ) := by
  apply Isogeny.ext_xy
  · rw [Isogeny.map_x, Isogeny.comp_alt, Isogeny.comp_alt, Isogeny.map_x, Isogeny.comap_map]
  · rw [Isogeny.map_y, Isogeny.comp_y, Isogeny.comp_y, Isogeny.map_y, Isogeny.comap_map]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_mulIsogeny (n : ℤ) (hn : n ≠ 0) :
    (mulIsogeny E n hn).map σ = mulIsogeny (E.map σ) n hn := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  apply Subtype.ext
  show Point.map (W' := E) (bcEmb (F' := F') E) (n • genericPoint E) =
    n • genericPoint (E.baseChange F')
  rw [map_zsmul, map_bcEmb_genericPoint]
  rfl

end Map

section Congr

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {C D C' D' C'' D'' : WeierstrassCurve F'} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
  [D'.IsElliptic] [C''.IsElliptic] [D''.IsElliptic]

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.congr (hC : C = D) (hC' : C' = D')
    (φ : Isogeny C C') : Isogeny D D' := by
  subst hC hC'; exact φ

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_alt (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').x = ffCongr hC φ.x := by
  subst hC hC'; rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_y (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').y = ffCongr hC φ.y := by
  subst hC hC'; rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_rfl (φ : Isogeny C C') : φ.congr rfl rfl = φ :=
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.degree_congr (hC : C = D) (hC' : C' = D')
    (φ : Isogeny C C') : (φ.congr hC hC').degree = φ.degree := by
  subst hC hC'; rfl

variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : Isogeny D D' :=
  (φ.map σ).congr hE hE'

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf_alt (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : (φ.mapOf σ hE hE').x = ffCongr hE (ffMap σ E φ.x) := by
  rw [Isogeny.mapOf, Isogeny.congr_alt, Isogeny.map_x]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf_y (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : (φ.mapOf σ hE hE').y = ffCongr hE (ffMap σ E φ.y) := by
  rw [Isogeny.mapOf, Isogeny.congr_y, Isogeny.map_y]

end Congr

end GroundTheory.Global
end
