module

public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogenyMap

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.ReductionDegree
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

section SlopeTestRemainingChoices

theorem exists_gaussResidue_eq (z : (W.map (residue 𝒪)).toAffine.FunctionField) :
    ∃ b : gaussRing W, gaussResidue W (residue _ b) = z := by
  obtain ⟨a, s, hs, rfl⟩ :=
    IsFractionRing.div_surjective (A := (W.map (residue 𝒪)).toAffine.CoordinateRing) z
  obtain ⟨a', rfl⟩ := coordReduce_surjective W a
  obtain ⟨s', rfl⟩ := coordReduce_surjective W s
  have hs' : s' ∈ (gaussPrime W).primeCompl := fun h =>
    nonZeroDivisors.ne_zero hs (RingHom.mem_ker.1 h)
  refine ⟨IsLocalization.mk' (gaussRing W) a' ⟨s', hs'⟩, ?_⟩
  have hspec := IsLocalization.mk'_spec (gaussRing W) a' ⟨s', hs'⟩
  have := congrArg (fun b => gaussResidue W (residue _ b)) hspec
  simp only [map_mul, gaussResidue_residue] at this
  have hne : algebraMap _ (W.map (residue 𝒪)).toAffine.FunctionField (coordReduce W s') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.ne_zero hs)
  rw [eq_div_iff hne]
  exact this

end SlopeTestRemainingChoices

section Isog

variable [W.IsElliptic] [W'.IsElliptic] (φ : Isogeny (W.baseChange K) (W'.baseChange K))

theorem exists_isogeny_coords : ∃ (x y : gaussRing W)
    (h : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Nonsingular
      (algebraMap _ _ x) (algebraMap _ _ y)), φ.1 = Point.some _ _ h := by
  letI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have hne : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W')
      (pointCongr (gaussCurve_map_functionField K W W').symm φ.1) ≠ 0 := by
    intro h0
    apply reduceFF_isogeny_ne_zero K W W' φ
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff]
    exact h0
  obtain ⟨x, y, h, e⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have e' : φ.1 = pointCongr (gaussCurve_map_functionField K W W') (Point.some _ _ h) := by
    rw [← e, pointCongr_pointCongr]; rfl
  rw [pointCongr_some] at e'
  exact ⟨x, y, _, e'⟩


set_option maxHeartbeats 1000000 in
theorem degree_reduceIsogeny_le : (reduceIsogeny K W W' φ).degree ≤ φ.degree := by
  obtain ⟨x, y, h, hφ⟩ := exists_isogeny_coords K W W' φ
  have hjM : ∀ c : 𝒪, algebraMap K (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 K c) =
      algebraMap (gaussRing W) _ (algebraMap 𝒪 (gaussRing W) c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hxy : (W'.map (algebraMap 𝒪 (gaussRing W))).toAffine.Equation x y := by
    have h₁ : ((W'.map (algebraMap 𝒪 (gaussRing W))).map
        (algebraMap _ (W.baseChange K).toAffine.FunctionField)).toAffine.Equation
        (algebraMap _ _ x) (algebraMap _ _ y) := by
      rw [← map_baseChange_eq_map_of K W' (algebraMap 𝒪 (gaussRing W)) _ hjM]; exact h.1
    exact (WeierstrassCurve.Affine.map_equation (W'.map (algebraMap 𝒪 (gaussRing W))).toAffine
      (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) x y).mp h₁
  obtain ⟨h', hred⟩ := reduceFF_some K W W' h
  have hφ' : (reduceIsogeny K W W' φ).1 = Point.some _ _ h' := by
    rw [reduceIsogeny_val, hφ, hred]
  have hx : Function.Injective (eval₂RingHom (ResidueField.map (algebraMap 𝒪 (gaussRing W)))
      (residue _ x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    have hT : Transcendental (ResidueField 𝒪) (gaussResidue W (residue _ x)) := by
      have := (reduceIsogeny K W W' φ).isGenPt
      rw [hφ'] at this
      exact this
    apply hT
    refine ⟨p, hp0, ?_⟩
    have key : aeval (gaussResidue W (residue _ x)) p = gaussResidue W
        (eval₂RingHom (ResidueField.map (algebraMap 𝒪 (gaussRing W))) (residue _ x) p) := by
      rw [aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, gaussResidue_comp_residueField_map]
    rw [key, hp, map_zero]
  set g := gaussLift W' (algebraMap 𝒪 (gaussRing W)) hxy hx
  have hσ : (φ.comap : _ →+* _).comp (algebraMap (gaussRing W')
      (W'.baseChange K).toAffine.FunctionField) =
        (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField).comp g := by
    apply comp_algebraMap_gaussLift W' (algebraMap 𝒪 (gaussRing W)) hxy hx K
    · intro c
      show φ.comap (algebraMap 𝒪 _ c) = _
      rw [IsScalarTower.algebraMap_apply 𝒪 K, φ.comap.commutes, hjM]
    · show φ.comap (genX _) = _
      rw [φ.comap_genX, Isogeny.x, hφ]; rfl
    · show φ.comap (genY _) = _
      rw [φ.comap_genY, Isogeny.y, hφ]; rfl
  have hring : (gaussResidue W).comp (fieldEvalRed W' (algebraMap 𝒪 (gaussRing W)) hxy hx) =
      ((reduceIsogeny K W W' φ).comap : _ →+* _) := by
    apply ringHom_ext_functionField
    · intro c
      rw [RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply,
        gaussResidue_comp_residueField_map]
      exact ((reduceIsogeny K W W' φ).comap.commutes c).symm
    · rw [RingHom.comp_apply, fieldEvalRed_genX]
      show _ = (reduceIsogeny K W W' φ).comap (genX _)
      rw [Isogeny.comap_genX, Isogeny.x, hφ']; rfl
    · rw [RingHom.comp_apply, fieldEvalRed_genY]
      show _ = (reduceIsogeny K W W' φ).comap (genY _)
      rw [Isogeny.comap_genY, Isogeny.y, hφ']; rfl
  have hres : (gaussResidue W).comp (ResidueField.map g) =
      ((reduceIsogeny K W W' φ).comap : _ →+* _).comp (gaussResidue W') := by
    rw [residueField_map_gaussLift, ← RingHom.comp_assoc, hring]
  haveI := φ.finiteDimensional
  haveI := (reduceIsogeny K W W' φ).finiteDimensional
  haveI : Module.Free (reduceIsogeny K W W' φ).comap.fieldRange
      (W.map (residue 𝒪)).toAffine.FunctionField := Module.Free.of_divisionRing _ _
  set bb := Module.finBasis (reduceIsogeny K W W' φ).comap.fieldRange
    (W.map (residue 𝒪)).toAffine.FunctionField
  choose b hb using fun i => exists_gaussResidue_eq W (bb i)
  have hli : LinearIndependent φ.comap.fieldRange
      (fun i => algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (b i)) := by
    classical
    rw [Fintype.linearIndependent_iff]
    intro c hc i₀
    by_contra hci
    choose f hf using fun i => AlgHom.mem_fieldRange.1 (c i).2
    obtain ⟨⟨s, hs⟩, hsf⟩ := IsLocalization.exist_integer_multiples
      (nonZeroDivisors (gaussRing W')) Finset.univ f
    choose a ha using fun i => hsf i (Finset.mem_univ i)

    have hrel : ∑ i, g (a i) * b i = 0 := by
      apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero]
      have h1 := congrArg (fun z => φ.comap (algebraMap _ _ s) * z) hc
      simp only [mul_zero, Finset.mul_sum, Algebra.smul_def, IntermediateField.algebraMap_apply]
        at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← RingHom.comp_apply (algebraMap (gaussRing W) _) g, ← hσ, RingHom.comp_apply,
        ← mul_assoc]
      congr 1
      rw [← hf i, ← map_mul]
      show φ.comap (algebraMap _ _ (a i)) = φ.comap (algebraMap _ _ s * f i)
      rw [ha i, Algebra.smul_def]
    have hinj : ∀ z : gaussRing W', z ≠ 0 → g z ≠ 0 := fun z hz h0 => by
      have h2 : (φ.comap : (W'.baseChange K).toAffine.FunctionField →+*
          (W.baseChange K).toAffine.FunctionField) (algebraMap (gaussRing W')
          (W'.baseChange K).toAffine.FunctionField z) = 0 := by
        rw [← RingHom.comp_apply, hσ, RingHom.comp_apply, h0, map_zero]
      rw [map_eq_zero_iff _ (RingHom.injective _),
        map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h2
      exact hz h2
    have hai₀ : a i₀ ≠ 0 := by
      intro h0
      apply hci
      have := ha i₀
      rw [h0, map_zero, eq_comm, smul_eq_zero] at this
      rcases this with h1 | h1
      · exact (nonZeroDivisors.ne_zero hs h1).elim
      · exact Subtype.ext (by rw [← hf i₀, h1, map_zero]; rfl)
    obtain ⟨i₁, hi₁, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i => a i ≠ 0)
      (fun i => IsDiscreteValuationRing.addVal (gaussRing W') (a i)) ⟨i₀, by simp [hai₀]⟩
    have hai₁ : a i₁ ≠ 0 := (Finset.mem_filter.1 hi₁).2
    have hdvd : ∀ i, a i₁ ∣ a i := fun i => by
      by_cases hi : a i = 0
      · rw [hi]; exact dvd_zero _
      · exact (IsDiscreteValuationRing.addVal_le_iff_dvd).1
          (hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩))
    choose a' ha' using hdvd
    have ha'₁ : a' i₁ = 1 := by
      have := ha' i₁
      exact (mul_eq_left₀ hai₁).1 this.symm
    have hrel' : ∑ i, g (a' i) * b i = 0 := by
      have : g (a i₁) * ∑ i, g (a' i) * b i = 0 := by
        rw [Finset.mul_sum, ← hrel]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ha' i, map_mul, mul_assoc]
      exact (mul_eq_zero.1 this).resolve_left (hinj _ hai₁)
    have hred' := congrArg (fun z => gaussResidue W (residue _ z)) hrel'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_zero, hb] at hred'
    have hcoef : ∀ i, gaussResidue W (residue _ (g (a' i))) =
        (reduceIsogeny K W W' φ).comap (gaussResidue W' (residue _ (a' i))) := fun i => by
      rw [← ResidueField.map_residue, ← RingHom.comp_apply, hres]; rfl
    have hli' := bb.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli'
    have h0 := hli' (fun i => ⟨(reduceIsogeny K W W' φ).comap (gaussResidue W' (residue _ (a' i))),
      ⟨_, rfl⟩⟩) (by
        simp only [Algebra.smul_def, IntermediateField.algebraMap_apply]
        rw [← hred']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcoef])
      i₁
    have h1 := congrArg Subtype.val h0
    simp only [ha'₁, map_one, ZeroMemClass.coe_zero] at h1
    exact one_ne_zero h1
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  exact this

theorem degree_reduceIsogeny : (reduceIsogeny K W W' φ).degree = φ.degree := by
  have h1 := degree_reduceIsogeny_le K W W' φ
  have h2 := degree_reduceIsogeny_le K W' W (dualOver φ)
  rw [degree_dualOver] at h2
  have hc := reduceIsogeny_comp K W W' W (dualOver φ) φ
  rw [dualOver_comp, reduceIsogeny_mulIsogeny] at hc
  have hdeg := congrArg Isogeny.degree hc
  rw [degree_mulIsogeny, Isogeny.degree_comp, Int.natAbs_natCast] at hdeg
  have hpos := φ.degree_pos
  have hpos' := (reduceIsogeny K W W' φ).degree_pos
  apply le_antisymm h1
  by_contra hlt
  push_neg at hlt
  have : (reduceIsogeny K W' W (dualOver φ)).degree * (reduceIsogeny K W W' φ).degree <
      φ.degree ^ 2 := by
    calc (reduceIsogeny K W' W (dualOver φ)).degree * (reduceIsogeny K W W' φ).degree
        ≤ φ.degree * (reduceIsogeny K W W' φ).degree := Nat.mul_le_mul_right _ h2
      _ < φ.degree * φ.degree := Nat.mul_lt_mul_of_pos_left hlt hpos
      _ = φ.degree ^ 2 := (sq _).symm
  omega

end Isog

section Hom

variable [W.IsElliptic] [W'.IsElliptic] [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))]

end Hom

end

end GroundTheory.Global
end

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped Polynomial.Bivariate

universe u

section Delta

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

def invDeriv (f : E.toAffine.FunctionField) : E.toAffine.FunctionField :=
  invCoeff E (D F E.toAffine.FunctionField f)

theorem invCoeff_smul_mul (c : E.toAffine.FunctionField) (η : KaehlerDifferential F E.toAffine.FunctionField) :
    invCoeff E (c • η) = c * invCoeff E η :=
  invCoeff_eq E (by rw [mul_smul, invCoeff_smul])

theorem invDeriv_add (f g : E.toAffine.FunctionField) :
    invDeriv E (f + g) = invDeriv E f + invDeriv E g := by
  rw [invDeriv, map_add (f := _), invCoeff_add]; rfl

theorem invDeriv_mul (f g : E.toAffine.FunctionField) :
    invDeriv E (f * g) = f * invDeriv E g + g * invDeriv E f := by
  rw [invDeriv, Derivation.leibniz, invCoeff_add, invCoeff_smul_mul, invCoeff_smul_mul]; rfl

theorem invDeriv_algebraMap (c : F) : invDeriv E (algebraMap F _ c) = 0 := by
  rw [invDeriv, D_coeff, invCoeff_zero]

theorem invDeriv_genX : invDeriv E (genX E) = 2 * genY E +
    algebraMap F _ E.a₁ * genX E + algebraMap F _ E.a₃ := by
  apply invCoeff_eq
  exact (omegaAt_some_spec E _).1

theorem invDeriv_genY : invDeriv E (genY E) = 3 * genX E ^ 2 +
    2 * algebraMap F _ E.a₂ * genX E + algebraMap F _ E.a₄ - algebraMap F _ E.a₁ * genY E := by
  apply invCoeff_eq
  exact (omegaAt_some_spec E _).2

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic]

theorem isogCoeff_mul (φ : Isogeny E E') {x y : E.toAffine.FunctionField}
    {h : (E'.baseChange E.toAffine.FunctionField).toAffine.Nonsingular x y}
    (hφ : φ.1 = Point.some x y h) :
    isogCoeff φ * (2 * y + algebraMap F _ E'.a₁ * x + algebraMap F _ E'.a₃) = invDeriv E x := by
  have e := (omegaAt_some_spec E' h).1
  rw [← hφ, ← isogenyPullback_invariantDifferential, isogenyPullback_invariantDifferential_eq_smul,
    smul_smul] at e
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at e
  rw [invDeriv, invCoeff_eq E e]
  ring

end Delta

section Dual

open TrivSqZeroExt

def dualMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    TrivSqZeroExt R R →+* TrivSqZeroExt S S where
  toFun z := inl (f z.fst) + inr (f z.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext <;> simp [fst_mul, snd_mul, MulOpposite.smul_eq_mul_unop]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem dualMap_fst {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : TrivSqZeroExt R R) : (dualMap f z).fst = f z.fst := by simp [dualMap]

theorem dualMap_snd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : TrivSqZeroExt R R) : (dualMap f z).snd = f z.snd := by simp [dualMap]

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

def invDerivHom : E.toAffine.FunctionField →+*
    TrivSqZeroExt E.toAffine.FunctionField E.toAffine.FunctionField where
  toFun f := inl f + inr (invDeriv E f)
  map_one' := by
    have h1 : invDeriv E 1 = 0 := by
      rw [← map_one (algebraMap F E.toAffine.FunctionField), invDeriv_algebraMap]
    ext <;> simp [h1]
  map_mul' a b := by
    ext <;> simp [fst_mul, snd_mul, MulOpposite.smul_eq_mul_unop, invDeriv_mul]
    ring
  map_zero' := by
    have h0 : invDeriv E 0 = 0 := by
      simpa using invDeriv_algebraMap E 0
    ext <;> simp [h0]
  map_add' a b := by ext <;> simp [invDeriv_add]

theorem invDerivHom_fst (f : E.toAffine.FunctionField) : (invDerivHom E f).fst = f := by
  simp [invDerivHom]

theorem invDerivHom_snd (f : E.toAffine.FunctionField) :
    (invDerivHom E f).snd = invDeriv E f := by
  simp [invDerivHom]

end Dual

section Gauss

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)

def gaussDX : gaussRing W :=
  2 * gaussY W + algebraMap 𝒪 _ W.a₁ * gaussX W + algebraMap 𝒪 _ W.a₃

def gaussDY : gaussRing W :=
  3 * gaussX W ^ 2 + 2 * algebraMap 𝒪 _ W.a₂ * gaussX W + algebraMap 𝒪 _ W.a₄ -
    algebraMap 𝒪 _ W.a₁ * gaussY W

theorem gauss_equation (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] :
    (W.map (algebraMap 𝒪 (gaussRing W))).toAffine.Equation (gaussX W) (gaussY W) := by
  have h := equation_gen (W.baseChange K)
  rw [← algebraMap_gaussX W K, ← algebraMap_gaussY W K] at h
  have e : (W.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField =
      (W.map (algebraMap 𝒪 (gaussRing W))).map (algebraMap (gaussRing W) _) :=
    (gaussCurve_map_functionField K W W).symm
  rw [e] at h
  exact (WeierstrassCurve.Affine.map_equation (W.map (algebraMap 𝒪 (gaussRing W))).toAffine
    (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) _ _).mp h

theorem gauss_dual_equation (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] :
    (W.map ((inlHom (gaussRing W) (gaussRing W)).comp (algebraMap 𝒪 (gaussRing W)))).toAffine.Equation
      (inl (gaussX W) + inr (gaussDX W)) (inl (gaussY W) + inr (gaussDY W)) := by
  have e := (WeierstrassCurve.Affine.equation_iff _ _).1 (gauss_equation W K)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, RingHom.comp_apply, inlHom_apply]
  ext
  · simp only [fst_add, fst_mul, fst_pow, fst_inl, fst_inr, add_zero]
    linear_combination e
  · simp only [fst_add, fst_mul, fst_pow, fst_inl, fst_inr, snd_add, snd_mul, snd_pow, snd_inl,
      snd_inr, add_zero, zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      nsmul_eq_mul, Nat.cast_ofNat, Nat.pred_eq_sub_one, mul_zero, zero_mul]
    simp only [gaussDX, gaussDY]
    norm_num
    ring

end Gauss

section GaussDeriv

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

def gaussDualA : W.toAffine.CoordinateRing →+* TrivSqZeroExt (gaussRing W) (gaussRing W) :=
  AdjoinRoot.lift (eval₂RingHom ((inlHom (gaussRing W) (gaussRing W)).comp
      (algebraMap 𝒪 (gaussRing W))) (inl (gaussX W) + inr (gaussDX W)))
    (inl (gaussY W) + inr (gaussDY W))
    (eval₂_polynomial_of_equation W _ (gauss_dual_equation W K))

theorem gaussDualA_algebraMap (c : 𝒪) :
    gaussDualA K W (algebraMap 𝒪 _ c) = inl (algebraMap 𝒪 (gaussRing W) c) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
    gaussDualA, AdjoinRoot.lift_of]
  simp

theorem gaussDualA_X :
    gaussDualA K W (CoordinateRing.mk W (C X)) = inl (gaussX W) + inr (gaussDX W) := by
  rw [AdjoinRoot.mk_C, gaussDualA, AdjoinRoot.lift_of]
  simp

theorem gaussDualA_Y :
    gaussDualA K W (CoordinateRing.mk W Y) = inl (gaussY W) + inr (gaussDY W) := by
  rw [AdjoinRoot.mk_X, gaussDualA, AdjoinRoot.lift_root]

theorem fst_gaussDualA (a : W.toAffine.CoordinateRing) :
    (gaussDualA K W a).fst = algebraMap _ (gaussRing W) a := by
  have : ((fstHom 𝒪 (gaussRing W) (gaussRing W)).toRingHom).comp (gaussDualA K W) =
      algebraMap _ (gaussRing W) := by
    apply coordinateRing_ringHom_ext
    · intro c
      simp [gaussDualA_algebraMap, ← IsScalarTower.algebraMap_apply]
    · show (gaussDualA K W (CoordinateRing.mk W (C X))).fst = _
      rw [gaussDualA_X, fst_add, fst_inl, fst_inr, add_zero]; rfl
    · show (gaussDualA K W (CoordinateRing.mk W Y)).fst = _
      rw [gaussDualA_Y, fst_add, fst_inl, fst_inr, add_zero]; rfl
  exact congrArg (fun f => f a) this

def gaussDual : gaussRing W →+* TrivSqZeroExt (gaussRing W) (gaussRing W) :=
  IsLocalization.lift (M := (gaussPrime W).primeCompl) (S := gaussRing W) (g := gaussDualA K W)
    fun s => isUnit_iff_isUnit_fst.2 (by
      rw [fst_gaussDualA]; exact IsLocalization.map_units (gaussRing W) s)

theorem gaussDual_algebraMap (a : W.toAffine.CoordinateRing) :
    gaussDual K W (algebraMap _ _ a) = gaussDualA K W a :=
  IsLocalization.lift_eq _ _

theorem gaussDual_algebraMap_base (c : 𝒪) :
    gaussDual K W (algebraMap 𝒪 (gaussRing W) c) = inl (algebraMap 𝒪 (gaussRing W) c) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
    gaussDual_algebraMap, gaussDualA_algebraMap, ← IsScalarTower.algebraMap_apply]

def gaussDeriv (g : gaussRing W) : gaussRing W := (gaussDual K W g).snd

end GaussDeriv

section Compat

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [W.IsElliptic]

theorem algebraMap_gauss_const (c : 𝒪) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 _ c) =
      algebraMap K _ (algebraMap 𝒪 K c) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply 𝒪 K]

theorem algebraMap_gaussDeriv (g : gaussRing W) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (gaussDeriv K W g) =
      invDeriv (W.baseChange K) (algebraMap (gaussRing W) _ g) := by
  have key : (dualMap (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField)).comp
      (gaussDual K W) = (invDerivHom (W.baseChange K)).comp (algebraMap (gaussRing W) _) := by
    apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
    apply coordinateRing_ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
        gaussDual_algebraMap_base]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_inl]
      · rw [dualMap_snd, invDerivHom_snd, snd_inl, map_zero, algebraMap_gauss_const,
          invDeriv_algebraMap]
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_X]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W (C X)) =
        gaussX W from rfl, algebraMap_gaussX]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero, algebraMap_gaussX]
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, invDeriv_genX,
          gaussDX]
        simp only [map_add (f := _), map_mul, map_ofNat, algebraMap_gaussX, algebraMap_gaussY,
          algebraMap_gauss_const]
        rfl
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_Y]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W Y) =
        gaussY W from rfl, algebraMap_gaussY]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero, algebraMap_gaussY]
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, invDeriv_genY,
          gaussDY]
        simp only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat, algebraMap_gaussX,
          algebraMap_gaussY, algebraMap_gauss_const]
        rfl
  have := congrArg (fun f => (f g).snd) key
  simp only [RingHom.comp_apply, dualMap_snd, invDerivHom_snd] at this
  rw [gaussDeriv]
  exact this

theorem gaussResidue_gaussDeriv (g : gaussRing W) :
    gaussResidue W (residue _ (gaussDeriv K W g)) =
      invDeriv (W.map (residue 𝒪)) (gaussResidue W (residue _ g)) := by
  have key : (dualMap ((gaussResidue W).comp (residue (gaussRing W)))).comp (gaussDual K W) =
      (invDerivHom (W.map (residue 𝒪))).comp ((gaussResidue W).comp (residue (gaussRing W))) := by
    apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
    apply coordinateRing_ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
        gaussDual_algebraMap_base]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_inl]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_inl, map_zero,
          gaussResidue_residue_algebraMap, invDeriv_algebraMap]
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_X]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W (C X)) =
        gaussX W from rfl]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, gaussResidue_gaussX, invDeriv_genX, gaussDX]
        simp only [map_add (f := _), map_mul, map_ofNat, RingHom.comp_apply, gaussResidue_gaussX,
          gaussResidue_gaussY, gaussResidue_residue_algebraMap]
        rfl
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_Y]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W Y) =
        gaussY W from rfl]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, gaussResidue_gaussY, invDeriv_genY, gaussDY]
        simp only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat, RingHom.comp_apply,
          gaussResidue_gaussX, gaussResidue_gaussY, gaussResidue_residue_algebraMap]
        rfl
  have := congrArg (fun f => (f g).snd) key
  simp only [RingHom.comp_apply, dualMap_snd, invDerivHom_snd] at this
  rw [gaussDeriv]
  exact this

end Compat

section Isog

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  [W.IsElliptic] [W'.IsElliptic] (φ : Isogeny (W.baseChange K) (W'.baseChange K))


set_option maxHeartbeats 1000000 in
theorem exists_invConst_reduceIsogeny :
    ∃ c : 𝒪, algebraMap 𝒪 K c = invConst φ ∧
      residue 𝒪 c = invConst (reduceIsogeny K W W' φ) := by
  obtain ⟨x, y, h, hφ⟩ := exists_isogeny_coords K W W' φ
  obtain ⟨h', hred⟩ := reduceFF_some K W W' h
  have hφ' : (reduceIsogeny K W W' φ).1 = Point.some _ _ h' := by
    rw [reduceIsogeny_val, hφ, hred]
  set u : gaussRing W := 2 * y + algebraMap 𝒪 _ W'.a₁ * x + algebraMap 𝒪 _ W'.a₃ with hu_def

  have hu_res : gaussResidue W (residue _ u) = 2 * gaussResidue W (residue _ y) +
      algebraMap (ResidueField 𝒪) _ (W'.map (residue 𝒪)).a₁ * gaussResidue W (residue _ x) +
        algebraMap (ResidueField 𝒪) _ (W'.map (residue 𝒪)).a₃ := by
    simp only [hu_def, map_add (f := _), map_mul, map_ofNat, gaussResidue_residue_algebraMap]
    rfl
  have hu_ne : gaussResidue W (residue _ u) ≠ 0 := by
    have hg := (reduceIsogeny K W W' φ).isGenPt
    rw [hφ'] at hg
    have hd := genDen_ne_zero (W'.map (residue 𝒪))
    intro h0
    apply hd
    apply (genEval (W'.map (residue 𝒪)) _ hg).toRingHom.injective
    rw [map_zero, ← h0, hu_res]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), map_mul, map_ofNat,
      AlgHom.commutes, genEval_genX, genEval_genY]
    rfl
  have hu : IsUnit u := by
    by_contra hnu
    exact hu_ne (by rw [(residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hnu), map_zero])

  have e1 : isogCoeff φ * algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField u =
      algebraMap (gaussRing W) _ (gaussDeriv K W x) := by
    rw [algebraMap_gaussDeriv, ← isogCoeff_mul φ hφ]
    congr 1
    simp only [hu_def, map_add (f := _), map_mul, map_ofNat, algebraMap_gauss_const]
    rfl
  set v : gaussRing W := gaussDeriv K W x * ↑hu.unit⁻¹ with hv_def
  have hv : algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField v = isogCoeff φ := by
    have hne : algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField u ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hu.ne_zero
    rw [hv_def, map_mul, ← e1, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]

  have hint : invConst φ ∈ Set.range (algebraMap 𝒪 K) := by
    by_contra hX
    obtain ⟨t, ht, hte⟩ := exists_inv_mem_of_notMem_range K hX
    have hc0 : invConst φ ≠ 0 := fun h0 => hX ⟨0, by rw [map_zero, h0]⟩
    have h1 : v * algebraMap 𝒪 (gaussRing W) t = 1 := by
      apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
      rw [map_mul, hv, algebraMap_gauss_const, hte, ← algebraMap_invConst, map_inv₀,
        mul_inv_cancel₀ ((_root_.map_ne_zero _).2 hc0), map_one]
    have : IsUnit (algebraMap 𝒪 (gaussRing W) t) :=
      isUnit_iff_exists_inv.2 ⟨v, by rw [mul_comm]; exact h1⟩
    exact (mem_maximalIdeal _).1 ht ((isUnit_map_iff (algebraMap 𝒪 (gaussRing W)) t).1 this)
  obtain ⟨c, hc⟩ := hint
  refine ⟨c, hc, ?_⟩
  have hvc : algebraMap 𝒪 (gaussRing W) c = v := by
    apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
    rw [algebraMap_gauss_const, hc, algebraMap_invConst, hv]

  have e2 := isogCoeff_mul (reduceIsogeny K W W' φ) hφ'
  rw [← gaussResidue_gaussDeriv K W x] at e2
  have e2' : isogCoeff (reduceIsogeny K W W' φ) = gaussResidue W (residue _ v) := by
    have hres_u : gaussResidue W (residue _ u) * gaussResidue W (residue _ ↑hu.unit⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, IsUnit.mul_val_inv, map_one, map_one]
    rw [hv_def, map_mul, map_mul, ← e2, ← hu_res, mul_assoc, hres_u, mul_one]
  apply (algebraMap (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.FunctionField).injective
  rw [algebraMap_invConst, e2', ← hvc, gaussResidue_residue_algebraMap]

end Isog

end

end GroundTheory.Global
