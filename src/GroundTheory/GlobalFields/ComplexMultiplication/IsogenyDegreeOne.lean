module

public import GroundTheory.GlobalFields.ComplexMultiplication.DualDescent

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobeniusFactor
namespace GroundTheory.Global

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField GroundTheory.Arith.Abelian

universe u

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] (p : ℕ)
  [hp : Fact p.Prime] [CharP F p]


omit [E.IsElliptic] in
theorem exists_frobeniusPoint_eq {L : Type*} [Field L] [Algebra F L] [CharP L p] [PerfectRing L p]
    (P : ((frobeniusTwist E p).baseChange L).toAffine.Point) :
    ∃ R : (E.baseChange L).toAffine.Point, frobeniusPoint E p L R = P := by
  have hroot : ∀ z : L, ∃ w : L, w ^ p = z := fun z =>
    ⟨(frobeniusEquiv L p).symm z, by rw [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]⟩
  rcases P with (_ | ⟨u, v, h⟩)
  · exact ⟨0, rfl⟩
  · obtain ⟨u', rfl⟩ := hroot u
    obtain ⟨v', rfl⟩ := hroot v
    exact ⟨.some u' v' ((nonsingular_pow_iff E p).mp h), rfl⟩

variable [PerfectRing F p]

theorem fieldRange_le_powField_of_not_isSeparable (φ : Isogeny E E') (hφ : ¬ φ.IsSeparable) :
    φ.comap.fieldRange ≤ powField E p := by
  have := φ.finiteDimensional
  apply le_powField_of_finSepDegree_lt E p
  exact lt_of_le_of_ne (Field.finSepDegree_le_finrank _ _)
    fun h => hφ ((Field.finSepDegree_eq_finrank_iff _ _).mp h)

theorem exists_comp_frobeniusIsogeny_eq (φ : Isogeny E E') (hφ : ¬ φ.IsSeparable) :
    ∃ ψ : Isogeny (frobeniusTwist E p) E', ψ.comp (frobeniusIsogeny E p) = φ := by
  classical
  have hle := fieldRange_le_powField_of_not_isSeparable p φ hφ
  rw [← fieldRange_comap_frobeniusIsogeny E p] at hle
  obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.mp (hle (AlgHom.mem_fieldRange.mpr ⟨genX E', φ.comap_genX⟩))
  obtain ⟨b, hb⟩ := AlgHom.mem_fieldRange.mp (hle (AlgHom.mem_fieldRange.mpr ⟨genY E', φ.comap_genY⟩))
  have hns : (E'.baseChange (frobeniusTwist E p).toAffine.FunctionField).toAffine.Nonsingular a b :=
    (E'.toAffine.baseChange_nonsingular (frobeniusIsogeny E p).comap.toRingHom.injective a b).mp (by
      rw [ha, hb]
      exact φ.nonsingular)
  have ht : Transcendental F a := fun h => φ.transcendental_alt (by rw [← ha]; exact h.algHom (frobeniusIsogeny E p).comap)
  set Q : (E'.baseChange (frobeniusTwist E p).toAffine.FunctionField).toAffine.Point :=
    .some a b hns with hQdef
  have hQ : Point.map (frobeniusIsogeny E p).comap Q = φ.1 := by
    rw [φ.val_eq_some_x_y, hQdef, Point.map_some]
    simp only [Point.some.injEq]
    exact ⟨ha, hb⟩

  have key : ∀ {L : Type u} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
      (R : (E.baseChange L).toAffine.Point) (hR : IsGenPt E R)
      (h' : IsGenPt (frobeniusTwist E p) (frobeniusPoint E p L R)),
      Point.map (genEval _ (frobeniusPoint E p L R) h') Q = φ.app R hR := by
    intro L _ _ _ _ R hR h'
    rw [genEval_congr _ (frobeniusIsogeny_app E p R hR).symm h'
      ((frobeniusIsogeny E p).isGenPt_app R hR), Isogeny.genEval_app, ← Point.map_map, hQ]
    rfl
  have hresp : RespectsAdd (frobeniusTwist E p) E' Q := by
    rw [respectsAdd_iff]
    intro L _ _ _ P₁ P₂ h₁ h₂ h₃
    have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
    have : CharP (AlgebraicClosure L) p :=
      charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure L)).injective p
    let σ : L →ₐ[F] AlgebraicClosure L := IsScalarTower.toAlgHom F L (AlgebraicClosure L)
    obtain ⟨R₁, e₁⟩ := exists_frobeniusPoint_eq (E := E) p (Point.map σ P₁)
    obtain ⟨R₂, e₂⟩ := exists_frobeniusPoint_eq (E := E) p (Point.map σ P₂)
    have e₃ : frobeniusPoint E p _ (R₁ + R₂) = Point.map σ (P₁ + P₂) := by
      rw [frobeniusPoint_add, e₁, e₂, map_add (f := _)]
    have gen : ∀ {R P} (hP : IsGenPt (frobeniusTwist E p) P)
        (e : frobeniusPoint E p (AlgebraicClosure L) R = Point.map σ P), IsGenPt E R :=
      fun hP e => (isGenPt_frobeniusPoint_iff E p _).mp (e ▸ isGenPt_map _ σ hP)
    have step : ∀ (P : ((frobeniusTwist E p).baseChange L).toAffine.Point)
        (hP : IsGenPt (frobeniusTwist E p) P) (R : (E.baseChange (AlgebraicClosure L)).toAffine.Point)
        (e : frobeniusPoint E p _ R = Point.map σ P),
        Point.map σ (Point.map (genEval _ P hP) Q) = φ.app R (gen hP e) := by
      intro P hP R e
      rw [Point.map_map, ← genEval_map, genEval_congr _ e.symm _
        ((isGenPt_frobeniusPoint_iff E p R).mpr (gen hP e))]
      exact key R _ _
    apply Point.map_injective (W' := E') σ
    rw [map_add (f := _), step _ h₁ R₁ e₁, step _ h₂ R₂ e₂, step _ h₃ _ e₃]
    exact φ.app_add (gen h₁ e₁) (gen h₂ e₂) (gen h₃ e₃)
  refine ⟨⟨Q, (isIsogeny_iff _).mpr ⟨ht, hresp⟩⟩, Isogeny.ext' ?_⟩
  exact (Isogeny.comp_val _ _).trans hQ

theorem exists_eq_comp_frobeniusIsogeny (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') = 0) :
    ∃ ψ : Isogeny (frobeniusTwist E p) E', φ = ψ.comp (frobeniusIsogeny E p) ∧
      φ.degree = ψ.degree * p ∧ ψ.degree = φ.degree / p := by
  obtain ⟨ψ, hψ⟩ := exists_comp_frobeniusIsogeny_eq p φ
    fun h => (isSeparable_iff_isogenyPullback_ne_zero φ).mp h hφ
  have hd : φ.degree = ψ.degree * p := by
    rw [← hψ, Isogeny.degree_comp, degree_frobeniusIsogeny]
  exact ⟨ψ, hψ.symm, hd, by rw [hd, Nat.mul_div_cancel _ hp.out.pos]⟩


omit [E.IsElliptic] [CharP F p] [PerfectRing F p] hp in
theorem Isogeny.comap_bijective_of_degree_eq_one {E₁ E₂ : WeierstrassCurve F} [E₁.IsElliptic]
    [E₂.IsElliptic] (ψ : Isogeny E₁ E₂) (h : ψ.degree = 1) : Function.Bijective ψ.comap := by
  refine ⟨ψ.comap.toRingHom.injective, fun z => ?_⟩
  have htop : (⊤ : IntermediateField F E₁.toAffine.FunctionField) ≤ ψ.comap.fieldRange := by
    rw [← relfinrank_eq_one_iff, relfinrank_top_right]
    exact h
  exact AlgHom.mem_fieldRange.mp (htop trivial)

theorem exists_isomorphism_of_degree_eq (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') = 0) (hdeg : φ.degree = p) :
    ∃ ψ : Isogeny (frobeniusTwist E p) E', φ = ψ.comp (frobeniusIsogeny E p) ∧ ψ.degree = 1 ∧
      Function.Bijective ψ.comap ∧
      (dualOver ψ).comp ψ = mulIsogeny (frobeniusTwist E p) 1 one_ne_zero ∧
      ψ.comp (dualOver ψ) = mulIsogeny E' 1 one_ne_zero := by
  obtain ⟨ψ, hψ, hd, -⟩ := exists_eq_comp_frobeniusIsogeny p φ hφ
  have h1 : ψ.degree = 1 := by
    rw [hdeg] at hd
    exact (Nat.mul_eq_right hp.out.ne_zero).mp hd.symm
  refine ⟨ψ, hψ, h1, Isogeny.comap_bijective_of_degree_eq_one ψ h1, ?_, ?_⟩
  · rw [dualOver_comp]
    congr 1
    simp [h1]
  · rw [comp_dualOver]
    congr 1
    simp [h1]

end GroundTheory.Global
end

namespace GroundTheory.Global

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero IntermediateField GroundTheory.Arith.Abelian

universe u

section Basis

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

theorem eq_zero_of_algebraMap_add_mul_genY {P Q : F[X]}
    (h : algebraMap F[X] W.toAffine.FunctionField P +
      algebraMap F[X] W.toAffine.FunctionField Q * genY W = 0) : P = 0 ∧ Q = 0 := by
  rw [← algebraMap_smul_basis] at h
  have h' := (IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField)
    (h.trans (map_zero _).symm)
  exact smul_basis_eq_zero h'

theorem eq_of_equation_genX_genY {W' : WeierstrassCurve F}
    (h : (W'.baseChange W.toAffine.FunctionField).toAffine.Equation (genX W) (genY W)) :
    W' = W := by
  have eW := genY_sq_add W
  have eW' := (equation_iff _ _).mp h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at eW'
  set P : F[X] := -(C (W.a₂ - W'.a₂) * X ^ 2 + C (W.a₄ - W'.a₄) * X + C (W.a₆ - W'.a₆)) with hP
  set Q : F[X] := C (W.a₁ - W'.a₁) * X + C (W.a₃ - W'.a₃) with hQ
  have key : algebraMap F[X] W.toAffine.FunctionField P +
      algebraMap F[X] W.toAffine.FunctionField Q * genY W = 0 := by
    simp only [hP, hQ, map_add (f := _), map_mul, map_neg, map_pow, algebraMap_C_functionField, ← genX_eq,
      map_sub]
    linear_combination eW - eW'
  obtain ⟨hP0, hQ0⟩ := eq_zero_of_algebraMap_add_mul_genY W key
  have c2 := congrArg (AddMonoidAlgebra.coeff · 2) hP0
  have c1 := congrArg (AddMonoidAlgebra.coeff · 1) hP0
  have c0 := congrArg (AddMonoidAlgebra.coeff · 0) hP0
  have d1 := congrArg (AddMonoidAlgebra.coeff · 1) hQ0
  have d0 := congrArg (AddMonoidAlgebra.coeff · 0) hQ0
  simp [hP, hQ, coeff_X, coeff_C, coeff_X_pow, -map_sub] at c2 c1 c0 d1 d0
  ext
  · linear_combination -d1
  · linear_combination c2
  · linear_combination -d0
  · linear_combination c1
  · linear_combination c0

end Basis

section Poles

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {W : WeierstrassCurve F}
  [W.IsElliptic]


omit [DecidableEq F] in
theorem valuationPoint_genY_le_one {P : W.toAffine.Point} (hP : P ≠ 0) :
    valuationPoint W P (genY W) ≤ 1 := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    show (heightOneOfNonsingular h).valuation _ (algebraMap _ _ _) ≤ 1
    exact HeightOneSpectrum.valuation_le_one _ _

theorem exists_algebraMap_eq_of_valuationPoint_le_one {f : W.toAffine.FunctionField}
    (h : ∀ P : W.toAffine.Point, P ≠ 0 → valuationPoint W P f ≤ 1) :
    ∃ p q : F[X], algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X) = f := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one W.toAffine.FunctionField f
    fun v => by rw [← valuationPoint_pointOfIdeal]; exact h _ (pointOfIdeal_ne_zero W v)
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  exact ⟨p, q, rfl⟩

theorem exists_eq_linear_of_valuation {f : W.toAffine.FunctionField}
    (h : ∀ P : W.toAffine.Point, P ≠ 0 → valuationPoint W P f ≤ 1)
    (h0 : valuationInfty W f = exp 2) :
    ∃ α β : F, α ≠ 0 ∧ f = algebraMap F W.toAffine.FunctionField α * genX W +
      algebraMap F W.toAffine.FunctionField β := by
  obtain ⟨p, q, rfl⟩ := exists_algebraMap_eq_of_valuationPoint_le_one h
  have ha : p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X ≠ 0 := by
    intro h'
    rw [h', map_zero, map_zero] at h0
    exact exp_ne_zero h0.symm
  rw [valuationInfty_algebraMap, valuationInftyCoord_apply W ha, exp_inj] at h0
  by_cases hq : q = 0
  · subst hq
    rw [natDegree_norm_smul_basis_of_q_eq_zero] at h0
    have hp1 : p.natDegree = 1 := by omega
    obtain ⟨c₁, c₀, rfl⟩ : ∃ c₁ c₀ : F, p = C c₁ * X + C c₀ :=
      ⟨_, _, eq_X_add_C_of_natDegree_le_one hp1.le⟩
    refine ⟨c₁, c₀, ?_, ?_⟩
    · rintro rfl
      simp at hp1
    · rw [algebraMap_smul_basis, map_zero, zero_mul, add_zero]
      simp only [map_add (f := _), map_mul, algebraMap_C_functionField, ← genX_eq]
  · exfalso
    by_cases hp : p = 0
    · subst hp
      rw [natDegree_norm_smul_basis_of_p_eq_zero hq] at h0
      omega
    · rw [natDegree_norm_smul_basis_of_ne_zero hp hq] at h0
      have := le_max_right (2 * p.natDegree) (2 * q.natDegree + 3)
      omega

theorem exists_eq_genY_form_of_valuation {g : W.toAffine.FunctionField}
    (h : ∀ P : W.toAffine.Point, P ≠ 0 → valuationPoint W P g ≤ 1)
    (h0 : valuationInfty W g = exp 3) :
    ∃ γ δ ε : F, γ ≠ 0 ∧ g = algebraMap F W.toAffine.FunctionField γ * genY W +
      algebraMap F W.toAffine.FunctionField δ * genX W + algebraMap F W.toAffine.FunctionField ε := by
  obtain ⟨p, q, rfl⟩ := exists_algebraMap_eq_of_valuationPoint_le_one h
  have ha : p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X ≠ 0 := by
    intro h'
    rw [h', map_zero, map_zero] at h0
    exact exp_ne_zero h0.symm
  rw [valuationInfty_algebraMap, valuationInftyCoord_apply W ha, exp_inj] at h0
  by_cases hq : q = 0
  · subst hq
    rw [natDegree_norm_smul_basis_of_q_eq_zero] at h0
    omega
  have hdeg : q.natDegree = 0 ∧ p.natDegree ≤ 1 := by
    by_cases hp : p = 0
    · subst hp
      rw [natDegree_norm_smul_basis_of_p_eq_zero hq] at h0
      exact ⟨by omega, by simp⟩
    · rw [natDegree_norm_smul_basis_of_ne_zero hp hq] at h0
      have h1 := le_max_left (2 * p.natDegree) (2 * q.natDegree + 3)
      have h2 := le_max_right (2 * p.natDegree) (2 * q.natDegree + 3)
      omega
  obtain ⟨c, rfl⟩ : ∃ c : F, q = C c := ⟨_, eq_C_of_natDegree_eq_zero hdeg.1⟩
  obtain ⟨c₁, c₀, rfl⟩ : ∃ c₁ c₀ : F, p = C c₁ * X + C c₀ :=
    ⟨_, _, eq_X_add_C_of_natDegree_le_one hdeg.2⟩
  refine ⟨c, c₁, c₀, ?_, ?_⟩
  · rintro rfl
    exact hq (map_zero C)
  · rw [algebraMap_smul_basis]
    simp only [map_add (f := _), map_mul, algebraMap_C_functionField, ← genX_eq]
    ring

end Poles

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

theorem exists_variableChange_of_degree_eq_one_of_isAlgClosed (ψ : Isogeny A B)
    (h : ψ.degree = 1) : ∃ C : VariableChange F, C • B = A := by
  have hmul := ψ.ramIdx_mul_card_ker
  rw [h] at hmul
  have hram : ψ.ramIdx = 1 := (mul_eq_one.mp hmul).1
  have hbot : ψ.pointHom.ker = ⊥ := AddSubgroup.card_eq_one.mp (mul_eq_one.mp hmul).2
  have hne : ∀ R : A.toAffine.Point, R ≠ 0 → ψ.pointMap R ≠ 0 := by
    intro R hR h0
    have hR' : R ∈ ψ.pointHom.ker := by
      rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply]; exact h0
    rw [hbot, AddSubgroup.mem_bot] at hR'
    exact hR hR'
  have hval : ∀ (R : A.toAffine.Point) (f : B.toAffine.FunctionField),
      valuationPoint A R (ψ.comap f) = valuationPoint B (ψ.pointMap R) f := by
    intro R f
    rw [ψ.valuationPoint_comap, hram, pow_one]
  have h0 : ψ.pointMap 0 = 0 := map_zero ψ.pointHom
  have hinf : ∀ f : B.toAffine.FunctionField, valuationInfty A (ψ.comap f) = valuationInfty B f := by
    intro f
    rw [← valuationPoint_zero_eq, hval, h0, valuationPoint_zero_eq]
  obtain ⟨α, β, hα, hf⟩ := exists_eq_linear_of_valuation (W := A) (f := ψ.comap (genX B))
    (fun R hR => by rw [hval]; exact valuationPoint_genX_le_one (hne R hR))
    (by rw [hinf, valuationInfty_genX B])
  obtain ⟨γ, δ, ε, hγ, hg⟩ := exists_eq_genY_form_of_valuation (W := A) (g := ψ.comap (genY B))
    (fun R hR => by rw [hval]; exact valuationPoint_genY_le_one (hne R hR))
    (by rw [hinf, valuationInfty_genY B])
  set ι := algebraMap F A.toAffine.FunctionField with hι
  have hx : ψ.x = ι α * genX A + ι β := by rw [← ψ.comap_genX]; exact hf
  have hy : ψ.y = ι γ * genY A + ι δ * genX A + ι ε := by rw [← ψ.comap_genY]; exact hg
  have hN := ψ.nonsingular
  have eB := (equation_iff _ _).mp hN.1
  rw [hx, hy] at eB
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at eB
  have eA := genY_sq_add A

  have hc3 : γ ^ 2 = α ^ 3 := by
    set P : F[X] := C (γ ^ 2 - α ^ 3) * X ^ 3 +
      C (γ ^ 2 * A.a₂ + δ ^ 2 + B.a₁ * α * δ - 3 * α ^ 2 * β - B.a₂ * α ^ 2) * X ^ 2 +
      C (γ ^ 2 * A.a₄ + 2 * δ * ε + B.a₁ * (α * ε + β * δ) + B.a₃ * δ - 3 * α * β ^ 2 -
        2 * B.a₂ * α * β - B.a₄ * α) * X +
      C (γ ^ 2 * A.a₆ + ε ^ 2 + B.a₁ * β * ε + B.a₃ * ε - β ^ 3 - B.a₂ * β ^ 2 - B.a₄ * β - B.a₆)
      with hP
    set Q : F[X] := C (2 * γ * δ + B.a₁ * γ * α - γ ^ 2 * A.a₁) * X +
      C (2 * γ * ε + B.a₁ * γ * β + B.a₃ * γ - γ ^ 2 * A.a₃) with hQ
    have key : algebraMap F[X] A.toAffine.FunctionField P +
        algebraMap F[X] A.toAffine.FunctionField Q * genY A = 0 := by
      simp only [hP, hQ, map_add (f := _), map_mul, map_pow, algebraMap_C_functionField, ← genX_eq, map_sub,
        map_ofNat]
      linear_combination eB - ι γ ^ 2 * eA
    have c3 := congrArg (AddMonoidAlgebra.coeff · 3) (eq_zero_of_algebraMap_add_mul_genY A key).1
    simp [hP, coeff_X_pow, -map_sub] at c3
    linear_combination c3
  have hu2 : (α / γ) ^ 2 * α = 1 := by
    field_simp
    linear_combination -hc3
  have hu3 : (α / γ) ^ 3 * γ = 1 := by
    field_simp
    linear_combination -hc3
  have hδ : ι (δ / α) * ι α = ι δ := by rw [← map_mul, div_mul_cancel₀ δ hα]
  have hu2' : ι (α / γ) ^ 2 * ι α = 1 := by rw [← map_pow, ← map_mul, hu2, map_one]
  have hu3' : ι (α / γ) ^ 3 * ι γ = 1 := by rw [← map_pow, ← map_mul, hu3, map_one]
  let Cv : VariableChange F := ⟨Units.mk0 (γ / α) (div_ne_zero hγ hα), β, δ / α, ε⟩
  refine ⟨Cv, eq_of_equation_genX_genY A ?_⟩
  have hV := (nonsingular_variableChange (Cv.map ι) (B.baseChange A.toAffine.FunctionField) hN).1
  have hcurve : (Cv.map ι) • (B.baseChange A.toAffine.FunctionField) =
      (Cv • B).baseChange A.toAffine.FunctionField :=
    map_variableChange B Cv ι
  rw [hcurve] at hV
  have hX : (↑(Cv.map ι).u⁻¹ : A.toAffine.FunctionField) ^ 2 * (ψ.x - (Cv.map ι).r) = genX A := by
    show ι ((γ / α)⁻¹) ^ 2 * (ψ.x - ι β) = genX A
    rw [hx, inv_div]
    linear_combination genX A * hu2'
  have hY : (↑(Cv.map ι).u⁻¹ : A.toAffine.FunctionField) ^ 3 *
      (ψ.y - (Cv.map ι).s * (ψ.x - (Cv.map ι).r) - (Cv.map ι).t) = genY A := by
    show ι ((γ / α)⁻¹) ^ 3 * (ψ.y - ι (δ / α) * (ψ.x - ι β) - ι ε) = genY A
    rw [hx, hy, inv_div]
    linear_combination genY A * hu3' - ι (α / γ) ^ 3 * genX A * hδ
  rw [hX, hY] at hV
  exact hV

end AlgClosed

section General

variable {F : Type u} [Field F]

theorem j_eq_of_variableChange_eq {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
    (C : VariableChange F) (h : C • W = W') : W'.j = W.j := by
  subst h
  exact variableChange_j _ _

theorem j_eq_of_degree_eq_one {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]
    (ψ : Isogeny A B) (h : ψ.degree = 1) : B.j = A.j := by
  classical
  have hd : (isogBaseChange (F' := AlgebraicClosure F) ψ).degree = 1 := by
    rw [degree_isogBaseChange, h]
  obtain ⟨C, hC⟩ := exists_variableChange_of_degree_eq_one_of_isAlgClosed _ hd
  have hj : (A.baseChange (AlgebraicClosure F)).j = (B.baseChange (AlgebraicClosure F)).j :=
    j_eq_of_variableChange_eq C hC
  have eA : (A.baseChange (AlgebraicClosure F)).j = algebraMap F (AlgebraicClosure F) A.j :=
    map_j _ _
  have eB : (B.baseChange (AlgebraicClosure F)).j = algebraMap F (AlgebraicClosure F) B.j :=
    map_j _ _
  rw [eA, eB] at hj
  exact ((algebraMap F (AlgebraicClosure F)).injective hj).symm

theorem j_eq_pow_of_isogenyPullback_eq_zero {E E' : WeierstrassCurve F} [E.IsElliptic]
    [E'.IsElliptic] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') = 0) (hdeg : φ.degree = p) :
    E'.j = E.j ^ p := by
  obtain ⟨ψ, -, h1, -⟩ := exists_isomorphism_of_degree_eq p φ hφ hdeg
  rw [j_eq_of_degree_eq_one ψ h1, j_frobeniusTwist]

end General

end GroundTheory.Global
