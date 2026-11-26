module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FunctionFieldPoint

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsNorm
section -- merged from GroundTheory.ArithmeticGeometry.AbelianVarieties.Divisors
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain

open scoped nonZeroDivisors

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

section Field

variable {W}

noncomputable def evalPoint {x y : F} (h : W.toAffine.Equation x y) :
    W.toAffine.CoordinateRing →+* F :=
  AdjoinRoot.lift (evalRingHom x) y (by rw [eval₂_evalRingHom]; exact h)

theorem evalPoint_mk {x y : F} (h : W.toAffine.Equation x y) (p : F[X][X]) :
    evalPoint h (AdjoinRoot.mk W.toAffine.polynomial p) = p.evalEval x y := by
  rw [evalPoint, AdjoinRoot.lift_mk, eval₂_evalRingHom]

theorem evalPoint_XClass {x y : F} (h : W.toAffine.Equation x y) (x' : F) :
    evalPoint h (XClass W.toAffine x') = x - x' := by
  rw [XClass, evalPoint_mk]
  simp [evalEval_C]

theorem evalPoint_YClass {x y : F} (h : W.toAffine.Equation x y) (y' : F) :
    evalPoint h (YClass W.toAffine (C y')) = y - y' := by
  rw [YClass, evalPoint_mk]
  simp [evalEval_sub, evalEval_X, evalEval_C]

theorem XYIdeal_le_ker {x y : F} (h : W.toAffine.Equation x y) :
    XYIdeal W.toAffine x (C y) ≤ RingHom.ker (evalPoint h) := by
  rw [XYIdeal, Ideal.span_le]
  rintro _ (rfl | rfl)
  · simp [evalPoint_XClass]
  · simp [evalPoint_YClass]

theorem isMaximal_XYIdeal {x y : F} (h : W.toAffine.Equation x y) :
    (XYIdeal W.toAffine x (C y)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    MulEquiv.isField (Field.toIsField F)
      (quotientXYIdealEquiv (W' := W.toAffine) (x := x) (y := C y) h).toRingEquiv.toMulEquiv

theorem XYIdeal_ne_bot (x : F) (y : F[X]) : XYIdeal W.toAffine x y ≠ ⊥ := by
  intro h0
  have hx : XClass W.toAffine x ∈ XYIdeal W.toAffine x y :=
    Ideal.subset_span (Set.mem_insert _ _)
  rw [h0, Ideal.mem_bot] at hx
  exact XClass_ne_zero x hx

theorem XYIdeal_inj {x y x' y' : F} (h' : W.toAffine.Equation x' y')
    (he : XYIdeal W.toAffine x (C y) = XYIdeal W.toAffine x' (C y')) : x = x' ∧ y = y' := by
  have h1 : XClass W.toAffine x ∈ XYIdeal W.toAffine x' (C y') :=
    he ▸ Ideal.subset_span (Set.mem_insert _ _)
  have h2 : YClass W.toAffine (C y) ∈ XYIdeal W.toAffine x' (C y') :=
    he ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have e1 := XYIdeal_le_ker h' h1
  have e2 := XYIdeal_le_ker h' h2
  rw [RingHom.mem_ker, evalPoint_XClass] at e1
  rw [RingHom.mem_ker, evalPoint_YClass] at e2
  exact ⟨(sub_eq_zero.mp e1).symm, (sub_eq_zero.mp e2).symm⟩

noncomputable def heightOneOfNonsingular {x y : F} (h : W.toAffine.Nonsingular x y) :
    HeightOneSpectrum W.toAffine.CoordinateRing where
  asIdeal := XYIdeal W.toAffine x (C y)
  isPrime := (isMaximal_XYIdeal h.1).isPrime
  ne_bot := XYIdeal_ne_bot x (C y)

theorem heightOneOfNonsingular_asIdeal {x y : F} (h : W.toAffine.Nonsingular x y) :
    (heightOneOfNonsingular h).asIdeal = XYIdeal W.toAffine x (C y) := rfl

theorem heightOneOfNonsingular_inj {x y x' y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x' y')
    (he : heightOneOfNonsingular h = heightOneOfNonsingular h') : x = x' ∧ y = y' :=
  XYIdeal_inj h'.1 (congrArg HeightOneSpectrum.asIdeal he)

instance : IsNoetherianRing W.toAffine.CoordinateRing :=
  inferInstanceAs (IsNoetherianRing (F[X][X] ⧸ Ideal.span {W.toAffine.polynomial}))

end Field

theorem isDiscreteValuationRing_of_maximalIdeal_mul_eq {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] (hnf : ¬ IsField R) (J : Ideal R) {t : R} (ht : t ≠ 0)
    (h : IsLocalRing.maximalIdeal R * J = Ideal.span {t}) : IsDiscreteValuationRing R := by
  have hunit : IsUnit ((IsLocalRing.maximalIdeal R : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) := by
    refine isUnit_iff_exists_inv.mpr ⟨(J : FractionalIdeal R⁰ (FractionRing R)) *
        ((Ideal.span {t} : Ideal R) : FractionalIdeal R⁰ (FractionRing R))⁻¹, ?_⟩
    rw [← mul_assoc, ← FractionalIdeal.coeIdeal_mul, h,
      FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing R) ht]
  have hprinc := Ideal.IsPrincipal.of_finite_maximals_of_isUnit
    ((Set.finite_singleton (IsLocalRing.maximalIdeal R)).subset
      fun I hI => IsLocalRing.eq_maximalIdeal hI) hunit
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 1 5).mpr hprinc

section AlgClosed

variable [IsAlgClosed F]

theorem exists_equation (x : F) : ∃ y, W.toAffine.Equation x y := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    (C (1 : F) * X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)))
    (by rw [degree_quadratic one_ne_zero]; norm_num)
  refine ⟨y, (W.toAffine.equation_iff x y).mpr ?_⟩
  simp only [IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hy
  linear_combination hy

variable [W.IsElliptic]

theorem exists_eq_XYIdeal {P : Ideal W.toAffine.CoordinateRing} [hP : P.IsPrime] (hP0 : P ≠ ⊥) :
    ∃ x y, W.toAffine.Nonsingular x y ∧ P = XYIdeal W.toAffine x (C y) := by
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = P.comap (algebraMap F[X] W.toAffine.CoordinateRing) := ⟨_, rfl⟩
  have hQ0 : Q ≠ ⊥ := fun h => hP0 (Ideal.eq_bot_of_comap_eq_bot (hQdef ▸ h))
  have hQ : Q.IsPrime := hQdef ▸ Ideal.IsPrime.comap _
  have hg := Submodule.IsPrincipal.prime_generator_of_isPrime Q hQ0
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ (degree_pos_of_irreducible hg.irreducible).ne'
  have hdvd : Submodule.IsPrincipal.generator Q ∣ X - C x :=
    (irreducible_X_sub_C x).dvd_symm hg.irreducible (dvd_iff_isRoot.mpr hx)
  have hxQ : X - C x ∈ Q := by
    rw [← Submodule.IsPrincipal.span_singleton_generator Q]
    exact Ideal.mem_span_singleton.mpr hdvd
  have hXP : XClass W.toAffine x ∈ P := by
    have : algebraMap F[X] W.toAffine.CoordinateRing (X - C x) = XClass W.toAffine x := by
      simp only [XClass, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
    rw [← this]
    exact Ideal.mem_comap.mp (hQdef ▸ hxQ)
  obtain ⟨y, hy⟩ := exists_equation W x
  have hns : W.toAffine.Nonsingular x y := equation_iff_nonsingular.mp hy
  have hle : XYIdeal W.toAffine x (C (W.toAffine.negY x y)) * XYIdeal W.toAffine x (C y) ≤ P := by
    rw [XYIdeal_neg_mul hns, XIdeal, Ideal.span_le, Set.singleton_subset_iff]
    exact hXP
  rcases hP.mul_le.mp hle with h1 | h1
  · exact ⟨x, _, (nonsingular_neg ..).mpr hns,
      ((isMaximal_XYIdeal ((equation_neg ..).mpr hy)).eq_of_le hP.ne_top h1).symm⟩
  · exact ⟨x, y, hns, ((isMaximal_XYIdeal hy).eq_of_le hP.ne_top h1).symm⟩


omit [IsAlgClosed F] [W.IsElliptic] in
theorem isDiscreteValuationRing_localization_XYIdeal {x y : F} (h : W.toAffine.Nonsingular x y)
    [(XYIdeal W.toAffine x (C y)).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (XYIdeal W.toAffine x (C y))) := by
  have hnf : ¬ IsField (Localization.AtPrime (XYIdeal W.toAffine x (C y))) :=
    IsLocalization.AtPrime.not_isField W.toAffine.CoordinateRing (P := XYIdeal W.toAffine x (C y))
      (XYIdeal_ne_bot x (C y)) _
  have hinj : Function.Injective (algebraMap W.toAffine.CoordinateRing
      (Localization.AtPrime (XYIdeal W.toAffine x (C y)))) :=
    IsLocalization.injective _ (XYIdeal W.toAffine x (C y)).primeCompl_le_nonZeroDivisors
  have : IsNoetherianRing (Localization.AtPrime (XYIdeal W.toAffine x (C y))) :=
    IsLocalization.isNoetherianRing (XYIdeal W.toAffine x (C y)).primeCompl _ inferInstance
  refine isDiscreteValuationRing_of_maximalIdeal_mul_eq hnf
    ((XYIdeal W.toAffine x (C (W.toAffine.negY x y))).map (algebraMap _ _))
    ((map_ne_zero_iff _ hinj).mpr (XClass_ne_zero (W' := W.toAffine) x)) ?_
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (XYIdeal W.toAffine x (C y)), ← Ideal.map_mul, mul_comm,
    XYIdeal_neg_mul h, XIdeal, Ideal.map_span, Set.image_singleton]

theorem isDedekindDomainDvr_coordinateRing (P : Ideal W.toAffine.CoordinateRing) (hP0 : P ≠ ⊥)
    (hP : P.IsPrime) : IsDiscreteValuationRing (Localization.AtPrime P) := by
  obtain ⟨x, y, h, rfl⟩ := exists_eq_XYIdeal W hP0
  exact isDiscreteValuationRing_localization_XYIdeal W h

instance isDedekindDomain_coordinateRing : IsDedekindDomain W.toAffine.CoordinateRing :=
  isDedekindDomain_iff_isDiscreteValuationRing_atPrime.mpr
    ⟨inferInstance, isDedekindDomainDvr_coordinateRing W⟩

noncomputable def affinePointEquiv :
    {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2} ≃
      HeightOneSpectrum W.toAffine.CoordinateRing :=
  Equiv.ofBijective (fun p => heightOneOfNonsingular p.2)
    ⟨fun p q he => by
      obtain ⟨h1, h2⟩ := heightOneOfNonsingular_inj p.2 q.2 he
      exact Subtype.ext (Prod.ext h1 h2),
    fun v => by
      have := v.isPrime
      obtain ⟨x, y, h, hv⟩ := exists_eq_XYIdeal W v.ne_bot
      exact ⟨⟨(x, y), h⟩, HeightOneSpectrum.ext hv.symm⟩⟩

theorem affinePointEquiv_apply_asIdeal (p : {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2}) :
    (affinePointEquiv W p).asIdeal = XYIdeal W.toAffine p.1.1 (C p.1.2) := rfl

end AlgClosed

end GroundTheory.Arith.Abelian
end

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain

open scoped nonZeroDivisors

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

theorem finrank_coordinateRing : Module.finrank F[X] W.toAffine.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (CoordinateRing.basis W.toAffine)).trans (Fintype.card_fin 2)

theorem algebraMap_X_sub_C (x : F) :
    algebraMap F[X] W.toAffine.CoordinateRing (X - C x) = XClass W.toAffine x := by
  simp only [XClass, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

theorem XIdeal_eq_map (x : F) : XIdeal W.toAffine x =
    (Ideal.span {X - C x}).map (algebraMap F[X] W.toAffine.CoordinateRing) := by
  rw [XIdeal, Ideal.map_span, Set.image_singleton, algebraMap_X_sub_C]

theorem span_X_sub_C_le_comap_XYIdeal (x : F) (y : F[X]) :
    Ideal.span {X - C x} ≤ (XYIdeal W.toAffine x y).comap (algebraMap F[X] _) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    algebraMap_X_sub_C]
  exact Ideal.subset_span (Set.mem_insert _ _)

variable [IsAlgClosed F] [W.IsElliptic]

local instance : IsDedekindDomain W.toAffine.CoordinateRing := by
  refine isDedekindDomain_iff_isDiscreteValuationRing_atPrime.mpr ⟨inferInstance, ?_⟩
  intro P hP0 hP
  obtain ⟨x, y, h, rfl⟩ := exists_eq_XYIdeal W hP0
  exact isDiscreteValuationRing_localization_XYIdeal W h

theorem relNorm_XYIdeal {x y : F} (h : W.toAffine.Nonsingular x y) :
    Ideal.relNorm F[X] (XYIdeal W.toAffine x (C y)) = Ideal.span {X - C x} := by
  have hq : (Ideal.span {X - C x} : Ideal F[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C x)
  have hle : ∀ {y' : F}, W.toAffine.Nonsingular x y' →
      Ideal.relNorm F[X] (XYIdeal W.toAffine x (C y')) ≤ Ideal.span {X - C x} := by
    intro y' h'
    refine (Ideal.relNorm_le_comap F[X] _).trans ?_
    exact (hq.eq_of_le (Ideal.comap_ne_top _ (isMaximal_XYIdeal h'.1).ne_top)
      (span_X_sub_C_le_comap_XYIdeal W x (C y'))).ge
  have hmul : Ideal.relNorm F[X] (XYIdeal W.toAffine x (C (W.toAffine.negY x y))) *
      Ideal.relNorm F[X] (XYIdeal W.toAffine x (C y)) = Ideal.span {X - C x} ^ 2 := by
    rw [← map_mul, XYIdeal_neg_mul h, XIdeal_eq_map, Ideal.relNorm_algebraMap,
      finrank_coordinateRing]
  obtain ⟨a, ha⟩ := Ideal.dvd_iff_le.mpr (hle h)
  obtain ⟨b, hb⟩ := Ideal.dvd_iff_le.mpr (hle ((nonsingular_neg ..).mpr h))
  rw [ha, hb, pow_two] at hmul
  have hq0 : (Ideal.span {X - C x} : Ideal F[X]) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero x
  have hba : b * a = 1 := by
    refine mul_left_cancel₀ (mul_ne_zero hq0 hq0) ?_
    calc Ideal.span {X - C x} * Ideal.span {X - C x} * (b * a)
        = Ideal.span {X - C x} * b * (Ideal.span {X - C x} * a) := by ring
      _ = _ := hmul
      _ = _ := (mul_one _).symm
  have ha1 : a = 1 := by
    rw [Ideal.one_eq_top] at hba ⊢
    exact eq_top_iff.mpr (by rw [← hba, mul_comm]; exact Ideal.mul_le_left)
  rw [ha, ha1, mul_one]

omit [IsAlgClosed F] [W.IsElliptic] in
theorem finite_support_count [IsDedekindDomain W.toAffine.CoordinateRing]
    (I : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) :
    (Function.support fun v : HeightOneSpectrum W.toAffine.CoordinateRing =>
      FractionalIdeal.count W.toAffine.FunctionField v I).Finite :=
  Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)

theorem finsum_count_XYIdeal {x y : F} (h : W.toAffine.Nonsingular x y) :
    ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        ((XYIdeal W.toAffine x (C y) : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) = 1 := by
  classical
  have hc := fun v => FractionalIdeal.count_maximal W.toAffine.FunctionField v
    (heightOneOfNonsingular h)
  simp only [heightOneOfNonsingular_asIdeal] at hc
  rw [finsum_eq_single _ (heightOneOfNonsingular h) (fun v hv => by
    rw [hc v, ite_eq_right (fun e => hv e.symm)]), hc, ite_eq_left rfl]

theorem natDegree_eq_finsum_count_of_relNorm_eq {I : Ideal W.toAffine.CoordinateRing} (hI : I ≠ 0)
    {p : F[X]} (hp : Ideal.relNorm F[X] I = Ideal.span {p}) :
    (p.natDegree : ℤ) = ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        (I : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime generalizing p with
  | h₁ => exact absurd rfl hI
  | h₂ I hu =>
    rw [Ideal.isUnit_iff.mp hu, Ideal.relNorm_top, eq_comm, Ideal.span_singleton_eq_top] at hp
    rw [Ideal.isUnit_iff.mp hu, FractionalIdeal.coeIdeal_top]
    simp [FractionalIdeal.count_one, natDegree_eq_zero_of_isUnit hp]
  | h₃ a P ha hP ih =>
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have := Ideal.isPrime_of_prime hP
    obtain ⟨x, y, h, rfl⟩ := exists_eq_XYIdeal W hP0
    obtain ⟨g, hg⟩ : ∃ g, Ideal.relNorm F[X] a = Ideal.span {g} :=
      ⟨_, (Submodule.IsPrincipal.span_singleton_generator _).symm⟩
    have hg0 : g ≠ 0 := by
      rintro rfl
      have hb : Ideal.relNorm F[X] a = ⊥ := by rw [hg]; simp
      exact ha (Ideal.relNorm_eq_bot_iff.mp hb)
    rw [map_mul, relNorm_XYIdeal W h, hg, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_eq_span_singleton] at hp
    have hdeg : p.natDegree = ((X - C x) * g).natDegree :=
      natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hp).symm
    have hc0 : ((XYIdeal W.toAffine x (C y) : Ideal _) :
        FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hP0
    have ha0 : (a : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr ha
    rw [hdeg, natDegree_mul (X_sub_C_ne_zero x) hg0, natDegree_X_sub_C,
      FractionalIdeal.coeIdeal_mul]
    simp_rw [FractionalIdeal.count_mul _ _ hc0 ha0]
    rw [finsum_add_distrib (finite_support_count W _) (finite_support_count W _),
      finsum_count_XYIdeal W h, ← ih ha hg]
    push_cast
    ring

theorem natDegree_norm_eq_finsum_count {f : W.toAffine.CoordinateRing} (hf : f ≠ 0) :
    ((Algebra.norm F[X] f).natDegree : ℤ) = ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        ((Ideal.span {f} : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by
  refine natDegree_eq_finsum_count_of_relNorm_eq W ?_ ?_
  · rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  · rw [Ideal.relNorm_singleton, Algebra.intNorm_eq_norm]

end GroundTheory.Arith.Abelian
end

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero

open scoped nonZeroDivisors

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

section Infinity

omit [Field F] in
private theorem two_nsmul_add_le {u v w : WithBot ℕ} (h : u ≤ max v w) (c : WithBot ℕ) :
    2 • u + c ≤ max (2 • v + c) (2 • w + c) := by
  rcases le_total v w with hvw | hvw
  · rw [max_eq_right hvw] at h
    exact le_max_of_le_right (add_le_add (nsmul_le_nsmul_right h 2) le_rfl)
  · rw [max_eq_left hvw] at h
    exact le_max_of_le_left (add_le_add (nsmul_le_nsmul_right h 2) le_rfl)

theorem degree_norm_add_le (a b : W.toAffine.CoordinateRing) :
    (Algebra.norm F[X] (a + b)).degree ≤
      max (Algebra.norm F[X] a).degree (Algebra.norm F[X] b).degree := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  obtain ⟨p', q', rfl⟩ := exists_smul_basis_eq b
  have hs : p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X +
      (p' • 1 + q' • AdjoinRoot.mk W.toAffine.polynomial X) =
        (p + p') • 1 + (q + q') • AdjoinRoot.mk W.toAffine.polynomial X := by
    rw [add_smul, add_smul]; abel
  rw [hs, degree_norm_smul_basis, degree_norm_smul_basis, degree_norm_smul_basis]
  have h1 := two_nsmul_add_le (degree_add_le p p') 0
  have h2 := two_nsmul_add_le (degree_add_le q q') 3
  simp only [add_zero] at h1
  exact max_le (h1.trans (max_le_max (le_max_left _ _) (le_max_left _ _)))
    (h2.trans (max_le_max (le_max_right _ _) (le_max_right _ _)))

theorem norm_coordinateRing_ne_zero {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    Algebra.norm F[X] a ≠ 0 :=
  Algebra.norm_ne_zero_iff.mpr ha

noncomputable def valuationInftyCoord : Valuation W.toAffine.CoordinateRing ℤᵐ⁰ where
  toFun a := if a = 0 then 0 else exp ((Algebra.norm F[X] a).natDegree : ℤ)
  map_zero' := if_pos rfl
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp only [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, map_mul,
      natDegree_mul (norm_coordinateRing_ne_zero W ha) (norm_coordinateRing_ne_zero W hb),
      Nat.cast_add, exp_add]
  map_add_le_max' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    by_cases hab : a + b = 0
    · simp [hab]
    simp only [if_neg ha, if_neg hb, if_neg hab]
    have hd := degree_norm_add_le W a b
    rw [degree_eq_natDegree (norm_coordinateRing_ne_zero W hab),
      degree_eq_natDegree (norm_coordinateRing_ne_zero W ha),
      degree_eq_natDegree (norm_coordinateRing_ne_zero W hb)] at hd
    rcases le_max_iff.mp hd with h | h
    · exact le_max_of_le_left (exp_le_exp.mpr (by exact_mod_cast WithBot.coe_le_coe.mp h))
    · exact le_max_of_le_right (exp_le_exp.mpr (by exact_mod_cast WithBot.coe_le_coe.mp h))

theorem valuationInftyCoord_apply {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    valuationInftyCoord W a = exp ((Algebra.norm F[X] a).natDegree : ℤ) := if_neg ha

theorem valuationInftyCoord_ne_zero {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    valuationInftyCoord W a ≠ 0 := by
  rw [valuationInftyCoord_apply W ha]; exact exp_ne_zero

noncomputable def valuationInfty : Valuation W.toAffine.FunctionField ℤᵐ⁰ :=
  (valuationInftyCoord W).extendToLocalization (S := W.toAffine.CoordinateRing⁰)
    (fun _ hr => Set.mem_compl (valuationInftyCoord_ne_zero W (nonZeroDivisors.ne_zero hr)))
    W.toAffine.FunctionField

theorem valuationInfty_algebraMap (a : W.toAffine.CoordinateRing) :
    valuationInfty W (algebraMap _ W.toAffine.FunctionField a) = valuationInftyCoord W a :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ a

noncomputable def ordInfty (f : W.toAffine.FunctionField) : ℤ :=
  -log (valuationInfty W f)

theorem valuationInfty_ne_zero {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    valuationInfty W f ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr hf

theorem valuationInfty_eq_exp {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    valuationInfty W f = exp (-ordInfty W f) := by
  rw [ordInfty, neg_neg, exp_log (valuationInfty_ne_zero W hf)]

theorem ordInfty_algebraMap {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    ordInfty W (algebraMap _ W.toAffine.FunctionField a) =
      -((Algebra.norm F[X] a).natDegree : ℤ) := by
  rw [ordInfty, valuationInfty_algebraMap, valuationInftyCoord_apply W ha, log_exp]

theorem ordInfty_mul {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordInfty W (f * g) = ordInfty W f + ordInfty W g := by
  rw [ordInfty, ordInfty, ordInfty, map_mul,
    log_mul (valuationInfty_ne_zero W hf) (valuationInfty_ne_zero W hg), neg_add]

theorem ordInfty_inv (f : W.toAffine.FunctionField) : ordInfty W f⁻¹ = -ordInfty W f := by
  rw [ordInfty, ordInfty, map_inv₀, log_inv]

theorem ordInfty_div {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordInfty W (f / g) = ordInfty W f - ordInfty W g := by
  rw [div_eq_mul_inv, ordInfty_mul W hf (inv_ne_zero hg), ordInfty_inv, sub_eq_add_neg]

theorem ordInfty_algebraMap_const {c : F} (hc : c ≠ 0) :
    ordInfty W (algebraMap F W.toAffine.FunctionField c) = 0 := by
  have h : algebraMap F W.toAffine.FunctionField c =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap F[X] W.toAffine.CoordinateRing (C c)) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F F[X] W.toAffine.FunctionField c,
      algebraMap_eq]
  have hc' : algebraMap F[X] W.toAffine.CoordinateRing (C c) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr (C_ne_zero.mpr hc)
  rw [h, ordInfty_algebraMap W hc', Algebra.norm_algebraMap, finrank_coordinateRing, ← C_pow,
    natDegree_C, Nat.cast_zero, neg_zero]

theorem ordInfty_X :
    ordInfty W (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial (C X))) = -2 := by
  have hx : AdjoinRoot.mk W.toAffine.polynomial (C X) =
      algebraMap F[X] W.toAffine.CoordinateRing X := by
    simp only [AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  have h0 : algebraMap F[X] W.toAffine.CoordinateRing X ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr X_ne_zero
  rw [hx, ordInfty_algebraMap W h0, Algebra.norm_algebraMap, finrank_coordinateRing,
    natDegree_X_pow]
  norm_num

theorem ordInfty_Y :
    ordInfty W (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial X)) = -3 := by
  have hy : AdjoinRoot.mk W.toAffine.polynomial X =
      (0 : F[X]) • (1 : W.toAffine.CoordinateRing) +
        (1 : F[X]) • AdjoinRoot.mk W.toAffine.polynomial X := by
    rw [zero_smul, one_smul, zero_add]
  have hdeg := degree_norm_smul_basis (W' := W.toAffine) (0 : F[X]) 1
  rw [← hy, degree_zero, degree_one] at hdeg
  have hdeg' : (Algebra.norm F[X] (AdjoinRoot.mk W.toAffine.polynomial X)).degree = 3 := by
    rw [hdeg]; rfl
  have h0 : AdjoinRoot.mk W.toAffine.polynomial X ≠ 0 := by
    rw [← basis_one]
    exact (CoordinateRing.basis W.toAffine).ne_zero 1
  rw [ordInfty_algebraMap W h0, natDegree_eq_of_degree_eq_some hdeg']
  norm_num

theorem ordInfty_X_div_Y :
    ordInfty W (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial (C X)) /
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.mk W.toAffine.polynomial X)) = 1 := by
  have hne : ∀ f : W.toAffine.FunctionField, ordInfty W f ≠ 0 → f ≠ 0 := by
    rintro f hf rfl
    exact hf (by simp [ordInfty])
  rw [ordInfty_div W (hne _ (by rw [ordInfty_X]; norm_num)) (hne _ (by rw [ordInfty_Y]; norm_num)),
    ordInfty_X, ordInfty_Y]
  norm_num

end Infinity

section Affine

variable [IsAlgClosed F] [W.IsElliptic]

noncomputable def ordAtIdeal (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    (f : W.toAffine.FunctionField) : ℤ :=
  FractionalIdeal.count W.toAffine.FunctionField v
    (FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ f)

omit [IsAlgClosed F] [W.IsElliptic] in
theorem spanSingleton_ne_zero {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ f ≠ 0 :=
  FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hf

theorem ordAtIdeal_mul (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordAtIdeal W v (f * g) = ordAtIdeal W v f + ordAtIdeal W v g := by
  rw [ordAtIdeal, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul _ _ (spanSingleton_ne_zero W hf) (spanSingleton_ne_zero W hg)]
  rfl

theorem ordAtIdeal_algebraMap (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    (a : W.toAffine.CoordinateRing) :
    ordAtIdeal W v (algebraMap _ W.toAffine.FunctionField a) =
      FractionalIdeal.count W.toAffine.FunctionField v
        ((Ideal.span {a} : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by
  rw [ordAtIdeal, FractionalIdeal.coeIdeal_span_singleton]

theorem valuation_eq_exp_neg_ordAtIdeal (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    v.valuation W.toAffine.FunctionField f = exp (-ordAtIdeal W v f) := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
  dsimp only at hf ⊢
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf (IsLocalization.mk'_zero _)
  have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hs' : algebraMap _ W.toAffine.FunctionField (s : W.toAffine.CoordinateRing) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ W.toAffine.FunctionField)).mpr hs
  have hsa : Ideal.span {a} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hss : Ideal.span {(s : W.toAffine.CoordinateRing)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hord := ordAtIdeal_mul W v hf hs'
  rw [IsLocalization.mk'_spec, ordAtIdeal_algebraMap, ordAtIdeal_algebraMap] at hord
  rw [HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.intValuation_if_neg _ ha,
    HeightOneSpectrum.intValuation_if_neg _ hs, ← FractionalIdeal.count_coe W.toAffine.FunctionField v hsa,
    ← FractionalIdeal.count_coe W.toAffine.FunctionField v hss, ← exp_sub]
  congr 1
  linarith

noncomputable def valuationPoint : W.toAffine.Point → Valuation W.toAffine.FunctionField ℤᵐ⁰
  | .zero => valuationInfty W
  | .some _ _ h => (heightOneOfNonsingular h).valuation W.toAffine.FunctionField

noncomputable def ordPoint : W.toAffine.Point → W.toAffine.FunctionField → ℤ
  | .zero => ordInfty W
  | .some _ _ h => ordAtIdeal W (heightOneOfNonsingular h)

theorem ordPoint_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    ordPoint W (.some x y h) = ordAtIdeal W (heightOneOfNonsingular h) := rfl

theorem valuationPoint_eq_exp (P : W.toAffine.Point) {f : W.toAffine.FunctionField}
    (hf : f ≠ 0) : valuationPoint W P f = exp (-ordPoint W P f) := by
  cases P with
  | zero => exact valuationInfty_eq_exp W hf
  | some x y h => exact valuation_eq_exp_neg_ordAtIdeal W _ hf

theorem ordPoint_mul (P : W.toAffine.Point) {f g : W.toAffine.FunctionField} (hf : f ≠ 0)
    (hg : g ≠ 0) : ordPoint W P (f * g) = ordPoint W P f + ordPoint W P g := by
  cases P with
  | zero => exact ordInfty_mul W hf hg
  | some x y h => exact ordAtIdeal_mul W _ hf hg

theorem exists_valuationPoint_eq_exp_neg_one (P : W.toAffine.Point) :
    ∃ t : W.toAffine.FunctionField, valuationPoint W P t = exp (-1) := by
  cases P with
  | zero =>
    refine ⟨algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial (C X)) /
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.mk W.toAffine.polynomial X), ?_⟩
    rw [valuationPoint, valuationInfty_eq_exp W, ordInfty_X_div_Y]
    intro h0
    have := ordInfty_X_div_Y W
    rw [h0] at this
    simp [ordInfty] at this
  | some x y h => exact HeightOneSpectrum.valuation_exists_uniformizer _ _

end Affine

end GroundTheory.Arith.Abelian
