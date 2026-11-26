module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterMemIff
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.MemMCoordIdealIffOfIsWeightedHomogeneous
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PSubringPrimeMaximal
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StAdjoinIndepRelfinrank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra

noncomputable section

namespace OrbitCurve

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def tDeg (ι : Type) [DecidableEq ι] : ι → ι → ℕ := fun k ↦ Pi.single k 1


omit [Fintype ι] in
theorem isWeightedHomogeneous_mConeMap (x : Cone n (AlgebraicClosure ℚ))
    {f : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f b) :
    IsWeightedHomogeneous (tDeg ι) (Geo.mConeMap (ι := blockIdx n) (flatCone x) f) b := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  rw [Geo.mConeMap, aeval_monomial, Finsupp.prod, MvPolynomial.algebraMap_apply]
  have hb : b = 0 + ∑ p ∈ m.support, m p • tDeg ι p.1 := by
    rw [zero_add, ← hf (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum]
    rfl
  rw [hb]
  refine (isWeightedHomogeneous_C _ _).mul (IsWeightedHomogeneous.prod _ _ _ fun p _ ↦ ?_)
  have h := ((isWeightedHomogeneous_C (tDeg ι) (flatCone x p)).mul
    (isWeightedHomogeneous_X (AlgebraicClosure ℚ) (tDeg ι) p.1)).pow (m p)
  rwa [zero_add] at h


omit [Fintype ι] in
theorem mConeMap_weightedHomogeneousComponent (x : Cone n (AlgebraicClosure ℚ))
    (f : MvPolynomial (Coord n) ℤ) (b : ι → ℕ) :
    Geo.mConeMap (ι := blockIdx n) (flatCone x) (weightedHomogeneousComponent (coordDeg n) b f) =
      weightedHomogeneousComponent (tDeg ι) b (Geo.mConeMap (ι := blockIdx n) (flatCone x) f) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum, map_sum]
  have hom : ∀ a, IsWeightedHomogeneous (tDeg ι)
      (Geo.mConeMap (ι := blockIdx n) (flatCone x) (weightedHomogeneousComponent (coordDeg n) a f)) a :=
    fun a ↦ isWeightedHomogeneous_mConeMap x (weightedHomogeneousComponent_isWeightedHomogeneous a f)
  rw [Finset.sum_eq_single b]
  · exact (IsWeightedHomogeneous.weightedHomogeneousComponent_same (hom b)).symm
  · intro a _ hab
    exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne b (hom a) (Ne.symm hab)
  · intro hb
    have h0 : weightedHomogeneousComponent (coordDeg n) b f = 0 := by
      by_contra h
      exact hb ((Set.Finite.mem_toFinset _).mpr h)
    rw [h0, map_zero, map_zero]


omit [Fintype ι] [DecidableEq ι] in
theorem isPrime_orbitIdeal (x : Cone n (AlgebraicClosure ℚ)) : (orbitIdeal x).IsPrime :=
  RingHom.ker_isPrime _


omit [Fintype ι] in
theorem weightedHomogeneousComponent_mem_orbitIdeal (x : Cone n (AlgebraicClosure ℚ))
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ orbitIdeal x) (b : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) b f ∈ orbitIdeal x := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at hf ⊢
  rw [mConeMap_weightedHomogeneousComponent, hf, map_zero]

theorem isMultiHomogIdeal_orbitIdeal (x : Cone n (AlgebraicClosure ℚ)) :
    Geo.IsMultiHomogIdeal (ι := blockIdx n) (orbitIdeal x) := by
  classical
  refine ⟨{f | f ∈ orbitIdeal x ∧ ∃ a, Geo.IsMultiHomog (ι := blockIdx n) f a}, fun f hf ↦ hf.2,
    le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.mpr fun f hf ↦ hf.1)⟩
  rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  refine Ideal.sum_mem _ fun m _ ↦
    Ideal.subset_span ⟨weightedHomogeneousComponent_mem_orbitIdeal x hf m, m, ?_⟩
  exact (geoMultiHomog_iff _ m).mpr (weightedHomogeneousComponent_isWeightedHomogeneous m f)

theorem isRelevant_orbitIdeal {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    Geo.IsRelevant (ι := blockIdx n) (orbitIdeal x) := by
  obtain ⟨c, hc⟩ := exists_chart hx
  refine fun k ↦ ⟨c k, fun h ↦ ?_⟩
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X] at h
  exact mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _) h


omit [Fintype ι] [DecidableEq ι] in
theorem isHorizontal_orbitIdeal (x : Cone n (AlgebraicClosure ℚ)) :
    Geo.IsHorizontal (ι := blockIdx n) (orbitIdeal x) := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_bot, orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker]
  change aeval _ (C a) = 0 ↔ a = 0
  rw [aeval_C]
  exact map_eq_zero_iff _ (RingHom.injective_int _)

def coneMapQ (x : Cone n (AlgebraicClosure ℚ)) :
    MvPolynomial (Coord n) ℚ →ₐ[ℚ] MvPolynomial ι (AlgebraicClosure ℚ) :=
  aeval fun p ↦ C (flatCone x p) * X p.1

omit [Fintype ι] [DecidableEq ι] in
theorem coneMapQ_map (x : Cone n (AlgebraicClosure ℚ)) (f : MvPolynomial (Coord n) ℤ) :
    coneMapQ x (map (Int.castRingHom ℚ) f) = Geo.mConeMap (ι := blockIdx n) (flatCone x) f := by
  rw [← algebraMap_int_eq, coneMapQ, aeval_map_algebraMap]
  rfl


omit [Fintype ι] [DecidableEq ι] in
theorem comap_ker_coneMapQ (x : Cone n (AlgebraicClosure ℚ)) :
    (RingHom.ker (coneMapQ x)).comap (map (Int.castRingHom ℚ)) = orbitIdeal x := by
  ext f
  rw [Ideal.mem_comap, RingHom.mem_ker, coneMapQ_map, orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker]


omit [DecidableEq ι] in
theorem ker_coneMapQ (x : Cone n (AlgebraicClosure ℚ)) :
    RingHom.ker (coneMapQ x) = ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) := by
  have := isPrime_orbitIdeal x
  have hz : ∀ m : ℤ, (C m : MvPolynomial (Coord n) ℤ) ∈ orbitIdeal x → m = 0 := fun m hm ↦ by
    have h : m ∈ (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := hm
    rwa [show (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) = ⊥ from
      isHorizontal_orbitIdeal x, Ideal.mem_bot] at h
  obtain ⟨-, hc, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec (orbitIdeal x) hz
  have hle : ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) ≤ RingHom.ker (coneMapQ x) :=
    Ideal.map_le_iff_le_comap.mpr (comap_ker_coneMapQ x).ge
  refine (eq_of_le_of_not_lt hle fun hlt ↦ ?_).symm
  have h := ReciprocityTheory.AnForm.R.IntegerToRational.comap_strictMono hlt
  simp only [hc, comap_ker_coneMapQ] at h
  exact lt_irrefl _ h


omit [Fintype ι] [DecidableEq ι] in
theorem algebraicIndependent_C_mul_X (a : ι → AlgebraicClosure ℚ) (ha : ∀ k, a k ≠ 0) :
    AlgebraicIndependent ℚ (fun k ↦ (C (a k) * X k : MvPolynomial ι (AlgebraicClosure ℚ))) := by
  let φ : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (a k) * X k
  let ψ : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (a k)⁻¹ * X k
  have hψφ : ψ.comp φ = AlgHom.id _ _ := by
    refine MvPolynomial.algHom_ext fun k ↦ ?_
    simp only [φ, ψ, AlgHom.comp_apply, aeval_X, map_mul, aeval_C, MvPolynomial.algebraMap_eq,
      AlgHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (ha k), C_1, one_mul]
  have hφ : Function.Injective φ := Function.LeftInverse.injective (g := ψ) fun p ↦ by
    rw [← AlgHom.comp_apply, hψφ, AlgHom.id_apply]
  have h := ((MvPolynomial.algebraicIndependent_X ι (AlgebraicClosure ℚ)).map' hφ).restrictScalars
    (R := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  convert h using 1
  funext k
  simp [φ]

theorem trdeg_range_coneMapQ {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    trdeg ℚ (coneMapQ x).range = Fintype.card ι := by
  obtain ⟨c, hc⟩ := exists_chart hx
  refine le_antisymm ?_ ?_
  · calc trdeg ℚ (coneMapQ x).range ≤ trdeg ℚ (MvPolynomial ι (AlgebraicClosure ℚ)) :=
          trdeg_le_of_injective (coneMapQ x).range.val Subtype.val_injective
      _ = Fintype.card ι := by
          have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
          rw [← trdeg_add_eq ℚ (AlgebraicClosure ℚ) (A := MvPolynomial ι (AlgebraicClosure ℚ)),
            trdeg_eq_zero, MvPolynomial.trdeg_of_isDomain]
          simp
  · let u : ι → (coneMapQ x).range := fun k ↦
      ⟨C (x k (c k)) * X k, ⟨X ⟨k, c k⟩, by simp [coneMapQ, flatCone]⟩⟩
    have hu : AlgebraicIndependent ℚ u :=
      AlgebraicIndependent.of_comp (coneMapQ x).range.val (algebraicIndependent_C_mul_X _ hc)
    simpa using hu.cardinalMk_le_trdeg

theorem ringKrullDim_quot_ker_coneMapQ {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    ringKrullDim (MvPolynomial (Coord n) ℚ ⧸ RingHom.ker (coneMapQ x)) = Fintype.card ι := by
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (coneMapQ x)).toRingEquiv]
  have : Algebra.FiniteType ℚ (coneMapQ x).range :=
    Algebra.FiniteType.of_surjective (coneMapQ x).rangeRestrict (coneMapQ x).rangeRestrict_surjective
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg ℚ, trdeg_range_coneMapQ hx]
  simp

theorem ringKrullDim_orbitIdeal {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ orbitIdeal x) =
      ((1 + Fintype.card ι : ℕ) : WithBot ℕ∞) := by
  have := isPrime_orbitIdeal x
  have hz : ∀ m : ℤ, (C m : MvPolynomial (Coord n) ℤ) ∈ orbitIdeal x → m = 0 := fun m hm ↦ by
    have h : m ∈ (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := hm
    rwa [show (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) = ⊥ from
      isHorizontal_orbitIdeal x, Ideal.mem_bot] at h
  obtain ⟨-, -, h⟩ := ReciprocityTheory.AnForm.R.extQ_spec (orbitIdeal x) hz
  rw [← h, ← ker_coneMapQ, ringKrullDim_quot_ker_coneMapQ hx, Nat.cast_add, Nat.cast_one, add_comm]

end OrbitCurve

theorem OrbitCurve.full : OrbitCurve.Statement := by
  intro ι _ _ _ n x hx
  exact ⟨inferInstance, ⟨OrbitCurve.isPrime_orbitIdeal x, OrbitCurve.isMultiHomogIdeal_orbitIdeal x,
    OrbitCurve.isRelevant_orbitIdeal hx⟩, OrbitCurve.isHorizontal_orbitIdeal x,
    OrbitCurve.ringKrullDim_orbitIdeal hx⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  refine isJacobsonRing_iff_prime_eq.mpr fun P hP ↦ ?_
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun a ha ↦ ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at ha
    have h1 := Int.isUnit_iff.mp (ha 1)
    have h2 := Int.isUnit_iff.mp (ha (-1))
    rw [Ideal.mem_bot]
    omega
  · have := hP.isMaximal h
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem natCard_eq_pow_length_of_finiteType (F : Type) [Field F] [Algebra.FiniteType ℤ F]
    (q : ℕ) [CharP F q] :
    q.Prime ∧ Nat.card F = q ^ (Module.length ℤ F).toNat := by
  have := int_isJacobsonRing
  have : Module.Finite ℤ F := finite_of_finite_type_of_isJacobsonRing ℤ F
  have hq : q ≠ 0 := by
    rintro rfl
    have : CharZero F := CharP.charP_to_charZero F
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (fun a b h ↦ by simpa using h) (Field.toIsField F))
  have hqp : q.Prime := (CharP.char_is_prime_or_zero F q).resolve_right hq
  have : Fact q.Prime := ⟨hqp⟩
  let : Algebra (ZMod q) F := ZMod.algebra F q
  have : Module.Finite (ZMod q) F := Module.Finite.of_restrictScalars_finite ℤ (ZMod q) F
  have : Finite F := Module.finite_of_finite (ZMod q)
  have : Fintype F := Fintype.ofFinite F
  refine ⟨hqp, ?_⟩
  rw [Module.length_eq_of_surjective (S := ℤ) (R := ZMod q) (M := F) (ZMod.intCast_surjective),
    Module.length_eq_finrank, ENat.toNat_natCast, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]

theorem OrbitChartResidue.proof (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement)
    (hD : OrbitChartDehom.Statement) : OrbitChartResidue.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c hc
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have hrel : Geo.IsRelevant V := hV.2
  have hxc : ∀ c' : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → ∀ k, x k (c' k) ≠ 0 := by
    intro c' h k h0
    apply h k
    apply hPV
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h0]
  set i : (k : ι) → Fin (n k + 1) := fun k ↦ (hrel k).choose
  have hi : ∀ k, (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) ∉ V := fun k ↦ (hrel k).choose_spec
  obtain ⟨eQ⟩ := hQ ι n x c (hxc c hc) V hPV
  obtain ⟨hchar, ⟨eD⟩⟩ := hD ι n A x s hx hs V hV i c hi hc
  set J := V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) - 1)
  let e : (chartRing x c ⧸ chartPoint x c V) ≃+* (MvPolynomial (Coord n) ℤ ⧸ J) := eQ.trans eD.symm
  have := hM ι n A x s hx hs V hV c hc
  have hfield : IsField (MvPolynomial (Coord n) ℤ ⧸ J) :=
    MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)
      e.symm.toMulEquiv
  have : J.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield
  let : Field (MvPolynomial (Coord n) ℤ ⧸ J) := Ideal.Quotient.field J
  have hft : Algebra.FiniteType ℤ (MvPolynomial (Coord n) ℤ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ J)
      (Ideal.Quotient.mkₐ_surjective ℤ J)
  have : CharP (MvPolynomial (Coord n) ℤ ⧸ J) (Geo.charOf V) := by
    constructor
    intro a
    have hJC : ∀ b : ℤ, ((b : MvPolynomial (Coord n) ℤ ⧸ J) = 0 ↔ b ∈ V.comap (C : ℤ →+* _)) := by
      intro b
      rw [(map_intCast (Ideal.Quotient.mk J) b).symm.trans (congrArg _ (eq_intCast C b).symm),
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hchar]
    rw [← Int.cast_natCast, hJC, Submodule.IsPrincipal.mem_iff_generator_dvd, ← Int.natAbs_dvd,
      Int.natCast_dvd_natCast]
    rfl
  obtain ⟨-, hcard⟩ := @natCard_eq_pow_length_of_finiteType (MvPolynomial (Coord n) ℤ ⧸ J) _
    (by convert hft using 1 <;> rfl) (Geo.charOf V) _
  have hgeo : Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 =
      ((Module.length ℤ (MvPolynomial (Coord n) ℤ ⧸ J)).toNat : ℤ) := by
    simp only [Geo.geoNum, dif_pos hrel]
    rfl
  rw [hgeo, Nat.card_congr e.toEquiv, hcard, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}


omit [Fintype ι] [DecidableEq ι] in
theorem val_chartEval_eq_aeval_div (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : chartRing x c) : ratioField x) : AlgebraicClosure ℚ) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), Subalgebra.coe_add, IntermediateField.coe_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Subalgebra.coe_mul, IntermediateField.coe_mul, hp]
    simp [chartEval, chartRatio]


omit [Fintype ι] [DecidableEq ι] in
theorem chartEval_surjective (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Function.Surjective (chartEval x c) := by
  rintro ⟨a, ha⟩
  rw [chartRing, Algebra.adjoin_range_eq_range_aeval] at ha
  obtain ⟨f, rfl⟩ := ha
  refine ⟨f, Subtype.ext ?_⟩
  have h : (chartRing x c).val.comp (chartEval x c) = aeval (chartRatio x c) :=
    MvPolynomial.algHom_ext fun p ↦ by simp [chartEval]
  exact AlgHom.congr_fun h f


omit [Fintype ι] [DecidableEq ι] in
theorem mem_ker_chartEval_iff (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    f ∈ RingHom.ker (chartEval x c) ↔ aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0 := by
  rw [RingHom.mem_ker, ← val_chartEval_eq_aeval_div]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact Subtype.ext (Subtype.ext h)

theorem aeval_blockScale_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (t : ι → Ω) (w : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    aeval (fun p ↦ t p.1 * w p) g = (∏ k, t k ^ m k) * aeval w g := by
  have h : algebraMap ℤ Ω = Int.castRingHom Ω := Subsingleton.elim _ _
  rw [aeval_def, aeval_def, h]
  exact eval₂_scale_of_isWeightedHomogeneous t w hg

theorem ker_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) :
    RingHom.ker (chartEval x c) = orbitIdeal x ⊔
      Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) := by
  set J := Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) with hJ
  set z : Coord n → AlgebraicClosure ℚ := fun p ↦ x p.1 p.2 / x p.1 (c p.1) with hz
  apply le_antisymm
  · intro f hf
    rw [mem_ker_chartEval_iff] at hf
    set N : ι → ℕ := fun k ↦ (compDegs f).sup fun m ↦ m k with hN
    have hle : ∀ m ∈ compDegs f, m ≤ N := fun m hm k ↦ Finset.le_sup (f := fun m : ι → ℕ ↦ m k) hm
    set F := ∑ m ∈ compDegs f,
      weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m) with hF
    have hFJ : f - F ∈ J := by
      have h1 : ∀ d, Ideal.Quotient.mk J (chartMonomial c d) = 1 := by
        intro d
        rw [chartMonomial, map_prod]
        refine Finset.prod_eq_one fun k _ ↦ ?_
        have hk : Ideal.Quotient.mk J (X ⟨k, c k⟩) = 1 := by
          rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
          exact Ideal.subset_span ⟨k, rfl⟩
        rw [map_pow, hk, one_pow]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq, hF, map_sum]
      simp only [map_mul, h1, mul_one]
      conv_lhs => rw [← sum_compDegs f]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
    have hFP : F ∈ orbitIdeal x := by
      have hhom : IsWeightedHomogeneous (coordDeg n) F N := by
        have : F ∈ weightedHomogeneousSubmodule ℤ (coordDeg n) N := by
          refine Submodule.sum_mem _ fun m hm ↦ ?_
          have h2 := (weightedHomogeneousComponent_isWeightedHomogeneous m f).mul
            (isWeightedHomogeneous_chartMonomial c (N - m))
          rwa [add_tsub_cancel_of_le (hle m hm)] at h2
        exact this
      rw [orbitIdeal, mem_mCoordIdeal_iff_of_isWeightedHomogeneous _ hhom]
      have hy : flatCone x = fun p ↦ x p.1 (c p.1) * z p := by
        funext p
        simp only [hz, flatCone]
        rw [mul_div_cancel₀ _ (hc p.1)]
      have hterm : ∀ m ∈ compDegs f,
          aeval (flatCone x) (weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m)) =
            (∏ k, x k (c k) ^ N k) * aeval z (weightedHomogeneousComponent (coordDeg n) m f) := by
        intro m hm
        have hs := aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ x k (c k)) z
          (weightedHomogeneousComponent_isWeightedHomogeneous m f)
        have hmon : aeval (flatCone x) (chartMonomial c (N - m)) = ∏ k, x k (c k) ^ (N k - m k) := by
          simp [chartMonomial, map_prod, flatCone]
        have hpow : ∏ k, x k (c k) ^ N k = (∏ k, x k (c k) ^ m k) * ∏ k, x k (c k) ^ (N k - m k) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun k _ ↦ ?_
          rw [← pow_add, Nat.add_sub_cancel' (hle m hm k)]
        rw [map_mul, hmon, hpow]
        rw [hy]
        rw [hs]
        ring
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hF, map_sum]
      refine (Finset.sum_congr rfl hterm).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Finset.mul_sum, ← map_sum, sum_compDegs, show aeval z f = 0 from hf, mul_zero]
    have : f = F + (f - F) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hFJ)
  · refine sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)
    · rw [mem_ker_chartEval_iff]
      rw [orbitIdeal, mem_mCoordIdeal_iff] at hf
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_compDegs f, map_sum]
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      have hs := aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ (x k (c k))⁻¹) (flatCone x)
        (weightedHomogeneousComponent_isWeightedHomogeneous m f)
      have hz' : (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) =
          fun p ↦ (x p.1 (c p.1))⁻¹ * flatCone x p := by
        funext p
        rw [div_eq_inv_mul]
        rfl
      rw [hz', hs]
      refine mul_eq_zero_of_right _ ?_
      have h0 := hf m
      rw [aeval_def, Subsingleton.elim (algebraMap ℤ _) (Int.castRingHom _)] at h0 ⊢
      exact h0
    · rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, mem_ker_chartEval_iff]
      simp [div_self (hc k)]

theorem OrbitChartQuot.proof : OrbitChartQuot.Statement := by
  intro ι _ _ n x c hc V hV
  have hsurj := chartEval_surjective x c
  let g : MvPolynomial (Coord n) ℤ →+* chartRing x c ⧸ chartPoint x c V :=
    (Ideal.Quotient.mk _).comp (chartEval x c : MvPolynomial (Coord n) ℤ →+* chartRing x c)
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hsurj
  have hker : RingHom.ker g =
      V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) := by
    ext f
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (chartEval x c f) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, chartPoint,
      Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, ker_chartEval x c hc,
      ← sup_assoc, sup_eq_left.mpr hV]
  exact ⟨(RingHom.quotientKerEquivOfSurjective hg).symm.trans (Ideal.quotEquivOfEq hker)⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCard
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField IsLocalRing

theorem LocalQuotCard.proof : LocalQuotCard.Statement := by
  intro L _ _ O hft _ m _ f hf
  have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing ℤ O
  have hO : Ring.KrullDimLE 1 O := Ring.KrullDimLE.mk₁' fun q hq0 hq ↦
    SubringPrimeMaximal.proof L O q hq hq0
  let R := Localization.AtPrime m
  have : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height m R]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans (Ring.krullDimLE_iff.mp hO)
  have hf' : algebraMap O R f ≠ 0 := by
    intro h
    apply hf
    exact IsLocalization.injective R m.primeCompl_le_nonZeroDivisors (by simpa using h)
  have hspan : Ideal.span {algebraMap O R f} = LinearMap.range (LinearMap.lsmul R R (algebraMap O R f)) := by
    ext z
    simp [Ideal.mem_span_singleton', LinearMap.mem_range, mul_comm]
  have hfin : Module.length R (R ⧸ Ideal.span {algebraMap O R f}) ≠ ⊤ := by
    rw [hspan]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top R hf'
  unfold localQuotLength
  rw [Inter.card_eq_card_residueField_pow_length _ hfin]
  congr 1
  exact Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal m R).toEquiv.symm

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCentred
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem card_quot_span_eq_relIndex {L : Type*} [CommRing L] (R : Subring L) (x : R) :
    Nat.card (R ⧸ Ideal.span {x}) =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).relIndex R.toAddSubgroup := by
  have h : (Ideal.span {x}).toAddSubgroup =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).addSubgroupOf R.toAddSubgroup := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, by simp [mul_comm]⟩
    · rintro ⟨a, ha, hy⟩
      exact ⟨⟨a, ha⟩, Subtype.ext (by simpa [mul_comm] using hy)⟩
  rw [AddSubgroup.relIndex, ← h]
  rfl

theorem relIndex_mulLeft_eq {L : Type*} [CommRing L] [IsDomain L] (A B : Subring L) (hAB : A ≤ B)
    (hfin : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0) (f : L) (hf : f ≠ 0) (hfA : f ∈ A) :
    (A.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex A.toAddSubgroup =
      (B.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex B.toAddSubgroup := by
  have hinj : Function.Injective (AddMonoidHom.mulLeft f) := mul_right_injective₀ hf
  have h1 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup.map (AddMonoidHom.mulLeft f) :=
    AddSubgroup.map_mono hAB
  have h2 : B.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact B.mul_mem (hAB hfA) hy
  have h3 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact A.mul_mem hfA hy
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  have e2 := AddSubgroup.relIndex_mul_relIndex _ _ _ h3 (show A.toAddSubgroup ≤ B.toAddSubgroup from hAB)
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj, ← e2, mul_comm] at e1
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfin) e1).symm

theorem LocalQuotCentred.proof (hN : CentredRingNormal.Statement) (hI : LocalNormalIndex.Statement) :
    LocalQuotCentred.Statement := by
  intro L _ _ O hft hfr m _ f hf g hg
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef
  have hS := hN L O hft m
  have hAI := hI L O hft m
  set P := placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} with hPdef
  have hAP : A.toSubring ≤ P := by
    rw [hS]
    intro x hx
    exact (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  have hfin : A.toSubring.toAddSubgroup.relIndex P.toAddSubgroup ≠ 0 := by
    rw [hS]
    exact hAI
  let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
  have h1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f}) =
      Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A f : A.toSubring)}) := by
    refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (e.commutes f).symm
  have hfL : ((algebraMap O A f : A.toSubring) : L) = (f : L) := rfl
  have hf0 : (f : L) ≠ 0 := fun h ↦ hf (Subtype.ext h)
  rw [h1, card_quot_span_eq_relIndex, card_quot_span_eq_relIndex, hfL, hg]
  exact relIndex_mulLeft_eq _ _ hAP hfin _ hf0 (algebraMap O A f).2

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalLengthPlaces
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem LocalLengthPlaces.proof (hC : LocalQuotCard.Statement) (hF : CentredPlacesFinite.Statement)
    (hE : LocalQuotCentred.Statement) (hP : PlacesRingQuot.Statement) :
    LocalLengthPlaces.Statement := by
  intro L _ _ O hft hfr m _ f hf
  have hfS : (f : L) ∈ placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} :=
    fun w hw ↦ hw.1 f
  have hg : (⟨f, hfS⟩ : placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}) ≠ 0 :=
    fun h ↦ hf (Subtype.ext (by simpa using congrArg Subtype.val h))
  rw [← Real.log_pow, ← Nat.cast_pow, ← hC L O hft hfr m f hf, hE L O hft hfr m f hf ⟨f, hfS⟩ rfl]
  exact hP L _ (hF L O hft hfr m) ⟨f, hfS⟩ hg

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitLocalSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem OrbitLocalSum.proof (hR : OrbitChartRing.Statement) (hM : OrbitChartMax.Statement)
    (hF : OrbitChartResidue.Statement) (hU : OrbitChartMult.Statement)
    (hP : LocalLengthPlaces.Statement) (hC : OrbitCenterChart.Statement)
    (hS : PlaceCentredSum.Statement) (hT : OrbitChartTerm.Statement) :
    OrbitLocalSum.Statement := by
  intro ι _ _ _ n A x s hx hs V hV
  obtain ⟨hVmin, hVrel⟩ := id hV
  choose c hc using hVrel
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hxc : ∀ k, x k (c k) ≠ 0 := fun k h ↦ hc k (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h]))
  obtain ⟨hft, hfr⟩ := hR ι n x c hxc
  have := hM ι n A x s hx hs V hV c hc
  obtain ⟨hf0, hterm⟩ := hT ι n A x s hs c hxc
  let _ : Algebra (ratioField x) (coordField x) :=
    (IntermediateField.inclusion (ratioField_le_coordField x)).toRingHom.toAlgebra
  have hset : {v : FinitePlace (coordField x) | orbitCenter x v = V} =
      {v : FinitePlace (coordField x) | AbsCentredAt (chartRing x c) (chartPoint x c V)
        fun u ↦ v (algebraMap (ratioField x) (coordField x) u)} :=
    Set.ext fun v ↦ hC ι n A x s hx hs V hV c hc v
  have hsum : ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
      (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) =
      ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
        -Real.log (v (algebraMap (ratioField x) (coordField x) (chartEval x c s))) :=
    finsum_mem_congr rfl fun v hv ↦ hterm v fun k hk ↦ hc k (by
      rw [← (show orbitCenter x v = V from hv)]
      exact hk)
  have hdeg := (letI : Module.Free (ratioField x) (coordField x) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (ratioField x) (coordField x))
  rw [hsum, hset, hS (ratioField x) (coordField x) (chartRing x c) (chartPoint x c V),
    hU ι n A x s hx hs V hV c hc, hF ι n A x s hx hs V hV c hc,
    ← hP (ratioField x) (chartRing x c) hft hfr (chartPoint x c V) (chartEval x c s) hf0, ← hdeg]
  push_cast
  ring_nf
  rfl

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

theorem mem_closure_chartRatio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) (z : ratioField x) :
    z ∈ Subfield.closure (Set.range (chartRatio x c)) := by
  set T := Subfield.closure (Set.range (chartRatio x c))
  let T' : Subfield (AlgebraicClosure ℚ) := T.map (ratioField x).val.toRingHom
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    T'.toIntermediateField fun q ↦ by
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem T' q
  have hE : ratioField x ≤ E := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨⟨k, i, j⟩, rfl⟩
    refine ⟨chartRatio x c ⟨k, i⟩ / chartRatio x c ⟨k, j⟩,
      div_mem (Subfield.subset_closure (Set.mem_range_self _))
        (Subfield.subset_closure (Set.mem_range_self _)), ?_⟩
    simp [chartRatio, div_div_div_cancel_right₀ (hc k)]
  obtain ⟨t, ht, hzt⟩ := hE z.2
  have : t = z := Subtype.ext hzt
  exact this ▸ ht

theorem OrbitChartRing.proof : OrbitChartRing.Statement := by
  intro ι _ _ n x c hc
  refine ⟨(Subalgebra.fg_iff_finiteType _).mp
    ⟨(Set.finite_range (chartRatio x c)).toFinset, by simp [chartRing]⟩, ?_⟩
  refine (isLocalization_iff _ _).mpr ⟨fun y ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩
  · refine isUnit_iff_ne_zero.mpr fun h ↦ nonZeroDivisors.coe_ne_zero y ?_
    exact Subtype.ext h
  · have hsub : Subring.closure (Set.range (chartRatio x c)) ≤ (chartRing x c).toSubring :=
      Subring.closure_le.mpr fun _ hp ↦ Algebra.subset_adjoin hp
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subfield.mem_closure_iff.mp (mem_closure_chartRatio x c hc z)
    by_cases hb0 : b = 0
    · refine ⟨(0, 1), ?_⟩
      rw [hb0, div_zero] at hab
      simp [← hab]
    · have hb' : (⟨b, hsub hb⟩ : chartRing x c) ≠ 0 := fun h ↦ hb0 (congrArg Subtype.val h)
      refine ⟨(⟨a, hsub ha⟩, ⟨⟨b, hsub hb⟩, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      change z * b = a
      rw [← hab, div_mul_cancel₀ _ hb0]
  · rw [Subtype.val_injective h]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartTerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem eval₂_mul_block_of_isMultiHomog {R : Type*} [CommRing R] (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (g : ℤ →+* R) (y : Coord n → R)
    (t : ι → R) :
    eval₂ g (fun p ↦ y p * t p.1) s = eval₂ g y s * ∏ k, t k ^ a k := by
  classical
  simp only [eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [mul_assoc]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  change ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
  rw [Finset.prod_pow_eq_pow_sum, hs m hm k]


omit [Fintype ι] in
theorem coe_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : ratioField x) : AlgebraicClosure ℚ)) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by
  have h : (((ratioField x).val.restrictScalars ℤ).comp (chartRing x c).val).comp (chartEval x c) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) :=
    algHom_ext fun p ↦ by simp [chartEval, chartRatio]
  exact DFunLike.congr_fun h f

theorem evalCone_ne_zero_of_notMem_orbitIdeal (x : Cone n (AlgebraicClosure ℚ))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a)
    (hW : s ∉ orbitIdeal x) : evalCone x s ≠ 0 := by
  intro h0
  apply hW
  have hC : ∀ g : ℤ →+* MvPolynomial ι (AlgebraicClosure ℚ),
      eval₂ g (fun p ↦ C (flatCone x p)) s = C (evalCone x s) := fun g ↦ by
    rw [evalCone, eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_def,
    eval₂_mul_block_of_isMultiHomog s a hs _ (fun p ↦ C (flatCone x p)) X, hC, h0, map_zero,
    zero_mul]


omit [Fintype ι] in
theorem coe_evalCone_coordVec (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ) :
    ((evalCone (coordVec x) s : coordField x) : AlgebraicClosure ℚ) = evalCone x s := by
  have h := eval₂_comp_left (algebraMap (coordField x) (AlgebraicClosure ℚ)) (Int.castRingHom _)
    (fun v ↦ coordVec x v.1 v.2) s
  rw [RingHom.ext_int ((algebraMap (coordField x) (AlgebraicClosure ℚ)).comp (Int.castRingHom _))
    (Int.castRingHom _)] at h
  exact h

theorem OrbitChartTerm.proof : OrbitChartTerm.Statement := by
  intro ι _ _ n A x s hs c hxc
  obtain ⟨a, ha, hhom, hW⟩ := hs
  have hfac : evalCone x s =
      ((chartEval x c s : ratioField x) : AlgebraicClosure ℚ) * ∏ k, x k (c k) ^ a k := by
    rw [coe_chartEval, aeval_def, ← eval₂_mul_block_of_isMultiHomog s a hhom _
      (fun p ↦ x p.1 p.2 / x p.1 (c p.1)) (fun k ↦ x k (c k)), evalCone]
    congr 1
    funext p
    exact (div_mul_cancel₀ _ (hxc p.1)).symm
  have hx0 : evalCone x s ≠ 0 := evalCone_ne_zero_of_notMem_orbitIdeal x s a hhom hW
  have hf0 : chartEval x c s ≠ 0 := by
    intro h
    rw [h] at hfac
    simp at hfac
    exact hx0 hfac
  refine ⟨hf0, fun v hv ↦ ?_⟩
  have hsup : ∀ k, ⨆ i, v (coordVec x k i) = v (coordVec x k (c k)) := fun k ↦
    le_antisymm (not_lt.mp fun h ↦ hv k (X_mem_orbitCenter x v k (c k) h))
      (le_ciSup (f := fun i ↦ v (coordVec x k i)) (Finite.bddAbove_range _) (c k))
  have hK : evalCone (coordVec x) s =
      IntermediateField.inclusion (ratioField_le_coordField x) (chartEval x c s) *
        ∏ k, coordVec x k (c k) ^ a k := by
    apply Subtype.ext
    rw [coe_evalCone_coordVec, hfac, MulMemClass.coe_mul, IntermediateField.coe_prod,
      IntermediateField.coe_inclusion]
    simp only [SubmonoidClass.coe_pow]
    rfl
  have hc0 : ∀ k, 0 < v (coordVec x k (c k)) := fun k ↦
    FinitePlace.pos_iff.mpr fun h ↦ hxc k (congrArg Subtype.val h)
  have hv0 : 0 < v (IntermediateField.inclusion (ratioField_le_coordField x) (chartEval x c s)) :=
    FinitePlace.pos_iff.mpr fun h ↦ hf0 (Subtype.ext
      ((IntermediateField.inclusion (ratioField_le_coordField x)).injective
        (h.trans (map_zero _).symm)))
  have ha' : ∀ k, (A.deg k : ℝ) = (a k : ℝ) := fun k ↦ by
    have h := ha k
    rw [HermLine.toGeo_a] at h
    exact_mod_cast h
  rw [hK, map_mul, map_prod, Real.log_mul hv0.ne' (Finset.prod_pos fun k _ ↦ (by
      rw [map_pow]; exact pow_pos (hc0 k) _)).ne',
    Real.log_prod fun k _ ↦ (by rw [map_pow]; exact (pow_pos (hc0 k) _).ne'), finiteTerm]
  simp only [map_pow, Real.log_pow, hsup, ha']
  ring

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitConjSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitConjSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (g : (Coord n → ℂ) → ℝ), BlockNonzero x →
    (∀ (c : ι → ℂ) (z : Coord n → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x) → g (fun p ↦ c p.1 * z p) = g z) →
    (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) *
        ∑ σ : coordField x →+* ℂ, g (fun p ↦ σ (coordVec x p.1 p.2)) =
      (Module.finrank ℚ (coordField x) : ℝ) *
        ∑ᶠ q : projPts (ι := blockIdx n) (orbitIdeal x),
          g (Quot.out q : Geo.mcPts (ι := blockIdx n) (orbitIdeal x))

end GroundTheory.Heights₂.Heights
end
