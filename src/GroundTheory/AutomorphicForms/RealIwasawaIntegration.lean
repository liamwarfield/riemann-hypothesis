module

public import GroundTheory.AutomorphicForms.RealIwasawaSubgroups

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.RealIwasawaUnipotentHaar
namespace GroundTheory.Automorphic

open Matrix Set MeasureTheory Measure
open scoped ComplexOrder NNReal ENNReal

set_option linter.unusedSectionVars false

section Det

theorem det_one_add_of_isNilpotent {m K : Type*} [Fintype m] [DecidableEq m] [Field K]
    {M : Matrix m m K} (hM : IsNilpotent M) : (1 + M).det = 1 := by
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 (isUnit_charpolyRev_of_isNilpotent hM)
  have h0 := eval_charpolyRev (M := M)
  rw [← hc, Polynomial.eval_C] at h0
  have h1 : M.charpolyRev = 1 := by rw [← hc, h0, Polynomial.C_1]
  have h2 := congrArg (Polynomial.eval (-1)) h1
  rw [charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det, map_one] at h2
  rw [← h2]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem det_one_add_linearMap_of_isNilpotent {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] {f : E →ₗ[K] E} (hf : IsNilpotent f) : LinearMap.det (1 + f) = 1 := by
  let b := Module.finBasis K E
  rw [← LinearMap.det_toMatrix b, map_add (f := _), LinearMap.toMatrix_one]
  apply det_one_add_of_isNilpotent
  obtain ⟨k, hk⟩ := hf
  exact ⟨k, by rw [LinearMap.toMatrix_pow, hk, map_zero]⟩

end Det

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

section Translations

def unipotentLeftLinear (w : StrictUpperIndex n → 𝕜) :
    (StrictUpperIndex n → 𝕜) →ₗ[𝕜] (StrictUpperIndex n → 𝕜) where
  toFun v := strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v)
  map_add' v v' := by
    rw [strictUpperMatrix_add, Matrix.mul_add, strictUpperCoords_add]
  map_smul' c v := by
    rw [strictUpperMatrix_smul, Matrix.mul_smul, strictUpperCoords_smul, RingHom.id_apply]

theorem isStrictUpper_mul (v w : StrictUpperIndex n → 𝕜) :
    IsStrictUpper (strictUpperMatrix v * strictUpperMatrix w) :=
  (isStrictUpper_strictUpperMatrix v).mul_right (isStrictUpper_strictUpperMatrix w).isUpperTriangular

theorem unipotentLeftLinear_pow_apply (w : StrictUpperIndex n → 𝕜) (k : ℕ)
    (v : StrictUpperIndex n → 𝕜) :
    (unipotentLeftLinear w ^ k) v = strictUpperCoords (strictUpperMatrix w ^ k * strictUpperMatrix v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    show strictUpperCoords (strictUpperMatrix w ^ k *
      strictUpperMatrix (strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v))) = _
    rw [strictUpperMatrix_strictUpperCoords (isStrictUpper_mul w v), ← Matrix.mul_assoc, ← pow_succ]

theorem restrictScalars_pow_apply (L : (StrictUpperIndex n → 𝕜) →ₗ[𝕜] (StrictUpperIndex n → 𝕜))
    (k : ℕ) (v : StrictUpperIndex n → 𝕜) : ((L.restrictScalars ℝ) ^ k) v = (L ^ k) v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]; rfl

theorem isNilpotent_unipotentLeftLinear (w : StrictUpperIndex n → 𝕜) :
    IsNilpotent ((unipotentLeftLinear w).restrictScalars ℝ) := by
  refine ⟨Fintype.card n, LinearMap.ext fun v => ?_⟩
  rw [restrictScalars_pow_apply, unipotentLeftLinear_pow_apply,
    (isStrictUpper_strictUpperMatrix w).pow_card_eq_zero, Matrix.zero_mul]
  rfl

theorem unipotentOfCoords_mul_eq_left (w v : StrictUpperIndex n → 𝕜) :
    unipotentOfCoords w * unipotentOfCoords v =
      unipotentOfCoords (w + (1 + (unipotentLeftLinear w).restrictScalars ℝ) v) := by
  rw [unipotentOfCoords_mul]
  congr 1
  show w + v + strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v) =
    w + (v + strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v))
  rw [add_assoc]

noncomputable def diagScaleLinear (a : PosDiag (n := n)) :
    (StrictUpperIndex n → 𝕜) →ₗ[ℝ] (StrictUpperIndex n → 𝕜) :=
  LinearMap.pi fun p => ((a.1 p.1.1 / a.1 p.1.2) • LinearMap.id).comp (LinearMap.proj p)

theorem diagScaleLinear_apply (a : PosDiag (n := n)) (v : StrictUpperIndex n → 𝕜) :
    diagScaleLinear a v = fun p => ((a.1 p.1.1 / a.1 p.1.2 : ℝ) : 𝕜) * v p := by
  funext p
  simp [diagScaleLinear, RCLike.real_smul_eq_coe_mul]

theorem det_diagScaleLinear (a : PosDiag (n := n)) :
    LinearMap.det (diagScaleLinear (𝕜 := 𝕜) a) = (iwasawaDelta (diagPosOf a : GL n 𝕜) : ℝ) := by
  rw [diagScaleLinear, LinearMap.det_pi, iwasawaDelta_diagPosOf]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]

end Translations

section Topology

instance : LocallyCompactSpace (upperUnipotentSubgroup n 𝕜) :=
  (unipotentCoordsHomeomorph (𝕜 := 𝕜) (n := n)).symm.isOpenEmbedding.locallyCompactSpace

instance : SecondCountableTopology (upperUnipotentSubgroup n 𝕜) :=
  (unipotentCoordsHomeomorph (𝕜 := 𝕜) (n := n)).symm.isEmbedding.secondCountableTopology

theorem isOpen_posDiag : IsOpen {a : n → ℝ | ∀ i, 0 < a i} := by
  rw [setOf_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

instance : LocallyCompactSpace (PosDiag (n := n)) :=
  isOpen_posDiag.locallyCompactSpace

instance : LocallyCompactSpace (diagPosSubgroup n 𝕜) :=
  (diagPosHomeomorph (𝕜 := 𝕜) (n := n)).symm.isOpenEmbedding.locallyCompactSpace

instance : SecondCountableTopology (diagPosSubgroup n 𝕜) :=
  (diagPosHomeomorph (𝕜 := 𝕜) (n := n)).symm.isEmbedding.secondCountableTopology

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

instance : LocallyCompactSpace (upperPosSubgroup n 𝕜) :=
  (diagUnipotentHomeomorph (𝕜 := 𝕜) (n := n)).symm.isOpenEmbedding.locallyCompactSpace

instance : SecondCountableTopology (upperPosSubgroup n 𝕜) :=
  (diagUnipotentHomeomorph (𝕜 := 𝕜) (n := n)).symm.isEmbedding.secondCountableTopology

end Topology

section Haar

variable [MeasurableSpace (GL n 𝕜)] [BorelSpace (GL n 𝕜)]

noncomputable def unipotentLebesgue : Measure (upperUnipotentSubgroup n 𝕜) :=
  Measure.map unipotentCoordsHomeomorph (Measure.addHaar : Measure (StrictUpperIndex n → 𝕜))

theorem map_affine_addHaar_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (w : E) (L : E →ₗ[ℝ] E) (hL : LinearMap.det L = 1) :
    Measure.map (fun v => w + L v) μ = μ := by
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have e : (fun v => w + L v) = (fun v => w + v) ∘ L := rfl
  rw [e, ← Measure.map_map (measurable_const_add w) hLc.measurable,
    map_linearMap_addHaar_eq_smul_addHaar μ (by rw [hL]; exact one_ne_zero), hL, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul, map_add_left_eq_self]

theorem unipotentLebesgue_map_mul_left (u : upperUnipotentSubgroup n 𝕜) :
    Measure.map (u * ·) (unipotentLebesgue (𝕜 := 𝕜) (n := n)) = unipotentLebesgue := by
  set w := unipotentCoordsHomeomorph.symm u
  have hu : u = unipotentCoordsHomeomorph w := (unipotentCoordsHomeomorph.apply_symm_apply u).symm
  have e : (u * ·) ∘ unipotentCoordsHomeomorph = unipotentCoordsHomeomorph ∘
      (fun v => w + (1 + (unipotentLeftLinear w).restrictScalars ℝ) v) := by
    funext v
    apply Subtype.ext
    simp only [Function.comp_apply, Subgroup.coe_mul, hu, coe_unipotentCoordsHomeomorph]
    exact unipotentOfCoords_mul_eq_left w v
  have hT : Measurable (fun v : StrictUpperIndex n → 𝕜 =>
      w + (1 + (unipotentLeftLinear w).restrictScalars ℝ) v) :=
    (continuous_const.add (LinearMap.continuous_of_finiteDimensional _)).measurable
  rw [unipotentLebesgue, Measure.map_map (measurable_const_mul u)
    unipotentCoordsHomeomorph.measurable, e, ← Measure.map_map unipotentCoordsHomeomorph.measurable hT,
    map_affine_addHaar_eq _ w _ (det_one_add_linearMap_of_isNilpotent
      (isNilpotent_unipotentLeftLinear w))]

instance isHaarMeasure_unipotentLebesgue : (unipotentLebesgue (𝕜 := 𝕜) (n := n)).IsHaarMeasure where
  map_mul_left_eq_self u := unipotentLebesgue_map_mul_left u
  lt_top_of_isCompact := by
    have := IsFiniteMeasureOnCompacts.map (Measure.addHaar : Measure (StrictUpperIndex n → 𝕜))
      (unipotentCoordsHomeomorph (𝕜 := 𝕜) (n := n))
    exact this.lt_top_of_isCompact
  open_pos U hU hne := by
    rw [unipotentLebesgue, Measure.map_apply unipotentCoordsHomeomorph.measurable hU.measurableSet]
    exact (hU.preimage unipotentCoordsHomeomorph.continuous).measure_ne_zero _
      (hne.preimage unipotentCoordsHomeomorph.surjective)

theorem exists_eq_smul_unipotentLebesgue (μ : Measure (upperUnipotentSubgroup n 𝕜))
    [μ.IsHaarMeasure] : ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • unipotentLebesgue := by
  refine ⟨haarScalarFactor μ unipotentLebesgue, ?_, isMulLeftInvariant_eq_smul μ _⟩
  intro h0
  have h := isMulLeftInvariant_eq_smul μ (unipotentLebesgue (𝕜 := 𝕜) (n := n))
  rw [h0, zero_smul] at h
  exact (IsHaarMeasure.toIsOpenPosMeasure (μ := μ)).open_pos univ isOpen_univ univ_nonempty
    (by rw [h]; rfl)

def diagConj (a : diagPosSubgroup n 𝕜) (u : upperUnipotentSubgroup n 𝕜) :
    upperUnipotentSubgroup n 𝕜 :=
  ⟨(a : GL n 𝕜) * u * (a : GL n 𝕜)⁻¹, by
    obtain ⟨x, rfl⟩ := diagPosHomeomorph.surjective a
    obtain ⟨v, rfl⟩ := unipotentCoordsHomeomorph.surjective u
    rw [coe_diagPosHomeomorph, coe_unipotentCoordsHomeomorph, conj_unipotentOfCoords]
    exact unipotentOfCoords_mem _⟩

@[simp] theorem coe_diagConj (a : diagPosSubgroup n 𝕜) (u : upperUnipotentSubgroup n 𝕜) :
    ((diagConj a u : upperUnipotentSubgroup n 𝕜) : GL n 𝕜) = (a : GL n 𝕜) * u * (a : GL n 𝕜)⁻¹ :=
  rfl

theorem continuous_diagConj (a : diagPosSubgroup n 𝕜) :
    Continuous (diagConj a) :=
  Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

theorem unipotentLebesgue_map_diagConj (a : diagPosSubgroup n 𝕜) :
    Measure.map (diagConj a) (unipotentLebesgue (𝕜 := 𝕜) (n := n)) =
      ((iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞))⁻¹ • unipotentLebesgue := by
  obtain ⟨x, rfl⟩ := diagPosHomeomorph.surjective a
  have e : diagConj (diagPosHomeomorph x) ∘ unipotentCoordsHomeomorph =
      unipotentCoordsHomeomorph ∘ diagScaleLinear (𝕜 := 𝕜) x := by
    funext v
    apply Subtype.ext
    simp only [Function.comp_apply, coe_diagConj, coe_diagPosHomeomorph,
      coe_unipotentCoordsHomeomorph, diagScaleLinear_apply]
    exact conj_unipotentOfCoords x v
  have hδ : (iwasawaDelta (diagPosOf x : GL n 𝕜) : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.2 (iwasawaDelta_ne_zero (diagPosSubgroup_le_upperPosSubgroup (diagPosOf_mem x)))
  rw [unipotentLebesgue, Measure.map_map (continuous_diagConj _).measurable
    unipotentCoordsHomeomorph.measurable, e, ← Measure.map_map unipotentCoordsHomeomorph.measurable
    (LinearMap.continuous_of_finiteDimensional _).measurable,
    map_linearMap_addHaar_eq_smul_addHaar _ (by rw [det_diagScaleLinear]; exact hδ),
    Measure.map_smul _ unipotentCoordsHomeomorph.measurable.aemeasurable,
    det_diagScaleLinear, coe_diagPosHomeomorph]
  congr 1
  rw [abs_of_pos (inv_pos.2 (lt_of_le_of_ne (NNReal.coe_nonneg _) hδ.symm)), ← NNReal.coe_inv,
    ENNReal.ofReal_coe_nnreal, ENNReal.coe_inv (NNReal.coe_ne_zero.1 hδ)]

theorem map_diagConj_haar (μ : Measure (upperUnipotentSubgroup n 𝕜)) [μ.IsHaarMeasure]
    (a : diagPosSubgroup n 𝕜) :
    Measure.map (diagConj a) μ = ((iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞))⁻¹ • μ := by
  obtain ⟨c, -, rfl⟩ := exists_eq_smul_unipotentLebesgue μ
  rw [Measure.map_smul _ (continuous_diagConj a).measurable.aemeasurable,
    unipotentLebesgue_map_diagConj, smul_comm]

end Haar

end GroundTheory.Automorphic
end

namespace GroundTheory.Automorphic

open Matrix Set MeasureTheory Measure
open scoped ComplexOrder NNReal ENNReal

set_option linter.unusedSectionVars false

section Unimodular

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]

theorem isInvInvariant_of_isMulRightInvariant (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := by
    have := isMulLeftInvariant_eq_smul μ.inv μ
    rwa [ENNReal.smul_def] at this
  have μeq : μ = c ^ 2 • μ := by
    conv_lhs => rw [← Measure.inv_inv μ]
    rw [hc, Measure.inv_def (c • μ), Measure.map_smul, ← Measure.inv_def, hc, smul_smul, pow_two]
    exact measurable_inv.aemeasurable
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h1 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h2 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h1
  have h3 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h2
  rw [hc, h3, one_smul]

theorem isMulRightInvariant_of_compactSpace [CompactSpace G] (μ : Measure G) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  constructor
  intro g
  have hfin : IsFiniteMeasureOnCompacts (map (· * g) μ) :=
    IsFiniteMeasureOnCompacts.map μ (Homeomorph.mulRight g)
  have h := isMulLeftInvariant_eq_smul (map (· * g) μ) μ
  set c := haarScalarFactor (map (· * g) μ) μ
  have hu := congrArg (fun ν : Measure G => ν univ) h
  simp only [map_apply (measurable_mul_const g) MeasurableSet.univ, preimage_univ,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hu
  have hpos : μ univ ≠ 0 := IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty
  have htop : μ univ ≠ ∞ := isCompact_univ.measure_lt_top.ne
  have hc : (c : ℝ≥0∞) = 1 := by
    have := (ENNReal.mul_left_inj hpos htop).1 (hu.symm.trans (one_mul _).symm)
    exact this
  rw [h, ENNReal.smul_def, hc, one_smul]

end Unimodular

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

section Abelian

variable [MeasurableSpace (GL n 𝕜)] [BorelSpace (GL n 𝕜)]

end Abelian

section Borel

variable [WellFoundedLT n] [LocallyFiniteOrderBot n] [MeasurableSpace (GL n 𝕜)]
  [BorelSpace (GL n 𝕜)]

theorem measurable_diagUnipotentMul :
    Measurable (diagUnipotentMul : diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜 →
      upperPosSubgroup n 𝕜) :=
  (diagUnipotentHomeomorph (𝕜 := 𝕜) (n := n)).continuous.measurable

theorem continuous_diagConj_inv_left (u' : upperUnipotentSubgroup n 𝕜) :
    Continuous fun a : diagPosSubgroup n 𝕜 => diagConj a⁻¹ u' := by
  refine continuous_induced_rng.2 ?_
  have h1 : Continuous fun a : diagPosSubgroup n 𝕜 => ((a⁻¹ : diagPosSubgroup n 𝕜) : GL n 𝕜) :=
    continuous_subtype_val.comp continuous_inv
  exact (h1.mul continuous_const).mul h1.inv

theorem isMulLeftInvariant_map_diagUnipotentMul (μA : Measure (diagPosSubgroup n 𝕜))
    [μA.IsHaarMeasure] (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure] :
    (map diagUnipotentMul (μA.prod μN)).IsMulLeftInvariant := by
  constructor
  intro b
  obtain ⟨⟨a', u'⟩, rfl⟩ := diagUnipotentHomeomorph.surjective b
  let S : diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜 →
      diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜 :=
    fun p => (a' * p.1, diagConj p.1⁻¹ u' * p.2)
  have hS : Measurable S :=
    ((continuous_const.mul continuous_fst).prodMk
      (((continuous_diagConj_inv_left u').comp continuous_fst).mul continuous_snd)).measurable
  have e : (fun x => diagUnipotentHomeomorph (a', u') * x) ∘ diagUnipotentMul =
      diagUnipotentMul ∘ S := by
    funext p
    apply Subtype.ext
    simp only [Function.comp_apply, diagUnipotentHomeomorph_apply, Subgroup.coe_mul,
      coe_diagUnipotentMul, coe_diagConj, Subgroup.coe_inv, S]
    group
  have hP : map S (μA.prod μN) = μA.prod μN := by
    ext s hs
    rw [map_apply hS hs, prod_apply (hS hs), prod_apply hs]
    have e2 : ∀ a, Prod.mk a ⁻¹' (S ⁻¹' s) =
        (fun u => diagConj a⁻¹ u' * u) ⁻¹' (Prod.mk (a' * a) ⁻¹' s) := fun a => rfl
    simp_rw [e2, measure_preimage_mul]
    exact lintegral_mul_left_eq_self (fun a => μN (Prod.mk a ⁻¹' s)) a'
  rw [map_map (measurable_const_mul _) measurable_diagUnipotentMul, e,
    ← map_map measurable_diagUnipotentMul hS, hP]

theorem exists_map_diagUnipotentMul_eq_smul (μA : Measure (diagPosSubgroup n 𝕜))
    [μA.IsHaarMeasure] (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n 𝕜)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ map diagUnipotentMul (μA.prod μN) = c • μB := by
  haveI := isMulLeftInvariant_map_diagUnipotentMul μA μN
  haveI : IsFiniteMeasureOnCompacts (map diagUnipotentMul (μA.prod μN)) :=
    IsFiniteMeasureOnCompacts.map (μA.prod μN) diagUnipotentHomeomorph
  refine ⟨haarScalarFactor (map diagUnipotentMul (μA.prod μN)) μB, ?_,
    isMulLeftInvariant_eq_smul _ _⟩
  intro h0
  have h := isMulLeftInvariant_eq_smul (map diagUnipotentMul (μA.prod μN)) μB
  rw [h0, zero_smul] at h
  have hu := congrArg (fun ν : Measure (upperPosSubgroup n 𝕜) => ν univ) h
  simp only [map_apply measurable_diagUnipotentMul MeasurableSet.univ, preimage_univ,
    ← univ_prod_univ, prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero] at hu
  rcases hu with hu | hu
  · exact IsOpenPosMeasure.open_pos (μ := μA) univ isOpen_univ univ_nonempty hu
  · exact IsOpenPosMeasure.open_pos (μ := μN) univ isOpen_univ univ_nonempty hu

theorem lintegral_upperPos_eq (μA : Measure (diagPosSubgroup n 𝕜)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n 𝕜)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : upperPosSubgroup n 𝕜 → ℝ≥0∞, Measurable f →
      ∫⁻ b, f b ∂μB = c * ∫⁻ a, ∫⁻ u, f (diagUnipotentMul (a, u)) ∂μN ∂μA := by
  obtain ⟨c, hc, h⟩ := exists_map_diagUnipotentMul_eq_smul μA μN μB
  refine ⟨c⁻¹, inv_ne_zero hc, fun f hf => ?_⟩
  have hB : μB = c⁻¹ • map diagUnipotentMul (μA.prod μN) := by
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hB, lintegral_smul_measure, lintegral_map hf measurable_diagUnipotentMul,
    lintegral_prod (fun p => f (diagUnipotentMul p))
      (hf.comp measurable_diagUnipotentMul).aemeasurable, ENNReal.smul_def,
    smul_eq_mul]

end Borel

section KAN

instance secondCountableTopology_matrix_rclike : SecondCountableTopology (Matrix n n 𝕜) :=
  inferInstanceAs (SecondCountableTopology (n → n → 𝕜))

instance locallyCompactSpace_matrix_rclike : LocallyCompactSpace (Matrix n n 𝕜) :=
  inferInstanceAs (LocallyCompactSpace (n → n → 𝕜))

instance secondCountableTopology_unitaryGroup : SecondCountableTopology (unitaryGroup n 𝕜) :=
  TopologicalSpace.Subtype.secondCountableTopology _

theorem continuous_unitary_toUnits :
    Continuous (fun k : unitaryGroup n 𝕜 => Unitary.toUnits k) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩

variable [WellFoundedLT n] [LocallyFiniteOrderBot n] [MeasurableSpace (GL n 𝕜)]
  [BorelSpace (GL n 𝕜)]

theorem lintegral_ANK_of_KB {μG : Measure (GL n 𝕜)} [μG.IsInvInvariant]
    [MeasurableSpace (unitaryGroup n 𝕜)] [BorelSpace (unitaryGroup n 𝕜)]
    {μK : Measure (unitaryGroup n 𝕜)} [SFinite μK] [μK.IsInvInvariant]
    (μA : Measure (diagPosSubgroup n 𝕜)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n 𝕜)) [μN.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n 𝕜)) [μB.IsHaarMeasure]
    (hKB : ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n 𝕜 → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n 𝕜 → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA := by
  obtain ⟨c, hc, h⟩ := hKB
  obtain ⟨c1, hc1, h1⟩ := lintegral_upperPos_eq μA μN μB
  refine ⟨c * c1, mul_ne_zero hc hc1, fun f hf => ?_⟩
  have hmF : Measurable fun p : upperPosSubgroup n 𝕜 × unitaryGroup n 𝕜 =>
      f ((p.1 : GL n 𝕜) * Unitary.toUnits p.2) :=
    hf.comp ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_unitary_toUnits.comp continuous_snd)).measurable
  have hmF' : Measurable fun p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜 =>
      f ((p.2 : GL n 𝕜) * (Unitary.toUnits p.1)⁻¹) :=
    hf.comp ((continuous_subtype_val.comp continuous_snd).mul
      (continuous_unitary_toUnits.comp continuous_fst).inv).measurable
  rw [← lintegral_inv_eq_self (μ := μG) f, h (fun g => f g⁻¹) (hf.comp measurable_inv)]
  have step2 : ∀ k : unitaryGroup n 𝕜,
      ∫⁻ b, f ((Unitary.toUnits k * (b : GL n 𝕜))⁻¹) ∂μB.inv =
        ∫⁻ b, f ((b : GL n 𝕜) * (Unitary.toUnits k)⁻¹) ∂μB := by
    intro k
    rw [Measure.inv_def, lintegral_map _ measurable_inv]
    · simp only [Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv]
    · exact hf.comp (measurable_inv.comp ((measurable_const_mul _).comp measurable_subtype_coe))
  rw [lintegral_congr step2, lintegral_lintegral_swap hmF'.aemeasurable]
  have step3 : ∀ b : upperPosSubgroup n 𝕜,
      ∫⁻ k, f ((b : GL n 𝕜) * (Unitary.toUnits k)⁻¹) ∂μK =
        ∫⁻ k, f ((b : GL n 𝕜) * Unitary.toUnits k) ∂μK := by
    intro b
    have := lintegral_inv_eq_self (μ := μK) (fun k => f ((b : GL n 𝕜) * Unitary.toUnits k))
    simpa only [map_inv] using this
  rw [lintegral_congr step3, h1 _ hmF.lintegral_prod_right']
  simp only [coe_diagUnipotentMul]
  rw [ENNReal.coe_mul, mul_assoc]

end KAN

section Real

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem exists_eq_smul_haarGLReal (μG : Measure (GL n ℝ)) [μG.IsHaarMeasure] :
    ∃ s : ℝ≥0, s ≠ 0 ∧ μG = s • haarGLReal (Measure.addHaar : Measure (Matrix n n ℝ)) :=
  ⟨_, (haarScalarFactor_pos_of_isHaarMeasure _ _).ne', isMulLeftInvariant_eq_smul _ _⟩

theorem lintegral_GLReal_ANK (μG : Measure (GL n ℝ)) [μG.IsHaarMeasure]
    (μK : Measure (unitaryGroup n ℝ)) [μK.IsHaarMeasure]
    (μA : Measure (diagPosSubgroup n ℝ)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n ℝ)) [μN.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA := by
  obtain ⟨s, hs, hG⟩ := exists_eq_smul_haarGLReal μG
  haveI : μG.IsMulRightInvariant := by rw [hG]; infer_instance
  haveI := isInvInvariant_of_isMulRightInvariant μG
  haveI := isMulRightInvariant_of_compactSpace μK
  haveI := isInvInvariant_of_isMulRightInvariant μK
  let μB : Measure (upperPosSubgroup n ℝ) := Measure.haar
  obtain ⟨c, hc, h⟩ := lintegral_haarGLReal_iwasawa
    (Measure.addHaar : Measure (Matrix n n ℝ)) μK μB
  refine lintegral_ANK_of_KB μA μN μB ⟨s * c, mul_ne_zero hs hc, fun f hf => ?_⟩
  rw [hG, lintegral_smul_measure, h f hf, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, mul_assoc]

end Real

section Complex

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem exists_eq_smul_haarGLComplex (μG : Measure (GL n ℂ)) [μG.IsHaarMeasure] :
    ∃ s : ℝ≥0, s ≠ 0 ∧ μG = s • haarGLComplex (Measure.addHaar : Measure (Matrix n n ℂ)) :=
  ⟨_, (haarScalarFactor_pos_of_isHaarMeasure _ _).ne', isMulLeftInvariant_eq_smul _ _⟩

theorem lintegral_GLComplex_ANK (μG : Measure (GL n ℂ)) [μG.IsHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μA : Measure (diagPosSubgroup n ℂ)) [μA.IsHaarMeasure]
    (μN : Measure (upperUnipotentSubgroup n ℂ)) [μN.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA := by
  obtain ⟨s, hs, hG⟩ := exists_eq_smul_haarGLComplex μG
  haveI : μG.IsMulRightInvariant := by rw [hG]; infer_instance
  haveI := isInvInvariant_of_isMulRightInvariant μG
  haveI := isMulRightInvariant_of_compactSpace μK
  haveI := isInvInvariant_of_isMulRightInvariant μK
  let μB : Measure (upperPosSubgroup n ℂ) := Measure.haar
  obtain ⟨c, hc, h⟩ := lintegral_haarGLComplex_iwasawa
    (Measure.addHaar : Measure (Matrix n n ℂ)) μK μB
  refine lintegral_ANK_of_KB μA μN μB ⟨s * c, mul_ne_zero hs hc, fun f hf => ?_⟩
  rw [hG, lintegral_smul_measure, h f hf, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, mul_assoc]

end Complex

end GroundTheory.Automorphic
