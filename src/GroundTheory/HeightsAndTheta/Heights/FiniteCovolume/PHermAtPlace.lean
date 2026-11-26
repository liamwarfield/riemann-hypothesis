module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem HermAtPlace.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    HermAtPlace.Statement h v := by
  intro w x y
  rw [sesq_eq_sum h.toSesq v x y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, embedding_conj, dotProduct, mulVec, gramAt, vecAt, Pi.star_apply,
    Matrix.map_apply, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Places

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GramAtData.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    GramAtData.Statement h v := by
  intro w
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [gramAt, conjTranspose_apply, map_apply, Automorphic.gram_apply]
    change starRingEnd ℂ (w.embedding (h.toSesq (v j) (v i))) = w.embedding (h.toSesq (v i) (v j))
    rw [← embedding_conj (F := F) w.embedding]
    congr 1
    exact h.isSymm.eq (v j) (v i)
  · simp only [gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Complement

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def IsHyperbolicPair (h : HermitianForm F E W) (v w : W) : Prop :=
  h.toSesq v v = 0 ∧ h.toSesq w w = 0 ∧ h.toSesq v w = 1

def hypComplement (h : HermitianForm F E W) (v w : W) : Submodule E W :=
  LinearMap.ker (h.toSesq v) ⊓ LinearMap.ker (h.toSesq w)

theorem mem_hypComplement {h : HermitianForm F E W} {v w x : W} :
    x ∈ hypComplement h v w ↔ h.toSesq v x = 0 ∧ h.toSesq w x = 0 := by
  simp [hypComplement]

def ComplementForm.Statement (h : HermitianForm F E W) : Prop :=
  ∀ v w : W, IsHyperbolicPair h v w →
    ∃ h' : HermitianForm F E (hypComplement h v w), ∀ x y, h'.toSesq x y = h.toSesq x y

end Complement

namespace GaussianPlane

end GaussianPlane

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    vecAt v x₀ w}
  one_mem' w := by simp
  mul_mem' {a b} ha hb w := by
    simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hb w, ha w]
  inv_mem' {a} ha w := by
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w
        = (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
            (((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) := by rw [ha w]
      _ = vecAt v x₀ w := by rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]

omit [NumberField E] in
theorem mem_vecFixGroup {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {g : archUnitary h v} : g ∈ vecFixGroup h v x₀ ↔
      ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w :=
  Iff.rfl


omit [NumberField E] in
theorem isClosed_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (vecFixGroup h v x₀ : Set (archUnitary h v)) := by
  have : (vecFixGroup h v x₀ : Set (archUnitary h v)) = ⋂ w, {g : archUnitary h v |
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w} := by
    ext g
    simp [mem_vecFixGroup]
  rw [this]
  refine isClosed_iInter fun w => isClosed_eq ?_ continuous_const
  exact (Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
    continuous_const

instance locallyCompactSpace_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (vecFixGroup h v x₀) :=
  (isClosed_vecFixGroup h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance secondCountableTopology_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    SecondCountableTopology (vecFixGroup h v x₀) :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance sigmaFinite_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (ν : Measure (vecFixGroup h v x₀)) [ν.IsHaarMeasure] : SigmaFinite ν :=
  inferInstance

instance measurableMul_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    MeasurableMul (vecFixGroup h v x₀) :=
  inferInstance

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

theorem tsum_orbit_eq_tsum_quotient {G X : Type*} [Group G] [MulAction G X] (b : X) (o : Set X)
    (ho : MulAction.orbit G b = o) (K : Subgroup G) (hK : MulAction.stabilizer G b = K)
    (f : X → ℝ≥0∞) : ∑' p : o, f p = ∑' q : G ⧸ K, f ((Quotient.out q : G) • b) := by
  subst ho hK
  rw [← (MulAction.orbitEquivQuotientStabilizer G b).symm.tsum_eq]
  refine tsum_congr fun q => ?_
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rw [MulAction.orbitEquivQuotientStabilizer_symm_apply]

section Action

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

@[reducible] def archMulAction (h : HermitianForm F E W) (v : Basis ι E W) :
    MulAction (archUnitary h v) (InfinitePlace E → ι → ℂ) where
  smul g y w := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w
  one_smul y := by
    funext w
    change (((1 : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w = y w
    simp
  mul_smul g k y := by
    funext w
    change (((g * k : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w)
    simp [Matrix.mulVec_mulVec]

attribute [local instance] archMulAction

theorem archSmul_apply {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    (g • y) w = ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w := rfl

theorem continuous_len_inv_smul {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (g⁻¹ • y) := by
  have hw : ∀ w, Continuous fun g : archUnitary h v => (g⁻¹ • y) w := fun w =>
    (Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const
  unfold Majorant.len
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => ?_)
  exact Complex.continuous_re.comp
    (((continuous_star.comp (hw w))).dotProduct (continuous_const.matrix_mulVec (hw w)))

def belowIndicator {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) (t : ℝ) : archUnitary h v → ℝ≥0∞ :=
  {g | M.len (g⁻¹ • y) < t}.indicator 1

theorem measurableSet_below {h : HermitianForm F E W} {v : Basis ι E W}
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) (t : ℝ) :
    MeasurableSet {g : archUnitary h v | M.len (g⁻¹ • y) < t} :=
  (isOpen_lt (continuous_len_inv_smul M y) continuous_const).measurableSet

theorem measurable_belowIndicator {h : HermitianForm F E W} {v : Basis ι E W}
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) (t : ℝ) :
    Measurable (belowIndicator M y t) :=
  measurable_one.indicator (measurableSet_below M y t)


omit [Fintype ι] [DecidableEq ι] in
theorem vecAt_injective (v : Basis ι E W) : Function.Injective (vecAt v) := by
  intro x y hxy
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply v.repr.injective
  ext i
  exact w.embedding.injective (congrFun (congrFun hxy w) i)

variable [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem archEmbed_smul_vecAt (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (x : W) : archEmbed h v γ • vecAt v x = vecAt v (γ • x) := by
  funext w i
  rw [archSmul_apply]
  have hm : (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
    rw [← unitaryGroupEquivMatrix_apply]
    rfl
  rw [hm]
  change _ = w.embedding (v.repr (((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x) i)
  rw [← LinearMap.toMatrix_mulVec_repr v v, RingHom.map_mulVec]
  rfl

theorem stabilizer_vecAt (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W)
    (y : W) : MulAction.stabilizer (archLatticeGroup h v La) (vecAt v y) =
      (vecStabGroup h v La y).subgroupOf (archLatticeGroup h v La) := by
  ext ⟨γ, hγ⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.1 hγ
  change archEmbed h v δ • vecAt v y = vecAt v y ↔ _
  constructor
  · intro he
    rw [archEmbed_smul_vecAt] at he
    exact Subgroup.mem_map.2 ⟨⟨δ, hδ⟩, MulAction.mem_stabilizer_iff.2 (vecAt_injective v he), rfl⟩
  · rintro ⟨ε, hε, he⟩
    have he' : archEmbed h v (ε : h.unitaryGroup) = archEmbed h v δ := he
    rw [← he', archEmbed_smul_vecAt]
    exact congrArg (vecAt v) (MulAction.mem_stabilizer_iff.1 hε)

theorem ScalingLaw.proof (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : UnfoldingIntegral.Statement h v) (h₂ : VectorOrbitsFinite.Statement h)
    (h₃ : UnfoldOrbit.Statement (archUnitary h v))
    (h₄ : DiscreteFundamentalDomain.Statement (archUnitary h v))
    (h₅ : ArchLatticeDiscrete.Statement h v) : ScalingLaw.Statement h v := by
  classical
  intro M μ _ D La VV hLa hVV hiso hstab hC
  set Γ := archLatticeGroup h v La with hΓ
  have : DiscreteTopology Γ := h₅ La hLa.isLattice
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hQc : ∀ K : Subgroup Γ, Countable (Γ ⧸ K) := fun K => QuotientGroup.mk_surjective.countable
  obtain ⟨FD, -, hFD⟩ := h₄ μ Γ inferInstance

  have key : ∀ y ∈ VV, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t : ℝ, 0 < t →
      ∫⁻ g in FD, ∑' q : Γ ⧸ (vecStabGroup h v La y).subgroupOf Γ,
        belowIndicator M (vecAt v y) t (((Quotient.out q : Γ) : archUnitary h v)⁻¹ * g) ∂μ =
        C * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1))) := by
    intro y hy
    obtain ⟨FD₀, hFD₀, C, -, hCtop, hCt⟩ :=
      h₁ M μ D La y hLa (hVV hy) (hiso y hy).1 (hiso y hy).2
    refine ⟨C, hCtop, fun t ht => ?_⟩
    have hle : vecStabGroup h v La y ≤ Γ := by
      rintro _ ⟨ε, -, rfl⟩
      exact Subgroup.mem_map.2 ⟨ε.1, ε.2, rfl⟩
    have hinv : ∀ γ ∈ vecStabGroup h v La y, ∀ g,
        belowIndicator M (vecAt v y) t (γ * g) = belowIndicator M (vecAt v y) t g := by
      intro γ hγ g
      obtain ⟨ε, hε, rfl⟩ := Subgroup.mem_map.1 hγ
      have hb : ((archEmbed h v).comp (latticeStab h La).subtype ε) • vecAt v y = vecAt v y := by
        change archEmbed h v (ε : h.unitaryGroup) • vecAt v y = vecAt v y
        rw [archEmbed_smul_vecAt]
        exact congrArg (vecAt v) (MulAction.mem_stabilizer_iff.1 hε)
      have hb' := (inv_smul_eq_iff.2 hb.symm).symm
      simp only [belowIndicator, Set.indicator_apply, Set.mem_setOf_eq, _root_.mul_inv_rev, mul_smul,
        ← hb', Pi.one_apply]
    rw [h₃ μ Γ _ hle FD FD₀ hFD hFD₀ _ (measurable_belowIndicator M (vecAt v y) t) hinv,
      belowIndicator, lintegral_indicator_one (measurableSet_below M _ t),
      Measure.restrict_apply (measurableSet_below M _ t), Set.inter_comm]
    exact hCt t ht
  choose! Cf hCf hCeq using key

  obtain ⟨S, hSV, hScov⟩ := h₂ D La VV hLa hVV hiso hstab hC
  let T : Finset (Set (InfinitePlace E → ι → ℂ)) :=
    S.image fun y => MulAction.orbit Γ (vecAt v y)
  have hT : ∀ o ∈ T, ∃ y, y ∈ S ∧ MulAction.orbit Γ (vecAt v y) = o := fun o ho => by
    obtain ⟨y, hy, e⟩ := Finset.mem_image.1 ho
    exact ⟨y, hy, e⟩
  choose! Y hYS hYo using hT
  have hP : vecAt v '' VV = ⋃ o ∈ (T : Set (Set (InfinitePlace E → ι → ℂ))), o := by
    ext p
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hyS, γ, hγ, rfl⟩ := hScov x hx
      refine ⟨MulAction.orbit Γ (vecAt v y), Finset.mem_image.2 ⟨y, hyS, rfl⟩, ?_⟩
      rw [← archEmbed_smul_vecAt]
      exact ⟨⟨archEmbed h v γ, Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩⟩, rfl⟩
    · rintro ⟨o, ho, hp⟩
      rw [← hYo o ho] at hp
      obtain ⟨⟨γ', hγ'⟩, rfl⟩ := hp
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
      exact ⟨γ • Y o, hstab γ hγ _ (hSV (hYS o ho)), (archEmbed_smul_vecAt h v γ (Y o)).symm⟩
  have hdisj : (T : Set (Set (InfinitePlace E → ι → ℂ))).PairwiseDisjoint fun o => o := by
    intro o₁ h₁' o₂ h₂' hne
    refine Set.disjoint_left.2 fun p hp1 hp2 => hne ?_
    rw [← hYo o₁ h₁'] at hp1 ⊢
    rw [← hYo o₂ h₂'] at hp2 ⊢
    exact (MulAction.orbit_eq_iff.2 hp1).symm.trans (MulAction.orbit_eq_iff.2 hp2)

  have hcount : ∀ g t, countBelow M VV g t = ∑ o ∈ T,
      ∑' q : Γ ⧸ (vecStabGroup h v La (Y o)).subgroupOf Γ,
        belowIndicator M (vecAt v (Y o)) t (((Quotient.out q : Γ) : archUnitary h v)⁻¹ * g) := by
    intro g t
    have hPA : vecAt v '' {x ∈ VV | M.len (invApply g (vecAt v x)) < t} =
        vecAt v '' VV ∩ {p | M.len (g⁻¹ • p) < t} := by
      ext p
      constructor
      · rintro ⟨x, ⟨hx, hxt⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hxt⟩
      · rintro ⟨⟨x, hx, rfl⟩, hxt⟩
        exact ⟨x, ⟨hx, hxt⟩, rfl⟩
    have h1 : countBelow M VV g t =
        ∑' p : (vecAt v '' VV : Set _), {p | M.len (g⁻¹ • p) < t}.indicator 1 (p : _) := by
      rw [countBelow, ← (vecAt_injective v).encard_image, hPA, ← ENNReal.tsum_set_one,
        tsum_subtype (vecAt v '' VV), Set.indicator_indicator, ← tsum_subtype]
      rfl
    rw [h1, hP, ENNReal.tsum_biUnion' hdisj]
    refine (Finset.tsum_subtype' T fun o : Set (InfinitePlace E → ι → ℂ) =>
      ∑' p : o, {p | M.len (g⁻¹ • p) < t}.indicator (1 : (InfinitePlace E → ι → ℂ) → ℝ≥0∞) (p : InfinitePlace E → ι → ℂ)).trans ?_
    refine Finset.sum_congr rfl fun o ho => ?_
    rw [tsum_orbit_eq_tsum_quotient (vecAt v (Y o)) o (hYo o ho) _ (stabilizer_vecAt h v La (Y o))]
    refine tsum_congr fun q => ?_
    simp only [belowIndicator, Set.indicator_apply, Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv,
      mul_smul]
    rfl
  have hm : ∀ t : ℝ, 0 < t → massBelow M μ FD VV t =
      ∑ o ∈ T, Cf (Y o) * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1))) := by
    intro t ht
    rw [massBelow, lintegral_congr fun g => hcount g t, MeasureTheory.lintegral_finsetSum]
    · exact Finset.sum_congr rfl fun o ho => hCeq (Y o) (hSV (hYS o ho)) t ht
    · intro o ho
      letI := hQc ((vecStabGroup h v La (Y o)).subgroupOf Γ)
      exact Measurable.tsum fun q =>
        (measurable_belowIndicator M _ t).comp (measurable_const_mul _)
  refine ⟨FD, hFD, fun t ht => ⟨?_, fun θ hθ => ?_⟩⟩
  · rw [hm t ht]
    exact ENNReal.sum_lt_top.2 fun o ho =>
      ENNReal.mul_lt_top (hCf _ (hSV (hYS o ho))) ENNReal.ofReal_lt_top
  · rw [hm (θ * t) (mul_pos hθ ht), hm t ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hθ.le _)]
    ring

end Action

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVectorOrbits
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Units

variable (E : Type*) [Field E] [NumberField E]

def congruenceUnits (N : ℕ) : Subgroup (𝓞 E)ˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)})).toMonoidHom).ker

omit [NumberField E] in
variable {E} in
theorem mem_congruenceUnits {N : ℕ} {ε : (𝓞 E)ˣ} :
    ε ∈ congruenceUnits E N ↔ (ε : 𝓞 E) - 1 ∈ Ideal.span {(N : 𝓞 E)} := by
  rw [congruenceUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq]

def CongruenceUnitsFiniteIndex.Statement : Prop :=
  ∀ N : ℕ, 0 < N → (congruenceUnits E N).index ≠ 0

end Units

section Groups

def BoundedIndexSubgroupsFinite.Statement (G : Type*) [AddCommGroup G] : Prop :=
  ∀ A B : AddSubgroup G, B.FG → A ≤ B → ∀ C : ℕ,
    {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C}.Finite

end Groups

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def IsotropicScaling.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (La : AddSubgroup W) (x₀ : W), IsLattice E La → IsIntegralOn h La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 → ∃ N : ℕ, 0 < N ∧ ∀ ε ∈ congruenceUnits E N,
      ∃ γ ∈ latticeStab h La, γ • x₀ = ((ε : 𝓞 E) : E) • x₀

end Spaces

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchLatticeDiscrete
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise

noncomputable section

theorem eq_zero_of_isIntegral_of_forall_place_lt_one {K : Type*} [Field K] [NumberField K] {c : K}
    (hc : IsIntegral ℤ c) (hlt : ∀ w : InfinitePlace K, w c < 1) : c = 0 := by
  by_contra hne
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have ha : (⟨c, hc⟩ : 𝓞 K) ≠ 0 := fun h0 => hne (congrArg ((↑) : 𝓞 K → K) h0)
  exact absurd (InfinitePlace.one_le_of_lt_one ha (fun z _ => hlt z)) (not_le.2 (hlt w))

section Discrete

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem archEmbed_apply_val (h : HermitianForm F E W) (v : Basis ι E W) (g : h.unitaryGroup)
    (w : InfinitePlace E) :
    ((((archEmbed h v g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : GL ι ℂ) :
        Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((g : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
  rw [← unitaryGroupEquivMatrix_apply]
  rfl

theorem ArchLatticeDiscrete.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchLatticeDiscrete.Statement h v := by
  classical
  intro La hLa
  obtain ⟨S, hS⟩ := hLa.fg
  have hSLa : ∀ s ∈ S, (s : W) ∈ La := fun s _ => s.property

  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun s => Finset.univ.image fun i => v.repr s i)
  let T : AddSubgroup W :=
    { carrier := {y | ∀ i, IsIntegral ℤ (d • v.repr y i)}
      add_mem' := fun {a b} ha hb i => by
        simpa only [map_add (f := _), Finsupp.add_apply, smul_add] using (ha i).add (hb i)
      zero_mem' := fun i => by
        simpa only [map_zero, Finsupp.zero_apply, smul_zero] using isIntegral_zero
      neg_mem' := fun {a} ha i => by
        simpa only [map_neg, Finsupp.neg_apply, smul_neg] using (ha i).neg }
  have hLaT : La ≤ T := by
    intro x hx
    suffices h : ∀ y : La, (y : W) ∈ T from h ⟨x, hx⟩
    intro y
    have hy : y ∈ AddSubsemigroup.closure (↑S : Set La) := by rw [hS]; trivial
    induction hy using AddSubsemigroup.closure_induction with
    | mem s hs =>
      intro i
      exact hd _ (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
    | add a b _ _ ha hb => exact T.add_mem ha hb
  have hdE : (d : E) ≠ 0 := Int.cast_ne_zero.2 hd0

  have key : ∀ y ∈ La, (∀ (w : InfinitePlace E) (i : ι),
      |(d : ℝ)| * ‖w.embedding (v.repr y i)‖ < 1) → y = 0 := by
    intro y hy hsmall
    refine v.repr.injective (Finsupp.ext fun i => ?_)
    have hz := eq_zero_of_isIntegral_of_forall_place_lt_one (hLaT hy i) fun w => by
      rw [← InfinitePlace.norm_embedding_eq, zsmul_eq_mul, map_mul, map_intCast, norm_mul,
        Complex.norm_intCast]
      exact hsmall w i
    rw [zsmul_eq_mul] at hz
    simpa [hdE] using hz

  set B : ℝ := ∑ s ∈ S, ∑ w : InfinitePlace E, ∑ j, ‖w.embedding (v.repr s j)‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hdpos : 0 < |(d : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd0)
  set δ : ℝ := 1 / (|(d : ℝ)| * (B + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hdδB : |(d : ℝ)| * δ * B < 1 := by
    have e : |(d : ℝ)| * δ = 1 / (B + 1) := by
      rw [hδ]; field_simp
    rw [e, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
    linarith
  let U : Set (InfinitePlace E → GL ι ℂ) :=
    {g | ∀ w i j, ‖((g w : GL ι ℂ) : Matrix ι ι ℂ) i j - (1 : Matrix ι ι ℂ) i j‖ < δ}
  have hU : IsOpen U := by
    have e : U = ⋂ w, ⋂ i, ⋂ j, {g : InfinitePlace E → GL ι ℂ |
        ‖((g w : GL ι ℂ) : Matrix ι ι ℂ) i j - (1 : Matrix ι ι ℂ) i j‖ < δ} := by
      ext g; simp [U]
    rw [e]
    refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    exact (((Units.continuous_val.comp (continuous_apply w)).matrix_elem i j).sub
      continuous_const).norm

  have hone : ∀ γ ∈ latticeStab h La,
      ((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) ∈ U → γ = 1 := by
    intro γ hγ hγU
    set M := LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) with hM
    have hγLa : ∀ x ∈ La, (γ : W ≃ₗ[E] W) x ∈ La := by
      intro x hx
      have h1 : γ • x ∈ γ • La := AddSubgroup.smul_mem_pointwise_smul x γ La hx
      rwa [MulAction.mem_stabilizer_iff.1 hγ] at h1
    have hrep : ∀ x : W, ∀ i, v.repr ((γ : W ≃ₗ[E] W) x - x) i =
        ∑ j, (M i j - (1 : Matrix ι ι E) i j) * v.repr x j := by
      intro x i
      have h1 := congrFun (LinearMap.toMatrix_mulVec_repr v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x) i
      simp only [LinearEquiv.coe_coe] at h1
      rw [map_sub, Finsupp.sub_apply, ← h1]
      simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hM]
    have h1ij : ∀ (w : InfinitePlace E) i j,
        w.embedding ((1 : Matrix ι ι E) i j) = (1 : Matrix ι ι ℂ) i j := by
      intro w i j
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hfix : ∀ s ∈ S, (γ : W ≃ₗ[E] W) s = s := by
      intro s hs
      refine sub_eq_zero.1 (key _ (sub_mem (hγLa s (hSLa s hs)) (hSLa s hs)) fun w i => ?_)
      have entry : ∀ j, ‖w.embedding (M i j - (1 : Matrix ι ι E) i j)‖ < δ := by
        intro j
        have := hγU w i j
        rw [archEmbed_apply_val, Matrix.map_apply] at this
        rwa [map_sub, h1ij]
      have hsum : ‖w.embedding (v.repr ((γ : W ≃ₗ[E] W) s - s) i)‖ ≤
          δ * ∑ j, ‖w.embedding (v.repr s j)‖ := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hrep, map_sum, Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [map_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right (entry j).le (norm_nonneg _)
      have hsB : ∑ j, ‖w.embedding (v.repr s j)‖ ≤ B := by
        dsimp only [B]
        refine le_trans ?_ (Finset.single_le_sum (f := fun s : La => ∑ w : InfinitePlace E, ∑ j,
          ‖w.embedding (v.repr s j)‖) (fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => norm_nonneg _) hs)
        exact Finset.single_le_sum (f := fun w : InfinitePlace E => ∑ j,
          ‖w.embedding (v.repr s j)‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (Finset.mem_univ w)
      calc |(d : ℝ)| * ‖w.embedding (v.repr ((γ : W ≃ₗ[E] W) s - s) i)‖
          ≤ |(d : ℝ)| * (δ * B) := by
            gcongr
            exact hsum.trans (mul_le_mul_of_nonneg_left hsB hδpos.le)
        _ = |(d : ℝ)| * δ * B := by ring
        _ < 1 := hdδB
    have hfixLa : ∀ x ∈ La, (γ : W ≃ₗ[E] W) x = x := by
      intro x hx
      suffices h : ∀ y : La, (γ : W ≃ₗ[E] W) y = y from h ⟨x, hx⟩
      intro y
      have hy : y ∈ AddSubsemigroup.closure (↑S : Set La) := by rw [hS]; trivial
      induction hy using AddSubsemigroup.closure_induction with
      | mem x hx => exact hfix x hx
      | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
    have hlin : ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) = LinearMap.id :=
      LinearMap.ext_on hLa.span_eq_top fun x hx => hfixLa x hx
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simpa using LinearMap.congr_fun hlin x

  refine discreteTopology_of_isOpen_singleton_one ?_
  have hcont : Continuous fun x : archLatticeGroup h v La =>
      ((x : archUnitary h v) : InfinitePlace E → GL ι ℂ) :=
    continuous_subtype_val.comp continuous_subtype_val
  have e : ({1} : Set (archLatticeGroup h v La)) = (fun x : archLatticeGroup h v La =>
      ((x : archUnitary h v) : InfinitePlace E → GL ι ℂ)) ⁻¹' U := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl w i j
      simpa using hδpos
    · intro hx
      obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 x.2
      have h1 := hone γ hγ (by rw [hγx]; exact hx)
      apply Subtype.ext
      rw [← hγx, h1, map_one]
      rfl
  rw [e]
  exact hU.preimage hcont

end Discrete

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVecAtNeZero
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module NumberField

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}

theorem VecAtNeZero.proof (v : Basis ι E W) : VecAtNeZero.Statement v := by
  intro x hx w hw
  apply hx
  apply v.repr.injective
  ext i
  have h := congrFun hw i
  simp only [vecAt, Pi.zero_apply] at h
  simpa using (map_eq_zero_iff w.embedding w.embedding.injective).mp h

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchInvariant
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem star_mulVec_dotProduct_mulVec_mulVec (M H : Matrix ι ι ℂ) (y z : ι → ℂ) :
    star (M *ᵥ y) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star y ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
  rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mul_assoc]

theorem ArchInvariant.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchInvariant.Statement h v := by
  intro g y z w
  have hmem := mem_archUnitary.mp (g⁻¹ : archUnitary h v).2 w
  set M : Matrix ι ι ℂ := (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    with hM
  have hct : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hct] at hmem
  show star (M *ᵥ y w) ⬝ᵥ (gramAt h v w *ᵥ (M *ᵥ z w)) = star (y w) ⬝ᵥ (gramAt h v w *ᵥ z w)
  rw [star_mulVec_dotProduct_mulVec_mulVec, hmem]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StArchCovolumeBound
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def vecAtHom (v : Basis ι E W) : W →+ (InfinitePlace E → ι → ℂ) where
  toFun := vecAt v
  map_zero' := by funext w i; simp [vecAt]
  map_add' x y := by funext w i; simp [vecAt]

omit [_root_.NumberField.IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem vecAtHom_apply (v : Basis ι E W) (x : W) : vecAtHom v x = vecAt v x := rfl

def archLattice (v : Basis ι E W) (La : AddSubgroup W) : Submodule ℤ (InfinitePlace E → ι → ℂ) :=
  AddSubgroup.toIntSubmodule (La.map (vecAtHom v))

omit [_root_.NumberField.IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem mem_archLattice {v : Basis ι E W} {La : AddSubgroup W} {y : InfinitePlace E → ι → ℂ} :
    y ∈ archLattice v La ↔ ∃ x ∈ La, vecAt v x = y := by
  change y ∈ La.map (vecAtHom v) ↔ _
  rw [AddSubgroup.mem_map]
  rfl

def ArchCovolumeBound.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ D : ℕ, ∃ c : ℝ, ∀ La : AddSubgroup W, IsDIntegral h D La →
    ∃ _ : DiscreteTopology (archLattice v La), IsZLattice ℝ (archLattice v La) ∧
      ZLattice.covolume (archLattice v La) ≤ c

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWittPartner
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem WittPartner.proof (h : HermitianForm F E W) : WittPartner.Statement h := by
  intro x₀ hx₀ hiso

  have hne : h.toSesq x₀ ≠ 0 := by
    intro h0
    apply hx₀
    apply h.nonsingular.1
    rw [h0, map_zero]
  obtain ⟨y', hy'⟩ : ∃ y', h.toSesq x₀ y' ≠ 0 := by
    by_contra hc
    exact hne (LinearMap.ext fun z => not_not.1 fun hz => hc ⟨z, hz⟩)

  obtain ⟨y, hy⟩ : ∃ y, h.toSesq x₀ y = 1 :=
    ⟨(h.toSesq x₀ y')⁻¹ • y', by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy']⟩
  have hyx : h.toSesq y x₀ = 1 := by
    rw [← h.isSymm.eq x₀ y, hy, map_one]

  obtain ⟨a, ha_def⟩ : ∃ a, h.toSesq y y = a := ⟨_, rfl⟩
  have ha : conjHom F E a = a := by
    rw [← ha_def]
    exact h.isSymm.eq y y
  have ht : conjHom F E (a / 2) = a / 2 := by
    rw [map_div₀, ha, map_ofNat]

  have hl : ∀ z, h.toSesq (y - (a / 2) • x₀) z = h.toSesq y z - (a / 2) * h.toSesq x₀ z := by
    intro z
    rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, ht, smul_eq_mul]
  refine ⟨y - (a / 2) • x₀, ?_, ?_⟩
  · rw [map_sub, map_smul, hy, hiso, smul_zero, sub_zero]
  · rw [hl]
    simp only [map_sub, map_smul, smul_eq_mul, hyx, hy, hiso, ha_def]
    ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordLatticeFullRank
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

def CoordLatticeFullRank.Statement (v : Basis ι E W) : Prop :=
  ∀ La : AddSubgroup W, IsLattice E La →
    (La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom).FG ∧
      Submodule.span ℚ ((La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom : Set (ι → E))) = ⊤

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLenCauchySchwarz
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LenCauchySchwarz.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x y : W) (w : InfinitePlace E),
    ‖w.embedding (h.toSesq x y)‖ ≤ M.len (invApply g (vecAt v x)) * M.len (invApply g (vecAt v y))

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StDualLatticeMultiple
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def DualLatticeMultiple.Statement (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ k : ℤ, k ≠ 0 ∧ ∀ La : AddSubgroup W, IsDIntegral h D La →
    (∀ x ∈ La, ∀ y ∈ La, ∃ n : ℤ, Algebra.trace ℚ E (h.toSesq x y) = n) ∧
    ∀ y : W, (∀ x ∈ La, ∃ n : ℤ, Algebra.trace ℚ E (h.toSesq y x) = n) → k • y ∈ La

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
