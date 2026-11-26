module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL

theorem exists_open_normalised_subgroup_subset (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] :
    ∀ U ∈ 𝓝 (1 : GL n k), ∃ J : Subgroup (GL n k), IsOpen (J : Set (GL n k)) ∧
      (J : Set (GL n k)) ⊆ U ∧ J ≤ KO k n ∧ ∀ x ∈ KO k n, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  intro U hU
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix n n k) :=
    inferInstanceAs (TotallyDisconnectedSpace (n → n → k))
  have : TotallyDisconnectedSpace (GL n k) :=
    ⟨(SplitFlip.isEmbedding_val_GL (k := k) (n := n)).isTotallyDisconnected
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  have : CompactSpace (KO k n) :=
    isCompact_iff_compactSpace.1 (SplitFlip.isCompact_KO (k := k) (n := n))
  have hV : IsOpen ((fun x : KO k n => (x : GL n k)) ⁻¹' interior U) :=
    isOpen_interior.preimage continuous_subtype_val
  have h1 : (1 : KO k n) ∈ (fun x : KO k n => (x : GL n k)) ⁻¹' interior U :=
    mem_interior_iff_mem_nhds.2 hU
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1
  refine ⟨H.toSubgroup.map (KO k n).subtype, ?_, ?_, ?_, ?_⟩
  · exact (SplitFlip.isOpen_KO (k := k) (n := n)).isOpenMap_subtype_val _ H.isOpen
  · rintro _ ⟨y, hy, rfl⟩
    exact interior_subset (hH hy)
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro x hx _ ⟨y, hy, rfl⟩
    have hc : (⟨x, hx⟩ : KO k n) * y * (⟨x, hx⟩ : KO k n)⁻¹ ∈ H.toSubgroup :=
      H.isNormal'.conj_mem y hy (⟨x, hx⟩ : KO k n)
    exact Subgroup.mem_map_of_mem (KO k n).subtype hc

end GlobalTheory.SmGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal

namespace GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem map_mul_left_volM (h : GL n k) :
    (volM ν n n).map (fun x => h.val * x) =
      ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ))) • volM ν n n := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  haveI : LocallyCompactSpace (Matrix n n k) := inferInstanceAs (LocallyCompactSpace (n → n → k))
  haveI : SecondCountableTopology (Matrix n n k) := inferInstanceAs (SecondCountableTopology (n → n → k))
  haveI : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e : Matrix n n k ≃+ Matrix n n k :=
    { toFun := fun x => h.val * x
      invFun := fun x => (h⁻¹).val * x
      left_inv := fun x => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun x => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun x y => Matrix.mul_add _ _ _ }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  haveI := e.isAddHaarMeasure_map (volM ν n n) c1 c2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (volM ν n n).map e = c • volM ν n n :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  change (volM ν n n).map e = _
  set K : Set (Matrix n n k) := {A | ∀ i j, A i j ∈ 𝒪[k]} with hK
  have hKo : IsOpen K := SplitFlip.isOpen_intMatrix
  have hKc : IsCompact K := SplitFlip.isCompact_intMatrix
  have h0 : volM ν n n K ≠ 0 := (hKo.measure_pos _ ⟨0, fun _ _ => zero_mem _⟩).ne'
  have ht : volM ν n n K ≠ ⊤ := hKc.measure_lt_top.ne
  have hr : (volM ν n n).real K ≠ 0 := by simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, ht]
  have key := integral_comp_mul_mul_volM ν (1 : GL n k) h (K.indicator fun _ => (1 : ℂ))
  have h1 : ∫ x, K.indicator (fun _ => (1 : ℂ)) (h.val * x * (1 : GL n k).val) ∂(volM ν n n) =
      ∫ x, K.indicator (fun _ => (1 : ℂ)) x ∂((volM ν n n).map e) := by
    rw [integral_map c1.measurable.aemeasurable
      (stronglyMeasurable_const.indicator hKo.measurableSet).aestronglyMeasurable]
    simp only [Units.val_one, Matrix.mul_one]
    rfl
  rw [h1, hc, integral_smul_nnreal_measure, integral_indicator_const _ hKo.measurableSet, map_one, nabs_one,
    Real.one_rpow, mul_one] at key
  have h2 : (c : ℝ) = nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ)) := by
    refine mul_right_cancel₀ hr ?_
    simp only [NNReal.smul_def, smul_smul, Complex.real_smul, mul_one] at key
    exact_mod_cast key
  rw [hc, ← h2, ENNReal.ofReal_coe_nnreal]
  rfl

omit [MeasurableSpace k] [BorelSpace k] in
theorem continuous_density_volGL : Continuous fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) :=
  (((isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det).comp
    (fun t : ℝ => ENNReal.ofReal (t ^ (-(Fintype.card n : ℝ))))).continuous

theorem isMulLeftInvariant_volGL : (volGL ν n).IsMulLeftInvariant := by
  haveI := secondCountable k
  haveI : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have hE := Model.measurableEmbedding_val (k := k) n
  have hd := (continuous_density_volGL (k := k) (n := n)).measurable
  set μ := (volM ν n n).comap (fun g : GL n k => g.val) with hμ
  set d := fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) with hdd
  have dmul : ∀ g h, d (g * h) = d g * d h := fun g h => by
    simp only [hdd, map_mul, nabs_mul]
    rw [Real.mul_rpow (nabs_pos' _).le (nabs_pos' _).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (nabs_pos' _).le _)]
  have done' : d 1 = 1 := by simp [hdd, nabs_one]
  have hm : ∀ h : GL n k, μ.map (fun x => h * x) = d h • μ := fun h => by
    ext s hs
    have cm : Measurable fun x : Matrix n n k => h.val * x :=
      (continuous_const.matrix_mul continuous_id).measurable
    rw [Measure.map_apply (measurable_const_mul h) hs, Measure.smul_apply, hE.comap_apply, hE.comap_apply,
      ← Measure.smul_apply, ← map_mul_left_volM ν h, Measure.map_apply cm (hE.measurableSet_image.2 hs)]
    congr 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨h * g, hg, rfl⟩
    · rintro ⟨g, hg, e⟩
      refine ⟨h⁻¹ * g, by simpa using hg, ?_⟩
      have e' : g.val = h.val * x := e
      simp only [Units.val_mul, e', ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨fun h => ?_⟩
  ext s hs
  have hs' := measurable_const_mul h hs
  change (μ.withDensity d).map _ s = μ.withDensity d s
  rw [Measure.map_apply (measurable_const_mul h) hs, withDensity_apply _ hs', withDensity_apply _ hs,
    ← lintegral_indicator hs', ← lintegral_indicator hs]
  have e1 : ∀ x, ((fun x => h * x) ⁻¹' s).indicator d x = d h⁻¹ * s.indicator d (h * x) := fun x => by
    by_cases hx : h * x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x => h * x) ⁻¹' s from hx), ← dmul,
        inv_mul_cancel_left]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun x => h * x) ⁻¹' s from hx),
        mul_zero]
  simp_rw [e1]
  rw [lintegral_const_mul _ (f := fun a => s.indicator d (h * a))
      ((hd.indicator hs).comp (measurable_const_mul h)),
    ← lintegral_map (hd.indicator hs) (measurable_const_mul h), hm, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, ← dmul, inv_mul_cancel, done', one_mul]

theorem volGL_KO : volGL ν n (KO k n) = volM ν n n ((fun g : GL n k => g.val) '' (KO k n)) := by
  have hE := Model.measurableEmbedding_val (k := k) n
  have hs := (SplitFlip.isOpen_KO (k := k) (n := n)).measurableSet
  unfold volGL
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 1), setLIntegral_one, hE.comap_apply]
  rintro _ ⟨u, rfl⟩
  have h1 : nabs k (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u)) = 1 := by
    rw [nabs_eq_one_iff]
    have : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) = algebraMap 𝒪[k] k u.val.det :=
      ((algebraMap 𝒪[k] k).map_det u.val).symm
    rw [this]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  simp only [h1, Real.one_rpow, ENNReal.ofReal_one]

theorem isHaarMeasure_volGL : (volGL ν n).IsHaarMeasure := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI := isMulLeftInvariant_volGL (n := n) ν
  have ho := SplitFlip.isOpen_KO (k := k) (n := n)
  have hc := SplitFlip.isCompact_KO (k := k) (n := n)
  have hoe : Topology.IsOpenEmbedding (fun g : GL n k => g.val) := by
    refine ⟨SplitFlip.isEmbedding_val_GL, ?_⟩
    have : Set.range (fun g : GL n k => g.val) = {x : Matrix n n k | x.det ≠ 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
      rfl
    rw [this]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ _ hc
    (by rw [ho.interior_eq]; exact ⟨1, one_mem _⟩) ?_ ?_
  · rw [volGL_KO]
    exact ((hoe.isOpenMap _ ho).measure_pos _ ⟨_, 1, one_mem _, rfl⟩).ne'
  · rw [volGL_KO]
    exact (hc.image hoe.continuous).measure_lt_top.ne

theorem volGL_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure], BorelSpace (GL n k) ∧ LocallyCompactSpace (GL n k) ∧ SecondCountableTopology (GL n k) ∧ IsCompact (KO k n : Set (GL n k)) ∧ IsOpen (KO k n : Set (GL n k)) ∧ IsOpen (KOne k n : Set (GL n k)) ∧ (volGL ν n).IsHaarMeasure ∧ (volGL ν n).IsMulRightInvariant :=
  fun _ _ _ _ _ _ _ n _ _ ν _ =>
    haveI := isHaarMeasure_volGL (n := n) ν
    ⟨SplitFlip.borel_GL, SplitFlip.locallyCompact_GL, SplitFlip.secondCountable_GL, SplitFlip.isCompact_KO,
      SplitFlip.isOpen_KO, StepData.isOpen_KOne, this, SplitFlip.isMulRightInvariant_of_haar _⟩

end GlobalTheory.SplitWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData ValuativeRel Matrix Topology Filter
open scoped TensorProduct

namespace GlobalTheory.CentralExponent

section Abstract

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mul_small {γ : (ValueGroupWithZero k)ˣ} {A B : Matrix n n k} (hA : IntM A)
    (hB : ∀ i j, valuation k (B i j) < γ) (i j : n) : valuation k ((A * B) i j) < γ := by
  refine Valuation.map_sum_lt _ γ.ne_zero fun s _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left' (hA i s)).trans_lt (hB s j)

variable (n) in
def cong (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) : Subgroup (GL n k) where
  carrier := {g | ∀ i j, valuation k ((g.val - 1) i j) < γ}
  one_mem' := fun i j => by simp
  mul_mem' := by
    intro g h hg hh i j
    have h1 : g ∈ KOne k n := mem_KOne.2 fun i j => (hg i j).trans_le hγ
    have : (g * h).val - 1 = g.val * (h.val - 1) + (g.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [this]
    exact Valuation.map_add_lt _ (mul_small (intM_of_mem_KO (KOne_le_KO h1)) hh i j) (hg i j)
  inv_mem' := by
    intro g hg i j
    have h1 : g ∈ KOne k n := mem_KOne.2 fun i j => (hg i j).trans_le hγ
    have : (g⁻¹).val - 1 = (-(g⁻¹).val) * (g.val - 1) := by
      rw [neg_mul, mul_sub, Units.inv_mul]; simp
    rw [this]
    exact mul_small (intM_of_mem_KO (KOne_le_KO (inv_mem h1))).neg hg i j

theorem isOpen_cong (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) :
    IsOpen (cong (n := n) γ hγ : Set (GL n k)) := by
  have e : (cong (n := n) γ hγ : Set (GL n k)) = ⋂ i, ⋂ j,
      (fun g : GL n k => (g.val - 1) i j) ⁻¹' {x | valuation k x < γ} := by
    ext g; simp only [SetLike.mem_coe, Set.mem_iInter]; rfl
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · exact (Units.continuous_val.sub continuous_const).matrix_elem i j
  · refine isOpen_iff_mem_nhds.2 fun x hx => (IsValuativeTopology.mem_nhds_iff).2 ⟨γ, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact Valuation.map_add_lt (valuation k) (g := γ) hx hy

theorem isCompact_cong (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) :
    IsCompact (cong (n := n) γ hγ : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_cong (n := n) γ hγ))
    fun _ hg => KOne_le_KO (mem_KOne.2 fun i j => (hg i j).trans_le hγ)

theorem exists_cong_subset {U : Set (GL n k)} (hU : U ∈ 𝓝 (1 : GL n k)) :
    ∃ (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1), ∀ g ∈ cong (n := n) γ hγ, g ∈ U := by
  rw [SplitFlip.isEmbedding_val_GL.nhds_eq_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  have h1 : (fun A : Matrix n n k => A + 1) ⁻¹' T ∈ 𝓝 (0 : Matrix n n k) :=
    (continuous_add_const _).continuousAt.preimage_mem_nhds (by simpa using hT)
  have h2 : Tendsto (fun p : (ValueGroupWithZero k)ˣ × Matrix n n k =>
      if ∀ i j, valuation k (p.2 i j) < p.1 then p.2 else 0) (atBot ×ˢ ⊤) (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [Matrix.zero_apply, (IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    filter_upwards [prod_mem_prod (mem_atBot γ) univ_mem] with p hp
    split_ifs with h
    · exact (h i j).trans_le hp.1
    · simp
  obtain ⟨γ, hγ1, hγ⟩ := ((eventually_le_atBot 1).and (mem_prod_top.1 (h2 h1))).exists
  refine ⟨γ, hγ1, fun g hg => hTU ?_⟩
  have := hγ (g.val - 1)
  have hg' : ∀ i j, valuation k ((g.val - 1) i j) < γ := hg
  rw [Set.mem_preimage, Set.mem_preimage, if_pos hg', sub_add_cancel] at this
  exact this

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem cong_factor (e : a ⊕ b ≃ n) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) :
    ∀ g ∈ cong (n := n) γ hγ, ∃ x ∈ unipRad k (two e), ∃ c ∈ cong (n := n) γ hγ ⊓ parabLower k (two e), g = x * c := by
  intro g hg
  let M : Matrix n n k := Matrix.of fun i j => if (e.symm j).isLeft then (1 : Matrix n n k) i j else g.val i j
  have hM : ∀ i j, valuation k ((M - 1) i j) < γ := fun i j => by
    by_cases h : (e.symm j).isLeft
    · simp [M, h]
    · simpa [M, h] using hg i j
  obtain ⟨p, -, hp⟩ := exists_mem_KOne (M := M) fun i j => (hM i j).trans_le hγ
  have hpK : p ∈ cong (n := n) γ hγ := fun i j => hp ▸ hM i j
  have hpP : p ∈ parab k (two e) := (mem_parab_two k).2 fun j i => by simp [hp, M, one_apply]
  let q : parab k (two e) := ⟨_, leviEmb_mem_parab k (two e) (leviProj k (two e) ⟨p, hpP⟩)⟩
  have hqK : q.1 ∈ cong (n := n) γ hγ := by
    intro i j
    obtain ⟨⟨s, i⟩, rfl⟩ := (two e).surjective i
    obtain ⟨⟨t, j⟩, rfl⟩ := (two e).surjective j
    by_cases h : s = t
    · subst h
      have := hpK (two e ⟨s, i⟩) (two e ⟨s, j⟩)
      simpa [q] using this
    · rw [Matrix.sub_apply, leviEmb_apply_ne k (two e) _ h, one_apply_ne (by simp [h])]
      simp
  refine ⟨((⟨p, hpP⟩ * q⁻¹ : parab k (two e)) : GL n k), (coe_mem_unipRad k _).2 ?_, q * (p⁻¹ * g),
    Subgroup.mem_inf.2 ⟨mul_mem hqK (mul_mem (inv_mem hpK) hg), mul_mem (leviEmb_mem_parabLower k _ _)
      ((mem_parabLower_two k).2 fun i j => ?_)⟩, by simp [mul_assoc]⟩
  · rw [map_mul, map_inv, leviProj_leviEmb, mul_inv_cancel]
  · have : (p⁻¹ * g).val (e (.inl i)) (e (.inr j)) = (p⁻¹ * p).val (e (.inl i)) (e (.inr j)) := by
      simp only [Units.val_mul, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      simp [hp, M]
    rw [this, inv_mul_cancel, Units.val_one, one_apply_ne (by simp)]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem val_emb₂_scalar (e : a ⊕ b ≃ n) (z : kˣ) :
    (emb₂ k e (GeneralLinearGroup.scalar a z, 1)).val =
      diagonal fun i => if (e.symm i).isLeft then (z : k) else 1 := by
  rw [val_emb₂]
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [GeneralLinearGroup.scalar, diagonal_apply, Matrix.one_apply]

theorem cong_contract (e : a ⊕ b ≃ n) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) {z : kˣ}
    (hz : valuation k (z : k) ≤ 1) : ∀ c ∈ cong (n := n) γ hγ ⊓ parabLower k (two e),
      (emb₂ k e (GeneralLinearGroup.scalar a z, 1))⁻¹ * c * emb₂ k e (GeneralLinearGroup.scalar a z, 1) ∈
        cong (n := n) γ hγ ⊓ parabLower k (two e) := by
  intro c hcc
  obtain ⟨hc, hc'⟩ := Subgroup.mem_inf.1 hcc
  have hm : emb₂ k e (GeneralLinearGroup.scalar a z, 1) ∈ parabLower k (two e) :=
    leviEmb_mem_parabLower k _ _
  refine Subgroup.mem_inf.2 ⟨fun i j => ?_, mul_mem (mul_mem (inv_mem hm) hc') hm⟩
  have h1 := hc i j
  rw [← map_inv, Prod.inv_mk, ← map_inv, inv_one, Units.val_mul, Units.val_mul, val_emb₂_scalar,
    val_emb₂_scalar, Matrix.sub_apply, mul_diagonal, diagonal_mul]
  rw [Matrix.sub_apply] at h1
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j
  · simpa [mul_comm, mul_left_comm] using h1
  · simp [(mem_parabLower_two k).1 hc' i j, one_apply]
  · simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, if_false, sub_zero] at h1 ⊢
    simpa using (mul_le_of_le_one_right' hz).trans_lt h1
  · simpa using h1

end Local

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  {V X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

variable (k) in
theorem exists_nabs_lt_one : ∃ z : kˣ, valuation k (z : k) ≤ 1 ∧ nabs k z < 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  refine ⟨Units.mk0 _ h0, ϖ.2, ?_⟩
  rw [nabs_uniformiser hϖ (x := Units.mk0 _ h0) rfl]
  refine inv_lt_one_of_one_lt₀ ?_
  rw [resCard]
  exact_mod_cast Finite.one_lt_card

end Main

end GlobalTheory.CentralExponent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.InertSupp

section Blocks

variable {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem _root_.GlobalTheory.InertSupp.exists_blocks (c : n → ℤ) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n),
    ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j := by
  classical
  let S : Finset ℤ := Finset.univ.image c
  let o := S.orderIsoOfFin rfl
  let φ : n → Fin S.card := fun i => o.symm ⟨c i, Finset.mem_image_of_mem c (Finset.mem_univ i)⟩
  refine ⟨S.card, fun a => Fintype.card {i // φ i = a},
    (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ), ?_⟩
  intro i j
  have key : ∀ x, (((Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ)).symm x).1 = φ x := fun x => rfl
  unfold _root_.GlobalTheory.SmGL.blk
  rw [key, key]
  simp only [φ, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

variable (R : Type) [CommRing R]

def unipOf (c : n → ℤ) : Subgroup (GL n R) :=
  (unipRad R (exists_blocks c).choose_spec.choose_spec.choose).copy
    {g | ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j} (by
      ext g
      simp only [SetLike.mem_coe, CuspMax.mem_unipRad_iff_entries,
        (exists_blocks c).choose_spec.choose_spec.choose_spec, Set.mem_setOf_eq])

variable {R}

variable {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.InertSupp.mem_unipOf {c : n → ℤ} {g : GL n R} :
    g ∈ _root_.GlobalTheory.InertSupp.unipOf R c ↔
      ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j :=
  Iff.rfl

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

variable {n : Type} [Fintype n] [DecidableEq n] in
variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] in
variable (R) in
theorem _root_.GlobalTheory.InertSupp.unipRad_eq_unipOf {e : (Σ a, m a) ≃ n}
    {c : n → ℤ} (h : ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j) :
    _root_.GlobalTheory.SmGL.unipRad R e = _root_.GlobalTheory.InertSupp.unipOf R c := by
  ext g
  rw [_root_.GlobalTheory.InertSupp.mem_unipOf, _root_.GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries]
  simp only [h]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

variable [MeasurableSpace k] [BorelSpace k]

def zetaIntegrand (Φ : Matrix n n k → ℂ) (c : GL n k → ℂ) (s : ℂ) (g : GL n k) : ℂ :=
  Φ g.val * c g * (absPow k (s + ((Fintype.card n : ℂ) - 1) / 2) (GeneralLinearGroup.det g) : ℂ)

end Local

end GlobalTheory.InertSupp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInduced
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatEventuallyInvariantOfContinuousAct
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem schwartzBruhat_eventually_invariant_of_continuous_action :
    ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
      (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) →
      Continuous (fun p : X × G => r p.1 p.2) →
      ∀ Φ : SB X, ∀ᶠ u in nhds (1 : G), ∀ x, Φ.1 (r x u) = Φ.1 x := by
  intro G X _ _ _ _ r h1 hmul hc Φ
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  obtain ⟨hlc, hcs⟩ := hΦ
  have hA : IsLocallyConstant (fun z : G × X => Φ.1 (r z.2 z.1)) :=
    hlc.comp_continuous (hc.comp continuous_swap)
  have hB : IsLocallyConstant (fun z : G × X => Φ.1 z.2) :=
    hlc.comp_continuous continuous_snd
  have key : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u) = Φ.1 x := by
    refine IsCompact.eventually_forall_of_forall_eventually
      (P := fun u x => Φ.1 (r x u) = Φ.1 x) hcs ?_
    intro y _
    filter_upwards [hA.eventually_eq ((1 : G), y), hB.eventually_eq ((1 : G), y)] with z hz hz'
    rw [hz, hz']
    simp only [h1]
  have key' : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u⁻¹) = Φ.1 x := by
    have ht : Filter.Tendsto (fun u : G => u⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact ht.eventually key
  filter_upwards [key, key'] with u hu hu' x
  by_cases hx : x ∈ tsupport Φ.1
  · exact hu x hx
  · by_cases hy : r x u ∈ tsupport Φ.1
    · have := hu' _ hy
      rw [← hmul, mul_inv_cancel, h1] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInduced
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology Filter

namespace GlobalTheory.SBInduced

variable {G X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
  [TopologicalSpace Y]

omit [IsTopologicalGroup G] in
theorem isClosedEmbedding_translate (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) (g : G) : IsClosedEmbedding fun y => r (j y) g := by
  have hc' : ∀ g, Continuous fun x => r x g := fun g => hc.comp (Continuous.prodMk_left g)
  let e : X ≃ₜ X :=
    { toFun := fun x => r x g
      invFun := fun x => r x g⁻¹
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := hc' g
      continuous_invFun := hc' g⁻¹ }
  exact e.isClosedEmbedding.comp hj

theorem isQuotientMap_sweep (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) :
    IsQuotientMap fun p : Y × K => r (j p.1) p.2 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e : X × K ≃ₜ X × K :=
    { toFun := fun p => (r p.1 p.2, p.2)
      invFun := fun p => (r p.1 (p.2 : G)⁻¹, p.2)
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).prodMk
        continuous_snd
      continuous_invFun := (hc.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd).inv)).prodMk continuous_snd }
  have hcl : IsClosedMap fun p : Y × K => r (j p.1) p.2 :=
    (isClosedMap_fst_of_compactSpace (X := X) (Y := K)).comp
      (e.isClosedMap.comp (hj.prodMap (IsClosedEmbedding.id (X := K))).isClosedMap)
  refine hcl.isQuotientMap (hc.comp ((hj.continuous.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))) fun x => ?_
  obtain ⟨y, c, hc, rfl⟩ := hs x
  exact ⟨(y, ⟨c, hc⟩), rfl⟩

theorem descend [T2Space X] (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) (H : G → SB Y)
    (hU : ∀ᶠ u in 𝓝 (1 : G), ∀ g, H (g * u) = H g)
    (hfib : ∀ y g y' g', r (j y) g = r (j y') g' → (H g).1 y = (H g').1 y') :
    ∃ Φ : SB X, ∀ g y, Φ.1 (r (j y) g) = (H g).1 y := by
  have hq := isQuotientMap_sweep r h1 hm hc hj hK hs
  choose y c hcK hx using hs
  let φ : X → ℂ := fun x => (H (c x)).1 (y x)
  have hφ : ∀ g z, φ (r (j z) g) = (H g).1 z := fun g z => hfib _ _ _ _ (hx _).symm
  have hnear : ∀ g : G, ∀ᶠ z in 𝓝 g, H z = H g := fun g => by
    have hc : Tendsto (fun z : G => g⁻¹ * z) (𝓝 g) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact (hc.eventually hU).mono fun z hz => by simpa using hz g
  have hlc : IsLocallyConstant fun p : Y × G => (H p.2).1 p.1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro p
    filter_upwards [(continuous_snd.tendsto p).eventually (hnear p.2),
      (continuous_fst.tendsto p).eventually ((H p.2).2.1.eventually_eq p.1)] with z h₁ h₂
    rw [h₁, h₂]
  refine ⟨⟨φ, fun s => ?_, ?_⟩, hφ⟩
  · rw [← hq.isOpen_preimage]
    have := (hlc.comp_continuous (f := fun p : Y × K => (p.1, (p.2 : G)))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) s
    convert this using 1
    ext p
    simp only [Set.mem_preimage, hφ, Function.comp_apply]
  · obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {z | H z = H x}) fun x _ => hnear x
    have hC : IsCompact (⋃ g ∈ t, tsupport (H g).1) :=
      t.isCompact_biUnion fun g _ => (H g).2.2
    refine HasCompactSupport.intro (((hC.image hj.continuous).prod hK).image hc) fun x hxn => ?_
    by_contra h0
    apply hxn
    obtain ⟨g, hg, hcg⟩ := Set.mem_iUnion₂.1 (ht (hcK x))
    refine ⟨(j (y x), c x), ⟨⟨y x, Set.mem_iUnion₂.2 ⟨g, hg, subset_tsupport _ ?_⟩, rfl⟩, hcK x⟩,
      (hx x).symm⟩
    rw [← show H (c x) = H g from hcg]
    exact h0

theorem sb_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  intro G X Y W _ _ _ _ _ _ _ _ r h1 hm hc j hj P K hK hs s hsP hP χ hχ σ ev hev
  have hχ' : ∀ᶠ u in 𝓝 (1 : G), χ u = 1 := IsOpen.mem_nhds hχ (one_mem χ.ker)
  have hce := isClosedEmbedding_translate r h1 hm hc hj
  let A : SB X → G → SB Y := fun Φ g => (χ g : ℂ) • ⟨fun y => Φ.1 (r (j y) g),
    Φ.2.1.comp_continuous (hce g).continuous, Φ.2.2.comp_isClosedEmbedding (hce g)⟩
  have hA : ∀ Φ g y, (A Φ g).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun _ _ _ => rfl
  have hext : ∀ w w' : W, (∀ y, (ev w).1 y = (ev w').1 y) → w = w' := fun w w' h =>
    ev.injective (Subtype.ext (funext h))
  let T : SB X →ₗ[ℂ] smoothPart (ind P σ) :=
    { toFun := fun Φ => ⟨⟨fun g => ev.symm (A Φ g), fun p g => hext _ _ fun y => by
          rw [hev, ev.apply_symm_apply, ev.apply_symm_apply, hA, hA, hm, hsP, map_mul, Units.val_mul,
            mul_assoc]⟩,
        mem_smoothPart_of_nhds (by
          filter_upwards [hχ', GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action G X r h1 hm hc Φ] with u hu hu'
          refine Subtype.ext (funext fun g => ?_)
          show ev.symm (A Φ (g * u)) = ev.symm (A Φ g)
          congr 1
          refine Subtype.ext (funext fun y => ?_)
          rw [hA, hA, map_mul, hu, mul_one, hm, hu'])⟩
      map_add' := fun Φ Ψ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (Φ + Ψ) g) = ev.symm (A Φ g) + ev.symm (A Ψ g)
        rw [← map_add (f := _)]
        congr 1
        exact Subtype.ext (funext fun y => mul_add _ _ _)))
      map_smul' := fun a Φ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (a • Φ) g) = a • ev.symm (A Φ g)
        rw [← map_smul]
        congr 1
        exact Subtype.ext (funext fun y => mul_left_comm _ _ _))) }
  have hT : ∀ Φ g y, (ev ((T Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun Φ g y => by
    show (ev (ev.symm (A Φ g))).1 y = _
    rw [ev.apply_symm_apply, hA]
  have hinj : Function.Injective T := fun Φ Ψ h => Subtype.ext (funext fun x => by
    obtain ⟨y, c, -, rfl⟩ := hs x
    have := hT Φ c y
    rw [h, hT] at this
    exact (mul_left_cancel₀ (χ c).ne_zero this).symm)
  have hsurj : Function.Surjective T := fun F => by
    have hF : ∀ᶠ u in 𝓝 (1 : G), ∀ x, F.1.1 (x * u) = F.1.1 x :=
      Filter.mem_of_superset (IsOpen.mem_nhds F.2 (by simp)) fun g hg x =>
        congrFun (congrArg Subtype.val (show ind P σ g F.1 = F.1 from hg)) x
    obtain ⟨Φ, hΦ⟩ := descend r h1 hm hc hj hK hs (fun g => (χ g : ℂ)⁻¹ • ev (F.1.1 g))
      (by
        filter_upwards [hχ', hF] with u hu hu' g
        rw [hu', map_mul, hu, mul_one])
      (fun y g y' g' h => by
        have h2 : r (j y) (g * g'⁻¹) = j y' := by rw [hm, h, ← hm, mul_inv_cancel, h1]
        have hp := hP _ _ _ h2
        have h3 : s y ⟨_, hp⟩ = y' := hj.injective ((hsP y ⟨_, hp⟩).symm.trans h2)
        have h4 := F.1.2 ⟨_, hp⟩ g'
        rw [show ((⟨_, hp⟩ : P) : G) * g' = g from inv_mul_cancel_right g g'] at h4
        show (χ g : ℂ)⁻¹ * (ev (F.1.1 g)).1 y = (χ g' : ℂ)⁻¹ * (ev (F.1.1 g')).1 y'
        rw [h4, hev, h3]
        simp [← mul_assoc])
    refine ⟨Φ, Subtype.ext (Subtype.ext (funext fun g => hext _ _ fun y => ?_))⟩
    rw [hT, hΦ]
    exact mul_inv_cancel_left₀ (χ g).ne_zero _
  exact ⟨LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

end GlobalTheory.SBInduced
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInducedStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  first | exact @GlobalTheory.SBInduced.sb_induced | exact GlobalTheory.SBInduced.sb_induced | (intros; apply GlobalTheory.SBInduced.sb_induced <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair
open SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}

theorem ite_mem_SB {X : Type*} [TopologicalSpace X] {p : X → Prop} [DecidablePred p] (h : IsClopen {x | p x})
    (hc : IsCompact {x | p x}) : (fun x => if p x then (1 : ℂ) else 0) ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro' hc h.1 fun x hx => if_neg hx⟩
  by_cases hx : p x
  · exact ⟨_, h.2, hx, fun y hy => (if_pos hy).trans (if_pos hx).symm⟩
  · exact ⟨_, h.compl.2, hx, fun y hy => (if_neg hy).trans (if_neg hx).symm⟩

variable [Fintype n] [Fintype n']

theorem isClopen_lattice (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] : IsClopen (L : Set (n → k)) := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have h : ((g • stdLat k n : Submodule 𝒪[k] (n → k)) : Set (n → k)) =
      ⋂ i, (fun x => ((g⁻¹ : GL n k).val *ᵥ x) i) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [SetLike.mem_coe, mem_smul_iff, mem_stdLat, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [h]
  refine isClopen_iInter_of_finite fun i => IsClopen.preimage ⟨(isCompact_int k).isClosed, isOpen_int k⟩ ?_
  exact (continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)

omit [Fintype n] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem maps_stdLat_iff {x : Matrix n n' k} :
    (∀ y ∈ stdLat k n', x *ᵥ y ∈ stdLat k n) ↔ ∀ i j, x i j ∈ 𝒪[k] := by
  classical
  simp only [mem_stdLat]
  refine ⟨fun h i j => ?_, fun h y hy i => sum_mem fun j _ => mul_mem (h i j) (hy j)⟩
  have := h (Pi.single j 1) (fun l => ?_) i
  · simpa using this
  · rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]

theorem isClopen_isCompact_maps (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsFullLattice k]
    [L.IsFullLattice k] : IsClopen {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} ∧
      IsCompact {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n') S
  obtain ⟨h, rfl⟩ := exists_smul_lat (stdLat k n) L
  let K : Set (Matrix n n' k) := Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have hKo : IsOpen K :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
  have e : {x : Matrix n n' k | ∀ y ∈ g • stdLat k n', x *ᵥ y ∈ h • stdLat k n} = sideMul g h ⁻¹' K := by
    ext x
    have h1 : sideMul g h x ∈ K ↔ ∀ i j, ((h⁻¹ : GL n k).val * x * g.val) i j ∈ 𝒪[k] :=
      ⟨fun H i j => H i trivial j trivial, fun H i _ j _ => H i j⟩
    rw [Set.mem_preimage, h1, ← maps_stdLat_iff, Set.mem_setOf_eq]
    simp only [mem_smul_iff, ← mulVec_mulVec]
    refine ⟨fun H y hy => H (g • y) (by simpa using hy), fun H y hy => ?_⟩
    have := H _ hy
    rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
  rw [e]
  exact ⟨IsClopen.preimage ⟨hKc.isClosed, hKo⟩ (sideMul g h).continuous, (sideMul g h).isCompact_preimage.2 hKc⟩

theorem latInd_mem_SB (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsFullLattice k] [L.IsFullLattice k] :
    latInd S L ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_maps S L).1 (isClopen_isCompact_maps S L).2

theorem isClopen_isCompact_mapsPair (P : Pair k n') (Q : Pair k n) :
    IsClopen {x : Matrix n n' k | Maps P Q x} ∧ IsCompact {x : Matrix n n' k | Maps P Q x} := by
  have e : {x : Matrix n n' k | Maps P Q x} = {x : Matrix n n' k | ∀ y ∈ P.ker, x *ᵥ y ∈ Q.ker} ∩
      (fun x : Matrix n n' k => x *ᵥ P.vec - Q.vec) ⁻¹' (Q.ker : Set (n → k)) := by
    ext x
    exact maps_iff_glue P.hasVal_vec Q.hasVal_vec
  have h2 := (isClopen_lattice Q.ker).preimage (f := fun x : Matrix n n' k => x *ᵥ P.vec - Q.vec)
    ((continuous_id.matrix_mulVec continuous_const).sub continuous_const)
  obtain ⟨h1, hc⟩ := isClopen_isCompact_maps P.ker Q.ker
  rw [e]
  exact ⟨h1.inter h2, hc.inter_right h2.1⟩

theorem phiOne_mem_SB (P : Pair k n') (Q : Pair k n) : phiOne P Q ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_mapsPair P Q).1 (isClopen_isCompact_mapsPair P Q).2

end GlobalTheory.LatPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
namespace GlobalTheory.LocAsm

def exOne {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) : ∀ b, X b → ℂ := fun b x =>
  match b, x with
  | .ex _ _, _ => 1
  | .theta i j, x => φ (.theta i j) x

@[simp] theorem exOne_theta {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) (i j : ℕ) (x : X (.theta i j)) :
    exOne φ (.theta i j) x = φ (.theta i j) x := rfl

end GlobalTheory.LocAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelCasselmanHolds
namespace GlobalTheory.Published

theorem BorelCasselman_holds : GlobalTheory.Published.BorelCasselman :=
  fun k _ _ _ _ n _ _ _ V _ _ π hπ =>
    ⟨GlobalTheory.IwahoriInj.iwahoriProj_injective k n V π hπ.1,
      GlobalTheory.SmGL.IwahoriOnto.iwahoriProj_surjective k n V π hπ⟩

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzFourierTransformPiSurjectiveSchwartzBruh
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzFourierTransformPiSurjectiveSchwartzBruh
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.SplitWeil.FourierSurj

theorem hat_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), (∀ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 ∈ SB (n → k)) ∧ ∀ g : SB (n → k), ∃ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 = g.1 := by
  intro k _ _ _ _ _ _ n _ _ ψ hc h1 ν hν
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have key := FourierPi.fourier_pi k n ψ hc h1 ν hν
  have hhat : ∀ f : (n → k) → ℂ,
      hat ψ ν f = fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro f
    funext y
    simp only [hat, dotProduct_comm y]
  have hmem : ∀ f ∈ SB (n → k), hat ψ ν f ∈ SB (n → k) := fun f hf => hhat f ▸ (key f hf).1
  refine ⟨fun Φ₀ => hmem _ Φ₀.2, fun g => ?_⟩
  have hcomp : ∀ (e : (n → k) ≃ₜ (n → k)), ∀ f ∈ SB (n → k), (fun x => f (e x)) ∈ SB (n → k) :=
    fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
  have hg' : (fun x => g.1 (-x)) ∈ SB (n → k) := hcomp (Homeomorph.neg _) _ g.2
  refine ⟨⟨_, hmem _ hg'⟩, ?_⟩
  funext u
  have hf : (fun x => g.1 (-(x + -u))) ∈ SB (n → k) := hcomp (Homeomorph.addRight (-u)) _ hg'
  have h2 := (key _ hf).2
  simp only [zero_add, neg_neg] at h2
  rw [← h2]
  show ∫ β, hat ψ ν (fun x => g.1 (-x)) β * (ψ (u ⬝ᵥ β) : ℂ) ∂(Measure.pi fun _ => ν) = _
  congr 1
  funext y
  rw [hhat, ← integral_mul_const,
    ← integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) _ (-u)]
  congr 1
  funext x
  rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← add_dotProduct, neg_add_cancel_right]

end GlobalTheory.SplitWeil.FourierSurj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzFourierTransformPiSurjectiveSchwartzBruhStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), (∀ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 ∈ SB (n → k)) ∧ ∀ g : SB (n → k), ∃ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 = g.1 := by
  first | exact @GlobalTheory.SplitWeil.FourierSurj.hat_surjective | exact GlobalTheory.SplitWeil.FourierSurj.hat_surjective | (intros; apply GlobalTheory.SplitWeil.FourierSurj.hat_surjective <;> assumption)
end
end
