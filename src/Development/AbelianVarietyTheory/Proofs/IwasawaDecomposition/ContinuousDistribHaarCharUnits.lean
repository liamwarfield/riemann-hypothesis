module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx Filter
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeEx

theorem continuous_distribHaarChar_units (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] :
    Continuous (fun u : Rˣ => distribHaarChar R u) := by
  let μ : Measure R := Measure.addHaar
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : R)
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have ht : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hup : ∀ c : ℝ≥0, 1 < c → ∃ V ∈ 𝓝 (1 : R), ∀ u : Rˣ, (u : R) ∈ V → distribHaarChar R u < c := by
    intro c hc
    have hlt : μ K < (c : ℝ≥0∞) * μ K := by
      calc μ K = 1 * μ K := (one_mul _).symm
        _ < _ := (ENNReal.mul_lt_mul_iff_left h0 ht).2 (by exact_mod_cast hc)
    obtain ⟨U, hKU, hUo, hU⟩ := Set.exists_isOpen_lt_of_lt K _ hlt
    obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hKc hUo hKU
    refine ⟨V, hV, fun u hu => ?_⟩
    have h1 : μ (u • K) ≤ μ U := by
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hVS ⟨u, hu, x, hx, rfl⟩
    rw [← distribHaarChar_mul μ u K] at h1
    have h3 := (ENNReal.mul_lt_mul_iff_left h0 ht).1 (h1.trans_lt hU)
    exact_mod_cast h3
  refine continuous_of_continuousAt_one (distribHaarChar R : Rˣ →* NNReal) ?_
  rw [ContinuousAt, map_one, tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a = 0
    · subst ha0
      exact Eventually.of_forall fun u => distribHaarChar_pos
    have hap : 0 < a := pos_iff_ne_zero.2 ha0
    obtain ⟨V, hV, h⟩ := hup a⁻¹ ((one_lt_inv₀ hap).2 ha)
    have e2 : ∀ᶠ u : Rˣ in 𝓝 1, ((u⁻¹ : Rˣ) : R) ∈ V :=
      Units.continuous_coe_inv.continuousAt.eventually
        (show V ∈ 𝓝 (((1 : Rˣ)⁻¹ : Rˣ) : R) by simpa using hV)
    filter_upwards [e2] with u hu
    have := h _ hu
    rw [map_inv] at this
    exact (inv_lt_inv₀ distribHaarChar_pos hap).1 this
  · intro c hc
    obtain ⟨V, hV, h⟩ := hup c hc
    have e1 : ∀ᶠ u : Rˣ in 𝓝 1, (u : R) ∈ V :=
      Units.continuous_val.continuousAt.eventually (show V ∈ 𝓝 ((1 : Rˣ) : R) by simpa using hV)
    filter_upwards [e1] with u hu using h u hu

theorem modu_units (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [LocallyCompactSpace S] (u : Sˣ) : modu S (u : S) = distribHaarChar S u := by
  simp [modu]

theorem modu_basic : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], (∀ u : S, IsUnit u → 0 < modu S u ∧ ∀ ν : Measure S, ν.IsAddHaarMeasure → ν = modu S u • ν.map (fun z => u * z)) ∧ (∀ u w : S, IsUnit u → IsUnit w → modu S (u * w) = modu S u * modu S w) ∧ modu S 1 = 1 ∧ (IsOpenUnits S → ContinuousOn (modu S) {u | IsUnit u}) := by
  intro S _ _ _ _ _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    rw [modu_units]
    refine ⟨distribHaarChar_pos, fun ν hν => ?_⟩
    ext s hs
    have e : (fun z : S => (u : S) * z) ⁻¹' s = u⁻¹ • s := by
      ext z
      rw [Set.mem_inv_smul_set_iff]; rfl
    rw [Measure.smul_apply, Measure.map_apply (measurable_const_mul _) hs, e, ENNReal.smul_def,
      smul_eq_mul, distribHaarChar_mul, smul_inv_smul]
  · rintro _ _ ⟨u, rfl⟩ ⟨w, rfl⟩
    rw [← Units.val_mul, modu_units, modu_units, modu_units, map_mul]
  · rw [← Units.val_one, modu_units, map_one]
  · intro hS
    rintro _ ⟨u, rfl⟩
    have hoe : IsOpenEmbedding (Units.val : Sˣ → S) := IsOpenUnits.isOpenEmbedding_unitsVal
    refine ContinuousAt.continuousWithinAt ?_
    rw [← hoe.continuousAt_iff]
    have : modu S ∘ Units.val = fun u : Sˣ => distribHaarChar S u := funext (modu_units S)
    rw [this]
    exact (continuous_distribHaarChar_units S).continuousAt

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeProdFormula

theorem card_residue (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  obtain ⟨a, ha⟩ := GlobalTheory.HaarLatticeScale.exists_valued_eq_exp F v (-1)
  have ha1 : a ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp _).2 ha.le).le
  have h := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 ⟨a, ha1⟩ 1
    (by simpa using ha)
  have e : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {⟨a, ha1⟩} := by
    ext y
    rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v
      (by change Valued.v a ≠ 0; rw [ha]; exact WithZero.exp_ne_zero)]
    change _ ↔ _ ≤ Valued.v a
    rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  rw [pow_one, ← e] at h
  exact h

theorem modu_finite (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v)
    (hx : x ≠ 0) : (modu (Fv F v) x : ℝ) = ‖x‖ := by
  have hu : IsUnit x := hx.isUnit
  have hv : Valued.v x ≠ 0 := by simpa using hx
  let μ : Measure (Fv F v) := Measure.addHaar
  have h := GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp F v (Fv F v) μ Unit
    (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm (WithZero.log (Valued.v x))
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have e0 : (v.adicCompletionIntegers F : Set (Fv F v)) = Metric.closedBall 0 1 := by
    ext y
    rw [mem_closedBall_zero_iff, Valued.toNormedField.norm_le_one_iff]
    rfl
  have h0 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
  have h1 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ ∞ := by
    rw [e0]; exact (isCompact_closedBall _ _).measure_lt_top.ne
  have e1 : {y : Fv F v | ∀ i, Valued.v ((ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i) ≤
      WithZero.exp (WithZero.log (Valued.v x))} = hu.unit • (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, WithZero.exp_log hv, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul,
      Units.val_inv_eq_inv_val, map_inv₀, IsUnit.unit_spec, inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
    simp
  have e2 : {y : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i ∈
      v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp
  rw [e1, e2, Measure.real, ← distribHaarChar_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, card_residue,
    Fintype.card_unit, pow_one] at h
  have h2 := mul_right_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h
  rw [modu, dite_eq_left hu, h2, FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  push_cast
  congr 1

theorem distribHaarChar_pi_real (ι : Type) [Fintype ι] (u : (ι → ℝ)ˣ) :
    (distribHaarChar (ι → ℝ) u : ℝ) = ∏ i, |(u : ι → ℝ) i| := by
  have hu : ∀ i, (u : ι → ℝ) i ≠ 0 := fun i => ((Pi.isUnit_iff.1 u.isUnit) i).ne_zero
  have hp : (volume : Measure (ι → ℝ)) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) = 1 := by
    rw [volume_pi_pi]; simp
  have e : u • (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) =
      Set.univ.pi fun i => (u : ι → ℝ) i • Set.Icc (0 : ℝ) 1 := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hu i), Units.smul_def, smul_eq_mul, smul_eq_mul, Pi.mul_apply]
    have : ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i = ((u : ι → ℝ) i)⁻¹ :=
      eq_inv_of_mul_eq_one_left (congrFun u.inv_mul i)
    rw [this]
  rw [distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume)
    (s := Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) (r := ∏ i, ‖(u : ι → ℝ) i‖₊) (by rw [hp]; simp) (by rw [hp]; simp)]
  · simp
  · rw [hp, e, volume_pi_pi, mul_one, ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Measure.addHaar_smul]
    rw [Module.finrank_self, pow_one, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one,
      ← Real.enorm_eq_ofReal_abs]
    rfl

theorem modu_infinite (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ainf F) (hx : IsUnit x) :
    (modu (Ainf F) x : ℝ) = ∏ w : InfinitePlace F, ‖x w‖ := by
  let r : Ainf F ≃+* (InfinitePlace F → ℝ) := RingEquiv.piCongrRight fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  let e : Ainf F ≃ₜ+ (InfinitePlace F → ℝ) :=
    { r.toAddEquiv with
      continuous_toFun := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
          (continuous_apply w)
      continuous_invFun := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous.comp
          (continuous_apply w) }
  have h := GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e hx.unit
    (Units.map (r : Ainf F →* (InfinitePlace F → ℝ)) hx.unit) (fun y => map_mul r x y)
  rw [modu, dite_eq_left hx, ← h, distribHaarChar_pi_real]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal w)).norm_map_of_map_zero (map_zero _) (x w)

theorem prod_modu_eq_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : F), e ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v) (algebraMap F (Fv F v) e)).Finite ∧ modu (Ainf F) (algebraMap F (Ainf F) e) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) = 1 := by
  intro F _ _ _ e he
  have hf : ∀ v : HeightOneSpectrum (𝓞 F), (modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ) =
      FinitePlace.equivHeightOneSpectrum.symm v e := fun v => by
    rw [modu_finite F v _ ((map_ne_zero _).2 he)]
    rfl
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      modu (Fv F v) (algebraMap F (Fv F v) e)).Finite := by
    refine ((FinitePlace.hasFiniteMulSupport he).preimage
      (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn).subset fun v hv h => hv ?_
    apply NNReal.coe_injective
    rw [hf]
    exact h
  refine ⟨hfin, NNReal.coe_injective ?_⟩
  have h1 : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ≥0) : ℝ) =
      ∏ᶠ w : FinitePlace F, w e := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [← hf]
    exact (NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.map_finprod hfin
  rw [NNReal.coe_mul, h1, modu_infinite F _ (he.isUnit.map _), NNReal.coe_one, ← prod_abs_eq_one he]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 e)

end GlobalTheory.GaugeProdFormula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyRealStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarModulus_product_formula_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : F), e ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v) (algebraMap F (Fv F v) e)).Finite ∧ modu (Ainf F) (algebraMap F (Ainf F) e) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) = 1 := by
  first | exact @GlobalTheory.GaugeProdFormula.prod_modu_eq_one | exact GlobalTheory.GaugeProdFormula.prod_modu_eq_one | (intros; apply GlobalTheory.GaugeProdFormula.prod_modu_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeGlue

theorem polishSpace_addCommGroup (G : Type) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    PolishSpace G := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace G
  haveI : (uniformity G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem repr_map (φ : R →ₐ[F] R') (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem tens_ext {z z' : R ⊗[F] E} (h : ∀ k, (Algebra.TensorProduct.basis R b).repr z k =
    (Algebra.TensorProduct.basis R b).repr z' k) : z = z' :=
  (Algebra.TensorProduct.basis R b).ext_elem h

theorem exists_repr (c : Fin d → R) :
    ∃ z : R ⊗[F] E, ∀ k, (Algebra.TensorProduct.basis R b).repr z k = c k :=
  ⟨(Algebra.TensorProduct.basis R b).equivFun.symm c, fun k => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩

include b in
theorem continuous_map [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) :
    Continuous (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have h1 : Continuous (Algebra.TensorProduct.basis R b).equivFun :=
    IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  have h2 : Continuous (Algebra.TensorProduct.basis R' b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R' b).equivFun.symm.toLinearMap
  have h3 : Continuous fun z : R ⊗[F] E => fun k => φ ((Algebra.TensorProduct.basis R b).equivFun z k) :=
    continuous_pi fun k => hφ.comp ((continuous_apply k).comp h1)
  refine (h2.comp h3).congr fun z => ?_
  simp only [Function.comp_apply]
  rw [LinearEquiv.symm_apply_eq]
  funext k
  simp only [Module.Basis.equivFun_apply, repr_map]

end Coord

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) {n M : ℕ}

theorem repr_projInf (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).1 :=
  repr_map b (fstA F) _ k

theorem repr_projV (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n)
    (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 v :=
  (repr_map b (evalV F v) _ k).trans (congrArg (evalV F v) (repr_map b (sndA F) _ k))

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

theorem continuous_sndA : Continuous (sndA F) := continuous_snd

theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval v

theorem adele_ext {x y : AF F} (h1 : x.1 = y.1) (h2 : ∀ v, x.2 v = y.2 v) : x = y :=
  Prod.ext h1 (RestrictedProduct.ext _ _ h2)

theorem exists_adele (x : Ainf F) (y : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (hy : ∀ᶠ v in Filter.cofinite, y v ∈ v.adicCompletionIntegers F) :
    ∃ z : AF F, z.1 = x ∧ ∀ v, z.2 v = y v :=
  ⟨pairA F x ⟨y, hy⟩, rfl, fun _ => rfl⟩

include b in
theorem continuous_projInf : Continuous (projInf (F := F) (E := E) (M := M) (n := n)) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_map b (fstA F) continuous_fstA).comp
      ((continuous_apply i).comp (continuous_apply a))

include b in
theorem continuous_projV (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_map b (evalV F v) (continuous_evalV v)).comp
      ((continuous_map b (sndA F) continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a)))

include b in
theorem injective_glue : Function.Injective (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) := by
  intro X X' h
  have h1 : projInf X = projInf X' := congrArg Prod.fst h
  have h2 : ∀ v, projV v (projFin X) = projV v (projFin X') := congrFun (congrArg Prod.snd h)
  funext a i
  refine tens_ext b fun k => adele_ext ?_ fun v => ?_
  · rw [← repr_projInf, ← repr_projInf, h1]
  · rw [← repr_projV, ← repr_projV, h2]

theorem range_glue : Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) =
    {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} := by
  ext Y
  constructor
  · rintro ⟨X, rfl⟩
    have : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ a i k,
        ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 v ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k =>
        ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2.2
    filter_upwards [this] with v hv a i k
    rw [repr_projV]
    exact hv a i k
  · intro hY
    choose c hc1 hc2 using fun (a : Fin n) (i : Fin M) (k : Fin d) =>
      exists_adele ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y.1 a i) k)
        (fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Y.2 v a i) k)
        (Filter.Eventually.mono hY fun v hv => hv a i k)
    choose X hX using fun a i => exists_repr b (c a i)
    have h1 : projInf X = Y.1 := by
      funext a i
      refine tens_ext b fun k => ?_
      rw [repr_projInf, hX, hc1]
    have h2 : ∀ v, projV v (projFin X) = Y.2 v := fun v => by
      funext a i
      refine tens_ext b fun k => ?_
      rw [repr_projV, hX, hc2]
    exact ⟨X, Prod.ext h1 (funext h2)⟩

end Adele

theorem adelicTuple_measurableEmbedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), MeasurableEmbedding (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) ∧ Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) = {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} ∧ Continuous (projInf (F := F) (E := E) (M := M) (n := n)) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) := by
  intro F E _ _ _ _ _ d b n M
  refine ⟨?_, range_glue b, continuous_projInf b, continuous_projV b⟩
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : PolishSpace (Fin n → Fin M → AF F ⊗[F] E) := polishSpace_addCommGroup _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (Fv F v ⊗[F] E) := fun v =>
    inferInstance
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v =>
    inferInstance
  haveI : BorelSpace (∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E) :=
    Pi.borelSpace
  haveI : BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := inferInstance
  exact ((continuous_projInf b).prodMk (continuous_pi (continuous_projV b))).measurableEmbedding
    (injective_glue b)

end GlobalTheory.GaugeGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponentsStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), MeasurableEmbedding (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) ∧ Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) = {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} ∧ Continuous (projInf (F := F) (E := E) (M := M) (n := n)) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) := by
  first | exact @GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding | exact GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding | (intros; apply GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_local_sqrt_nontrivial (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) :
    ∃ U : Set K, IsOpen U ∧ (1 : K) ∈ U ∧ ∃ s : K → K, ContinuousOn s U ∧ s 1 = 1 ∧
      ∀ u ∈ U, s u * s u = u := by
  have hd : HasStrictDerivAt (fun x : K => x * x) 2 1 := by
    have := (hasStrictDerivAt_id (1 : K)).mul (hasStrictDerivAt_id (1 : K))
    have h11 : (1 : K) * id 1 + id 1 * 1 = 2 := by simp; norm_num
    rw [h11] at this
    exact this
  have hF := hd.hasStrictFDerivAt_equiv h2
  let e := hF.toOpenPartialHomeomorph
  have he : ∀ x, e x = x * x := fun x => rfl
  have h1 : (1 : K) ∈ e.source := hF.mem_toOpenPartialHomeomorph_source
  have h1' : e 1 = 1 := by rw [he, mul_one]
  refine ⟨e.target, e.open_target, h1' ▸ e.map_source h1, e.symm, e.continuousOn_symm, ?_, ?_⟩
  · have := e.left_inv h1
    rwa [h1'] at this
  · intro u hu
    rw [← he]; exact e.right_inv hu

theorem exists_local_sqrt (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) :
    ∃ U : Set K, IsOpen U ∧ (1 : K) ∈ U ∧ ∃ s : K → K, ContinuousOn s U ∧ s 1 = 1 ∧
      ∀ u ∈ U, s u * s u = u := by
  by_cases h : ∃ x : K, 1 < ‖x‖
  · let : NontriviallyNormedField K := { (inferInstance : NormedField K) with non_trivial := h }
    exact exists_local_sqrt_nontrivial K h2
  · push Not at h
    refine ⟨Metric.ball 1 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun _ => 1,
      continuousOn_const, rfl, fun u hu => ?_⟩
    rw [mem_ball_iff_norm] at hu
    by_contra hne
    have h0 : u - 1 ≠ 0 := fun h0 => hne (by rw [sub_eq_zero.1 h0, mul_one])
    have h3 := h (u - 1)⁻¹
    rw [norm_inv, inv_le_one₀ (norm_pos_iff.2 h0)] at h3
    exact absurd hu (not_lt.2 h3)

theorem nice_field (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) : Nice K :=
  ⟨inferInstance, inferInstance, inferInstance, exists_local_sqrt K h2⟩

theorem nice_pi {ι : Type} [Fintype ι] (K : ι → Type) [∀ i, NormedField (K i)]
    [∀ i, CompleteSpace (K i)] (h2 : ∀ i, (2 : K i) ≠ 0) : Nice (∀ i, K i) := by
  refine ⟨inferInstance, inferInstance, ⟨Units.isOpenEmbedding_val⟩, ?_⟩
  choose U hU h1 s hs hs1 hss using fun i => exists_local_sqrt (K i) (h2 i)
  refine ⟨Set.univ.pi U, isOpen_set_pi Set.finite_univ fun i _ => hU i, fun i _ => h1 i,
    fun x i => s i (x i), ?_, funext fun i => hs1 i, fun u hu => funext fun i => hss i _ (hu i trivial)⟩
  exact continuousOn_pi.2 fun i => (hs i).comp (continuous_apply i).continuousOn
    fun x hx => hx i trivial

theorem nice_ainf_fv : ∀ (F : Type) [Field F] [NumberField F],
    Nice (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Nice (Fv F v) := by
  intro F _ _
  refine ⟨nice_pi (fun w : InfinitePlace F => w.Completion) fun w => ?_, fun v => nice_field _ ?_⟩
  · have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    exact two_ne_zero
  · have : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
    exact two_ne_zero

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesCompletStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNiceLocalFieldProductRing_infiniteAdeles_completions : ∀ (F : Type) [Field F] [NumberField F], Nice (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Nice (Fv F v) := by
  first | exact @GlobalTheory.GaugeEx.nice_ainf_fv | exact GlobalTheory.GaugeEx.nice_ainf_fv | (intros; apply GlobalTheory.GaugeEx.nice_ainf_fv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

def IsNeg (Y : Matrix (Ix P Q) (Fin Q) ℂ) : Prop := (-(Yᴴ * Jm P Q * Y)).PosDef

def matA (Y : Matrix (Ix P Q) (Fin Q) ℂ) : Matrix (Fin P) (Fin Q) ℂ := Y.toRows₁ * (Y.toRows₂)⁻¹

def linX (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) : Ix P Q → ℂ :=
  Sum.elim (v ∘ Sum.inl - matA Y *ᵥ (v ∘ Sum.inr)) ((φ ∘ Sum.inl) ᵥ* matA Y + φ ∘ Sum.inr)

def scal (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) : ℂ :=
  (Y.toRows₂.det)⁻¹ * Complex.exp (-((linX Y v φ ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr)))

def ker (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : Matrix (Ix P Q) (Fin Q) ℂ)
    (v' φ' : Ix P Q → ℂ) : ℂ :=
  ((-(Yᴴ * Jm P Q * Y')).det)⁻¹ * Complex.exp ((star v ᵥ* Jm P Q) ⬝ᵥ v' -
    (star v ᵥ* Jm P Q + φ') ⬝ᵥ (Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q) *ᵥ (Jm P Q *ᵥ star φ + v'))

def baseY (A : Matrix (Fin P) (Fin Q) ℂ) : Matrix (Ix P Q) (Fin Q) ℂ := Matrix.fromRows A 1

def baseV (x : Ix P Q → ℂ) : Ix P Q → ℂ := Sum.elim (x ∘ Sum.inl) 0

def baseF (x : Ix P Q → ℂ) : Ix P Q → ℂ := Sum.elim 0 (x ∘ Sum.inr)

def dA (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) : Matrix (Fin P) (Fin Q) ℂ :=
  Z.toBlocks₁₁ * A + Z.toBlocks₁₂ - A * (Z.toBlocks₂₁ * A + Z.toBlocks₂₂)

def dX (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : Ix P Q → ℂ :=
  Sum.elim ((Z.toBlocks₁₁ - A * Z.toBlocks₂₁) *ᵥ (x ∘ Sum.inl))
    (-((x ∘ Sum.inr) ᵥ* (Z.toBlocks₂₁ * A + Z.toBlocks₂₂)))

def dS (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : ℂ :=
  -(Z.toBlocks₂₁ * A + Z.toBlocks₂₂).trace - (x ∘ Sum.inr) ⬝ᵥ Z.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)

theorem toRows₂_baseY (A : Matrix (Fin P) (Fin Q) ℂ) : (baseY A).toRows₂ = 1 := rfl

theorem matA_baseY (A : Matrix (Fin P) (Fin Q) ℂ) : matA (baseY A) = A := by
  simp [matA, baseY]

theorem linX_base (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : linX (baseY A) (baseV x) (baseF x) = x := by
  have h1 : baseV x ∘ Sum.inr = 0 := rfl
  have h2 : baseF x ∘ Sum.inl = 0 := rfl
  rw [linX, h1, h2]
  ext (i | j) <;> simp [baseV, baseF]

theorem scal_base (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : scal (baseY A) (baseV x) (baseF x) = 1 := by
  have h1 : baseV x ∘ Sum.inr = 0 := rfl
  simp [scal, h1, toRows₂_baseY]

theorem form_blocks (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) :
    -(Yᴴ * Jm P Q * Y') = Y.toRows₂ᴴ * Y'.toRows₂ - Y.toRows₁ᴴ * Y'.toRows₁ := by
  conv_lhs => rw [← Matrix.fromRows_toRows Y, ← Matrix.fromRows_toRows Y']
  rw [Jm, Formalism.UG.Jpq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

theorem frame_eq (Y : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det) :
    Y = baseY (matA Y) * Y.toRows₂ := by
  rw [baseY, Matrix.fromRows_mul, matA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one,
    Matrix.one_mul, Matrix.fromRows_toRows]

theorem form_factor (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det) (h' : IsUnit Y'.toRows₂.det) :
    -(Yᴴ * Jm P Q * Y') = Y.toRows₂ᴴ * (1 - (matA Y)ᴴ * matA Y') * Y'.toRows₂ := by
  have e : ∀ Y : Matrix (Ix P Q) (Fin Q) ℂ, IsUnit Y.toRows₂.det → matA Y * Y.toRows₂ = Y.toRows₁ := fun Y h => by
    rw [matA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one]
  rw [form_blocks, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
    e Y h, Matrix.mul_assoc, e Y' h']

theorem isNeg_baseY {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) : IsNeg (baseY A) := by
  rw [IsNeg, form_blocks]
  simpa [baseY] using h

theorem IsNeg.isUnit {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) : IsUnit Y.toRows₂.det := by
  rw [IsNeg, form_blocks] at h
  have h2 := h.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self Y.toRows₁)
  rw [sub_add_cancel] at h2
  have h3 := h2.isUnit
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h3
  exact isUnit_of_mul_isUnit_right h3

theorem IsNeg.posDef {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) : (1 - (matA Y)ᴴ * matA Y).PosDef := by
  have hu := h.isUnit
  rw [IsNeg, form_factor Y Y hu hu] at h
  have hu' : IsUnit Y.toRows₂ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  exact (hu'.posDef_star_left_conjugate_iff).1 h

theorem form_mul {g : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) :
    (g * Y)ᴴ * Jm P Q * (g * Y') = Yᴴ * Jm P Q * Y' := by
  rw [Matrix.conjTranspose_mul]
  conv_rhs => rw [← hg]
  simp only [Matrix.mul_assoc]

theorem IsNeg.mul {g : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) :
    IsNeg (g * Y) := by
  rwa [IsNeg, form_mul hg]

theorem Jm_mul_Jm : Jm P Q * Jm P Q = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem ker_mul {g g' : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) (hg' : g' * g = 1)
    (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : Ix P Q → ℂ) :
    ker (g * Y) (g *ᵥ v) (φ ᵥ* g') (g * Y') (g *ᵥ v') (φ' ᵥ* g') = ker Y v φ Y' v' φ' := by
  have hg2 : g * g' = 1 := mul_eq_one_comm.1 hg'
  have h1 : gᴴ * Jm P Q = Jm P Q * g' := by
    conv_rhs => rw [← hg, Matrix.mul_assoc, hg2, Matrix.mul_one]
  have h0 : g' = Jm P Q * gᴴ * Jm P Q := by
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have hJ : (Jm P Q)ᴴ = Jm P Q := by simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h2 : Jm P Q * g'ᴴ = g * Jm P Q := by
    rw [h0, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have e1 : star (g *ᵥ v) ᵥ* Jm P Q = (star v ᵥ* Jm P Q) ᵥ* g' := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h1]
  have e2 : Jm P Q *ᵥ star (φ ᵥ* g') = g *ᵥ (Jm P Q *ᵥ star φ) := by
    rw [Matrix.star_vecMul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2]
  have e3 : g * Y' * (Yᴴ * Jm P Q * Y')⁻¹ * (g * Y)ᴴ * Jm P Q =
      g * (Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q) * g' := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, h1]
  have e4 : ∀ (u w : Ix P Q → ℂ) (M : Mat P Q), (u ᵥ* g') ⬝ᵥ (g * M * g') *ᵥ (g *ᵥ w) = u ⬝ᵥ M *ᵥ w := by
    intro u w M
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg', Matrix.one_mul, Matrix.mul_assoc, hg', Matrix.mul_one]
  rw [ker, ker, form_mul hg, e1, e2, e3, ← Matrix.add_vecMul, ← Matrix.mulVec_add, e4, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]

end GlobalTheory.OscGauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
noncomputable section

namespace GlobalTheory.GaugeEx.IntBasis

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem ev_int (a : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  have h := (algebraMap F (Af F) a).2
  filter_upwards [h] with v hv
  exact hv

theorem _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord {d : ℕ}
    (b : Module.Basis (Fin d) F E) (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b.repr e k) ∈ v.adicCompletionIntegers F := by
  rw [Filter.eventually_all]
  intro k
  exact RestrictedProduct.eventually _ _ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr e k))

theorem eq_sum {d : ℕ} (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R]
    (y : R ⊗[F] E) :
    y = ∑ i, (Algebra.TensorProduct.basis R b).repr y i ⊗ₜ[F] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

private theorem mem_intV_iff_basis_repr_mem_integers (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    y ∈ _root_.GlobalTheory.GaugeEx.intV b v ↔
      ∀ k, (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).repr y k ∈
        v.adicCompletionIntegers F := by
  unfold _root_.GlobalTheory.GaugeEx.intV
  rfl

theorem _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem {r : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v}
    (hr : r ∈ v.adicCompletionIntegers F) {e : E}
    (he : ∀ k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b.repr e k) ∈ v.adicCompletionIntegers F) :
    r ⊗ₜ[F] e ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
    smul_eq_mul]
  exact mul_mem hr (he k)

theorem _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' {ι : Type} (s : Finset ι)
    (f : ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) (hf : ∀ i ∈ s, f i ∈ _root_.GlobalTheory.GaugeEx.intV b v) :
    ∑ i ∈ s, f i ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun i hi => (mem_intV_iff_basis_repr_mem_integers b v (f i)).1 (hf i hi) k

theorem compact_open : IsCompact (intV b v) ∧ IsOpen (intV b v) := by
  let l := (Algebra.TensorProduct.basis (Fv F v) b).equivFun
  have h1 : Continuous l := IsModuleTopology.continuous_of_linearMap l.toLinearMap
  have h2 : Continuous l.symm := by
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
    exact IsModuleTopology.continuous_of_linearMap l.symm.toLinearMap
  let e : (Fv F v ⊗[F] E) ≃ₜ (Fin d → Fv F v) := ⟨l.toEquiv, h1, h2⟩
  have he : intV b v = e ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
    rfl
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
    exact isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  rw [he]
  exact ⟨e.isCompact_preimage.2 (isCompact_univ_pi fun _ => hc),
    (isOpen_set_pi Set.finite_univ fun _ _ => ho).preimage e.continuous⟩

private theorem eventually_basis_repr_mem_adicCompletionIntegers {ι : Type} [Finite ι] (e : ι → E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w) (b.repr (e i) k) ∈ w.adicCompletionIntegers F :=
  Filter.eventually_all.2 fun i => _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b (e i)

private theorem eq_sum_basis_repr_tmul_basis (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    y = ∑ k, (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).repr y k ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).sum_repr y]
  simp only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem zero_mem_intV : (0 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  rw [map_zero, Finsupp.zero_apply]
  exact zero_mem _

private theorem add_mem_intV {y z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E}
    (hy : y ∈ _root_.GlobalTheory.GaugeEx.intV b v) (hz : z ∈ _root_.GlobalTheory.GaugeEx.intV b v) :
    y + z ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers] at hy hz ⊢
  intro k
  rw [map_add (f := _), Finsupp.add_apply]
  exact add_mem (hy k) (hz k)

private theorem intV_subset_intV_of_basis_repr_integral {d' : ℕ} (b' : Module.Basis (Fin d') F E)
    (h : ∀ i k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b'.repr (b i) k) ∈ v.adicCompletionIntegers F) :
    _root_.GlobalTheory.GaugeEx.intV b v ⊆ _root_.GlobalTheory.GaugeEx.intV b' v := by
  intro y hy
  rw [eq_sum_basis_repr_tmul_basis b v y]
  exact _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b' v _ _ fun i _ =>
    _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b' v
      ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy i) (h i)

theorem _root_.GlobalTheory.GaugeEx.IntBasis.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ v : HeightOneSpectrum (𝓞 F), IsCompact (_root_.GlobalTheory.GaugeEx.intV b v) ∧ IsOpen (_root_.GlobalTheory.GaugeEx.intV b v)) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) ∈ _root_.GlobalTheory.GaugeEx.intV b v ∧ (∀ y ∈ _root_.GlobalTheory.GaugeEx.intV b v, ∀ z ∈ _root_.GlobalTheory.GaugeEx.intV b v, y * z ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ ∀ y ∈ _root_.GlobalTheory.GaugeEx.intV b v, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ y ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ (∀ z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, _root_.GlobalTheory.GaugeEx.prV v z ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, _root_.GlobalTheory.GaugeEx.intV b v = _root_.GlobalTheory.GaugeEx.intV b' v := by
  intro F E _ _ _ _ _ σ d b
  refine ⟨fun v => ?_, ?_, fun z => ?_, fun d' b' => ?_⟩
  · let φ := (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).equivFun
    have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ.toLinearMap
    have hφs : Continuous φ.symm := IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap
    let h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E ≃ₜ (Fin d → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :=
      { φ.toEquiv with continuous_toFun := hφ, continuous_invFun := hφs }
    have hS : _root_.GlobalTheory.GaugeEx.intV b v =
        h ⁻¹' Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))) := by
      ext y
      rw [mem_intV_iff_basis_repr_mem_integers]
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      rfl
    have hO : IsCompact (v.adicCompletionIntegers F : Set (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) :=
      isCompact_iff_compactSpace.mpr (_root_.GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
    rw [hS]
    exact ⟨h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hO),
      (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_integer _).preimage h.continuous⟩
  · filter_upwards [_root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b (1 : E),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun p : Fin d × Fin d => b p.1 * b p.2),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun k => σ (b k))] with v hv1 hv2 hv3
    refine ⟨?_, ?_, ?_⟩
    · rw [Algebra.TensorProduct.one_def]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v (one_mem _) hv1
    · intro y hy z hz
      rw [eq_sum_basis_repr_tmul_basis b v y, eq_sum_basis_repr_tmul_basis b v z, Finset.sum_mul_sum]
      refine _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun k _ =>
        _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun l _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v
        (mul_mem ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy k)
          ((mem_intV_iff_basis_repr_mem_integers b v z).1 hz l)) (hv2 (k, l))
    · intro y hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [eq_sum_basis_repr_tmul_basis b v y, map_sum]
      refine _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun k _ => ?_
      simp only [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v
        ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy k) (hv3 k)
  · induction z using TensorProduct.induction_on with
    | zero =>
      exact Filter.Eventually.of_forall fun v => by
        rw [map_zero]
        exact zero_mem_intV b v
    | tmul a e =>
      filter_upwards [RestrictedProduct.eventually _ _ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F a),
        _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b e] with v ha he
      simp only [_root_.GlobalTheory.GaugeEx.prV, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v ha he
    | add x y hx hy =>
      filter_upwards [hx, hy] with v hxv hyv
      rw [map_add (f := _)]
      exact add_mem_intV b v hxv hyv
  · filter_upwards [eventually_basis_repr_mem_adicCompletionIntegers b' (fun k => b k),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun k => b' k)] with v h h'
    exact Set.Subset.antisymm (intV_subset_intV_of_basis_repr_integral b v b' h)
      (intV_subset_intV_of_basis_repr_integral b' v b h')

end GlobalTheory.GaugeEx.IntBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorPropertiesStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralPointsFinitePlaceTensor_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ v : HeightOneSpectrum (𝓞 F), IsCompact (intV b v) ∧ IsOpen (intV b v)) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (1 : Fv F v ⊗[F] E) ∈ intV b v ∧ (∀ y ∈ intV b v, ∀ z ∈ intV b v, y * z ∈ intV b v) ∧ ∀ y ∈ intV b v, sigR (Fv F v) σ y ∈ intV b v) ∧ (∀ z : AF F ⊗[F] E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, prV v z ∈ intV b v) ∧ ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, intV b v = intV b' v := by
  first | exact @GlobalTheory.GaugeEx.IntBasis.main | exact GlobalTheory.GaugeEx.IntBasis.main | (intros; apply GlobalTheory.GaugeEx.IntBasis.main <;> assumption)
end
end
