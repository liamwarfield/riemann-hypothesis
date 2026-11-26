module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ZDom
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UMeasEx

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AdelicSL2.IsOpenEmbeddingProjection
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal
private theorem continuous_gl' : Continuous (gl : G1 ℚ → GL (Fin 2) (A ℚ)) := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  have h : (fun g : G1 ℚ => (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun g : G1 ℚ => ((g⁻¹ : G1 ℚ) : Matrix (Fin 2) (Fin 2) (A ℚ)) := by
    funext g
    have : (gl g)⁻¹ = gl g⁻¹ := by
      rw [inv_eq_iff_mul_eq_one]
      exact Units.ext (by
        change (g : Matrix (Fin 2) (Fin 2) (A ℚ)) * ((g⁻¹ : G1 ℚ) : Matrix (Fin 2) (Fin 2) (A ℚ)) = 1
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one])
    rw [this]
    rfl
  rw [show (fun x : G1 ℚ => ((((gl x)⁻¹ : GL (Fin 2) (A ℚ))) : Matrix (Fin 2) (Fin 2) (A ℚ))) = _ from h]
  exact continuous_subtype_val.comp (continuous_inv : Continuous fun g : G1 ℚ => g⁻¹)

private theorem dM_inv' (t : (A ℚ)ˣ) : (dM t)⁻¹ = dM t⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← dM_mul, mul_inv_cancel]
  apply Units.ext
  change !![1, 0; 0, ((1 : (A ℚ)ˣ) : A ℚ)] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem continuous_dM_val : Continuous (fun t : (A ℚ)ˣ => ((dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) := by
  have h : (fun t : (A ℚ)ˣ => ((dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun t : (A ℚ)ˣ => !![1, 0; 0, (t : A ℚ)] := rfl
  rw [h]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact Units.continuous_val

private theorem continuous_dM' : Continuous (dM : (A ℚ)ˣ → GL (Fin 2) (A ℚ)) := by
  refine Units.continuous_iff.2 ⟨continuous_dM_val, ?_⟩
  have h : (fun t : (A ℚ)ˣ => (((dM t)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun t : (A ℚ)ˣ => ((dM t⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) := by
    funext t
    rw [dM_inv']
  exact h ▸ (continuous_dM_val.comp continuous_inv)

private theorem det_dM' (t : (A ℚ)ˣ) : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (dM t) = t := by
  have h := det_el 1 t
  simpa using h

private theorem det_rest (x : GL (Fin 2) (A ℚ)) :
    Matrix.det (((x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹ : GL (Fin 2) (A ℚ))) : Matrix (Fin 2) (Fin 2) (A ℚ)) = 1 := by
  have h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹) = 1 := by
    rw [map_mul, map_inv, det_dM', mul_inv_cancel]
  have := congrArg Units.val h
  rwa [GroundTheory.Automorphic.AdelicGLn.coe_det] at this

private noncomputable def rt (x : GL (Fin 2) (A ℚ)) : G1 ℚ × (A ℚ)ˣ :=
  (⟨((x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)), det_rest x⟩,
    GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x)

private theorem continuous_rt : Continuous rt := by
  have hd := GroundTheory.Automorphic.AdelicGLn.continuous_det ℚ 2
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hd
  exact Units.continuous_val.comp (continuous_id.mul (continuous_dM'.comp hd).inv)

private theorem rt_pre : Function.LeftInverse rt (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) := by
  rintro ⟨g, t⟩
  refine Prod.ext (Subtype.ext ?_) (det_el g t)
  change (((gl g * dM t) * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (gl g * dM t)))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = (g : Matrix (Fin 2) (Fin 2) (A ℚ))
  rw [det_el, mul_inv_cancel_right]
  rfl

private theorem pos_of_UU {t : (A ℚ)ˣ} (ht : t ∈ UU) : t ∈ RationalIdeles.positiveSubgroup := by
  have hi : (t⁻¹ : (A ℚ)ˣ) ∈ UU := US.inv_mem (show t ∈ US from ht)
  refine RationalIdeles.mem_positiveSubgroup.2 ⟨(IdeleGroup.mem_standardOpenSubgroup ℚ).2 fun v => ⟨?_, ?_⟩, ?_⟩
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (ht.2 v).le
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hi.2 v).le
  · rw [RationalIdeles.coe_realPart, ht.1, map_one]
    exact one_pos

private theorem UU_of_pos {t : (A ℚ)ˣ} (hp : t ∈ RationalIdeles.positiveSubgroup)
    (hm : ((IdeleGroup.ideleModule ℚ t : {r : ℝ // 0 < r}) : ℝ) = 1) : t ∈ UU := by
  have hr : (RationalIdeles.realPart t : ℝ) = 1 := by
    rw [← GroundTheory.Automorphic.GL2Classical.ideleModule_eq_realPart_of_mem hp, hm]
  obtain ⟨hs, -⟩ := RationalIdeles.mem_positiveSubgroup.1 hp
  refine ⟨RationalIdeles.realEquiv.injective ?_, fun v => ?_⟩
  · rw [map_one, ← RationalIdeles.coe_realPart, hr]
  · obtain ⟨ha, hb⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 hs v
    have ha' : Valued.v (H.cp v (t : A ℚ)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha
    have hb' : Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb
    have hm1 : Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (t : A ℚ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    refine le_antisymm ha' ?_
    calc (1 : _) = Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (t : A ℚ)) := hm1.symm
      _ ≤ Valued.v (H.cp v (t : A ℚ)) := mul_le_of_le_one_left' hb'

theorem UpperTheory.isOpenEmbedding_projection :
    IsOpenEmbedding pm := by
  have hf : Topology.IsEmbedding (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) :=
    Function.LeftInverse.isEmbedding rt_pre continuous_rt
      ((continuous_gl'.comp continuous_fst).mul (continuous_dM'.comp continuous_snd))
  have hu : Topology.IsEmbedding (Prod.map id Subtype.val : G1 ℚ × US → G1 ℚ × (A ℚ)ˣ) :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  have he : (Subtype.val ∘ pm : G1 ℚ × US → GL (Fin 2) (A ℚ)) =
      (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) ∘ (Prod.map id Subtype.val : G1 ℚ × US → G1 ℚ × (A ℚ)ˣ) := by
    funext p
    rfl
  have hc : Topology.IsEmbedding (Subtype.val ∘ pm : G1 ℚ × US → GL (Fin 2) (A ℚ)) := by
    rw [he]
    exact hf.comp hu
  have hp : Continuous pm := Continuous.subtype_mk hc.continuous _
  refine ⟨Topology.IsEmbedding.of_comp hp continuous_subtype_val hc, ?_⟩
  have hs : Set.range pm = (fun x : GG => GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ))) ⁻¹'
      (RationalIdeles.positiveSubgroup : Set (IdeleGroup ℚ)) := by
    rw [range_pm]
    ext x
    refine ⟨fun h => pos_of_UU h, fun h => UU_of_pos h ?_⟩
    exact GroundTheory.Automorphic.Reduction.mem_normOneGL.1 x.2
  rw [hs]
  exact RationalIdeles.isOpen_positiveSubgroup.preimage
    ((GroundTheory.Automorphic.AdelicGLn.continuous_det ℚ 2).comp continuous_subtype_val)
end

section -- merged from Development.AutomorphicArithmetic.AdelicSL2.ExistsHaarRestrictRangeSl2IdeleMapEqSmulProd
section -- merged from Development.AutomorphicArithmetic.AdelicSL2.ExistsHaarRestrictRangeEqSmulMapOfInvariant
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

theorem UpperTheory.exists_haar_restrict_range_eq_smul_map_of_invariant :
    ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (e : X → G) (ν : Measure X) [IsFiniteMeasureOnCompacts ν], IsOpenEmbedding e → (1 : G) ∈ Set.range e → (∀ a ∈ Set.range e, ∀ b ∈ Set.range e, a * b ∈ Set.range e) → (∀ a ∈ Set.range e, a⁻¹ ∈ Set.range e) → ν ≠ 0 → (∀ x, ∃ T : X → X, MeasurePreserving T ν ν ∧ ∀ y, e x * e y = e (T y)) → ∃ c : ℝ≥0, μ.restrict (Set.range e) = c • ν.map e := by
  intro G X _ _ _ _ _ _ _ _ μ _ _ _ _ e ν _ he h1 hmul hinv hν hT
  let H : Subgroup G :=
    { carrier := Set.range e
      mul_mem' := fun ha hb => hmul _ ha _ hb
      one_mem' := h1
      inv_mem' := fun ha => hinv _ ha }
  have hHo : IsOpen (H : Set G) := he.isOpen_range
  have hemb : IsOpenEmbedding (H.subtype) := hHo.isOpenEmbedding_subtypeVal
  haveI : LocallyCompactSpace H := hemb.locallyCompactSpace
  haveI hHaar : (μ.comap H.subtype).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) μ hemb
  have hme : MeasurableEmbedding (H.subtype) := hemb.measurableEmbedding
  let e' : X → H := fun x => ⟨e x, x, rfl⟩
  have he'c : Continuous e' := he.continuous.subtype_mk _
  have he'i : IsInducing e' :=
    (IsInducing.of_comp_iff (g := H.subtype) IsInducing.subtypeVal).mp he.isInducing
  have he'sur : Function.Surjective e' := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hval : H.subtype ∘ e' = e := rfl
  have hlamval : (ν.map e').map H.subtype = ν.map e := by
    rw [Measure.map_map hme.measurable he'c.measurable, hval]
  have hlam0 : ν.map e' ≠ 0 := by
    intro h0
    apply hν
    rw [← Measure.measure_univ_eq_zero]
    have := congrArg (fun m : Measure H => m Set.univ) h0
    simpa [Measure.map_apply he'c.measurable MeasurableSet.univ] using this
  haveI : IsFiniteMeasureOnCompacts (ν.map e') := ⟨fun K hK => by
    rw [Measure.map_apply he'c.measurable hK.measurableSet]
    exact (he'i.isCompact_preimage (by simp [he'sur.range_eq]) hK).measure_lt_top⟩
  haveI : (ν.map e').IsMulLeftInvariant := ⟨fun h => by
    obtain ⟨_, x, rfl⟩ := h
    obtain ⟨T, hTm, hTe⟩ := hT x
    rw [Measure.map_map (measurable_const_mul _) he'c.measurable]
    have hcomp : (fun y : H => (⟨e x, x, rfl⟩ : H) * y) ∘ e' = e' ∘ T :=
      funext fun y => Subtype.ext (hTe y)
    rw [hcomp, ← Measure.map_map he'c.measurable hTm.measurable, hTm.map_eq]⟩
  have key := Measure.isMulLeftInvariant_eq_smul (ν.map e') (μ.comap H.subtype)
  set c := Measure.haarScalarFactor (ν.map e') (μ.comap H.subtype) with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hlam0
    rw [key, h0, zero_smul]
  have hμH : μ.comap H.subtype = c⁻¹ • ν.map e' := by
    rw [key, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨c⁻¹, ?_⟩
  have hres : μ.restrict (Set.range e) = (μ.comap H.subtype).map H.subtype := by
    rw [hme.map_comap]
    congr 1
    simp [H]
    rfl
  rw [hres, hμH, Measure.map_smul, hlamval]
  exact hme.measurable.aemeasurable
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

theorem UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod :
    ∀ (M : Meas ℚ) (U : UMeas) (μ : Measure GG) [μ.IsHaarMeasure], ∃ c : ℝ≥0, μ.restrict (Set.range pm) = c • (M.μ.prod (us U)).map pm := by
  intro M U μ _
  haveI := M.haar
  haveI : SecondCountableTopology (G1 ℚ × US) := UpperTheory.isOpenEmbedding_projection.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (G1 ℚ) := inferInstance
  haveI : BorelSpace (G1 ℚ × US) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (M.μ.prod (us U)) := inferInstance
  refine UpperTheory.exists_haar_restrict_range_eq_smul_map_of_invariant GG (G1 ℚ × US) μ pm (M.μ.prod (us U)) UpperTheory.isOpenEmbedding_projection ?_ ?_ ?_ ?_ ?_
  · rw [range_pm]
    change GroundTheory.Automorphic.AdelicGLn.det ℚ 2 1 ∈ US
    rw [map_one]
    exact US.one_mem
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact ⟨_, (pm_mul p q).symm⟩
  · rw [range_pm]
    intro a ha
    change GroundTheory.Automorphic.AdelicGLn.det ℚ 2 ((a : GL (Fin 2) (A ℚ))⁻¹) ∈ US
    rw [map_inv]
    exact US.inv_mem ha
  · intro h0
    have h1 := congrArg (fun m : Measure (G1 ℚ × US) => m (Set.univ ×ˢ Set.univ)) h0
    simp only [Measure.prod_prod, measure_univ, mul_one, Measure.coe_zero, Pi.zero_apply] at h1
    exact (isOpen_univ.measure_ne_zero M.μ Set.univ_nonempty) h1
  · intro x
    refine ⟨Prod.map ((fun g => x.1 * g) ∘ cD (x.2 : (A ℚ)ˣ)) (fun t => x.2 * t), ?_, fun y => pm_mul x y⟩
    exact ((measurePreserving_mul_left M.μ x.1).comp (UpperTheory.ConvolutionTheory.R2.M.cdMeas ℚ M _)).prod (us_mul U x.2)
end

section -- merged from Development.AutomorphicArithmetic.AdelicSL2.IsFundamentalDomainImageSl2DomainProdIdeles
section -- merged from Development.AutomorphicArithmetic.AdelicSL2.ExistsGl2RatSmulMemRangeAdelicSL2IdeleMap
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

private lemma eq_one_of_mul' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma mem_UU_of_pos {y : IdeleGroup ℚ} (hy : y ∈ RationalIdeles.positiveSubgroup)
    (hm : (IdeleGroup.ideleModule ℚ y : ℝ) = 1) : y ∈ UU := by
  obtain ⟨h1, h2⟩ := RationalIdeles.mem_positiveSubgroup.1 hy
  rw [IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one,
    IdeleGroup.infiniteModule, Fintype.prod_unique,
    InfinitePlace.IsReal.mult_eq_one (RationalIdeles.isReal_infinitePlace default), pow_one] at hm
  refine ⟨?_, fun v => ?_⟩
  · have hn : ‖(RationalIdeles.realPart y : ℝ)‖ = 1 := by
      rw [RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply, ← hm]
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero
        (map_zero _) _
    rw [Real.norm_eq_abs, abs_of_pos h2, RationalIdeles.coe_realPart] at hn
    exact RationalIdeles.realEquiv.injective (hn.trans (map_one _).symm)
  · obtain ⟨ha, hb⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1 v
    refine eq_one_of_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) ?_
    rw [← map_mul]
    have h := congrArg (fun x : NumberField.AdeleRing (𝓞 ℚ) ℚ => x.2 v) (Units.mul_inv y)
    have h' : (y : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v *
        ((y⁻¹ : IdeleGroup ℚ) : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v = 1 := h
    exact (congrArg _ h').trans (map_one _)

theorem UpperTheory.exists_gl2Rat_smul_mem_range_adelicSL2IdeleMap :
    ∀ x : GG, ∃ γ : Ga, γ • x ∈ Set.range pm := by
  intro x
  obtain ⟨⟨q, y⟩, hq⟩ := RationalIdeles.mulMap_bijective.2
    (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ)))
  rw [RationalIdeles.mulMap_apply] at hq
  dsimp only at hq
  have hx := GroundTheory.Automorphic.Reduction.mem_normOneGL.1 x.2
  rw [← hq, map_mul, IdeleGroup.ideleModule_diagonal, one_mul] at hx
  have hy : (y : IdeleGroup ℚ) ∈ UU := mem_UU_of_pos y.2 hx
  obtain ⟨r, hr⟩ : ∃ r : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.det r = q⁻¹ := by
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, ((q⁻¹ : ℚˣ) : ℚ)] ?_, Units.ext ?_⟩
    · simp [Matrix.det_fin_two_of]
    · simp [Matrix.det_fin_two_of]
  have h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r) =
      IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) := by
    refine Units.ext ?_
    rw [GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
    exact (RingHom.map_det (algebraMap ℚ (NumberField.AdeleRing (𝓞 ℚ) ℚ))
      (r : Matrix (Fin 2) (Fin 2) ℚ)).symm
  refine ⟨⟨⟨GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r,
    GroundTheory.Automorphic.Reduction.rationalGL_le_normOneGL ⟨r, rfl⟩⟩, ⟨r, rfl⟩⟩, ?_⟩
  rw [range_pm]
  change GroundTheory.Automorphic.AdelicGLn.det ℚ 2
    (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r * (x : GL (Fin 2) (A ℚ))) ∈ UU
  rw [map_mul, h, hr, ← hq, map_inv, inv_mul_cancel_left]
  exact hy
end

section -- merged from Development.AutomorphicArithmetic.AdelicSL2.EqSl2RatMulOfGl2RatSmulAdelicSL2IdeleMapEq
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

private theorem us_pos (x : US) : ((x : (A ℚ)ˣ) : IdeleGroup ℚ) ∈ RationalIdeles.positiveSubgroup := by
  obtain ⟨h1, h2⟩ := x.2
  set t : IdeleGroup ℚ := (x : (A ℚ)ˣ) with ht
  have hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    intro v
    rw [← map_mul]
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))
    have h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
    rw [h', map_one]
  refine RationalIdeles.mem_positiveSubgroup.2 ⟨?_, ?_⟩
  · change IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ
    refine (mem_finiteIntegralUnits ℚ).2 fun v => ?_
    have hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := h2 v
    have hi := hinv v
    rw [hv, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  · rw [RationalIdeles.coe_realPart]
    have h1' : (t : NumberField.AdeleRing (𝓞 ℚ) ℚ).1 = 1 := h1
    rw [h1', map_one]
    exact one_pos

theorem UpperTheory.eq_sl2Rat_mul_of_gl2Rat_smul_adelicSL2IdeleMap_eq :
    ∀ (γ : Ga) (p q : G1 ℚ × US), γ • pm p = pm q → q.2 = p.2 ∧ ∃ s : SpecialLinearGroup (Fin 2) ℚ, q.1 = ratS ℚ s * p.1 ∧ ((γ : GG) : GL (Fin 2) (A ℚ)) = gl (ratS ℚ s) := by
  intro γ p q h
  obtain ⟨r, hr⟩ := γ.2
  have h1 : GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r * (gl p.1 * dM (p.2 : (A ℚ)ˣ)) = gl q.1 * dM (q.2 : (A ℚ)ˣ) := by
    rw [hr]
    exact congrArg Subtype.val h
  have hdet : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r) =
      IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) := by
    refine Units.ext ?_
    rw [GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
    exact (RingHom.map_det (algebraMap ℚ _) (r : Matrix (Fin 2) (Fin 2) ℚ)).symm
  have h2 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) * (p.2 : (A ℚ)ˣ) = (q.2 : (A ℚ)ˣ) := by
    have := congrArg (GroundTheory.Automorphic.AdelicGLn.det ℚ 2) h1
    rwa [map_mul, det_el, det_el, hdet] at this
  have h3 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) = ((q.2 * p.2⁻¹ : US) : (A ℚ)ˣ) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← h2, mul_inv_cancel_right]
  have h4 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) = 1 := by
    have hm : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) ∈
        RationalIdeles.positiveSubgroup ⊓ (IdeleGroup.diagonal ℚ).range :=
      ⟨h3 ▸ us_pos _, ⟨_, rfl⟩⟩
    rw [RationalIdeles.positiveSubgroup_inf_diagonal_range] at hm
    exact hm
  have h5 : (q.2 : (A ℚ)ˣ) = (p.2 : (A ℚ)ˣ) := by rw [← h2, h4, one_mul]
  have h6 : (r : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    have := congrArg Units.val h4
    rw [IdeleGroup.coe_diagonal, Units.val_one] at this
    apply NumberField.AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ
    rw [map_one]
    exact this
  let s : SpecialLinearGroup (Fin 2) ℚ := ⟨r.val, h6⟩
  have h7 : GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r = gl (ratS ℚ s) := by
    apply Units.ext
    ext i j
    rfl
  refine ⟨Subtype.ext h5, s, ?_, hr.symm.trans h7⟩
  rw [h5, h7, ← mul_assoc] at h1
  have h8 : gl (ratS ℚ s) * gl p.1 = gl q.1 := mul_right_cancel h1
  apply Subtype.ext
  have := congrArg Units.val h8
  exact this.symm
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Pointwise Classical ENNReal NNReal

theorem UpperTheory.isFundamentalDomain_image_sl2Domain_prod_ideles :
    ∀ (M : Meas ℚ) (U : UMeas) (μ : Measure GG) [μ.IsHaarMeasure], IsFundamentalDomain Ga (pm '' (M.D ×ˢ Set.univ)) μ := by
  intro M U μ _
  haveI := M.haar
  have emb : MeasurableEmbedding pm := UpperTheory.isOpenEmbedding_projection.measurableEmbedding
  obtain ⟨c, hc⟩ := UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod M U μ
  have null : ∀ N : Set (G1 ℚ), M.μ N = 0 → μ (pm '' (N ×ˢ Set.univ)) = 0 := fun N hN => by
    rw [← Measure.restrict_eq_self μ (Set.image_subset_range _ _), hc, Measure.smul_apply, emb.map_apply,
      Set.preimage_image_eq _ emb.injective, Measure.prod_prod, hN, zero_mul, smul_zero]
  have lift : ∀ s : SpecialLinearGroup (Fin 2) ℚ, ∃ γ : Ga, ∀ p : G1 ℚ × US, γ • pm p = pm (ratS ℚ s * p.1, p.2) := fun s => by
    refine ⟨⟨pm (ratS ℚ s, 1), ?_⟩, fun p => Subtype.ext ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ⟨SpecialLinearGroup.toGL s, Units.ext ?_⟩
      change _ = (ratS ℚ s).1 * !![1, 0; 0, (1 : A ℚ)]
      rw [← Matrix.one_fin_two, mul_one]
      rfl
    · change gl (ratS ℚ s) * dM 1 * (gl p.1 * dM p.2.1) = gl (ratS ℚ s * p.1) * dM p.2.1
      have : dM (1 : (A ℚ)ˣ) = 1 := Units.ext Matrix.one_fin_two.symm
      rw [this, mul_one, ← mul_assoc, ← map_mul]
  refine ⟨(emb.measurableSet_image.2 (M.meas.prod MeasurableSet.univ)).nullMeasurableSet, ?_, fun γ γ' hne => ?_⟩
  · have h0 := null _ (ae_iff.1 M.fund.ae_covers)
    rw [ae_iff]
    refine measure_mono_null (t := ⋃ γ : Ga, (fun x : GG => (γ : GG) * x) ⁻¹'
      (pm '' ({g | ¬ ∃ s : Gam ℚ, s • g ∈ M.D} ×ˢ Set.univ))) (fun x hx => ?_)
      (measure_iUnion_null fun γ => by rw [measure_preimage_mul]; exact h0)
    obtain ⟨γ, p, hp⟩ := UpperTheory.exists_gl2Rat_smul_mem_range_adelicSL2IdeleMap x
    refine Set.mem_iUnion.2 ⟨γ, p, ⟨?_, trivial⟩, hp⟩
    rintro ⟨⟨_, s, rfl⟩, hs⟩
    obtain ⟨δ, hδ⟩ := lift s
    exact hx ⟨δ * γ, (ratS ℚ s * p.1, p.2), ⟨hs, trivial⟩, by rw [mul_smul, ← hp, hδ]⟩
  · haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
    haveI : Countable (SpecialLinearGroup (Fin 2) ℚ) := Subtype.countable
    have hN : M.μ (⋃ s : {s : SpecialLinearGroup (Fin 2) ℚ // ratS ℚ s ≠ 1},
        ((⟨ratS ℚ s.1, s.1, rfl⟩ : Gam ℚ) • M.D ∩ (1 : Gam ℚ) • M.D)) = 0 :=
      measure_iUnion_null fun s => M.fund.aedisjoint fun h => s.2 (congrArg Subtype.val h)
    refine measure_mono_null (t := (fun x : GG => ((γ'⁻¹ : Ga) : GG) * x) ⁻¹' (pm '' (_ ×ˢ Set.univ))) ?_
      (by rw [measure_preimage_mul]; exact null _ hN)
    rintro x ⟨⟨_, ⟨p, hp, rfl⟩, e⟩, ⟨_, ⟨q, hq, rfl⟩, e'⟩⟩
    have e1 : (γ'⁻¹ * γ) • pm p = pm q := by
      rw [mul_smul, inv_smul_eq_iff]
      exact e.trans e'.symm
    obtain ⟨-, s, h1, h2⟩ := UpperTheory.eq_sl2Rat_mul_of_gl2Rat_smul_adelicSL2IdeleMap_eq _ p q e1
    have hs : ratS ℚ s ≠ 1 := fun h => hne (by
      rw [h] at h2
      exact (inv_mul_eq_one.1 (Subtype.ext (Subtype.ext (h2.trans (Units.ext rfl))))).symm)
    refine ⟨q, ⟨Set.mem_iUnion.2 ⟨⟨s, hs⟩, ⟨p.1, hp.1, h1.symm⟩, by rw [one_smul]; exact hq.1⟩, trivial⟩, ?_⟩
    change pm q = γ'⁻¹ • x
    rw [eq_inv_smul_iff]
    exact e'
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical
open scoped ENNReal NNReal

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.fibre :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fibre := by
  intro M μ _ Φ hΦ h0
  obtain ⟨U⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.uMeasEx_of
  haveI := M.haar
  have hemb : MeasurableEmbedding pm := UpperTheory.isOpenEmbedding_projection.measurableEmbedding
  set F : Set GG := pm '' (M.D ×ˢ Set.univ) with hFdef
  have hF : IsFundamentalDomain Ga F μ := UpperTheory.isFundamentalDomain_image_sl2Domain_prod_ideles M U μ
  have hFm : MeasurableSet F := hemb.measurableSet_image.2 (M.meas.prod MeasurableSet.univ)
  have hinv : ∀ (γ : Ga) (x : GG), Φ ((γ • x : GG) : GL (Fin 2) (A ℚ)) = Φ (x : GL (Fin 2) (A ℚ)) := by
    intro γ x
    obtain ⟨r, hr⟩ : ∃ r : GL (Fin 2) ℚ, ratGL ℚ 2 r = ((γ : GG) : GL (Fin 2) (A ℚ)) := by
      obtain ⟨r, hr⟩ := γ.2
      exact ⟨r, hr⟩
    have := hΦ.left r (x : GL (Fin 2) (A ℚ))
    rw [hr] at this
    exact this
  let Φq : GroundTheory.Automorphic.RightCosetSpace Ga → ℂ := fun y => Φ ((Quotient.out y : GG) : GL (Fin 2) (A ℚ))
  have hq : ∀ x : GG, Φq (GroundTheory.Automorphic.RightCosetSpace.mk Ga x) = Φ (x : GL (Fin 2) (A ℚ)) := by
    intro x
    have h : GroundTheory.Automorphic.RightCosetSpace.mk Ga (Quotient.out (GroundTheory.Automorphic.RightCosetSpace.mk Ga x)) =
        GroundTheory.Automorphic.RightCosetSpace.mk Ga x := Quotient.out_eq _
    obtain ⟨γ, hγ⟩ := GroundTheory.Automorphic.RightCosetSpace.mk_eq_mk_iff.1 h
    change Φ ((Quotient.out (GroundTheory.Automorphic.RightCosetSpace.mk Ga x) : GG) : GL (Fin 2) (A ℚ)) = _
    rw [← hγ, hinv]
  have hqc : Continuous Φq := by
    refine (GroundTheory.Automorphic.RightCosetSpace.isOpenQuotientMap_mk (Γ := Ga)).isQuotientMap.continuous_iff.2 ?_
    have : Φq ∘ GroundTheory.Automorphic.RightCosetSpace.mk Ga = fun x : GG => Φ (x : GL (Fin 2) (A ℚ)) := funext hq
    rw [this]
    exact hΦ.cont.comp continuous_subtype_val
  change ∫ y, Φq y ∂(GroundTheory.Automorphic.RightCosetSpace.quotientMeasure Ga μ) = 0
  rw [← GroundTheory.Automorphic.RightCosetSpace.map_restrict_eq_quotientMeasure μ hF,
    integral_map (GroundTheory.Automorphic.RightCosetSpace.measurable_mk Ga).aemeasurable hqc.aestronglyMeasurable]
  simp only [hq]
  obtain ⟨c, hc⟩ := UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod M U μ
  have hFR : F ⊆ Set.range pm := Set.image_subset_range _ _
  have hres : μ.restrict F = (c • (M.μ.prod (us U)).map pm).restrict F := by
    rw [← hc, Measure.restrict_restrict hFm, Set.inter_eq_self_of_subset_left hFR]
  rw [hres, Measure.restrict_smul, integral_smul_nnreal_measure, hemb.setIntegral_map]
  have hpre : pm ⁻¹' F = M.D ×ˢ Set.univ := hemb.injective.preimage_image _
  have hr : (M.μ.prod (us U)).restrict (M.D ×ˢ Set.univ) = (M.μ.restrict M.D).prod (us U) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hpre, hr]
  by_cases hi : Integrable (fun x : G1 ℚ × US => Φ (pm x : GL (Fin 2) (A ℚ))) ((M.μ.restrict M.D).prod (us U))
  · rw [integral_prod_symm _ hi]
    have : ∀ t : US, ∫ g in M.D, Φ (pm (g, t) : GL (Fin 2) (A ℚ)) ∂M.μ = 0 := fun t => h0 t t.2
    simp [this]
  · rw [integral_undef hi, smul_zero]
