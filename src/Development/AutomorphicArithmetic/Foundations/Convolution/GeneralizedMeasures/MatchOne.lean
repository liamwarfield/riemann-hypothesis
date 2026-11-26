module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalHeightDeterminant

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem haar_ex {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {K : Set G} (hc : IsCompact K) (ho : IsOpen K) (h1 : (1 : G) ∈ K) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m K = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K, hc⟩, by
    show (interior K).Nonempty
    rw [ho.interior_eq]; exact ⟨1, h1⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

private theorem haar_uniq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {K : Set G} {m m' : Measure G}
    (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure) (h : m K = 1) (h' : m' K = 1) : m = m' := by
  have e := Measure.isMulLeftInvariant_eq_smul m m'
  have e2 : m K = (Measure.haarScalarFactor m m' • m') K := by rw [← e]
  rw [h, Measure.smul_apply, h', ENNReal.smul_def, smul_eq_mul, mul_one] at e2
  have e3 : Measure.haarScalarFactor m m' = 1 := by exact_mod_cast e2.symm
  rw [e3, one_smul] at e
  exact e

private theorem gl_top (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact ⟨inferInstance, Units.isEmbedding_embedProduct.secondCountableTopology⟩

private theorem gl_int {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (n : ℕ)
    (O : Subring R) (hc : IsCompact (O : Set R)) (ho : IsOpen (O : Set R)) :
    IsCompact {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} ∧
    IsOpen {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} := by
  let S : Subring (Matrix (Fin n) (Fin n) R) := (RingHom.mapMatrix O.subtype).range
  have hS : ∀ A : Matrix (Fin n) (Fin n) R, A ∈ S ↔ ∀ i j, A i j ∈ O := by
    intro A
    constructor
    · rintro ⟨B, rfl⟩ i j
      exact (B i j).2
    · intro h
      exact ⟨Matrix.of fun i j => ⟨A i j, h i j⟩, rfl⟩
  constructor
  · have e : {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} =
        (S.toSubmonoid.units : Set (GL (Fin n) R)) := by
      ext g
      rw [SetLike.mem_coe, Submonoid.mem_units_iff, Subring.mem_toSubmonoid, Subring.mem_toSubmonoid, hS, hS]
      rfl
    rw [e]
    apply Submonoid.units_isCompact
    have : (S.toSubmonoid : Set (Matrix (Fin n) (Fin n) R)) =
        Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (O : Set R) := by
      ext A
      change A ∈ S ↔ ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, A i j ∈ (O : Set R)
      rw [hS]
      simp
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
  · simp only [Set.setOf_and, Set.setOf_forall]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_val.matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage ((Units.continuous_val.matrix_elem i j).comp continuous_inv)

open ValuativeRel in
private theorem unitSet_top {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) :
    IsCompact (unitSet E n v) ∧ IsOpen (unitSet E n v) ∧ (1 : GL (Fin n) (CompletionsOver E v)) ∈ unitSet E n v := by
  let O : Subring (CompletionsOver E v) :=
    ⨅ w : PlacesOver E v, (𝒪[w.1.adicCompletion E]).comap
      (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)
  have hO : (O : Set (CompletionsOver E v)) =
      Set.pi Set.univ fun w : PlacesOver E v => (𝒪[w.1.adicCompletion E] : Set (w.1.adicCompletion E)) := by
    ext x
    simp [O, Subring.mem_iInf]
  have hc : IsCompact (O : Set (CompletionsOver E v)) := by
    rw [hO]
    exact isCompact_univ_pi fun w => isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[w.1.adicCompletion E]))
  have ho : IsOpen (O : Set (CompletionsOver E v)) := by
    rw [hO]
    exact isOpen_set_pi Set.finite_univ fun w _ => Valuation.isOpen_integer
  have e : unitSet E n v = {g : GL (Fin n) (CompletionsOver E v) | (∀ i j, g i j ∈ O) ∧
      ∀ i j, (g⁻¹ : GL (Fin n) (CompletionsOver E v)) i j ∈ O} := by
    ext g
    simp only [unitSet, Set.mem_setOf_eq, GLnLocal.mem_integralGL_iff, ← map_inv, O, Subring.mem_iInf, Subring.mem_comap]
    exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
      fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩
  refine ⟨e ▸ (gl_int n O hc ho).1, e ▸ (gl_int n O hc ho).2, fun w => ?_⟩
  rw [map_one]
  exact one_mem _

theorem UpperTheory.ConvolutionTheory.GM.matchOne :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (v : Pl F),
    (∃ (_ : MeasurableSpace (GL (Fin n) (CompletionsOver E v))) (_ : BorelSpace (GL (Fin n) (CompletionsOver E v)))
      (_ : MeasurableSpace (GL (Fin n) (v.adicCompletion F))) (_ : BorelSpace (GL (Fin n) (v.adicCompletion F)))
      (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))),
      mE.IsHaarMeasure ∧ mF.IsHaarMeasure ∧ mE (unitSet E n v) = 1 ∧ mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1) ∧
    ∀ [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
      [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
      (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))),
      mE.IsHaarMeasure → mF.IsHaarMeasure → mE (unitSet E n v) = 1 → mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1 →
      ∀ (c : ℂ) (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : GL (Fin n) (v.adicCompletion F) → ℂ),
      Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF c φ f → MatchAt σ v c φ f := by
  intro F E _ _ _ _ _ σ n v
  obtain ⟨lE, sE⟩ := gl_top (CompletionsOver E v) n
  obtain ⟨lF, sF⟩ := gl_top (v.adicCompletion F) n
  obtain ⟨hc, ho, h1⟩ := unitSet_top (E := E) n v
  constructor
  · borelize (GL (Fin n) (CompletionsOver E v))
    borelize (GL (Fin n) (v.adicCompletion F))
    obtain ⟨mE, hE, hE1⟩ := haar_ex hc ho h1
    obtain ⟨mF, hF, hF1⟩ := haar_ex (GLnLocal.isCompact_integralGL (v.adicCompletion F) n)
      (GLnLocal.isOpen_integralGL (v.adicCompletion F) n) (one_mem _)
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, mE, mF, hE, hF, hE1, hF1⟩
  · intro aE bE aF bF mE mF hE hF hE1 hF1 c φ f hM aE' bE' aF' bF' mE' mF' hE' hF' hE1' hF1'
    obtain rfl : aE = aE' := bE.measurable_eq.trans bE'.measurable_eq.symm
    obtain rfl : aF = aF' := bF.measurable_eq.trans bF'.measurable_eq.symm
    obtain rfl : mE = mE' := haar_uniq hE hE' hE1 hE1'
    obtain rfl : mF = mF' := haar_uniq hF hF' hF1 hF1'
    exact hM
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.StepFin
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private noncomputable def trCc {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : G)
    (β : CompactlySupportedContinuousMap G ℂ) : CompactlySupportedContinuousMap G ℂ where
  toFun x := β (h⁻¹ * x)
  continuous_toFun := β.continuous.comp (continuous_const_mul h⁻¹)
  hasCompactSupport' := by
    refine HasCompactSupport.intro (β.hasCompactSupport.isCompact.image (continuous_const_mul h))
      fun x hx => ?_
    by_contra hne
    exact hx ⟨h⁻¹ * x, subset_tsupport _ hne, by simp⟩

private theorem map_integrated_trCc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts ν] (π : UnitaryRep G H) (h : G)
    (β : CompactlySupportedContinuousMap G ℂ) (v : H) :
    π h (π.integrated ν (UnitaryRep.ccToL1 ν β) v) =
      π.integrated ν (UnitaryRep.ccToL1 ν (trCc h β)) v := by
  have e := π.map_comp_integrated ν h (UnitaryRep.ccToL1 ν β)
  have e2 : UnitaryRep.leftTranslate ν h (UnitaryRep.ccToL1 ν β) =
      UnitaryRep.ccToL1 ν (trCc h β) := by
    refine Lp.ext ?_
    have hc := (β.continuous.memLp_of_hasCompactSupport (μ := ν) (p := 1) β.hasCompactSupport).coeFn_toLp
    have hc' := ((trCc h β).continuous.memLp_of_hasCompactSupport (μ := ν) (p := 1)
      (trCc h β).hasCompactSupport).coeFn_toLp
    filter_upwards [UnitaryRep.coeFn_leftTranslate ν h (UnitaryRep.ccToL1 ν β), hc',
      (measurePreserving_mul_left ν h⁻¹).quasiMeasurePreserving.ae_eq_comp hc] with x h1 h2 h3
    rw [h1]
    change (UnitaryRep.ccToL1 ν β : G → ℂ) (h⁻¹ * x) = (UnitaryRep.ccToL1 ν (trCc h β)) x
    rw [show (UnitaryRep.ccToL1 ν β : G → ℂ) (h⁻¹ * x) = β (h⁻¹ * x) from h3,
      show (UnitaryRep.ccToL1 ν (trCc h β) : G → ℂ) x = trCc h β x from h2]
    rfl
  rw [e2] at e
  exact congrArg (fun A : H →L[ℂ] H => A v) e

private theorem ccToL1_smul {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (a : ℂ) (f : CompactlySupportedContinuousMap G ℂ) :
    UnitaryRep.ccToL1 ν (a • f) = a • UnitaryRep.ccToL1 ν f := by
  unfold UnitaryRep.ccToL1
  rw [← MemLp.toLp_const_smul]
  rfl

private theorem ccToL1_finsetSum {G ι : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (s : Finset ι) (f : ι → CompactlySupportedContinuousMap G ℂ) :
    UnitaryRep.ccToL1 ν (∑ i ∈ s, f i) = ∑ i ∈ s, UnitaryRep.ccToL1 ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    unfold UnitaryRep.ccToL1
    exact MemLp.toLp_zero _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    unfold UnitaryRep.ccToL1
    rw [← MemLp.toLp_add]
    rfl

private theorem integrated_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {G ι : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (π : UnitaryRep G H) (s : Finset ι) (a : ι → ℂ)
    (f : ι → CompactlySupportedContinuousMap G ℂ) :
    π.integrated ν (UnitaryRep.ccToL1 ν (∑ i ∈ s, a i • f i)) = ∑ i ∈ s, a i • π.integrated ν (UnitaryRep.ccToL1 ν (f i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ccToL1_finsetSum, map_sum]
  simp only [ccToL1_smul, map_smul]

private theorem Ofin_sum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → TF K n) :
    Ofin μ m (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i • Ofin μ m (f i) :=
  integrated_sum m ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj) s a f

private theorem rhoF_comp_Ofin {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (y : AdelicGLn.FiniteAdelicGL K n) (e : TF K n) :
    rhoF μ y ∘L Ofin μ m e = Ofin μ m (trCc y e) := by
  refine ContinuousLinearMap.ext fun v => ?_
  exact map_integrated_trCc m
    ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj) y e v

private theorem cf_local {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (y : GL (Fin n) (w.adicCompletion K))
    (x : AdelicGLn.FiniteAdelicGL K n) : cf w (AdelicGLn.localEmbedding w y * x) = y * cf w x := by
  unfold cf
  rw [map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]

private theorem exists_cover {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G)
    (hJ : IsOpen (J : Set G)) (h : G → ℂ) (hc : HasCompactSupport h) :
    ∃ t : Finset (G ⧸ J), ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ J) ∈ t := by
  have hop : ∀ c : G ⧸ J, IsOpen ((QuotientGroup.mk : G → G ⧸ J) ⁻¹' {c}) := fun c => by
    have : (QuotientGroup.mk : G → G ⧸ J) ⁻¹' {c} = (fun g => c.out⁻¹ * g) ⁻¹' (J : Set G) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      exact eq_comm
    rw [this]
    exact hJ.preimage (continuous_const_mul _)
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover _ hop fun y _ =>
    Set.mem_iUnion.2 ⟨QuotientGroup.mk y, rfl⟩
  refine ⟨t, fun y hy => ?_⟩
  obtain ⟨c, hc', hyc⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport _ hy))
  rw [show (QuotientGroup.mk y : G ⧸ J) = c from hyc]
  exact hc'

private theorem coset_sum {G : Type*} [Group G] (J : Subgroup G) (h : G → ℂ) (hinv : ∀ k ∈ J, ∀ x, h (x * k) = h x)
    (t : Finset (G ⧸ J)) (ht : ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ J) ∈ t) (y : G) :
    ∑ c ∈ t, h c.out * (J : Set G).indicator (1 : G → ℂ) (c.out⁻¹ * y) = h y := by
  classical
  have hind : ∀ c : G ⧸ J, (J : Set G).indicator (1 : G → ℂ) (c.out⁻¹ * y) = if (QuotientGroup.mk y : G ⧸ J) = c then 1 else 0 := fun c => by
    have : c.out⁻¹ * y ∈ (J : Set G) ↔ (QuotientGroup.mk y : G ⧸ J) = c := by
      rw [SetLike.mem_coe, ← QuotientGroup.eq, QuotientGroup.out_eq']
      exact eq_comm
    by_cases hh : (QuotientGroup.mk y : G ⧸ J) = c
    · rw [if_pos hh, Set.indicator_of_mem (this.2 hh)]; rfl
    · rw [if_neg hh, Set.indicator_of_notMem (fun q => hh (this.1 q))]
  have hout : h (QuotientGroup.mk y : G ⧸ J).out = h y := by
    have hk : (QuotientGroup.mk y : G ⧸ J).out⁻¹ * y ∈ J := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have := hinv _ hk (QuotientGroup.mk y : G ⧸ J).out
    rw [mul_inv_cancel_left] at this
    exact this.symm
  simp only [hind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · exact hout
  · by_contra hne
    exact hm (ht y (Ne.symm hne))

theorem UpperTheory.ConvolutionTheory.GM.stepFin :
    StepFin := by
  intro K _ _ n hn μ _ m _ w J hJ h hc hinv r hr e₀ e₁ h0 h1
  have htr : ∀ (y : GL (Fin n) (w.adicCompletion K)) x,
      trCc (AdelicGLn.localEmbedding w y) e₀ x =
        r x * (J : Set _).indicator 1 (y⁻¹ * cf w x) := fun y x => by
    show e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x) = _
    rw [h0, ← map_inv, hr, cf_local]
  refine ⟨fun u => ?_, ?_⟩
  · refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have e : trCc (AdelicGLn.localEmbedding w k) e₀ = e₀ := by
      ext x
      rw [htr, h0]
      congr 1
      by_cases hx : cf w x ∈ (J : Set _)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (J.mul_mem (J.inv_mem hk) hx)]; rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        intro q
        exact hx (by simpa using J.mul_mem hk q)
    have := congrArg (fun A : LL μ →L[ℂ] LL μ => A u) (rhoF_comp_Ofin μ m (AdelicGLn.localEmbedding w k) e₀)
    simpa [e] using this
  · obtain ⟨t, ht⟩ := exists_cover J hJ h hc
    have hfs : (∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ J, h c.out • rhoL μ w c.out) = ∑ c ∈ t, h c.out • rhoL μ w c.out := by
      refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
      have hne : h c.out ≠ 0 := fun q => hc' (by simp [q])
      have := ht _ hne
      rwa [QuotientGroup.out_eq'] at this
    have he : e₁ = ∑ c ∈ t, h c.out • trCc (AdelicGLn.localEmbedding w c.out) e₀ := by
      ext x
      rw [h1, CompactlySupportedContinuousMap.sum_apply]
      simp only [CompactlySupportedContinuousMap.smul_apply, htr, smul_eq_mul]
      rw [← coset_sum J h hinv t ht (cf w x), Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hfs, he]
    rw [Ofin_sum]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← rhoF_comp_Ofin]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ContinuousMapGL
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsLCProd
theorem UpperTheory.Reformulated.B.Qf48.isLC_prod {X : Type*} {ι : Type*} [TopologicalSpace X] (T : Finset ι) (f : ι → X → ℂ)
    (h : ∀ i ∈ T, IsLocallyConstant (f i)) : IsLocallyConstant fun x ↦ ∏ i ∈ T, f i x := by
  classical
  induction T using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

open scoped RestrictedProduct

namespace UpperTheory.ConvolutionTheory.GM.CompactClopenAverage

section Gen

private theorem rp_compact {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : ∀ i, Set (R i)}
    (D : ∀ i, Set (R i)) (hD : ∀ i, IsCompact (D i)) (T : Set ι) (hT : T.Finite)
    (hDA : ∀ i, i ∉ T → D i ⊆ A i) : IsCompact {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ D i} := by
  have hle : (Filter.cofinite : Filter ι) ≤ Filter.principal Tᶜ := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact hT
  have Y : IsCompact ((↑) ⁻¹' (Set.univ.pi D) : Set (Πʳ i, [R i, A i]_[Filter.principal Tᶜ])) := by
    refine RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr
      (isCompact_univ_pi hD)
    rw [RestrictedProduct.range_coe_principal]
    intro f hf i hi
    exact hDA i hi (hf i trivial)
  convert Y.image (RestrictedProduct.continuous_inclusion hle) using 1
  ext x
  constructor
  · intro hx
    refine ⟨⟨x, Filter.eventually_principal.2 fun i hi => hDA i hi (hx i)⟩, fun i _ => hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩ i
    exact hy i trivial

private theorem isLC_prod {X ι : Type*} [TopologicalSpace X] (T : Finset ι) (f : ι → X → ℂ)
    (h : ∀ i ∈ T, IsLocallyConstant (f i)) : IsLocallyConstant fun x => ∏ i ∈ T, f i x :=
  _root_.UpperTheory.Reformulated.B.Qf48.isLC_prod T f h

private theorem continuous_mapGL' {m : ℕ} {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] (f : R →+* S) (hf : Continuous f) : Continuous (mapGL m f) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id hf)

end Gen

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem liesOver_under (w : Pl E) : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩

private theorem under_eq {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem finite_under (S : Set (Pl F)) (hS : S.Finite) :
    {w : Pl E | w.under (𝓞 F) ∈ S}.Finite := by
  refine (hS.biUnion fun v _ => Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  intro w hw
  exact Set.mem_biUnion hw ⟨⟨w, liesOver_under w⟩, rfl⟩

private noncomputable def pv (v : Pl F) (x : AdelicGLn.FiniteAdelicGL E n) : GL (Fin n) (CompletionsOver E v) :=
  mapGL n (atFin v) (finEmb E n x)

private theorem finEmb_entry (x : AdelicGLn.FiniteAdelicGL E n) (a b : Fin n) :
    ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd E n (finEmb E n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

private theorem cmp_pv {v : Pl F} (w : PlacesOver E v) (x : AdelicGLn.FiniteAdelicGL E n) :
    cmp w (pv v x) = AdelicGLn.finiteRestrictedEquiv E n x w.1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 w.1 = _
  rw [finEmb_entry]
  rfl

private theorem continuous_atFin (v : Pl F) : Continuous (atFin (E := E) v) :=
  continuous_pi fun w => (RestrictedProduct.continuous_eval w.1).comp continuous_snd

private theorem continuous_pv (v : Pl F) : Continuous (pv (E := E) (n := n) v) :=
  (continuous_mapGL' _ (continuous_atFin v)).comp continuous_finEmb

private theorem continuous_cmp {v : Pl F} (w : PlacesOver E v) : Continuous (cmp (n := n) w) :=
  continuous_mapGL' _ (continuous_apply w)

private def U (S : Finset (Pl F)) : Set (AdelicGLn.FiniteAdelicGL E n) :=
  {x | ∀ w : Pl E, w.under (𝓞 F) ∉ S →
    AdelicGLn.finiteRestrictedEquiv E n x w ∈ GLnLocal.integralGL (w.adicCompletion E) n}

private theorem isClopen_U (S : Finset (Pl F)) : IsClopen (U (E := E) (n := n) S) := by
  constructor
  · simp only [U, Set.setOf_forall]
    refine isClosed_iInter fun w => isClosed_iInter fun _ => ?_
    exact (GLnLocal.isCompact_integralGL (w.adicCompletion E) n).isClosed.preimage
      ((RestrictedProduct.continuous_eval w).comp (AdelicGLn.finiteRestrictedEquiv E n).continuous)
  · have h := RestrictedProduct.isOpen_forall_imp_mem
      (R := fun w : Pl E => GL (Fin n) (w.adicCompletion E))
      (A := fun w => (GLnLocal.integralGL (w.adicCompletion E) n : Set _))
      (fun w => GLnLocal.isOpen_integralGL (w.adicCompletion E) n) (p := fun w => w.under (𝓞 F) ∉ S)
    exact h.preimage (AdelicGLn.finiteRestrictedEquiv E n).continuous

private theorem e_formula (S : Finset (Pl F)) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ)
    (hφ : ∀ v ∉ S, φ v = (unitSet E n v).indicator 1) (x : AdelicGLn.FiniteAdelicGL E n) :
    ∏ᶠ v, φ v (pv v x) = (∏ v ∈ S, φ v (pv v x)) * (U S).indicator 1 x := by
  classical
  by_cases hx : x ∈ U (E := E) (n := n) S
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS
    refine hv ?_
    have hvS' : v ∉ S := hvS
    change φ v (pv v x) = 1
    rw [hφ v hvS', Set.indicator_of_mem, Pi.one_apply]
    intro w
    have := hx w.1 (by rw [under_eq]; exact hvS')
    rw [← cmp_pv] at this
    exact this
  · rw [Set.indicator_of_notMem hx, mul_zero]
    simp only [U, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨w, hwS, hw⟩ := hx
    have hB : {w : Pl E | AdelicGLn.finiteRestrictedEquiv E n x w ∉
        GLnLocal.integralGL (w.adicCompletion E) n}.Finite :=
      Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv E n x).2
    refine finprod_eq_zero _ (w.under (𝓞 F)) ?_ ?_
    · rw [hφ _ hwS, Set.indicator_of_notMem]
      intro h
      refine hw ?_
      have h1 : cmp (⟨w, liesOver_under w⟩ : PlacesOver E (w.under (𝓞 F))) (pv _ x) ∈
          GLnLocal.integralGL (w.adicCompletion E) n := h ⟨w, liesOver_under w⟩
      rw [cmp_pv] at h1
      exact h1
    · refine (S.finite_toSet.union (hB.image fun w : Pl E => w.under (𝓞 F))).subset fun v hv => ?_
      by_cases hvS : v ∈ S
      · exact Or.inl hvS
      · right
        have hnot : pv v x ∉ unitSet E n v := by
          intro h
          refine hv ?_
          change φ v (pv v x) = 1
          rw [hφ v hvS, Set.indicator_of_mem h, Pi.one_apply]
        simp only [unitSet, Set.mem_setOf_eq, not_forall] at hnot
        obtain ⟨w', hw'⟩ := hnot
        refine ⟨w'.1, ?_, under_eq w'⟩
        intro h
        refine hw' ?_
        have : cmp w' (pv v x) ∈ GLnLocal.integralGL (w'.1.adicCompletion E) n := by
          rw [cmp_pv]
          exact h
        exact this

private theorem e_compact (S : Finset (Pl F)) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ)
    (hS : ∀ v ∈ S, HasCompactSupport (φ v)) :
    ∃ C : Set (AdelicGLn.FiniteAdelicGL E n), IsCompact C ∧
      ∀ x ∈ U S, (∀ v ∈ S, φ v (pv v x) ≠ 0) → x ∈ C := by
  classical
  let D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E)) := fun w =>
    if w.under (𝓞 F) ∈ S then
      cmp (⟨w, liesOver_under w⟩ : PlacesOver E (w.under (𝓞 F))) '' tsupport (φ (w.under (𝓞 F)))
    else (GLnLocal.integralGL (w.adicCompletion E) n : Set _)
  have hD : ∀ w, IsCompact (D w) := fun w => by
    by_cases h : w.under (𝓞 F) ∈ S
    · simp only [D, if_pos h]
      exact (hS _ h).isCompact.image (continuous_cmp _)
    · simp only [D, if_neg h]
      exact GLnLocal.isCompact_integralGL _ n
  have hK := rp_compact (A := fun w : Pl E => (GLnLocal.integralGL (w.adicCompletion E) n : Set _)) D hD
    {w : Pl E | w.under (𝓞 F) ∈ S} (finite_under _ S.finite_toSet) (fun w hw => by
      have h : w.under (𝓞 F) ∉ S := hw
      simp only [D, if_neg h]
      exact subset_rfl)
  refine ⟨_, (AdelicGLn.finiteRestrictedEquiv E n).toHomeomorph.isCompact_preimage.2 hK, ?_⟩
  intro x hx hne w
  by_cases h : w.under (𝓞 F) ∈ S
  · change _ ∈ D w
    simp only [D, if_pos h]
    exact ⟨pv _ x, subset_tsupport _ (hne _ h), cmp_pv _ x⟩
  · change _ ∈ D w
    simp only [D, if_neg h]
    exact hx w h

private theorem pv_finPart (v : Pl F) (g : AdelicGLn.AdelicGL E n) :
    pv v (CuspidalSpectrum.finPart E n g) = mapGL n (atFin v) g := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  funext w
  change ((finEmb E n (CuspidalSpectrum.finPart E n g) : AdelicGLn.AdelicGL E n) a b).2 w.1 = (g a b).2 w.1
  rw [finEmb_entry]
  rfl

end Main

end UpperTheory.ConvolutionTheory.GM.CompactClopenAverage

set_option synthInstance.maxHeartbeats 200000 in
open UpperTheory.ConvolutionTheory.GM.CompactClopenAverage in
theorem UpperTheory.ConvolutionTheory.GM.avgE :
    AvgE := by
  intro F E _ _ _ _ _ n hn S β φ hS hoff
  classical
  let e₀ : AdelicGLn.FiniteAdelicGL E n → ℂ := fun x => ∏ᶠ v, φ v (pv v x)
  have hform : ∀ x, e₀ x = (∏ v ∈ S, φ v (pv v x)) * (U S).indicator 1 x :=
    fun x => e_formula S φ hoff x
  have hlc : IsLocallyConstant e₀ := by
    have h1 : IsLocallyConstant fun x : AdelicGLn.FiniteAdelicGL E n => ∏ v ∈ S, φ v (pv v x) :=
      isLC_prod S (fun v x => φ v (pv v x)) fun v hv => (hS v hv).1.comp_continuous (continuous_pv v)
    have h2 : IsLocallyConstant ((U (E := E) (n := n) S).indicator (1 : AdelicGLn.FiniteAdelicGL E n → ℂ)) := by
      rw [← LocallyConstant.coe_charFn ℂ (isClopen_U S)]
      exact LocallyConstant.isLocallyConstant _
    have h3 := h1.mul h2
    have : e₀ = _ := funext hform
    rw [this]
    exact h3
  have hcs : HasCompactSupport e₀ := by
    obtain ⟨C, hC, hsub⟩ := e_compact S φ fun v hv => (hS v hv).2
    refine HasCompactSupport.of_support_subset_isCompact hC fun x hx => ?_
    have hx' : e₀ x ≠ 0 := hx
    rw [hform] at hx'
    have hU : x ∈ U (E := E) (n := n) S := by
      by_contra h
      exact hx' (by rw [Set.indicator_of_notMem h, mul_zero])
    refine hsub x hU fun v hv h0 => hx' ?_
    rw [Finset.prod_eq_zero hv h0, zero_mul]
  let e : TF E n := ⟨⟨e₀, hlc.continuous⟩, hcs⟩
  refine ⟨e, hlc, fun x => rfl, fun x => ?_⟩
  have hinf := (UpperTheory.ConvolutionTheory.Tf.avgTens E n hn β e _ fun _ => rfl).2
  have hΦ : ∀ g, tensE (onInf β) φ g = β (infPart E n g) * e (CuspidalSpectrum.finPart E n g) := by
    intro g
    change onInf β _ * _ = β _ * ∏ᶠ v, φ v (pv v _)
    simp only [pv_finPart]
    congr 1
  exact ((UpperTheory.ConvolutionTheory.Tf.avgTens E n hn β e _ hΦ).1 x).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.PolyMem
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem haar_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (U : Subgroup G) (hc : IsCompact (U : Set G)) (ho : IsOpen (U : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m U = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨U, hc⟩, by
    rw [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk, ho.interior_eq]
    exact ⟨1, U.one_mem⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

private theorem poly_mem {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    polyEmb (n := n) (aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) p) ∈
      symmetricLaurent (n := n) := fun σ => by
  rw [← polyEmb_rename]
  congr 1
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  exact MvPolynomial.esymm_isSymmetric (Fin n) ℂ _ σ

theorem UpperTheory.ConvolutionTheory.GM.sphEx :
    SphEx := by
  intro K _ _ n _ w
  refine ⟨fun p => ?_, ?_, ?_⟩
  · borelize (GL (Fin n) (w.adicCompletion K))
    obtain ⟨m, hm, h1⟩ := haar_one (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n)
    obtain ⟨H, hH⟩ := (AlgHom.mem_range _).1 (symmetricLaurent_le_range (μ := m) (F := w.adicCompletion K) (poly_mem p))
    exact ⟨fun x => (H : HeckeAlgebra m) x, _, inferInstance, m, hm, h1, H, fun _ => rfl, hH⟩
  · borelize (GL (Fin n) (w.adicCompletion K))
    obtain ⟨m, hm, h1⟩ := haar_one (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n)
    refine ⟨_, inferInstance, m, hm, h1, 1, fun x => ?_, by rw [map_one, map_one, map_one]⟩
    rw [HeckeAlgebra.HeckeAlgebraLevel.val_one]
    have hr : m.real (GLnLocal.integralGL (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) = 1 := by
      simp [Measure.real, h1]
    rw [HeckeAlgebra.idem_apply, hr]
    simp only [Complex.ofReal_one, inv_one]
    rfl
  · rintro p h ⟨_, _, m, _, -, H, hH, -⟩
    obtain rfl : (fun x => (H : HeckeAlgebra m) x) = h := funext hH
    exact ⟨(H : HeckeAlgebra m).mem.1, (H : HeckeAlgebra m).mem.2,
      fun k hk x => HeckeAlgebra.HeckeAlgebraLevel.val_mem _ _ H k hk x⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ConvSpec
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

theorem UpperTheory.ConvolutionTheory.GM.convSpec :
    ConvSpec := by
  intro K _ _ n _ ν _ β γ
  obtain ⟨g, hg, -, hop⟩ := UpperTheory.ConvolutionTheory.Tf.homConv (archGroup K n) (archGroup K n) (MonoidHom.id _) continuous_id ν ν β γ
  have hex : ∃ δ : TI K n, ∀ x, δ x = ∫ y, β y * γ (y⁻¹ * x) ∂ν := ⟨g, hg⟩
  have h1 : ∀ x, GM.conv ν β γ x = ∫ y, β y * γ (y⁻¹ * x) ∂ν := by
    intro x
    unfold GM.conv
    rw [dite_eq_left hex]
    exact hex.choose_spec x
  refine ⟨h1, fun μ _ => ?_⟩
  have h2 : GM.conv ν β γ = g := by
    ext x
    exact (h1 x).trans (hg x).symm
  rw [h2]
  exact hop (LL μ) ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (archP K n) continuous_archP)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.TensHt
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem norm_det_le_pow {R : Type*} [NormedField R] [IsUltrametricDist R] {n : ℕ} (g : GL (Fin n) R) :
    ‖(g : Matrix (Fin n) (Fin n) R).det‖ ≤ locHeight g ^ n :=
  _root_.UpperTheory.Reformulated.B.LocalHeightDeterminant.norm_det_le_pow g

private theorem norm_det_inv {R : Type*} [NormedField R] {n : ℕ} (h : GL (Fin n) R)
    (H : ‖(h : Matrix (Fin n) (Fin n) R).det‖ = 1) :
    ‖((h⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).det‖ = 1 := by
  have := congrArg norm (show (h : Matrix (Fin n) (Fin n) R).det *
      ((h⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).det = 1 by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one])
  rwa [norm_mul, H, one_mul, norm_one] at this

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem norm_eq_one_of_v {w : Pl E} {y : w.adicCompletion E} (h : Valued.v y = 1) : ‖y‖ = 1 := by
  have hy : y ≠ 0 := by
    rintro rfl
    simp at h
  refine le_antisymm (Valued.toNormedField.norm_le_one_iff.2 h.le) ?_
  have h2 : ‖y⁻¹‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 (by rw [map_inv₀, h, inv_one])
  rw [norm_inv] at h2
  exact (inv_le_one₀ (norm_pos_iff.2 hy)).1 h2

private theorem infAt_finEmb' (w : InfinitePlace E) (x : AdelicGLn.FiniteAdelicGL E n) :
    infAt w (finEmb E n x) = 1 := by
  show (AdelicGLn.infiniteEquiv E n (AdelicGLn.prodEquiv E n (finEmb E n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

private theorem liesOver_of_below {w : Pl E} {q : Pl F} (h : AdeleBaseChange.below F w = q) :
    w.asIdeal.LiesOver q.asIdeal := by
  subst h
  constructor
  rfl

private theorem heightOff_inv (q : Pl F) (g : AdelicGLn.AdelicGL E n) : heightOff q g⁻¹ = heightOff q g := by
  simp only [heightOff, infAt_inv, finAt_inv, locHeight_inv]

private theorem heightOff_nonneg (q : Pl F) (g : AdelicGLn.AdelicGL E n) : 0 ≤ heightOff q g :=
  mul_nonneg (Finset.prod_nonneg fun w _ => pow_nonneg (locHeight_pos _).le _)
    (finprod_nonneg fun w => finprod_nonneg fun _ => (locHeight_pos _).le)

private theorem module_le (q : Pl F) (x : AdelicGLn.FiniteAdelicGL E n)
    (hq : ∀ w : PlacesOver E q, ‖((finAt w.1 (finEmb E n x) : GL (Fin n) (w.1.adicCompletion E)) :
      Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).det‖ = 1) :
    (detModule E n (finEmb E n x) : ℝ) ≤ heightOff q (finEmb E n x) ^ n := by
  classical
  set X := finEmb E n x with hX
  have hi : ∀ w : InfinitePlace E, ((AdelicGLn.det E n X : AdeleRing (𝓞 E) E)).1 w = 1 := fun w => by
    have h : ((AdelicGLn.det E n X : AdeleRing (𝓞 E) E)).1 w =
        (infAt w X : Matrix (Fin n) (Fin n) w.Completion).det := by
      rw [AdelicGLn.coe_det, ← infEval_apply, RingHom.map_det]; rfl
    rw [h, hX, infAt_finEmb']
    simp
  have hf : ∀ v : Pl E, ((AdelicGLn.det E n X : AdeleRing (𝓞 E) E)).2 v =
      (finAt v X : Matrix (Fin n) (Fin n) (v.adicCompletion E)).det := fun v => by
    rw [AdelicGLn.coe_det, ← finEval_apply, RingHom.map_det]; rfl
  have hg : ∀ w : Pl E, (∏ᶠ (_ : AdeleBaseChange.below F w ≠ q), locHeight (finAt w X)) =
      if AdeleBaseChange.below F w ≠ q then locHeight (finAt w X) else 1 := fun w => finprod_eq_if
  have hP : (∏ w : InfinitePlace E, locHeight (infAt w X) ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [hX, infAt_finEmb', locHeight_one, one_pow]
  have h1 := IdeleGroup.finite_mulSupport_norm (AdelicGLn.det E n X)
  have h2 := finite_mulSupport_locHeight_finAt X
  have e1 := finprod_eq_prod_of_mulSupport_subset (fun v : Pl E => ‖((AdelicGLn.det E n X : AdeleRing (𝓞 E) E)).2 v‖)
    (s := (h1.union h2).toFinset) (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inl hv)
  have e2 := finprod_eq_prod_of_mulSupport_subset
    (fun w : Pl E => if AdeleBaseChange.below F w ≠ q then locHeight (finAt w X) else 1)
    (s := (h1.union h2).toFinset) (fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      refine Or.inr fun h3 => hv ?_
      dsimp only
      split_ifs
      · exact h3
      · rfl)
  rw [show (detModule E n X : ℝ) = (IdeleGroup.ideleModule E (AdelicGLn.det E n X) : ℝ) from rfl,
    IdeleGroup.ideleModule_eq, heightOff, hP, one_mul]
  simp only [hg, hi, norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [e1, e2, ← Finset.prod_pow]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
  rw [hf]
  by_cases hb : AdeleBaseChange.below F v = q
  · have := hq ⟨v, liesOver_of_below hb⟩
    simp only [ne_eq, hb, not_true_eq_false, if_false, one_pow]
    exact this.le
  · rw [if_pos hb]
    exact norm_det_le_pow _

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.GM.tensHt : TensHt := by
  classical
  intro F E _ _ _ _ _ n hn q
  obtain ⟨D, N, -, hD⟩ := UpperTheory.adelicNorm_det_le_height_pow E n
  set m := 2 * Fintype.card (InfinitePlace E) with hm
  refine ⟨N * m + 1, fun Yf hYf => ?_⟩
  set M : ℝ := max 1 D with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hYf0 : 0 ≤ Yf := zero_le_one.trans hYf
  refine ⟨heightConst E n * M ^ m * Yf ^ (n * m) * Yf,
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le one_le_heightConst (one_le_pow₀ hM)) (one_le_pow₀ hYf)) hYf,
    fun β e Y hY hβ he g hg => ?_⟩
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  have hg' : kbar β (infPart E n (g : AdelicGLn.AdelicGL E n)) *
      e (finPart E n (g : AdelicGLn.AdelicGL E n)) ≠ 0 := by
    have := (UpperTheory.ConvolutionTheory.Tf.tensApply E n hn β e).1 g
    rw [this] at hg
    exact hg
  have he0 : e (finPart E n (g : AdelicGLn.AdelicGL E n)) ≠ 0 := right_ne_zero_of_mul hg'
  refine ⟨?_, he0⟩
  have hk := left_ne_zero_of_mul hg'
  obtain ⟨s, hs⟩ : ∃ s, β (infPart E n (g : AdelicGLn.AdelicGL E n) * zInf E n s) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hk (by simp [kbar, hc])
  set x := finPart E n (g : AdelicGLn.AdelicGL E n) with hx
  set G := infEmb E n (infPart E n (g : AdelicGLn.AdelicGL E n)) with hG
  set X := finEmb E n x with hX
  have hGX : G * X = (g : AdelicGLn.AdelicGL E n) := infEmb_infPart_mul_finEmb_finPart _
  set A := infEmb E n (infPart E n (g : AdelicGLn.AdelicGL E n) * zInf E n s) with hAdef
  have hA : A = G * centralSection E n s := by rw [hAdef, map_mul, infEmb_zInf]
  have hAY : AutomorphicForm.height A ≤ Y := hβ _ hs
  obtain ⟨hXY, hdet⟩ := he x he0
  have hq : ∀ w : PlacesOver E q, ‖((finAt w.1 (finEmb E n x) : GL (Fin n) (w.1.adicCompletion E)) :
      Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).det‖ = 1 := fun w => norm_eq_one_of_v (hdet w)
  have hq' : ∀ w : PlacesOver E q, ‖((finAt w.1 (finEmb E n x⁻¹) : GL (Fin n) (w.1.adicCompletion E)) :
      Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).det‖ = 1 := fun w => by
    rw [map_inv, finAt_inv]
    exact norm_det_inv _ (hq w)
  have hg1 : detModule E n (g : AdelicGLn.AdelicGL E n) = 1 := mem_normOneGL_iff_detModule.1 g.2
  have hGX1 : detModule E n G * detModule E n X = 1 := by rw [← map_mul, hGX, hg1]
  have hs_eq : detModule E n A * detModule E n X = s := by
    rw [hA, map_mul, detModule_centralSection hn, mul_right_comm, hGX1, one_mul]
  have hsR : (detModule E n A : ℝ) * (detModule E n X : ℝ) = s := congrArg Subtype.val hs_eq
  have hsR' : (detModule E n A⁻¹ : ℝ) * (detModule E n X⁻¹ : ℝ) = (s : ℝ)⁻¹ := by
    rw [map_inv, map_inv, Positive.coe_inv, Positive.coe_inv, ← mul_inv, hsR]
  have hb : ∀ B : AdelicGLn.AdelicGL E n, AutomorphicForm.height B ≤ Y →
      (detModule E n B : ℝ) ≤ M * Y ^ N := fun B hB =>
    (hD B).trans (mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (height_pos B).le hB N)
      (pow_nonneg (height_pos B).le N) hM0)
  have hxb : (detModule E n X : ℝ) ≤ Yf ^ n :=
    (module_le q x hq).trans (pow_le_pow_left₀ (heightOff_nonneg q _) hXY n)
  have hxb' : (detModule E n X⁻¹ : ℝ) ≤ Yf ^ n := by
    have h := module_le q x⁻¹ hq'
    rw [map_inv, heightOff_inv] at h
    exact h.trans (pow_le_pow_left₀ (heightOff_nonneg q _) hXY n)
  set L : ℝ := M * Y ^ N * Yf ^ n with hL
  have hL1 : 1 ≤ L := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hY)) (one_le_pow₀ hYf)
  have hMY : 0 ≤ M * Y ^ N := mul_nonneg hM0 (pow_nonneg hY0 N)
  have hsL : (s : ℝ) ≤ L := by
    rw [← hsR]
    exact mul_le_mul (hb A hAY) hxb (detModule E n X).2.le hMY
  have hsL' : (s : ℝ)⁻¹ ≤ L := by
    rw [← hsR']
    exact mul_le_mul (hb A⁻¹ (by rwa [height_inv])) hxb' (detModule E n X⁻¹).2.le hMY
  have hZ : AutomorphicForm.height (centralSection E n s) ≤ L ^ m := by
    set ee : ℝ := ((n * Module.finrank ℚ E : ℝ))⁻¹ with hee
    have he0' : 0 ≤ ee := by positivity
    have he1 : ee ≤ 1 := by
      rw [hee, ← Nat.cast_mul]
      exact Nat.cast_inv_le_one _
    have key : ∀ y : ℝ, 0 ≤ y → y ≤ L → y ^ ee ≤ L := fun y hy hyL =>
      calc y ^ ee ≤ L ^ ee := Real.rpow_le_rpow hy hyL he0'
        _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 he1
        _ = L := Real.rpow_one L
    refine height_diagUnits_posIdele_le (K := E) (n := n) (ρ := fun _ => (s : ℝ) ^ ee)
      (fun _ => Real.rpow_pos_of_pos s.2 ee) hL1 fun _ => ⟨key _ s.2.le hsL, ?_⟩
    rw [← Real.inv_rpow s.2.le]
    exact key _ (inv_pos.2 s.2).le hsL'
  have hGh : AutomorphicForm.height G ≤ heightConst E n * Y * L ^ m := by
    have h1 : G = A * (centralSection E n s)⁻¹ := by rw [hA, mul_inv_cancel_right]
    rw [h1]
    refine (height_mul_le _ _).trans ?_
    rw [height_inv]
    have hc0 : 0 ≤ heightConst E n := zero_le_one.trans one_le_heightConst
    exact mul_le_mul (mul_le_mul_of_nonneg_left hAY hc0) hZ (height_pos _).le (mul_nonneg hc0 hY0)
  have e1 : ∀ w, infAt w (g : AdelicGLn.AdelicGL E n) = infAt w G := fun w => by
    rw [← hGX, infAt_mul, hX, infAt_finEmb', mul_one]
  have e2 : ∀ w, finAt w (g : AdelicGLn.AdelicGL E n) = finAt w X := fun w => by
    rw [← hGX, finAt_mul, hG, finAt_infEmb, one_mul]
  have hsplit : heightOff q (g : AdelicGLn.AdelicGL E n) =
      (∏ w : InfinitePlace E, locHeight (infAt w G) ^ w.mult) * heightOff q X := by
    unfold heightOff
    simp only [e1, e2, hX, infAt_finEmb', locHeight_one, one_pow, Finset.prod_const_one, one_mul]
  have hPG : (∏ w : InfinitePlace E, locHeight (infAt w G) ^ w.mult) ≤ AutomorphicForm.height G :=
    le_mul_of_one_le_right (zero_le_one.trans (one_le_prod_locHeight G)) (one_le_finprod_locHeight G)
  rw [hsplit]
  calc (∏ w : InfinitePlace E, locHeight (infAt w G) ^ w.mult) * heightOff q X
      ≤ (heightConst E n * Y * L ^ m) * Yf :=
        mul_le_mul (hPG.trans hGh) hXY (heightOff_nonneg q _)
          (mul_nonneg (mul_nonneg (zero_le_one.trans one_le_heightConst) hY0) (pow_nonneg (zero_le_one.trans hL1) m))
    _ = heightConst E n * M ^ m * Yf ^ (n * m) * Yf * Y ^ (N * m + 1) := by
        rw [hL, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
        ring
end
