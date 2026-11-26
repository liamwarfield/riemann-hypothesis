module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.GenericFunctionalEquation.GenFE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat

@[expose] public section

attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.SideCenOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.HenQ Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.GJStandardLCuspidal UpperTheory.V UpperTheory.V.Z.Inf

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ArchOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal
open scoped SchwartzMap Classical

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem UpperTheory.V.Z.Inf.archOf :
    UpperTheory.V.Z.Inf.ArchOf := by
  intro hS hF hT hB K _ _ _ n hn ψ m hm fi hfi hne μ _
  obtain ⟨hsurj, hpe, habs, e, c, c', he, hc, hc', hΦ⟩ := hB K n μ
  obtain ⟨k, hk, hS⟩ := hS K n
  obtain ⟨κ, hκ, hF⟩ := hF K n e he
  have hcont : ContinuousOn (chart ψ.1 1) (invSet K n) := fun x hx =>
    (contDiffAt_chart ψ.2 1 hx).continuousAt.continuousWithinAt
  have hval : ∀ y, fi (archComp K n (infGL K n y)) = chart ψ.1 1 (toL y.val) := by
    intro y
    rw [hfi, hpe, chart_val, one_mul]
  have hne' : ∃ x ∈ invSet K n, chart ψ.1 1 x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨_, val_mem_invSet y, by rwa [← hval]⟩
  obtain ⟨Φ, hΦt, hdiff, s₀, hs₀⟩ := hT K n _ hcont hne'
  obtain ⟨hDt, hsh⟩ := hS ψ m hm Φ hΦt
  obtain ⟨φ, hφ, hφF⟩ := hΦ Φ hΦt
  obtain ⟨φ', hφ', hφF'⟩ := hΦ _ hDt
  refine ⟨φ, φ', k, κ, hk, hκ, ?_, ?_, ?_, ?_⟩
  · have h : archZeta μ φ fi = fun s => c * (fun s : ℂ => ∫ x, Φ x * chart ψ.1 1 x * ((UpperTheory.V.Z.Inf.nrm x : ℝ) : ℂ) ^ s)
        (s + ((n : ℂ) - 1) / 2 - n) := funext fun s => hφ fi _ hcont hval s
    rw [h]
    exact (hdiff.comp ((differentiable_id.add_const _).sub_const _)).const_mul c
  · intro h0
    have h := hφ fi _ hcont hval (s₀ + n - ((n : ℂ) - 1) / 2)
    rw [h0, show s₀ + n - ((n : ℂ) - 1) / 2 + ((n : ℂ) - 1) / 2 - n = s₀ by ring] at h
    exact mul_ne_zero hc hs₀ h.symm
  · intro s
    rw [hφ' fi _ hcont hval, hφ fi _ hcont hval, hsh 1 s]
    ring
  · intro g s
    unfold archZeta
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨y, rfl⟩ := hsurj x
    have hp : ((archAbsDet (archComp K n (infGL K n y)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (archAbsDet_pos _).ne'
    simp only [archIntegrand, archDetPow]
    rw [hφF, hφF', hF Φ hΦt, show s + 1 + ((n : ℂ) - 1) / 2 = (s + ((n : ℂ) - 1) / 2) + 1 by ring,
      Complex.cpow_add _ 1 hp, Complex.cpow_one, habs]
    ring
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.SatDict
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL
open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.GJStandardLCuspidal
open scoped Classical

namespace UpperTheory.V.Z.Inf

private theorem localEmbedding_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (w.adicCompletion K)) :
    AdelicGLn.localEmbedding w g = locGL K n w g := by
  refine Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun v => ?_
  change ((AdelicGLn.finiteRestrictedEquiv K n).symm _ : AdelicGLn.FiniteAdelicGL K n) a b v = _
  rw [AdelicGLn.finiteRestrictedEquiv_symm_apply, RestrictedProduct.coe_mulSingle_apply]
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (pLoc_locGL v g)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (pLoc_locGL_of_ne h g)).symm

private theorem isSatake_of_eig {K : Type} [Field K] [NumberField K] {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion K)) V)
    (hirr : ρ.IsIrreducible) (hs : IsSmooth ρ) (y : V) (hy : y ∈ fixedVectors ρ (integralGL (w.adicCompletion K) n))
    (l : Module.Dual ℂ V) (hl : l y ≠ 0) (z : Fin n → ℂˣ)
    (hE : Af.Smo.Eig w (Finset.univ.val.map z) fun g => l (ρ g y)) :
    Spherical.IsSatakeParameter (F := w.adicCompletion K) ρ (localHaar n w) z := by
  obtain ⟨hKeq, hu, hq, -⟩ := UpperTheory.V.Af.Smo.sphDict K n w
  have hTj := UpperTheory.V.Af.Smo.tjSet UpperTheory.V.Af.Smo.sphDict K n w
  have hf : ∀ g, ∀ k ∈ integralGL (w.adicCompletion K) n, l (ρ (g * k) y) = l (ρ g y) := by
    rw [hKeq]
    exact hE.inv
  have hT : ∀ r ≤ n, Spherical.minusculeHecke (localHaar n w) r ∈
      Spherical.eigenSubalgebra (localHaar n w) z (fun g => l (ρ g y)) hf := by
    intro r hr
    refine GlobalTheory.HenQ.ShellOp.minuscule_mem_of z hf hr fun g => ?_
    rw [hKeq, ← hTj r hr, hE.eig _ hu r hr g, hq r hr, GlobalTheory.HenQ.ShellOp.esymm_eq, GlobalTheory.LFun.satEig]
  have htop := Spherical.eigenSubalgebra_eq_top z hf hT (GlobalTheory.HenQ.ShellOp.central_mem_of_top z hf (hT n le_rfl))
  have hne : fixedVectors ρ (integralGL (w.adicCompletion K) n) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨y, hy, fun e => hl (by rw [e, map_zero])⟩
  obtain ⟨z', hz'⟩ := Spherical.exists_satakeParameter (μ := localHaar n w) hs hne
  intro h u hu'
  have h1 : h ∈ Spherical.eigenSubalgebra (localHaar n w) z (fun g => l (ρ g y)) hf := htop ▸ Algebra.mem_top
  have h2 := h1 1
  simp only [one_mul, map_one, one_apply_eq_self] at h2
  have h3 := dual_heckeAct (localHaar n w) (ρ := ρ) (h : HeckeAlgebra (localHaar n w)).mem (hs y) l
  rw [h2, hz' h y hy, map_smul, smul_eq_mul] at h3
  rw [hz' h u hu', mul_right_cancel₀ hl h3]

end UpperTheory.V.Z.Inf

open UpperTheory.V UpperTheory.V.Z.Inf in
theorem UpperTheory.V.Z.Inf.satDict :
    UpperTheory.V.Z.Inf.SatDict := by
  intro K _ _ _ n σ h D v B hB
  obtain ⟨z, rfl⟩ : ∃ z : Fin n → ℂˣ, Finset.univ.val.map z = B := by
    obtain ⟨l, rfl⟩ := Quotient.exists_rep B
    have hl : l.length = n := hB.card
    subst hl
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  refine ⟨z, ?_, rfl⟩
  by_cases hK : fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) = ⊥
  · intro f u hu
    rw [hK, Submodule.mem_bot] at hu
    subst hu
    rw [smul_zero]
    simpa using heckeAct_smul_right (μ := localHaar n v) (ρ := D.finite.π v) (f : HeckeAlgebra (localHaar n v)).mem 0
      (Submodule.zero_mem _)
  obtain ⟨a, x, hx, ha, hx0, hxK⟩ := exists_pureTensor_spherical (Cm.toRep σ h) D
  let J : D.finite.W v →ₗ[ℂ] σ.V := (Cm.carrierEq σ).toLinearMap ∘ₗ Iv D a x hx v
  have hJ : ∀ g y t, (J (D.finite.π v g y)).1.1 t = (J y).1.1 (t * finGL K n (locGL K n v g)) := by
    intro g y t
    have e : J (D.finite.π v g y) = σ.op (.fin (locGL K n v g)) (J y) := by
      rw [← localEmbedding_eq]
      exact (congrArg (Cm.carrierEq σ) (Iv_int D a x hx v g y)).trans (Cm.carrierEq_τ σ _ _)
    rw [e]
    rfl
  have h0 : J (x v) ≠ 0 := by
    intro e
    have e' : Iv D a x hx v (x v) = 0 := (Cm.carrierEq σ).map_eq_zero_iff.1 e
    rw [Iv_self] at e'
    exact phi_ne D a x hx ha hx0 e'
  obtain ⟨t, ht⟩ : ∃ t, (J (x v)).1.1 t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (Subtype.ext (Subtype.ext (funext hc)))
  let l : Module.Dual ℂ (D.finite.W v) :=
    { toFun := fun y => (J y).1.1 t
      map_add' := fun y y' => by rw [map_add (f := _)]; rfl
      map_smul' := fun c y => by rw [map_smul]; rfl }
  have hE := Af.StrongMultiplicityOne.eigOfSat K n σ v _ ((CG.hasSat_mk σ v _).1 hB) (J (x v)).1 (J (x v)).2 (fun g k hk => by
    rw [← (Af.Smo.sphDict K n v).1] at hk
    rw [← hJ, hxK v hK k hk]) t
  refine isSatake_of_eig v _ (D.finite.isIrreducible v) (D.finite.isAdmissible v).1 (x v) (hxK v hK) l ht z ?_
  have e : (fun g => l (D.finite.π v g (x v))) = fun g => (J (x v)).1.1 (t * finGL K n (locGL K n v g)) :=
    funext fun g => hJ g _ t
  rw [e]
  exact hE
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.BridgeOf
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal
open scoped SchwartzMap Classical

noncomputable section

namespace UpperTheory.V.Z.Inf.Bridge

open NumberField.mixedEmbedding GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ)

private theorem hms_infEq (x : Cinf K) : homeomorphMixedSpace K (infEq K x) = Cm.mixEq K x :=
  homeomorphMixedSpace_apply K _

private theorem coe_infEq : ⇑(infEq K) = (homeomorphMixedSpace K).symm ∘ Cm.mixEq K := by
  funext x
  rw [Function.comp_apply, ← hms_infEq, Homeomorph.symm_apply_apply]

private theorem coe_infEq_symm : ⇑(infEq K).symm = (Cm.mixEq K).symm ∘ homeomorphMixedSpace K := by
  funext x
  obtain ⟨y, rfl⟩ := (infEq K).surjective x
  rw [Function.comp_apply, hms_infEq, RingEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]

private def matC : Matrix (Fin n) (Fin n) (Cinf K) ≃ₜ* Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) :=
  { (infEq K).mapMatrix.toMulEquiv with
    continuous_toFun := by
      refine Continuous.matrix_map (f := infEq K) continuous_id ?_
      rw [coe_infEq]
      exact (homeomorphMixedSpace K).symm.continuous.comp
        (Cm.mixEq K).toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := by
      refine Continuous.matrix_map (f := (infEq K).symm) continuous_id ?_
      rw [coe_infEq_symm]
      exact (Cm.mixEq K).symm.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp
        (homeomorphMixedSpace K).continuous }

private def grpC : GL (Fin n) (Cinf K) ≃ₜ* AdelicGLn.InfiniteAdelicGL K n :=
  Units.mapContinuousMulEquiv (matC K n)

private theorem archComp_infGL (y : GL (Fin n) (Cinf K)) : archComp K n (infGL K n y) = grpC K n y := by
  refine Units.ext ?_
  rw [coe_archComp]
  exact Matrix.ext fun i j => Cm.infGL_entry y i j

private theorem symm_archComp (y : GL (Fin n) (Cinf K)) :
    (AdelicGLn.prodEquiv K n).symm (archComp K n (infGL K n y), 1) = infGL K n y := by
  rw [ContinuousMulEquiv.symm_apply_eq]
  exact Prod.ext rfl (pFin_infGL y).symm

private theorem archAbsDet_grpC (y : GL (Fin n) (Cinf K)) : archAbsDet (grpC K n y) = nrm (toL y.val) := by
  unfold archAbsDet nrm
  refine Finset.prod_congr rfl fun w _ => ?_
  have h : ((grpC K n y).val).det = infEq K (y.val).det := ((infEq K).map_det y.val).symm
  rw [h, Cm.infEq_apply, InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩]
  congr 1
  have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val.det w))
  rw [← this]
  exact congrArg _ ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).apply_symm_apply _)

private def linC : Lie K n ≃L[ℝ] (Fin n × Fin n → mixedSpace K) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x p => Cm.mixEq K (x p.1 p.2)
      invFun := fun z i j => (Cm.mixEq K).symm (z (i, j))
      map_add' := fun x y => funext fun p => map_add (Cm.mixEq K) _ _
      map_smul' := fun c x => funext fun p => map_smul (Cm.mixEq K) c _
      left_inv := fun x => funext fun i => funext fun j => (Cm.mixEq K).symm_apply_apply _
      right_inv := fun z => funext fun p => (Cm.mixEq K).apply_symm_apply _ }

private theorem archSchwartz_grpC (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ)) (y : GL (Fin n) (Cinf K)) :
    archSchwartz φ (grpC K n y).val = φ (linC K n (toL y.val)) :=
  congrArg φ (funext fun p => hms_infEq K _)

private theorem trace_mixEq (x : Cinf K) : mixedTrace K (Cm.mixEq K x) = 2 * ∑ w, (x w).re := by
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  rw [mixedTrace_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_add, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv (IsTotallyComplex.isComplex (K := K))) _ _ fun w => ?_
  exact congrArg (fun z : ℂ => 2 * z.re) (Cm.mixRing_snd x w)

private theorem pairing (x y : Lie K n) :
    mixedPairingPi K (linC K n x) (swapCLE K n (linC K n y)) = 2 * ∑ w, ((Matrix.of x * Matrix.of y).trace w).re := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← trace_mixEq, trace_mul_eq_sum, map_sum, map_sum, mixedPairingPi]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mixedTraceForm_apply, map_mul (Cm.mixEq K)]
  rfl

private theorem vol_haar : (volume : Measure (Lie K n)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin n → Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

private theorem four_eq : ∃ c' : ℂ, c' ≠ 0 ∧ ∀ (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ)) (y : Lie K n),
    archMatrixFourier φ (linC K n y) = c' * four (-4 * Real.pi) (fun x => φ (linC K n x)) y := by
  haveI := vol_haar K n
  haveI : (Measure.map (linC K n) (volume : Measure (Lie K n))).IsAddHaarMeasure :=
    (linC K n).isAddHaarMeasure_map _
  set ν := Measure.map (linC K n) (volume : Measure (Lie K n)) with hν
  have h := Measure.isAddLeftInvariant_eq_smul (mixedMeasurePi K : Measure (Fin n × Fin n → mixedSpace K)) ν
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (mixedMeasurePi K : Measure (Fin n × Fin n → mixedSpace K)) ν
  generalize Measure.addHaarScalarFactor (mixedMeasurePi K : Measure (Fin n × Fin n → mixedSpace K)) ν = c at h hpos
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hpos.ne', fun φ y => ?_⟩
  have e1 : archMatrixFourier φ (linC K n y) = mixedFourierPi K φ (swapCLE K n (linC K n y)) := by
    rw [← mixedFourierPiSchwartz_apply]
    rfl
  rw [e1, mixedFourierPi, h, integral_smul_nnreal_measure, hν,
    MeasurableEmbedding.integral_map (f := linC K n) (linC K n).toHomeomorph.measurableEmbedding, NNReal.smul_def, Complex.real_smul, four]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [pairing, Circle.smul_def, smul_eq_mul, mul_comm, Real.fourierChar_apply]
  congr 2
  push_cast
  ring

private theorem nrm_pos {x : Lie K n} (hx : x ∈ invSet K n) : 0 < nrm x := by
  have h : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
  exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (Pi.isUnit_iff.1 h w).ne_zero) _

private theorem continuous_nrm : Continuous (nrm : Lie K n → ℝ) := by
  have h : Continuous fun x : Lie K n => (Matrix.of x).det := Continuous.matrix_det continuous_id
  exact continuous_finsetProd _ fun w _ => (((continuous_apply w).comp h).norm).pow 2

private theorem haar_eq (hH : HaarL) (μ : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (F : AdelicGLn.InfiniteAdelicGL K n → ℂ) (H : Lie K n → ℂ), ContinuousOn H (invSet K n) →
      (∀ y, F (grpC K n y) = H (toL y.val)) → ∫ x, F x ∂μ = c * ∫ x in invSet K n, ((nrm x)⁻¹ ^ n : ℝ) • H x := by
  letI : MeasurableSpace (GL (Fin n) (Cinf K)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf K)) := ⟨rfl⟩
  obtain ⟨m, hm, hmap⟩ := hH K n
  haveI : (Measure.map (grpC K n) m).IsHaarMeasure := (grpC K n).isHaarMeasure_map _
  haveI : LocallyCompactSpace (AdelicGLn.InfiniteAdelicGL K n) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  haveI : SecondCountableTopology (AdelicGLn.InfiniteAdelicGL K n) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  have h := Measure.isMulLeftInvariant_eq_smul μ (Measure.map (grpC K n) m)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure μ (Measure.map (grpC K n) m)
  generalize Measure.haarScalarFactor μ (Measure.map (grpC K n) m) = c at h hpos
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hpos.ne', fun F H hc hF => ?_⟩
  have hme : MeasurableEmbedding (grpC K n) := (grpC K n).toHomeomorph.measurableEmbedding
  have hv : Continuous fun g : GL (Fin n) (Cinf K) => toL g.val :=
    Units.continuous_val (M := Matrix (Fin n) (Fin n) (Cinf K))
  have hms : MeasurableSet (invSet K n) := isOpen_invSet.measurableSet
  rw [h, integral_smul_nnreal_measure, hme.integral_map, NNReal.smul_def, Complex.real_smul]
  congr 1
  simp_rw [hF]
  rw [← integral_map hv.measurable.aemeasurable, hmap, integral_withDensity_eq_integral_toReal_smul]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal]
    exact pow_nonneg (inv_nonneg.2 (Finset.prod_nonneg fun w _ => sq_nonneg _)) _
  · exact (((continuous_nrm K n).measurable.inv).pow_const n).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  · rw [hmap]
    exact (hc.aestronglyMeasurable hms).mono_ac (withDensity_absolutelyContinuous _ _)

end UpperTheory.V.Z.Inf.Bridge

open UpperTheory.V.Z.Inf UpperTheory.V.Z.Inf.Bridge in
theorem UpperTheory.V.Z.Inf.bridgeOf :
    UpperTheory.V.Z.Inf.BridgeOf := by
  intro hH K _ _ _ n μ _
  obtain ⟨c, hc, hz⟩ := haar_eq K n hH μ
  obtain ⟨c', hc', hf⟩ := four_eq K n
  simp only [archComp_infGL]
  refine ⟨(grpC K n).surjective, fun y => by rw [← archComp_infGL, symm_archComp], archAbsDet_grpC K n,
    -4 * Real.pi, c, c', mul_ne_zero (by norm_num) Real.pi_ne_zero, hc, hc', fun Φ hΦ => ?_⟩
  have h1 : HasCompactSupport (Φ ∘ (linC K n).symm) := hΦ.2.1.comp_homeomorph (linC K n).symm.toHomeomorph
  have h2 := hΦ.1.comp (linC K n).symm.contDiff
  have h3 : ∀ x, h1.toSchwartzMap h2 (linC K n x) = Φ x := fun x =>
    congrArg Φ ((linC K n).symm_apply_apply x)
  refine ⟨h1.toSchwartzMap h2, fun fi f hcf hfi s => ?_, fun y => ?_⟩
  · rw [archZeta, hz _ (fun x => Φ x * f x * ((nrm x : ℝ) : ℂ) ^ (s + ((n : ℂ) - 1) / 2))]
    · congr 1
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := invSet K n) (μ := volume)]
      · refine setIntegral_congr_fun isOpen_invSet.measurableSet fun x hx => ?_
        have h0 : ((nrm x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (nrm_pos K n hx).ne'
        rw [Complex.cpow_sub _ _ h0, Complex.cpow_natCast, Complex.real_smul]
        push_cast
        rw [inv_pow, div_eq_mul_inv]
        ring
      · intro x hx
        rw [image_eq_zero_of_notMem_tsupport fun h => hx (hΦ.2.2 h), zero_mul, zero_mul]
    · refine (hΦ.1.continuous.continuousOn.mul hcf).mul ?_
      exact ContinuousOn.cpow_const (Complex.continuous_ofReal.comp (continuous_nrm K n)).continuousOn
        fun x hx => Complex.ofReal_mem_slitPlane.2 (nrm_pos K n hx)
    · intro y
      rw [archIntegrand, archSchwartz_grpC, h3, hfi, archDetPow, archAbsDet_grpC]
  · rw [archSchwartz_grpC, hf]
    simp only [h3]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.LocUnr
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Automorphic GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.HeckeAlgebra

namespace UpperTheory.V.Z.Inf.LocalUnramifiedTorus

section Alg

variable {F : Type} [Field F] {n : ℕ}

private theorem anti_symm :
    (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id = (1 : Matrix (Fin n) (Fin n) F).submatrix id Fin.rev := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.one_apply, Fin.rev_eq_iff]

private theorem anti_mul (A : Matrix (Fin n) (Fin n) F) :
    (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id * A = A.submatrix Fin.rev id := by
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) F) A Fin.rev (Equiv.refl (Fin n)) id
  simpa using this

private theorem mul_anti (A : Matrix (Fin n) (Fin n) F) :
    A * (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id = A.submatrix id Fin.rev := by
  rw [anti_symm]
  have := Matrix.submatrix_mul_equiv A (1 : Matrix (Fin n) (Fin n) F) id (Equiv.refl (Fin n)) Fin.rev
  simpa using this

private theorem anti_sq :
    (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id * (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id = 1 := by
  rw [anti_mul]
  ext i j
  simp [Matrix.one_apply]

variable (F n) in
private def wl : GL (Fin n) F :=
  ⟨(1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id, (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id, anti_sq, anti_sq⟩

private theorem wl_conj (g : GL (Fin n) F) (i j : Fin n) :
    ((wl F n * g * (wl F n)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (g : Matrix (Fin n) (Fin n) F) i.rev j.rev := by
  have : ((wl F n * g * (wl F n)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id * (g : Matrix (Fin n) (Fin n) F) *
        (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id := rfl
  rw [this, anti_mul, mul_anti]
  rfl

variable [ValuativeRel F]

private theorem wl_mem : wl F n ∈ integralGL F n := by
  have h : ∀ i j, ((1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id) i j ∈ (ValuativeRel.valuation F).integer := by
    intro i j
    simp only [Matrix.submatrix_apply, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [mem_integralGL_iff]
  exact ⟨h, h⟩

private theorem conj_unip {u : GL (Fin n) F} (hu : u ∈ unipotent F n) :
    wl F n * transposeInv F n u * (wl F n)⁻¹ ∈ unipotent F n := by
  have hi := (unipotent F n).inv_mem hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [wl_conj, coe_transposeInv, Matrix.transpose_apply]
    exact hi.1 (Fin.rev_lt_rev.2 hij)
  · change ((wl F n * transposeInv F n u * (wl F n)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = 1
    rw [wl_conj, coe_transposeInv, Matrix.transpose_apply]
    exact hi.2 _

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem conj_torus (l : Fin n → ℤ) :
    wl F n * transposeInv F n (torusPow F n l) * (wl F n)⁻¹ = torusPow F n fun i => -l i.rev := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [wl_conj, coe_transposeInv, Matrix.transpose_apply, torusPow, ← map_inv, coe_diagGL, coe_torusPow]
  by_cases h : i = j
  · subst h
    simp [Units.val_zpow_eq_zpow_val]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm)]

private theorem exponent_conj (g : GL (Fin n) F) :
    iwasawaExponent F n (wl F n * transposeInv F n g) = fun i => -iwasawaExponent F n g i.rev := by
  obtain ⟨u, hu, k, hk, hg⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
  set l := iwasawaExponent F n g
  have : wl F n * transposeInv F n g = (wl F n * transposeInv F n u * (wl F n)⁻¹) *
      (torusPow F n fun i => -l i.rev) * (wl F n * transposeInv F n k) := by
    rw [← conj_torus, hg, map_mul, map_mul]
    group
  rw [this]
  exact iwasawaExponent_eq F n (conj_unip hu) ((integralGL F n).mul_mem wl_mem (transposeInv_mem_integralGL hk))

private theorem halfPoint_rev (i : Fin n) : halfPoint F n i.rev = (halfPoint F n i)⁻¹ := by
  refine Units.ext ?_
  rw [Units.val_inv_eq_inv_val, halfPoint, halfPoint, Units.val_mk0, Units.val_mk0, halfModulus_eq, halfModulus_eq,
    rhoPair_single, rhoPair_single, ← zpow_neg, Fin.val_rev]
  congr 1
  have := i.is_lt
  omega

private theorem monomial_conj (l : Fin n → ℤ) (z : Fin n → ℂˣ) :
    monomialChar (fun i => -l i.rev) (((z⁻¹) ∘ (Fin.revPerm : Equiv.Perm (Fin n))) * halfPoint F n) =
      monomialChar l (z * halfPoint F n) := by
  rw [monomialChar_apply, monomialChar_apply]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  congr 1
  simp only [Pi.mul_apply, Function.comp_apply, Pi.inv_apply, Fin.revPerm_apply, halfPoint_rev]
  rw [← inv_zpow', mul_inv, inv_inv]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

private theorem evalAt_eq_integral (z : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt z (satakeTransform μ h) =
      ∫ g, (h : HeckeAlgebra μ) g * monomialChar (iwasawaExponent F n g) (z * halfPoint F n) ∂μ := by
  rw [satakeTransform_apply, evalAt_normalize, evalAt_satake, sphericalCharacter_apply, sphericalEigen]
  simp only [sphericalFun_unramifiedChar]

private def flip (h : SphericalHecke μ (F := F) (n := n)) : SphericalHecke μ (F := F) (n := n) :=
  HeckeAlgebraLevel.mk _ _ (HeckeAlgebra.mk μ (fun g => (h : HeckeAlgebra μ) (transposeInv F n g))
    ⟨(h : HeckeAlgebra μ).mem.1.comp_continuous continuous_transposeInv,
      (h : HeckeAlgebra μ).mem.2.comp_homeomorph (transposeInvHomeomorph (F := F) (n := n))⟩)
    (fun k hk x => by
      have := HeckeAlgebraLevel.val_mem _ _ h _ (transposeInv_mem_integralGL hk) (transposeInv F n x)
      change (h : HeckeAlgebra μ) (transposeInv F n (k * x)) = (h : HeckeAlgebra μ) (transposeInv F n x) ∧
        (h : HeckeAlgebra μ) (transposeInv F n (x * k)) = (h : HeckeAlgebra μ) (transposeInv F n x)
      rw [map_mul (transposeInv F n), map_mul (transposeInv F n)]
      exact this)

private theorem flip_apply (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    (flip h : HeckeAlgebra μ) g = (h : HeckeAlgebra μ) (transposeInv F n g) := rfl

private theorem evalAt_flip (z : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt z (satakeTransform μ (flip h)) = evalAt z⁻¹ (satakeTransform μ h) := by
  rw [← evalAt_comp_satakeTransform z⁻¹ Fin.revPerm h, evalAt_eq_integral, evalAt_eq_integral]
  set φ : GL (Fin n) F → ℂ := fun g => (h : HeckeAlgebra μ) g *
    monomialChar (iwasawaExponent F n g) (((z⁻¹) ∘ (Fin.revPerm : Equiv.Perm (Fin n))) * halfPoint F n) with hφ
  rw [← integral_mul_left_eq_self φ (wl F n), ← integral_comp_transposeInv μ fun g => φ (wl F n * g)]
  congr 1
  funext g
  dsimp only [φ]
  rw [exponent_conj, monomial_conj, flip_apply, (HeckeAlgebraLevel.val_mem _ _ h _ wl_mem _).1]

private theorem exists_pair {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
    (hπ : IsAdmissible π) (hK : fixedVectors π (integralGL F n) ≠ ⊥) :
    ∃ v₀ ∈ fixedVectors π (integralGL F n), ∃ ℓ₀ ∈ fixedVectors (Representation.dual π) (integralGL F n),
      ℓ₀ v₀ = 1 := by
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  obtain ⟨v₀, hv₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  have hne : (⟨v₀, hv₀⟩ : fixedVectors π (integralGL F n)) ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hne
  refine ⟨v₀, hv₀, f ∘ₗ fixedProj π hπ.1 hKc hKo, mem_fixedVectors_dual.2 fun k hk x => ?_, ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, fixedProj_apply_act hπ.1 hKc hKo hk]
  · have : fixedProj π hπ.1 hKc hKo v₀ = ⟨v₀, hv₀⟩ := Subtype.ext (fixedProj_apply_of_mem hπ.1 hKc hKo hv₀)
    simp only [LinearMap.coe_comp, Function.comp_apply, this, hf]

private theorem lfun_contra [NeZero n] {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} [π.IsIrreducible] (hπ : IsAdmissible π)
    (hK : fixedVectors π (integralGL F n) ≠ ⊥) {z : Fin n → ℂˣ} (hz : IsSatakeParameter π μ z) (t : ℂ) :
    LFunction (contragredient π) t = ∏ i, (1 - (z i : ℂ)⁻¹ * qs F t)⁻¹ := by
  obtain ⟨v₀, hv₀, ℓ₀, hℓK, hℓ⟩ := exists_pair hπ hK
  obtain ⟨z', hz', hL⟩ := exists_satakeParameter_contragredient π hπ μ hℓK hℓ
  have hsm : ℓ₀ ∈ smoothVectors (Representation.dual π) :=
    mem_smoothVectors_of_mem_fixedVectors (isOpen_integralGL F n) hℓK
  have hfix : (⟨ℓ₀, hsm⟩ : smoothVectors (Representation.dual π)) ∈
      fixedVectors (contragredient π) (integralGL F n) :=
    mem_fixedVectors_contragredient.2 (mem_fixedVectors_dual.1 hℓK)
  have hbi : ∀ k ∈ integralGL F n, ∀ x, Parabolic.matrixCoeff π v₀ ℓ₀ (k * x) = Parabolic.matrixCoeff π v₀ ℓ₀ x ∧
      Parabolic.matrixCoeff π v₀ ℓ₀ (x * k) = Parabolic.matrixCoeff π v₀ ℓ₀ x := by
    intro k hk x
    constructor
    · change ℓ₀ (π (k * x) v₀) = ℓ₀ (π x v₀)
      rw [map_mul, Module.End.mul_apply, mem_fixedVectors_dual.1 hℓK k hk]
    · change ℓ₀ (π (x * k) v₀) = ℓ₀ (π x v₀)
      rw [map_mul, Module.End.mul_apply, hv₀ k hk]
  have key : (evalAt z⁻¹).comp (satakeTransform μ (F := F) (n := n)) = (evalAt z').comp (satakeTransform μ) := by
    refine AlgHom.ext fun h => ?_
    have h1 := integral_mul_matrixCoeff_of_isSatakeParameter hz' hfix (evalSmooth π v₀) h
    have h2 := integral_mul_matrixCoeff_of_isSatakeParameter hz hv₀ ℓ₀ (flip h)
    have hev : evalSmooth π v₀ ⟨ℓ₀, hsm⟩ = 1 := hℓ
    rw [hev, mul_one] at h1
    rw [hℓ, mul_one, evalAt_flip] at h2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, ← h1, ← h2, ← integral_comp_transposeInv μ
      fun g => (h : HeckeAlgebra μ) g * Parabolic.matrixCoeff (contragredient π) ⟨ℓ₀, hsm⟩ (evalSmooth π v₀) g]
    congr 1
    funext g
    rw [flip_apply, ← matrixCoeff_inv_eq_contragredient, apply_inv_transposeInv hbi]
  obtain ⟨σ, rfl⟩ := (evalAt_comp_satakeTransform_eq_iff _ _).1 key
  rw [hL]
  refine Fintype.prod_equiv σ _ _ fun i => ?_
  simp only [Function.comp_apply, Pi.inv_apply, Units.val_inv_eq_inv_val]

end Alg

end UpperTheory.V.Z.Inf.LocalUnramifiedTorus

theorem UpperTheory.V.Z.Inf.locUnr :
    UpperTheory.V.Z.Inf.LocUnr := by
  intro K _ _ n hn v V _ _ π hirr hadm hK z hz t
  haveI : NeZero n := ⟨by omega⟩
  have hq : qs (v.adicCompletion K) t = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-t) := by
    rw [qs, GroundTheory.Global.residueCard_adicCompletion]
  rw [← hq]
  exact ⟨LFunction_eq_prod_of_isSatakeParameter hadm hK _ hz t, LocalUnramifiedTorus.lfun_contra hadm hK hz t⟩
end
end
