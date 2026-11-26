module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
public import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoLaws
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]

private theorem haar {n : ℕ} {U : Type} [Group U] [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (e : archCompact K n ≃ₜ* (ι → U)) (ν : Measure U) [IsProbabilityMeasure ν] (hl : ∀ k, MeasurePreserving (k * ·) ν ν)
    (hr : ∀ k, MeasurePreserving (· * k) ν ν) : IsHaarK (Measure.map e.symm (Measure.pi fun _ : ι => ν)) := by
  have hm : Measurable e.symm := e.symm.continuous.measurable
  have hE : MeasurePreserving e.symm (Measure.pi fun _ : ι => ν) (Measure.map e.symm (Measure.pi fun _ : ι => ν)) := ⟨hm, rfl⟩
  refine ⟨inferInstance, fun k => ?_, fun k => ?_⟩
  · refine hE.of_semiconj (measurePreserving_pi _ _ fun i => hl (e k i)) (fun x => ?_) (continuous_const_mul k).measurable
    change e.symm (e k * x) = _
    rw [map_mul, e.symm_apply_apply]
  · refine hE.of_semiconj (measurePreserving_pi _ _ fun i => hr (e k i)) (fun x => ?_) (continuous_mul_const k).measurable
    change e.symm (x * e k) = _
    rw [map_mul, e.symm_apply_apply]

private theorem coe_arc {n : ℕ} (k : archCompact K n) :
    ((arc1 k : G1 K n) : AdelicGLn.AdelicGL K n) = infEmb K n (k : archGroup K n) := by
  rw [arc1, ← retract_infEmb]
  exact congrArg Subtype.val (retractOne_coe (⟨_, maxCompact_le_normOneGL k.2⟩ : normOneGL (K := K) (n := n)))

private theorem zt0 : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

private theorem inf_fst {n : ℕ} (x : archGroup K n) (a b : Fin n) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (infEmb K n x a b).1 =
      (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from (x.1 : ArchMatrix K n)) a b := by
  rw [← AdelicGLn.prodEquiv_apply_fst, prodEquiv_infEmb]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _

private theorem inf_snd {n : ℕ} (x : archGroup K n) (a b : Fin n) :
    (infEmb K n x a b).2 = (1 : Matrix (Fin n) (Fin n) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) a b := by
  rw [← AdelicGLn.prodEquiv_apply_snd, prodEquiv_infEmb]
  rfl

omit [Fintype ι] in
private theorem ent (C : Co K ι) {n : ℕ} (x : ι → unitaryGroup (Fin n) ℂ) (i : ι) (a b : Fin n) :
    C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K (infEmb K n ((C.Φ n).symm x : archCompact K n) a b).1) i =
      (x i : Matrix (Fin n) (Fin n) ℂ) a b := by
  rw [inf_fst, ← C.Ψ_val, ← C.Φ_val, ContinuousMulEquiv.apply_symm_apply]

omit [Fintype ι] in
private theorem blkA (C : Co K ι) (a b : ι → U2) :
    lv (arc1 ((C.Φ 2).symm a)) (arc1 ((C.Φ 2).symm b)) 0 = arc1 ((C.Φ (2 + 2)).symm fun i => bd (a i) (b i)) := by
  apply Subtype.ext
  rw [(blkLaws (K := K)).1, neg_zero, zt0, mul_one, mul_one, coe_arc, coe_arc, coe_arc]
  ext r s
  obtain ⟨r, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective r
  obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective s
  refine Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace K).injective (C.c.injective (funext fun i => ?_))) ?_
  · rw [ent, u4.1]
    simp only [blk, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rcases r with r | r <;> rcases s with s | s
    · exact ent C a i r s
    · change C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K 0) i = 0
      rw [map_zero, map_zero]; rfl
    · change C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K 0) i = 0
      rw [map_zero, map_zero]; rfl
    · exact ent C b i r s
  · rw [inf_snd, ← Matrix.submatrix_apply (1 : Matrix _ _ _) finSumFinEquiv finSumFinEquiv, Matrix.submatrix_one_equiv,
      ← Matrix.fromBlocks_one]
    simp only [blk, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rcases r with r | r <;> rcases s with s | s
    · exact inf_snd _ r s
    · rfl
    · rfl
    · exact inf_snd _ r s

private theorem cmm {n : ℕ} (g : archGroup K n) (h : FA K n) : Commute (archP K n g) (fin1 h) :=
  (MultiplicityOne.finProj_mul_archProj_comm h g).symm

private theorem dec (n : ℕ) (k : G1 K n) (hk : k ∈ KG K n) :
    ∃ (a : archCompact K n) (h : FA K n), h ∈ AdelicGLn.integralFiniteGL K n ∧ k = arc1 a * fin1 h := by
  have hk' : (k : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact := hk
  have e := infEmb_infPart_mul_finEmb_finPart (k : AdelicGLn.AdelicGL K n)
  have hf : finEmb K n (finPart K n k) ∈ Reduction.maxCompact := by
    refine ⟨fun w => ?_, fun v => ?_⟩
    · have : infAt w (finEmb K n (finPart K n k)) = 1 := by
        refine Units.ext (Matrix.ext fun a b => ?_)
        change (finEmb K n (finPart K n k) a b).1 w = _
        rw [← AdelicGLn.prodEquiv_apply_fst, prodEquiv_finEmb]
        by_cases h : a = b
        · subst h; simp; rfl
        · simp [h]; rfl
      rw [this]; exact one_mem _
    · have : finAt v (finEmb K n (finPart K n k)) = finAt v (k : AdelicGLn.AdelicGL K n) := by
        exact Units.ext (Matrix.ext fun a b => rfl)
      rw [this]; exact hk'.2 v
  refine ⟨⟨infPart K n k, ?_⟩, finPart K n k, (AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => ?_, Subtype.ext ?_⟩
  · change infEmb K n (infPart K n k) ∈ Reduction.maxCompact
    rw [eq_mul_inv_of_mul_eq e]
    exact mul_mem hk' (inv_mem hf)
  · have : (AdelicGLn.finiteRestrictedEquiv K n (finPart K n k) v : GL (Fin n) (v.adicCompletion K)) =
        finAt v (k : AdelicGLn.AdelicGL K n) := by
      exact Units.ext (Matrix.ext fun a b => rfl)
    rw [this]; exact hk'.2 v
  · rw [Subgroup.coe_mul, coe_arc, fin1, MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL hf)]
    exact e.symm

private noncomputable def GG (C : Co K ι) : (ι → GL (Fin 2) ℂ) →* G1 K 2 := (archP K 2).comp (C.Ψ 2).symm.toMonoidHom

omit [Fintype ι] in
private theorem gl_eq (C : Co K ι) (i : ι) (a : GL (Fin 2) ℂ) : C.gl i a = GG C (Pi.mulSingle i a) := rfl

omit [Fintype ι] in
private theorem GG_eq (C : Co K ι) (g : archGroup K 2) : archP K 2 g = GG C (C.Ψ 2 g) :=
  congrArg (archP K 2) ((C.Ψ 2).symm_apply_apply g).symm

omit [Fintype ι] in
private theorem GG_cmm (C : Co K ι) (x : ι → GL (Fin 2) ℂ) (h : FA K 2) : Commute (GG C x) (fin1 h) := cmm _ h

omit [Fintype ι] in
private theorem ms_cont (i : ι) : Continuous fun m : GL (Fin 2) ℂ => (Pi.mulSingle i m : ι → GL (Fin 2) ℂ) :=
  continuous_pi fun j => by
    by_cases h : j = i
    · subst h; simpa using continuous_id'
    · simpa [h] using continuous_const

omit [Fintype ι] in
private theorem spl (C : Co K ι) (i : ι) (g : G1 K 2) : ∃ a h, g = C.gl i a * h ∧ ∀ b, Commute h (C.gl i b) := by
  obtain ⟨A, u, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj g
  obtain ⟨x, hx⟩ : ∃ x, archProj K 2 A = GG C x := ⟨_, GG_eq C ⟨A, Subgroup.mem_top _⟩⟩
  refine ⟨x i, GG C (Function.update x i 1) * fin1 u, ?_, fun b => Commute.mul_left ?_ ?_⟩
  · have : Pi.mulSingle i (x i) * Function.update x i 1 = x := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [gl_eq, ← mul_assoc, ← map_mul, this, hx]
  · rw [gl_eq]
    refine Commute.map ?_ (GG C)
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  · rw [gl_eq]
    exact (GG_cmm C _ u).symm

omit [Fintype ι] in
private theorem lst (C : Co K ι) (g : archGroup K 2) :
    ∃ a : ι → GL (Fin 2) ℂ, ∀ l : List ι, l.Nodup → (∀ i, i ∈ l) → archP K 2 g = (l.map fun i => C.gl i (a i)).prod := by
  refine ⟨C.Ψ 2 g, fun l hl hm => ?_⟩
  rw [GG_eq C]
  generalize C.Ψ 2 g = x
  have : (l.map fun i => (Pi.mulSingle i (x i) : ι → GL (Fin 2) ℂ)).prod = x := by
    funext j
    rw [Pi.list_prod_apply, List.map_map, List.prod_map_eq_pow_single j, List.count_eq_one_of_mem hl (hm j)]
    · simp
    · intro i hi _
      simp [hi.symm]
  conv_lhs => rw [← this, map_list_prod, List.map_map]
  rfl

omit [Fintype ι] in
private theorem un_eq (C : Co K ι) (i : ι) (m : U2) : C.un i m = C.gl i (kC m) := by
  refine congrArg (archP K 2) ((C.Ψ 2).injective (funext fun j => Units.ext ?_))
  rw [← C.Φ_val, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coLaws :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι), IsHaarK C.κ₂ ∧ (∀ μ, Haar4 μ → IsHaarK (C.κ₄ μ)) ∧ (∀ i m, C.un i m = C.gl i (kC m)) ∧ (∀ i, Continuous (C.gl i)) ∧
      (∀ i a b, C.gl i (a * b) = C.gl i a * C.gl i b) ∧ (∀ i j, i ≠ j → ∀ a b, Commute (C.gl i a) (C.gl j b)) ∧
      (∀ i a (h : FA K 2), Commute (C.gl i a) (fin1 h)) ∧ (∀ i (g : G1 K 2), ∃ a h, g = C.gl i a * h ∧ ∀ b, Commute h (C.gl i b)) ∧
      (∀ g : archGroup K 2, ∃ a : ι → GL (Fin 2) ℂ, ∀ l : List ι, l.Nodup → (∀ i, i ∈ l) → archP K 2 g = (l.map fun i => C.gl i (a i)).prod) ∧
      (∀ a b : ι → U2, lv (arc1 ((C.Φ 2).symm a)) (arc1 ((C.Φ 2).symm b)) 0 = arc1 ((C.Φ (2 + 2)).symm fun i => bd (a i) (b i))) ∧
      (∀ n (k : archCompact K n) (h : FA K n), Commute (arc1 k) (fin1 h)) ∧
      ∀ n, ∀ k ∈ KG K n, ∃ (a : archCompact K n) (h : FA K n), h ∈ AdelicGLn.integralFiniteGL K n ∧ k = arc1 a * fin1 h := by
  intro K _ _ _ ι _ C
  refine ⟨haar _ _ (measurePreserving_mul_left μK) (measurePreserving_mul_right μK), fun μ hμ => ?_, un_eq C, fun i => ?_,
    fun i a b => ?_, fun i j hij a b => ?_, fun i a h => cmm _ h, spl C, lst C, blkA C, fun n k h => cmm _ h, dec⟩
  · haveI := hμ.prob
    exact haar _ μ hμ.left hμ.right
  · exact continuous_archP.comp ((C.Ψ 2).symm.continuous.comp (ms_cont i))
  · rw [gl_eq, gl_eq, gl_eq, Pi.mulSingle_mul, map_mul]
  · rw [gl_eq, gl_eq]
    exact (Pi.mulSingle_commute (f := fun _ => GL (Fin 2) ℂ) hij a b).map (GG C)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.MinSwap
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.SingleShift
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section

open PositivityTheory.Rg.Tf.Geo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem gal_infEmb (σ : E ≃ₐ[F] E) (n : ℕ) (a : archGroup E n) :
    Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.toRingEquiv) (infEmb E n a) =
      infEmb E n (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) := by
  apply (AdelicGLn.prodEquiv E n).injective
  rw [prodEquiv_infEmb, ContinuousMulEquiv.symm_apply_apply]
  refine Prod.ext ?_ ?_
  · have h1 : UpperTheory.ConvolutionTheory.T4.pI E n (infEmb E n a) = (archEquiv E n).symm a := congrArg Prod.fst (prodEquiv_infEmb a)
    rw [← UpperTheory.ConvolutionTheory.K.galAdEq F E σ, ← h1]
    exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).1 _
  · have h2 : (AdelicGLn.prodEquiv E n (infEmb E n a)).2 = 1 := congrArg Prod.snd (prodEquiv_infEmb a)
    have h3 : (AdelicGLn.prodEquiv E n
        (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.toRingEquiv) (infEmb E n a))).2 =
        mapGL n (Formalism.L2.Host.CT.finMap σ.toRingEquiv) (AdelicGLn.prodEquiv E n (infEmb E n a)).2 :=
      Units.ext (Matrix.ext fun _ _ => rfl)
    rw [h3, h2, map_one]

private theorem compA_shift {σ : E ≃ₐ[F] E} {m : ℕ} (D : InfD σ m) (n : ℕ) (a : archGroup E n) (i : Fin (m + 1)) :
    compA D n i (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) = compA D n (i + 1) a := by
  have e : ∀ j x, compA D n j x = archEquiv F n (D.comp n j ((archEquiv E n).symm x)) := fun _ _ => rfl
  rw [e, e, ContinuousMulEquiv.symm_apply_apply]
  congr 1
  exact Units.ext (Matrix.ext fun p q => D.map_shift _ i)

private theorem single_shift {ι G : Type} [One G] (s i : Fin 2) (u v : ι) (m : G) :
    (Pi.mulSingle (s, u) m : Fin 2 × ι → G) (i + 1, v) = (Pi.mulSingle (s + 1, u) m : Fin 2 × ι → G) (i, v) := by
  have h : i + 1 = s ↔ i = s + 1 := by revert i s; decide
  simp only [Pi.mulSingle_apply, Prod.mk.injEq, h]

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coTw :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1) (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      (∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u) →
      ∀ (μ : Measure (G1 E 2)) [μ.IsHaarMeasure] (θ : Twist μ), UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ → ∀ s u m, θ.e (CE.un (s, u) m) = CE.un (s + 1, u) m := by
  intro F E _ _ _ _ _ _ _ σ D CF CE hC μ _ θ hθ s u m
  apply Subtype.ext
  rw [hθ]
  simp only [Co.un, arc1, archimedeanProjection_maximalCompact]
  rw [gal_infEmb]
  congr 1
  apply (CE.Ψ 2).injective
  funext ⟨i, v⟩
  rw [hC, compA_shift, ← hC]
  apply Units.ext
  rw [← CE.Φ_val, ← CE.Φ_val, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  congr 1
  convert single_shift s i u v m
end

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.minSwap :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1) (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      (∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u) →
      ∀ (μ : Measure (G1 E 2)) [μ.IsHaarMeasure] (θ : Twist μ), UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ → ∀ τ₁ τ₂ : Submodule ℂ (LL μ),
        τ₁.map (θ.U : LL μ →ₗ[ℂ] LL μ) = τ₂ → ∀ s u n q, CE.MinAt μ τ₁ (s, u) n q → CE.MinAt μ τ₂ (s + 1, u) n q := by
  intro F E _ _ _ _ _ _ _ σ D CF CE hC μ _ θ hθ τ₁ τ₂ hτ s u n q hmin
  obtain ⟨hnorm, -, hint⟩ := UpperTheory.ConvolutionTheory.Dp.twUnitary E 2 μ θ
  have htw := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coTw F E σ D CF CE hC μ θ hθ
  let L : LL μ →ₗᵢ[ℂ] LL μ := ⟨(θ.U : LL μ →ₗ[ℂ] LL μ), hnorm⟩
  have hL : ∀ v, L v = θ.U v := fun _ => rfl
  have key : ∀ n' q' v, θ.U (CE.Pi μ (s, u) n' q' v) = CE.Pi μ (s + 1, u) n' q' (θ.U v) := by
    intro n' q' v
    unfold Co.Pi
    rw [← hL, ← L.integral_comp_comm]
    congr 1
    funext m
    rw [map_smul, hL, hint, htw]
  subst hτ
  obtain ⟨⟨v, hv, hne⟩, hz⟩ := hmin
  refine ⟨⟨θ.U v, Submodule.mem_map_of_mem hv, fun h => hne ?_⟩, ?_⟩
  · rw [← key] at h
    rw [← norm_eq_zero, ← hnorm, h, norm_zero]
  · rintro n' q' hn _ ⟨w, hw, rfl⟩
    have := key n' q' w
    rw [hz n' q' hn w hw, map_zero] at this
    exact this.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.UpdateMulSingle
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

section Gen

variable {ι : Type} [Fintype ι] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]

private theorem integ_of_cont {X : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] {f : X → ℂ} (hf : Continuous f) : Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

omit [Fintype ι] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem single_mul_eq (i : ι) (h : G) (k : ι → G) :
    (Pi.mulSingle i h : ι → G) * k = Function.update k i (h * k i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

omit [Fintype ι] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem update_mul_single (i : ι) (y h : G) (k : ι → G) :
    Function.update k i y * (Pi.mulSingle i h : ι → G) = Function.update k i (y * h) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

private theorem integral_update [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (i : ι) {F : (ι → G) → ℂ}
    (hF : Continuous F) :
    ∫ k, F k ∂(Measure.pi fun _ : ι => μ) =
      ∫ k, ∫ h, F (Function.update k i h) ∂μ ∂(Measure.pi fun _ : ι => μ) := by
  have h1 : ∀ k : ι → G, ∫ h, F (Function.update k i h) ∂μ = ∫ h, F ((Pi.mulSingle i h : ι → G) * k) ∂μ := by
    intro k
    simp only [single_mul_eq]
    exact (integral_mul_right_eq_self (fun h => F (Function.update k i h)) (k i)).symm
  simp only [h1]
  rw [integral_integral_swap]
  · have h2 : ∀ h : G, ∫ k, F ((Pi.mulSingle i h : ι → G) * k) ∂(Measure.pi fun _ : ι => μ) =
        ∫ k, F k ∂(Measure.pi fun _ : ι => μ) := fun h => integral_mul_left_eq_self F _
    simp [h2]
  · apply integ_of_cont
    exact hF.comp (((continuous_mulSingle i).comp continuous_snd).mul continuous_fst)

private theorem fix_prod [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {M : Type} [Group M] [TopologicalSpace M]
    [IsTopologicalGroup M] (j : G → M) (hj : Continuous j) (t : ι → G → ℂ) (ht : ∀ i, Continuous (t i))
    (Ψ : (ι → M) → ℂ) (hΨ : Continuous Ψ)
    (h : ∀ i g, ∫ m, t i m * Ψ (g * (Pi.mulSingle i (j m) : ι → M)) ∂μ = Ψ g) (g : ι → M) :
    ∫ m : ι → G, (∏ i, t i (m i)) * Ψ (g * fun i => j (m i)) ∂(Measure.pi fun _ : ι => μ) = Ψ g := by
  have key : ∀ s : Finset ι, ∫ m : ι → G, (∏ i ∈ s, t i (m i)) * Ψ (g * fun i => if i ∈ s then j (m i) else 1)
      ∂(Measure.pi fun _ : ι => μ) = Ψ g := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun _ : ι => (1 : M)) = 1 := rfl
      simp [this]
    | insert a s ha ih =>
      rw [integral_update μ a, ← ih]
      · refine integral_congr_ae (Eventually.of_forall fun m => ?_)
        beta_reduce
        rw [← h a, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        beta_reduce
        have e1 : ∏ i ∈ s, t i (Function.update m a y i) = ∏ i ∈ s, t i (m i) :=
          Finset.prod_congr rfl fun i hi => by
            rw [Function.update_of_ne (show i ≠ a from fun hh => ha (by rwa [← hh]))]
        have e2 : (g * fun i => if i ∈ insert a s then j (Function.update m a y i) else 1) =
            (g * fun i => if i ∈ s then j (m i) else 1) * (Pi.mulSingle a (j y) : ι → M) := by
          funext i
          by_cases hi : i = a
          · subst hi; simp [ha]
          · simp [hi]
        rw [Finset.prod_insert ha, e1, e2, Function.update_self]
        ring
      · refine (continuous_finsetProd _ fun i _ => (ht i).comp (continuous_apply i)).mul
          (hΨ.comp (continuous_const.mul (continuous_pi fun i => ?_)))
        split_ifs
        · exact hj.comp (continuous_apply i)
        · exact continuous_const
  simpa using key Finset.univ

private theorem fix_slice [μ.IsMulLeftInvariant] (e : ι → G → ℂ) (he : ∀ i, Idem μ (e i)) (Φ : (ι → G) → ℂ)
    (hΦ : Continuous Φ) (hf : RFix (Measure.pi fun _ : ι => μ) (fun k => ∏ i, e i (k i)) Φ) (i : ι) (g₀ : ι → G) :
    RFix μ (e i) fun y => Φ (Function.update g₀ i y) := by
  intro y
  simp only [← update_mul_single]
  generalize Function.update g₀ i y = g
  have h1 : ∀ h : G, Φ (g * (Pi.mulSingle i h : ι → G)) =
      ∫ k, e i (h⁻¹ * k i) * ((∏ j ∈ Finset.univ.erase i, e j (k j)) * Φ (g * k)) ∂(Measure.pi fun _ : ι => μ) := by
    intro h
    rw [← hf (g * (Pi.mulSingle i h : ι → G)),
      ← integral_mul_left_eq_self _ (Pi.mulSingle i h⁻¹ : ι → G)]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    beta_reduce
    have e1 : ∏ j ∈ Finset.univ.erase i, e j (((Pi.mulSingle i h⁻¹ : ι → G) * k) j) =
        ∏ j ∈ Finset.univ.erase i, e j (k j) :=
      Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
    have e2 : g * (Pi.mulSingle i h : ι → G) * ((Pi.mulSingle i h⁻¹ : ι → G) * k) = g * k := by
      rw [mul_assoc, ← mul_assoc (Pi.mulSingle i h : ι → G), ← Pi.mulSingle_mul]; simp
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), e1, e2]
    simp [mul_assoc]
  simp only [h1, ← integral_const_mul]
  rw [integral_integral_swap]
  · rw [← hf g]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    beta_reduce
    simp only [← mul_assoc (e i _), mul_assoc (e i _ * _)]
    rw [integral_mul_const, (he i).idem, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_assoc]
  · apply integ_of_cont
    refine ((he i).cont.comp continuous_fst).mul (((he i).cont.comp
      (continuous_fst.inv.mul ((continuous_apply i).comp continuous_snd))).mul
      ((continuous_finsetProd _ fun j _ => (he j).cont.comp ((continuous_apply j).comp continuous_snd)).mul
        (hΦ.comp (continuous_const.mul continuous_snd))))

private theorem aboveSlice {ι : Type} {j : U2 → U4} {n : ℕ} {q : ℤ} {Φ : (ι → U4) → ℂ} (c : ι) (k : ι → U4)
    (h : LAbove (fun m => (Pi.mulSingle c (j m) : ι → U4)) n q Φ) :
    LAbove j n q fun y => Φ (Function.update k c y) := by
  intro n' q' hn l y
  have := h n' q' hn l (Function.update k c y)
  simpa only [single_mul_eq, Function.update_self, Function.update_idem] using this

end Gen

private theorem continuous_alt (n : ℕ) (q : ℤ) : Continuous (T n q) := by
  unfold T
  exact continuous_const.mul (Complex.continuous_conj.comp (KT.continuous_psi n q n))

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.extPi :
    ∀ (ι : Type) [Fintype ι] (μ : Measure U4) (e : ι → U4 → ℂ) n q n' q' (x : ι → U4), Haar4 μ →
      (∀ i, Ext μ (e i) (n i) (q i) (n' i) (q' i) (x i)) → ExtP μ e n q n' q' x := by
  intro ι _ μ e n q n' q' x hμ hE
  haveI : IsProbabilityMeasure μ := hμ.prob
  haveI : μ.IsMulLeftInvariant := ⟨fun g => (hμ.left g).map_eq⟩
  haveI : μ.IsMulRightInvariant := ⟨fun g => (hμ.right g).map_eq⟩
  obtain ⟨-, -, -, -, hbd, -, -, -, -, -, -, hcpt, -⟩ := u4
  haveI : CompactSpace U4 := hcpt
  have hb1 : Continuous fun m : U2 => bd m 1 := hbd.comp (continuous_id.prodMk continuous_const)
  have hb2 : Continuous fun m : U2 => bd 1 m := hbd.comp (continuous_const.prodMk continuous_id)
  have hcontS : ∀ (Φ : (ι → U4) → ℂ), Continuous Φ → ∀ (i : ι) (k : ι → U4),
      Continuous fun y => Φ (Function.update k i y) := fun Φ hΦ i k =>
    hΦ.comp (continuous_const.update i continuous_id)
  have hsl : ∀ (Φ : (ι → U4) → ℂ) (i : ι) (g : ι → U4) (h : U4),
      Φ (g * (Pi.mulSingle i h : ι → U4) * x) =
        (fun y => Φ (Function.update (g * x) i y)) (g i * h * x i) := by
    intro Φ i g h
    beta_reduce
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have hsl0 : ∀ (Φ : (ι → U4) → ℂ) (i : ι) (g : ι → U4),
      Φ (g * x) = (fun y => Φ (Function.update (g * x) i y)) (g i * x i) := by
    intro Φ i g
    beta_reduce
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have hidem : ∀ i, Idem μ (e i) := fun i => (hE i).idem
  refine ⟨⟨continuous_finsetProd _ fun i _ => (hE i).idem.cont.comp (continuous_apply i), ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k
    simp only [Pi.inv_apply, (hE _).idem.star, map_prod]
  · intro k
    have h1 : ∀ h : ι → U4, (∏ i, e i (h i)) * ∏ i, e i ((h⁻¹ * k) i) = ∏ i, e i (h i) * e i ((h i)⁻¹ * k i) := by
      intro h
      simp only [Pi.mul_apply, Pi.inv_apply, Finset.prod_mul_distrib]
    simp only [h1]
    rw [integral_fintype_prod_eq_prod (fun i h => e i h * e i (h⁻¹ * k i))]
    exact Finset.prod_congr rfl fun i _ => (hE i).idem.idem (k i)
  · intro Φ hΦ hR g
    constructor
    · refine fix_prod μK (fun m => bd m 1) hb1 (fun i => T (n i) (q i)) (fun i => continuous_alt _ _)
        (fun y => Φ (y * x)) (hΦ.comp (continuous_id.mul continuous_const)) ?_ g
      intro i g
      beta_reduce
      simp only [hsl Φ i g]
      rw [hsl0 Φ i g]
      exact ((hE i).fix _ (hcontS Φ hΦ i _) (fix_slice μ e hidem Φ hΦ hR i _) (g i)).1
    · refine fix_prod μK (fun m => bd 1 m) hb2 (fun i => T (n' i) (q' i)) (fun i => continuous_alt _ _)
        (fun y => Φ (y * x)) (hΦ.comp (continuous_id.mul continuous_const)) ?_ g
      intro i g
      beta_reduce
      simp only [hsl Φ i g]
      rw [hsl0 Φ i g]
      exact ((hE i).fix _ (hcontS Φ hΦ i _) (fix_slice μ e hidem Φ hΦ hR i _) (g i)).2
  · intro Φ hΦ hR hL hL' h0
    have key : ∀ s : Finset ι, ∀ k : ι → U4, (∀ i, i ∉ s → ∃ a b, k i = bd a b * x i) → Φ k = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro k hk
        choose a b hab using fun i => hk i (Finset.notMem_empty i)
        have : k = (fun i => bd (a i) (b i)) * x := funext hab
        rw [this]
        exact h0 a b
      | insert c s hc ih =>
        intro k hk
        have hz := (hE c).inj (fun y => Φ (Function.update k c y)) (hcontS Φ hΦ c k)
          (fix_slice μ e hidem Φ hΦ hR c k) (aboveSlice c k (hL c)) (aboveSlice c k (hL' c)) ?_
        · have := congrFun hz (k c)
          simpa using this
        · intro a b
          refine ih _ fun i hi => ?_
          by_cases hic : i = c
          · subst hic
            exact ⟨a, b, Function.update_self ..⟩
          · rw [Function.update_of_ne hic]
            exact hk i (by simp [hic, hi])
    funext k
    exact key Finset.univ k fun i hi => absurd (Finset.mem_univ i) hi
  · choose ψ hc hfix hval using fun i => (hE i).ex
    refine ⟨fun k => ∏ i, ψ i (k i), continuous_finsetProd _ fun i _ => (hc i).comp (continuous_apply i), ?_, ?_⟩
    · intro g
      have h1 : ∀ k : ι → U4, (∏ i, e i (k i)) * ∏ i, ψ i ((g * k) i) = ∏ i, e i (k i) * ψ i (g i * k i) := by
        intro k
        simp only [Pi.mul_apply, Finset.prod_mul_distrib]
      simp only [h1]
      rw [integral_fintype_prod_eq_prod (fun i h => e i h * ψ i (g i * h))]
      exact Finset.prod_congr rfl fun i _ => hfix i (g i)
    · intro a b
      simp only [Pi.mul_apply, hval, map_prod, Finset.prod_mul_distrib]
end
