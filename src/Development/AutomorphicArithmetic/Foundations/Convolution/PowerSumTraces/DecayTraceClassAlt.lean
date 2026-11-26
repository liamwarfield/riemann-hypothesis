module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.CuspDecay

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
noncomputable section

open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core

namespace UpperTheory.ConvolutionTheory.C

def fcalc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (φ : ℝ → ℝ) (A : H →L[ℂ] H) :
    H →L[ℂ] H := cfc φ A

def TwistUnitary : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ),
    ∃ U : L2 μ ≃ₗᵢ[ℂ] L2 μ, (U : L2 μ →L[ℂ] L2 μ) = θ.U ∧
      (∀ g v, U (rightRegularRep (Gam K n) μ g v) = rightRegularRep (Gam K n) μ (θ.e g) (U v)) ∧
      (cuspidalL2 μ).map (U : L2 μ →ₗ[ℂ] L2 μ) = cuspidalL2 μ

def CuspTrSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ), MultOneAt μ →
    (∀ B : L2 μ →L[ℂ] L2 μ, (∀ V, IsSummand μ V → ∀ v ∈ V, B v ∈ V) → IsTraceClass (Pc μ ∘L B ∘L Pc μ) →
      HasSum (fun V : {V // IsSummand μ V ∧ V.map (θ.U : L2 μ →ₗ[ℂ] L2 μ) = V} => trOn V.1 (B ∘L θ.U))
        (trace (Pc μ ∘L B ∘L θ.U ∘L Pc μ))) ∧
    ∀ f : CC K n, IsTraceClass (Pc μ ∘L Rop μ f ∘L Pc μ) →
      HasSum (fun V : {V // IsSummand μ V ∧ V.map (θ.U : L2 μ →ₗ[ℂ] L2 μ) = V} => trOn V.1 (Rop μ f ∘L θ.U))
        (cuspTr μ θ f)

def PolyBdAll : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n), PolyBd μ a

def SmoothDecay : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n),
    IsLeftSmooth a → CuspDecay μ a

def DecayTraceClass : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a g : CC K n)
    (M : L2 μ →L[ℂ] L2 μ), CuspDecay μ a → CuspDecay μ (CuspidalProjection.ccStar g) → M ∘L Pc μ = Pc μ ∘L M →
    IsTraceClass (Pc μ ∘L (Rop μ a ∘L M ∘L Rop μ g) ∘L Pc μ)

def CuspTrBand : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ), MultOneAt μ →
    ∀ A : L2 μ →L[ℂ] L2 μ, 0 ≤ A → (∀ V, IsSummand μ V → ∀ v ∈ V, A v ∈ V) → IsCompactOperator (A ∘L Pc μ) →
    ∀ η : ℝ, 0 < η → ∃ S : Finset (ℝ × Submodule ℂ (L2 μ)),
      (∀ p, p ∈ S ↔ η < p.1 ∧ IsSummand μ p.2 ∧ p.2.map (θ.U : L2 μ →ₗ[ℂ] L2 μ) = p.2 ∧ eigIn p.2 A p.1 ≠ ⊥) ∧
      (∀ p ∈ S, FiniteDimensional ℂ (eigIn p.2 A p.1)) ∧
      ∀ (φ : ℝ → ℝ) (c : ℝ) (T : L2 μ →L[ℂ] L2 μ), Continuous φ → 0 ≤ c → (∀ x ∈ Set.Icc 0 η, |φ x| ≤ c) →
        (∀ V, IsSummand μ V → ∀ v ∈ V, T v ∈ V) → IsTraceClass (Pc μ ∘L T ∘L Pc μ) →
        ‖trace (Pc μ ∘L fcalc φ A ∘L T ∘L θ.U ∘L Pc μ) - ∑ p ∈ S, (φ p.1 : ℂ) * trOn (eigIn p.2 A p.1) (T ∘L θ.U)‖ ≤
          c * (traceNorm (Pc μ ∘L T ∘L Pc μ)).toReal

end UpperTheory.ConvolutionTheory.C
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OpBasics
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

private theorem compact_of_restrict {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) (hW : IsClosed (W : Set H)) (A : H →L[ℂ] H) (T : W →L[ℂ] W)
    (hT : IsCompactOperator T) (h : W.subtypeL ∘L T = A ∘L W.subtypeL) :
    IsCompactOperator (A ∘L prj W) := by
  have hmem : ∀ v, prj W v ∈ W := fun v => by
    have h1 : prj W v ∈ W.topologicalClosure := W.topologicalClosure.starProjection_apply_mem v
    rwa [hW.submodule_topologicalClosure_eq] at h1
  let P := (prj W).codRestrict W hmem
  have hP : W.subtypeL ∘L P = prj W :=
    ContinuousLinearMap.subtypeL_comp_codRestrict _ _ _
  have e : A ∘L prj W = (W.subtypeL ∘L T) ∘L P := by
    rw [h, ContinuousLinearMap.comp_assoc, hP]
  rw [e]
  exact (hT.clm_comp W.subtypeL).comp_clm P

theorem UpperTheory.ConvolutionTheory.C.opBasics :
    UpperTheory.ConvolutionTheory.C.OpBasics := by
  intro K _ _ n μ _ f
  refine ⟨fun V hV v hv => ?_, fun v hv => ?_, ?_⟩
  · exact UnitaryRep.IsInvariant.integrated_mem _ μ hV.closed hV.inv _ hv
  · exact UnitaryRep.IsInvariant.integrated_mem _ μ (isClosed_cuspidalL2 μ)
      (isInvariant_cuspidalL2 μ) _ hv
  · exact compact_of_restrict _ (isClosed_cuspidalL2 μ) _ _ (isCompactOperator_cuspRep μ f)
      (subtypeL_comp_integrated μ _)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandsSpan
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

section Generic

variable {G H : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (π : UnitaryRep G H) (W : Submodule ℂ H) [CompleteSpace W]
  (hWi : π.IsInvariant W)

private theorem isSummandOf_map (hWc : IsClosed (W : Set H))
    (V : Submodule ℂ W) [CompleteSpace V] (hinv : (π.restrict W hWi).IsInvariant V)
    (hirr : ((π.restrict W hWi).restrict V hinv).IsIrreducible) :
    IsSummandOf π W (V.map W.subtype) := by
  have hVc : IsClosed (V : Set W) :=
    (completeSpace_coe_iff_isComplete.1 ‹CompleteSpace V›).isClosed
  have hemb : Topology.IsClosedEmbedding ((↑) : W → H) := hWc.isClosedEmbedding_subtypeVal
  refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
  · have h := hemb.isClosedMap _ hVc
    simpa [Submodule.map_coe] using h
  · rintro g _ ⟨w, hw, rfl⟩
    exact ⟨π.restrict W hWi g w, hinv g w hw, rfl⟩
  · haveI := hirr.1
    obtain ⟨w, hw0⟩ := exists_ne (0 : V)
    intro hb
    have hm : ((w : W) : H) ∈ V.map W.subtype := ⟨w.1, w.2, rfl⟩
    rw [hb, Submodule.mem_bot] at hm
    exact hw0 (Subtype.ext (Subtype.ext hm))
  · intro V' hle hcl hinv'
    have hYc : IsClosed (((V'.comap W.subtype).comap V.subtype : Submodule ℂ V) : Set V) :=
      hcl.preimage (continuous_subtype_val.comp continuous_subtype_val)
    have hYi : ((π.restrict W hWi).restrict V hinv).IsInvariant
        ((V'.comap W.subtype).comap V.subtype) := fun g v hv => hinv' g _ hv
    rcases hirr.2 _ hYc hYi with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hle hx
      have hm : (⟨w, hw⟩ : V) ∈ (V'.comap W.subtype).comap V.subtype := hx
      rw [h, Submodule.mem_bot] at hm
      have h0 : w = 0 := congrArg Subtype.val hm
      simp [h0]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨w, hw, rfl⟩
      have hm : (⟨w, hw⟩ : V) ∈ (V'.comap W.subtype).comap V.subtype := h ▸ Submodule.mem_top
      exact hm

private theorem closure_iSup_summands (hWc : IsClosed (W : Set H))
    (s : Set (Submodule ℂ W)) [∀ V : s, CompleteSpace (V : Submodule ℂ W)]
    (hinv : ∀ V : s, (π.restrict W hWi).IsInvariant V)
    (hH : IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ W)) (fun V => (V : Submodule ℂ W).subtypeₗᵢ))
    (hirr : ∀ V : s, ((π.restrict W hWi).restrict V (hinv V)).IsIrreducible) :
    (⨆ V : {V // IsSummandOf π W V}, V.1).topologicalClosure = W := by
  have hmain : ∀ V : s, IsSummandOf π W ((V : Submodule ℂ W).map W.subtype) :=
    fun V => isSummandOf_map π W hWi hWc V.1 (hinv V) (hirr V)
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (iSup_le fun V => V.2.le) hWc
  · set S : Submodule ℂ H := ⨆ V : {V // IsSummandOf π W V}, V.1
    have hcl : IsClosed ((S.topologicalClosure.comap W.subtype : Submodule ℂ W) : Set W) :=
      S.isClosed_topologicalClosure.preimage continuous_subtype_val
    have hle : (⨆ V : s, (V : Submodule ℂ W)) ≤
        S.topologicalClosure.comap W.subtype := by
      refine iSup_le fun V w hw => ?_
      exact S.le_topologicalClosure
        (le_iSup (fun V : {V // IsSummandOf π W V} => V.1) ⟨_, hmain V⟩ ⟨w, hw, rfl⟩)
    have hspan : (⨆ V : s, (V : Submodule ℂ W)).topologicalClosure = ⊤ := by
      simpa only [Submodule.subtypeₗᵢ_toLinearMap, Submodule.range_subtype] using
        hH.OrthogonalFamily.range_linearIsometry.symm.trans
          (LinearMap.range_eq_top.2 hH.surjective_isometry)
    have htop : (⊤ : Submodule ℂ W) ≤ S.topologicalClosure.comap W.subtype := by
      rw [← hspan]
      exact Submodule.topologicalClosure_minimal _ hle hcl
    intro x hx
    exact htop (Submodule.mem_top : (⟨x, hx⟩ : W) ∈ ⊤)

end Generic

theorem UpperTheory.ConvolutionTheory.C.summandsSpan :
    UpperTheory.ConvolutionTheory.C.SummandsSpan := by
  intro K _ _ n μ _
  obtain ⟨s, hc, hinv, hH, hirr⟩ := exists_isHilbertSum_isIrreducible_cuspidal μ
  haveI := hc
  exact closure_iSup_summands (rightRegularRep (rationalGLOne (K := K) (n := n)) μ) (cuspidalL2 μ)
    (isInvariant_cuspidalL2 μ) (isClosed_cuspidalL2 μ) s hinv hH hirr
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigSummands
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TraceSum
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

private theorem exists_adapted {H ι : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ι → Submodule ℂ H) (hc : ∀ i, IsClosed (U i : Set H)) (ho : Pairwise fun i j => U i ⟂ U j)
    (ht : ∀ x : H, (∀ i, x ∈ (U i)ᗮ) → x = 0) :
    ∃ (κ : ι → Type) (b : HilbertBasis (Σ i, κ i) ℂ H), ∀ i k, b ⟨i, k⟩ ∈ U i := by
  haveI : ∀ i, CompleteSpace (U i) := fun i => (hc i).completeSpace_coe
  choose w b hb using fun i => exists_hilbertBasis ℂ (U i)
  have hfam : OrthogonalFamily ℂ (fun i => U i) fun i => (U i).subtypeₗᵢ :=
    OrthogonalFamily.of_pairwise ho
  have hon : Orthonormal ℂ fun a : Σ i, w i => (U a.1).subtypeₗᵢ (b a.1 a.2) :=
    hfam.orthonormal_sigma_orthonormal fun i => (b i).orthonormal
  have hsp : (Submodule.span ℂ (Set.range fun a : Σ i, w i => (U a.1).subtypeₗᵢ (b a.1 a.2)))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine ht x fun i => ?_
    rw [Submodule.mem_orthogonal']
    intro u hu
    have h1 := ((innerSL ℂ x).comp (U i).subtypeL).hasSum ((b i).hasSum_repr ⟨u, hu⟩)
    have h2 : ∀ k, inner ℂ x ((b i k : U i) : H) = 0 := fun k =>
      (Submodule.mem_orthogonal' _ _).1 hx _ (Submodule.subset_span ⟨⟨i, k⟩, rfl⟩)
    simp only [map_smul, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, innerSL_apply_apply, h2,
      smul_zero] at h1
    exact h1.unique hasSum_zero
  refine ⟨fun i => w i, HilbertBasis.mkOfOrthogonalEqBot hon hsp, fun i k => ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact (b i k).2

private theorem inner_prj {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (T : H →L[ℂ] H) (x : H) :
    inner ℂ x ((prj V ∘L T ∘L prj V) x) = inner ℂ (prj V x) (T (prj V x)) := by
  simp only [ContinuousLinearMap.comp_apply, prj]
  exact (Submodule.inner_starProjection_left_eq_right _ _ _).symm

theorem UpperTheory.ConvolutionTheory.C.traceSum :
    UpperTheory.ConvolutionTheory.C.TraceSum := by
  intro H ι _ _ _ V T ho hT
  set W := ⨆ i, V i with hW
  let U : Option ι → Submodule ℂ H := fun o => o.elim W.topologicalClosureᗮ fun i => (V i).topologicalClosure
  have hle : ∀ i, (V i).topologicalClosure ≤ W.topologicalClosure := fun i =>
    Submodule.topologicalClosure_mono (le_iSup V i)
  have hoU : Pairwise fun i j => U i ⟂ U j := by
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact (Submodule.isOrtho_orthogonal_left _).mono_right (hle j)
    · exact (Submodule.isOrtho_orthogonal_right _).mono_left (hle i)
    · have h := ho (fun e => hij (congrArg some e) : i ≠ j)
      change (V i).topologicalClosure ≤ (V j).topologicalClosureᗮ
      rw [Submodule.orthogonal_closure]
      exact Submodule.topologicalClosure_minimal _ h (Submodule.isClosed_orthogonal _)
  obtain ⟨κ, b, hb⟩ := exists_adapted U (by
      rintro (_ | i)
      · exact Submodule.isClosed_orthogonal _
      · exact Submodule.isClosed_topologicalClosure _) hoU (by
      intro x hx
      have h1 : x ∈ W.topologicalClosureᗮ := by
        rw [Submodule.orthogonal_closure, hW, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
        intro i
        have := hx (some i)
        change x ∈ (V i).topologicalClosureᗮ at this
        rwa [Submodule.orthogonal_closure] at this
      exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (hx none) x h1))
  have hWs : ∀ i k, prj W (b ⟨some i, k⟩) = b ⟨some i, k⟩ := fun i k =>
    Submodule.starProjection_eq_self_iff.2 (hle i (hb (some i) k))
  have hWn : ∀ k, prj W (b ⟨none, k⟩) = 0 := fun k =>
    (Submodule.starProjection_apply_eq_zero_iff _).2 (hb none k)
  have hVs : ∀ i k, prj (V i) (b ⟨some i, k⟩) = b ⟨some i, k⟩ := fun i k =>
    Submodule.starProjection_eq_self_iff.2 (hb (some i) k)
  have hVn : ∀ i o k, o ≠ some i → prj (V i) (b ⟨o, k⟩) = 0 := fun i o k h =>
    (Submodule.starProjection_apply_eq_zero_iff _).2 (hoU h (hb o k))
  have htc : ∀ i, IsTraceClass (prj (V i) ∘L T ∘L prj (V i)) := fun i => by
    have e1 : prj (V i) ∘L prj W = prj (V i) := Submodule.starProjection_comp_starProjection_of_le (hle i)
    have e2 : ∀ x, prj W (prj (V i) x) = prj (V i) x := fun x =>
      Submodule.starProjection_eq_self_iff.2 (hle i (Submodule.starProjection_apply_mem _ _))
    have e3 : ∀ x, prj (V i) (prj W x) = prj (V i) x := fun x => DFunLike.congr_fun e1 x
    have := (hT.comp_left (prj (V i))).comp_right (prj (V i))
    convert this using 1
    ext x
    simp only [ContinuousLinearMap.comp_apply, e2, e3]
  have h0 := hT.hasSum_trace b
  simp only [inner_prj] at h0
  have h1 : HasSum (fun o : Option ι => o.elim 0 fun i => trOn (V i) T) (trOn W T) := by
    refine h0.sigma ?_
    rintro (_ | i)
    · simpa only [hWn, inner_zero_left, Option.elim_none] using hasSum_zero
    · have h2 := (htc i).hasSum_trace b
      simp only [inner_prj] at h2
      rw [← (sigma_mk_injective (i := some i)).hasSum_iff] at h2
      · simpa only [Function.comp_def, hVs, hWs, Option.elim_some, trOn] using h2
      · rintro ⟨o, k⟩ hk
        rw [hVn i o k, inner_zero_left]
        rintro rfl
        exact hk ⟨k, rfl⟩
  rw [← (Option.some_injective ι).hasSum_iff] at h1
  · exact h1
  · rintro (_ | i) h
    · rfl
    · exact absurd ⟨i, rfl⟩ h
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

section SlopeTestRemainingChoices

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem isHS_prj (E : Submodule ℂ H) [FiniteDimensional ℂ E] : IsHilbertSchmidt (prj E) := by
  have hcl : E.topologicalClosure = E :=
    (Submodule.closed_of_finiteDimensional E).submodule_topologicalClosure_eq
  haveI : FiniteDimensional ℂ E.topologicalClosure := by rw [hcl]; infer_instance
  have h1 : IsHilbertSchmidt (E.topologicalClosure.subtypeL) := by
    rw [isHilbertSchmidt_iff (stdOrthonormalBasis ℂ E.topologicalClosure).toHilbertBasis, tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.pow_lt_top enorm_lt_top
  exact h1.comp_right E.topologicalClosure.orthogonalProjection

private theorem mem_eigIn {W : Submodule ℂ H} {A : H →L[ℂ] H} {x : ℝ} {v : H} :
    v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

private theorem prj_mem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V := by
  have h : prj V v ∈ V.topologicalClosure := Submodule.starProjection_apply_mem _ v
  rwa [hV.submodule_topologicalClosure_eq] at h

private theorem prj_eq_zero {V : Submodule ℂ H} {v : H} (hv : v ∈ Vᗮ) : prj V v = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).2 (by rwa [Submodule.orthogonal_closure])

private theorem prj_self {V : Submodule ℂ H} {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)

private theorem sub_prj_mem (V : Submodule ℂ H) (v : H) : v - prj V v ∈ Vᗮ := by
  have h := Submodule.sub_starProjection_mem_orthogonal (K := V.topologicalClosure) v
  rwa [Submodule.orthogonal_closure] at h

private theorem prj_comm {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (hinv : ∀ v ∈ V, A v ∈ V) (v : H) : prj V (A v) = A (prj V v) := by
  have hu := sub_prj_mem V v
  have hadj : ContinuousLinearMap.adjoint A = A := (ContinuousLinearMap.isSelfAdjoint_iff').1 hA
  have hAu : A (v - prj V v) ∈ Vᗮ := by
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro w hw
    rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
    exact hu _ (hinv w hw)
  have h : A v = A (prj V v) + A (v - prj V v) := by
    rw [← map_add (f := _)]; congr 1; abel
  rw [h, map_add (f := _), prj_eq_zero hAu, add_zero, prj_self (hinv _ (prj_mem hV v))]

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.C.eigSummands :
    UpperTheory.ConvolutionTheory.C.EigSummands := by
  intro H ι _ _ _ V W A x hc ho hW hA hinv hfd
  classical
  let E : ι → Submodule ℂ H := fun i => eigIn (V i) A x
  have hVW : ∀ i, V i ≤ W := fun i => hW ▸ (le_iSup V i).trans (Submodule.le_topologicalClosure _)
  have hEW : ∀ i, E i ≤ eigIn W A x := fun i => inf_le_inf_right _ (hVW i)
  have hEV : ∀ i, E i ≤ V i := fun i => inf_le_left
  have hEo : Pairwise fun i j => E i ⟂ E j := fun i j hij => (ho hij).mono (hEV i) (hEV j)
  have hfin : {i | E i ≠ ⊥}.Finite := by
    have hex : ∀ i : {i | E i ≠ ⊥}, ∃ v ∈ E i, v ≠ 0 := fun i => (Submodule.ne_bot_iff _).1 i.2
    choose v hvE hv0 using hex
    have hli : LinearIndependent ℂ v := linearIndependent_of_ne_zero_of_inner_eq_zero hv0 fun i j hij =>
      (hEo fun e => hij (Subtype.ext e)).inner_eq (hvE i) (hvE j)
    let v' : {i | E i ≠ ⊥} → eigIn W A x := fun i => ⟨v i, hEW i (hvE i)⟩
    have hli' : LinearIndependent ℂ v' := LinearIndependent.of_comp (eigIn W A x).subtype hli
    exact Set.finite_coe_iff.1 hli'.finite_of_isNoetherian
  let s := hfin.toFinset
  have hs : ∀ i, i ∈ s ↔ E i ≠ ⊥ := fun i => by simp [s]
  have hPE : ∀ i, ∀ v ∈ eigIn W A x, prj (V i) v ∈ E i := by
    intro i v hv
    refine mem_eigIn.2 ⟨prj_mem (hc i) v, ?_⟩
    rw [← prj_comm (hc i) hA (hinv i), (mem_eigIn.1 hv).2, map_smul]
  have hPP : ∀ i j, i ≠ j → ∀ v, prj (V j) (prj (V i) v) = 0 := fun i j hij v =>
    prj_eq_zero ((ho hij) (prj_mem (hc i) v))
  have hsup : eigIn W A x = ⨆ i ∈ s, E i := by
    refine le_antisymm (fun v hv => ?_) (iSup₂_le fun i _ => hEW i)
    have hu : ∑ i ∈ s, prj (V i) v ∈ ⨆ i ∈ s, E i :=
      Submodule.sum_mem _ fun i hi => (le_iSup₂_of_le i hi le_rfl : E i ≤ ⨆ i ∈ s, E i) (hPE i v hv)
    have huE : ∑ i ∈ s, prj (V i) v ∈ eigIn W A x :=
      (iSup₂_le fun i _ => hEW i : (⨆ i ∈ s, E i) ≤ eigIn W A x) hu
    have hw : v - ∑ i ∈ s, prj (V i) v ∈ W := sub_mem (mem_eigIn.1 hv).1 (mem_eigIn.1 huE).1
    have hPw : ∀ j, prj (V j) (v - ∑ i ∈ s, prj (V i) v) = 0 := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      by_cases hj : j ∈ s
      · rw [Finset.sum_eq_single_of_mem j hj (fun i _ hij => hPP i j hij v), prj_self (prj_mem (hc j) v), sub_self]
      · have h0 : prj (V j) v = 0 := by
          have hb : E j = ⊥ := by_contra fun h => hj ((hs j).2 h)
          have h1 := hPE j v hv
          rw [hb] at h1
          exact (Submodule.mem_bot ℂ).1 h1
        rw [h0, Finset.sum_eq_zero (fun i hi => hPP i j (ne_of_mem_of_not_mem hi hj) v), sub_zero]
    have hperp : v - ∑ i ∈ s, prj (V i) v ∈ Wᗮ := by
      rw [← hW, Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro j
      have h := sub_prj_mem (V j) (v - ∑ i ∈ s, prj (V i) v)
      rwa [hPw j, sub_zero] at h
    have hz : v - ∑ i ∈ s, prj (V i) v = 0 :=
      inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hperp _ hw)
    rw [sub_eq_zero.1 hz]
    exact hu
  refine ⟨s, hs, hsup, fun T => ?_⟩
  have hS : (⨆ i : s, E i) = eigIn W A x := by
    rw [hsup, iSup_subtype']
  have htc : IsTraceClass (prj (⨆ i : s, E i) ∘L T ∘L prj (⨆ i : s, E i)) := by
    rw [hS]
    exact isTraceClass_comp (isHS_prj _) ((isHS_prj _).comp_left T)
  have h := UpperTheory.ConvolutionTheory.C.traceSum H s (fun i => E i) T (fun i j hij => hEo fun e => hij (Subtype.ext e)) htc
  rw [hS] at h
  rw [h.unique (hasSum_fintype _)]
  exact Finset.sum_coe_sort s fun i => trOn (E i) T
end
