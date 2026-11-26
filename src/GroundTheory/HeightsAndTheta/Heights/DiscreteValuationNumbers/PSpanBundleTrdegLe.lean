module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleTrdegLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IntermediateField.algebraAdjoinAdjoin

noncomputable section


set_option maxHeartbeats 400000 in
theorem SpanBundleTrdegLe.proof : SpanBundleTrdegLe.Statement := by
  intro F _ Ω _ _ K _ ι y M i G c a H _hc hH hGH Φ _ _ s

  let κΦ : Φ →+* FractionRing (MvPolynomial (Option K) Φ) :=
    (algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))).comp C
  let κ : Ω →+* FractionRing (MvPolynomial (Option K) Φ) := κΦ.comp (algebraMap Ω Φ)
  let _ : Algebra F (FractionRing (MvPolynomial (Option K) Φ)) := (κ.comp (algebraMap F Ω)).toAlgebra
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))) :=
    IsFractionRing.injective _ _
  let Xo : Option K → FractionRing (MvPolynomial (Option K) Φ) := fun o =>
    algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ)) (X o)

  let gy : (Σ k, ι k) → FractionRing (MvPolynomial (Option K) Φ) := fun p => κ (y p) * Xo (some p.1)

  have hAy : Algebra.trdeg F (Algebra.adjoin F (Set.range gy)) ≤
      Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) := by
    have hθ : ∀ f, (aeval gy : MRing ι F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) f =
        algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))
          (rename some (map (algebraMap Ω Φ) (pointConeMap F y f))) := by
      intro f
      have e := MvPolynomial.ringHom_ext
        (f := ((aeval gy : MRing ι F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) :
          MRing ι F →+* FractionRing (MvPolynomial (Option K) Φ)))
        (g := ((algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))).comp
          (((rename some : MvPolynomial K Φ →ₐ[Φ] MvPolynomial (Option K) Φ) :
            MvPolynomial K Φ →+* MvPolynomial (Option K) Φ).comp
            ((map (algebraMap Ω Φ)).comp (pointConeMap F y : MRing ι F →+* MvPolynomial K Ω)))))
        (fun r => by
          simp [pointConeMap, MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra, κ, κΦ])
        (fun p => by simp [pointConeMap, gy, κ, κΦ, Xo])
      exact congrArg (fun φ => φ f) e
    rw [Algebra.adjoin_range_eq_range_aeval]
    refine trdeg_le_of_surjective (Ideal.Quotient.liftₐ (pointIdeal F y) (aeval gy).rangeRestrict ?_) ?_
    · intro f hf
      apply Subtype.ext
      change (aeval gy) f = 0
      rw [hθ, show pointConeMap F y f = 0 from hf]
      simp
    · intro x
      obtain ⟨f, rfl⟩ := AlgHom.rangeRestrict_surjective _ x
      exact ⟨Ideal.Quotient.mk _ f, rfl⟩

  have hSyL : Algebra.trdeg F (Algebra.adjoin F (Set.range gy)) =
      Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) := by
    have : FaithfulSMul F (Algebra.adjoin F (Set.range gy)) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
    have : FaithfulSMul F (IntermediateField.adjoin F (Set.range gy)) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
    have e := trdeg_add_eq F (Algebra.adjoin F (Set.range gy))
      (A := IntermediateField.adjoin F (Set.range gy))
    rwa [trdeg_eq_zero (R := Algebra.adjoin F (Set.range gy)), add_zero] at e

  have hchart : ∀ u ∈ chartRing F (segreVec y) c, κ u ∈ IntermediateField.adjoin F (Set.range gy) := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem u hu =>
      obtain ⟨c', rfl⟩ := hu
      have hQ : ∏ k, Xo (some k) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun k _ => (map_ne_zero_iff _ hinj).2 (X_ne_zero _)
      have e : κ (segreVec y c' / segreVec y c) = (∏ k, gy ⟨k, c' k⟩) / ∏ k, gy ⟨k, c k⟩ := by
        simp only [gy, Finset.prod_mul_distrib, segreVec, map_div₀, map_prod]
        rw [mul_div_mul_right _ _ hQ]
      rw [e]
      exact div_mem (prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩)
        (prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩)
    | algebraMap r => exact IntermediateField.algebraMap_mem _ r
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | mul u v _ _ hu hv => rw [map_mul]; exact mul_mem hu hv

  choose g hg hGm using hGH
  set p0 : Ω := ∏ k, y ⟨k, c k⟩ ^ a k with hp0
  have hgL : ∀ l m, κ (g l m) ∈ IntermediateField.adjoin F (Set.range gy) := fun l m => hchart _ (hg l m)

  let w : Fin i → FractionRing (MvPolynomial (Option K) Φ) := fun m =>
    κ p0 * κΦ (∑ m', algebraMap Ω Φ (H⁻¹ m m') * s m') * Xo none
  let T := (aeval w : MvPolynomial (Fin i) (IntermediateField.adjoin F (Set.range gy)) →ₐ[_]
    FractionRing (MvPolynomial (Option K) Φ)).range
  have hTi : Algebra.trdeg (IntermediateField.adjoin F (Set.range gy)) T ≤ i := by
    have := trdeg_le_of_surjective _ (AlgHom.rangeRestrict_surjective
      (aeval w : MvPolynomial (Fin i) (IntermediateField.adjoin F (Set.range gy)) →ₐ[_]
        FractionRing (MvPolynomial (Option K) Φ)))
    simpa using this
  have : FaithfulSMul F (IntermediateField.adjoin F (Set.range gy)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul (IntermediateField.adjoin F (Set.range gy)) T :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have hT : Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) +
      Algebra.trdeg (IntermediateField.adjoin F (Set.range gy)) T = Algebra.trdeg F T :=
    trdeg_add_eq F (IntermediateField.adjoin F (Set.range gy)) (A := T)

  let gz : (Σ o, bundleIdx ι M o) → FractionRing (MvPolynomial (Option K) Φ) := fun p =>
    algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))
      (C (projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s p) *
        X p.1)
  have hφ : ∀ l m', ((LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (Pi.basisFun Ω (Fin i) m') : Ω) =
      G l m' := by
    intro l m'
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hΦ : ∀ l, (∑ m', s m' * algebraMap Ω Φ (G l m')) =
      ∑ m, algebraMap Ω Φ (g l m) * algebraMap Ω Φ p0 * ∑ m', algebraMap Ω Φ (H⁻¹ m m') * s m' := by
    intro l
    have hG : ∀ m', G l m' = ∑ m, (g l m * p0) * H⁻¹ m m' := by
      intro m'
      have h := congrFun (congrFun (Matrix.mul_nonsing_inv_cancel_right H (Matrix.of G) hH) l) m'
      rw [Matrix.mul_apply] at h
      calc G l m' = Matrix.of G l m' := rfl
        _ = _ := h.symm
        _ = _ := Finset.sum_congr rfl fun m _ => by rw [hGm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [hG, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
  have hnone : ∀ l : Fin M, gz ⟨none, l⟩ = ∑ m, κ (g l m) * w m := by
    intro l
    have e1 : projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s
        (⟨none, l⟩ : Σ o, bundleIdx ι M o) = ∑ m', s m' * algebraMap Ω Φ (G l m') := by
      simp only [projCoord, hφ]
    have e2 : gz ⟨none, l⟩ = κΦ (∑ m', s m' * algebraMap Ω Φ (G l m')) * Xo none := by
      simp only [gz, e1, map_mul]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2, hΦ l, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [w, κ, RingHom.comp_apply, map_mul]
    ring
  have hsome : ∀ k (j : ι k), gz ⟨some k, j⟩ = gy ⟨k, j⟩ := by
    intro k j
    simp only [gz, gy, projCoord, map_mul]
    rfl
  have hgzT : ∀ p, gz p ∈ T := by
    rintro ⟨_ | k, j⟩
    · rw [hnone j]
      refine ⟨∑ m, C ⟨κ (g j m), hgL j m⟩ * X m, ?_⟩
      set_option synthInstance.maxHeartbeats 200000 in
        simp
    · rw [hsome k j]
      exact ⟨C ⟨gy ⟨k, j⟩, IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩⟩, by simp⟩

  have hz : ∀ f, (aeval gz : MRing (bundleIdx ι M) F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) f =
      algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))
        (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
          (fun p => C (projCoord y (Pi.basisFun Ω (Fin i))
            (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s p) * X p.1) f) := by
    intro f
    have e := MvPolynomial.ringHom_ext
      (f := ((aeval gz : MRing (bundleIdx ι M) F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) :
        MRing (bundleIdx ι M) F →+* FractionRing (MvPolynomial (Option K) Φ)))
      (g := (algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))).comp
        (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
          (fun p => C (projCoord y (Pi.basisFun Ω (Fin i))
            (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s p) * X p.1)))
      (fun r => by simp [RingHom.algebraMap_toAlgebra, κ, κΦ])
      (fun p => by simp [gz])
    exact congrArg (fun φ => φ f) e
  let φT : MRing (bundleIdx ι M) F →ₐ[F] T := aeval fun p => ⟨gz p, hgzT p⟩
  have hφT : ∀ f, (φT f : FractionRing (MvPolynomial (Option K) Φ)) = aeval gz f := by
    intro f
    have e := MvPolynomial.ringHom_ext
      (f := (T.val : T →+* FractionRing (MvPolynomial (Option K) Φ)).comp
        (φT : MRing (bundleIdx ι M) F →+* T))
      (g := ((aeval gz : MRing (bundleIdx ι M) F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) :
        MRing (bundleIdx ι M) F →+* FractionRing (MvPolynomial (Option K) Φ)))
      (fun r => by simp [φT])
      (fun p => by simp [φT])
    exact congrArg (fun φ => φ f) e
  have hmem : ∀ f, φT f = 0 ↔ f ∈ projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s := by
    intro f
    rw [projIdeal, RingHom.mem_ker, ← Subtype.val_inj, hφT, hz, ZeroMemClass.coe_zero,
      map_eq_zero_iff _ hinj]
  have hAz : Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ≤ Algebra.trdeg F T := by
    refine trdeg_le_of_injective (Ideal.Quotient.liftₐ _ φT fun f hf => (hmem f).2 hf) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hmem f).1 hx)
  calc _ ≤ Algebra.trdeg F T := hAz
    _ = Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) +
        Algebra.trdeg (IntermediateField.adjoin F (Set.range gy)) T := hT.symm
    _ ≤ Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) + i := by gcongr
    _ = Algebra.trdeg F (Algebra.adjoin F (Set.range gy)) + i := by rw [hSyL]
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointFlagModel
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart pullDeg liftVar ptIdx ptCoord chartMon
  IsGradedFrame IsUnitOn FlagPair IsPull fnField IsVertDiv mcIdeal)

namespace JoinPointFlagModel

section Charts

variable {Ω : Type*} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def extChart (t : ∀ k, ι k) : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k
  | .inl k => t k
  | .inr _ => (0 : Fin 1)

theorem mseg_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) :
    mseg (joinCoord y (ptCoord (Ω := Ω))) s = mseg y (restrictChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  simp [joinCoord, ptCoord, restrictChart]

theorem chartMon_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) (a : K → ℤ) :
    chartMon (joinCoord y (ptCoord (Ω := Ω))) s (pullDeg a) = chartMon y (restrictChart s) a := by
  simp only [chartMon, Fintype.prod_sum_type]
  simp [joinCoord, ptCoord, restrictChart, pullDeg]

variable (O : Type*) [CommRing O] [Algebra O Ω]

theorem chartRing_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) :
    chartRing O (mseg (joinCoord y (ptCoord (Ω := Ω)))) s = chartRing O (mseg y) (restrictChart s) := by
  unfold chartRing
  congr 1
  ext a
  simp only [Set.mem_range, mseg_join]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨restrictChart t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨extChart t, rfl⟩

theorem mem_chartRing_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) (a : Ω) :
    a ∈ chartRing O (mseg (joinCoord y (ptCoord (Ω := Ω)))) s ↔
      a ∈ chartRing O (mseg y) (restrictChart s) := by
  rw [chartRing_join]

end Charts

section Bundles

variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def pullBundle (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E) :
    ChartBundle O (mseg (joinCoord y (ptCoord (Ω := Ω)))) N E where
  lat s := B.lat (restrictChart s)
  stable s a ha e he := B.stable _ a ((mem_chartRing_join O y s a).mp ha) e he
  frame s hs := by
    rw [chartRing_join]
    exact B.frame _ (by rwa [mseg_join] at hs)
  overlap s t hs ht e he := by
    rw [mseg_join, mseg_join]
    rw [mseg_join] at hs ht
    exact B.overlap _ _ hs ht e he

theorem pullBundle_lat (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E)
    (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) : (pullBundle O y B).lat s = B.lat (restrictChart s) :=
  rfl

theorem isPull_pullBundle (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E) :
    IsPull O y (ptCoord (Ω := Ω)) B (pullBundle O y B) := by
  intro s _
  rw [pullBundle_lat]
  apply le_antisymm
  · intro v hv
    exact AddSubgroup.subset_closure ⟨1, one_mem _, v, hv, (one_smul _ _).symm⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact B.stable _ a ((mem_chartRing_join O y s a).mp ha) e he

theorem isGradedFrame_pull (y : (Σ k, ι k) → Ω) {B : ChartBundle O (mseg y) N E}
    {Vs : Fin (N + 1) → Submodule Ω E} {m : Fin N → K → ℤ} {gen : Fin N → E}
    (h : IsGradedFrame O y B Vs m gen) :
    IsGradedFrame O (joinCoord y (ptCoord (Ω := Ω))) (pullBundle O y B) Vs
      (fun i => pullDeg (m i)) gen := by
  intro s hs
  rw [mseg_join] at hs
  obtain ⟨k, f, c, hf, hc, hsum, hl⟩ := h _ hs
  refine ⟨k, f, c, fun l => (mem_chartRing_join O y s _).mpr (hf l),
    fun l => (mem_chartRing_join O y s _).mpr (hc l), hsum, fun l => ?_⟩
  obtain ⟨b, hli, hspan, hiff, hw⟩ := hl l
  refine ⟨b, hli, hspan, fun e => ?_, fun i => ?_⟩
  · rw [pullBundle_lat]
    simp only [mem_chartRing_join]
    exact hiff e
  · obtain ⟨w, ⟨hw0, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩, hmem⟩ := hw i
    refine ⟨w, ⟨hw0, ⟨n₁, (mem_chartRing_join O y s _).mpr hn₁⟩,
      ⟨n₂, (mem_chartRing_join O y s _).mpr hn₂⟩⟩, ?_⟩
    rw [chartMon_join]
    exact hmem

end Bundles

section Forms

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_join (y : (Σ k, ι k) → Ω) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) :
    aeval (joinCoord y (ptCoord (Ω := Ω))) (rename (liftVar ptIdx) f) = aeval y f := by
  rw [aeval_rename]
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := Unit) a - pullDeg (K' := Unit) b = pullDeg (K' := Unit) (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end Forms

section Pairs

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω]
  [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def pullFlagPair (y : (Σ k, ι k) → Ω) {B B' : ChartBundle O (mseg y) N E} (F : FlagPair O y B B')
    (hvert : ∀ i, IsVertDiv O (mcIdeal O (joinCoord y (ptCoord (Ω := Ω))))
      (pullDeg (K' := Unit) (F.deg i - F.deg' i)) (rename (liftVar ptIdx) (F.f i))
      (rename (liftVar ptIdx) (F.g i))) :
    FlagPair O (joinCoord y (ptCoord (Ω := Ω))) (pullBundle O y B) (pullBundle O y B') where
  Vs := F.Vs
  mono := F.mono
  dim := F.dim
  top := F.top
  deg i := pullDeg (F.deg i)
  gen := F.gen
  gen_mem := F.gen_mem
  frame := isGradedFrame_pull O y F.frame
  deg' i := pullDeg (F.deg' i)
  gen' := F.gen'
  gen'_mem := F.gen'_mem
  frame' := isGradedFrame_pull O y F.frame'
  f i := rename (liftVar ptIdx) (F.f i)
  g i := rename (liftVar ptIdx) (F.g i)
  rel i := by
    simp only [aeval_join]
    exact F.rel i
  vert i := by
    simp only [pullDeg_sub]
    exact hvert i

theorem fnField_join (y : (Σ k, ι k) → Ω) :
    fnField O (joinCoord y (ptCoord (Ω := Ω))) = fnField O y := by
  unfold fnField
  apply le_antisymm
  · rw [Subfield.closure_le]
    rintro a (ha | ⟨⟨k | u, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ha)
    · exact Subfield.subset_closure (Or.inr ⟨⟨k, i, j⟩, rfl⟩)
    · have h1 : joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, i⟩ /
          joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, j⟩ = 1 := by
        simp [joinCoord, ptCoord]
      simp only at h1 ⊢
      rw [h1]
      exact one_mem _
  · apply Subfield.closure_mono
    rintro a (ha | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨⟨Sum.inl k, i, j⟩, rfl⟩

end Pairs

end JoinPointFlagModel


open JoinPointFlagModel in
theorem JoinPointFlagModel.proof (hIff : FlagPairCharacterisation.Statement.{0, 0, 0})
    (hModel : JoinPointModel.Statement) (hVert : JoinPointVerticalDivisor.Statement) :
    JoinPointFlagModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hW N E _ _ B B' _ w w' x x' f g hF
  obtain ⟨F, -, -, hdeg, hdeg', hf, hg⟩ :=
    ((hIff O Ω K ι y N E B B' ϖ hϖ hW.multiProj).1 w w' x x' f g).1 hF
  refine ⟨pullBundle O y B, pullBundle O y B',
    pullFlagPair O y F fun i => hVert O Ω K ι y _ _ _ (F.vert i),
    hModel O Ω K ι y d hW, fnField_join O y, isPull_pullBundle O y B, isPull_pullBundle O y B',
    ?_, ?_, ?_, ?_⟩
  · show (fun i => pullDeg (F.deg i)) = _
    rw [hdeg]
  · show (fun i => pullDeg (F.deg' i)) = _
    rw [hdeg']
  · show (fun i => rename (liftVar ptIdx) (F.f i)) = _
    rw [hf]
  · show (fun i => rename (liftVar ptIdx) (F.g i)) = _
    rw [hg]

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleLineBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundleLineBaseProof

theorem intNum_eq_intNumL {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F P bs = intNumL F P (List.ofFn bs) := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem pullDeg_some {K : Type*} (c : K → ℤ) :
    FieldNumbers.pullDeg (Function.Embedding.some : K ↪ Option K) c = liftDeg c := by
  funext o
  cases o with
  | none =>
    simp only [FieldNumbers.pullDeg, liftDeg, Option.elim]
    rw [Function.extend_apply']
    · rfl
    · rintro ⟨k, hk⟩
      exact Option.some_ne_none k hk
  | some k =>
    simp only [FieldNumbers.pullDeg, liftDeg, Option.elim]
    exact (Option.some_injective K).extend_apply c 0 k

theorem relDim_of_krull {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type)
    [Field F] (I : Ideal (MRing ι F)) (e : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim I = ((e : ℕ) : WithBot (WithTop ℤ)) := by
  exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff I e).2 h

theorem contractPrime_projIdeal {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] {N M : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (F : Type)
    [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K) (projIdeal F y w φ t) =
      pointIdeal (ι := fun k => bundleIdx ι M ((Function.Embedding.some : K ↪ Option K) k)) F y := by
  let ψ : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename (Option.some : K → Option K)).toRingHom.comp (MvPolynomial.map (algebraMap Ω Φ))
  have hψ : Function.Injective ψ :=
    (rename_injective _ (Option.some_injective K)).comp
      (MvPolynomial.map_injective _ (algebraMap Ω Φ).injective)
  unfold FieldNumbers.contractPrime projIdeal pointIdeal
  have hcomp : (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
      (fun p => C (projCoord y w φ t p) * X p.1)).comp
      (rename (FieldNumbers.blockIncl (Function.Embedding.some : K ↪ Option K)
        (bundleIdx ι M))).toRingHom = ψ.comp (pointConeMap (ι := fun k => bundleIdx ι M ((Function.Embedding.some : K ↪ Option K) k))
        F y).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, pointConeMap, MvPolynomial.algebraMap_eq]
    · rintro ⟨k, i⟩
      simp [ψ, pointConeMap, FieldNumbers.blockIncl, projCoord]
      rfl
  exact (RingHom.comap_ker _ _).trans
    ((congrArg RingHom.ker hcomp).trans (RingHom.ker_comp_of_injective _ hψ))

theorem replace_zeta {K : Type} [Fintype K] [DecidableEq K] {ι' : Option K → Type}
    [∀ o, Fintype (ι' o)] (F : Type) [Field F] (P : Ideal (MRing ι' F)) (hP : IsMultiProjPrime P)
    (e : ℕ) (hd : FieldNumbers.relDim P = ((e : ℕ) : WithBot (WithTop ℤ))) (c : K → ℤ)
    (bf bg : Option K → ℕ) (f g : MRing ι' F) (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg)
    (hfP : f ∉ P) (hgP : g ∉ P) (hfg : (fun o => (bf o : ℤ) - bg o) = zetaDeg - liftDeg c)
    (hdiv : ratDiv P f g = 0) :
    ∀ (n : ℕ) (Y : List (K → ℤ)), n + Y.length = e →
      intNumL F P (List.replicate n zetaDeg ++ Y.map liftDeg) =
        intNumL F P ((List.replicate n c ++ Y).map liftDeg) := by
  intro n
  induction n with
  | zero => intro Y _; simp
  | succ m ih =>
    intro Y hY
    set l := List.replicate m (zetaDeg : Option K → ℤ) ++ Y.map liftDeg with hl
    have hlen : l.length + 1 = e := by simp [hl]; omega
    have hdl : FieldNumbers.relDim P = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ)) := by
      rw [hlen]; exact hd
    have hsplit : (zetaDeg : Option K → ℤ) = liftDeg c + (zetaDeg - liftDeg c) := by abel
    rw [List.replicate_succ, List.cons_append, ← hl, hsplit,
      NumericalSegreProof.intNumL_cons_add FieldNumbers.IntNumAdd.full F P hP l hdl]
    have hzero : intNumL F P ((zetaDeg - liftDeg c) :: l) = 0 := by
      rw [NumericalSegreProof.intNumL_perm F P (List.perm_append_singleton _ _).symm]
      have hcut := FieldNumbers.CutRational.full F (Option K) ι' P hP l.length hdl bf bg f g hf hg
        hfP hgP l.get
      rw [hfg, hdiv, intNum_eq_intNumL, List.ofFn_succ', List.concat_eq_append] at hcut
      simp only [Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_get] at hcut
      rw [hcut]
      simp [cycEval]
    rw [hzero, add_zero]
    have hperm : (liftDeg c :: l).Perm
        (List.replicate m zetaDeg ++ (c :: Y).map liftDeg) := by
      rw [hl, List.map_cons]
      exact List.perm_middle.symm
    rw [NumericalSegreProof.intNumL_perm F P hperm, ih (c :: Y) (by simp; omega)]
    congr 1
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]

end FlagBundleLineBaseProof


open FlagBundleLineBaseProof in
theorem FlagBundleLineBase.proof (hdim : FlagBundleDim.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hpf : FieldNumbers.ProjectionFormulaDegree.Statement.{0}) :
    FlagBundleLineBase.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdimV N E _ _ B w b hflag M a φ hφ Φ _ _ t ht h0 n Y hnY
  obtain ⟨hP, hPd⟩ := hdim F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht 1 le_rfl h0
  rw [show e + 1 - 1 = e by omega] at hPd
  obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hfg, hdiv⟩ :=
    hsec F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht h0
  rw [replace_zeta F _ hP e hPd (a - b ⟨0, h0⟩) bf bg f g hf hg hfP hgP hfg hdiv n Y hnY]
  set L := List.replicate n (a - b ⟨0, h0⟩) ++ Y with hL
  have hLlen : L.length = e := by simp [hL]; omega
  have hcon := contractPrime_projIdeal (K := K) F y w φ (truncCoord t 1)
  have hcd : FieldNumbers.relDim (FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K)
      (projIdeal F y w φ (truncCoord t 1))) = ((L.length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hLlen]
    exact (congrArg FieldNumbers.relDim hcon).trans (relDim_of_krull F (pointIdeal F y) e hdimV)
  have hPd' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t 1)) =
      ((L.length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hLlen]; exact hPd
  have h := (hpf F K (Option K) Function.Embedding.some (bundleIdx ι M) _ hP L.length hPd' hcd
    L.get).2
  have h2 : intNum F (FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K)
      (projIdeal F y w φ (truncCoord t 1))) L.get = intNum F (pointIdeal F y) L.get :=
    congrArg (fun I => intNum F I L.get) hcon
  rw [hdeg F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht h0, Nat.cast_one, one_mul,
    h2] at h
  simp only [pullDeg_some] at h
  rw [intNum_eq_intNumL, intNum_eq_intNumL, List.ofFn_get] at h
  have hmap : List.ofFn (fun i => liftDeg (L.get i)) = L.map liftDeg := by
    apply List.ext_get <;> simp
  rw [hmap] at h
  exact h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
