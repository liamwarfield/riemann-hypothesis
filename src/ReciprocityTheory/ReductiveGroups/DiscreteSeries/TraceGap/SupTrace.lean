module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TotalDegreeBindLeOfLinear
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.LayerLeGeneratedTensorFock
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TraceIntegralRestrict
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

section Int

variable {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]

theorem integrable_of_cont {F : Type*} [NormedAddCommGroup F] [SecondCountableTopologyEither Kg F]
    {f : Kg → F} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SecondCountableTopologyEither Kg H]

theorem trace_integral_restrict (L : Submodule ℂ H) [FiniteDimensional ℂ L] {c : Kg → ℂ} (hc : Continuous c)
    (A : Kg → (H →L[ℂ] H)) (hA : ∀ v, Continuous fun k => A k v) (hAL : ∀ k, ∀ x ∈ L, A k x ∈ L)
    (B : H →L[ℂ] H) (hB : ∀ w, B w = ∫ k, c k • A k w ∂μ) (hBL : ∀ x ∈ L, B x ∈ L) :
    LinearMap.trace ℂ L ((B : H →ₗ[ℂ] H).restrict hBL) =
      ∫ k, c k * LinearMap.trace ℂ L ((A k : H →ₗ[ℂ] H).restrict (hAL k)) ∂μ := by
  let b := stdOrthonormalBasis ℂ L
  have hint : ∀ i, Integrable (fun k => c k • A k ((b i : L) : H)) μ :=
    fun i => integrable_of_cont (hc.smul (hA _))
  have h1 : ∀ i, inner ℂ (b i) (((B : H →ₗ[ℂ] H).restrict hBL) (b i)) =
      ∫ k, c k * inner ℂ ((b i : L) : H) (A k ((b i : L) : H)) ∂μ := by
    intro i
    rw [Submodule.coe_inner, LinearMap.coe_restrict_apply]
    change inner ℂ ((b i : L) : H) (B ((b i : L) : H)) = _
    rw [hB, ← integral_inner (hint i)]
    simp only [inner_smul_right]
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp only [h1]
  rw [← integral_finsetSum _ fun i _ => integrable_of_cont (μ := μ)
    (f := fun k => c k * inner ℂ ((b i : L) : H) (A k ((b i : L) : H))) (hc.mul (continuous_const.inner (hA _)))]
  congr 1
  funext k
  rw [LinearMap.trace_eq_sum_inner _ b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_inner, LinearMap.coe_restrict_apply]
  rfl

end Int

section Str

variable {n : ℕ} {ε : Fin n → Bool}
  {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem int_str_eq (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {Y Y₀ : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ Y] (hle : Y₀ ≤ Y)
    (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y)
    (hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y₀, wK hD hk y ∈ Y₀)
    (hYG : ∀ y ∈ Y, gradT y ∈ Y) (hY0G : ∀ y ∈ Y₀, gradT y ∈ Y₀)
    {φ : Kg → Matrix (Fin n) (Fin n) ℂ} (hφc : Continuous φ) (hφK : ∀ g, φ g ∈ Kset ε)
    {c : Kg → ℂ} (hc : Continuous c)
    (hrange : ∀ y : TSub Y, tsubVal Y ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) ∈ Y₀) :
    ∫ k, c k * LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (hφK k)).restrict
        (fun y hy => hYG _ (hSK _ (hφK k) y hy))) ∂μ =
      ∫ k, c k * LinearMap.trace ℂ Y₀ ((gradT ∘ₗ wK hD (hφK k)).restrict
        (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) ∂μ := by
  classical
  set Yt := TSub Y
  let W : Kg → (Yt →L[ℂ] Yt) := fun k => tOp hD hSK (φ k)
  have hWc : Continuous W := by
    rw [continuous_clm_apply]
    intro y
    exact ((tOp_isURepOn hD hSK hσ).2.2 y).comp_continuous hφc hφK
  let Γt : Yt →L[ℂ] Yt := LinearMap.toContinuousLinearMap
    ((gradT.restrict hYG : Y →ₗ[ℂ] Y) : Yt →ₗ[ℂ] Yt)
  let Y0t : Submodule ℂ Yt := Y₀.comap (tsubVal Y)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Y0t
  let π : Yt →ₗ[ℂ] Yt := Y0t.subtype ∘ₗ Y0t.linearProjOfIsCompl C hC
  have hπ : ∀ z ∈ Y0t, π z = z := fun z hz => by
    show ((Y0t.linearProjOfIsCompl C hC z : Y0t) : Yt) = z
    have := Submodule.linearProjOfIsCompl_apply_left hC ⟨z, hz⟩
    exact congrArg Subtype.val this
  have hπr : ∀ z, π z ∈ Y0t := fun z => (Y0t.linearProjOfIsCompl C hC z).2
  let ℓl : (Yt →L[ℂ] Yt) →ₗ[ℂ] ℂ :=
    { toFun := fun A => LinearMap.trace ℂ Yt ((LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (A : Yt →ₗ[ℂ] Yt))
      map_add' := fun A A' => by simp [LinearMap.comp_add]
      map_smul' := fun a A => by simp [LinearMap.comp_smul] }
  let ℓ := LinearMap.toContinuousLinearMap ℓl
  have hint : Integrable (fun k => c k • W k) μ := integrable_of_cont (hc.smul hWc)
  set Bt := ∫ k, c k • W k ∂μ
  have hB0 : ℓ Bt = 0 := by
    show LinearMap.trace ℂ Yt ((LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (Bt : Yt →ₗ[ℂ] Yt)) = 0
    have : (LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (Bt : Yt →ₗ[ℂ] Yt) = 0 := by
      apply LinearMap.ext
      intro y
      have hy : Γt (Bt y) ∈ Y0t := hY0G _ (hrange y)
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
      rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, hπ _ hy, sub_self]
    rw [this, map_zero]
  have hcomm : ℓ Bt = ∫ k, c k * ℓ (W k) ∂μ := by
    rw [← ContinuousLinearMap.integral_comp_comm ℓ hint]
    simp only [map_smul, smul_eq_mul]

  have hWk : ∀ k, ((W k : Yt →L[ℂ] Yt) : Yt →ₗ[ℂ] Yt) =
      (((wK hD (hφK k)).restrict (hSK _ (hφK k)) : Y →ₗ[ℂ] Y) : Yt →ₗ[ℂ] Yt) := by
    intro k
    simp only [W, tOp, dif_pos (hφK k)]
    rfl
  have hY : ∀ k, LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (hφK k)).restrict
      (fun y hy => hYG _ (hSK _ (hφK k) y hy))) =
      LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    intro k
    rw [hWk]
    rfl
  have hY0 : ∀ k, LinearMap.trace ℂ Y₀ ((gradT ∘ₗ wK hD (hφK k)).restrict
      (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) =
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    intro k
    have hr : LinearMap.range (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) ≤ Y0t := by
      rintro _ ⟨y, rfl⟩
      exact hπr _
    rw [trace_eq_trace_restrict_of_range_le _ _ hr]
    have hmem : ∀ z : Y0t, tsubVal Y (z : Yt) ∈ Y₀ := fun z => z.2
    let f : Y0t →ₗ[ℂ] Y₀ :=
      { toFun := fun z => ⟨tsubVal Y (z : Yt), hmem z⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        have h' : ((f x : Y₀) : TensorProduct ℂ D (Fock n)) = ((f y : Y₀) : TensorProduct ℂ D (Fock n)) := by
          rw [hxy]
        exact Subtype.ext (tsubVal_injective h')
      · intro y
        exact ⟨⟨(show Yt from ⟨y, hle y.2⟩), y.2⟩, rfl⟩
    let e := LinearEquiv.ofBijective f hf
    rw [← LinearMap.trace_conj' _ e]
    congr 1
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply_apply]
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    have hx : (Γt : Yt →ₗ[ℂ] Yt) ((W k : Yt →ₗ[ℂ] Yt) (x : Yt)) ∈ Y0t := by
      rw [hWk]
      exact hY0G _ (hY0K _ (hφK k) _ x.2)
    show _ = tsubVal Y (π ((Γt : Yt →ₗ[ℂ] Yt) ((W k : Yt →ₗ[ℂ] Yt) (x : Yt))))
    rw [hπ _ hx, hWk]
    rfl
  have hℓ : ∀ k, ℓ (W k) = LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) -
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    intro k
    show LinearMap.trace ℂ Yt ((LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) = _
    rw [LinearMap.sub_comp, map_sub, LinearMap.id_comp]
  have htc : Continuous fun k => LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    let m : (Yt →L[ℂ] Yt) →ₗ[ℂ] ℂ :=
      { toFun := fun A => LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (A : Yt →ₗ[ℂ] Yt))
        map_add' := fun A A' => by simp [LinearMap.comp_add]
        map_smul' := fun a A => by simp [LinearMap.comp_smul] }
    exact (LinearMap.continuous_of_finiteDimensional m).comp hWc
  have hℓc : Continuous fun k => ℓ (W k) := ℓ.continuous.comp hWc
  have hdiff : ∫ k, c k * (LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) -
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) ∂μ = 0 := by
    rw [← hB0, hcomm]
    simp only [hℓ]
  simp only [hY, hY0]
  have hi1 : Integrable (fun k => c k * LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) μ :=
    integrable_of_cont (hc.mul htc)
  have hi2 : Integrable (fun k => c k *
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) μ := by
    refine integrable_of_cont (hc.mul ?_)
    have : (fun k => LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) =
        fun k => LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) - ℓ (W k) := by
      funext k
      rw [hℓ]
      ring
    rw [this]
    exact htc.sub hℓc
  rw [← sub_eq_zero, ← integral_sub hi1 hi2]
  simpa only [mul_sub] using hdiff

end Str

section Range

variable {n : ℕ} {ε : Fin n → Bool}
  {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SecondCountableTopologyEither Kg H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem btot_range (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {Y : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ Y]
    (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y)
    {L : Submodule ℂ D} {φ : Kg → Matrix (Fin n) (Fin n) ℂ} (hφc : Continuous φ) (hφK : ∀ g, φ g ∈ Kset ε)
    {c : Kg → ℂ} (hc : Continuous c)
    (hL : ∀ (s s' : Finset (Fin (n * n))) (u : H),
      ∫ k, (c k * ffMat ε (φ k) s s') • σ (φ k) u ∂μ ∈ L.map D.subtype)
    (hYP : Y ≤ physicalSubspace ε) (y : TSub Y) :
    tsubVal Y ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) ∈ tensFock (n := n) L ⊓ physicalSubspace ε := by
  refine ⟨?_, hYP (tsubVal_mem _)⟩
  apply mem_tensorFock_of_coeffs
  intro s
  have hW : Continuous fun k => tOp hD hSK (φ k) := by
    rw [continuous_clm_apply]
    intro v
    exact ((tOp_isURepOn hD hSK hσ).2.2 v).comp_continuous hφc hφK
  have hint : Integrable (fun k => c k • tOp hD hSK (φ k)) μ := integrable_of_cont (hc.smul hW)
  let Ψ : TSub Y →L[ℂ] H := LinearMap.toContinuousLinearMap
    (D.subtype ∘ₗ tcoef ((fockBasis n).coord s) ∘ₗ tsubVal Y)
  have hΨ : ∀ z, Ψ z = ((tcoef ((fockBasis n).coord s) (tsubVal Y z) : D) : H) := fun z => rfl
  have h1 : Ψ ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) = ∫ k, c k • Ψ (tOp hD hSK (φ k) y) ∂μ := by
    rw [ContinuousLinearMap.integral_apply hint, ← ContinuousLinearMap.integral_comp_comm Ψ
      (hint.apply_continuousLinearMap y)]
    simp only [ContinuousLinearMap.smul_apply, map_smul]
  have h2 : ∀ k, c k • Ψ (tOp hD hSK (φ k) y) =
      ∑ s', (c k * ffMat ε (φ k) s s') • σ (φ k) ((tcoef ((fockBasis n).coord s') (tsubVal Y y) : D) : H) := by
    intro k
    rw [hΨ, tOp_apply hD hSK (hφK k), tco_wK, Submodule.coe_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [coord_ff_basis, Submodule.coe_smul, smul_smul]
    rfl
  have hmem : Ψ ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) ∈ L.map D.subtype := by
    rw [h1]
    simp_rw [h2]
    rw [integral_finsetSum]
    · exact Submodule.sum_mem _ fun s' _ => hL s s' _
    · intro s' _
      exact integrable_of_cont ((hc.mul ((ffMat_continuous s s').comp hφc)).smul
        (((hσ.2.2 _).comp_continuous hφc fun g => kset_mem_UJset (hφK g))))
  obtain ⟨x, hx, hxe⟩ := hmem
  have : tcoef ((fockBasis n).coord s) (tsubVal Y ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y)) = x :=
    Subtype.ext (hxe.trans (hΨ _)).symm
  rw [this]
  exact hx

end Range

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.InvoluteExteriorPower
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem involute_exteriorPower {p : ℕ} {w : Fock n} (hw : w ∈ ⋀[ℂ]^p (Fin n × Fin n → ℂ)) :
    CliffordAlgebra.involute w = ((-1 : ℂ) ^ p) • w := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact involute_ιMulti p v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem gradT_range_ext {V : Submodule ℂ N} {p : ℕ} {z : TensorProduct ℂ N (Fock n)}
    (hz : z ∈ LinearMap.range (TensorProduct.map V.subtype (⋀[ℂ]^p (Fin n × Fin n → ℂ)).subtype)) :
    gradT z = ((-1 : ℂ) ^ p) • z := by
  obtain ⟨x, rfl⟩ := hz
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    simp only [TensorProduct.map_tmul, gradT, Submodule.coe_subtype, AlgHom.toLinearMap_apply,
      LinearMap.id_apply]
    rw [involute_exteriorPower w.2, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem gradT_cpcm (i a j b : Fin n) :
    gradT (N := N) * (cpT i a * cmT j b) = cpT i a * cmT j b * gradT := by
  rw [← mul_assoc, gradT_cpT, neg_mul, mul_assoc, gradT_cmT, mul_neg, neg_neg, mul_assoc]

theorem gradT_sgE (a b : Fin n) :
    gradT (N := N) * sgE ε cpT cmT a b = sgE ε cpT cmT a b * gradT := by
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => gradT_cpcm _ _ _ _
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => gradT_cpcm _ _ _ _
  · simp

theorem gradT_diagE (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) (y : TensorProduct ℂ N (Fock n)) :
    gradT (diagE ε (eT E) cpT cmT a b y) = diagE ε (eT E) cpT cmT a b (gradT y) := by
  have h1 := LinearMap.congr_fun (eT_gradT E a b) y
  have h2 := LinearMap.congr_fun (gradT_sgE (ε := ε) (N := N) a b) y
  simp only [mul_apply_eq_comp] at h1 h2
  simp only [diagE, LinearMap.add_apply, map_add (f := _), h1, h2]

theorem gradT_kLowSpan (E : Fin n → Fin n → Module.End ℂ N) {z : TensorProduct ℂ N (Fock n)} {c : ℂ}
    (hz : gradT z = c • z) {y : TensorProduct ℂ N (Fock n)}
    (hy : y ∈ kLowSpan ε (diagE ε (eT E) cpT cmT) z) : gradT y = c • y := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, -, rfl⟩ := hx
    induction l with
    | nil => exact hz
    | cons p l ih =>
      simp only [lowWord]
      rw [gradT_diagE, ih, map_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

def SupTraceStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDS ε lam σ → Formalism.QuantumDeterminants.IsHCParam lam → GapAtLeast ε lam h → thrStar ε < h →
    1 ≤ pOf ε → 1 ≤ qOf ε →
    ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (_ : FiniteDimensional ℂ W)
      (T : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)),
      Nontrivial W ∧ Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T ∧ Formalism.MainNotions.S.IsKTypeOf ε T (gaW ε lam) ⊤ ∧
      ∀ (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) (B : H →L[ℂ] H),
        (∀ w : H, B w = ∫ k, (MvPolynomial.eval (entVar (Formalism.REAL.toMK k)) P * physDet ε (Formalism.REAL.toMK k)) •
          σ (Formalism.REAL.toMK k) w ∂(Formalism.REAL.muK ε)) →
        FiniteDimensional ℂ (LinearMap.range (B : H →ₗ[ℂ] H)) ∧
        LinearMap.trace ℂ (LinearMap.range (B : H →ₗ[ℂ] H))
            ((B : H →ₗ[ℂ] H).restrict (fun x _ => LinearMap.mem_range_self (B : H →ₗ[ℂ] H) x)) =
          (-1 : ℂ) ^ sDeg ε * ∫ k, MvPolynomial.eval (entVar (Formalism.REAL.toMK k)) P *
            LinearMap.trace ℂ W (T (Formalism.REAL.toMK k) : W →ₗ[ℂ] W) ∂(Formalism.REAL.muK ε)

section Helpers

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem trace_restrict_range (f : M →ₗ[ℂ] M) (L : Submodule ℂ M) [FiniteDimensional ℂ L] (hfL : ∀ x, f x ∈ L) :
    LinearMap.trace ℂ (LinearMap.range f) (f.restrict (fun x _ => LinearMap.mem_range_self f x)) =
      LinearMap.trace ℂ L (f.restrict (fun x _ => hfL x)) := by
  have hle : LinearMap.range f ≤ L := by
    rintro _ ⟨x, rfl⟩
    exact hfL x
  set R' : Submodule ℂ L := (LinearMap.range f).comap L.subtype
  have hr : LinearMap.range (f.restrict (fun x _ => hfL x) : L →ₗ[ℂ] L) ≤ R' := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_range_self f _
  rw [trace_eq_trace_restrict_of_range_le _ _ hr]
  let e : R' ≃ₗ[ℂ] LinearMap.range f := Submodule.comapSubtypeEquivOfLe hle
  rw [← LinearMap.trace_conj' _ e]
  congr 1

end Helpers

section Helpers2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

theorem trace_map_subtype {L : Submodule ℂ D} [FiniteDimensional ℂ L] (g : D →ₗ[ℂ] D) (hg : ∀ x ∈ L, g x ∈ L)
    (f : H →ₗ[ℂ] H) (hf : ∀ x ∈ L.map D.subtype, f x ∈ L.map D.subtype) (hfg : ∀ x : D, f x = g x) :
    LinearMap.trace ℂ (L.map D.subtype) (f.restrict hf) = LinearMap.trace ℂ L (g.restrict hg) := by
  let e : L ≃ₗ[ℂ] L.map D.subtype := L.equivMapOfInjective D.subtype D.injective_subtype
  rw [← LinearMap.trace_conj' (g.restrict hg) e]
  congr 1
  apply LinearMap.ext
  intro y
  rw [LinearEquiv.conj_apply_apply]
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [LinearEquiv.symm_apply_apply]
  show f ((x : D) : H) = ((g (x : D) : D) : H)
  exact hfg x

end Helpers2


theorem supTrace (n : ℕ) : SupTraceStatement n := by
  intro ε lam h H _ _ σ hDS hHC hgap hthr hp hq
  have : CompleteSpace H := hDS.1
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨hanti, hint⟩ := hHC
  have hstd : StdGap ε lam := ⟨hanti, h, hgap, lt_of_le_of_lt (le_max_left _ _) hthr⟩
  obtain ⟨V, hV, hV0, hVK, hc⟩ := arb_datum hDS (casOnSmooth_of_isDS hDS hstd)
  have hD := isDerivedOn_smE hσ
  have htop := data_closGen_eq_top hstd hσ hD hV hc hVK hDS.2.2.2.1 hV0
  obtain ⟨W, i1, i2, i3, T, hWnt, hTU, hTK, hTtr⟩ :=
    kType_clause hσ hD hV hc hVK hint hanti hgap hthr hp hq
  refine ⟨W, i1, i2, i3, T, hWnt, hTU, hTK, fun P B hB => ?_⟩
  obtain ⟨z, -, hzV, hzK, hzdeg, hKK, -⟩ := ker_D_eq_kLowSpan hσ hD hV hc hVK hint hanti hgap hthr hp hq
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (Formalism.REAL.KG ε) := hemb.isInducing.secondCountableTopology
  set φ : Formalism.REAL.KG ε → Matrix (Fin n) (Fin n) ℂ := fun k => Formalism.REAL.toMK k with hφdef
  have hφc : Continuous φ := hemb.continuous
  have hφK : ∀ g, φ g ∈ Kset ε := fun g => g.2
  have hφ1 : φ 1 = 1 := rfl
  have hφm : ∀ a b, φ (a * b) = φ a * φ b := fun a b => rfl
  have hφs : ∀ m ∈ Kset ε, ∃ g, φ g = m := by
    intro m hm
    have : m ∈ Set.range (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) := by
      rw [Formalism.REAL.range_toMK]
      exact hm
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg⟩

  choose Qm hQm using fun s s' => ffMat_poly (ε := ε) s s'
  set Q := ∑ s ∈ Finset.univ.filter (IsPhysSet ε), ((-1 : ℂ) ^ s.card) • Qm s s with hQdef
  have hQ : ∀ m, MvPolynomial.eval (entVar m) Q = physDet ε m := by
    intro m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← strPhys_eq_physDet, strPhys, hQdef, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.smul_eval, hQm]
    rfl
  have hL3 := fun R => range_one_layer hstd hσ hD hV hc htop (Formalism.REAL.muK ε) φ hφc hφ1 hφm hφK hφs R
  obtain ⟨j0, hj0⟩ := hL3 (P * Q)
  choose js hjs using fun (s s' : Finset (Fin (n * n))) => hL3 (P * Qm s s')
  set J := max j0 (Finset.univ.sup fun p : Finset (Fin (n * n)) × Finset (Fin (n * n)) => js p.1 p.2) with hJ
  have hj0J : j0 ≤ J := le_max_left _ _
  have hjsJ : ∀ s s', js s s' ≤ J := fun s s' =>
    le_trans (Finset.le_sup (f := fun p : Finset (Fin (n * n)) × Finset (Fin (n * n)) => js p.1 p.2)
      (Finset.mem_univ (s, s'))) (le_max_right _ _)

  have hE : IsGlRep (smE ε σ) := hD.glRep
  have hLDf : FiniteDimensional ℂ (layer ε (smE ε σ) V J) := finiteDimensional_layer hV.1 J
  have hlayer : ∀ {j : ℕ}, j ≤ J → (layer ε (smE ε σ) V j).map (smD ε σ).subtype ≤
      (layer ε (smE ε σ) V J).map (smD ε σ).subtype := fun hj => Submodule.map_mono (layer_mono hj)
  set LH := (layer ε (smE ε σ) V J).map (smD ε σ).subtype with hLHdef
  have hLHf : FiniteDimensional ℂ LH := Module.Finite.map _ _
  have hent : ∀ R : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ,
      Continuous fun k => MvPolynomial.eval (entVar (φ k)) R := by
    intro R
    refine (MvPolynomial.continuous_eval R).comp (continuous_pi fun p => ?_)
    rcases p with p | p
    · exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hφc))
  have hBL : ∀ w, B w ∈ LH := by
    intro w
    rw [hB]
    have := hlayer hj0J (hj0 w)
    simpa only [map_mul, hQ] using this
  have hrB : LinearMap.range (B : H →ₗ[ℂ] H) ≤ LH := by
    rintro _ ⟨w, rfl⟩
    exact hBL w
  refine ⟨Submodule.finiteDimensional_of_le hrB, ?_⟩
  rw [trace_restrict_range (B : H →ₗ[ℂ] H) LH hBL]
  have hAL : ∀ k, ∀ x ∈ LH, σ (φ k) x ∈ LH := by
    rintro k _ ⟨y, hy, rfl⟩
    exact ⟨sigD hD (hφK k) y, sigD_layer hσ hD hV.2.1 hVK J (hφK k) hy, rfl⟩
  have hAc : ∀ v, Continuous fun k => σ (φ k) v := fun v =>
    (hσ.2.2 v).comp_continuous hφc fun g => kset_mem_UJset (hφK g)
  have hcont : Continuous fun k => MvPolynomial.eval (entVar (φ k)) P * physDet ε (φ k) := by
    have := hent (P * Q)
    simpa only [map_mul, hQ] using this
  rw [trace_integral_restrict (μ := Formalism.REAL.muK ε) LH hcont (fun k => σ (φ k)) hAc hAL B hB
    (fun x _ => hBL x)]

  have hYf : FiniteDimensional ℂ (YY ε (smE ε σ) V J) := YY_fd hV.1 J
  have hY0G : ∀ y ∈ Y0 ε (smE ε σ) V J, gradT y ∈ Y0 ε (smE ε σ) V J := fun y hy =>
    ⟨tensFock_lTensor_stable _ hy.1, (physSub_stable ε (smE ε σ)).2.2.2.2 y hy.2⟩
  have hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y0 ε (smE ε σ) V J,
      wK hD hk y ∈ Y0 ε (smE ε σ) V J := fun k hk y hy => compactAction_mem_layer hσ hD hV.2.1 hVK J hk hy
  have hYK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ YY ε (smE ε σ) V J,
      wK hD hk y ∈ YY ε (smE ε σ) V J := fun k hk y hy => YY_wK hσ hD hV.2.1 hVK J hk hy
  have hle : Y0 ε (smE ε σ) V J ≤ YY ε (smE ε σ) V J := le_sup_left

  have hpt : ∀ k, MvPolynomial.eval (entVar (φ k)) P * physDet ε (φ k) *
      LinearMap.trace ℂ LH (((σ (φ k) : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict (hAL k)) =
      MvPolynomial.eval (entVar (φ k)) P * LinearMap.trace ℂ (Y0 ε (smE ε σ) V J)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) := by
    intro k
    rw [trace_map_subtype (sigD hD (hφK k)) (fun x hx => sigD_layer hσ hD hV.2.1 hVK J (hφK k) hx) _ _
      (fun x => rfl)]
    have := str_tensFock_physSub hD (hφK k) (fun x hx => sigD_layer hσ hD hV.2.1 hVK J (hφK k) hx)
      (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))
    rw [show LinearMap.trace ℂ (Y0 ε (smE ε σ) V J)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) = _ from this]
    ring
  simp_rw [hpt]

  have hcP := hent P
  have hrange := fun y => btot_range (μ := Formalism.REAL.muK ε) hσ hD hYK (L := layer ε (smE ε σ) V J) hφc hφK hcP
    (fun s s' u => by
      have h1 := hlayer (hjsJ s s') (hjs s s' u)
      have h2 : ∫ k, (MvPolynomial.eval (entVar (φ k)) P * ffMat ε (φ k) s s') • σ (φ k) u ∂(Formalism.REAL.muK ε) =
          ∫ k, MvPolynomial.eval (entVar (φ k)) (P * Qm s s') • σ (φ k) u ∂(Formalism.REAL.muK ε) := by
        congr 1
        funext k
        rw [map_mul, hQm]
        rfl
      show ∫ k, (MvPolynomial.eval (entVar (φ k)) P * ffMat ε (φ k) s s') • σ (φ k) u ∂(Formalism.REAL.muK ε) ∈ _
      rw [h2]
      exact h1) (YY_le_genSub J |>.trans inf_le_right) y
  rw [← int_str_eq (μ := Formalism.REAL.muK ε) hσ hD hle hYK hY0K (fun y hy => YY_gradT J hy) hY0G hφc hφK hcP hrange]

  have hcg : ∀ v ∈ genSub (smE ε σ) V, casimir (smE ε σ) v = ((casVal lam : ℝ) : ℂ) • v :=
    casimir_scalar_on_generated hE hc
  have hAK : IsKStableSub ε (diagE ε (eT (smE ε σ)) cpT cmT) (tensFock (n := n) V) :=
    fun a b hab y hy => tensorFock_diagAction_stable ε hV.2.1 hab hy
  have hKKY0 : LinearMap.ker (dOp ε (eT (smE ε σ)) cpT + dOp' ε (eT (smE ε σ)) cmT) ⊓
      tensFock (genSub (smE ε σ) V) ⊓ physicalSubspace ε ≤ Y0 ε (smE ε σ) V J := by
    intro y hy
    have hyP : y ∈ physicalSubspace (N := smD ε σ) ε := hy.2
    rw [hKK] at hy
    have hyV : y ∈ tensFock (n := n) V := kLowSpan_le hAK hzV hy
    exact ⟨tensorFock_mono (layer_mono (E := smE ε σ) (V := V) (ε := ε) (Nat.zero_le J)) hyV, hyP⟩
  have hgr : ∀ y ∈ LinearMap.ker (dOp ε (eT (smE ε σ)) cpT + dOp' ε (eT (smE ε σ)) cmT) ⊓
      tensFock (genSub (smE ε σ) V) ⊓ physicalSubspace ε, gradT y = ((-1 : ℂ) ^ sDeg ε) • y := by
    intro y hy
    rw [hKK] at hy
    exact gradT_kLowSpan (smE ε σ) (gradT_range_ext hzdeg) hy
  have hfin : ∀ k, MvPolynomial.eval (entVar (φ k)) P * LinearMap.trace ℂ (YY ε (smE ε σ) V J)
      ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => YY_gradT J (hYK _ (hφK k) y hy))) =
      (-1 : ℂ) ^ sDeg ε * (MvPolynomial.eval (entVar (φ k)) P * LinearMap.trace ℂ W (T (φ k) : W →ₗ[ℂ] W)) := by
    intro k
    rw [str_YY hσ hD hV.2.1 hVK hcg J hKKY0 hgr (hφK k), hTtr (φ k) (hφK k)]
    ring
  simp_rw [hfin]
  rw [integral_const_mul]

end ReciprocityTheory.ChartRestriction.DS.TRGap
