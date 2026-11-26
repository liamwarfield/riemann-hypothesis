module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {c : kˣ}

theorem isSelfDual_iff_vol (h : HasConductor ψ c) (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1 := by
  have := t2Space k
  have hcl : IsClosed (𝒪[k] : Set k) := (isCompact_int k).isClosed
  have hclo : IsClopen (𝒪[k] : Set k) := ⟨hcl, isOpen_int k⟩
  set f : k → ℂ := (𝒪[k] : Set k).indicator 1 with hf
  have hfSB : f ∈ SB k := by
    refine ⟨?_, ?_⟩
    · have hlc := (LocallyConstant.charFn ℂ hclo).isLocallyConstant
      exact hlc
    · exact HasCompactSupport.intro' (isCompact_int k) hcl fun x hx => by simp [f, hx]
  have hf0 : f 0 = 1 := by simp [f]
  have hvol : ν.real (𝒪[k] : Set k) = (ν (𝒪[k] : Set k)).toReal := measureReal_def ν _
  constructor
  · rintro ⟨-, hsd⟩
    have e := (fourier_inversion ν h hfSB).symm.trans (hsd f hfSB)
    rw [hf0, mul_one] at e
    rw [← hvol]
    exact_mod_cast e
  · intro hC
    refine ⟨inferInstance, fun g hg => ?_⟩
    rw [fourier_inversion ν h hg, hvol, hC]
    simp

theorem exists_isSelfDual_of_hasConductor (h : HasConductor ψ c) : ∃ ν : Measure k, IsSelfDual ψ ν := by
  obtain ⟨ν₀, hH, h1⟩ := exists_isUnitVol k
  have hn : 0 < nabs k c := nabs_pos k c
  set a : ℝ≥0 := ⟨(Real.sqrt (nabs k c))⁻¹, by positivity⟩ with ha
  have ha0 : a ≠ 0 := by
    intro h0
    have : (Real.sqrt (nabs k c))⁻¹ = 0 := congrArg Subtype.val h0
    have hs : 0 < Real.sqrt (nabs k c) := Real.sqrt_pos.2 hn
    exact (inv_pos.2 hs).ne' this
  have : (a • ν₀).IsAddHaarMeasure := .nnreal_smul ν₀ ha0
  refine ⟨a • ν₀, (isSelfDual_iff_vol h _).2 ?_⟩
  have hval : ((a • ν₀) (𝒪[k] : Set k)).toReal = (Real.sqrt (nabs k c))⁻¹ := by
    rw [smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal]
    rfl
  rw [hval, inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']

theorem isUnitVol_iff_isSelfDual (h : HasConductor ψ 1) (ν : Measure k) : IsUnitVol ν ↔ IsSelfDual ψ ν := by
  constructor
  · intro hν
    haveI := hν.1
    exact isSelfDual_of_isUnitVol ν h hν
  · intro hsd
    haveI : ν.IsAddHaarMeasure := hsd.1
    have e := (isSelfDual_iff_vol h ν).1 hsd
    rw [nabs_one, mul_one] at e
    have hnn : 0 ≤ (ν (𝒪[k] : Set k)).toReal := ENNReal.toReal_nonneg
    have e1 : (ν (𝒪[k] : Set k)).toReal = 1 := by nlinarith
    exact ⟨hsd.1, (ENNReal.toReal_eq_one_iff _).1 e1⟩

theorem selfDual_measure : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1), (∃ ν : Measure k, IsSelfDual ψ ν) ∧ (HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν ↔ IsSelfDual ψ ν) ∧ ∀ (c : kˣ) (ν : Measure k), HasConductor ψ c → ν.IsAddHaarMeasure → (IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1) := by
  intro k _ _ _ _ _ _ ψ hψ h1
  refine ⟨?_, fun h ν => isUnitVol_iff_isSelfDual h ν, fun c ν hc hν => ?_⟩
  · obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
    exact exists_isSelfDual_of_hasConductor hc
  · exact isSelfDual_iff_vol hc ν

end GlobalTheory.SplitWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
noncomputable section

open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

theorem phase_eq_eChar (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) :
    phase w x = GlobalTheory.Published.Metaplectic.eChar (⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2) := by
  rw [GlobalTheory.Published.Metaplectic.eChar_apply, phase]
  congr 1
  push_cast
  ring

theorem hasTemperateGrowth_phase' (w : l ⊕ l → ℝ) : Function.HasTemperateGrowth (phase w) := by
  have h1 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ :=
    (innerSL ℝ (qPart w)).hasTemperateGrowth
  have h := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (h1.add (Function.HasTemperateGrowth.const
    (⟪pPart w, qPart w⟫ / 2)))
  have e : phase w = (GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘
      ((fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫) + fun _ => ⟪pPart w, qPart w⟫ / 2) := by
    funext x
    simp [phase_eq_eChar]
  rw [e]
  exact h

def rhoSch (w : l ⊕ l → ℝ) : Sch l →L[ℂ] Sch l :=
  SchwartzMap.smulLeftCLM ℂ (phase w) ∘L SchwartzMap.compSubConstCLM ℂ (-pPart w)

theorem coe_rhoSch (w : l ⊕ l → ℝ) (f : Sch l) : ⇑(rhoSch w f) = rhoFun w ⇑f := by
  funext x
  rw [rhoSch, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase' w),
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul, rhoFun]

theorem exists_schwartz_rhoFun : ∀ (l : Type) [Fintype l] (w : l ⊕ l → ℝ) (f : Sch l), ∃ f₁ : Sch l, ⇑f₁ = rhoFun w ⇑f :=
  fun _ _ w f => ⟨rhoSch w f, coe_rhoSch w f⟩

end GlobalTheory.RealWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.SBConv

section Abstract
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem eventually_translate {F : G → ℂ} (hF : F ∈ SB G) :
    ∀ᶠ x in nhds (0 : G), ∀ g, F (g - x) = F g := by
  have hlc : IsLocallyConstant F := hF.1
  have hK : IsCompact (tsupport F) := hF.2
  have hz : ∀ z, z ∉ tsupport F → F z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport F h)
  have step : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - x) = F y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hy := hlc.eventually_eq y
    have h1 : Filter.Tendsto (fun p : G × G => p.2 - p.1) (nhds ((0 : G), y)) (nhds y) := by
      simpa using (continuous_snd.tendsto ((0 : G), y)).sub (continuous_fst.tendsto ((0 : G), y))
    have h2 : Filter.Tendsto (fun p : G × G => p.2) (nhds ((0 : G), y)) (nhds y) :=
      continuous_snd.tendsto _
    filter_upwards [h1.eventually hy, h2.eventually hy] with p hp1 hp2
    exact hp1.trans hp2.symm
  have step' : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - -x) = F y :=
    (continuous_neg.tendsto' (0 : G) 0 neg_zero).eventually step
  filter_upwards [step, step'] with x hx hx' g
  by_cases hg : g ∈ tsupport F
  · exact hx g hg
  · rw [hz g hg]
    by_cases hg' : g - x ∈ tsupport F
    · have h := hx' (g - x) hg'
      rw [sub_neg_eq_add, sub_add_cancel, hz g hg] at h
      exact h.symm
    · exact hz _ hg'

def translate (Ψ : SB G) (y : G) : SB G :=
  ⟨fun x => Ψ.1 (x - y), Ψ.2.1.comp_continuous (continuous_sub_right y),
    Ψ.2.2.comp_homeomorph (Homeomorph.subRight y)⟩

theorem isLocallyConstant_translate (Ψ : SB G) : IsLocallyConstant (translate Ψ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hmap : Filter.Tendsto (fun y' : G => y' - y) (nhds y) (nhds 0) := by
    simpa using (continuous_id.tendsto y).sub_const y
  filter_upwards [hmap.eventually (eventually_translate Ψ.2)] with y' hy'
  apply Subtype.ext
  funext x
  show Ψ.1 (x - y') = Ψ.1 (x - y)
  have h := hy' (x - y)
  rwa [sub_sub_sub_cancel_right] at h

theorem exists_conv [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (Φ Ψ : SB G) :
    ∃ w : SB G, (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂μ) ∧
      ∀ l : SB G →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (translate Ψ y) ∂μ := by
  have hT : IsLocallyConstant (fun y => Φ.1 y • translate Ψ y) :=
    IsLocallyConstant.comp₂ Φ.2.1 (isLocallyConstant_translate Ψ) (fun c f => c • f)
  have hz : ∀ y, y ∉ tsupport Φ.1 → Φ.1 y • translate Ψ y = 0 := by
    intro y hy
    have h0 : Φ.1 y = 0 := by
      by_contra h
      exact hy (subset_tsupport _ h)
    rw [h0, zero_smul]
  obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact G μ (SB G)
    (fun y => Φ.1 y • translate Ψ y) hT (tsupport Φ.1) Φ.2.2.isCompact hz
  refine ⟨w, fun x => ?_, fun l => ?_⟩
  · exact hw ((LinearMap.proj x).comp (SB G).subtype)
  · rw [hw l]
    simp only [map_smul, smul_eq_mul]

end Abstract

theorem exists_convolution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (Φ Ψ : SB (n → k)), ∃ (T : (n → k) → SB (n → k)) (w : SB (n → k)), (∀ y x, (T y).1 x = Ψ.1 (x - y)) ∧ (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ ∀ l : SB (n → k) →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (T y) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n _ _ ν _ Φ Ψ
  have : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  have : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have : ν.Regular := inferInstance
  have : ν.IsNegInvariant := inferInstance
  obtain ⟨w, hw1, hw2⟩ := exists_conv (Measure.pi fun _ : n => ν) Φ Ψ
  refine ⟨translate Ψ, w, fun y x => rfl, hw1, fun x => ?_, hw2⟩
  rw [hw1 x]
  have h := integral_sub_left_eq_self (fun y => Φ.1 (x - y) * Ψ.1 y) (Measure.pi fun _ : n => ν) x
  simp only [sub_sub_cancel] at h
  refine h.trans ?_
  congr 1
  funext y
  exact mul_comm _ _

end GlobalTheory.SBConv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPowerStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_convolution_localFieldPower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (Φ Ψ : SB (n → k)), ∃ (T : (n → k) → SB (n → k)) (w : SB (n → k)), (∀ y x, (T y).1 x = Ψ.1 (x - y)) ∧ (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ ∀ l : SB (n → k) →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (T y) ∂(Measure.pi fun _ => ν) := by
  first | exact @GlobalTheory.SBConv.exists_convolution | exact GlobalTheory.SBConv.exists_convolution | (intros; apply GlobalTheory.SBConv.exists_convolution <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralLinear
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx Topology
open scoped Pointwise

namespace GlobalTheory.RootEx.QuotLinear

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem isClosed_N : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (N k n c p : Set (GL (n ⊕ Fin c) k)) = ⋂ r, ⋂ s, ⋂ (_ : lev p s ≤ lev p r),
      {g : GL (n ⊕ Fin c) k | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
    ext g
    simp only [SetLike.mem_coe, Radical.mem_N_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_eq ?_ continuous_const
  have := Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  fun_prop

theorem continuous_embX : Continuous (embX c : GL n k → GL (n ⊕ Fin c) k) := by
  rw [SplitFlip.isEmbedding_val_GL.continuous_iff]
  change Continuous fun x : GL n k => (fromBlocks x.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  exact Continuous.matrix_fromBlocks Units.continuous_val continuous_const continuous_const continuous_const

theorem exists_compact_prod {K : Set (GL (n ⊕ Fin c) k)} (hK : IsCompact K) :
    ∃ (A : Set (GL n k)) (B : Set (N k n c p)), IsCompact A ∧ IsCompact B ∧
      ∀ (x : GL n k) (u : N k n c p), embX c x * (u : GL (n ⊕ Fin c) k) ∈ K → x ∈ A ∧ u ∈ B := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let φ : GL (n ⊕ Fin c) k → Matrix n n k × (Matrix n n k)ᵐᵒᵖ :=
    fun g => (g.val.toBlocks₁₁, MulOpposite.op (g⁻¹).val.toBlocks₁₁)
  have hb : Continuous fun M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => M.toBlocks₁₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem _ _
  have hφ : Continuous φ :=
    (hb.comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp (hb.comp Units.continuous_coe_inv))
  have hA := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hK.image hφ)
  have hB := (isClosed_N (k := k) (n := n) (c := c) (p := p)).isClosedEmbedding_subtypeVal.isCompact_preimage
    ((hA.image (continuous_embX (c := c))).inv.mul hK)
  refine ⟨_, _, hA, hB, fun x u h => ?_⟩
  have hx : x ∈ (Units.embedProduct (Matrix n n k)) ⁻¹' (φ '' K) := by
    refine ⟨_, h, ?_⟩
    have e : (embX c x * (u : GL (n ⊕ Fin c) k))⁻¹ =
        embX c x⁻¹ * (embX c x * (u : GL (n ⊕ Fin c) k)⁻¹ * (embX c x)⁻¹) := by
      rw [map_inv]; group
    simp only [φ]
    rw [e, Radical.toBlocks₁₁_embX_mul x u.2,
      Radical.toBlocks₁₁_embX_mul x⁻¹ (Radical.conj_mem x (inv_mem u.2))]
    rfl
  refine ⟨hx, ?_⟩
  refine ⟨(embX c x)⁻¹, ?_, _, h, by simp⟩
  rw [Set.mem_inv, inv_inv]
  exact ⟨x, hx, rfl⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem finiteOnCompacts_volN (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsFiniteMeasureOnCompacts (volN ν n c p) := by
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨fun K hK => ?_⟩
  unfold volN
  rw [(Model.coord_embedding (k := k) (n := n) (c := c) p).1.comap_apply]
  refine (hK.image ?_).measure_lt_top
  have := Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  fun_prop

theorem integrable_average (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure]
    {F : GL (n ⊕ Fin c) k → ℂ} (hF : F ∈ SB (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) :
    (∀ x : GL n k, Integrable (fun u : N k n c p => F (embX c x * (u : GL (n ⊕ Fin c) k) * h)) (volN ν n c p)) ∧
    Integrable (fun x : GL n k =>
      ∫ u : N k n c p, F (embX c x * (u : GL (n ⊕ Fin c) k) * h) ∂(volN ν n c p)) μX := by
  haveI := finiteOnCompacts_volN (n := n) (c := c) (p := p) ν
  haveI : LocallyCompactSpace (N k n c p) :=
    (isClosed_N (k := k) (n := n) (c := c) (p := p)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure (volN ν n c p) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (volN ν n c p) := sigmaFinite_of_locallyFinite
  have hK : IsCompact ((fun g => g * h⁻¹) '' tsupport F) := hF.2.isCompact.image (by fun_prop)
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_compact_prod (p := p) hK
  have hz : ∀ (x : GL n k) (u : N k n c p), ¬ (x ∈ A ∧ u ∈ B) →
      F (embX c x * (u : GL (n ⊕ Fin c) k) * h) = 0 := fun x u hn => by
    by_contra h0
    exact hn (hAB x u ⟨_, subset_tsupport _ h0, by simp⟩)
  have hc : Continuous fun z : GL n k × N k n c p => F (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) * h) :=
    hF.1.continuous.comp (((continuous_embX.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul continuous_const)
  refine ⟨fun x => ?_, ?_⟩
  · exact (hc.comp (Continuous.prodMk_right x)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hB fun u hu => hz x u fun h => hu h.2)
  · have hi : Integrable (fun z : GL n k × N k n c p => F (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) * h))
        (μX.prod (volN ν n c p)) :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (hA.prod hB) fun z hz' => hz z.1 z.2 hz')
    exact hi.integral_prod_left

theorem isQuotInt_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f f' : GL (n ⊕ Fin c) k → ℂ) (a z z' : ℂ), IsQuotInt ν μX μG p f z → IsQuotInt ν μX μG p f' z' → IsQuotInt ν μX μG p (fun h => a * f h + f' h) (a * z + z') := by
  intro k _ _ _ _ _ _ n _ _ c p _ _ ν _ μX _ μG _ f f' a z z' ⟨F, hF, h1, h2⟩ ⟨F', hF', h1', h2'⟩
  refine ⟨a • F + F', add_mem (Submodule.smul_mem _ a hF) hF', fun h => ?_, ?_⟩
  · obtain ⟨i1, i2⟩ := integrable_average (p := p) ν μX hF h
    obtain ⟨j1, j2⟩ := integrable_average (p := p) ν μX hF' h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, h1', ← integral_const_mul, ← integral_add (i2.const_mul a) j2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_add ((i1 x).const_mul a) (j1 x), integral_const_mul]
  · have i : Integrable F μG := hF.1.continuous.integrable_of_hasCompactSupport hF.2
    have j : Integrable F' μG := hF'.1.continuous.integrable_of_hasCompactSupport hF'.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (i.const_mul a) j, integral_const_mul, h2, h2']

end GlobalTheory.RootEx.QuotLinear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.CompactQuotientFourier

theorem setIntegral_translate {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → ℂ)
    (hp : ∀ γ ∈ Γ, ∀ w, h (γ + w) = h w) (u : G) : ∫ w in 𝓕, h (w + u) ∂μ = ∫ w in 𝓕, h w ∂μ := by
  have h1 : IsAddFundamentalDomain Γ (u +ᵥ 𝓕) μ := h𝓕.vadd_of_comm u
  rw [h𝓕.setIntegral_eq h1 (f := h) fun γ w => hp γ γ.2 w]
  have h2 := (measurePreserving_add_left μ u).setIntegral_image_emb (measurableEmbedding_addLeft u) h 𝓕
  simp only [add_comm _ u]
  exact h2.symm

theorem inversion_at_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] [Countable A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ‖∫ x in 𝓕, χ a x * Φ x ∂μ‖) → Φ 0 = ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ _ χ hc hx ha hn hker hinj μ 𝓕 hμ h𝓕 h1 Φ hΦ hper hsum
  classical
  haveI := hμ
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hvol : μ.real 𝓕 = 1 := by simp [Measure.real, h1]
  have hne : ∀ a x, χ a x ≠ 0 := fun a x h => by simpa [h] using hn a x
  have hχ0 : ∀ x, χ 0 x = 1 := fun x => by
    have h2 : χ 0 x * χ 0 x = χ 0 x * 1 := by rw [mul_one, ← ha, add_zero]
    exact mul_left_cancel₀ (hne 0 x) h2
  have hχx0 : ∀ a, χ a 0 = 1 := fun a => by
    have h2 : χ a 0 * χ a 0 = χ a 0 * 1 := by rw [mul_one, ← hx, add_zero]
    exact mul_left_cancel₀ (hne a 0) h2
  have hstar : ∀ a x, star (χ a x) = χ (-a) x := fun a x => by
    have h1' : χ (-a) x * χ a x = 1 := by rw [← ha, neg_add_cancel, hχ0]
    have h2 : star (χ a x) * χ a x = 1 := by simp [Complex.conj_mul', hn]
    exact mul_right_cancel₀ (hne a x) (h2.trans h1'.symm)
  have hperχ : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := fun a γ hγ x => by
    rw [hx, (hker γ).2 hγ a, one_mul]
  have horth : ∀ a b, ∫ x in 𝓕, χ b x * star (χ a x) ∂μ = if a = b then 1 else 0 := by
    intro a b
    have he : ∀ x, χ b x * star (χ a x) = χ (b - a) x := fun x => by rw [hstar, ← ha, sub_eq_add_neg]
    simp_rw [he]
    split_ifs with hab
    · subst hab
      simp [hχ0, hvol]
    · have hc' : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
      obtain ⟨x₀, hx₀⟩ : ∃ x₀, χ (b - a) x₀ ≠ 1 := by
        by_contra h
        push_neg at h
        exact hc' (hinj _ h)
      have key := setIntegral_translate Γ μ 𝓕 h𝓕 (χ (b - a)) (hperχ _) x₀
      simp_rw [hx _ _ x₀] at key
      rw [integral_mul_const] at key
      have h3 : (∫ x in 𝓕, χ (b - a) x ∂μ) * (χ (b - a) x₀ - 1) = 0 := by
        rw [mul_sub, key, mul_one, sub_self]
      exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hx₀)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  have hΦb : ∀ x, ‖Φ x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    rw [← hper γ hγ x]
    exact hC _ hk
  have hint : ∀ f : G → ℂ, Continuous f → ∀ B, (∀ x, ‖f x‖ ≤ B) → Integrable f (μ.restrict 𝓕) :=
    fun f hf B hB => Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  set c : A → ℂ := fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ with hcdef
  have hterm : ∀ a x, ‖c a * star (χ a x)‖ = ‖c a‖ := fun a x => by
    rw [norm_mul, norm_star, hn, mul_one]
  let S : G → ℂ := fun x => ∑' a, c a * star (χ a x)
  have hScont : Continuous S :=
    continuous_tsum (fun a => continuous_const.mul (hc a).star) hsum (fun a x => (hterm a x).le)
  have hSper : ∀ γ ∈ Γ, ∀ x, S (γ + x) = S x := fun γ hγ x => by
    simp only [S, hperχ _ γ hγ]
  have hSb : ∀ x, ‖S x‖ ≤ ∑' a, ‖c a‖ := fun x => by
    have hs : Summable (fun a => ‖c a * star (χ a x)‖) := by simp_rw [hterm]; exact hsum
    calc ‖S x‖ ≤ ∑' a, ‖c a * star (χ a x)‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' a, ‖c a‖ := by simp_rw [hterm]
  have hcS : ∀ b, ∫ x in 𝓕, χ b x * S x ∂μ = c b := by
    intro b
    have e : ∀ x, χ b x * S x = ∑' a, χ b x * (c a * star (χ a x)) := fun x => tsum_mul_left.symm
    have hnorm : ∀ a x, ‖χ b x * (c a * star (χ a x))‖ = ‖c a‖ := fun a x => by
      rw [norm_mul, hn, one_mul, hterm]
    have hFi : ∀ a, Integrable (fun x => χ b x * (c a * star (χ a x))) (μ.restrict 𝓕) := fun a =>
      hint _ ((hc b).mul (continuous_const.mul (hc a).star)) ‖c a‖ fun x => (hnorm a x).le
    have hFs : Summable fun a => ∫ x in 𝓕, ‖χ b x * (c a * star (χ a x))‖ ∂μ := by
      simp_rw [hnorm]
      simpa [hvol] using hsum
    have e2 : ∀ a, ∫ x in 𝓕, χ b x * (c a * star (χ a x)) ∂μ = c a * (if a = b then 1 else 0) := fun a => by
      rw [← horth, ← integral_const_mul]
      congr 1
      funext x
      ring
    simp_rw [e]
    rw [← integral_tsum_of_summable_integral_norm hFi hFs]
    simp_rw [e2, mul_ite, mul_one, mul_zero]
    simp
  have hdiff := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha hχ0 hn hker
    μ 𝓕 hμ h𝓕 (Φ - S) (hΦ.sub hScont) (fun γ hγ x => by simp only [Pi.sub_apply, hper γ hγ, hSper γ hγ])
    (fun a => by
      simp only [Pi.sub_apply, mul_sub]
      have i1 : Integrable (fun x => χ a x * Φ x) (μ.restrict 𝓕) :=
        hint _ ((hc a).mul hΦ) C fun x => by rw [norm_mul, hn, one_mul]; exact hΦb x
      have i2 : Integrable (fun x => χ a x * S x) (μ.restrict 𝓕) :=
        hint _ ((hc a).mul hScont) _ fun x => by rw [norm_mul, hn, one_mul]; exact hSb x
      rw [integral_sub i1 i2, hcS, sub_self])
  have h0 := congrFun hdiff 0
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h0
  rw [h0]
  simp only [S, hχx0, star_one, mul_one]

end GlobalTheory.CompactQuotientFourier
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_inversion_zero_compact_quotient : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] [Countable A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ‖∫ x in 𝓕, χ a x * Φ x ∂μ‖) → Φ 0 = ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ := by
  first | exact @GlobalTheory.CompactQuotientFourier.inversion_at_zero | exact GlobalTheory.CompactQuotientFourier.inversion_at_zero | (intros; apply GlobalTheory.CompactQuotientFourier.inversion_at_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerEquivUpperSwap
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.SwapBlocks

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem smInd_equiv_of_eq [TopologicalSpace G] [IsTopologicalGroup G] {H H' : Subgroup G} (h : H = H')
    (σ : Representation ℂ H V) (σ' : Representation ℂ H' V)
    (hσ : ∀ g (hg : g ∈ H) (hg' : g ∈ H'), σ ⟨g, hg⟩ = σ' ⟨g, hg'⟩) :
    Nonempty ((smInd H σ).Equiv (smInd H' σ')) := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun g => hσ g.1 g.2 g.2
  exact ⟨Representation.Equiv.refl _⟩

end General

section Blocks

variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n]

end Blocks

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

end Local

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem nonempty_equiv_smInd_of_eq [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Type} [AddCommGroup W] [Module ℂ W] {H H' : Subgroup G} (h : H = H')
    (σ : Representation ℂ H W) (σ' : Representation ℂ H' W)
    (hσ : ∀ (g : G) (hg : g ∈ H) (hg' : g ∈ H'), σ ⟨g, hg⟩ = σ' ⟨g, hg'⟩) :
    Nonempty ((_root_.GlobalTheory.PRep.smInd H σ).Equiv (_root_.GlobalTheory.PRep.smInd H' σ')) := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun p => hσ p p.2 p.2
  exact ⟨Representation.Equiv.refl _⟩

variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem parabLower_eq_parab_sumComm (e : a ⊕ b ≃ n) :
    _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e) =
      _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) := by
  ext g
  rw [_root_.GlobalTheory.SmGL.mem_parabLower_two, _root_.GlobalTheory.SmGL.mem_parab_two]
  simp

variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem leviProj_sumComm_eq_swap_leviProjLower (e : a ⊕ b ≃ n)
    (p : _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e))
    (hp : (p : GL n R) ∈
      _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e))) :
    _root_.GlobalTheory.SmGL.leviProj R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) ⟨p, hp⟩ =
      _root_.GlobalTheory.SmGL.leviTwo R b a
        ((_root_.GlobalTheory.SmGL.leviTwo R a b).symm
          (_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p)).swap := by
  funext x
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  cases x
  · change _ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p true : GL b R) :
      Matrix b b R) i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]
    rfl
  · change _ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p false : GL a R) :
      Matrix a a R) i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]
    rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
private theorem deltaHalf_inv_leviTwo_eq_deltaHalf_swap (g : GL a k × GL b k) :
    (_root_.GlobalTheory.SmGL.deltaHalf k (_root_.GlobalTheory.SmGL.Two a b))⁻¹ (_root_.GlobalTheory.SmGL.leviTwo k a b g) =
      _root_.GlobalTheory.SmGL.deltaHalf k (_root_.GlobalTheory.SmGL.Two b a) (_root_.GlobalTheory.SmGL.leviTwo k b a g.swap) := by
  rw [MonoidHom.inv_apply, _root_.GlobalTheory.SmGL.deltaHalf_two,
    _root_.GlobalTheory.SmGL.deltaHalf_two, neg_div, neg_div, _root_.GlobalTheory.SmGL.absPow_neg,
    _root_.GlobalTheory.SmGL.absPow_neg]
  simp only [Prod.fst_swap, Prod.snd_swap, MonoidHom.inv_apply, mul_inv, inv_inv]
  exact mul_comm _ _

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem jacquet_apply_eq_of_eq {M M' : Type} [Group M] [Group M']
    (π : Representation ℂ G V) (N : Subgroup G) (s : M →* G) (s' : M' →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ m, s' m ∈ Subgroup.normalizer (N : Set G)) {x : M} {x' : M'} (h : s x = s' x') :
    _root_.GlobalTheory.PRep.jacquet π N s hs x = _root_.GlobalTheory.PRep.jacquet π N s' hs' x' := by
  unfold _root_.GlobalTheory.PRep.jacquet
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  rw [h]

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem nonempty_equiv_twist_jacquet_comp {M M' K : Type} [Group M] [Group M'] [Group K]
    (π : Representation ℂ G V) {N N' : Subgroup G} (hN : N = N') (s : M →* G) (s' : M' →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ m, s' m ∈ Subgroup.normalizer (N' : Set G)) (φ : K →* M) (φ' : K →* M')
    (hφ : ∀ x, s (φ x) = s' (φ' x)) (χ : M →* ℂˣ) (χ' : M' →* ℂˣ)
    (hχ : ∀ x, χ (φ x) = χ' (φ' x)) :
    Nonempty (Representation.Equiv
      ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ)
      ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N' s' hs') χ').comp φ')) := by
  subst hN
  have h : (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ =
      (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s' hs') χ').comp φ' := by
    refine MonoidHom.ext fun x => LinearMap.ext fun v => ?_
    simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply, hχ,
      jacquet_apply_eq_of_eq π N s s' hs hs' (hφ x)]
  rw [h]
  exact ⟨Representation.Equiv.refl _⟩

section
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n]

private theorem unipRadLower_eq_unipRad_sumComm (e : a ⊕ b ≃ n) :
    _root_.GlobalTheory.SmGL.unipRadLower R (_root_.GlobalTheory.SmGL.two e) =
      _root_.GlobalTheory.SmGL.unipRad R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) := by
  ext g
  rw [_root_.GlobalTheory.SmGL.mem_unipRadLower, _root_.GlobalTheory.SmGL.mem_unipRad,
    parabLower_eq_parab_sumComm]
  refine and_congr_right fun _ => ?_
  simp only [Bool.forall_bool]
  exact and_comm

private theorem leviEmb_leviTwo_apply_eq_fromBlocks (e : a ⊕ b ≃ n) (g : GL a R × GL b R) (u v : a ⊕ b) :
    (_root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two e) (_root_.GlobalTheory.SmGL.leviTwo R a b g) :
        Matrix n n R) (e u) (e v) =
      Matrix.fromBlocks (g.1 : Matrix a a R) 0 0 (g.2 : Matrix b b R) u v := by
  rcases u with u | u <;> rcases v with v | v
  · rw [← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_false e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_same]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_true e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : false ≠ true)]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_false e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : true ≠ false)]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_true e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_same]
    rfl

private theorem leviEmb_leviTwo_eq_leviEmb_sumComm_swap (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    _root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two e) (_root_.GlobalTheory.SmGL.leviTwo R a b g) =
      _root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e))
        (_root_.GlobalTheory.SmGL.leviTwo R b a g.swap) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  obtain ⟨u, rfl⟩ := e.surjective i
  obtain ⟨v, rfl⟩ := e.surjective j
  have hu : e u = ((Equiv.sumComm b a).trans e) u.swap := by simp
  have hv : e v = ((Equiv.sumComm b a).trans e) v.swap := by simp
  rw [leviEmb_leviTwo_apply_eq_fromBlocks, hu, hv, leviEmb_leviTwo_apply_eq_fromBlocks]
  rcases u with u | u <;> rcases v with v | v <;> rfl
end

theorem _root_.GlobalTheory.SmGL.SwapBlocks.lower_equiv_upper_swap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V], (∀ ρ : Representation ℂ (GL a k × GL b k) V, Nonempty ((_root_.GlobalTheory.SmGL.ind₂Lower e ρ).Equiv (_root_.GlobalTheory.SmGL.ind₂ ((Equiv.sumComm b a).trans e) (ρ.comp (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom)))) ∧ ∀ π : Representation ℂ (GL n k) V, Nonempty ((_root_.GlobalTheory.SmGL.jac₂Lower e π).Equiv ((_root_.GlobalTheory.SmGL.jac₂ ((Equiv.sumComm b a).trans e) π).comp (MulEquiv.prodComm : GL a k × GL b k ≃* GL b k × GL a k).toMonoidHom)) := by
  intro k _ _ _ _ a b n _ _ _ _ _ _ e V _ _
  refine ⟨fun ρ => ?_, fun π => ?_⟩
  · unfold _root_.GlobalTheory.SmGL.ind₂Lower _root_.GlobalTheory.SmGL.ind₂
      _root_.GlobalTheory.SmGL.parIndLower _root_.GlobalTheory.SmGL.parInd
    refine nonempty_equiv_smInd_of_eq (parabLower_eq_parab_sumComm k e) _ _
      fun g hg hg' => LinearMap.ext fun v => ?_
    simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply,
      MulEquiv.coe_toMonoidHom]
    rw [leviProj_sumComm_eq_swap_leviProjLower k e ⟨g, hg⟩ hg', ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap]
    simp
  · unfold _root_.GlobalTheory.SmGL.jac₂Lower _root_.GlobalTheory.SmGL.jac₂ _root_.GlobalTheory.SmGL.jacLower
      _root_.GlobalTheory.SmGL.jac _root_.GlobalTheory.SmGL.jacU
    rw [MonoidHom.comp_assoc]
    refine nonempty_equiv_twist_jacquet_comp π (unipRadLower_eq_unipRad_sumComm k e) _ _ _ _
      _ _ (fun x => leviEmb_leviTwo_eq_leviEmb_sumComm_swap k e x) _ _ fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MonoidHom.inv_apply, show (MulEquiv.prodComm x : GL b k × GL a k) = x.swap from rfl,
      ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap, MonoidHom.inv_apply, inv_inv]

end GlobalTheory.SmGL.SwapBlocks
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantCosetInd
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

noncomputable section

namespace GlobalTheory.InvBilinTest

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open Classical in
def cosetInd (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (g : G) :
    SB G := by
  classical
  exact ⟨fun x => if x * g⁻¹ ∈ K then 1 else 0, by
    constructor
    · have h1 : IsOpen {x : G | x * g⁻¹ ∈ K} := ho.preimage (continuous_id.mul continuous_const)
      have h2 : IsClosed {x : G | x * g⁻¹ ∈ K} :=
        (K.isClosed_of_isOpen ho).preimage (continuous_id.mul continuous_const)
      rw [IsLocallyConstant.iff_exists_open]
      intro y
      by_cases hy : y * g⁻¹ ∈ K
      · exact ⟨_, h1, hy, fun x hx => by rw [if_pos hy]; exact if_pos hx⟩
      · exact ⟨_, h2.isOpen_compl, hy, fun x hx => by rw [if_neg hy]; exact if_neg hx⟩
    · refine HasCompactSupport.intro (hK.image (continuous_id.mul (continuous_const (y := g))))
        fun x hx => if_neg fun h => hx ⟨x * g⁻¹, h, by change (x * g⁻¹) * g = x; group⟩⟩

open Classical in
theorem cosetInd_apply (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    (g x : G) : (cosetInd K ho hK g).1 x = if x * g⁻¹ ∈ K then 1 else 0 := rfl

variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]

open Classical in
theorem _root_.GlobalTheory.InvBilinTest.integral_ite (K : Subgroup G) (ho : IsOpen (K : Set G)) (c : ℂ) :
    ∫ g, (if g ∈ K then c else 0) ∂μ = (μ.real K : ℂ) * c := by
  classical
  have hm : MeasurableSet (K : Set G) := ho.measurableSet
  have h : (fun g : G => if g ∈ K then c else 0) = (K : Set G).indicator (fun _ => c) := by
    ext g
    simp [Set.indicator_apply]
  rw [h, integral_indicator_const c hm, Complex.real_smul]

end GlobalTheory.InvBilinTest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentSubgroupSuccDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentSubgroupSuccDecomposition
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.RadicalDecomp
open GlobalTheory.RootEx.Radical

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem mem_N_of_succ {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c (p + 1))
    (h0 : ∀ (l : Fin c) (s : n), l.val + 1 = p → g.val (Sum.inr l) (Sum.inl s) = 0) :
    g ∈ N k n c p := by
  rw [mem_N_iff] at hg ⊢
  intro r s hrs
  rcases r with a | l <;> rcases s with b | j
  · exact hg _ _ (by simp [lev])
  · exact hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢; omega)
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    by_cases hp : l.val + 1 = p
    · rw [h0 l b hp]
      simp
    · exact hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega)
  · exact hg _ _ (by simpa [lev] using hrs)

theorem inv_rowE_val (u : n → k) : ((rowE c p u)⁻¹).val =
    fromBlocks 1 0 (-(Matrix.of fun (l : Fin c) s => if l.val + 1 = p then u s else 0)) 1 := rfl

theorem succ_decomp : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), ∀ g ∈ N k n c (p + 1), ∃ g₁ ∈ N k n c p ⊓ N k n c (p + 1), ∃ u : n → k, g = g₁ * rowE c p u := by
  intro k _ n _ _ c p g hg
  set u : n → k := fun s => ∑ l : Fin c, if l.val + 1 = p then g.val (Sum.inr l) (Sum.inl s) else 0
    with hu
  have hE : rowE c p u ∈ N k n c (p + 1) := rowE_mem u (Nat.lt_succ_self p)
  have h1 : g * (rowE c p u)⁻¹ ∈ N k n c (p + 1) := Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hE)
  refine ⟨g * (rowE c p u)⁻¹, ⟨?_, h1⟩, u, by simp⟩
  refine mem_N_of_succ h1 ?_
  intro l s hl
  have hg' := (mem_N_iff g).1 hg
  have key : ∀ l' : Fin c, (l'.val + 1 = p ↔ l' = l) :=
    fun l' => ⟨fun h => Fin.ext (by omega), fun h => h ▸ hl⟩
  have hd : g.val (Sum.inr l) (Sum.inr l) = 1 := by
    have := hg' (Sum.inr l) (Sum.inr l) le_rfl
    simpa using this
  have hus : u s = g.val (Sum.inr l) (Sum.inl s) := by
    simp only [hu, key, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Units.val_mul, inv_rowE_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.one_apply, Matrix.neg_apply,
    Matrix.of_apply, key, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, hus]
  simp only [Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hd]
  ring

end GlobalTheory.RootEx.RadicalDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentSubgroupSuccDecompositionStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchangeUnipotentSubgroup_succ_decomposition : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), ∀ g ∈ N k n c (p + 1), ∃ g₁ ∈ N k n c p ⊓ N k n c (p + 1), ∃ u : n → k, g = g₁ * rowE c p u := by
  first | exact @GlobalTheory.RootEx.RadicalDecomp.succ_decomp | exact GlobalTheory.RootEx.RadicalDecomp.succ_decomp | (intros; apply GlobalTheory.RootEx.RadicalDecomp.succ_decomp <;> assumption)
end
end
