module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfLocalDiscriminant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentQuotientInvariantProbability
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentQuotientInvariantProbability
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

namespace GlobalTheory.UnipQuot

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem exists_domain (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m : G, ∃ γ ∈ Γ, γ * m ∈ C) :
    ∃ D : Set G, MeasurableSet D ∧ D ⊆ C ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ D := by
  obtain ⟨ψ, hψm, hψi⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated G
  have he := measurableEmbedding_embeddingReal (ℕ → Bool)
  set φ : G → ℝ := fun x => embeddingReal (ℕ → Bool) (ψ x) with hφ
  have hφm : Measurable φ := he.measurable.comp hψm
  have hφi : Function.Injective φ := he.injective.comp hψi
  have hCm : MeasurableSet C := hC.measurableSet
  refine ⟨C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)}, ?_, Set.inter_subset_left, ?_⟩
  · refine hCm.inter (MeasurableSet.iInter fun γ => ?_)
    have h1 : MeasurableSet {y : G | (γ : G) * y ∈ C} := (measurable_const_mul (γ : G)) hCm
    have h2 : MeasurableSet {y : G | φ y ≤ φ ((γ : G) * y)} :=
      measurableSet_le hφm (hφm.comp (measurable_const_mul (γ : G)))
    have : {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} =
        {y : G | (γ : G) * y ∈ C}ᶜ ∪ {y : G | φ y ≤ φ ((γ : G) * y)} := by
      ext y; simp [imp_iff_not_or]
    rw [this]; exact h1.compl.union h2
  · intro x
    have hK : IsCompact ((fun y => y * x⁻¹) '' C) := hC.image (continuous_mul_const _)
    have hF := hfin _ hK
    obtain ⟨γ₀, hγ₀, hγ₀C⟩ := hcov x
    have hne : ((fun y => y * x⁻¹) '' C ∩ (Γ : Set G)).Nonempty :=
      ⟨γ₀, ⟨γ₀ * x, hγ₀C, by simp⟩, hγ₀⟩
    obtain ⟨γ, ⟨⟨y, hy, hyγ⟩, hγΓ⟩, hmin⟩ := Set.exists_min_image _ (fun g => φ (g * x)) hF hne
    have hγx : γ * x ∈ C := by rw [← hyγ]; simpa using hy
    have hmem : (⟨γ, hγΓ⟩ : Γ) • x ∈
        C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} := by
      refine ⟨hγx, Set.mem_iInter.2 fun δ hδ => ?_⟩
      have hδ' : (δ : G) * (γ * x) ∈ C := hδ
      have := hmin ((δ : G) * γ) ⟨⟨_, hδ', by simp [mul_assoc]⟩, Γ.mul_mem δ.2 hγΓ⟩
      show φ (γ * x) ≤ φ ((δ : G) * (γ * x))
      simpa [mul_assoc] using this
    refine ⟨⟨γ, hγΓ⟩, hmem, fun δ hδ => ?_⟩
    have hδC : (δ : G) * x ∈ C := hδ.1
    have h1 : φ ((δ : G) * x) ≤ φ (γ * x) := by
      have := Set.mem_iInter.1 hδ.2 ⟨γ * (δ : G)⁻¹, Γ.mul_mem hγΓ (Γ.inv_mem δ.2)⟩
      have e : γ * (δ : G)⁻¹ * (δ • x) = γ * x := by
        show γ * (δ : G)⁻¹ * ((δ : G) * x) = γ * x
        simp [mul_assoc]
      simp only [Set.mem_ofPred_eq, e] at this
      exact this hγx
    have h2 : φ (γ * x) ≤ φ ((δ : G) * x) := hmin δ ⟨⟨_, hδC, by simp⟩, δ.2⟩
    exact Subtype.ext (mul_right_cancel (hφi (le_antisymm h1 h2)))

theorem exists_prob [LocallyCompactSpace G] (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m : G, ∃ γ ∈ Γ, γ * m ∈ C) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧
      ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) → ∀ g : G, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν := by
  obtain ⟨D, hDm, hDC, hD⟩ := exists_domain Γ hfin C hC hcov
  set μ : Measure G := Measure.haar
  have hfd : IsFundamentalDomain Γ D μ := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hfd' : ∀ g : G, IsFundamentalDomain Γ ((fun y => y * g) ⁻¹' D) μ := fun g =>
    IsFundamentalDomain.mk' ((measurable_mul_const g) hDm).nullMeasurableSet fun x => by
      have := hD (x * g)
      simpa [Subgroup.smul_def, mul_assoc] using this
  have h0 : μ D ≠ 0 := hfd.measure_ne_zero (NeZero.ne μ)
  have htop : μ D ≠ ⊤ := ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono hDC)
  have hinv : ∀ g : G, Measure.map (fun y => y * g) μ = μ := by
    intro g
    have : IsFiniteMeasureOnCompacts (Measure.map (fun y => y * g) μ) := ⟨fun K hK => by
      rw [Measure.map_apply (measurable_mul_const g) hK.measurableSet]
      exact ((Homeomorph.mulRight g).isCompact_preimage.2 hK).measure_lt_top⟩
    have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun y => y * g) μ) μ
    set c := (Measure.map (fun y => y * g) μ).haarScalarFactor μ
    have h1 : Measure.map (fun y => y * g) μ D = μ D := by
      rw [Measure.map_apply (measurable_mul_const g) hDm]
      exact (hfd' g).measure_eq hfd
    rw [h] at h1
    have h2 : (c : ENNReal) = 1 := by
      have : (c : ENNReal) * μ D = 1 * μ D := by simpa using h1
      exact (ENNReal.mul_left_inj h0 htop).1 this
    have h3 : c = 1 := by exact_mod_cast h2
    rw [h, h3, one_smul]
  refine ⟨(μ D)⁻¹ • μ.restrict D, ⟨?_⟩, ?_, ?_⟩
  · simp [ENNReal.inv_mul_cancel h0 htop]
  · have : Cᶜ ∩ D = ∅ := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h1 h2 => h1 (hDC h2)
    rw [smul_apply, Measure.restrict_apply hC.measurableSet.compl, this]
    simp
  · intro f hf g
    rw [integral_smul_measure, integral_smul_measure]
    congr 1
    have hemb : MeasurableEmbedding (fun y : G => y * g) := measurableEmbedding_mulRight g
    have h1 := hemb.setIntegral_map (μ := μ) f ((fun y => y * g⁻¹) ⁻¹' D)
    have h2 : (fun y : G => y * g) ⁻¹' ((fun y => y * g⁻¹) ⁻¹' D) = D := by
      ext y; simp
    rw [hinv g, h2] at h1
    rw [← h1]
    exact (hfd' g⁻¹).setIntegral_eq hfd fun γ x => hf γ γ.2 x

theorem exists_prob_subgroup [LocallyCompactSpace G] (N Γ : Subgroup G) (hN : IsClosed (N : Set G))
    [Countable Γ] (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m ∈ N, ∃ γ ∈ Γ, γ ∈ N ∧ γ * m ∈ C) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧ ν (N : Set G)ᶜ = 0 ∧
      ∀ f : G → ℂ, (∀ γ ∈ Γ, γ ∈ N → ∀ y, f (γ * y) = f y) →
        ∀ g ∈ N, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν := by
  have hce : Topology.IsClosedEmbedding (Subtype.val : N → G) := hN.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace N := hce.locallyCompactSpace
  have : SecondCountableTopology N := hce.isEmbedding.secondCountableTopology
  have hemb : MeasurableEmbedding (Subtype.val : N → G) := hce.measurableEmbedding
  have : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨x.1.1, x.2⟩ : Γ)) ?_
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  obtain ⟨ν, hν, hνC, hνf⟩ := exists_prob (Γ.subgroupOf N) (fun K hK => by
      have := hfin _ (hK.image continuous_subtype_val)
      refine (this.preimage (f := (Subtype.val : N → G)) Subtype.val_injective.injOn).subset ?_
      rintro x ⟨hx, hx'⟩
      exact ⟨⟨x, hx, rfl⟩, hx'⟩)
    (Subtype.val ⁻¹' C) (hce.isCompact_preimage hC) (fun m => by
      obtain ⟨γ, h1, h2, h3⟩ := hcov m m.2
      exact ⟨⟨γ, h2⟩, h1, h3⟩)
  refine ⟨ν.map Subtype.val, (by letI := hν; infer_instance), ?_, ?_, ?_⟩
  · rw [hemb.map_apply]; exact hνC
  · rw [hemb.map_apply]
    have : (Subtype.val : N → G) ⁻¹' (N : Set G)ᶜ = ∅ := by
      ext y; simp
    rw [this, measure_empty]
  · intro f hf g hg
    rw [hemb.integral_map, hemb.integral_map]
    exact hνf (fun y => f y) (fun γ hγ y => hf γ hγ γ.2 y) ⟨g, hg⟩

end General

theorem exists_quot_prob (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) :
    ∃ ν : Measure I.GA, IsProbabilityMeasure ν ∧ I.IsNQuotMeas W ν ∧
      ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ν Cpᶜ = 0 := by
  obtain ⟨h2, hlc, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨⟨N, hN⟩, hcl, -, -, C, hC, hCN, hcov⟩ := GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I W hW
  obtain ⟨Γ, hΓ, hΓc, hfin, -⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain I
  have : BorelSpace I.GA := inferInstance
  have mN : ∀ x, x ∈ N ↔ x ∈ I.NA W := fun x => by rw [← hN]; rfl
  have mΓ : ∀ x, x ∈ Γ ↔ x ∈ I.GFset := fun x => by rw [← hΓ]; rfl
  obtain ⟨ν, hν, hνC, hνN, hf⟩ := exists_prob_subgroup N Γ (hN ▸ hcl) (hΓ ▸ hfin) C hC (fun m hm => by
    obtain ⟨γ, ⟨h1, h1'⟩, h3⟩ := hcov m ((mN m).1 hm)
    exact ⟨γ⁻¹, Γ.inv_mem ((mΓ γ).2 h1), N.inv_mem ((mN γ).2 h1'), h3⟩)
  refine ⟨ν, hν, ⟨inferInstance, IsProbabilityMeasure.ne_zero ν, hN ▸ hνN, ?_⟩, C, hC, hCN, hνC⟩
  intro f hfi g hg
  exact hf f (fun γ h1 h1' y => hfi γ ⟨(mΓ γ).1 h1, (mN γ).1 h1'⟩ y) g ((mN g).2 hg)

end GlobalTheory.UnipQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentQuotientInvariantProbabilityStatement
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentQuotient_invariant_probability : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)), I.IsIsot W → ∃ ν : Measure I.GA, IsProbabilityMeasure ν ∧ I.IsNQuotMeas W ν ∧ ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ν Cpᶜ = 0 := by
  first | exact @GlobalTheory.UnipQuot.exists_quot_prob | exact GlobalTheory.UnipQuot.exists_quot_prob | (intros; apply GlobalTheory.UnipQuot.exists_quot_prob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativesCoefficientsConvolutionFixedVector
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativesCoefficientsConvolutionFixedVector
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff Topology Pointwise

namespace GlobalTheory.DerivConv

theorem exists_weak_deriv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (c : ℝ → H) (hc : ∀ u, DifferentiableAt ℝ (fun t => ⟪u, c t⟫_ℂ) 0) :
    ∃ v : H, ∀ u, deriv (fun t => ⟪u, c t⟫_ℂ) 0 = ⟪u, v⟫_ℂ := by
  have h : Filter.Tendsto (fun (t : ℝ) (u : H) => innerSL ℂ (slope c 0 t) u) (𝓝[≠] 0)
      (𝓝 fun u => (starRingEnd ℂ) (deriv (fun t => ⟪u, c t⟫_ℂ) 0)) := by
    refine tendsto_pi_nhds.2 fun u => ?_
    have h1 := (Complex.continuous_conj.tendsto _).comp (hc u).hasDerivAt.tendsto_slope
    refine h1.congr fun t => ?_
    simp only [Function.comp, innerSL_apply_apply]
    rw [← inner_conj_symm (slope c 0 t) u]
    congr 1
    simp only [slope_def_module, inner_sub_right, ← Complex.coe_smul, inner_smul_right, smul_eq_mul]
  let L : H →L[ℂ] ℂ := continuousLinearMapOfTendsto (fun t : ℝ => innerSL ℂ (slope c 0 t)) h
  refine ⟨(InnerProductSpace.toDual ℂ H).symm L, fun u => ?_⟩
  rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
  exact (Complex.conj_conj _).symm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem differentiableAt_curve {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    DifferentiableAt ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 := by
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  obtain ⟨U, F, hU, hg, hF, hfF⟩ := hf 1 h1
  have hγ := hasDerivAt_mul_exp_smul_zero 1 X
  simp only [Matrix.one_mul] at hγ
  have hγ0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F 1 :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.differentiableAt.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
  filter_upwards [hmem] with t ht
  exact hfF _ ht (exp_indefinite_unitary_holds n ε X hX t)

theorem smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (h : ∀ g, inUJ ε g → f g = f' g) : SmoothOnG ε f' := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  exact ⟨U, F, hU, hgU, hF, fun x hx hxJ => (h x hxJ).symm.trans (e x hx hxJ)⟩

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_Rd (hσ : IsURepOn (UJset ε) σ) {s : H} (hs : ∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    ∃ v : H, ∀ u, ∀ g, inUJ ε g → Rd X (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g v⟫_ℂ := by
  obtain ⟨v, hv⟩ := exists_weak_deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) s)
    fun u => differentiableAt_curve (hs u) hX
  refine ⟨v, fun u g hg => ?_⟩
  rw [← ContinuousLinearMap.adjoint_inner_left, ← hv]
  unfold Rd
  congr 1
  funext t
  beta_reduce
  rw [hσ.1.2 g hg _ (exp_indefinite_unitary_holds n ε X hX t), ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem exists_Eword (hσ : IsURepOn (UJset ε) σ) {s : H} (hs : ∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ))
    (w : List (Fin n × Fin n)) :
    ∃ s' : H, (∀ u, SmoothOnG ε (fun g => ⟪u, σ g s'⟫_ℂ)) ∧
      ∀ u, ∀ g, inUJ ε g → Eword ε w (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
  induction w with
  | nil => exact ⟨s, hs, fun _ _ _ => rfl⟩
  | cons p w ih =>
    obtain ⟨s', hs', e⟩ := ih
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    obtain ⟨v₁, h₁⟩ := exists_Rd hσ hs' hc.1
    obtain ⟨v₂, h₂⟩ := exists_Rd hσ hs' hc.2.1
    refine ⟨v₁ + Complex.I • v₂, fun u g hg => ?_, fun u g hg => ?_⟩
    · obtain ⟨U, F, hU, hgU, hF, e⟩ := smooth_congr (rdSmooth_of right_derivative_extends n ε _ _ (hs' u) hc.1) (h₁ u) g hg
      obtain ⟨U', F', hU', hgU', hF', e'⟩ :=
        smooth_congr (rdSmooth_of right_derivative_extends n ε _ _ (hs' u) hc.2.1) (h₂ u) g hg
      refine ⟨U ∩ U', fun h => F h + Complex.I * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
        (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
      intro x hx hxJ
      simp only [← e x hx.1 hxJ, ← e' x hx.2 hxJ, map_add (f := _), map_smul, inner_add_right, inner_smul_right]
    · refine (Eword_congr ε (e u) [p] g hg).trans ?_
      simp only [Eword, Eab, Ec, id, h₁ u g hg, h₂ u g hg, map_add (f := _), map_smul, inner_add_right, inner_smul_right]

theorem smooth_coef (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} {s : H}
    (hα : SmoothOnG ε α) (hαc : HasCompactSupport (fun g : UJ ε => α (umat g)))
    (hfix : ∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ) (u : H) :
    SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := isClosedEmbeddingMatrix n ε
  obtain ⟨F, hF, hFα⟩ := GlobalTheory.smoothOnG_exists_contDiff_extension n ε α hα
  have hmem : ∀ g : UJ ε, inUJ ε (umat g) := fun g => g.2
  have hu : Continuous fun g : UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : UJ ε => ⟪u, σ (umat g) s⟫_ℂ :=
    continuous_const.inner ((hcont s).comp_continuous hu hmem)
  have hlift : ∀ x, inUJ ε x → ∃ z : UJ ε, umat z = x := fun x hx => by
    have : x ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [show Set.range (fun g : UJ ε => umat g) = _ from hrange]; exact hx
    exact this
  have hinv : ∀ z : UJ ε, Jm ε * (umat z)ᴴ * Jm ε = umat z⁻¹ := fun z => by
    have h : (umat z)ᴴ * Jm ε * umat z = Jm ε := hmem z
    have i2 : umat z * umat z⁻¹ = 1 := Units.mul_inv _
    calc Jm ε * (umat z)ᴴ * Jm ε = Jm ε * (umat z)ᴴ * Jm ε * (umat z * umat z⁻¹) := by rw [i2, Matrix.mul_one]
      _ = Jm ε * ((umat z)ᴴ * Jm ε * umat z) * umat z⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Jm_mul_self, Matrix.one_mul]
  have hform : ∀ z : UJ ε, ⟪u, σ (umat z) s⟫_ℂ
      = ∫ g : UJ ε, α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro z
    rw [← ContinuousLinearMap.adjoint_inner_left, ← hfix,
      ← integral_mul_left_eq_self (fun g : UJ ε => α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : umat (z * g) = umat z * umat g := rfl
    simp only [inv_mul_cancel_left, e]
    rw [hmul _ (hmem z) _ (hmem g), ContinuousLinearMap.adjoint_inner_left]
    rfl
  intro g₀ hg₀
  have hC : IsCompact ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) :=
    hemb.isCompact_preimage (isCompact_closedBall g₀ 1)
  have hK := hC.mul hαc
  set K := ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) * tsupport (fun g : UJ ε => α (umat g))
  have hΨ : ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
      F (fun i j => (Jm ε * z.1ᴴ * Jm ε * z.2.1) i j) * z.2.2 := by
    refine ContDiff.mul (hF.comp ?_) (contDiff_snd.comp contDiff_snd)
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    have e1 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        star (z.1 a b) := fun a b =>
      Complex.conjCLE.contDiff.comp ((contDiff_apply_apply (𝕜 := ℝ) a b).comp contDiff_fst)
    have e2 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        z.2.1 a b := fun a b =>
      (contDiff_apply_apply (𝕜 := ℝ) a b).comp (contDiff_fst.comp contDiff_snd)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact ContDiff.sum fun a _ => (ContDiff.sum fun b _ => (ContDiff.sum fun c _ =>
      contDiff_const.mul (e1 _ _)).mul contDiff_const).mul (e2 _ _)
  refine ⟨Metric.ball g₀ 1, fun x => ∫ g in K, F (fun i j => (Jm ε * xᴴ * Jm ε * umat g) i j) *
    ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε), Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_, ?_⟩
  · exact (contDiff_infty.2 fun m =>
      GlobalTheory.GardingVec.contDiff_setIntegral_nat (muG ε) hK (hu.prodMk hb) m _ hΨ).contDiffOn
  · intro x hx hxJ
    obtain ⟨z, rfl⟩ := hlift x hxJ
    have e : ∀ g : UJ ε, F (fun i j => (Jm ε * (umat z)ᴴ * Jm ε * umat g) i j) = α (umat (z⁻¹ * g)) := fun g => by
      rw [hinv]; exact hFα _ (hmem (z⁻¹ * g))
    simp only [e]
    rw [hform z]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra hne
    exact hg ⟨z, Metric.ball_subset_closedBall hx, z⁻¹ * g,
      subset_tsupport _ fun h => hne (by rw [show α (umat (z⁻¹ * g)) = 0 from h, zero_mul]),
      mul_inv_cancel_left z g⟩

theorem derivConv : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ) → (∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ)) ∧ ∀ w : List (Fin n × Fin n), ∃ s' : H, ∀ u, ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
  intro n ε H _ _ _ σ α s hσ hα hαc hfix
  have hs := smooth_coef hσ hα hαc hfix
  refine ⟨hs, fun w => ?_⟩
  obtain ⟨s', -, h⟩ := exists_Eword hσ hs w
  exact ⟨s', h⟩

end GlobalTheory.DerivConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativesCoefficientsConvolutionFixedVectorStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivatives_coefficients_convolutionFixed_vector : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ) → (∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ)) ∧ ∀ w : List (Fin n × Fin n), ∃ s' : H, ∀ u, ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
  first | exact @GlobalTheory.DerivConv.derivConv | exact GlobalTheory.DerivConv.derivConv | (intros; apply GlobalTheory.DerivConv.derivConv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameComponentLocalFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameComponentLocalFrame
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.FrLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem prV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] Ad F) :
    prV (E := E) v (sigR σ (Ad F) a) = sigR σ (v.adicCompletion F) (prV (E := E) v a) :=
  RingHom.congr_fun (Formalism.UG.P.afsplit_prV_comp_sigR σ v) a

theorem prV_OAd (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) :
    prV (E := E) v a ∈ intV E v :=
  ((GlobalTheory.St.G.IntAd.integral_adeles_properties F E).1 a).1 ha v

theorem prVec_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fin n → E ⊗[F] Ad F) :
    prVec v (x + y) = prVec v x + prVec v y := by
  funext i; simp [prVec, map_add (f := _)]

theorem prVec_zero (v : HeightOneSpectrum (𝓞 F)) : prVec v (0 : Fin n → E ⊗[F] Ad F) = 0 := by
  funext i; simp [prVec]

theorem prVec_smul (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] Ad F) (x : Fin n → E ⊗[F] Ad F) :
    prVec v (a • x) = prV (E := E) v a • prVec v x := by
  funext i; simp [prVec, map_mul]

theorem prVec_span (v : HeightOneSpectrum (𝓞 F)) (S : Set (Fin n → E ⊗[F] Ad F))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ Submodule.span (OAd F E) S) :
    prVec v x ∈ Submodule.span (intV E v) (prVec v '' S) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero => rw [prVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [prVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have h : prVec v (a • x) = (⟨prV (E := E) v a, prV_OAd v a.2⟩ : intV E v) • prVec v x :=
      prVec_smul v (a : E ⊗[F] Ad F) x
    rw [h]; exact Submodule.smul_mem _ _ hx

theorem prVec_hat (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ hat F L) : prVec v x ∈ loc v L := by
  have h := prVec_span v _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  exact ⟨l, hl, rfl⟩

theorem hR_prVec (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin n → E ⊗[F] Ad F) :
    hR σ J (v.adicCompletion F) (prVec v x) (prVec v y) = prV (E := E) v (hR σ J (Ad F) x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, map_mul, prV_sigR, prVec, Matrix.map_apply, Formalism.UG.P.afsplit_prV_inclE]

end GlobalTheory.St.G.FrLoc

open GlobalTheory.St.G.FrLoc in
theorem GlobalTheory.St.G.frame_component_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (g k : ℕ) (Fr : AdFrame σ J (hat F L) g k) (v : HeightOneSpectrum (𝓞 F)), prV (E := E) v Fr.eps * prV (E := E) v Fr.eps = prV (E := E) v Fr.eps ∧ prV (E := E) v Fr.eps * sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) = 0 ∧ prV (E := E) v Fr.eps ∈ intV E v ∧ (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - prV (E := E) v Fr.eps - sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps)) • y = (g : E ⊗[F] v.adicCompletion F) • z) ∧ (∀ i, prVec v (Fr.b i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.bd i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.b i) = prV (E := E) v Fr.eps • prVec v (Fr.b i)) ∧ (∀ i, prVec v (Fr.bd i) = sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) • prVec v (Fr.bd i)) ∧ (∀ i j, ∃ t ∈ intV E v, hR σ J (v.adicCompletion F) (prVec v (Fr.bd i)) (prVec v (Fr.b j)) - (if i = j then prV (E := E) v Fr.eps else 0) = (g : E ⊗[F] v.adicCompletion F) * t) ∧ (∀ y ∈ loc v L, InModL (loc v L) g (Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))) y) := by
  intro F E _ _ _ _ _ σ n J L g k Fr v
  refine ⟨?_, ?_, prV_OAd v Fr.eps_int, ?_, fun i => prVec_hat v L (Fr.b_mem i),
    fun i => prVec_hat v L (Fr.bd_mem i), ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, Fr.eps_idem]
  · rw [← prV_sigR, ← map_mul, Fr.eps_orth, map_zero]
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨z, hz, hzeq⟩ := Fr.eps_full (fun i => inclE (F := F) (Ad F) (l i))
        (Submodule.subset_span ⟨l, hl, rfl⟩)
      refine ⟨prVec v z, prVec_hat v L hz, ?_⟩
      have h := congrArg (prVec v) hzeq
      rw [prVec_smul, prVec_smul, map_sub, map_sub, map_one, prV_sigR, map_natCast] at h
      exact h
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨z₁, hz₁, e₁⟩ := hx
      obtain ⟨z₂, hz₂, e₂⟩ := hy
      exact ⟨z₁ + z₂, add_mem hz₁ hz₂, by rw [smul_add, smul_add, e₁, e₂]⟩
    | smul c x _ hx =>
      obtain ⟨z, hz, e⟩ := hx
      refine ⟨c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [Subring.smul_def, Subring.smul_def, smul_smul, mul_comm, ← smul_smul, e, smul_smul,
        smul_smul, mul_comm]
  · intro i
    have h := congrArg (prVec v) (Fr.b_eps i)
    rw [prVec_smul] at h
    exact h
  · intro i
    have h := congrArg (prVec v) (Fr.bd_eps i)
    rw [prVec_smul, prV_sigR] at h
    exact h
  · intro i j
    obtain ⟨t, ht, e⟩ := Fr.dual i j
    refine ⟨prV (E := E) v t, prV_OAd v ht, ?_⟩
    have h := congrArg (prV (E := E) v) e
    rw [map_sub, map_mul, map_natCast, ← hR_prVec, apply_ite (prV (E := E) v), map_zero] at h
    exact h
  · have hsub : prVec v '' (Set.range Fr.b ∪ Set.range Fr.bd) ⊆
        Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j)) := by
      rintro _ ⟨x, hx | hx, rfl⟩
      · obtain ⟨j, rfl⟩ := hx; exact Or.inl ⟨j, rfl⟩
      · obtain ⟨j, rfl⟩ := hx; exact Or.inr ⟨j, rfl⟩
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨s, hs, z, hz, e⟩ := Fr.span (fun i => inclE (F := F) (Ad F) (l i))
        (Submodule.subset_span ⟨l, hl, rfl⟩)
      refine ⟨prVec v s, Submodule.span_mono hsub (prVec_span v _ hs), prVec v z, prVec_hat v L hz, ?_⟩
      have h := congrArg (prVec v) e
      rw [prVec_add, prVec_smul, map_natCast] at h
      exact h
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s₁, hs₁, z₁, hz₁, e₁⟩ := hx
      obtain ⟨s₂, hs₂, z₂, hz₂, e₂⟩ := hy
      refine ⟨s₁ + s₂, add_mem hs₁ hs₂, z₁ + z₂, add_mem hz₁ hz₂, ?_⟩
      rw [e₁, e₂, smul_add]; abel
    | smul c x _ hx =>
      obtain ⟨s, hs, z, hz, e⟩ := hx
      refine ⟨c • s, Submodule.smul_mem _ c hs, c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [e, smul_add, Subring.smul_def, Subring.smul_def, Subring.smul_def, smul_smul, smul_smul,
        mul_comm]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameComponentLocalFrameStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeFrame_component_localFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (g k : ℕ) (Fr : AdFrame σ J (hat F L) g k) (v : HeightOneSpectrum (𝓞 F)), prV (E := E) v Fr.eps * prV (E := E) v Fr.eps = prV (E := E) v Fr.eps ∧ prV (E := E) v Fr.eps * sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) = 0 ∧ prV (E := E) v Fr.eps ∈ intV E v ∧ (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - prV (E := E) v Fr.eps - sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps)) • y = (g : E ⊗[F] v.adicCompletion F) • z) ∧ (∀ i, prVec v (Fr.b i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.bd i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.b i) = prV (E := E) v Fr.eps • prVec v (Fr.b i)) ∧ (∀ i, prVec v (Fr.bd i) = sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) • prVec v (Fr.bd i)) ∧ (∀ i j, ∃ t ∈ intV E v, hR σ J (v.adicCompletion F) (prVec v (Fr.bd i)) (prVec v (Fr.b j)) - (if i = j then prV (E := E) v Fr.eps else 0) = (g : E ⊗[F] v.adicCompletion F) * t) ∧ (∀ y ∈ loc v L, InModL (loc v L) g (Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))) y) := by
  first | exact @GlobalTheory.St.G.frame_component_local | exact GlobalTheory.St.G.frame_component_local | (intros; apply GlobalTheory.St.G.frame_component_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticePropertiesTransportByIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticePropertiesTransportByIsometry
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatTransport

variable {D : D7}

theorem mem_gmap_inv (g : GV D) (Λ : LV D) (x : (VS D).V) : x ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ↔ g x ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g x, h, by simp⟩

variable {T : D.host.E} {F0 G' : FlagG (VS D) D.R.rS T} {g : GV D}

theorem e_eq (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (a : Fin D.R.rS) : g (F0.e a) = G'.e a := by
  have h := hfr a.castSucc
  simpa [FlagG.fvec, Fin.snoc_castSucc] using h

theorem z_eq (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) : g F0.z = G'.z := by
  have h := hfr (Fin.last _)
  simpa [FlagG.fvec, Fin.snoc_last] using h

theorem map_X (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) :
    F0.X.map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = G'.X := by
  unfold FlagG.X
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext a
  exact e_eq hfr a

theorem mem_X (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) : v ∈ F0.X ↔ g v ∈ G'.X := by
  rw [← map_X hfr]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := g.injective hwv
    exact this ▸ hw

theorem mem_orth (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) :
    v ∈ orth (VS D) F0.X ↔ g v ∈ orth (VS D) G'.X := by
  have hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h y hy
    have hy' : g.symm y ∈ F0.X := by
      rw [mem_X hfr]
      simpa using hy
    have := h _ hy'
    rw [← hiso] at this
    simpa using this
  · intro h x hx
    rw [← hiso]
    exact h _ ((mem_X hfr x).1 hx)

theorem mem_XS (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) : v ∈ XS D F0 ↔ g v ∈ XS D G' := by
  have hmap : (XS D F0).map ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) = XS D G' := by
    unfold XS
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨a, x, hx, rfl⟩, rfl⟩
      refine ⟨a, x, hx, ?_⟩
      simp [e_eq hfr a]
    · rintro ⟨a, x, hx, rfl⟩
      refine ⟨x • F0.e a, ⟨a, x, hx, rfl⟩, ?_⟩
      simp [e_eq hfr a]
  rw [← hmap]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := g.injective hwv
    exact this ▸ hw

theorem mem_dual (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (Λ : LV D) (x : (VS D).V) :
    x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ↔ g x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
  have hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]
  constructor
  · intro h y hy
    have hy' : g.symm y ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ := by
      rw [mem_gmap_inv]
      simpa using hy
    have := h _ hy'
    rw [← hiso] at this
    simpa using this
  · intro h y hy
    rw [← hiso]
    exact h _ ((mem_gmap_inv g Λ y).1 hy)

theorem isLattice_inv (g : GV D) {Λ : LV D} (hL : Submodule.IsLattice D.host.E Λ) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  exact Submodule.IsLattice.of_fg D.host.E (hL.fg.map _)

theorem mem_Lsub (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (Λ : LV D)
    (v : (VS D).V) (hv : v ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0)) : g v ∈ Lsub Λ (lf D G') := by
  obtain ⟨hs, ho⟩ := hv
  refine ⟨?_, (mem_orth hg hfr v).1 ho⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hs
  obtain ⟨hyΛ, hyo⟩ := hy
  rw [map_add (f := _)]
  refine Submodule.add_mem_sup ⟨(mem_gmap_inv g Λ y).1 hyΛ, (mem_orth hg hfr y).1 hyo⟩ ?_
  exact (mem_X hfr w).1 hw

end GlobalTheory.RowLatTransport

namespace GlobalTheory.RowLatTransport

theorem rowLat_transport : ∀ (D : D7) (T : D.host.E) (F0 G' : FlagG (VS D) D.R.rS T) (g : GV D), g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, g (F0.fvec a) = G'.fvec a) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → G'.z ∈ Λ → XLam Λ (lf D G') = XS D G' → (∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) → Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 ∧ Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ F0.z ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∧ XLam (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) = XS D F0 ∧ (∀ c : D.host.E, c • F0.z ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) := by
  intro D T F0 G' g hg hfr Λ hL hU hz hX hprim
  have hL' := isLattice_inv g hL
  have hU' : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
    unfold Formalism.HermitianLatticesTheory.IsUnimodular
    ext x
    rw [mem_dual hg, mem_gmap_inv]
    have hU0 : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
    rw [hU0]
  refine ⟨Formalism.MainNotions.BridgeRowsGenus.unimodular_mem_genus Formalism.L2.SG.Pf.Cnt.local_unimodular_holds D.sp.cm (VS D) _ hL' hU',
    hL', hU', ?_, ?_, ?_⟩
  · rw [mem_gmap_inv, z_eq hfr]
    exact hz
  · ext v
    change v ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ⊓ toO (VS D) F0.X ↔ v ∈ XS D F0
    rw [mem_XS hfr, ← hX]
    change _ ↔ g v ∈ Λ ⊓ toO (VS D) G'.X
    simp only [Submodule.mem_inf, toO, Submodule.restrictScalars_mem]
    rw [mem_gmap_inv, mem_X hfr]
  · intro c hc
    apply hprim c
    have := mem_Lsub hg hfr Λ _ hc
    rw [map_smul, z_eq hfr] at this
    exact this

end GlobalTheory.RowLatTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticePropertiesTransportByIsometryStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLattice_properties_transport_by_isometry : ∀ (D : D7) (T : D.host.E) (F0 G' : FlagG (VS D) D.R.rS T) (g : GV D), g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, g (F0.fvec a) = G'.fvec a) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → G'.z ∈ Λ → XLam Λ (lf D G') = XS D G' → (∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) → Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 ∧ Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ F0.z ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∧ XLam (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) = XS D F0 ∧ (∀ c : D.host.E, c • F0.z ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) := by
  first | exact @GlobalTheory.RowLatTransport.rowLat_transport | exact GlobalTheory.RowLatTransport.rowLat_transport | (intros; apply GlobalTheory.RowLatTransport.rowLat_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientModelExists
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientModelExists
noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm
open Formalism.HermitianLatticeCounting.S6

section EmbGen
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}

def frPerp (F : FlagD H r) : Submodule K V where
  carrier := {v | ∀ a, H.B (F.e a) v = 0}
  add_mem' := by
    intro x y hx hy a
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add (f := _), hx a, hy a, add_zero]
  zero_mem' := by
    intro a
    simp
  smul_mem' := by
    intro c x hx a
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smulₛₗ, hx a, smul_zero]

theorem mem_frPerp (F : FlagD H r) (v : V) : v ∈ frPerp F ↔ ∀ a, H.B (F.e a) v = 0 := Iff.rfl

theorem B_right_nondeg (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (w : V) (h : ∀ v, H.B v w = 0) : w = 0 :=
  H.nondeg w (fun y => by rw [← H.herm y w, h y, star_zero])

theorem fr_indep (F : FlagD H r) : LinearIndependent K F.e := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hz : c (Fin.last r) = 0 := by
    have h : H.B (∑ a, c a • F.e a) (F.e (Fin.last r)) = 0 := by rw [hc, map_zero, LinearMap.zero_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [F.zperp, F.zz, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add] at h
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd (neg_eq_zero.1 h) F.hT
  have hc' : ∑ a : Fin r, c a.castSucc • F.e a.castSucc = 0 := by
    rw [Fin.sum_univ_castSucc, hz, zero_smul, add_zero] at hc
    exact hc
  have hcs := Fintype.linearIndependent_iff.1 F.indep (fun a => c a.castSucc) hc'
  intro i
  induction i using Fin.lastCases with
  | last => exact hz
  | cast a => exact hcs a

def frMap (F : FlagD H r) : V →ₗ[K] (Fin (r + 1) → K) :=
  LinearMap.pi fun a => H.B.flip (F.e a)

theorem frMap_apply (F : FlagD H r) (v : V) (a : Fin (r + 1)) : frMap F v a = H.B v (F.e a) := rfl

theorem ker_frMap (F : FlagD H r) : LinearMap.ker (frMap F) = frPerp F := by
  ext v
  rw [LinearMap.mem_ker, mem_frPerp, funext_iff]
  refine forall_congr' fun a => ?_
  rw [frMap_apply, Pi.zero_apply, ← H.herm (F.e a) v]
  exact ⟨fun h => by rw [← star_star (H.B (F.e a) v), h, star_zero], fun h => by rw [h, star_zero]⟩

theorem range_frMap (F : FlagD H r) : LinearMap.range (frMap F) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  set c : Fin (r + 1) → K := fun a => f (fun j => if a = j then 1 else 0) with hcdef
  have hfx : ∀ x, f x = ∑ a, x a * c a := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, hcdef]
  have hv : ∀ v, H.B v (∑ a, star (c a) • F.e a) = 0 := by
    intro v
    have h1 : f (frMap F v) = 0 := by
      have : f (frMap F v) ∈ Submodule.map f (LinearMap.range (frMap F)) :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self _ v)
      rw [hf] at this
      exact (Submodule.mem_bot K).1 this
    rw [hfx] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul]
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [frMap_apply, mul_comm]
  have hw := B_right_nondeg H _ hv
  have hc := Fintype.linearIndependent_iff.1 (fr_indep F) _ hw
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [hfx]
  simp only [LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : c a = 0 := by simpa using hc a
  rw [this, mul_zero]

theorem finrank_frPerp [FiniteDimensional K V] (F : FlagD H r) :
    Module.finrank K (frPerp F) + (r + 1) = Module.finrank K V := by
  have h := LinearMap.finrank_range_add_finrank_ker (frMap F)
  rw [range_frMap, ker_frMap, finrank_top, Module.finrank_fin_fun] at h
  omega

theorem X_le_frPerp (F : FlagD H r) : F.X ≤ frPerp F := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, -, rfl⟩ a
  induction a using Fin.lastCases with
  | last => rw [← H.herm (F.e b.castSucc) (F.e (Fin.last r)), F.zperp b, star_zero]
  | cast a => exact F.iso a b

theorem finrank_X (F : FlagD H r) : Module.finrank K F.X = r := by
  have h : F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
    show Submodule.span K _ = _
    congr 1
    ext x
    simp
  rw [h, finrank_span_eq_card F.indep, Fintype.card_fin]

def resH (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (W : Submodule K V) (hnd : ∀ x : W, (∀ y : W, H.B x y = 0) → x = 0) :
    Formalism.HermitianLatticeCounting.S6.HermSpace K W where
  B := (H.B.comp W.subtype).compl₂ W.subtype
  herm x y := H.herm x y
  nondeg x h := hnd x h

theorem exists_emb [FiniteDimensional K V] (F : FlagD H r) (τ₀ : K →+* ℂ) (hP : ∀ σ : K →+* ℂ, F.PosDefAt σ) :
    ∃ (W : Submodule K V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W), GlobalTheory.DegAsm.IsEmb F HW W.subtype ∧
      Module.finrank K W + (2 * r + 1) = Module.finrank K V ∧ GlobalTheory.Mass.PD HW.B.flip := by
  obtain ⟨Y, hY⟩ := Submodule.exists_isCompl F.X
  set W := Y ⊓ frPerp F with hW
  have hsup : F.X ⊔ W = frPerp F := by
    rw [hW, ← sup_inf_assoc_of_le Y (X_le_frPerp F), hY.sup_eq_top, top_inf_eq]
  have hinf : F.X ⊓ W = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    exact hY.inf_eq_bot ▸ ⟨hx.1, hx.2.1⟩
  have hpos : ∀ (σ : K →+* ℂ) (x : W), x ≠ 0 → 0 < (σ (H.B x x)).re := by
    intro σ x hx
    refine hP σ x ((mem_frPerp F _).1 x.2.2) fun hxX => hx ?_
    have : (x : V) ∈ F.X ⊓ W := ⟨hxX, x.2⟩
    rw [hinf] at this
    exact Subtype.ext ((Submodule.mem_bot K).1 this)
  have hnd : ∀ x : W, (∀ y : W, H.B x y = 0) → x = 0 := by
    intro x h
    by_contra hx
    have := hpos τ₀ x hx
    rw [h x, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨W, resH H W hnd, ⟨fun x y => rfl, fun v => ?_⟩, ?_, fun σ x hx => hpos σ x hx⟩
  · rw [← mem_frPerp, Submodule.range_subtype, sup_comm, hsup]
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq F.X W
    rw [hsup, hinf, finrank_bot, finrank_X] at h1
    have h2 := finrank_frPerp F
    omega

end EmbGen

theorem embC : EmbC := by
  intro D large₂ X u _
  have hpos : ∀ σ : D.host.E →+* ℂ, (F0 X u).PosDefAt σ := fun σ =>
    Formalism.MainNotions.KappaEndpoints.nf_pos (lf D (X.Fu u)) (tu_ne D u)
      (p_posX D (Tu D u) (D.mem u).A.T_prime.pos _) σ
  let τ₀ : D.host.E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := D.host.E)).toRingHom
  obtain ⟨W, HW, h1, h2, h3⟩ := exists_emb (F0 X u) τ₀ hpos
  refine ⟨W, HW, h1, ?_, h3⟩
  have hV : Module.finrank D.host.E (VS D).V = D.R.rankY 0 := by
    rw [(VS D).rank_eq]
    exact D.sp.Y_rank 0 (Nat.zero_le _)
  have hR : D.R.rankY 0 = 2 * D.R.rS + D.R.k + 1 := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r, zero_mul, add_zero]
    omega
  rw [hV, hR] at h2
  omega

end GlobalTheory.TypeAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientModelExistsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_quotient_model_exists : GlobalTheory.TypeAsm.EmbC := by
  first | exact @GlobalTheory.TypeAsm.embC | exact GlobalTheory.TypeAsm.embC | (intros; apply GlobalTheory.TypeAsm.embC <;> assumption)
end
end
