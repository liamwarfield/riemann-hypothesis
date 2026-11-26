module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.InertPlaceConj

open GlobalTheory.SelfDualGenus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isInertAt_of_not_split (w : HeightOneSpectrum (𝓞 E))
    (hu : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) (hs : ¬ IsSplitAt w) :
    Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w := by
  classical
  haveI := w.isPrime
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have hva : v.asIdeal = w.asIdeal.under (𝓞 (maximalRealSubfield E)) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  unfold Formalism.UG.IsInertAt
  rw [hva]
  have hle : (w.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ w.asIdeal := Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 (maximalRealSubfield E))
        (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal).1 hu).2
  have h2 : ¬ (w.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ w.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  set I := Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
    (w.asIdeal.under (𝓞 (maximalRealSubfield E))) with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact v.ne_bot
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = w.asIdeal := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    have hp0 : p ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))
    let u : HeightOneSpectrum (𝓞 E) := ⟨p, hpp, hp0⟩
    have hu' : u.under (𝓞 (maximalRealSubfield E)) = v := by
      ext1
      exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top)
        (Ideal.map_le_iff_le_comap.1 hpl)).symm
    by_contra hne
    exact hs ⟨u, fun h => hne (congrArg HeightOneSpectrum.asIdeal h), hu'⟩
  obtain ⟨n, hn⟩ : ∃ n, I = w.asIdeal ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  rcases n with _ | _ | n
  · exfalso
    rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact w.isPrime.ne_top hle
  · simpa using hn
  · exact absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2

theorem exists_sub_conj_notMem_of_inert (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w) :
    ∃ x : 𝓞 E, x - IsCMField.ringOfIntegersComplexConj E x ∉ w.asIdeal := by
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal := h
  have := v.isPrime
  have := w.isPrime
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[maximalRealSubfield E] E) v.asIdeal w.asIdeal
  have hsq : ¬ Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ w.asIdeal ^ 2 := by
    rw [h']
    exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (E ≃ₐ[maximalRealSubfield E] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff (le_of_eq h')).1 hsq)] at hcard
  by_contra hn
  push_neg at hn
  have hs : IsCMField.complexConj E ∈ w.asIdeal.inertia (E ≃ₐ[maximalRealSubfield E] E) :=
    AddSubgroup.mem_inertia.2 fun x => by
      have := w.asIdeal.neg_mem (hn x)
      rw [neg_sub] at this
      exact this
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact IsCMField.complexConj_ne_one E hs

theorem exists_isUnramInv_of_inert (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w) :
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧
      IsUnramInv ϖ s (Ideal.absNorm (w.under (𝓞 (maximalRealSubfield E))).asIdeal) := by
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal := h
  have hc : Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w w := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = IsCMField.ringOfIntegersComplexConj E x := RingOfIntegers.ext hxy
    rw [e]
    refine ⟨GlobalTheory.InertConj.conj_mem_of_inert h, fun hx => ?_⟩
    have h2 := GlobalTheory.InertConj.conj_mem_of_inert h hx
    have e2 : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E x) = x := by
      ext; simp
    rwa [e2] at h2
  obtain ⟨σ, σ1, σ2, σ3⟩ := UnramCompletion.exists_ringEquiv w _ hc
  have σ2' : ∀ x : E, σ (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x) := σ2
  obtain ⟨s, hs, hs2⟩ : ∃ s ∈ v.asIdeal,
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∉ w.asIdeal ^ 2 := by
    by_contra hn
    push_neg at hn
    have h1 : w.asIdeal ≤ w.asIdeal ^ 2 := by
      conv_lhs => rw [← h']
      exact Ideal.map_le_iff_le_comap.2 hn
    exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge h1
  have hs1 : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∈ w.asIdeal :=
    h' ▸ Ideal.mem_map_of_mem _ hs
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    refine congrFun (UnramCompletion.ringHom_ext_of_continuous w (f := fun x => σ (σ x))
      (σ1.comp σ1) continuous_id fun k => ?_) x
    simp [σ2']
  have hres : ∃ x, Valued.v x ≤ 1 ∧ Valued.v ((σ : w.adicCompletion E →+* w.adicCompletion E) x - x) = 1 := by
    obtain ⟨x, hx⟩ := exists_sub_conj_notMem_of_inert w h
    refine ⟨algebraMap E _ (x : E), ?_, ?_⟩
    · rw [hval]; exact w.valuation_le_one x
    · change Valued.v (σ _ - _) = 1
      rw [Valuation.map_sub_swap, σ2', ← map_sub]
      exact (hval (x - IsCMField.ringOfIntegersComplexConj E x)).trans
        ((HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hx)
  have hfix : (σ : w.adicCompletion E →+* w.adicCompletion E)
      (algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E)) =
      algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) := by
    change σ _ = _
    rw [σ2']
    congr 1
    exact IsCMField.complexConj_apply_eq_self E (s : maximalRealSubfield E)
  have hunif : IsUnifV E w (algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E)) := by
    unfold IsUnifV
    rw [hval, HeightOneSpectrum.valuation_of_algebraMap]
    exact UnramCompletion.intValuation_eq_of_notMem_sq w hs1 hs2
  refine ⟨σ, _, σ2', hinv, σ3, hfix, hunif, ?_, ?_, ?_⟩
  · obtain ⟨x, hx1, hx2⟩ := hres
    exact ⟨x, hx1, hx2⟩
  · have a : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have b : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  · have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← h', Ideal.absNorm_algebraMap,
        ← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
        (𝓞 E) E).symm
    rw [← hN]
    exact Formalism.UG.P.tjcosets_card_residue w

theorem exists_conj_isUnramInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w →
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q := by
  intro E _ _ _ w hu hs
  obtain ⟨s, ϖ, h1, h2⟩ := exists_isUnramInv_of_inert w (isInertAt_of_not_split w hu hs)
  exact ⟨s, ϖ, _, h1, h2⟩

end GlobalTheory.InertPlaceConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformiseStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_nonsplit_exists_conj_involution_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w → ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q := by
  first | exact @GlobalTheory.InertPlaceConj.exists_conj_isUnramInv | exact GlobalTheory.InertPlaceConj.exists_conj_isUnramInv | (intros; apply GlobalTheory.InertPlaceConj.exists_conj_isUnramInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.IntByParts

theorem setIntegral_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (a : G) :
    ∫ g in 𝓕, Φ (g * a) ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hm : MeasurePreserving (fun g : G => g * a) μ μ := measurePreserving_mul_right μ a
  have h' : IsFundamentalDomain Γ ((fun g : G => g * a) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc _ _ _
  rw [← hm.setIntegral_preimage_emb (measurableEmbedding_mulRight a) Φ 𝓕]
  exact h.setIntegral_eq h' (f := fun g => Φ (g * a)) fun γ g => by
    change Φ ((γ : G) * g * a) = _
    rw [mul_assoc, hΦ _ γ.2]

theorem setIntegral_deriv_eq_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) {Φ Φ' : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ) (hc' : Continuous Φ')
    {B B' : ℝ} (hB : ∀ g, ‖Φ g‖ ≤ B) (hB' : ∀ g, ‖Φ' g‖ ≤ B') {a : ℝ → G} (h0 : a 0 = 1)
    (hd : ∀ g t, HasDerivAt (fun s : ℝ => Φ (g * a s)) (Φ' (g * a t)) t) : ∫ g in 𝓕, Φ' g ∂μ = 0 := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ) (x₀ := 0)
    (F := fun t g => Φ (g * a t)) (F' := fun t g => Φ' (g * a t)) (s := Set.univ) (bound := fun _ => B')
    Filter.univ_mem
    (.of_forall fun t => (hc.comp (continuous_mul_const _)).measurable.aestronglyMeasurable)
    (Integrable.of_bound (hc.comp (continuous_mul_const _)).measurable.aestronglyMeasurable B
      (.of_forall fun g => hB _))
    (hc'.comp (continuous_mul_const _)).measurable.aestronglyMeasurable
    (.of_forall fun g t _ => hB' _) (integrable_const _) (.of_forall fun g t _ => hd g t)
  have h2 := key.2
  simp only [setIntegral_mul_right Γ μ h hΦ, h0, mul_one] at h2
  exact h2.unique (hasDerivAt_const _ _)

variable {D : D7} {θ : InfF D} {V : HSp D}

theorem mul_cont_bounded {φ F : GA D V → ℂ} (hφ : IsMod θ V φ) (hF : F ∈ Decay θ V) :
    Continuous (fun g => φ g * F g) ∧ ∃ B : ℝ, ∀ g, ‖φ g * F g‖ ≤ B := by
  obtain ⟨c1, N, C, hC⟩ := hφ.2.2 [] (by simp)
  obtain ⟨c2, hr⟩ := hF.2.2 [] (by simp)
  obtain ⟨B, hB⟩ := IsRapidDecay.mul_bounded (φ := F) (ψ := φ) hr hφ.2.1 hC
  exact ⟨Continuous.mul c1 c2, B, fun g => by rw [norm_mul]; exact hB g⟩

theorem integral_Rder_mul : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ F, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ ∧ ∫ g in 𝓕, Rder θ V τ X φ g * F g ∂μ = -∫ g in 𝓕, φ g * Rder θ V τ X F g ∂μ := by
  intro D θ hθ V μ 𝓕 hq τ X hX φ F hφ hF
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hfin := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 hq).2
  haveI := hq.1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hq.1).1
  have int : ∀ {φ F : GA D V → ℂ}, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ := by
    intro φ F hφ hF
    obtain ⟨c, B, hB⟩ := mul_cont_bounded hφ hF
    exact Measure.integrableOn_of_bounded (M := B) hfin c.measurable.aestronglyMeasurable (.of_forall hB)
  refine ⟨int hφ hF, ?_⟩
  obtain ⟨c0, B0, hB0⟩ := mul_cont_bounded hφ hF
  obtain ⟨c1, B1, hB1⟩ := mul_cont_bounded (hφ.rder hX) hF
  obtain ⟨c2, B2, hB2⟩ := mul_cont_bounded hφ (Rder_mem_Decay hF hX)
  have key := setIntegral_deriv_eq_zero (GQ V) μ hq.2 hfin (Φ := fun g => φ g * F g)
    (Φ' := fun g => Rder θ V τ X φ g * F g + φ g * Rder θ V τ X F g)
    (fun γ hγ g => by simp only [hφ.2.1 γ hγ, hF.2.1 γ hγ]) c0 (c1.add c2) hB0
    (fun g => (norm_add_le _ _).trans (add_le_add (hB1 g) (hB2 g))) (oneP_zero (V := V) (τ := τ) (X := X) hθ)
    fun g t => (hasDerivAt_oneP hθ hX (hasDerivAt_Rder hφ.1 hX) g t).mul
      (hasDerivAt_oneP hθ hX (hasDerivAt_Rder hF.1 hX) g t)
  rw [integral_add (int (hφ.rder hX) hF) (int hφ (Rder_mem_Decay hF hX))] at key
  exact eq_neg_of_add_eq_zero_left key

end GlobalTheory.Mem.IntByParts

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotientStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integration_by_parts_rightDerivative_adelicQuotient : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ F, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ ∧ ∫ g in 𝓕, Rder θ V τ X φ g * F g ∂μ = -∫ g in 𝓕, φ g * Rder θ V τ X F g ∂μ := by
  first | exact @GlobalTheory.Mem.IntByParts.integral_Rder_mul | exact GlobalTheory.Mem.IntByParts.integral_Rder_mul | (intros; apply GlobalTheory.Mem.IntByParts.integral_Rder_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRank
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfBoundedKorbitDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfBoundedKorbitDimension
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.admitted

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem isKFin_of_mem_closure (hσ : IsURepOn (UJset ε) σ) {U : Set H} {M : ℕ}
    (hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S)
    {u : H} (hu : u ∈ closure U) : IsKFin ε σ u := by
  let t : Set H := Set.range fun k : KG ε => σ (toMK k) u
  obtain ⟨b, hbt, hsp, hli⟩ := exists_linearIndependent ℂ t
  have hfin : b.Finite := by
    by_contra hinf
    haveI : Infinite b := Set.infinite_coe_iff.2 hinf
    let e : Fin (M + 1) ↪ b := Fin.valEmbedding.trans (Infinite.natEmbedding b)
    choose k hk using fun i => hbt (e i).2
    have hc : Continuous fun w : H => fun i : Fin (M + 1) => σ (toMK (k i)) w :=
      continuous_pi fun i => (σ _).continuous
    have ho := (isOpen_setOf_linearIndependent (𝕜 := ℂ) (E := H) (ι := Fin (M + 1))).preimage hc
    have hu' : LinearIndependent ℂ fun i : Fin (M + 1) => σ (toMK (k i)) u := by
      have := hli.comp e e.injective
      rwa [show (Subtype.val ∘ e : Fin (M + 1) → H) = _ from funext fun i => (hk i).symm] at this
    obtain ⟨w, hw, hwU⟩ := mem_closure_iff.1 hu _ ho hu'
    obtain ⟨S, hS, hM, hwS, hK⟩ := hU w hwU
    have h1 : LinearIndependent ℂ fun i : Fin (M + 1) =>
        (⟨σ (toMK (k i)) w, hK _ (toMK_mem_K _) w hwS⟩ : S) :=
      LinearIndependent.of_comp S.subtype hw
    have h2 := h1.fintype_card_le_finrank
    rw [Fintype.card_fin] at h2
    omega
  refine ⟨Submodule.span ℂ t, hsp ▸ FiniteDimensional.span_of_finite ℂ hfin, Submodule.subset_span ⟨1, ?_⟩,
    fun g hg v hv => ?_⟩
  · exact sigma_one hσ u
  · refine (Submodule.map_span_le (σ g : H →ₗ[ℂ] H) _ _).2 ?_ ⟨v, hv, rfl⟩
    rintro _ ⟨k, rfl⟩
    obtain ⟨g', rfl⟩ : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
    exact Submodule.subset_span ⟨g' * k, sigma_mul hσ (K_le_UJ hg) (K_le_UJ (toMK_mem_K k)) u⟩

variable [CompleteSpace H]

theorem exists_word_clm (h : Std ε σ) (W : Submodule ℂ H) [CompleteSpace W] (hW : ∀ w ∈ W, Sm ε σ w)
    {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) : ∃ A : W →L[ℂ] H, ∀ w : W, A w = Dw σ l w := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) h.1 l hl
  let A : W →ₗ[ℂ] H := (smooth (Jm ε) σ).subtype ∘ₗ L ∘ₗ Submodule.inclusion hW
  have hA : ∀ x : W, A x = Dw σ l x := fun x => hL _
  refine ⟨⟨A, A.continuous_of_seq_closed_graph fun s x z hs hz =>
    h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_⟩, hA⟩
  have h1 : Tendsto (fun j => ⟪y, A (s j)⟫_ℂ) atTop (𝓝 ⟪y, z⟫_ℂ) := tendsto_const_nhds.inner hz
  simp only [hA, fun x : W => inner_Dw h.1 hl hy (hW _ x.2)] at h1 ⊢
  exact tendsto_nhds_unique h1
    (tendsto_const_nhds.mul (tendsto_const_nhds.inner ((continuous_subtype_val.tendsto x).comp hs)))

theorem finiteDimensional_of_smooth (h : Std ε σ) (W : Submodule ℂ H) [CompleteSpace W]
    (hW : ∀ w ∈ W, Sm ε σ w) : FiniteDimensional ℂ W := by
  obtain ⟨S, C, hS, hC, hts⟩ := GlobalTheory.T.sobolev_embedding_discrete_series_hilbertSchmidt n ε H σ h
  choose A hA using fun l : {l // l ∈ S} => exists_word_clm h W hW (hS l.1 l.2)
  haveI : Finite {l // l ∈ S} := (List.finite_toSet S).to_subtype
  obtain ⟨B, hB⟩ := (Set.finite_range fun l => ‖A l‖ ^ 2).bddAbove
  have hB' : ∀ l, ‖A l‖ ^ 2 ≤ |B| := fun l => (hB ⟨l, rfl⟩).trans (le_abs_self B)
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ W
  have hfin : Finite w := by
    by_contra hinf
    haveI : Infinite w := not_finite_iff_infinite.1 hinf
    obtain ⟨m, hm⟩ := exists_nat_gt (C * |B|)
    let e : Fin m ↪ w := Fin.valEmbedding.trans (Infinite.natEmbedding w)
    have ho : Orthonormal ℂ fun j => b (e j) := b.orthonormal.comp e e.injective
    have key := hts (Fin m) (fun j => b (e j)) (fun j => b (e j)) |B| (abs_nonneg B) (fun j => hW _ (b (e j)).2)
      (fun l hl z => by
        have e1 : ∑ j, z j • Dw σ l (b (e j) : H) = A ⟨l, hl⟩ (∑ j, z j • b (e j)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hA]
        have e2 : ‖∑ j, z j • b (e j)‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := by
          have := ho.inner_sum z z Finset.univ
          rw [inner_self_eq_norm_sq_to_K] at this
          simp only [RCLike.conj_mul] at this
          exact_mod_cast this
        rw [e1, ← e2]
        calc _ ≤ (‖A ⟨l, hl⟩‖ * ‖∑ j, z j • b (e j)‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ((A _).le_opNorm _) 2
          _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hB' _) (sq_nonneg _))
    have hn : ∀ j, ‖(b (e j) : H)‖ = 1 := fun j => ho.1 j
    simp only [inner_self_eq_norm_sq_to_K, hn] at key
    simp at key
    have h0 : 0 ≤ C * |B| := mul_nonneg hC (abs_nonneg B)
    nlinarith
  haveI := Fintype.ofFinite w
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

end GlobalTheory.TypeSum.admitted

namespace GlobalTheory.TypeSum

theorem finiteDimensional_of_bounded_orbits : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (U : Submodule ℂ H) (M : ℕ),
    (∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S) →
      FiniteDimensional ℂ U := by
  intro n ε H _ _ _ σ h U M hU
  haveI : CompleteSpace U.topologicalClosure := U.isClosed_topologicalClosure.completeSpace_coe
  haveI := admitted.finiteDimensional_of_smooth h U.topologicalClosure fun w hw =>
    h.2.2.1 w (admitted.isKFin_of_mem_closure h.1 (U := U) hU hw)
  exact Submodule.finiteDimensional_of_le U.le_topologicalClosure

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfBoundedKorbitDimensionStatement
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (U : Submodule ℂ H) (M : ℕ), (∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S) → FiniteDimensional ℂ U := by
  first | exact @GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits | exact GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits | (intros; apply GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRank
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KAvgRank

open GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sigma_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (k₀ : KG ε) (w : H) :
    σ (toMK k₀) (kAvg ε σ e w) = kAvg ε σ (fun k => e (k₀⁻¹ * k)) w := by
  rw [kAvg, ← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ he w), kAvg,
    ← integral_mul_left_eq_self (fun k => e (k₀⁻¹ * k) • σ (toMK k) w) k₀]
  simp only [map_smul, inv_mul_cancel_left, sigma_K_mul hσ]

theorem exists_stable (hσ : IsURepOn (UJset ε) σ) {F : Submodule ℂ (KG ε → ℂ)} [FiniteDimensional ℂ F]
    (hc : ∀ φ ∈ F, Continuous φ) (hl : ∀ φ ∈ F, ∀ k₀ : KG ε, (fun k => φ (k₀ * k)) ∈ F) {e : KG ε → ℂ} (he : e ∈ F)
    (w : H) : ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      kAvg ε σ e w ∈ S ∧ IsKStableOn ε σ S := by
  let L : F →ₗ[ℂ] H :=
    { toFun := fun φ => kAvg ε σ φ w
      map_add' := fun x y => by
        simp only [kAvg, Submodule.coe_add, Pi.add_apply, add_smul]
        exact integral_add (integrable_avg hσ (hc _ x.2) w) (integrable_avg hσ (hc _ y.2) w)
      map_smul' := fun c x => by
        simp only [kAvg, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_assoc]
        exact integral_smul _ _ }
  refine ⟨LinearMap.range L, inferInstance, LinearMap.finrank_range_le L, ⟨⟨e, he⟩, rfl⟩, ?_⟩
  rintro k hk _ ⟨φ, rfl⟩
  obtain ⟨k₀, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hk
  exact ⟨⟨_, hl φ φ.2 k₀⁻¹⟩, (sigma_kAvg hσ (hc _ φ.2) k₀ w).symm⟩

theorem adjoint_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {Q : H →L[ℂ] H}
    (hQ : ∀ w, Q w = kAvg ε σ e w) {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H}
    (hz : z ∈ S) : ContinuousLinearMap.adjoint Q z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal']
  intro u hu
  rw [ContinuousLinearMap.adjoint_inner_left, hQ, inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪z, σ (toMK k) u⟫_ℂ = 0 := fun k => by
    have h := inner_K hσ k⁻¹ u z
    rw [inv_inv] at h
    rw [← h]
    exact Submodule.inner_right_of_mem_orthogonal (hK _ (toMK_mem_K _) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KAvgRank

namespace GlobalTheory.TypeSum

theorem kAvg_finite_rank : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), Orthonormal ℂ a ∧ (∀ j, IsKFin ε σ (a j)) ∧ (∀ j, IsKFin ε σ (c j)) ∧ ∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j := by
  intro n ε H _ _ _ σ h e ⟨F, hF, heF, hc, ht⟩
  have hσ := h.1
  obtain ⟨Q, hQ⟩ := KCoef.exists_clm_kAvg hσ (hc e heF)
  let U : Submodule ℂ H := LinearMap.range (Q : H →ₗ[ℂ] H)
  have hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      u ∈ S ∧ IsKStableOn ε σ S := by
    rintro _ ⟨w, rfl⟩
    have := KAvgRank.exists_stable hσ hc (fun φ hφ k₀ => (ht φ hφ k₀).1) heF w
    rwa [← hQ] at this
  haveI : FiniteDimensional ℂ U := GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension n ε H σ h U _ hU
  let b := stdOrthonormalBasis ℂ U
  refine ⟨_, fun j => (b j : H), fun j => ContinuousLinearMap.adjoint Q (b j), ?_, fun j => ?_, fun j => ?_,
    fun w => ?_⟩
  · exact b.orthonormal.comp_linearIsometry U.subtypeₗᵢ
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, h2, h3⟩
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, KAvgRank.adjoint_mem hσ (hc e heF) hQ h3 h2, h3⟩
  · have := congrArg Subtype.val (b.sum_repr' ⟨Q w, ⟨w, rfl⟩⟩)
    rw [← hQ]
    simp only [ContinuousLinearMap.adjoint_inner_left]
    simpa using this.symm

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRankStatement
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactAverage_kFinite_finiteRank : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), Orthonormal ℂ a ∧ (∀ j, IsKFin ε σ (a j)) ∧ (∀ j, IsKFin ε σ (c j)) ∧ ∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j := by
  first | exact @GlobalTheory.TypeSum.kAvg_finite_rank | exact GlobalTheory.TypeSum.kAvg_finite_rank | (intros; apply GlobalTheory.TypeSum.kAvg_finite_rank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubst
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubst
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockBasis

section Mat

variable {m n : ℕ}

theorem unitMap_mul (B u : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j =
      ∑ a, ∑ b, (k a i * u⁻¹ j b) • Formalism.IndefR.Datum.unitMap B B' a b := by
  have e : k * Matrix.single i j (1 : ℂ) * u⁻¹ = ∑ a, ∑ b, (k a i * u⁻¹ j b) • Matrix.single a b (1 : ℂ) := by
    rw [Matrix.matrix_eq_sum_single (k * Matrix.single i j (1 : ℂ) * u⁻¹)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc]
    · simp
  unfold Formalism.IndefR.Datum.unitMap
  rw [Matrix.mul_inv_rev]
  calc B' * k * Matrix.single i j (1 : ℂ) * (u⁻¹ * B⁻¹) = B' * (k * Matrix.single i j (1 : ℂ) * u⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [e]
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]


open scoped ComplexOrder in
theorem isCartanInv_one {G B : Matrix (Fin n) (Fin n) ℂ} (hB : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * 1 * B⁻¹ := by
    rw [← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  refine ⟨Matrix.one_mul _, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_mul_same Matrix.PosDef.one ?_
  exact Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu))

end Mat

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (s : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
include hψ hθ hf

theorem aPlus_add_dir (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (z + z') f =
      Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f + Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z' f := by
  have e : cplxO 1 s (z + z') = cplxO 1 s z + cplxO 1 s z' := by
    simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
  simp only [GlobalTheory.FockSubst.aPlus_eq, e, fun z => (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ z).2.2.1]
  module

theorem dRho_smul_dir (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.dRho (heisO ψ S T) θ τ (c • z) f =
      (c.re : ℂ) • Datum.dRho (heisO ψ S T) θ τ z f + (c.im : ℂ) • Datum.dRho (heisO ψ S T) θ τ (Complex.I • z) f := by
  have e : c • z = (c.re : ℂ) • z + (c.im : ℂ) • (Complex.I • z) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [e, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.1, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.2.1,
    (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.2.1]

theorem aPlus_smul_dir (e : Bool) (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (hz : cplxO 1 s z = (Complex.I * if e then 1 else -1) • z) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (c • z) f =
      (if e then c else star c) • Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f := by
  have e1 : cplxO 1 s (c • z) = c • cplxO 1 s z := by
    simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_comm c]
  simp only [GlobalTheory.FockSubst.aPlus_eq]
  rw [e1, hz, smul_smul, dRho_smul_dir hψ hθ τ hf c, dRho_smul_dir hψ hθ τ hf (c * _),
    dRho_smul_dir hψ hθ τ hf (Complex.I * _)]
  generalize ((fockScale D τ : ℝ) : ℂ)⁻¹ = r
  cases e
  · match_scalars <;> apply Complex.ext <;> simp <;> ring
  · match_scalars <;> apply Complex.ext <;> simp <;> ring

theorem aPlus_sum_dir {ι : Type} (t : Finset ι) (z : ι → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (∑ i ∈ t, z i) f =
      ∑ i ∈ t, Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (z i) f := by
  induction t using Finset.induction_on with
  | empty =>
    have h := aPlus_add_dir hψ hθ τ s hf 0 0
    rw [add_zero] at h
    rw [Finset.sum_empty, Finset.sum_empty]
    exact left_eq_add.1 h
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, aPlus_add_dir hψ hθ τ s hf, ih]

theorem aPlus_unitMap_mul {ε : Fin T.rank → Bool} {B' k : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (ht : s * B' = B' * diagonal fun a => if ε a then (1 : ℂ) else -1) (hk : k ∈ Formalism.REAL.Kset ε)
    (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) {u : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) (i : Fin T.rank) (j : Fin S.rank) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j) f =
      ∑ a, ∑ b, (if ε i = true then k a i * u⁻¹ j b else k⁻¹ i a * u b j) •
        Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (Formalism.IndefR.Datum.unitMap B B' a b) f := by
  rw [unitMap_mul, aPlus_sum_dir hψ hθ τ _ hf]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [aPlus_sum_dir hψ hθ τ _ hf]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [aPlus_smul_dir hψ hθ τ _ hf (ε a) _ _ (GlobalTheory.FockIndep.cplxO_unitMap ht a b)]
  refine congrArg (· • _) ?_
  have hk1 : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hk.1)
  have hu1 : u⁻¹ = uᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hu)
  have hc := congrFun (congrFun hk.2 a) i
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  rw [hk1, hu1, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, star_mul', star_star]
  by_cases h : ε a = ε i
  · rw [h]
  · have h0 : k a i = 0 := by
      cases h1 : ε a <;> cases h2 : ε i <;> simp only [h1, h2, not_true, if_true, Bool.false_eq_true, if_false] at h hc
      · linear_combination hc / 2
      · linear_combination -hc / 2
    simp [h0]

omit hψ hθ hf

section Generic

variable {ι κ μ X : Type} [Fintype κ] [Fintype μ] {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_subst {g : X → ℂ} (c : ι → κ → μ → ℂ) (e : ι → κ → μ → ι)
    (hm : ∀ Q, P (pureTensorL A g Q))
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (hA : ∀ v h, P h → A' v h = ∑ a, ∑ b, c v a b • A (e v a b) h) (Q : MvPolynomial ι ℂ) :
    pureTensorL A' g Q = pureTensorL A g
      (MvPolynomial.aeval (fun v => ∑ a, ∑ b, MvPolynomial.C (c v a b) * MvPolynomial.X (e v a b)) Q) := by
  have hC : ∀ (A : ι → (X → ℂ) → (X → ℂ)) a, pureTensorL A g (MvPolynomial.C a) = a • g := fun A a => by
    rw [← mul_one (MvPolynomial.C a), MvPolynomial.C_mul', map_smul, GlobalTheory.FockIndep.pure_one]
  induction Q using MvPolynomial.induction_on with
  | C a => rw [hC, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, hC]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, hX', hp, map_mul, MvPolynomial.aeval_X, hA _ _ (hm _)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, map_sum, mul_assoc]
    simp only [MvPolynomial.C_mul', map_smul, smul_mul_assoc, hX]

end Generic

theorem pureTensorO_basis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (k : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∀ f, IsThetaFunO ψ S T f → ∀ P : PolF D T.rank S.rank, pureTensorO ψ θ S T (fun _ => 1) (cart M) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fsub M.ε k u P) := by
  intro D ψ θ S T Sp M BS hψ hθ hB k u hk hu f hf P
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hS := fun τ => isCartanInv_one (hB τ)
  have hfr := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have ht : ∀ τ, cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (hfr τ)]
    rfl
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ B B' v g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B' v g) :=
    fun _ _ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ B B' v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B') f Q) := fun B B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm (hth B B') ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hA : ∀ v g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) v g =
      ∑ a, ∑ b, (if M.ε v.1 v.2.1 = true then k v.1 a v.2.1 * (u v.1)⁻¹ v.2.2 b
        else (k v.1)⁻¹ v.2.1 a * u v.1 b v.2.2) •
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (onb M) (v.1, a, b) g := fun v g hg => by
    unfold aPlusAll
    exact aPlus_unitMap_mul hψ hθ v.1 _ hg (ht v.1) (hk v.1) _ (hu v.1) v.2.1 v.2.2
  have key := pure_subst (P := IsThetaFunO ψ S T) _ _
    (GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm (hth _ _) hf) (hX _ _) (hX _ _) hA P
  unfold pureTensorO fsub
  exact key

end GlobalTheory.FockBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubstStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_change_orthonormalBases_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (k : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∀ f, IsThetaFunO ψ S T f → ∀ P : PolF D T.rank S.rank, pureTensorO ψ θ S T (fun _ => 1) (cart M) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fsub M.ε k u P) := by
  first | exact @GlobalTheory.FockBasis.pureTensorO_basis | exact GlobalTheory.FockBasis.pureTensorO_basis | (intros; apply GlobalTheory.FockBasis.pureTensorO_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesField
noncomputable section

namespace GlobalTheory.Mem.PlaceVal

section General

open Formalism.L2.DIV Formalism.BasicNotions Formalism.BasicNotions.TH

theorem exists_ext_pol {K K' I W : Type} [Field K] [Field K'] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ} (ι : K →+* K')
    (σ' : K' →+* ℂ) (hσ : σ'.comp ι = σ) (U : Submodule K (MvPolynomial I K)) (c : U →ₛₗ[σ] W) :
    ∃ c' : MvPolynomial I K' →ₛₗ[σ'] W, ∀ v : U, c' (MvPolynomial.map ι (v : MvPolynomial I K)) = c v := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  let _ : Module K' W := Module.compHom W σ'
  let f : MvPolynomial I K' →ₗ[K'] W :=
    (MvPolynomial.basisMonomials I K').constr K' fun m => c (π (MvPolynomial.monomial m 1))
  have hf : ∀ m, f (MvPolynomial.monomial m 1) = c (π (MvPolynomial.monomial m 1)) := fun m => by
    have := (MvPolynomial.basisMonomials I K').constr_basis K' (fun m => c (π (MvPolynomial.monomial m 1))) m
    rwa [MvPolynomial.coe_basisMonomials] at this
  have key : ∀ p : MvPolynomial I K, f (MvPolynomial.map ι p) = c (π p) := fun p => by
    induction p using MvPolynomial.induction_on' with
    | monomial m a =>
      have e1 : MvPolynomial.map ι (MvPolynomial.monomial m a) = ι a • MvPolynomial.monomial m (1 : K') := by
        rw [MvPolynomial.map_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      have e2 : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : K) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [e1, f.map_smul, hf, e2, π.map_smul, map_smulₛₗ, ← RingHom.congr_fun hσ a]
      rfl
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  refine ⟨{ toFun := f, map_add' := f.map_add, map_smul' := fun a p => f.map_smul a p }, fun v => (key v).trans ?_⟩
  exact congrArg c (LinearMap.congr_fun hπ v)

theorem exists_ext_VV {K K' I W : Type} [Field K] [Field K'] [Fintype I] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}
    (ι : K →+* K') (σ' : K' →+* ℂ) (hσ : σ'.comp ι = σ) {n : ℕ} (lam : I → DomWeight n) (c : VV K lam →ₛₗ[σ] W) :
    ∃ c' : VV K' lam →ₛₗ[σ'] W, ∀ v : VV K lam, ∃ v' : VV K' lam,
      (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) ∧ c' v' = c v := by
  obtain ⟨c', hc⟩ := exists_ext_pol ι σ' hσ (VV K lam) c
  exact ⟨c'.comp (VV K' lam).subtype, fun v => ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩, rfl, hc v⟩⟩

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1600000 in
theorem exists_coef_placeEx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, (∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c0') ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR _ _ i K' _ jL σ' hσ
  obtain ⟨gramR, c0R, c0L, hT⟩ := hR.fam.tie
  obtain ⟨c0', hc⟩ := exists_ext_VV (W := (R.cV i).W) jL σ' hσ (lamV D i) (c0L i)
  exact ⟨c0', ⟨gramR, c0R, c0L, hT, hc⟩, fun t Cl _ h =>
    GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hR.models.jV hT hc hR.lev hR.grp.chiW hR.fam.pl_onto hR.fam.muVal⟩

end GlobalTheory.Mem.PlaceVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffExt_rationalForms_values_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, (∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c0') ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  first | exact @GlobalTheory.Mem.PlaceVal.exists_coef_placeEx | exact GlobalTheory.Mem.PlaceVal.exists_coef_placeEx | (intros; apply GlobalTheory.Mem.PlaceVal.exists_coef_placeEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactIntegralGLFiniteAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactIntegralGLFiniteAdeles
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory

theorem isCompact_matInt_set (F : Type) [Field F] [NumberField F] (n : ℕ) :
    IsCompact {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) | PIW.ClassFinD.MatInt M} := by
  have hO : IsCompact ((PIW.ClassFinD.Ohat F : Subring (FiniteAdeleRing (𝓞 F) F)) :
      Set (FiniteAdeleRing (𝓞 F) F)) := PI.WAU.isCompact_Ohat (F := F)
  have h := isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => hO))
  have he : {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) | PIW.ClassFinD.MatInt M} =
      Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n =>
        ((PIW.ClassFinD.Ohat F : Subring (FiniteAdeleRing (𝓞 F) F)) : Set (FiniteAdeleRing (𝓞 F) F)))) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [he]
  exact h

theorem isCompact_KGL (F : Type) [Field F] [NumberField F] (n : ℕ) :
    IsCompact (PIW.ClassFinD.KGL F n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) := by
  have hA := isCompact_matInt_set F n
  have hA' := (MulOpposite.opHomeomorph
    (M := Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))).symm.isCompact_preimage.2 hA
  have h := (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))).isCompact_preimage (hA.prod hA')
  convert h using 1
  ext g
  exact Iff.rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactIntegralGLFiniteAdelesStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_integralGL_finiteAdeles : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), IsCompact (PIW.ClassFinD.KGL F n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) := by
  first | exact @GlobalTheory.isCompact_KGL | exact GlobalTheory.isCompact_KGL | (intros; apply GlobalTheory.isCompact_KGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKsOfFinExt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem finiteDimensional_Ks_of_finExt {l : ℕ} [Fact l.Prime] (K : FinExt l) (s : ℕ) :
    FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h0 : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  have hfin : Finite ↥{x : Om l | x ^ (l ^ s) = 1} := by
    apply Set.Finite.to_subtype
    refine (Multiset.finite_toSet (Polynomial.nthRoots (l ^ s) (1 : Om l))).subset ?_
    intro x hx
    exact (Polynomial.mem_nthRoots hpos).2 hx
  have h1 : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  unfold Ks
  exact IntermediateField.finiteDimensional_sup _ _

end GlobalTheory.MemLoc
end
