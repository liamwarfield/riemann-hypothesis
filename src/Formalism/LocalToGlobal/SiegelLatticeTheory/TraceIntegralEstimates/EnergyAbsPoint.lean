module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsTrunc

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsTail
noncomputable section

open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def K4 (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH) (W : G → V) (W' : G → V') (γ : G)
    (q : (G × G) × (G × G)) : V' →L[ℂ] V :=
  kG σ d w W W' γ (φinv q.1, φinv q.2)

section Hyp

variable {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
  {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
  {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}

theorem integrable_liftedRankOneKernel (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    Integrable (K4 σ d w W W' γ) ((ν.prod μS).prod (ν'.prod μS')) := by
  have hi := integrable_kG hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB
  rw [prod_map_φinv hm hm'] at hi
  exact hi.comp_measurable (Measurable.prodMap (measurable_φinv (G := G)) (measurable_φinv (G := G)))

theorem integral_liftedRankOneKernel [μ.IsMulLeftInvariant] [SFinite μ] (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W)
    (hW' : IsWAbs μ σ d w S' τ' ν' W') (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ∫ q, K4 σ d w W W' γ q ∂((ν.prod μS).prod (ν'.prod μS')) = ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ := by
  have hi := integrable_kG hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB
  have hF : Measurable (Prod.map (φinv : G × G → G) (φinv : G × G → G)) :=
    Measurable.prodMap (measurable_φinv (G := G)) (measurable_φinv (G := G))
  have hi' := hi
  rw [prod_map_φinv hm hm'] at hi'
  rw [← integral_kG hσ hW W' γ hi, prod_map_φinv hm hm',
    integral_map hF.aemeasurable hi'.aestronglyMeasurable]
  rfl

theorem prod_restrict_four (A A' : Set G) :
    (ν.prod (μS.restrict A)).prod (ν'.prod (μS'.restrict A')) =
      ((ν.prod μS).prod (ν'.prod μS')).restrict ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A')) := by
  have e1 : ν.prod (μS.restrict A) = (ν.prod μS).restrict (Set.univ ×ˢ A) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have e2 : ν'.prod (μS'.restrict A') = (ν'.prod μS').restrict (Set.univ ×ˢ A') := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e1, e2, Measure.prod_restrict]

end Hyp

section Approx

variable {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
  {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
  {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}

theorem approx_OO [μ.IsMulLeftInvariant] [SFinite μ] (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W)
    (hW' : IsWAbs μ σ d w S' τ' ν' W') (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤)
    (C C' : ℕ → Set G) (hCm : ∀ n, MeasurableSet (C n)) (hC'm : ∀ n, MeasurableSet (C' n))
    (hCmono : Monotone C) (hC'mono : Monotone C') (hCS : S ⊆ ⋃ n, C n) (hC'S : S' ⊆ ⋃ n, C' n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀, ∀ A A' : Set G, MeasurableSet A → A ⊆ S → μS A < ⊤ → MeasurableSet A' → A' ⊆ S' → μS' A' < ⊤ →
      C n₀ ⊆ A → C' n₀ ⊆ A' →
      Real.sqrt (hsA (∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ - Xop μS ν μS' ν' σ d w W W' A A' γ)) ≤ ε := by
  set P := (ν.prod μS).prod (ν'.prod μS') with hP
  have hK4 := integrable_liftedRankOneKernel hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ X : V' →L[ℂ] V, Real.sqrt (hsA X) ≤ c * ‖X‖ :=
    ⟨‖hsC (V := V) (V' := V')‖, norm_nonneg _, fun X => by
      rw [← norm_hsC]
      exact ContinuousLinearMap.le_opNorm _ _⟩
  let Rn : ℕ → Set ((G × G) × (G × G)) := fun n => (Set.univ ×ˢ C n) ×ˢ (Set.univ ×ˢ C' n)
  have hRm : ∀ n, MeasurableSet (Rn n) := fun n =>
    (MeasurableSet.univ.prod (hCm n)).prod (MeasurableSet.univ.prod (hC'm n))
  have hanti : Antitone fun n => (Rn n)ᶜ := fun n m hnm =>
    Set.compl_subset_compl.mpr
      (Set.prod_mono (Set.prod_mono subset_rfl (hCmono hnm)) (Set.prod_mono subset_rfl (hC'mono hnm)))
  have hnull : P (⋂ n, (Rn n)ᶜ) = 0 := by
    have hae := ae_mem_four (ν := ν) (μS := μS) (ν' := ν') (μS' := μS') h0 h0'
    rw [ae_iff] at hae
    refine measure_mono_null (fun p hp => ?_) hae
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hp
    rintro ⟨h1, h2⟩
    obtain ⟨n1, hn1⟩ := Set.mem_iUnion.mp (hCS h1)
    obtain ⟨n2, hn2⟩ := Set.mem_iUnion.mp (hC'S h2)
    exact hp (max n1 n2)
      ⟨⟨trivial, hCmono (le_max_left _ _) hn1⟩, ⟨trivial, hC'mono (le_max_right _ _) hn2⟩⟩
  have hT := tendsto_setIntegral_of_antitone (μ := P) (f := fun q => ‖K4 σ d w W W' γ q‖)
    (fun n => (hRm n).compl) hanti ⟨0, hK4.norm.integrableOn⟩
  rw [setIntegral_measure_zero _ hnull] at hT
  have hT' := hT.const_mul c
  rw [mul_zero] at hT'
  obtain ⟨n₀, hn₀⟩ := (hT'.eventually (gt_mem_nhds hε)).exists
  refine ⟨n₀, fun A A' hA hAS hAf hA' hAS' hAf' hCA hC'A => ?_⟩
  have hR : MeasurableSet (((Set.univ : Set G) ×ˢ A) ×ˢ ((Set.univ : Set G) ×ˢ A')) :=
    (MeasurableSet.univ.prod hA).prod (MeasurableSet.univ.prod hA')
  have hX : Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q in (Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'), K4 σ d w W W' γ q ∂P := by
    rw [Xop_eq_integral hσ hW hW' hinv hinv' hA hAS hAf hA' hAS' hAf' γ
      (by rw [prod_restrict_four]; exact hK4.restrict), prod_restrict_four]
    rfl
  have hdiff : ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ - Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, K4 σ d w W W' γ q ∂P := by
    rw [← integral_liftedRankOneKernel hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB, hX, setIntegral_compl hR hK4]
  have hsub : ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ ⊆ (Rn n₀)ᶜ :=
    Set.compl_subset_compl.mpr
      (Set.prod_mono (Set.prod_mono subset_rfl hCA) (Set.prod_mono subset_rfl hC'A))
  rw [hdiff]
  calc Real.sqrt (hsA (∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, K4 σ d w W W' γ q ∂P))
      ≤ ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, Real.sqrt (hsA (K4 σ d w W W' γ q)) ∂P :=
        sqrt_hsA_integral_le _ hK4.restrict
    _ ≤ ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, c * ‖K4 σ d w W W' γ q‖ ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => Real.sqrt_nonneg _)
          (hK4.norm.const_mul c).restrict (Filter.Eventually.of_forall fun q => hc _)
    _ = c * ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, ‖K4 σ d w W W' γ q‖ ∂P :=
        integral_const_mul c _
    _ ≤ c * ∫ q in (Rn n₀)ᶜ, ‖K4 σ d w W W' γ q‖ ∂P :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hK4.norm.integrableOn
          (Filter.Eventually.of_forall fun q => norm_nonneg _) (Filter.Eventually.of_forall hsub)) hc0
    _ ≤ ε := hn₀.le

end Approx

end Formalism.L2.S.Pv.EnergyAbs
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsEquiv
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace HH] in
theorem fY_linear (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (e : V) (p : G × G) :
    ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p = fY σ w W e p := by
  simp only [fY]
  simp_rw [smul_smul, ← Finset.sum_smul]
  congr 1
  rw [← (stdOrthonormalBasis ℂ V).sum_inner_mul_inner (W (p.2⁻¹ * p.1)) e]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem Yop_apply_integral {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν]
    [SFinite μS] {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAf : μS A < ⊤) (e : V) :
    Yop μS ν σ w W A e = ∫ p, fY σ w W e p ∂(ν.prod (μS.restrict A)) := by
  rw [Yop_apply]
  simp_rw [yv_eq_integral hσ hW hinv hA hAS hAf]
  have hint : ∀ i, Integrable (fun p => ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ •
      fY σ w W (stdOrthonormalBasis ℂ V i) p) (ν.prod (μS.restrict A)) :=
    fun i => (integrable_fY hσ hW hinv hA hAS hAf _).smul _
  symm
  calc ∫ p, fY σ w W e p ∂(ν.prod (μS.restrict A))
      = ∫ p, ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p
          ∂(ν.prod (μS.restrict A)) := by
        congr 1
        funext p
        exact (fY_linear σ w W e p).symm
    _ = ∑ i, ∫ p, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p
          ∂(ν.prod (μS.restrict A)) := integral_finsetSum _ fun i _ => hint i
    _ = _ := by simp_rw [integral_smul]

omit [SecondCountableTopology G] in
theorem prod_restrict_translate {μS : Measure G} [SFinite μS] (ν : Measure G) [SFinite ν] {s0 : G}
    (hmap : μS.map (fun x => x * s0⁻¹) = μS) (A : Set G) :
    ν.prod (μS.restrict A) =
      (ν.prod (μS.restrict ((fun v => v * s0⁻¹) ⁻¹' A))).map (Prod.map id (fun v => v * s0⁻¹)) := by
  have hE := (MeasurableEquiv.mulRight (s0⁻¹ : G)).measurableEmbedding.restrict_map μS A
  rw [MeasurableEquiv.coe_mulRight, hmap] at hE
  rw [← Measure.map_prod_map ν _ measurable_id (measurable_mul_const s0⁻¹), Measure.map_id, ← hE]

theorem sigma_Yop {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν] {S : Set G}
    (hS : IsHaarSub S μS) {d : ℝ} {w : HH} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S) (hAf : μS A < ⊤)
    {s0 : G} (hs0 : s0 ∈ S) (e : V) :
    σ s0⁻¹ (Yop μS ν σ w W A e) =
      Yop μS ν σ w W ((fun v => v * s0⁻¹) ⁻¹' A) (ContinuousLinearMap.adjoint (τ s0) e) := by
  obtain ⟨-, -, hmulS, hinvS, hsig, -, -, -, -, hright, -⟩ := hS
  have : SFinite μS := by have := hsig; infer_instance
  have hmap : μS.map (fun x => x * s0⁻¹) = μS := hright _ (hinvS s0 hs0)
  have hA'm : MeasurableSet ((fun v => v * s0⁻¹) ⁻¹' A) := measurable_mul_const s0⁻¹ hA
  have hA'S : (fun v => v * s0⁻¹) ⁻¹' A ⊆ S := by
    intro v hv
    have h1 := hmulS _ (hAS hv) s0 hs0
    simpa [mul_assoc] using h1
  have hA'f : μS ((fun v => v * s0⁻¹) ⁻¹' A) < ⊤ := by
    rw [← Measure.map_apply (measurable_mul_const s0⁻¹) hA, hmap]
    exact hAf
  have hemb : MeasurableEmbedding (Prod.map id (fun v : G => v * s0⁻¹)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl G) (MeasurableEquiv.mulRight s0⁻¹)).measurableEmbedding

  rw [Yop_apply_integral hσ hW hinvS hA hAS hAf, Yop_apply_integral hσ hW hinvS hA'm hA'S hA'f,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_fY hσ hW hinvS hA hAS hAf e),
    prod_restrict_translate ν hmap A, hemb.integral_map]
  congr 1
  funext p
  have hq : (p.2 * s0⁻¹)⁻¹ * p.1 = s0 * (p.2⁻¹ * p.1) := by group
  simp only [fY, Prod.map, id_eq, ContinuousLinearMap.map_smul]
  rw [hq, rep_mul_apply hσ, inv_mul_cancel_left, hW.2.2.2.1 s0 hs0,
    ContinuousLinearMap.adjoint_inner_right]

theorem sand_translate {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν μS' ν' : Measure G} [SFinite ν]
    [SFinite ν'] {S S' : Set G} (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS') {d : ℝ} {w : HH}
    {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    {Ω Ω' : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hΩf : μS Ω < ⊤)
    (hΩm' : MeasurableSet Ω') (hΩS' : Ω' ⊆ S') (hΩf' : μS' Ω' < ⊤)
    {s0 s0' : G} (hs0 : s0 ∈ S) (hs0' : s0' ∈ S') (γ : G) :
    sand σ (Yop μS ν σ w W Ω) (Yop μS' ν' σ w W' Ω') (s0 * γ * s0'⁻¹) =
      (τ s0).comp ((sand σ (Yop μS ν σ w W ((fun v => v * s0⁻¹) ⁻¹' Ω))
        (Yop μS' ν' σ w W' ((fun v => v * s0'⁻¹) ⁻¹' Ω')) γ).comp (ContinuousLinearMap.adjoint (τ' s0'))) := by
  ext b
  refine ext_inner_left ℂ fun a => ?_
  rw [inner_sand]
  conv_rhs => rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left, inner_sand]
  rw [← sigma_Yop hσ hS hW hΩm hΩS hΩf hs0 a, ← sigma_Yop hσ hS' hW' hΩm' hΩS' hΩf' hs0' b]
  have hmove : ∀ u : HH, σ γ (σ s0'⁻¹ u) = σ s0⁻¹ (σ (s0 * γ * s0'⁻¹) u) := by
    intro u
    rw [rep_mul_apply hσ, rep_mul_apply hσ, show s0⁻¹ * (s0 * γ * s0'⁻¹) = γ * s0'⁻¹ by group]
  rw [hmove, hσ.2.2.1]

theorem hsA_Xop_translate {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G}
    {μS ν μS' ν' : Measure G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    [SFinite ν] [SFinite ν'] (hσ : IsUnitRep σ) (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS')
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    {Ω Ω' : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hΩf : μS Ω < ⊤)
    (hΩm' : MeasurableSet Ω') (hΩS' : Ω' ⊆ S') (hΩf' : μS' Ω' < ⊤)
    {s0 s0' : G} (hs0 : s0 ∈ S) (hs0' : s0' ∈ S') (γ : G) :
    hsA (Xop μS ν μS' ν' σ d w W W' Ω Ω' (s0 * γ * s0'⁻¹)) =
      hsA (Xop μS ν μS' ν' σ d w W W' ((fun v => v * s0⁻¹) ⁻¹' Ω) ((fun v => v * s0'⁻¹) ⁻¹' Ω') γ) := by
  simp only [Xop]
  rw [hsA_smul, hsA_smul, sand_translate hσ hS hS' hW hW' hΩm hΩS hΩf hΩm' hΩS' hΩf' hs0 hs0' γ,
    hsA_conj (τ s0) (τ' s0') (hW.2.2.1 s0 hs0) (hW'.2.2.1 s0' hs0')]

end Formalism.L2.S.Pv.EnergyAbs
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsLower
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]

theorem lintegral_ge_rect {μS μS' : Measure G} [SFinite μS'] (f : G → G → ℝ≥0∞)
    (hf : Measurable (fun p : G × G => f p.1 p.2)) (E E' : Set G) (c : ℝ≥0∞)
    (h : ∀ s ∈ E, ∀ s' ∈ E', c ≤ f s s') : c * μS' E' * μS E ≤ ∫⁻ s, ∫⁻ s', f s s' ∂μS' ∂μS := by
  have hsec : ∀ s, Measurable (f s) := fun s =>
    hf.comp (by fun_prop : Measurable (fun s' : G => (s, s')))
  have hin : ∀ s ∈ E, c * μS' E' ≤ ∫⁻ s', f s s' ∂μS' := by
    intro s hs
    calc c * μS' E' ≤ c * μS' {s' | c ≤ f s s'} :=
          mul_le_mul' le_rfl (measure_mono fun s' hs' => h s hs s' hs')
      _ ≤ _ := mul_meas_ge_le_lintegral₀ (hsec s).aemeasurable c
  have hg : Measurable (fun s => ∫⁻ s', f s s' ∂μS') := hf.lintegral_prod_right'
  calc c * μS' E' * μS E ≤ c * μS' E' * μS {s | c * μS' E' ≤ ∫⁻ s', f s s' ∂μS'} :=
        mul_le_mul' le_rfl (measure_mono fun s hs => hin s hs)
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hg.aemeasurable _

def folInt (Ω K : Set G) : Set G := {t | t ∈ Ω ∧ ∀ k ∈ K, k * t ∈ Ω}

theorem measure_inv_preimage {μS : Measure G} [MeasurableInv G] (hinv : μS.map (fun x => x⁻¹) = μS)
    (B : Set G) : μS {s | s⁻¹ ∈ B} = μS B := by
  have e : (μS.map (MeasurableEquiv.inv G)) B = μS ((MeasurableEquiv.inv G) ⁻¹' B) :=
    MeasurableEquiv.map_apply _ _
  have hm : μS.map (MeasurableEquiv.inv G) = μS := hinv
  rw [hm] at e
  exact e.symm

theorem tendsto_ratio_ennreal {a b : ℕ → ℝ≥0∞} (hb0 : ∀ n, 0 < b n) (hbt : ∀ n, b n < ⊤)
    (hab : ∀ n, a n ≤ b n) (h : Tendsto (fun n => (a n).toReal / (b n).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => a n / b n) atTop (𝓝 1) := by
  have hfin : ∀ n, a n / b n ≠ ⊤ := fun n =>
    ENNReal.div_ne_top (ne_top_of_le_ne_top (hbt n).ne (hab n)) (hb0 n).ne'
  have hfun : (fun n => a n / b n) = fun n => ENNReal.ofReal ((a n).toReal / (b n).toReal) := by
    funext n
    rw [← ENNReal.toReal_div, ENNReal.ofReal_toReal (hfin n)]
  rw [hfun, ← ENNReal.ofReal_one]
  exact ENNReal.tendsto_ofReal h

theorem liminf_lower {μS μS' : Measure G} [SFinite μS'] [MeasurableInv G]
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (Ω Ω' : ℕ → Set G) (hΩ0 : ∀ n, 0 < μS (Ω n)) (hΩt : ∀ n, μS (Ω n) < ⊤)
    (hΩ0' : ∀ n, 0 < μS' (Ω' n)) (hΩt' : ∀ n, μS' (Ω' n) < ⊤)
    (f : ℕ → G → G → ℝ≥0∞) (hf : ∀ n, Measurable (fun p : G × G => f n p.1 p.2)) (h : ℝ) (hh : 0 ≤ h)
    (key : ∀ ε : ℝ, 0 < ε → ∃ K K' : Set G,
      Tendsto (fun n => μS (folInt (Ω n) K) / μS (Ω n)) atTop (𝓝 1) ∧
      Tendsto (fun n => μS' (folInt (Ω' n) K') / μS' (Ω' n)) atTop (𝓝 1) ∧
      ∀ n s s', s⁻¹ ∈ folInt (Ω n) K → s'⁻¹ ∈ folInt (Ω' n) K' →
        ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ f n s s') :
    ENNReal.ofReal h ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop := by
  set L := liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop
    with hL
  have step : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ L := by
    intro ε hε
    obtain ⟨K, K', hK, hK', hf'⟩ := key ε hε
    set c := ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) with hc
    have hlim : Tendsto (fun n => c * ((μS (folInt (Ω n) K) / μS (Ω n)) *
        (μS' (folInt (Ω' n) K') / μS' (Ω' n)))) atTop (𝓝 c) := by
      have h1 := ENNReal.Tendsto.mul hK (Or.inl one_ne_zero) hK' (Or.inl one_ne_zero)
      have h2 := ENNReal.Tendsto.const_mul h1 (a := c) (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_one, mul_one] at h2
      exact h2
    rw [hL, ← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    have hA0 := (hΩ0 n).ne'
    have hAt := (hΩt n).ne
    have hmain := lintegral_ge_rect (μS := μS) (μS' := μS') (f n) (hf n)
      {s | s⁻¹ ∈ folInt (Ω n) K} {s' | s'⁻¹ ∈ folInt (Ω' n) K'} c
      (fun s hs s' hs' => hf' n s s' hs hs')
    rw [measure_inv_preimage hinv, measure_inv_preimage hinv'] at hmain
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), div_eq_mul_inv, div_eq_mul_inv]
    calc c * (μS (folInt (Ω n) K) * (μS (Ω n))⁻¹ *
          (μS' (folInt (Ω' n) K') * (μS' (Ω' n))⁻¹))
        = (μS (Ω n))⁻¹ * (μS' (Ω' n))⁻¹ *
          (c * μS' (folInt (Ω' n) K') * μS (folInt (Ω n) K)) := by ring
      _ ≤ _ := mul_le_mul' le_rfl hmain
  have hcont : Continuous (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) :=
    ENNReal.continuous_ofReal.comp (((continuous_const.sub continuous_id).max continuous_const).pow 2)
  have h0 : ENNReal.ofReal ((max (Real.sqrt h - 0) 0) ^ 2) = ENNReal.ofReal h := by
    rw [sub_zero, max_eq_left (Real.sqrt_nonneg h), Real.sq_sqrt hh]
  have hg : Tendsto (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal h)) := by
    rw [← h0]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hg (eventually_nhdsWithin_of_forall fun ε hε => step ε hε)

end Formalism.L2.S.Pv.EnergyAbs
end
end

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def cpiece (S : Set G) (n : ℕ) : Set G := CompactExhaustion.choice G n ∩ S

theorem cpiece_compact {S : Set G} (hS : IsClosed S) (n : ℕ) : IsCompact (cpiece S n) :=
  ((CompactExhaustion.choice G).isCompact n).inter_right hS

theorem cpiece_mono (S : Set G) : Monotone (cpiece S) := by
  intro m n hmn
  exact Set.inter_subset_inter_left _ ((CompactExhaustion.choice G).subset hmn)

theorem cpiece_cover (S : Set G) : S ⊆ ⋃ n, cpiece S n := by
  intro x hx
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem x
  exact Set.mem_iUnion.2 ⟨n, hn, hx⟩

theorem translate_props {μS : Measure G} {S : Set G} (hS : IsHaarSub S μS) {Ω : Set G} (hΩm : MeasurableSet Ω)
    (hΩS : Ω ⊆ S) (hΩt : μS Ω < ⊤) {s : G} (hs : s ∈ S) :
    MeasurableSet ((fun v => v * s⁻¹) ⁻¹' Ω) ∧ (fun v => v * s⁻¹) ⁻¹' Ω ⊆ S ∧
      μS ((fun v => v * s⁻¹) ⁻¹' Ω) < ⊤ := by
  obtain ⟨-, -, hmul, hinv, -, -, -, -, -, hr, -⟩ := hS
  refine ⟨hΩm.preimage (measurable_mul_const s⁻¹), fun v hv => ?_, ?_⟩
  · have h1 : v * s⁻¹ * s ∈ S := hmul _ (@hΩS (v * s⁻¹) hv) _ hs
    simpa using h1
  · rw [← Measure.map_apply (measurable_mul_const s⁻¹) hΩm, hr _ (hinv _ hs)]
    exact hΩt

private theorem hilbertSchmidtSq_nonneg_aux_lemma (A : V' →L[ℂ] V) : 0 ≤ Formalism.L2.SG.Pf.EnergyAbs.hsA A := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

private theorem sq_max_le_hilbertSchmidtSq_lemma_2 (A B : V' →L[ℂ] V) {ε : ℝ}
    (h : Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA (A - B)) ≤ ε) :
    max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ^ 2 ≤ Formalism.L2.SG.Pf.EnergyAbs.hsA B := by
  have hB := hilbertSchmidtSq_nonneg_aux_lemma B
  have htri := sqrt_hsA_le_add_sub A B
  have hmax : max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ≤ Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA B) :=
    max_le (by linarith) (Real.sqrt_nonneg _)
  calc max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ^ 2 ≤ Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA B) ^ 2 :=
        pow_le_pow_left₀ (le_max_right _ _) hmax 2
    _ = Formalism.L2.SG.Pf.EnergyAbs.hsA B := Real.sq_sqrt hB

theorem point_lower {μ : Measure G} [μ.IsHaarMeasure] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    {w : HH} {S S' : Set G} {μS μS' ν ν' : Measure G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')}
    {W : G → V} {W' : G → V'} [SFinite ν] [SFinite ν'] (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS')
    (hq : IsQuot μ μS ν) (hq' : IsQuot μ μS' ν')
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (Ω Ω' : ℕ → Set G) (hΩ : ∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤)
    (hΩ' : ∀ n, MeasurableSet (Ω' n) ∧ Ω' n ⊆ S' ∧ 0 < μS' (Ω' n) ∧ μS' (Ω' n) < ⊤)
    (hF : ∀ K : Set G, IsCompact K → K ⊆ S → Tendsto (fun n =>
      (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1))
    (hF' : ∀ K : Set G, IsCompact K → K ⊆ S' → Tendsto (fun n =>
      (μS' {t | t ∈ Ω' n ∧ ∀ k ∈ K, k * t ∈ Ω' n}).toReal / (μS' (Ω' n)).toReal) atTop (𝓝 1))
    (hXc : ∀ n, Continuous (fun g => hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) g)))
    (γ : G) (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ)) ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ *
        ∫⁻ s, ∫⁻ s', ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) (s * γ * s'⁻¹)))
          ∂μS' ∂μS) atTop := by
  have hS₀ := hS
  have hS'₀ := hS'
  obtain ⟨hSc, -, -, hinvS, hσS, -, h0S, -, -, -, hinvmS⟩ := hS₀
  obtain ⟨hSc', -, -, hinvS', hσS', -, h0S', -, -, -, hinvmS'⟩ := hS'₀
  have : SigmaFinite μS := hσS
  have : SigmaFinite μS' := hσS'
  have hm : μ = (ν.prod μS).map φinv := (quot_map_inv hq) hinvmS
  have hm' : μ = (ν'.prod μS').map φinv := (quot_map_inv hq') hinvmS'
  refine liminf_lower hinvmS hinvmS' Ω Ω'
    (fun n => (hΩ n).2.2.1) (fun n => (hΩ n).2.2.2) (fun n => (hΩ' n).2.2.1) (fun n => (hΩ' n).2.2.2)
    (fun n s s' => ENNReal.ofReal (Formalism.L2.SG.Pf.EnergyAbs.hsA
      (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) (s * γ * s'⁻¹))))
    (fun n => ?_) (Formalism.L2.SG.Pf.EnergyAbs.hsA (∫ x, Formalism.L2.SG.Pf.EnergyAbs.rk1A (W x) (W' (γ⁻¹ * x)) ∂μ))
    (hilbertSchmidtSq_nonneg_aux_lemma _) (fun ε hε => ?_)
  · exact ENNReal.measurable_ofReal.comp ((hXc n).measurable.comp
      ((continuous_fst.mul continuous_const).mul continuous_snd.inv).measurable)
  · obtain ⟨n₀, hn₀⟩ := approx_OO hσ hW hW' hinvS hinvS' h0S h0S' hm hm' γ hB
      (cpiece S) (cpiece S')
      (fun n => (cpiece_compact hSc n).isClosed.measurableSet)
      (fun n => (cpiece_compact hSc' n).isClosed.measurableSet)
      (cpiece_mono S) (cpiece_mono S')
      (cpiece_cover S) (cpiece_cover S') ε hε
    refine ⟨cpiece S n₀, cpiece S' n₀, ?_, ?_, ?_⟩
    · refine tendsto_ratio_ennreal (fun n => (hΩ n).2.2.1) (fun n => (hΩ n).2.2.2)
        (fun n => measure_mono fun t ht => (show t ∈ Ω n ∧ _ from ht).1) ?_
      exact hF _ (cpiece_compact hSc n₀) Set.inter_subset_right
    · refine tendsto_ratio_ennreal (fun n => (hΩ' n).2.2.1) (fun n => (hΩ' n).2.2.2)
        (fun n => measure_mono fun t ht => (show t ∈ Ω' n ∧ _ from ht).1) ?_
      exact hF' _ (cpiece_compact hSc' n₀) Set.inter_subset_right
    · intro n s s' hs hs'
      have hs2 : s⁻¹ ∈ Ω n ∧ ∀ k ∈ cpiece S n₀, k * s⁻¹ ∈ Ω n := hs
      have hs2' : s'⁻¹ ∈ Ω' n ∧ ∀ k ∈ cpiece S' n₀, k * s'⁻¹ ∈ Ω' n := hs'
      have hsS : s ∈ S := by simpa using hinvS _ ((hΩ n).2.1 hs2.1)
      have hsS' : s' ∈ S' := by simpa using hinvS' _ ((hΩ' n).2.1 hs2'.1)
      obtain ⟨hAm, hAS, hAt⟩ := translate_props hS (hΩ n).1 (hΩ n).2.1 (hΩ n).2.2.2 hsS
      obtain ⟨hAm', hAS', hAt'⟩ :=
        translate_props hS' (hΩ' n).1 (hΩ' n).2.1 (hΩ' n).2.2.2 hsS'
      have happrox := hn₀ _ _ hAm hAS hAt hAm' hAS' hAt' (fun k hk => hs2.2 k hk)
        (fun k hk => hs2'.2 k hk)
      rw [hsA_Xop_translate hσ hS hS' hW hW' (hΩ n).1 (hΩ n).2.1
        (hΩ n).2.2.2 (hΩ' n).1 (hΩ' n).2.1 (hΩ' n).2.2.2 hsS hsS' γ]
      exact ENNReal.ofReal_le_ofReal (sq_max_le_hilbertSchmidtSq_lemma_2 _ _ happrox)

end Formalism.L2.S.Pv.EnergyAbs
