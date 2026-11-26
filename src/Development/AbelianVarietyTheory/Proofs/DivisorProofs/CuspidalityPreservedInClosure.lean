module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalityPreservedInClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalityPreservedInClosure
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.HolDict.ZClosed

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem exists_bound_orbit (Γ : Subgroup G) [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ x : G, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) ≤ N := by
  classical
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have hKK : IsCompact (K * K⁻¹) := hK.mul hK.inv
  have hfin : (((↑) : Γ → G) ⁻¹' (K * K⁻¹)).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKK).finite_of_discrete
  refine ⟨hfin.toFinset.card, fun x => ?_⟩
  by_cases h : ∃ γ₀ : Γ, γ₀⁻¹ • x ∈ K
  · obtain ⟨γ₀, h₀⟩ := h
    have hs : ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) =
        ∑ γ ∈ hfin.toFinset.image (fun δ => γ₀ * δ⁻¹), K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) := by
      refine tsum_eq_sum fun γ hγ => Set.indicator_of_notMem (fun hx => hγ ?_) _
      refine Finset.mem_image.2 ⟨γ⁻¹ * γ₀, ?_, by group⟩
      rw [Set.Finite.mem_toFinset]
      refine ⟨_, hx, _, Set.inv_mem_inv.2 h₀, ?_⟩
      simp only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hs]
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun γ _ =>
      Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)) ?_
    simp only [nsmul_eq_mul, mul_one, Nat.cast_le]
    exact Finset.card_image_le
  · push_neg at h
    simp only [Set.indicator_of_notMem (h _), tsum_zero, zero_le]

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

theorem exists_lintegral_le (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {K : Set G} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ f : G → ℝ≥0∞, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      ∫⁻ x in K, f x ∂μ ≤ N * ∫⁻ x in 𝓕, f x ∂μ := by
  obtain ⟨N, hN⟩ := exists_bound_orbit Γ hK
  refine ⟨N, fun f hf hinv => ?_⟩
  have hKm := hK.measurableSet
  rw [← lintegral_indicator hKm, h𝓕.lintegral_eq_tsum', ← lintegral_tsum, ← lintegral_const_mul _ hf]
  · refine lintegral_mono fun x => ?_
    have : ∀ γ : Γ, K.indicator f (γ⁻¹ • x) = K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) * f x := by
      intro γ
      by_cases h : γ⁻¹ • x ∈ K
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
        exact hinv _ (γ⁻¹).2 x
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    simp only [this]
    rw [ENNReal.tsum_mul_right]
    exact mul_le_mul_left (hN x) _
  · intro γ
    exact ((hf.indicator hKm).comp (measurable_const_mul ((γ⁻¹ : Γ) : G))).aemeasurable

theorem lintegral_average_le (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] {X : Type} [MeasurableSpace X]
    (m : Measure X) [IsFiniteMeasure m] {j : X → G} (hj : Measurable j) {K Ω : Set G}
    (hΩ : IsCompact Ω) (hm : ∀ᵐ z ∂m, j z ∈ K) {h : G → ℂ} (hh : Continuous h) :
    ∫⁻ g in Ω, ‖∫ z, h (j z * g) ∂m‖ₑ ∂μ ≤ m Set.univ * ∫⁻ x in K * Ω, ‖h x‖ₑ ∂μ := by
  have hmeas : Measurable fun p : G × X => ‖h (j p.2 * p.1)‖ₑ :=
    hh.enorm.measurable.comp ((hj.comp measurable_snd).mul measurable_fst)
  calc _ ≤ ∫⁻ g in Ω, ∫⁻ z, ‖h (j z * g)‖ₑ ∂m ∂μ := lintegral_mono fun g => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ z, ∫⁻ g in Ω, ‖h (j z * g)‖ₑ ∂μ ∂m := lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ ∫⁻ _z, ∫⁻ x in K * Ω, ‖h x‖ₑ ∂μ ∂m := by
        refine lintegral_mono_ae (hm.mono fun z hz => ?_)
        have e := (measurePreserving_mul_left μ (j z)).setLIntegral_comp_emb
          (MeasurableEquiv.mulLeft (j z)).measurableEmbedding (fun x => ‖h x‖ₑ) Ω
        refine (le_of_eq e).trans (lintegral_mono_set ?_)
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨_, hz, _, hg, rfl⟩
    _ = _ := by rw [lintegral_const, mul_comm]

theorem average_eq_zero_of_mem_closure [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) {Q : Type} [MeasurableSpace Q] {π : G → Q} (hπ : Measurable π)
    (ρ : G → Lp ℂ 2 ((μ.restrict 𝓕).map π) → Lp ℂ 2 ((μ.restrict 𝓕).map π))
    (hρ : ∀ g F, ∀ᵐ x ∂μ, ρ g F (π x) = F (π (x * g)))
    {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]
    {j : X → G} (hj : Continuous j) {s : Set X} (hs : IsCompact s) (hm : ∀ᵐ z ∂m, z ∈ s)
    {φ ψ : G → ℂ} {F₀ F : Lp ℂ 2 ((μ.restrict 𝓕).map π)}
    (hφ : Continuous φ) (hφΓ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (hφ0 : ∀ g, ∫ z, φ (j z * g) ∂m = 0)
    (hF₀ : ∀ᵐ x ∂μ, F₀ (π x) = φ x)
    (hψ : Continuous ψ) (hψΓ : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (hF : ∀ᵐ x ∂μ, F (π x) = ψ x)
    (hcl : F ∈ closure (Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀} : Set (Lp ℂ 2 ((μ.restrict 𝓕).map π))))
    (g₀ : G) : ∫ z, ψ (j z * g₀) ∂m = 0 := by
  have hms : m.restrict s = m := Measure.restrict_eq_self_of_ae_mem hm
  have hint : ∀ h : G → ℂ, Continuous h → ∀ g, Integrable (fun z => h (j z * g)) m := by
    intro h hh g
    rw [← hms]
    exact (hh.comp (hj.mul continuous_const)).continuousOn.integrableOn_compact hs
  have hspan : ∀ H ∈ Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀}, ∃ h : G → ℂ, Continuous h ∧
      (∀ γ ∈ Γ, ∀ g, h (γ * g) = h g) ∧ (∀ g, ∫ z, h (j z * g) ∂m = 0) ∧ ∀ᵐ x ∂μ.restrict 𝓕, H (π x) = h x := by
    intro H hH
    induction hH using Submodule.span_induction with
    | mem H hH =>
      obtain ⟨u, rfl⟩ := hH
      refine ⟨fun x => φ (x * u), hφ.comp (continuous_id.mul continuous_const), fun γ hγ g => ?_, fun g => ?_,
        ae_restrict_of_ae ?_⟩
      · simp only [mul_assoc, hφΓ γ hγ]
      · simp only [mul_assoc, hφ0]
      · filter_upwards [hρ u F₀, (measurePreserving_mul_right μ u).quasiMeasurePreserving.ae hF₀] with x h1 h2
        rw [h1, h2]
    | zero =>
      refine ⟨0, continuous_const, fun _ _ _ => rfl, fun g => by simp, ?_⟩
      exact ae_of_ae_map hπ.aemeasurable (Lp.coeFn_zero ℂ 2 _)
    | add H H' _ _ h1 h2 =>
      obtain ⟨h, hc, hi, h0, ha⟩ := h1
      obtain ⟨h', hc', hi', h0', ha'⟩ := h2
      refine ⟨h + h', hc.add hc', fun γ hγ g => by simp only [Pi.add_apply, hi γ hγ, hi' γ hγ], fun g => ?_, ?_⟩
      · simp only [Pi.add_apply]
        rw [integral_add (hint h hc g) (hint h' hc' g), h0, h0', add_zero]
      · filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_add H H'), ha, ha'] with x e1 e2 e3
        rw [e1, Pi.add_apply, Pi.add_apply, e2, e3]
    | smul a H _ h1 =>
      obtain ⟨h, hc, hi, h0, ha⟩ := h1
      refine ⟨a • h, hc.const_smul a, fun γ hγ g => by simp only [Pi.smul_apply, hi γ hγ], fun g => ?_, ?_⟩
      · simp only [Pi.smul_apply]
        rw [integral_smul, h0, smul_zero]
      · filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_smul a H), ha] with x e1 e2
        rw [e1, Pi.smul_apply, Pi.smul_apply, e2]
  obtain ⟨Ω, hΩ, hg₀⟩ := exists_compact_mem_nhds g₀
  have hK : IsCompact (j '' s) := hs.image hj
  obtain ⟨N, hN⟩ := exists_lintegral_le Γ μ h𝓕 (hK.mul hΩ)
  set c : ℝ≥0∞ := m Set.univ * (N * μ 𝓕 ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) with hc
  have hc' : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_)
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hfin
    norm_num
  have hbd : ∀ H ∈ (Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀} : Set (Lp ℂ 2 ((μ.restrict 𝓕).map π))),
      ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - H‖ₑ := by
    intro H hH
    obtain ⟨h, hh, hi, h0, ha⟩ := hspan H hH
    have hd : Continuous (ψ - h) := hψ.sub hh
    have e1 : ∀ g, ∫ z, ψ (j z * g) ∂m = ∫ z, (ψ - h) (j z * g) ∂m := by
      intro g
      simp only [Pi.sub_apply]
      rw [integral_sub (hint ψ hψ g) (hint h hh g), h0, sub_zero]
    simp only [e1]
    refine (lintegral_average_le μ m hj.measurable hΩ (K := j '' s)
      (hm.mono fun z hz => Set.mem_image_of_mem j hz) hd).trans ?_
    rw [hc, mul_assoc, mul_assoc]
    refine mul_le_mul_right ((hN _ hd.enorm.measurable fun γ hγ g => ?_).trans (mul_le_mul_right ?_ _)) _
    · simp only [Pi.sub_apply, hψΓ γ hγ, hi γ hγ]
    · rw [← eLpNorm_one_eq_lintegral_enorm]
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (q := 2) one_le_two hd.aestronglyMeasurable).trans ?_
      rw [Measure.restrict_apply_univ, mul_comm, Lp.enorm_def,
        eLpNorm_map_measure (Lp.aestronglyMeasurable _) hπ.aemeasurable]
      refine le_of_eq (congrArg _ (eLpNorm_congr_ae ?_))
      filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_sub F H), ha, ae_restrict_of_ae hF] with x e1 e2 e3
      rw [Function.comp_apply, e1, Pi.sub_apply, Pi.sub_apply, e2, e3]
      exact hd.aestronglyMeasurable
  have hz : ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ = 0 := by
    have hcont : Continuous fun H : Lp ℂ 2 ((μ.restrict 𝓕).map π) => c * ‖F - H‖ₑ :=
      (ENNReal.continuous_const_mul hc').comp (continuous_const.sub continuous_id).enorm
    have : ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - F‖ₑ :=
      closure_minimal (t := {H | ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - H‖ₑ}) hbd
        (isClosed_le continuous_const hcont) hcl
    simpa using this
  have hC : Continuous fun g => ∫ z, ψ (j z * g) ∂m := by
    have := continuous_parametric_integral_of_continuous (μ := m) (f := fun g z => ψ (j z * g))
      (hψ.comp ((hj.comp continuous_snd).mul continuous_fst)) hs
    rwa [hms] at this
  rw [lintegral_eq_zero_iff hC.enorm.measurable] at hz
  have hz' : (fun g => ∫ z, ψ (j z * g) ∂m) =ᵐ[μ.restrict (interior Ω)] fun _ => 0 := by
    refine ae_restrict_of_ae_restrict_of_subset interior_subset (hz.mono fun g hg => ?_)
    simpa using hg
  exact Measure.eqOn_open_of_ae_eq hz' isOpen_interior hC.continuousOn continuousOn_const
    (mem_interior_iff_mem_nhds.2 hg₀)

end Abstract

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem zcusp_of_mem_closure : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (φ ψ : GA D V → ℂ) F₀ F, IsAutFun V φ → ZCusp V φ → Repr V μ 𝓕 F₀ φ → IsAutFun V ψ → Repr V μ 𝓕 F ψ → F ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set (Lp ℂ 2 (nuQ V μ 𝓕))) → ZCusp V ψ := by
  intro D θ V hθ μ 𝓕 ρ hP hρ φ ψ F₀ F hφ hφ0 hF₀ hψ hF hcl ξ hξ ν 𝓖 hν h𝓖 g
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨ν₀, 𝓖₀, hν₀, h𝓖₀, hc⟩ := (GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ ξ hξ).1
  have hZ : IsClosed (ZI V ξ : Set (GA D V)) := (GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed D θ V hθ ξ hξ).2.1
  haveI : LocallyCompactSpace (ZI V ξ) := hZ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Countable ((GQ V).subgroupOf (ZI V ξ)) :=
    Function.Injective.countable (f := fun x : (GQ V).subgroupOf (ZI V ξ) => (⟨x.1.1, x.2⟩ : GQ V))
      fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : GQ V => (t : GA D V)) h))
  haveI : SecondCountableTopology (ZI V ξ) := TopologicalSpace.Subtype.secondCountableTopology (ZI V ξ : Set (GA D V))
  have h₁ : IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓖₀ ν :=
    h𝓖₀.mono (Measure.absolutelyContinuous_isHaarMeasure ν ν₀)
  haveI := hP.haar
  haveI := hP.right
  haveI : IsFiniteMeasure (ν.restrict 𝓖₀) :=
    isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hc.measure_lt_top).ne
  rw [h𝓖.setIntegral_eq h₁ (f := fun z : ZI V ξ => ψ ((z : GA D V) * g)) fun γ z => by
    have := hψ.left γ.1.1 γ.2 (z.1 * g)
    rw [← mul_assoc] at this
    exact this]
  exact average_eq_zero_of_mem_closure (GQ V) μ hP.fd hP.fin (π := autMk V) measurable_quotient_mk'' (fun u H => ρ u H)
    hρ.val (ν.restrict 𝓖₀) continuous_subtype_val hc
    ((ae_restrict_mem₀ h₁.nullMeasurableSet).mono fun z hz => subset_closure hz)
    hφ.cont hφ.left (hφ0 ξ hξ ν 𝓖₀ hν h₁) hF₀ hψ.cont hψ.left hF hcl g

end GlobalTheory.HolDict.ZClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalityPreservedInClosureStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidality_preserved_in_closure : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (φ ψ : GA D V → ℂ) F₀ F, IsAutFun V φ → ZCusp V φ → Repr V μ 𝓕 F₀ φ → IsAutFun V ψ → Repr V μ 𝓕 F ψ → F ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set (Lp ℂ 2 (nuQ V μ 𝓕))) → ZCusp V ψ := by
  first | exact @GlobalTheory.HolDict.ZClosed.zcusp_of_mem_closure | exact GlobalTheory.HolDict.ZClosed.zcusp_of_mem_closure | (intros; apply GlobalTheory.HolDict.ZClosed.zcusp_of_mem_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSkewHermitianCm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSkewHermitianCm
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section
namespace GlobalTheory.PlaneSkew

theorem exists_re_pos_of_congr_diagonal {n : ℕ} (H Q : Matrix (Fin n) (Fin n) ℂ) (δ : Fin n → ℂ)
    (hQ : Q.det ≠ 0) (hd : Qᵀ * H * Q.map star = Matrix.diagonal δ)
    (u : Fin n → ℂ) (hu : 0 < (u ⬝ᵥ H *ᵥ star u).re) : ∃ i, 0 < (δ i).re := by
  by_contra hneg
  push_neg at hneg
  obtain ⟨v, rfl⟩ : ∃ v, Q *ᵥ v = u :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr hQ)) u
  have hs : star (Q *ᵥ v) = Q.map star *ᵥ star v := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  have key : (Q *ᵥ v) ⬝ᵥ H *ᵥ star (Q *ᵥ v) = v ⬝ᵥ (Qᵀ * H * Q.map star) *ᵥ star v := by
    rw [hs, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Qᵀ,
      Matrix.vecMul_transpose]
  rw [key, hd] at hu
  have h2 : v ⬝ᵥ Matrix.diagonal δ *ᵥ star v = ∑ i, δ i * (Complex.normSq (v i) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp [Pi.star_apply]
    ring
  rw [h2, Complex.re_sum] at hu
  refine hu.not_ge (Finset.sum_nonpos fun i _ => ?_)
  rw [Complex.re_mul_ofReal]
  exact mul_nonpos_of_nonpos_of_nonneg (hneg i) (Complex.normSq_nonneg _)

theorem exists_algebraMap_eq_of_fixed {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (σ : E →ₐ[F] E) {ξ : E} (hξ0 : ξ ≠ 0) (hξ : σ ξ = -ξ) {e : E}
    (he : σ e = e) : ∃ a : F, algebraMap F E a = e := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  set V : Submodule F E := LinearMap.ker (σ.toLinearMap - LinearMap.id) with hV
  have mem : ∀ x, x ∈ V ↔ σ x = x := fun x => by
    simp [hV, sub_eq_zero]
  have hle : Submodule.span F {(1 : E)} ≤ V := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem, map_one]
  have hne : V ≠ ⊤ := by
    intro htop
    have : ξ ∈ V := htop ▸ Submodule.mem_top
    rw [mem, hξ] at this
    have h2' : (2 : E) * ξ = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h2' with h | h
    · exact two_ne_zero h
    · exact hξ0 h
  have hlt := Submodule.finrank_lt hne
  have h1 : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have : e ∈ Submodule.span F {(1 : E)} := heq ▸ (mem e).mpr he
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
  exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one, ha]⟩

theorem re_embedding_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E]
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (τ : E →+* ℂ) (a : F) :
    (τ (algebraMap F E a)).re =
      ((emb (InfinitePlace.mk (τ.comp (algebraMap F E)))).1 (algebraMap F E a)).re := by
  have h1 := congrArg (fun f : F →+* ℂ => f a) (emb (InfinitePlace.mk (τ.comp (algebraMap F E)))).2
  simp only [RingHom.comp_apply] at h1
  rw [h1]
  rcases InfinitePlace.embedding_mk_eq (τ.comp (algebraMap F E)) with h | h
  · rw [h, RingHom.comp_apply]
  · rw [h, ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, Complex.conj_re]

theorem exists_isotropic_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r s : ℕ), (∀ i j, σ (J j i) = -J i j) →
    (∀ w, HasSig (Complex.I • J.map (B.emb w).1) r s) → 1 ≤ r → 1 ≤ s → 3 ≤ n →
    ∃ x : Fin n → E, x ≠ 0 ∧ form σ J x x = 0 := by
  intro F E _ _ _ _ _ σ B hcm n J r s hJ hsig hr hs hn
  obtain ⟨hTR, hTC, h2, hconj⟩ := hcm
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ x, σ (σ x) = x := fun x => τ₀.injective (by rw [hconj, hconj, star_star])
  by_cases hd : J.det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    refine ⟨fun i => σ (v i), fun h => hv0 (funext fun i => ?_), ?_⟩
    · have := congrArg σ (congrFun h i)
      simpa [hσσ] using this
    · have : (fun i => σ ((fun i => σ (v i)) i)) = v := funext fun i => hσσ _
      simp only [form]
      rw [this, hv, dotProduct_zero]
  haveI := hTR
  haveI := hTC
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ a, σ a = IsCMField.complexConj E a := fun a =>
    τ₀.injective (by rw [hconj, IsCMField.complexEmbedding_complexConj]; rfl)
  obtain ⟨x₀, hx₀⟩ : ∃ x, σ x ≠ x := by
    by_contra hno
    push_neg at hno
    apply IsCMField.complexConj_ne_one E
    ext x
    rw [← hcc, hno]
    rfl
  set ξ := x₀ - σ x₀ with hξdef
  have hξ : σ ξ = -ξ := by rw [hξdef, map_sub, hσσ]; ring
  have hξ0 : ξ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx₀)
  set G : Matrix (Fin n) (Fin n) E := ξ • J with hG
  have hform : ∀ x, GlobalTheory.UTrans.hf (σ : E →+* E) G x x = ξ * form σ J x x := fun x => by
    simp only [GlobalTheory.UTrans.hf, form, dotProduct, Matrix.mulVec, hG, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [AlgHom.coe_toRingHom]
    ring
  have hherm : GlobalTheory.UTrans.IsHerm (σ : E →+* E) G :=
    { invol := hσσ
      ne_id := ⟨x₀, hx₀⟩
      herm := fun a b => by
        simp only [AlgHom.coe_toRingHom, hG, Matrix.smul_apply, smul_eq_mul, map_mul, hξ, hJ]
        ring
      det_ne := by
        rw [hG, Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ hξ0) hd }
  have hh : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a := fun a b => by
    rw [← hherm.herm a b]
    simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, AlgHom.coe_toRingHom, hcc]
  obtain ⟨P, d, hP, hPg, hdfix, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hh
  have hPg' : Pᵀ * G * P.map σ = Matrix.diagonal d := by
    rw [← hPg]; congr 2; ext a b; simp [ReciprocityTheory.ChartRestriction.G.FD.cc, hcc]
  have hdσ : ∀ i, σ (d i) = d i := fun i => by
    rw [hcc]; exact hdfix i
  have hdiag : ∀ i, GlobalTheory.UTrans.hf (σ : E →+* E) G (fun a => P a i) (fun a => P a i) = d i := fun i => by
    have := congrFun (congrFun hPg' i) i
    rw [Matrix.diagonal_apply_eq] at this
    rw [← this]
    simp only [GlobalTheory.UTrans.hf, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Finset.sum_mul, AlgHom.coe_toRingHom]
    exact Finset.sum_comm

  have hsignE : ∀ w : InfinitePlace F,
      (∃ i, 0 < ((B.emb w).1 (d i)).re) ∧ ∃ j, ((B.emb w).1 (d j)).re < 0 := by
    intro w
    set φ : E →+* ℂ := (B.emb w).1 with hφ
    obtain ⟨hrs, A, hA⟩ := hsig w
    have hφσ : ∀ x, φ (σ x) = star (φ x) := hconj φ
    have hQ : (P.map φ).det ≠ 0 := by
      have h := RingHom.map_det φ P
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero φ).mpr hP
    have hdQ : (P.map φ)ᵀ * G.map φ * (P.map φ).map star = Matrix.diagonal (fun i => φ (d i)) := by
      have e1 : (P.map φ).map star = (P.map σ).map φ := by
        ext a b
        simp [hφσ]
      rw [e1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPg',
        Matrix.diagonal_map (map_zero φ)]
    set c : ℂ := -Complex.I * φ ξ with hc
    have hGM : G.map φ = c • (Complex.I • J.map φ) := by
      ext a b
      simp only [hG, hc, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      linear_combination (φ ξ * φ (J a b)) * Complex.I_sq
    have hcol : ∀ k, (fun a => A a k) ⬝ᵥ G.map φ *ᵥ star (fun a => A a k) =
        c * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) k k := by
      intro k
      rw [← hA, hGM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct,
        Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hφξ : (φ ξ).re = 0 := by
      have h1 := congrArg Complex.re (hφσ ξ)
      rw [hξ, map_neg, Complex.neg_re, Complex.star_def, Complex.conj_re] at h1
      linarith
    have hφξ0 : (φ ξ).im ≠ 0 := by
      intro him
      apply hξ0
      apply φ.injective
      rw [map_zero]
      exact Complex.ext hφξ him
    have hcre : c.re = (φ ξ).im := by simp [hc, hφξ]
    have pos : ∀ u, 0 < (u ⬝ᵥ G.map φ *ᵥ star u).re → ∃ i, 0 < (φ (d i)).re :=
      fun u hu => exists_re_pos_of_congr_diagonal _ _ _ hQ hdQ u hu
    have neg : ∀ u, (u ⬝ᵥ G.map φ *ᵥ star u).re < 0 → ∃ i, (φ (d i)).re < 0 := fun u hu => by
      obtain ⟨i, hi⟩ := exists_re_pos_of_congr_diagonal (-(G.map φ)) _ (fun i => -φ (d i)) hQ
        (by rw [Matrix.mul_neg, Matrix.neg_mul, hdQ, Matrix.diagonal_neg]) u
        (by rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]; linarith)
      exact ⟨i, by simpa using hi⟩
    have v1 := hcol (Sum.inl ⟨0, by omega⟩)
    have v2 := hcol (Sum.inr ⟨0, by omega⟩)
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq,
      Matrix.neg_apply, mul_one, mul_neg] at v1 v2
    rcases lt_or_gt_of_ne hφξ0 with h | h
    · exact ⟨pos _ (by rw [v2, Complex.neg_re, hcre]; linarith),
        neg _ (by rw [v1, hcre]; exact h)⟩
    · exact ⟨pos _ (by rw [v1, hcre]; exact h),
        neg _ (by rw [v2, Complex.neg_re, hcre]; linarith)⟩
  have hre : ∀ (τ : E →+* ℂ) i, (τ (d i)).re =
      ((B.emb (InfinitePlace.mk (τ.comp (algebraMap F E)))).1 (d i)).re := fun τ i => by
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_fixed h2 σ hξ0 hξ (hdσ i)
    rw [← ha]
    exact re_embedding_algebraMap B.emb τ a
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.UTrans.exists_isotropic_of_indefinite E n (σ : E →+* E) G
    (fun a => hcc a) hherm hn (fun τ => by
      obtain ⟨⟨i, hi⟩, j, hj⟩ := hsignE (InfinitePlace.mk (τ.comp (algebraMap F E)))
      exact ⟨⟨_, by rw [hdiag, hre]; exact hi⟩, _, by rw [hdiag, hre]; exact hj⟩)
  refine ⟨z, hz0, ?_⟩
  rw [hform] at hz
  exact (mul_eq_zero.mp hz).resolve_left hξ0

end GlobalTheory.PlaneSkew
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSkewHermitianCmStatement
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_indefinite_skewHermitian_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r s : ℕ), (∀ i j, σ (J j i) = -J i j) →
    (∀ w, HasSig (Complex.I • J.map (B.emb w).1) r s) → 1 ≤ r → 1 ≤ s → 3 ≤ n →
    ∃ x : Fin n → E, x ≠ 0 ∧ form σ J x x = 0 := by
  first | exact @GlobalTheory.PlaneSkew.exists_isotropic_skew | exact GlobalTheory.PlaneSkew.exists_isotropic_skew | (intros; apply GlobalTheory.PlaneSkew.exists_isotropic_skew <;> assumption)
end
end
