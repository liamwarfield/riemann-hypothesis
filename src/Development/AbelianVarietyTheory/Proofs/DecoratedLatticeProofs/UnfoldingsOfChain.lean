module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingEvaluationIntegrandContinuousInva
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatPeriodEqIntegralEvaluationPeriods
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfWeilDatumDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfDoubleStepLastTwoSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfDoubleStepLastTwoSteps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.IterProof

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem rTrans_lift {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (s : Step ψ V V₀ W W₀ ρ σ) (G : GA D W → ℂ) (Φ : WO V W → ℂ)
    (g : GA D V) : rTrans g (s.lift G Φ) = s.lift G (s.om (g, 1) Φ) := by
  funext x
  have key : ∀ h, s.om (x * g, h) Φ = s.om (x, h) (s.om (g, 1) Φ) := by
    intro h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [rTrans, Step.lift, liftS_apply, key]

end GlobalTheory.Unf.IterProof


open GlobalTheory.Unf.IterProof in
theorem GlobalTheory.Unf.iter_of_doubleStep_lastLaw : ∀ D : D7, DoubleStep D → LastLaw D → IT D := by
  intro D hD hL ψ T ρ B c
  induction c with
  | @last B t =>
    intro Φ F φ g hΦ hF hφ _
    show B.per ψ φ (rTrans g (t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ.2) Φ.1)) =
      t.Q φ (t.s.om (g, 1) Φ.1) Φ.2 F
    rw [rTrans_lift]
    exact hL ψ T B t φ _ Φ.2 F hφ hF (t.s.weil.om_pres _ _ hΦ.1) hΦ.2
  | @step σ B J B' s₁ s₂ l vL c ih =>
    intro Φ F φ g hΦ hF hφ hR
    obtain ⟨hR₁, hR₂, hR₃⟩ := hR
    obtain ⟨hΦ₁, hΦ₂, hΦ₃⟩ := hΦ
    obtain ⟨hcont, f₁, h₁, h₂⟩ := hD ψ σ B J B' s₁ s₂ l vL Φ.1 Φ.2.1 φ (c.down Φ.2.2 F) g hΦ₁ hΦ₂ hφ hR₂ hR₁
    refine ⟨f₁, fun a b => B'.per ψ (Chain.hand s₁ s₂ l vL Φ.1 Φ.2.1 φ g a b) (rTrans b (c.down Φ.2.2 F)), h₁,
      fun a => ⟨h₂ a, fun b => ?_⟩⟩
    exact ih Φ.2.2 F _ b hΦ₃ hF (hcont a b) hR₃
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfDoubleStepLastTwoStepsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedThetaUnfolding_of_doubleStep_lastTwoSteps : ∀ D : D7, DoubleStep D → LastLaw D → IT D := by
  first | exact @GlobalTheory.Unf.iter_of_doubleStep_lastLaw | exact GlobalTheory.Unf.iter_of_doubleStep_lastLaw | (intros; apply GlobalTheory.Unf.iter_of_doubleStep_lastLaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfWeilDatumDescent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem GlobalTheory.Unf.iteratedUnfolding_of_descent : ∀ D : D7, Descent D → IT D :=
  fun D hD => GlobalTheory.T.iteratedThetaUnfolding_of_doubleStep_lastTwoSteps D (GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent D hD) (GlobalTheory.T.doubleLiftPeriod_rankZero_fubini_compactQuotient D)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfWeilDatumDescentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedThetaUnfolding_of_weilDatumDescent : ∀ D : D7, Descent D → IT D := by
  first | exact @GlobalTheory.Unf.iteratedUnfolding_of_descent | exact GlobalTheory.Unf.iteratedUnfolding_of_descent | (intros; apply GlobalTheory.Unf.iteratedUnfolding_of_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodEvaluationUnfoldingOfWittDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvaluationFormAbsoluteConvergence
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsQuotientIntegrableFoldUnimodular
open MeasureTheory GlobalTheory.Grow GlobalTheory.Tw
open scoped ENNReal

namespace GlobalTheory.EvalAbs

theorem lintegral_eq_of_integral {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {m₁ : Measure α} {m₂ : Measure β} {a : α → γ} {b : β → γ} (ha : Measurable a) (hb : Measurable b)
    (h : ∀ f : γ → ℂ, Measurable f → (Integrable (fun x => f (a x)) m₁ ↔ Integrable (fun y => f (b y)) m₂) ∧
      (Integrable (fun y => f (b y)) m₂ → ∫ x, f (a x) ∂m₁ = ∫ y, f (b y) ∂m₂))
    (F : γ → ℝ≥0∞) (hF : Measurable F) : ∫⁻ x, F (a x) ∂m₁ = ∫⁻ y, F (b y) ∂m₂ := by
  have e : m₁.map a = m₂.map b := by
    ext A hA
    rw [Measure.map_apply ha hA, Measure.map_apply hb hA]
    obtain ⟨h1, h2⟩ := h (A.indicator fun _ => 1) (measurable_const.indicator hA)
    have e1 : (fun x => A.indicator (fun _ => (1 : ℂ)) (a x)) = (a ⁻¹' A).indicator fun _ => 1 := rfl
    have e2 : (fun x => A.indicator (fun _ => (1 : ℂ)) (b x)) = (b ⁻¹' A).indicator fun _ => 1 := rfl
    rw [e1, e2, integrable_indicator_iff (ha hA), integrable_indicator_iff (hb hA), integrableOn_const_iff,
      integrableOn_const_iff] at h1
    rw [e1, e2, integrable_indicator_iff (hb hA), integrableOn_const_iff, integral_indicator (ha hA),
      integral_indicator (hb hA)] at h2
    simp only [enorm_eq_zero, one_ne_zero, false_or, integral_const, MeasurableSet.univ, measureReal_restrict_apply,
      Set.univ_inter, Complex.real_smul, mul_one, Complex.ofReal_inj] at h1 h2
    by_cases hf : m₂ (b ⁻¹' A) < ∞
    · exact (ENNReal.toReal_eq_toReal_iff' (h1.2 hf).ne hf.ne).1 (h2 hf)
    · rw [not_lt_top_iff.1 hf, not_lt_top_iff.1 (fun h' => hf (h1.1 h'))]
  rw [← lintegral_map hF ha, e, lintegral_map hF hb]

theorem setLIntegral_mul_right {R : Type} [Group R] [MeasurableSpace R] [MeasurableMul R] {μ : Measure R}
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Γ : Subgroup R} [Countable Γ] {𝓡 : Set R}
    (h : IsFundamentalDomain Γ 𝓡 μ) (q : R → ℝ≥0∞) (hq : ∀ γ ∈ Γ, ∀ r, q (γ * r) = q r) (m : R) :
    ∫⁻ r in 𝓡, q (r * m) ∂μ = ∫⁻ r in 𝓡, q r ∂μ := by
  have hp : MeasurePreserving (· * m) μ μ := measurePreserving_mul_right μ m
  have h2 : IsFundamentalDomain Γ ((· * m) ⁻¹' 𝓡) μ :=
    h.preimage_of_equiv hp.quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  rw [h.setLIntegral_eq h2 (fun r => q (r * m)) fun γ r => by
    rw [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hq _ γ.2 _]
  exact hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.mulRight m).measurableEmbedding q 𝓡

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {R Γ : Subgroup G} {μR : Measure R} [μR.IsHaarMeasure] [μR.IsInvInvariant] {𝓡 : Set R} {𝓑 : Set G}

theorem exists_quotientIntegrable_of_le_mean (hΓR : Γ ≤ R) (hR : IsClosed (R : Set G)) [Countable Γ] [DiscreteTopology Γ]
    (h𝓡 : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR) (h𝓑 : IsFundamentalDomain Γ 𝓑 μ) {K : G → ℝ≥0∞}
    (hK : Measurable K) (hKΓ : ∀ γ ∈ Γ, ∀ g, K (γ * g) = K g) (hfin : ∫⁻ g in 𝓑, K g ∂μ < ∞) {f : G → ℂ}
    (hf : Measurable f) (hfR : ∀ r ∈ R, ∀ g, f (r * g) = f g) (hle : ∀ h, ‖f h‖ₑ ≤ ∫⁻ r in 𝓡, K (r * h) ∂μR) :
    ∃ z, IsQuotIntL1 μR μ f z := by
  refine ⟨_, (isQuotIntL1_iff hR hf).2 ⟨hfR, ⟨(measurable_comp_out hf hfR).aestronglyMeasurable, ?_⟩, rfl⟩⟩
  obtain ⟨S, hSm, hS⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hSfd : IsFundamentalDomain Γ S μ := IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  have hSh : ∀ h : G, MeasurableSet {r : R | (r : G) * h ∈ S} := fun h =>
    (continuous_subtype_val.mul continuous_const).measurable hSm
  have e : ∀ h : G, ∫⁻ r in 𝓡, K (r * h) ∂μR = ∫⁻ r : R, S.indicator K (r * h) ∂μR := fun h => by
    have hfd : IsFundamentalDomain (Γ.subgroupOf R) {r : R | (r : G) * h ∈ S} μR :=
      IsFundamentalDomain.mk' (hSh h).nullMeasurableSet (GlobalTheory.QuotDiscrete.existsUnique_subgroupOf hΓR hS h)
    rw [h𝓡.setLIntegral_eq hfd (fun r : R => K (r * h)) fun γ r => by
      change K ((((γ : R) : G) * r) * h) = _
      rw [mul_assoc]; exact hKΓ _ γ.2 _, ← lintegral_indicator (hSh h)]
    rfl
  calc ∫⁻ c, ‖f (Quotient.out c)‖ₑ ∂quotMeas R μ μR
      ≤ ∫⁻ c, ∫⁻ r : R, S.indicator K (r * Quotient.out c) ∂μR ∂quotMeas R μ μR :=
        lintegral_mono fun c => (hle _).trans (e _).le
    _ = ∫⁻ g, S.indicator K g ∂μ := (isQuotMeasure_quotMeas hR _ (hK.indicator hSm)).symm
    _ = ∫⁻ g in 𝓑, K g ∂μ := by
        rw [lintegral_indicator hSm]
        exact hSfd.setLIntegral_eq h𝓑 K fun γ x => hKΓ _ γ.2 x
    _ < ∞ := hfin

theorem exists_quotientIntegrable_fold_unimodular (hΓR : Γ ≤ R) (hR : IsClosed (R : Set G)) [Countable Γ] [DiscreteTopology Γ]
    (h𝓡 : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR) (h𝓑 : IsFundamentalDomain Γ 𝓑 μ)
    {U : Type} [Group U] [MeasurableSpace U] [MeasurableMul U] [MeasurableInv U] {ν : Measure U} [SFinite ν]
    [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (j : U →* G) (hj : Measurable j) (hjR : ∀ u, j u ∈ R)
    {q : G → G → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (hqΓ : ∀ γ ∈ Γ, ∀ g, ∀ r ∈ R, q (γ * g) (γ * r) = q g r)
    (hqR : ∀ r ∈ R, ∃ v, ∀ g u, q g (r * j u) = q g (j (v * u)))
    (hfin : ∫⁻ g in 𝓑, ∫⁻ u, q g (j u) ∂ν ∂μ < ∞) {P : G → ℂ} (hP : Measurable P)
    (hPR : ∀ r ∈ R, ∃ v, ∀ g u, P (j u * (r * g)) = P (j (u * v) * g))
    (hle : ∀ h, ‖P h‖ₑ ≤ ∫⁻ r in 𝓡, q (r * h) r ∂μR) :
    ∃ z, IsQuotIntL1 μR μ (fun h => ((∫ u, ‖P (j u * h)‖ ∂ν : ℝ) : ℂ)) z := by
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  have : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  have : ν.IsMulRightInvariant := by rw [← Measure.inv_eq_self ν]; infer_instance
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hU : ∀ r ∈ R, ∀ g, ∫⁻ u, q g (r * j u) ∂ν = ∫⁻ u, q g (j u) ∂ν := fun r hr g => by
    obtain ⟨v, hv⟩ := hqR r hr
    simp only [hv]
    exact lintegral_mul_left_eq_self (fun u => q g (j u)) v
  refine exists_quotientIntegrable_of_le_mean hΓR hR h𝓡 h𝓑 (K := fun g => ∫⁻ u, q g (j u) ∂ν) ?_ (fun γ hγ g => ?_) hfin ?_
    (fun r hr g => ?_) fun h => ?_
  · exact (hq.comp (measurable_fst.prodMk (hj.comp measurable_snd))).lintegral_prod_right'
  · rw [← hU γ⁻¹ (inv_mem (hΓR hγ)) g]
    refine lintegral_congr fun u => ?_
    rw [← hqΓ γ hγ g _ (mul_mem (inv_mem (hΓR hγ)) (hjR u)), mul_inv_cancel_left]
  · refine Complex.measurable_ofReal.comp (StronglyMeasurable.measurable ?_)
    exact (hP.comp ((hj.comp measurable_snd).mul measurable_fst)).norm.stronglyMeasurable.integral_prod_right'
  · obtain ⟨v, hv⟩ := hPR r hr
    simp only [hv]
    rw [integral_mul_right_eq_self (fun u => ‖P (j u * g)‖) v]
  · have hm : Measurable fun p : U × R => q (p.2 * h) (p.2 * j p.1⁻¹) :=
      hq.comp (((measurable_subtype_coe.comp measurable_snd).mul_const h).prodMk
        ((measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst.inv)))
    calc ‖((∫ u, ‖P (j u * h)‖ ∂ν : ℝ) : ℂ)‖ₑ = ‖∫ u, ‖P (j u * h)‖ ∂ν‖ₑ := by
          simp [eNorm_eq_nnNorm]
      _ ≤ ∫⁻ u, ‖‖P (j u * h)‖‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ u, ∫⁻ r in 𝓡, q (r * h) (r * j u⁻¹) ∂μR ∂ν := by
          refine lintegral_mono fun u => ?_
          rw [enorm_norm]
          refine (hle _).trans (le_of_eq ?_)
          rw [← setLIntegral_mul_right h𝓡 (fun r : R => q (r * h) (r * j u⁻¹)) (fun γ hγ r => by
            simp only [Subgroup.coe_mul, mul_assoc]
            exact hqΓ _ hγ _ _ (mul_mem r.2 (hjR _))) ⟨j u, hjR u⟩]
          simp only [Subgroup.coe_mul, mul_assoc, map_inv, mul_inv_cancel, mul_one]
      _ = ∫⁻ r in 𝓡, ∫⁻ u, q (r * h) (r * j u⁻¹) ∂ν ∂μR := lintegral_lintegral_swap hm.aemeasurable
      _ = _ := by
          refine lintegral_congr fun r => ?_
          rw [lintegral_inv_eq_self (μ := ν) fun u => q (r * h) (r * j u), hU r r.2]

end

end GlobalTheory.EvalAbs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvaluationFormAbsoluteConvergence
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.EvalAbs

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem sFinite_of_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] : SFinite μ := inferInstance

theorem lintegral_three_lt_top {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {κ : Measure γ} [SFinite μ] [SFinite ν] [SFinite κ] {φ : α → ℂ} {G : β → ℂ}
    {E : α → β → γ → ℂ} (hφ : Measurable φ) (hG : Measurable G) (hE : Measurable fun p : α × β × γ => E p.1 p.2.1 p.2.2)
    (hi : Integrable φ μ) {M : ℝ} (hM : ∀ a, ∫⁻ b, ‖G b‖ₑ * ∫⁻ c, ‖E a b c‖ₑ ∂κ ∂ν ≤ ENNReal.ofReal M) :
    ∫⁻ b, ∫⁻ c, ‖G b‖ₑ * ∫⁻ a, ‖φ a‖ₑ * ‖E a b c‖ₑ ∂μ ∂κ ∂ν < ∞ := by
  have hm : Measurable fun p : (β × γ) × α => ‖φ p.2‖ₑ * (‖G p.1.1‖ₑ * ‖E p.2 p.1.1 p.1.2‖ₑ) :=
    (hφ.comp measurable_snd).enorm.mul ((hG.comp (measurable_fst.comp measurable_fst)).enorm.mul
      (hE.comp (measurable_snd.prodMk measurable_fst)).enorm)
  calc ∫⁻ b, ∫⁻ c, ‖G b‖ₑ * ∫⁻ a, ‖φ a‖ₑ * ‖E a b c‖ₑ ∂μ ∂κ ∂ν
      = ∫⁻ b, ∫⁻ c, ∫⁻ a, ‖φ a‖ₑ * (‖G b‖ₑ * ‖E a b c‖ₑ) ∂μ ∂κ ∂ν := by
        refine lintegral_congr fun b => lintegral_congr fun c => ?_
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        exact lintegral_congr fun a => mul_left_comm _ _ _
    _ = ∫⁻ p : β × γ, ∫⁻ a, ‖φ a‖ₑ * (‖G p.1‖ₑ * ‖E a p.1 p.2‖ₑ) ∂μ ∂ν.prod κ :=
        (lintegral_prod _ hm.lintegral_prod_right'.aemeasurable).symm
    _ = ∫⁻ a, ∫⁻ p : β × γ, ‖φ a‖ₑ * (‖G p.1‖ₑ * ‖E a p.1 p.2‖ₑ) ∂ν.prod κ ∂μ := lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ a, ‖φ a‖ₑ * ENNReal.ofReal M ∂μ := by
        refine lintegral_mono fun a => ?_
        have h1 : Measurable fun p : β × γ => ‖G p.1‖ₑ * ‖E a p.1 p.2‖ₑ :=
          (hG.comp measurable_fst).enorm.mul (hE.comp measurable_prodMk_left).enorm
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_prod _ h1.aemeasurable]
        simp only [lintegral_const_mul' _ _ enorm_ne_top]
        exact mul_le_mul_right (hM a) _
    _ < ∞ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top hi.2 ENNReal.ofReal_lt_top

theorem norm_theta_add (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : WO S T}
    (hγ : γ ∈ ratMx D T.rank S.rank) (w : WO S T) : ‖f (γ + w)‖ = ‖f w‖ := by
  obtain ⟨δ, rfl⟩ := hγ
  have h := hf.quasi δ w
  rw [show f ((incA D).toAddMonoidHom.mapMatrix δ + w) = _ from h, norm_mul, hψ.1.2.1, one_mul]

theorem yZero_mem (S : HSp D) (ρ : ℕ) (z : Fin S.rank → D.host.E) : yZero S ρ z ∈ ratMx D S.rank ρ := by
  refine neg_mem (mem_ratMx.2 ⟨vecMulVec z fun i => if i.1 + 1 = ρ then 1 else 0, ?_⟩)
  funext i j
  change incA D (z i * if j.1 + 1 = ρ then 1 else 0) = incA D (z i) * ell D ρ j
  unfold ell
  split_ifs
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, map_zero]

theorem incAdj_mem {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {y : Mx D S.rank ρ} (hy : y ∈ ratMx D S.rank ρ) :
    d.incAdj S y ∈ ratMx D T.rank S.rank :=
  ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))

variable {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)

def val (Ψ : WO B.V J.W → ℂ) (x : Mx D J.W.rank ρ) : WO B.V₀ J.W₀ → ℂ :=
  evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ x (yZero B.V₀ ρ (vecB B.o B.ζ))

theorem val_theta {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (x : Mx D J.W.rank ρ) :
    IsThetaFunO ψ B.V₀ J.W₀ (val s Ψ x) :=
  (GlobalTheory.MixValues.mixed_values D ψ s.weil.std).2 _ _ _ _ J.d _ _ s.vT.covol _
    ((GlobalTheory.MixValues.mixed_values D ψ s.weil.std).1 _ _ _ _ B.d _ _ s.vS.covol Ψ hΨ x) _

theorem enorm_val_le {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (x : Mx D J.W.rank ρ) :
    ‖val s Ψ x 0‖ₑ ≤ ∫⁻ b in s.vT.𝓕, ‖B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x (xZero J.d ⬝ b)‖ₑ ∂s.vT.μ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun b => ?_))
  have hf := (GlobalTheory.MixValues.mixed_values D ψ s.weil.std).1 _ _ _ _ B.d _ _ s.vS.covol Ψ hΨ x
  change IsThetaFunO ψ B.V₀ J.W (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x) at hf
  change ‖heisO ψ B.V₀ J.W (J.d.incX B.V₀ b)
    (heisO ψ B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)))
      (heisO ψ B.V₀ J.W (J.d.inc0 B.V₀ 0) (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x))) 0‖ₑ = _
  rw [J.d.integrandT_eq, map_zero, add_zero, add_comm, ← ofReal_norm, ← ofReal_norm, norm_mul, s.weil.std.1.2.1, one_mul,
    norm_theta_add s.weil.std hf (incAdj_mem J.d _ (yZero_mem _ _ _))]
  rfl

variable {om' : Om B.V₀ J.W} (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om')
include hom

theorem val_flag {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (h₀ : GA D B.A) {n : GA D J.W} (hn : n ∈ flagN J.d)
    (h' : GA D J.W₀) (u : UX D ρ) :
    val s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (mt J.W (n * J.d.emb0 h') ⬝ (xZero J.d ⬝ u.1.1)) =
      s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (val s Ψ (xZero J.d ⬝ u.1.1))) := by
  obtain ⟨v, hv, b, c, rfl⟩ := Decomp.flag_decomp J.d hn
  have hr : J.d.nB b * J.d.nC c ∈ radX J.d := (Decomp.mem_radX_iff J.d).2 ⟨b, c, rfl⟩
  have e1 : s.om (embA B.d B.o h₀, J.d.levi v * (J.d.nB b * J.d.nC c) * J.d.emb0 h') Ψ =
      s.om (1, J.d.levi v) (s.om (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_assoc (J.d.levi v)]
  have e2 : mt J.W (J.d.levi v * (J.d.nB b * J.d.nC c) * J.d.emb0 h') ⬝ (xZero J.d ⬝ u.1.1) =
      xZero J.d ⬝ ((⟨v, hv⟩ : UX D ρ) * u).1.1 := by
    rw [xZero, ← Matrix.mul_assoc, mt_mul, Matrix.mul_assoc (mt J.W _), J.d.wittDecomp_anisotropicEmbedding_inclX, Decomp.mt_flag_jX, Matrix.mul_assoc]
    rfl
  have e3 := (GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom _ (s.weil.om_pres (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ hΨ)).2
    (⟨v, hv⟩ * u) ⟨v, hv⟩
  rw [inv_mul_cancel_left] at e3
  rw [e1, e2, val, e3, (GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom Ψ hΨ).1 u h₀ _ hr h', opA, opA,
    jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hv)]
  rfl

theorem val_ratA {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) {γ : GA D B.A} (hγ : γ ∈ GQ B.A) (u : UX D ρ) :
    val s (s.om (embA B.d B.o γ, 1) Ψ) (xZero J.d ⬝ u.1.1) 0 = val s Ψ (xZero J.d ⬝ u.1.1) 0 := by
  have h := val_flag s hom hΨ γ (one_mem _) 1 u
  rw [map_one, mul_one, mt_one, Matrix.one_mul, opA, jacT_one, id, Prod.mk_one_one, map_one, Module.End.one_apply] at h
  rw [h]
  exact s.weil₀.om_aut _ (B.o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) _ (val_theta s hΨ _)

theorem val_ratR {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) {γ : GA D J.W} (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d)
    (u : UX D ρ) :
    ‖val s (s.om (1, γ) Ψ) (mt J.W γ ⬝ (xZero J.d ⬝ u.1.1)) 0‖ = ‖val s Ψ (xZero J.d ⬝ u.1.1) 0‖ := by
  obtain ⟨hq, hj⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨n, hn, h', rfl⟩ := (Decomp.mem_jacGrp_iff J.d).1 hj
  obtain ⟨hnq, hh⟩ := ((GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d).2.2.2.2.2 n hn h').1 hq
  have h := val_flag s hom hΨ 1 hn h' u
  rw [map_one, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply] at h
  have ht := val_theta s hΨ (xZero J.d ⬝ u.1.1)
  have hp : ptT J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n ∈ ratMx D J.W₀.rank B.V₀.rank :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff _ _).1 (inv_mem hnq)) (incAdj_mem J.d _ (yZero_mem _ _ _)))
  rw [h, opA, jacT, Pi.smul_apply, smul_eq_mul, heisO, norm_mul, norm_mul, s.weil.std.1.2.1, s.weil.std.1.2.1, one_mul,
    one_mul, add_comm, norm_theta_add s.weil.std (s.weil₀.om_pres _ _ ht) hp,
    s.weil₀.om_aut 1 (one_mem _) h' hh _ ht]

variable (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ)


omit hom in
def evalMaj (g r : GA D J.W) : ℝ≥0∞ :=
  ‖G g‖ₑ * ∫⁻ h₀ in B.vA.𝓕, ‖φ h₀‖ₑ * ‖val s (s.om (embA B.d B.o h₀, g) Φ) (mt J.W r ⬝ xZero J.d) 0‖ₑ ∂B.vA.μ

variable {φ G Φ}

omit hom in
theorem continuous_val (hΦ : IsThetaFunO ψ B.V J.W Φ) {X : Type} [TopologicalSpace X] {a : X → GA D B.A} {g : X → GA D J.W}
    {x : X → Mx D J.W.rank ρ} (ha : Continuous a) (hg : Continuous g) (hx : Continuous x) :
    Continuous fun p => val s (s.om (embA B.d B.o (a p), g p) Φ) (x p) 0 := by
  have hA : Continuous (embA B.d B.o) :=
    B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hc : Continuous fun p : X => ((embA B.d B.o (a p), g p), x p, yZero B.V₀ ρ (vecB B.o B.ζ), (0 : WO B.V₀ J.W₀)) :=
    ((hA.comp ha).prodMk hg).prodMk (hx.prodMk continuous_const)
  have h := (GlobalTheory.MixCont.mixed_coords_continuous D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil Φ hΦ).2.comp hc
  simpa only [Function.comp_def, val] using h

omit hom in
theorem measurable_maj (hφ : IsContAut B.A φ) (hG : RapidDec J.W G) (hΦ : IsThetaFunO ψ B.V J.W Φ) :
    Measurable (Function.uncurry (evalMaj s φ G Φ)) := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (GA D B.A) := ⟨rfl⟩
  have := B.vA.haar
  have := sFinite_of_haar B.vA.μ
  refine (hG.continuous.measurable.comp measurable_fst).enorm.mul ?_
  have hc : Continuous fun p : GA D B.A × GA D J.W × GA D J.W =>
      val s (s.om (embA B.d B.o p.1, p.2.1) Φ) (mt J.W p.2.2 ⬝ xZero J.d) 0 :=
    continuous_val s hΦ continuous_fst (continuous_fst.comp continuous_snd)
      (((continuous_mt J.W).comp (continuous_snd.comp continuous_snd)).matrix_mul continuous_const)
  exact ((hφ.2.measurable.comp measurable_fst).enorm.mul hc.measurable.enorm).lintegral_prod_left'

omit hom in
theorem exists_mt_xZero {r : GA D J.W} (hr : r ∈ jacGrp J.d) : ∃ v : UX D ρ, mt J.W r ⬝ xZero J.d = xZero J.d ⬝ v.1.1 := by
  rw [← (GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d).2.2.2.1] at hr
  obtain ⟨v, hv, e⟩ := hr
  exact ⟨⟨v, hv⟩, e⟩


omit hom in
theorem exists_levi_conj {r : GA D J.W} (hr : r ∈ jacGrp J.d) : ∃ v : UX D ρ, ∀ u : UX D ρ,
    ∃ t ∈ radX J.d ⊔ J.d.emb0.range, J.d.levi u.1 * r = t * J.d.levi (u * v).1 := by
  obtain ⟨v, hv⟩ := exists_mt_xZero hr
  refine ⟨v, fun u => ⟨J.d.levi u.1 * r * (J.d.levi (u * v).1)⁻¹, ?_, (inv_mul_cancel_right _ _).symm⟩⟩
  have hs : J.d.levi u.1 * r * (J.d.levi (u * v).1)⁻¹ ∈ stabX J.d := by
    have h1 : mt J.W (J.d.levi u.1 * r) ⬝ xZero J.d = mt J.W (J.d.levi (u * v).1) ⬝ xZero J.d := by
      rw [mt_mul, Matrix.mul_assoc, hv, ← Matrix.mul_assoc, levi_xZero, levi_xZero, Matrix.mul_assoc]
      rfl
    change mt J.W _ ⬝ xZero J.d = xZero J.d
    rw [← map_inv, mt_mul, Matrix.mul_assoc, levi_xZero, ← Matrix.mul_assoc, h1, levi_xZero, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  obtain ⟨n, hn, h', e⟩ := (Decomp.mem_stabX_iff J.d).1 hs
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h', rfl⟩)

theorem maj_left (hG : RapidDec J.W G) (hΦ : IsThetaFunO ψ B.V J.W Φ) {γ : GA D J.W} (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d)
    (g : GA D J.W) {r : GA D J.W} (hr : r ∈ jacGrp J.d) : evalMaj s φ G Φ (γ * g) (γ * r) = evalMaj s φ G Φ g r := by
  obtain ⟨v, hv⟩ := exists_mt_xZero hr
  rw [evalMaj, evalMaj, hG.left (Subgroup.mem_inf.1 hγ).1]
  refine congrArg (‖G g‖ₑ * ·) (lintegral_congr fun h₀ => ?_)
  have h := val_ratR s hom (s.weil.om_pres (embA B.d B.o h₀, g) Φ hΦ) hγ v
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul] at h
  rw [mt_mul, Matrix.mul_assoc, hv, ← ofReal_norm (val s _ _ 0), h, ofReal_norm]

omit hom in
theorem maj_levi {r : GA D J.W} (hr : r ∈ jacGrp J.d) :
    ∃ v : UX D ρ, ∀ g (u : UX D ρ), evalMaj s φ G Φ g (r * J.d.levi u.1) = evalMaj s φ G Φ g (J.d.levi (v * u).1) := by
  obtain ⟨v, hv⟩ := exists_mt_xZero hr
  refine ⟨v, fun g u => ?_⟩
  have e : mt J.W (r * J.d.levi u.1) ⬝ xZero J.d = mt J.W (J.d.levi (v * u).1) ⬝ xZero J.d := by
    rw [mt_mul, Matrix.mul_assoc, levi_xZero, levi_xZero, ← Matrix.mul_assoc, hv, Matrix.mul_assoc]
    rfl
  rw [evalMaj, evalMaj, e]

theorem enorm_fjAllFun_le (hΦ : IsThetaFunO ψ B.V J.W Φ) (h : GA D J.W) (h' : GA D J.W₀) (n : flagN J.d) :
    ‖fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (evalBF s (s.om (1, h) Φ)) h' n‖ₑ ≤
      evalMaj s φ G Φ (n.1 * J.d.emb0 h' * h) (n.1 * J.d.emb0 h') := by
  have e : ‖star (psiFlag ψ J.d n.1)‖ₑ = 1 := by
    rw [← ofReal_norm, norm_star, psiFlag, psiE, s.weil.std.1.2.1, ENNReal.ofReal_one]
  rw [fjAllFun, enorm_mul, enorm_mul, e, mul_one, evalMaj]
  refine mul_le_mul_right ((enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun h₀ => ?_))) _
  have h1 := val_flag s hom (s.weil.om_pres (1, h) Φ hΦ) h₀ n.2 h' 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, OneMemClass.coe_one, Units.val_one, Matrix.mul_one] at h1
  rw [enorm_mul, h1]
  rfl

theorem exists_bound (hG : RapidDec J.W G) (hΦ : IsThetaFunO ψ B.V J.W Φ)
    {𝓑 : Set (GA D J.W)} (h𝓑 : IsFundamentalDomain (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) 𝓑 s.vW.μ) :
    ∃ M : ℝ, ∀ h₀, ∫⁻ g in 𝓑, ‖G g‖ₑ * ∫⁻ u : UX D ρ,
      ‖val s (s.om (embA B.d B.o h₀, g) Φ) (xZero J.d ⬝ u.1.1) 0‖ₑ ∂s.vU.ν ∂s.vW.μ ≤ ENNReal.ofReal M := by
  obtain ⟨hb, -, -, hR, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  obtain ⟨C, A, hC⟩ := GlobalTheory.Unf.UnfoldBound.unfolded_integral_le D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom s.vS s.vT s.vU s.vW J.d.e hb G Φ
    hG hΦ 𝓑 (by rw [hR]; exact h𝓑)
  have hA : Continuous (embA B.d B.o) :=
    B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  obtain ⟨K, hK, hcov⟩ := B.cpt
  have hc : Continuous fun h₀ => C * height B.V (embA B.d B.o h₀) ^ A :=
    continuous_const.mul (((continuous_height B.V).comp hA).pow A)
  obtain ⟨M, hM⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨M, fun h₀ => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hcov h₀
  refine le_trans (lintegral_mono fun g => ?_)
    ((hC (embA B.d B.o (γ * h₀))).trans (ENNReal.ofReal_le_ofReal (hM ⟨_, hk, rfl⟩)))
  refine mul_le_mul_right (lintegral_mono fun u => ?_) _
  have h1 := val_ratA s hom (s.weil.om_pres (embA B.d B.o h₀, g) Φ hΦ) hγ u
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, ← map_mul] at h1
  exact (congrArg enorm h1).symm.le.trans (enorm_val_le s (s.weil.om_pres _ Φ hΦ) _)

theorem lintegral_maj_lt_top (hφ : IsContAut B.A φ) (hG : RapidDec J.W G) (hΦ : IsThetaFunO ψ B.V J.W Φ)
    {𝓑 : Set (GA D J.W)} (h𝓑 : IsFundamentalDomain (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) 𝓑 s.vW.μ) :
    ∫⁻ g in 𝓑, ∫⁻ u : UX D ρ, evalMaj s φ G Φ g (J.d.levi u.1) ∂s.vU.ν ∂s.vW.μ < ∞ := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (GA D B.A) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := B.vA.haar
  have := sFinite_of_haar B.vA.μ
  have := s.vW.haar
  have := sFinite_of_haar s.vW.μ
  have := s.vU.unit.1
  have := sFinite_of_haar s.vU.ν
  obtain ⟨M, hM⟩ := exists_bound s hom hG hΦ h𝓑
  have hc : Continuous fun p : GA D B.A × GA D J.W × UX D ρ =>
      val s (s.om (embA B.d B.o p.1, p.2.1) Φ) (xZero J.d ⬝ p.2.2.1.1) 0 :=
    continuous_val s hΦ continuous_fst (continuous_fst.comp continuous_snd) (continuous_const.matrix_mul
      ((GlobalTheory.UnitU.isClosedEmbedding_val D ρ).continuous.comp (continuous_snd.comp continuous_snd)))
  simp only [evalMaj, levi_xZero]
  exact lintegral_three_lt_top (E := fun h₀ g (u : UX D ρ) => val s (s.om (embA B.d B.o h₀, g) Φ) (xZero J.d ⬝ u.1.1) 0)
    hφ.2.measurable hG.continuous.measurable hc.measurable
    ((contAut_rapidDec_bounded_integrable D B.A B.cpt φ hφ).2.2 B.vA) hM


omit hom in
theorem exists_domain (J : JacLev D ρ) : IsClosed (jacGrp J.d : Set (GA D J.W)) ∧ J.μR.IsHaarMeasure ∧ J.μR.IsInvInvariant ∧
    ∃ 𝓡 : Set (jacGrp J.d), IsFundamentalDomain ((GQ J.W ⊓ jacGrp J.d).subgroupOf (jacGrp J.d)) 𝓡 J.μR ∧
      ∀ F : GA D J.W → ℝ≥0∞, Measurable F →
        ∫⁻ r in 𝓡, F r ∂J.μR = ∫⁻ h in J.v0.𝓕, ∫⁻ n in J.vN.𝓝, F (n.1 * J.d.emb0 h) ∂J.vN.ν ∂J.v0.μ := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W₀
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (GA D J.W₀) := ⟨rfl⟩
  have := J.v0.haar
  have := J.vN.unit.1
  have o : OrthDec J.W₀ J.W₀ (diagSp D 0 ![] 0 0) :=
    { iA := 1
      iB := 0
      isoA := by simp
      isoB := funext fun i => Fin.elim0 i
      orth := funext fun i => Fin.elim0 i
      rank_add := rfl }
  obtain ⟨⟨hc, hH⟩, -⟩ := GlobalTheory.MixPer.jacGrp_besGrp_haar D J.W J.W₀ J.W₀ (diagSp D 0 ![] 0 0) ρ J.d o J.vN.ν J.vN.𝓝 J.vN.unit
  have hN : IsClosed (flagN J.d : Set (GA D J.W)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag J.W (isIsoSub_e J.d)
  have : LocallyCompactSpace (flagN J.d) := hN.locallyCompactSpace
  have : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology (flagN J.d : Set (GA D J.W))
  have : LocallyCompactSpace (jacGrp J.d) := hc.locallyCompactSpace
  have : SecondCountableTopology (jacGrp J.d) := TopologicalSpace.Subtype.secondCountableTopology (jacGrp J.d : Set (GA D J.W))
  have := sFinite_of_haar J.v0.μ
  have := sFinite_of_haar J.vN.ν
  have hHaar : J.μR.IsHaarMeasure := hH _ J.v0.haar
  obtain ⟨𝓡, h𝓡', hint⟩ : ∃ 𝓡 : Set (jacGrp J.d),
      IsFundamentalDomain ((GQ J.W ⊓ jacGrp J.d).subgroupOf (jacGrp J.d)) 𝓡 J.μR ∧ ∀ f : GA D J.W → ℂ, Measurable f →
        (IntegrableOn (fun r : jacGrp J.d => f r) 𝓡 J.μR ↔
          AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h n => f (n.1 * J.d.emb0 h)) ∧
        (AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fun h n => f (n.1 * J.d.emb0 h)) → ∫ r in 𝓡, f (r : GA D J.W) ∂J.μR =
          ∫ h in J.v0.𝓕, ∫ n in J.vN.𝓝, f (n.1 * J.d.emb0 h) ∂J.vN.ν ∂J.v0.μ) := GlobalTheory.Unf.semiFd_iterated D J.W J.W₀ (flagN J.d) J.d.emb0 J.d.continuous_embed hN
    (fun n hn h => Decomp.conj_mem J.d hn h) (fun n hn n' hn' h h' e => Decomp.flag_unipotent_mul_embedded_anisotropic_unique J.d hn hn' e)
    (GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d).2.2.2.2.2 J.v0 J.vN.ν J.vN.𝓝 J.vN.unit.1 J.vN.unit.2.1 hHaar
  have hb : Measurable fun p : GA D J.W₀ × flagN J.d => p.2.1 * J.d.emb0 p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul (J.d.continuous_embed.measurable.comp measurable_fst)
  have hF : ∀ F : GA D J.W → ℝ≥0∞, Measurable F →
      ∫⁻ r in 𝓡, F r ∂J.μR = ∫⁻ h in J.v0.𝓕, ∫⁻ n in J.vN.𝓝, F (n.1 * J.d.emb0 h) ∂J.vN.ν ∂J.v0.μ := fun F hF => by
    refine (lintegral_eq_of_integral (a := fun r : jacGrp J.d => r.1) measurable_subtype_coe hb (fun f hf => ?_) F hF).trans
      (lintegral_prod _ (hF.comp hb).aemeasurable)
    exact ⟨(hint f hf).1, fun hi => ((hint f hf).2 hi).trans (integral_prod _ hi).symm⟩
  have : Countable (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) := (GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D J.W _ inf_le_left).1
  have : Countable ((GQ J.W ⊓ jacGrp J.d).subgroupOf (jacGrp J.d)) :=
    (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv.countable_iff.2 inferInstance
  have hfin : J.μR 𝓡 ≠ ∞ := by
    have h1 := hF (fun _ => 1) measurable_const
    have h2 := (contAut_rapidDec_bounded_integrable D J.W₀ J.cpt (fun _ => 1) ⟨fun _ _ _ => rfl, continuous_const⟩).2.2 J.v0
    rw [integrableOn_const_iff] at h2
    simp only [enorm_eq_zero, one_ne_zero, false_or] at h2
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul, J.vN.unit.2.2] at h1
    rw [h1]; exact h2.ne
  have := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ J.μR h𝓡' (h𝓡'.measure_ne_zero (NeZero.ne _)) hfin
  exact ⟨hc, hHaar, GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant _, 𝓡, h𝓡', hF⟩

end GlobalTheory.EvalAbs

namespace GlobalTheory.Unf


set_option maxHeartbeats 800000 in
open GlobalTheory.EvalAbs in
theorem evalBF_abs : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∃ z', IsQuotIntL1 J.μR s.vW.μ (fun h => ((∫ u : UX D ρ, ‖J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ))‖ ∂s.vU.ν : ℝ) : ℂ)) z' := by
  intro D ψ ρ B J s om' hom φ G Φ hφ hG hΦ
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vW.haar
  have := sFinite_of_haar s.vW.μ
  have := s.vU.unit.1
  have := sFinite_of_haar s.vU.ν
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit
  have := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant s.vU.ν
  obtain ⟨hc, hH, hI, 𝓡, h𝓡, hF⟩ := exists_domain J
  obtain ⟨c1, c2, hex⟩ := GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D J.W (GQ J.W ⊓ jacGrp J.d) inf_le_left
  obtain ⟨𝓑, h𝓑⟩ := hex _ s.vW.haar
  obtain ⟨hcont, hinv⟩ := GlobalTheory.Unf.evalIntegrand_continuous_invariant D ψ ρ B J s om' hom φ G Φ hφ hG hΦ
  have hq := measurable_maj s hφ hG hΦ
  refine exists_quotientIntegrable_fold_unimodular inf_le_right hc h𝓡 h𝓑 (J.d.levi.comp (UX D ρ).subtype)
    (J.d.continuous_levi.comp continuous_subtype_val).measurable
    (fun u => Subgroup.mem_sup_left (J.d.levi_mem_NFlag u.2)) hq (fun γ hγ g r hr => maj_left s hom hG hΦ hγ g hr)
    (fun r hr => maj_levi s hr) (lintegral_maj_lt_top s hom hφ hG hΦ h𝓑)
    (P := fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (evalBF s (s.om (1, h) Φ))) hcont.measurable
    (fun r hr => ?_) fun h => ?_
  · obtain ⟨v, hv⟩ := exists_levi_conj hr
    refine ⟨v, fun g u => ?_⟩
    obtain ⟨t, ht, e⟩ := hv u
    have h2 := hinv t ht (J.d.levi (u * v).1 * g)
    rw [← mul_assoc, ← e, mul_assoc] at h2
    exact h2
  · have hp : Measurable fun r : GA D J.W => (r * h, r) := (measurable_id.mul_const h).prodMk measurable_id
    have hm := hq.comp hp
    simp only [Function.comp_def, Function.uncurry_apply_pair] at hm
    refine le_trans ?_ (hF (fun r => evalMaj s φ G Φ (r * h) r) hm).ge
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun h' =>
      (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun n => enorm_fjAllFun_le s hom hΦ h h' n))

end GlobalTheory.Unf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvaluationFormAbsoluteConvergenceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluationForm_absolute_convergence : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∃ z', IsQuotIntL1 J.μR s.vW.μ (fun h => ((∫ u : UX D ρ, ‖J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ))‖ ∂s.vU.ν : ℝ) : ℂ)) z' := by
  first | exact @GlobalTheory.Unf.evalBF_abs | exact GlobalTheory.Unf.evalBF_abs | (intros; apply GlobalTheory.Unf.evalBF_abs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralInStages
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralInStages
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal
open Filter

noncomputable section

namespace GlobalTheory.Unf

open GlobalTheory.Tw

section InductionInStages
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem lintegral_eq_cutoff_inner {T : Subgroup G} {μ : Measure G} {μT : Measure T}
    [SFinite μ] [μ.IsMulLeftInvariant] [SFinite μT] [μT.IsInvInvariant]
    {β : G → NNReal} (hβ : IsCosetCutoff T μT β) {H : G → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ x, H x ∂μ = ∫⁻ x, (β x : ℝ≥0∞) * ∫⁻ t : T, H (t * x) ∂μT ∂μ := by
  have hb : Measurable fun x => (β x : ℝ≥0∞) := hβ.1.coe_nnreal_ennreal
  have hmul : Measurable fun p : G × T => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hmul' : Measurable fun p : G × T => ((p.2⁻¹ : T) : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd.inv).mul measurable_fst
  have e1 : ∀ x, (β x : ℝ≥0∞) * ∫⁻ t : T, H (t * x) ∂μT = ∫⁻ t : T, β x * H (t * x) ∂μT := fun x =>
    (lintegral_const_mul' _ _ ENNReal.coe_ne_top).symm
  rw [lintegral_congr e1, lintegral_lintegral_swap ((hb.comp measurable_fst).mul (hH.comp hmul)).aemeasurable]
  have e2 : ∀ t : T, ∫⁻ x, β x * H (t * x) ∂μ = ∫⁻ x, β ((t⁻¹ : T) * x) * H x ∂μ := fun t => by
    rw [← lintegral_mul_left_eq_self (μ := μ) (fun x => β ((t⁻¹ : T) * x) * H x) t]
    simp
  rw [lintegral_congr e2,
    ← lintegral_lintegral_swap (f := fun x (t : T) => β ((t⁻¹ : T) * x) * H x)
      ((hb.comp hmul').mul (hH.comp measurable_fst)).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [lintegral_mul_const _ (f := fun t : T => (β ((t⁻¹ : T) * x) : ℝ≥0∞)) (hb.comp (hmul'.comp measurable_prodMk_left)),
    lintegral_inv_eq_self (μ := μT) (fun t : T => (β (t * x) : ℝ≥0∞)), hβ.2, one_mul]

theorem map_val_eq_map_stages {R₀ R : Subgroup G} (μ₀ : Measure R₀) (μR : Measure R) [SFinite μ₀]
    {U : Type} [MeasurableSpace U] (ν : Measure U) {j : U → G} (hj : Measurable j)
    (hst : ∀ F : G → ℝ≥0∞, Measurable F → ∫⁻ r : R, F r ∂μR = ∫⁻ u, ∫⁻ r : R₀, F (r * j u) ∂μ₀ ∂ν) :
    μR.map Subtype.val = (ν.prod μ₀).map (fun p : U × R₀ => (p.2 : G) * j p.1) := by
  have hm : Measurable (fun p : U × R₀ => (p.2 : G) * j p.1) :=
    (measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst)
  have key : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ y, F y ∂(μR.map Subtype.val) = ∫⁻ y, F y ∂((ν.prod μ₀).map (fun p : U × R₀ => (p.2 : G) * j p.1)) := by
    intro F hF
    rw [lintegral_map hF measurable_subtype_coe, lintegral_map hF hm, lintegral_prod (f := fun p : U × R₀ => F ((p.2 : G) * j p.1)) (hF.comp hm).aemeasurable]
    exact hst F hF
  ext A hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA]
  exact key _ (measurable_one.indicator hA)

end InductionInStages

theorem invariant_integral_in_stages : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (R₀ R : Subgroup G), IsClosed (R₀ : Set G) → IsClosed (R : Set G) → ∀ (μ₀ : Measure R₀) (μR : Measure R), μ₀.IsHaarMeasure → μ₀.IsInvInvariant → μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (U : Type) [MeasurableSpace U] (ν : Measure U) [SFinite ν] (j : U → G), Measurable j → (∀ F : G → ENNReal, Measurable F → ∫⁻ r : R, F r ∂μR = ∫⁻ u, ∫⁻ r : R₀, F (r * j u) ∂μ₀ ∂ν) → ∀ f : G → ℂ, Measurable f → (∀ r ∈ R₀, ∀ g, f (r * g) = f g) → (∀ g, Integrable (fun u => f (j u * g)) ν) → (∃ z', IsQuotIntL1 μR μ (fun g => ((∫ u, ‖f (j u * g)‖ ∂ν : ℝ) : ℂ)) z') → ∀ z, IsQuotIntL1 μR μ (fun g => ∫ u, f (j u * g) ∂ν) z → IsQuotIntL1 μ₀ μ f z := by
  intro G _ _ _ _ _ _ _ _ μ _ R₀ R hR₀ hR μ₀ μR _ _ _ _ U _ ν _ j hj hst f hf hinv hint hz' z hz
  obtain ⟨z', hz'⟩ := hz'
  have : LocallyCompactSpace R₀ := hR₀.locallyCompactSpace
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  have : SecondCountableTopology R₀ := TopologicalSpace.Subtype.secondCountableTopology (R₀ : Set G)
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  obtain ⟨β₀, -, hβ₀⟩ := exists_isCosetCutoff (μT := μ₀) hR₀
  obtain ⟨β, -, hβ⟩ := exists_isCosetCutoff (μT := μR) hR
  obtain ⟨F, hF⟩ : ∃ F : G → ℂ, F = fun x => (β₀ x : ℝ) • f x := ⟨_, rfl⟩
  have hFm : Measurable F := by rw [hF]; exact hβ₀.1.coe_nnreal_real.smul hf
  have hc0 : ∀ y, Integrable (fun r : R₀ => (β₀ (r * y) : ℝ)) μ₀ ∧ ∫ r : R₀, (β₀ (r * y) : ℝ) ∂μ₀ = 1 :=
    fun y => integrable_of_lintegral_eq_one (hβ₀.1.comp (measurable_subtype_coe.mul_const y)) (hβ₀.2 y)
  have hFe : ∀ y, ∀ r : R₀, F (r * y) = (β₀ (r * y) : ℝ) • f y := fun y r => by
    rw [hF]
    show (β₀ (r * y) : ℝ) • f (r * y) = _
    rw [hinv r r.2 y]
  have hFr : ∀ y, Integrable (fun r : R₀ => F (r * y)) μ₀ ∧ ∫ r : R₀, F (r * y) ∂μ₀ = f y := fun y => by
    simp only [hFe y]
    exact ⟨(hc0 y).1.smul_const _, by rw [integral_smul_const, (hc0 y).2, one_smul]⟩
  have hFn : ∀ y, ∫ r : R₀, ‖F (r * y)‖ ∂μ₀ = ‖f y‖ := fun y => by
    simp only [hFe y, norm_smul, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    rw [integral_mul_const, (hc0 y).2, one_mul]
  have hFn' : ∀ y, ∫⁻ r : R₀, ‖F (r * y)‖ₑ ∂μ₀ = ‖f y‖ₑ := fun y => by
    have e : ∀ r : R₀, ‖F (r * y)‖ₑ = (β₀ (r * y) : ℝ≥0∞) * ‖f y‖ₑ := fun r => by
      rw [hFe y r, enorm_smul]
      simp
    rw [lintegral_congr e, lintegral_mul_const' _ _ enorm_ne_top, hβ₀.2, one_mul]
  have hm : Measurable (fun p : U × R₀ => (p.2 : G) * j p.1) :=
    (measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst)
  have hM := map_val_eq_map_stages μ₀ μR ν hj hst
  have hP : ∀ h, Integrable ((fun y => F (y * h)) ∘ fun p : U × R₀ => (p.2 : G) * j p.1) (ν.prod μ₀) := fun h => by
    refine (integrable_prod_iff ((hFm.comp (measurable_mul_const h)).comp hm).aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine Eventually.of_forall fun u => ?_
      simpa [Function.comp_def, mul_assoc] using (hFr (j u * h)).1
    · have e : ∀ u, ∫ r : R₀, ‖((fun y => F (y * h)) ∘ fun p : U × R₀ => (p.2 : G) * j p.1) (u, r)‖ ∂μ₀ = ‖f (j u * h)‖ :=
        fun u => by simpa [Function.comp_def, mul_assoc] using hFn (j u * h)
      exact (hint h).norm.congr (Eventually.of_forall fun u => (e u).symm)
  have hRint : ∀ h, Integrable (fun r : R => F (r * h)) μR := fun h => by
    have hi : Integrable (fun y => F (y * h)) (μR.map Subtype.val) := by
      rw [hM]
      exact (integrable_map_measure (hFm.comp (measurable_mul_const h)).aestronglyMeasurable hm.aemeasurable).2 (hP h)
    exact hi.comp_measurable measurable_subtype_coe
  have hRval : ∀ h, ∫ r : R, F (r * h) ∂μR = ∫ u, f (j u * h) ∂ν := fun h => by
    have e1 : ∫ r : R, F (r * h) ∂μR = ∫ y, F (y * h) ∂(μR.map Subtype.val) :=
      (integral_map measurable_subtype_coe.aemeasurable (hFm.comp (measurable_mul_const h)).aestronglyMeasurable).symm
    rw [e1, hM, integral_map (f := fun y => F (y * h)) hm.aemeasurable (hFm.comp (measurable_mul_const h)).aestronglyMeasurable]
    have e2 := integral_prod _ (hP h)
    simp only [Function.comp_def] at e2
    rw [e2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simpa [mul_assoc] using (hFr (j u * h)).2
  have hGint : Integrable F μ := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_eq_cutoff_inner hβ hFm.enorm]
    have e : ∀ x, ∫⁻ r : R, ‖F (r * x)‖ₑ ∂μR = ∫⁻ u, ‖f (j u * x)‖ₑ ∂ν := fun x => by
      rw [hst (fun y => ‖F (y * x)‖ₑ) (hFm.comp (measurable_mul_const x)).enorm]
      refine lintegral_congr fun u => ?_
      have h1 := hFn' (j u * x)
      simp only [mul_assoc] at h1 ⊢
      exact h1
    simp only [e]
    obtain ⟨hi, -⟩ := hz'.cutoff hβ
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) hi.2
    rw [enorm_smul, ← ofReal_integral_norm_eq_lintegral_enorm (hint x)]
    simp [Real.enorm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hq : IsQuotIntL1 μR μ (fun g => ∫ u, f (j u * g) ∂ν) (∫ x, F x ∂μ) :=
    ⟨F, hGint, hRint, fun h => (hRval h).symm, rfl⟩
  exact ⟨F, hGint, fun h => (hFr h).1, fun h => (hFr h).2.symm, hz.unique hR hq⟩

end GlobalTheory.Unf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralInStagesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_integral_in_stages_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (R₀ R : Subgroup G), IsClosed (R₀ : Set G) → IsClosed (R : Set G) → ∀ (μ₀ : Measure R₀) (μR : Measure R), μ₀.IsHaarMeasure → μ₀.IsInvInvariant → μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (U : Type) [MeasurableSpace U] (ν : Measure U) [SFinite ν] (j : U → G), Measurable j → (∀ F : G → ENNReal, Measurable F → ∫⁻ r : R, F r ∂μR = ∫⁻ u, ∫⁻ r : R₀, F (r * j u) ∂μ₀ ∂ν) → ∀ f : G → ℂ, Measurable f → (∀ r ∈ R₀, ∀ g, f (r * g) = f g) → (∀ g, Integrable (fun u => f (j u * g)) ν) → (∃ z', IsQuotIntL1 μR μ (fun g => ((∫ u, ‖f (j u * g)‖ ∂ν : ℝ) : ℂ)) z') → ∀ z, IsQuotIntL1 μR μ (fun g => ∫ u, f (j u * g) ∂ν) z → IsQuotIntL1 μ₀ μ f z := by
  first | exact @GlobalTheory.Unf.invariant_integral_in_stages | exact GlobalTheory.Unf.invariant_integral_in_stages | (intros; apply GlobalTheory.Unf.invariant_integral_in_stages <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodEvaluationUnfoldingOfWittDescent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem nonempty_orthDec_zero (D : D7) (S : HSp D) : Nonempty (OrthDec S S (diagSp D 0 ![] 0 0)) :=
  ⟨{ iA := 1
     iB := 0
     isoA := by simp
     isoB := funext fun i => Fin.elim0 i
     orth := funext fun i => Fin.elim0 i
     rank_add := rfl }⟩

private theorem s_finite_of_sigma_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] : SFinite ν :=
  inferInstance

theorem evalBF_of_descent : ∀ D : D7, Descent D → EvalBF D := by
  intro D hD ψ ρ B J s φ G Φ hφ hG hΦ ν₀ 𝓝₀ hν₀ h𝓝₀ h1
  obtain ⟨om', hom'⟩ := (hD ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vW.haar
  have := s.vU.unit.1
  have : SigmaCompactSpace (UX D ρ) := inferInstance
  have : IsFiniteMeasureOnCompacts s.vU.ν := inferInstance
  have : IsLocallyFiniteMeasure s.vU.ν := inferInstance
  have : SigmaFinite s.vU.ν := inferInstance
  have : SFinite s.vU.ν := s_finite_of_sigma_finite s.vU.ν
  obtain ⟨hc0, hH0, hI0, hI, hF⟩ := GlobalTheory.T.fourierJacobi_measure_unitriangular_coordinates D ρ J s.vU ν₀ 𝓝₀ hν₀ h𝓝₀ h1
  obtain ⟨o⟩ := nonempty_orthDec_zero D J.W₀
  obtain ⟨⟨hc, hH⟩, -⟩ := GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product D J.W J.W₀ J.W₀ (diagSp D 0 ![] 0 0) ρ J.d o J.vN.ν J.vN.𝓝 J.vN.unit
  obtain ⟨hcont, hinv⟩ := GlobalTheory.T.besselUnfolding_evaluationIntegrand_continuous_invariant D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have hrel := GlobalTheory.T.flatPeriod_eq_integral_evaluationPeriods D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have habs := GlobalTheory.T.evaluationForm_absolute_convergence D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have hU := GlobalTheory.T.besselPeriod_thetaLift_unfolding D hD ψ ρ B J s φ G Φ hφ hG hΦ
  rw [funext fun h => (hrel h).2] at hU
  exact GlobalTheory.T.invariant_integral_in_stages_alt (GA D J.W) s.vW.μ (radX J.d ⊔ J.d.emb0.range) (jacGrp J.d) hc0 hc
    (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) J.μR hH0 hI0 (hH _ J.v0.haar) hI (UX D ρ) s.vU.ν (fun u => J.d.levi u.1)
    (J.d.continuous_levi.comp continuous_subtype_val).measurable hF _ hcont.measurable hinv (fun h => (hrel h).1) habs _ hU

end GlobalTheory.Unf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodEvaluationUnfoldingOfWittDescentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_period_evaluation_unfolding_of_witt_descent : ∀ D : D7, Descent D → EvalBF D := by
  first | exact @GlobalTheory.Unf.evalBF_of_descent | exact GlobalTheory.Unf.evalBF_of_descent | (intros; apply GlobalTheory.Unf.evalBF_of_descent <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem unfoldings_of_chain :
    ∀ D : D7, UnfBF D ∧ EvalBF D ∧ UnfFB D ∧ DoubleStep D ∧ LastLaw D ∧ IT D ∧ ContrLaw D ∧ SeeLast D := by
  intro D
  have hD : Descent D := GlobalTheory.T.weilDatum_descends_to_wittCore D
  exact ⟨GlobalTheory.T.besselPeriod_thetaLift_unfolding D hD, GlobalTheory.T.bessel_period_evaluation_unfolding_of_witt_descent D hD, GlobalTheory.T.fourierJacobi_period_unfolding_of_witt_descent D hD, GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent D hD,
    GlobalTheory.T.doubleLiftPeriod_rankZero_fubini_compactQuotient D, GlobalTheory.T.iteratedThetaUnfolding_of_weilDatumDescent D hD, GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D, GlobalTheory.T.lastSeeSaw_thetaIdentity D⟩

end GlobalTheory.Unf
