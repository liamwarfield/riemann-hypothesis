module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MemStabiliserIffFrameLowerBlock
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.Imports

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.AbsUnfA
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PositivityTheory.SiegelWeilFormula.kunf

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] {lam : Measure V} [lam.IsAddHaarMeasure] {Λ : AddSubgroup V} [Countable Λ]
  {𝓖 : Set V}


omit [SecondCountableTopology V] in
theorem lintegral_fd_le (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (S : V → ℝ≥0∞)
    (hS : ∀ (ν : Λ) β, S (β + ν) = S β) {C : Set V} (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C) :
    ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in C, S β ∂lam := by
  rw [h𝓖.setLIntegral_eq_tsum' S C]
  have hsub : 𝓖 ⊆ ⋃ ν : Λ, (ν +ᵥ C) ∩ 𝓖 := by
    intro β hβ
    obtain ⟨ν, hν⟩ := hcov β
    refine Set.mem_iUnion.2 ⟨-ν, ?_, hβ⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    exact hν
  calc ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in ⋃ ν : Λ, (ν +ᵥ C) ∩ 𝓖, S β ∂lam := lintegral_mono_set hsub
    _ ≤ ∑' ν : Λ, ∫⁻ β in (ν +ᵥ C) ∩ 𝓖, S β ∂lam := lintegral_iUnion_le _ _
    _ = ∑' ν : Λ, ∫⁻ x in (ν +ᵥ C) ∩ 𝓖, S (-ν +ᵥ x) ∂lam := by
      refine tsum_congr fun ν => lintegral_congr fun x => ?_
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
      exact (hS (-ν) x).symm


omit [SecondCountableTopology V] in
theorem setIntegral_fd_eq_zero (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (g : V → ℂ)
    (hg : ∀ (ν : Λ) β, g (β + ν) = g β) (β₀ : V) (c : ℂ) (hc : c ≠ 1) (hβ₀ : ∀ β, g (β + β₀) = c * g β) :
    ∫ β in 𝓖, g β ∂lam = 0 := by
  have h1 : IsAddFundamentalDomain Λ ((-β₀) +ᵥ 𝓖) lam := h𝓖.vadd_of_comm (-β₀)
  have h2 : ∫ β in 𝓖, g β ∂lam = ∫ x in (-β₀) +ᵥ 𝓖, g (β₀ +ᵥ x) ∂lam := by
    rw [← (measurePreserving_vadd β₀ lam).setIntegral_image_emb (measurableEmbedding_const_vadd β₀)]
    congr 1
    rw [Set.image_vadd, vadd_vadd, add_neg_cancel, zero_vadd]
  have h3 : ∫ x in (-β₀) +ᵥ 𝓖, g (β₀ +ᵥ x) ∂lam = c * ∫ β in 𝓖, g β ∂lam := by
    have e : (fun x => g (β₀ +ᵥ x)) = fun x => c * g x := funext fun x => by
      rw [vadd_eq_add, add_comm, hβ₀]
    rw [e, h1.setIntegral_eq h𝓖 (fun ν x => by rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm, hg]),
      integral_const_mul]
  have h4 : (1 - c) * ∫ β in 𝓖, g β ∂lam = 0 := by
    rw [sub_mul, one_mul, ← h3, ← h2, sub_self]
  exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (Ne.symm hc))

end PositivityTheory.SiegelWeilFormula.kunf

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.AbsUnfB
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.SiegelWeilFormula.kunf

theorem abs_integrable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (lam : Measure V) [lam.IsAddHaarMeasure]
    (Λ : AddSubgroup V) [Countable Λ] (𝓖 : Set V) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam)
    {Q : Type} [Countable Q] (act : Q → Λ → Q) (hact0 : ∀ q, act q 0 = q)
    (hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν'))
    (A : Q → V → ℂ) (hA : ∀ q, Continuous (A q)) (hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : V)))
    (C : Set V) (hC : IsCompact C) (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C)
    (u : Q → ℝ) (hu : Summable u) (hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q)
    (q₀ : Q) (hinj : Function.Injective (act q₀)) : Integrable (A q₀) lam := by
  have hAm : ∀ q, Measurable fun β => ‖A q β‖ₑ := fun q => (hA q).measurable.enorm
  obtain ⟨S, hS_def⟩ : ∃ S : V → ℝ≥0∞, S = fun β => ∑' q, ‖A q β‖ₑ := ⟨_, rfl⟩
  have hSm : Measurable S := by
    rw [hS_def]
    exact Measurable.tsum fun q => hAm q
  have hSper : ∀ (ν : Λ) β, S (β + ν) = S β := by
    intro ν β
    let e : Q ≃ Q := ⟨fun q => act q ν, fun q => act q (-ν),
      fun q => show act (act q ν) (-ν) = q by rw [hact, add_neg_cancel, hact0],
      fun q => show act (act q (-ν)) ν = q by rw [hact, neg_add_cancel, hact0]⟩
    rw [hS_def]
    simp only [← hAact]
    exact e.tsum_eq (fun q => ‖A q β‖ₑ)
  obtain ⟨ν₀, hν₀⟩ := hcov 0
  have hu0 : ∀ q, 0 ≤ u q := fun q => (norm_nonneg _).trans (hAu q _ hν₀)
  have hM : (∑' q, ENNReal.ofReal (u q)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hu0 hu]
    exact ENNReal.ofReal_ne_top
  have hmeas : ∀ ν : Λ, AEMeasurable (fun β => ‖A q₀ (ν +ᵥ β)‖ₑ) (lam.restrict 𝓖) := fun ν =>
    ((hA q₀).comp (continuous_const_add (ν : V))).measurable.enorm.aemeasurable
  have h1 : ∫⁻ β, ‖A q₀ β‖ₑ ∂lam ≤ ∫⁻ β in 𝓖, S β ∂lam := by
    rw [h𝓖.lintegral_eq_tsum'', ← lintegral_tsum hmeas]
    refine lintegral_mono fun β => ?_
    have h5 : ∀ ν : Λ, ‖A q₀ (ν +ᵥ β)‖ₑ = ‖A (act q₀ ν) β‖ₑ := fun ν => by
      show ‖A q₀ ((ν : V) + β)‖ₑ = _
      rw [hAact, add_comm]
    simp only [h5, hS_def]
    exact ENNReal.tsum_comp_le_tsum_of_injective hinj (fun q => ‖A q β‖ₑ)
  have h2 : ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in C, S β ∂lam := lintegral_fd_le h𝓖 S hSper hcov
  have h3 : ∫⁻ β in C, S β ∂lam ≤ ∫⁻ _ in C, (∑' q, ENNReal.ofReal (u q)) ∂lam := by
    apply lintegral_mono_ae
    rw [ae_restrict_iff (measurableSet_le hSm measurable_const)]
    refine Filter.Eventually.of_forall fun β hβ => ?_
    rw [hS_def]
    exact ENNReal.tsum_le_tsum fun q => by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hAu q β hβ)
  rw [setLIntegral_const] at h3
  refine ⟨(hA q₀).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (h1.trans (h2.trans h3)) (ENNReal.mul_lt_top hM.lt_top hC.measure_lt_top)

end PositivityTheory.SiegelWeilFormula.kunf

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.AbsUnf
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.SiegelWeilFormula.kunf

theorem abs_unfold {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] (lam : Measure V) [lam.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ]
    (𝓖 : Set V) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam)
    {Q : Type} [Countable Q] (act : Q → Λ → Q) (hact0 : ∀ q, act q 0 = q)
    (hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν'))
    (A : Q → V → ℂ) (hA : ∀ q, Continuous (A q)) (hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : V)))
    (χ₀ : V → ℂ) (hχc : Continuous χ₀) (hχadd : ∀ β β', χ₀ (β + β') = χ₀ β * χ₀ β') (hχΛ : ∀ ν : Λ, χ₀ (ν : V) = 1)
    (C : Set V) (hC : IsCompact C) (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C)
    (u : Q → ℝ) (hu : Summable u) (hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q)
    (q₀ : Q) (hinj : Function.Injective (act q₀))
    (hsmall : ∀ q, (∀ ν, act q₀ ν ≠ q) → ∃ β₀, χ₀ β₀ ≠ 1 ∧ ∀ ν β, A (act q ν) (β + β₀) = A (act q ν) β) :
    Integrable (A q₀) lam ∧ Integrable (fun β => A q₀ β * χ₀ β) lam ∧
      ∫ β in 𝓖, (∑' q, A q β) * χ₀ β ∂lam = ∫ β, A q₀ β * χ₀ β ∂lam := by
  classical
  have hactneg : ∀ q ν, act (act q ν) (-ν) = q := fun q ν => by rw [hact, add_neg_cancel, hact0]
  have hactneg' : ∀ q ν, act (act q (-ν)) ν = q := fun q ν => by rw [hact, neg_add_cancel, hact0]
  let e : Λ → Q ≃ Q := fun ν => ⟨fun q => act q ν, fun q => act q (-ν), fun q => hactneg q ν, fun q => hactneg' q ν⟩

  obtain ⟨M, hM⟩ : ∃ M, ∀ β, ‖χ₀ β‖ ≤ M := by
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hχc.continuousOn
    refine ⟨M, fun β => ?_⟩
    obtain ⟨ν, hν⟩ := hcov β
    have := hM _ hν
    rwa [hχadd, hχΛ, mul_one] at this

  have hu0 : ∀ q, 0 ≤ u q := fun q => by
    obtain ⟨ν, hν⟩ := hcov 0
    exact (norm_nonneg _).trans (hAu q _ hν)

  set S : V → ℝ≥0∞ := fun β => ∑' q, ‖A q β‖ₑ with hS
  have hSper : ∀ (ν : Λ) β, S (β + ν) = S β := fun ν β => by
    simp only [hS]
    calc ∑' q, ‖A q (β + ν)‖ₑ = ∑' q, ‖A (e ν q) β‖ₑ := tsum_congr fun q => by rw [← hAact]; rfl
      _ = ∑' q, ‖A q β‖ₑ := (e ν).tsum_eq (fun q => ‖A q β‖ₑ)
  have hSC : ∀ β ∈ C, S β ≤ ENNReal.ofReal (∑' q, u q) := fun β hβ => by
    rw [ENNReal.ofReal_tsum_of_nonneg hu0 hu]
    exact ENNReal.tsum_le_tsum fun q => by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hAu q β hβ)
  have hS𝓖 : ∫⁻ β in 𝓖, S β ∂lam < ∞ := by
    refine (lintegral_fd_le h𝓖 S hSper hcov).trans_lt ?_
    calc ∫⁻ β in C, S β ∂lam ≤ ∫⁻ _ in C, ENNReal.ofReal (∑' q, u q) ∂lam := setLIntegral_mono measurable_const hSC
      _ = ENNReal.ofReal (∑' q, u q) * lam C := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top
  have hmeasA : ∀ q, Measurable fun β => ‖A q β‖ₑ := fun q => (hA q).measurable.enorm
  have hsumA : ∑' q, ∫⁻ β in 𝓖, ‖A q β‖ₑ ∂lam < ∞ := by
    rw [← lintegral_tsum fun q => (hmeasA q).aemeasurable]
    exact hS𝓖
  have hsumAχ : ∑' q, ∫⁻ β in 𝓖, ‖A q β * χ₀ β‖ₑ ∂lam < ∞ := by
    calc ∑' q, ∫⁻ β in 𝓖, ‖A q β * χ₀ β‖ₑ ∂lam ≤ ∑' q, ∫⁻ β in 𝓖, ENNReal.ofReal M * ‖A q β‖ₑ ∂lam :=
          ENNReal.tsum_le_tsum fun q => lintegral_mono fun β => by
            rw [enorm_mul, mul_comm]
            refine mul_le_mul' ?_ le_rfl
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hM β)
      _ = ENNReal.ofReal M * ∑' q, ∫⁻ β in 𝓖, ‖A q β‖ₑ ∂lam := by
          simp_rw [lintegral_const_mul _ (hmeasA _)]
          exact ENNReal.tsum_mul_left
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsumA

  set J : Q → ℂ := fun q => ∫ β in 𝓖, A q β * χ₀ β ∂lam with hJ
  have hmeasAχ : ∀ q, AEStronglyMeasurable (fun β => A q β * χ₀ β) (lam.restrict 𝓖) := fun q =>
    ((hA q).mul hχc).aestronglyMeasurable
  have hLHS : ∫ β in 𝓖, (∑' q, A q β) * χ₀ β ∂lam = ∑' q, J q := by
    simp_rw [← tsum_mul_right]
    exact integral_tsum hmeasAχ hsumAχ.ne
  have hJs : Summable fun q => ‖J q‖ := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) (ENNReal.summable_toReal hsumAχ.ne)
    refine (norm_integral_le_lintegral_norm _).trans_eq ?_
    congr 1
    exact lintegral_congr fun β => ofReal_norm _
  have hJsum : Summable J := hJs.of_norm

  have hint : Integrable (A q₀) lam := by
    refine ⟨(hA q₀).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, h𝓖.lintegral_eq_tsum'']
    refine lt_of_le_of_lt ?_ hsumA
    calc ∑' ν : Λ, ∫⁻ β in 𝓖, ‖A q₀ (ν +ᵥ β)‖ₑ ∂lam = ∑' ν : Λ, ∫⁻ β in 𝓖, ‖A (act q₀ ν) β‖ₑ ∂lam :=
          tsum_congr fun ν => lintegral_congr fun β => by
            rw [hAact, AddSubgroup.vadd_def, vadd_eq_add, add_comm]
      _ ≤ ∑' q, ∫⁻ β in 𝓖, ‖A q β‖ₑ ∂lam :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun q => ∫⁻ β in 𝓖, ‖A q β‖ₑ ∂lam)
  have hintχ : Integrable (fun β => A q₀ β * χ₀ β) lam := by
    refine Integrable.mono' (hint.norm.const_mul M) ((hA q₀).mul hχc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM β) (norm_nonneg _)
  refine ⟨hint, hintχ, ?_⟩
  rw [hLHS]

  letI s : Setoid Q :=
    { r := fun q q' => ∃ ν, act q ν = q'
      iseqv := ⟨fun q => ⟨0, hact0 q⟩, fun ⟨ν, h⟩ => ⟨-ν, by rw [← h, hactneg]⟩,
        fun ⟨ν, h⟩ ⟨ν', h'⟩ => ⟨ν + ν', by rw [← hact, h, h']⟩⟩ }
  have hmem : ∀ q q' : Q, (⟦q⟧ : Quotient s) = ⟦q'⟧ → ∃ ν, act q' ν = q := fun q q' h => by
    obtain ⟨ν, hν⟩ := Quotient.exact h
    exact ⟨-ν, by rw [← hν, hactneg]⟩
  have hdecomp : ∑' q, J q = ∑' c : Quotient s, ∑' x : {q // (⟦q⟧ : Quotient s) = c}, J x := by
    rw [← (Equiv.sigmaFiberEquiv (fun q : Q => (⟦q⟧ : Quotient s))).tsum_eq]
    exact Summable.tsum_sigma' (fun c => hJsum.comp_injective Subtype.val_injective)
      ((Equiv.sigmaFiberEquiv _).summable_iff.2 hJsum)
  have hbig : ∑' x : {q // (⟦q⟧ : Quotient s) = ⟦q₀⟧}, J x = ∫ β, A q₀ β * χ₀ β ∂lam := by
    let eb : Λ ≃ {q // (⟦q⟧ : Quotient s) = ⟦q₀⟧} :=
      Equiv.ofBijective (fun ν => ⟨act q₀ ν, Quotient.sound (s := s) ⟨-ν, hactneg q₀ ν⟩⟩)
        ⟨fun ν ν' h => hinj (congrArg Subtype.val h), fun x => by
          obtain ⟨ν, hν⟩ := hmem x q₀ x.2
          exact ⟨ν, Subtype.ext hν⟩⟩
    rw [← eb.tsum_eq, h𝓖.integral_eq_tsum'' _ hintχ]
    refine tsum_congr fun ν => ?_
    show ∫ β in 𝓖, A (act q₀ ν) β * χ₀ β ∂lam = _
    congr 1
    funext β
    rw [hAact, AddSubgroup.vadd_def, vadd_eq_add, add_comm (ν : V) β, hχadd β ν, hχΛ, mul_one]
  have hsmall0 : ∀ c : Quotient s, c ≠ ⟦q₀⟧ → ∑' x : {q // (⟦q⟧ : Quotient s) = c}, J x = 0 := by
    intro c hc
    have hq₁c : (⟦c.out⟧ : Quotient s) = c := Quotient.out_eq c
    have hnot : ∀ ν, act q₀ ν ≠ c.out := fun ν h => hc (by
      rw [← hq₁c, ← h]
      exact Quotient.sound (s := s) ⟨-ν, hactneg q₀ ν⟩)
    obtain ⟨β₀, hβ₀, hinv⟩ := hsmall c.out hnot
    have hmemc : ∀ x : {q // (⟦q⟧ : Quotient s) = c}, ∃ ν, act c.out ν = x := fun x =>
      hmem x c.out (x.2.trans hq₁c.symm)
    set H : V → ℂ := fun β => ∑' x : {q // (⟦q⟧ : Quotient s) = c}, A x β with hH
    have hfib : ∑' x : {q // (⟦q⟧ : Quotient s) = c}, J x = ∫ β in 𝓖, H β * χ₀ β ∂lam := by
      simp only [hH, hJ]
      simp_rw [← tsum_mul_right]
      refine (integral_tsum (f := fun (x : {q // (⟦q⟧ : Quotient s) = c}) β => A x β * χ₀ β)
        (fun x => hmeasAχ x.1) ?_).symm
      exact ne_top_of_le_ne_top hsumAχ.ne
        (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun q => ∫⁻ β in 𝓖, ‖A q β * χ₀ β‖ₑ ∂lam))
    rw [hfib]
    refine setIntegral_fd_eq_zero h𝓖 (fun β => H β * χ₀ β) (fun ν β => ?_) β₀ (χ₀ β₀) hβ₀ (fun β => ?_)
    · have hper : H (β + ν) = H β := by
        let ec : {q // (⟦q⟧ : Quotient s) = c} ≃ {q // (⟦q⟧ : Quotient s) = c} :=
          ⟨fun x => ⟨act x ν, (Quotient.sound (s := s) ⟨-ν, hactneg x ν⟩).trans x.2⟩,
            fun x => ⟨act x (-ν), (Quotient.sound (s := s) ⟨ν, hactneg' x ν⟩).trans x.2⟩,
            fun x => Subtype.ext (hactneg x ν), fun x => Subtype.ext (hactneg' x ν)⟩
        simp only [hH]
        rw [← ec.tsum_eq (fun x => A x β)]
        exact tsum_congr fun x => (hAact x ν β).symm
      show H (β + ν) * χ₀ (β + ν) = H β * χ₀ β
      rw [hper, hχadd, hχΛ, mul_one]
    · have htr : H (β + β₀) = H β := tsum_congr fun x => by
        obtain ⟨ν, hν⟩ := hmemc x
        rw [← hν]
        exact hinv ν β
      show H (β + β₀) * χ₀ (β + β₀) = χ₀ β₀ * (H β * χ₀ β)
      rw [htr, hχadd]
      ring
  rw [hdecomp, tsum_eq_single (⟦q₀⟧ : Quotient s) hsmall0, hbig]

end PositivityTheory.SiegelWeilFormula.kunf

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}

theorem unfoldCore (B : Base F E) (hB : B.IsGood σ) (hb : IsFrame2 σ Y b) {nb : nA σ Y b → G2 σ Y}
    {lam : Measure (nA σ Y b)} {𝓖 : Set (nA σ Y b)} (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (φ : G2 σ Y → ℂ) (hφ : Continuous φ) (hrat : ∀ p ∈ par2 σ Y, p ∈ rat2 σ Y → ∀ y, φ (p * y) = φ y)
    (hone : ∀ p t, IsPar p t → Matrix.GeneralLinearGroup.det t = 1 → ∀ y, φ (p * y) = φ y)
    (hmaj : ∀ C : Set (G2 σ Y), IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ Y) (rat2 σ Y) φ g q‖ ≤ u q)
    {ε : ℤˣ} {w : G2 σ Y} (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (x : G2 σ Y) :
    Integrable (fun β => φ (w * nb β * x)) lam ∧ ∀ T : nF σ Y b, IsND T →
      fc B.ψ b nb lam 𝓖 (GlobalTheory.Eis.cosetSum (par2 σ Y) (rat2 σ Y) φ) T x =
        ∫ β, φ (w * nb β * x) * B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β.1).trace)) ∂lam := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    obtain ⟨hnb, hHaar, h𝓖, -⟩ := hc
    have := hHaar
    have : Countable (rat2 σ Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ Y
    have : Countable (GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y)) := Quotient.countable
    obtain ⟨ε₀, hε₀⟩ := hb.1

    have hw_rat : w ∈ rat2 σ Y := by
      refine rat_of_inFrame (b := b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
      rw [hw]
      ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp

    have hLI : GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ Y ⊓ rat2 σ Y) φ := fun γ hγ g => hrat γ hγ.1 hγ.2 g

    let nbR : nF σ Y b → rat2 σ Y := fun ν => ⟨nb ν.1, nb_rat hnb ν.2⟩
    have nbR_zero : nbR 0 = 1 := Subtype.ext (nb_zero hnb)
    have nbR_add : ∀ ν ν', nbR (ν + ν') = nbR ν * nbR ν' := fun ν ν' => Subtype.ext (nb_add hnb ν.1 ν'.1)
    let act : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → nF σ Y b → GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) :=
      fun q ν => GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q
    have hact0 : ∀ q, act q 0 = q := fun q => by
      show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR 0) q = q
      rw [nbR_zero, GlobalTheory.AutomorphicL2Unitary.rmul_one]
    have hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν') := fun q ν ν' => by
      show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν') (GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q) = GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR (ν + ν')) q
      rw [nbR_add, GlobalTheory.AutomorphicL2Unitary.rmul_mul]

    let A : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → nA σ Y b → ℂ := fun q β =>
      GlobalTheory.Eis.term (par2 σ Y) (rat2 σ Y) φ (nb β * x) q
    have hA : ∀ q, Continuous (A q) := fun q =>
      hφ.comp (continuous_const.mul ((continuous_nb hnb).mul continuous_const))
    have hAmk : ∀ (γ : rat2 σ Y) β, A (GlobalTheory.AutomorphicL2Unitary.mk _ γ) β = φ (γ.1 * (nb β * x)) := fun γ β =>
      GlobalTheory.Eis.term_mk hLI (nb β * x) γ
    have hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : nA σ Y b)) := fun q ν β => by
      have e : act q ν = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * nbR ν) := by
        show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q = _
        conv_lhs => rw [← Quotient.out_eq q]
        rfl
      rw [e, hAmk]
      show φ ((q.out : rat2 σ Y).1 * nb ν.1 * (nb β * x)) = φ ((q.out : rat2 σ Y).1 * (nb (β + ν.1) * x))
      rw [nb_add hnb, nb_comm hnb β]
      simp only [mul_assoc]

    obtain ⟨C, hC, hcov⟩ := exists_cover B hB hb
    obtain ⟨u, hu, hAu'⟩ := hmaj ((fun β => nb β * x) '' C) (hC.image ((continuous_nb hnb).mul continuous_const))
    have hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q := fun q β hβ => hAu' _ ⟨β, hβ, rfl⟩ q

    let q₀ : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) := GlobalTheory.AutomorphicL2Unitary.mk _ ⟨w, hw_rat⟩
    have hq₀ : ∀ ν, act q₀ ν = GlobalTheory.AutomorphicL2Unitary.mk _ (⟨w, hw_rat⟩ * nbR ν) := fun ν => rfl
    have hinj : Function.Injective (act q₀) := fun ν ν' h => by
      rw [hq₀, hq₀] at h
      obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
      have hP : (w * nb ν'.1) * (w * nb ν.1)⁻¹ ∈ par2 σ Y := by
        have e : (w * nb ν'.1) = (γ : rat2 σ Y).1 * (w * nb ν.1) := (congrArg Subtype.val hγ).symm
        rw [e, mul_inv_cancel_right]
        exact Subgroup.mem_subgroupOf.1 γ.2
      exact (Subtype.ext (big_inj hb hw hnb hP)).symm
    have hAq₀ : ∀ β, A q₀ β = φ (w * nb β * x) := fun β => by
      rw [hAmk, mul_assoc]
    have hI := abs_integrable lam (nF σ Y b) 𝓖 h𝓖 act hact0 hact A hA hAact C hC hcov u hu hAu q₀ hinj
    refine ⟨hI.congr (Filter.Eventually.of_forall hAq₀), fun T hT => ?_⟩

    let χ₀ : nA σ Y b → ℂ := fun β => B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β.1).trace))
    have htr : Continuous fun M : Matrix (Fin n) (Fin n) (AE F E) => Algebra.trace (AF F) (AE F E) M.trace :=
      (IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))).comp continuous_id.matrix_trace
    have hχc : Continuous χ₀ :=
      hB.std.1.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val)).neg)
    have hχadd : ∀ β β', χ₀ (β + β') = χ₀ β * χ₀ β' := fun β β' => by
      simp only [χ₀, AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add]
      exact AddChar.map_add_eq_mul _ _ _
    have hχΛ : ∀ ν : nF σ Y b, χ₀ (ν : nA σ Y b) = 1 := fun ν => by
      simp only [χ₀, AddChar.map_neg_eq_inv, psi_rat hB.std T ν, inv_one]
    have hsmall : ∀ q, (∀ ν, act q₀ ν ≠ q) →
        ∃ β₀, χ₀ β₀ ≠ 1 ∧ ∀ ν β, A (act q ν) (β + β₀) = A (act q ν) β := fun q hq => by
      rcases cells B hB hb hw hnb T hT (q.out : rat2 σ Y).1 (q.out : rat2 σ Y).2 with
        ⟨p, hpP, hpΓ, ν, hνF, hγ⟩ | ⟨β₀, hψ, t, hpar, hdet⟩
      · exfalso
        refine hq ⟨ν, hνF⟩ ?_
        rw [hq₀, ← Quotient.out_eq q]
        refine GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨⟨p, hpΓ⟩, Subgroup.mem_subgroupOf.2 hpP⟩, Subtype.ext ?_⟩
        exact hγ.symm
      · refine ⟨β₀, hψ, fun ν β => ?_⟩
        rw [hAact, hAact]
        show φ ((q.out : rat2 σ Y).1 * (nb (β + β₀ + ν.1) * x)) = φ ((q.out : rat2 σ Y).1 * (nb (β + ν.1) * x))
        set γ := (q.out : rat2 σ Y).1
        have e : γ * (nb (β + β₀ + ν.1) * x) = (γ * nb β₀ * γ⁻¹) * (γ * (nb (β + ν.1) * x)) := by
          rw [show β + β₀ + ν.1 = β₀ + (β + ν.1) by abel, nb_add hnb]
          group
        rw [e, hone _ t hpar hdet]
    obtain ⟨-, -, heq⟩ := abs_unfold lam (nF σ Y b) 𝓖 h𝓖 act hact0 hact A hA hAact χ₀ hχc hχadd hχΛ C hC hcov u hu hAu
      q₀ hinj hsmall
    show ∫ β in 𝓖, GlobalTheory.Eis.cosetSum (par2 σ Y) (rat2 σ Y) φ (nb β * x) * χ₀ β ∂lam = ∫ β, φ (w * nb β * x) * χ₀ β ∂lam
    have e2 : ∫ β, φ (w * nb β * x) * χ₀ β ∂lam = ∫ β, A q₀ β * χ₀ β ∂lam :=
      integral_congr_ae (Filter.Eventually.of_forall fun β => by simp only [hAq₀])
    rw [e2]
    exact heq

end PositivityTheory.SiegelWeilFormula.kunf

end
