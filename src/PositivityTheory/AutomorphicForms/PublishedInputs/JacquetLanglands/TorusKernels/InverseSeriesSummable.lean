module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.InverseSeriesSummable
noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UpperTheory.Esk.InverseSeriesLemmas

theorem enorm_smul_nonneg (r : ℝ) (hr : 0 ≤ r) (x : ℂ) : ‖r • x‖ₑ = ENNReal.ofReal r * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal hr]

theorem hasSum_inv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ)
    (hb : IsCut G b) (y : Y) : HasSum (fun g : G => b (g⁻¹ • y)) 1 := by
  have h := (Equiv.inv G).hasSum_iff.mpr (hb.sum y)
  exact h

theorem tsum_ofReal_inv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ)
    (hb : IsCut G b) (y : Y) : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1 := by
  have hs := UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb y
  calc ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ENNReal.ofReal (∑' g : G, b (g⁻¹ • y)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) hs.summable).symm
    _ = 1 := by rw [hs.tsum_eq, ENNReal.ofReal_one]

end UpperTheory.Esk.InverseSeriesLemmas

open UpperTheory.Esk.InverseSeriesLemmas in
theorem UpperTheory.Esk.inverse_series_summable : UpperTheory.Esk.C3 := by
  unfold UpperTheory.Esk.C3
  intro G Y _ _ _ _ μ hμ b hb f hf hfi
  have hμ' : ∀ g : G, MeasurePreserving (fun y : Y => g • y) μ μ := hμ
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → Y → ℂ, ∀ g y, Φ g y = b y • f (g • y) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : G → Y → ℂ, ∀ g y, Ψ g y = b (g⁻¹ • y) • f y := ⟨_, fun _ _ => rfl⟩
  have hΦm : ∀ g, Measurable (Φ g) := by
    intro g
    rw [show Φ g = fun y => b y • f (g • y) from funext (hΦ g)]
    exact hb.meas.smul (hf.comp (hμ' g).measurable)
  have hΨm : ∀ g, Measurable (Ψ g) := by
    intro g
    rw [show Ψ g = fun y => b (g⁻¹ • y) • f y from funext (hΨ g)]
    exact (hb.meas.comp (hμ' g⁻¹).measurable).smul hf
  have emb : ∀ g : G, MeasurableEmbedding (fun y : Y => g • y) := fun g =>
    (MeasurableEquiv.mk (MulAction.toPerm g) (hμ' g).measurable (hμ' g⁻¹).measurable).measurableEmbedding
  have hΨl : ∀ g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ := fun g =>
    lintegral_congr (fun z => by rw [hΨ, UpperTheory.Esk.InverseSeriesLemmas.enorm_smul_nonneg _ (hb.nonneg _)])
  have hΦl : ∀ g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖Ψ g z‖ₑ ∂μ := by
    intro g
    rw [← (hμ' g).lintegral_comp (hΨm g).enorm]
    exact lintegral_congr (fun y => by rw [hΦ, hΨ, inv_smul_smul])
  have hfin : ∫⁻ z, ‖f z‖ₑ ∂μ < ⊤ := hfi.2
  have hsumΨ : ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := by
    calc ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∑' g : G, ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
          tsum_congr hΨl
      _ = ∫⁻ z, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
          (lintegral_tsum (fun g =>
            ((hb.meas.comp (hμ' g⁻¹).measurable).ennreal_ofReal.mul hf.enorm).aemeasurable)).symm
      _ = ∫⁻ z, ‖f z‖ₑ ∂μ := lintegral_congr (fun z => by
          rw [ENNReal.tsum_mul_right, UpperTheory.Esk.InverseSeriesLemmas.tsum_ofReal_inv b hb z, one_mul])
  have hsumΦ' : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := (tsum_congr hΦl).trans hsumΨ
  have hsumΦ : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ ≠ ⊤ := by rw [hsumΦ']; exact hfin.ne
  have hΦi : ∀ g, ∫ y, Φ g y ∂μ = ∫ z, Ψ g z ∂μ := by
    intro g
    rw [← (hμ' g).integral_comp (emb g) (Ψ g)]
    congr 1
    funext y
    rw [hΦ, hΨ, inv_smul_smul]
  have hΨt : ∫ z, ∑' g, Ψ g z ∂μ = ∑' g, ∫ z, Ψ g z ∂μ :=
    integral_tsum (fun g => (hΨm g).aestronglyMeasurable) (by rw [hsumΨ]; exact hfin.ne)
  have hΨp : ∀ z, ∑' g, Ψ g z = f z := by
    intro z
    simp only [hΨ]
    rw [((UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb z).smul_const (f z)).tsum_eq, one_smul]
  have hΦt : ∫ y, ∑' g, Φ g y ∂μ = ∑' g, ∫ y, Φ g y ∂μ :=
    integral_tsum (fun g => (hΦm g).aestronglyMeasurable) hsumΦ
  have hΦp : ∀ y, ∑' g, Φ g y = b y • ∑' g : G, f (g • y) := by
    intro y
    simp only [hΦ]
    exact tsum_const_smul'' (b y)
  have hfun : (fun y => b y • ∑' g : G, f (g • y)) = fun y => ∑' g, Φ g y :=
    funext (fun y => (hΦp y).symm)
  have heq : ∫ y, b y • ∑' g : G, f (g • y) ∂μ = ∫ y, f y ∂μ := by
    rw [hfun, hΦt, tsum_congr hΦi, ← hΨt]
    congr 1
    funext z
    exact hΨp z
  have hint : Integrable (fun y => ∑' g, Φ g y) μ := by
    refine ⟨AEStronglyMeasurable.tsum (fun g => (hΦm g).aestronglyMeasurable), ?_⟩
    have hle : ∫⁻ y, ‖∑' g, Φ g y‖ₑ ∂μ ≤ ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ :=
      lintegral_mono (fun y => enorm_tsum_le_tsum_enorm)
    have hsum_eq : ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ = ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ :=
      lintegral_tsum (fun g => (hΦm g).enorm.aemeasurable)
    exact lt_of_le_of_lt (hle.trans hsum_eq.le) (lt_top_iff_ne_top.mpr hsumΦ)
  exact ⟨by rw [hfun]; exact hint, heq⟩
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ActionIntegralSwapProof
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Esk.AnnihilatorQuotientResidues

variable {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] {μ : Measure Y}

def actEquiv (hP : Pres G μ) (g : G) : Y ≃ᵐ Y where
  toEquiv := MulAction.toPerm g
  measurable_toFun := (hP g).measurable
  measurable_invFun := (hP g⁻¹).measurable

lemma embed (hP : Pres G μ) (g : G) : MeasurableEmbedding (fun y : Y => g • y) :=
  (actEquiv hP g).measurableEmbedding

lemma enorm_cut {b : Y → ℝ} (hb : IsCut G b) (y : Y) (x : ℂ) :
    ‖b y • x‖ₑ = ENNReal.ofReal (b y) * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal (hb.nonneg y)]

lemma lint_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ
      = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ := by
  rw [← lintegral_tsum]
  · congr 1
    funext y
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb'.nonneg _)
      (hb'.sum y).summable, (hb'.sum y).tsum_eq, ENNReal.ofReal_one, one_mul]
  · intro g
    exact ((ENNReal.measurable_ofReal.comp (hb'.meas.comp (hP g).measurable)).mul
      ((ENNReal.measurable_ofReal.comp hb.meas).mul hu)).aemeasurable

lemma lint_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℝ≥0∞)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ
      = ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ := by
  have h := (hP g).lintegral_comp_emb (embed hP g)
    (fun z => ENNReal.ofReal (b (g⁻¹ • z)) * (ENNReal.ofReal (b' z) * u z))
  rw [← h]
  congr 1
  funext y
  simp only [inv_smul_smul, hinv, mul_left_comm]

lemma lint_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ = ∫⁻ y, ENNReal.ofReal (b' y) * u y ∂μ := by
  rw [lint_split hP hb hb' u hu, lint_split hP hb' hb u hu]
  calc _ = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ :=
        tsum_congr (lint_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq
        (fun g => ∫⁻ y, ENNReal.ofReal (b (g • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ)

lemma integrable_swap [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) : Integrable (fun y => b' y • u y) μ := by
  refine ⟨(hb'.meas.smul hu).aestronglyMeasurable, ?_⟩
  have h := hi.hasFiniteIntegral
  have e := lint_eq hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm (fun g y => by simp only [hinv])
  simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h ⊢
  rwa [← e]

lemma int_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hi : Integrable (fun y => b y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∑' g : G, ∫ y, b' (g • y) • (b y • u y) ∂μ := by
  rw [← integral_tsum]
  · congr 1
    funext y
    rw [(hb'.sum y).summable.tsum_smul_const, (hb'.sum y).tsum_eq, one_smul]
  · intro g
    exact ((hb'.meas.comp (hP g).measurable).smul (hb.meas.smul hu)).aestronglyMeasurable
  · have h := hi.hasFiniteIntegral
    have e := lint_split hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm
    simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h e ⊢
    rw [← e]
    exact h.ne

lemma int_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℂ)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫ y, b' (g • y) • (b y • u y) ∂μ = ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := by
  have h := (hP g).integral_comp (embed hP g) (fun z => b (g⁻¹ • z) • (b' z • u z))
  rw [← h]
  congr 1
  funext y
  rw [inv_smul_smul, hinv, smul_comm]

lemma int_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) (hi' : Integrable (fun y => b' y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∫ y, b' y • u y ∂μ := by
  rw [int_split hP hb hb' u hu hi, int_split hP hb' hb u hu hi']
  calc _ = ∑' g : G, ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := tsum_congr (int_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq (fun g => ∫ y, b (g • y) • (b' y • u y) ∂μ)

end UpperTheory.Esk.AnnihilatorQuotientResidues

theorem UpperTheory.Esk.action_integral_swap_proof : UpperTheory.Esk.C1 := by
  intro G Y _ _ _ _ μ hP b b' hb hb'
  refine ⟨fun u hu hinv => UpperTheory.Esk.AnnihilatorQuotientResidues.lint_eq hP hb hb' u hu hinv, fun u hu hinv hi => ?_⟩
  have hi' := UpperTheory.Esk.AnnihilatorQuotientResidues.integrable_swap hP hb hb' u hu hinv hi
  exact ⟨hi', UpperTheory.Esk.AnnihilatorQuotientResidues.int_eq hP hb hb' u hu hinv hi hi'⟩
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.CountingMeasureInvarianceProof
noncomputable section

open MeasureTheory

namespace UpperTheory.Esk.CountingMeasureInvariance

variable {G Ω X : Type} [Group G] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [Countable Ω]
  [MeasurableSpace X] [MulAction G Ω] [MulAction G X]

theorem meas_of_left {f : Ω × X → ℝ} (hf : ∀ ω, Measurable fun x => f (ω, x)) : Measurable f := by
  intro s hs
  have : f ⁻¹' s = ⋃ ω : Ω, ({ω} : Set Ω) ×ˢ ((fun x => f (ω, x)) ⁻¹' s) := by
    ext ⟨ω, x⟩; simp
  rw [this]
  exact MeasurableSet.iUnion fun ω => (MeasurableSet.of_discrete (s := {ω})).prod (hf ω hs)

omit [Countable Ω] in
theorem count_pres (g : G) :
    MeasurePreserving (fun ω : Ω => g • ω) Measure.count Measure.count := by
  have hm : ∀ h : G, Measurable (fun ω : Ω => h • ω) := fun h => Measurable.of_discrete
  refine ⟨hm g, le_antisymm ((MulAction.injective g).map_count_le (hm g)) ?_⟩
  calc (Measure.count : Measure Ω)
      = (Measure.count.map (fun ω : Ω => g⁻¹ • ω)).map (fun ω => g • ω) := by
        rw [Measure.map_map (hm g) (hm g⁻¹)]
        simp [Function.comp_def]
    _ ≤ Measure.count.map (fun ω : Ω => g • ω) :=
        Measure.map_mono ((MulAction.injective g⁻¹).map_count_le (hm _)) (hm g)

theorem pres_prod (μ : Measure X) [SigmaFinite μ] (hμ : Pres G μ) :
    Pres G ((Measure.count : Measure Ω).prod μ) := fun g =>
  (count_pres g).prod (hμ g)


open Classical in
def cut (R : Set Ω) (β : Ω → X → ℝ) (p : Ω × X) : ℝ := by
  classical
  exact if p.1 ∈ R then β p.1 p.2 else 0

theorem cut_isCut (R : Set Ω) (hR : ∀ ω, ∃! r, r ∈ R ∧ r ∈ MulAction.orbit G ω) (β : Ω → X → ℝ)
    (hβ : ∀ r ∈ R, IsCut (MulAction.stabilizer G r) (β r)) : IsCut G (cut R β) := by
  refine ⟨?_, ?_, ?_⟩
  · refine meas_of_left fun ω => ?_
    by_cases h : ω ∈ R
    · simpa [cut, h] using (hβ ω h).meas
    · simp [cut, h]
  · rintro ⟨ω, x⟩
    unfold cut
    split_ifs with h
    · exact (hβ _ h).nonneg x
    · exact le_rfl
  · rintro ⟨ω, x⟩
    obtain ⟨r, ⟨hrR, g₀, hg₀'⟩, hu⟩ := hR ω
    have hg₀ : g₀ • ω = r := hg₀'
    have key : ∀ g : G, g • ω ∈ R → g • ω = r := fun g hg => hu _ ⟨hg, MulAction.mem_orbit ω g⟩
    let e : MulAction.stabilizer G r → G := fun s => (s : G) * g₀
    have he : Function.Injective e := fun s t h => Subtype.ext (mul_right_cancel h)
    rw [← he.hasSum_iff]
    · convert (hβ r hrR).sum (g₀ • x) using 1
      funext s
      have hs : (s : G) • r = r := s.2
      have h2 : ((s : G) * g₀) • ω = r := by rw [mul_smul, hg₀, hs]
      simp only [Function.comp_apply, e, cut, Prod.smul_mk, h2, mul_smul, Subgroup.smul_def]
      split_ifs with hc
      · rfl
      · exact absurd (h2.symm ▸ hrR) hc
    · intro g hg
      simp only [cut, Prod.smul_mk]
      rw [ite_eq_right]
      intro hgR
      apply hg
      refine ⟨⟨g * g₀⁻¹, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hg₀, inv_smul_smul, key g hgR, hg₀]
      · simp [e]

end UpperTheory.Esk.CountingMeasureInvariance

open UpperTheory.Esk.CountingMeasureInvariance in
theorem UpperTheory.Esk.counting_measure_invariance_proof : UpperTheory.Esk.C1 → UpperTheory.Esk.C4 := by
  intro hC1 G Ω X _ _ _ _ _ _ _ _ μ _ hμ b hb u hu hinv hint R hR β hβ
  have hP : Pres G ((Measure.count : Measure Ω).prod μ) := pres_prod μ hμ
  have hb' := cut_isCut R hR β hβ
  obtain ⟨hI', hE⟩ := (hC1 G (Ω × X) ((Measure.count : Measure Ω).prod μ) hP b (cut R β) hb hb').2
    u hu hinv hint
  have hsec : ∀ ω, Integrable (fun x => cut R β (ω, x) • u (ω, x)) μ := by
    have := hI'.prod_right_ae
    rwa [Measure.ae_count_iff] at this
  have hF : Integrable (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ) Measure.count :=
    hI'.integral_prod_left
  have hsum : HasSum (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ)
      (∫ y, b y • u y ∂((Measure.count : Measure Ω).prod μ)) := by
    rw [hE, integral_prod _ hI', integral_countable hF]
    simp only [count_real_singleton, one_smul]
    exact (integrable_count_iff.mp hF).of_norm.hasSum
  refine ⟨fun r hr => by simpa [cut, hr] using hsec r, ?_⟩
  have hsupp : Function.support (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ) ⊆ R := by
    intro ω hω
    by_contra h
    apply hω
    simp [cut, h]
  rw [← hasSum_subtype_iff_of_support_subset hsupp] at hsum
  convert hsum using 1
  funext r
  simp [cut, r.2]
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfLinTr
noncomputable section

open MeasureTheory

namespace UpperTheory.Esk.LinearTraceLemmas

variable {A Y : Type} [MeasurableSpace Y] (ν : Measure Y) (V : Submodule ℂ (A → ℂ))

def evl (a : A) : Module.Dual ℂ V := (LinearMap.proj a : (A → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype

theorem evl_apply (a : A) (f : V) : evl V a f = f.1 a := rfl

theorem span_evl [FiniteDimensional ℂ V] : Submodule.span ℂ (Set.range (evl V)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ V).surjective f
  have hv : v = 0 := by
    apply Subtype.ext
    funext a
    have h1 : (Module.evalEquiv ℂ V v) (evl V a) = 0 :=
      LinearMap.mem_ker.mp (hfk (Submodule.subset_span ⟨a, rfl⟩))
    have h2 : (Module.evalEquiv ℂ V v) (evl V a) = v.1 a := by
      rfl
    have h3 : v.1 a = 0 := h2.symm.trans h1
    simpa using h3
  exact hf0 (by rw [hv, map_zero])

omit [MeasurableSpace Y] in
theorem bound_mul {g h : Y → ℂ} {n : Y → ℝ} (hn : ∀ y, 0 < n y) (C D : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C * n y) (hD : ∀ y, ‖h y‖ * n y ≤ D) (y : Y) : ‖g y * h y‖ ≤ C * D := by
  have hn' := hn y
  have hC0 : 0 ≤ C := by
    by_contra hneg
    have hlt : C < 0 := not_le.mp hneg
    have : C * n y < 0 := mul_neg_of_neg_of_pos hlt hn'
    linarith [norm_nonneg (g y), hC y]
  rw [norm_mul]
  calc ‖g y‖ * ‖h y‖ ≤ (C * n y) * ‖h y‖ := mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)
    _ = C * (‖h y‖ * n y) := by ring
    _ ≤ C * D := mul_le_mul_of_nonneg_left (hD y) hC0

theorem integrable_mul [IsFiniteMeasure ν] {g h : Y → ℂ} {n : Y → ℝ} (hn : ∀ y, 0 < n y)
    (hg : Measurable g) (hh : Measurable h) (C D : ℝ) (hC : ∀ y, ‖g y‖ ≤ C * n y)
    (hD : ∀ y, ‖h y‖ * n y ≤ D) : Integrable (fun y => g y * h y) ν := by
  exact (integrable_const (C * D)).mono' (hg.mul hh).aestronglyMeasurable
    (ae_of_all _ fun y => bound_mul hn C D hC hD y)

def Good (K : Y → V) (ev : Y → A) (n : Y → ℝ) (φ : Module.Dual ℂ V) : Prop :=
  Measurable (fun y => φ (K y)) ∧ (∃ C, ∀ y, ‖φ (K y)‖ ≤ C * n y) ∧
    ∀ f : V, ∫ y, φ (K y) * f.1 (ev y) ∂ν = φ f

theorem good_all [IsFiniteMeasure ν] [FiniteDimensional ℂ V] (K : Y → V) (ev : Y → A) (n : Y → ℝ)
    (hn : ∀ y, 0 < n y) (hK : ∀ a, Measurable fun y => (K y).1 a)
    (hev : ∀ f : V, Measurable fun y => f.1 (ev y)) (hKb : ∀ a, ∃ C, ∀ y, ‖(K y).1 a‖ ≤ C * n y)
    (hevb : ∀ f : V, ∃ C, ∀ y, ‖f.1 (ev y)‖ * n y ≤ C)
    (hrep : ∀ (f : V) a, ∫ y, (K y).1 a * f.1 (ev y) ∂ν = f.1 a) (φ : Module.Dual ℂ V) :
    Good ν V K ev n φ := by
  have hint : ∀ ψ : Module.Dual ℂ V, Good ν V K ev n ψ → ∀ f : V,
      Integrable (fun y => ψ (K y) * f.1 (ev y)) ν := by
    intro ψ hψ f
    obtain ⟨C, hC⟩ := hψ.2.1
    obtain ⟨D, hD⟩ := hevb f
    exact integrable_mul ν hn hψ.1 (hev f) C D hC hD
  have hadd : ∀ φ₁ φ₂, Good ν V K ev n φ₁ → Good ν V K ev n φ₂ → Good ν V K ev n (φ₁ + φ₂) := by
    intro φ₁ φ₂ h₁ h₂
    obtain ⟨C₁, hC₁⟩ := h₁.2.1
    obtain ⟨C₂, hC₂⟩ := h₂.2.1
    refine ⟨h₁.1.add h₂.1, ⟨C₁ + C₂, fun y => ?_⟩, fun f => ?_⟩
    · rw [LinearMap.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hC₁ y) (hC₂ y))
    · simp only [LinearMap.add_apply, add_mul]
      rw [integral_add (hint φ₁ h₁ f) (hint φ₂ h₂ f), h₁.2.2 f, h₂.2.2 f]
  have hzero : Good ν V K ev n 0 := by
    refine ⟨?_, ⟨0, fun y => ?_⟩, fun f => ?_⟩
    · simp
    · simp
    · simp
  have hsmul : ∀ (c : ℂ) φ, Good ν V K ev n φ → Good ν V K ev n (c • φ) := by
    intro c φ h
    obtain ⟨C, hC⟩ := h.2.1
    refine ⟨h.1.const_mul c, ⟨‖c‖ * C, fun y => ?_⟩, fun f => ?_⟩
    · rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)
    · simp only [LinearMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, h.2.2 f]
  obtain ⟨Sg, hSg⟩ : ∃ Sg : Submodule ℂ (Module.Dual ℂ V), ∀ ψ, ψ ∈ Sg ↔ Good ν V K ev n ψ :=
    ⟨{ carrier := {ψ | Good ν V K ev n ψ}
       add_mem' := fun {a b} ha hb => hadd a b ha hb
       zero_mem' := hzero
       smul_mem' := fun c ψ h => hsmul c ψ h }, fun _ => Iff.rfl⟩
  have hev' : ∀ a, Good ν V K ev n (evl V a) := by
    intro a
    refine ⟨?_, ?_, fun f => ?_⟩
    · simpa only [evl_apply] using hK a
    · simpa only [evl_apply] using hKb a
    · simpa only [evl_apply] using hrep f a
  have htop : Sg = ⊤ := by
    rw [eq_top_iff, ← span_evl V, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact (hSg _).mpr (hev' a)
  exact (hSg φ).mp (by rw [htop]; exact Submodule.mem_top)

theorem main : UpperTheory.Esk.LinTr := by
  intro A Y _ ν _ V _ T K ev n _ hn hK hev hKb hevb hrep
  have hgood : ∀ φ : Module.Dual ℂ V, Good ν V K ev n φ :=
    good_all ν V K ev n hn hK hev hKb hevb hrep
  let b := Module.finBasis ℂ V
  have hexp : ∀ y, (T (K y)).1 (ev y) = ∑ i, b.coord i (K y) * (T (b i)).1 (ev y) := by
    intro y
    have e : T (K y) = ∑ i, b.repr (K y) i • T (b i) := by
      conv_lhs => rw [← b.sum_repr (K y)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul]
    rw [e]
    simp [Module.Basis.coord_apply]
  have hmeas : Measurable fun y => (T (K y)).1 (ev y) := by
    simp_rw [hexp]
    exact Finset.measurable_sum _ fun i _ => (hgood (b.coord i)).1.mul (hev (T (b i)))
  have hbd : ∃ C, ∀ y, ‖(T (K y)).1 (ev y)‖ ≤ C := by
    choose Cs hCs using fun i => (hgood (b.coord i)).2.1
    choose Ds hDs using fun i => hevb (T (b i))
    refine ⟨∑ i, Cs i * Ds i, fun y => ?_⟩
    rw [hexp]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => bound_mul hn (Cs i) (Ds i) (hCs i) (hDs i) y)
  have hintg : ∀ i, Integrable (fun y => b.coord i (K y) * (T (b i)).1 (ev y)) ν := by
    intro i
    obtain ⟨C, hC⟩ := (hgood (b.coord i)).2.1
    obtain ⟨D, hD⟩ := hevb (T (b i))
    exact integrable_mul ν hn (hgood (b.coord i)).1 (hev (T (b i))) C D hC hD
  refine ⟨hmeas, hbd, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ b T, Matrix.trace]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => hintg i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hgood (b.coord i)).2.2 (T (b i))]
  simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]

end UpperTheory.Esk.LinearTraceLemmas

theorem UpperTheory.Esk.pf_LinTr : UpperTheory.Esk.LinTr := by
  exact UpperTheory.Esk.LinearTraceLemmas.main
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ContinuousCompTorusMap
noncomputable section

namespace UpperTheory.Esk.OrbitalSingularIntegrals

open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood

open scoped Real

def SepHol {n : ℕ} (f : (Fin n → ℂ) → ℂ) (S : Set (Fin n → ℂ)) : Prop :=
  ContinuousOn f S ∧ ∀ ζ ∈ S, ∀ i, DifferentiableAt ℂ (fun t => f (Function.update ζ i t)) (ζ i)

theorem continuous_comp_torusMap' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall c r)) :
    Continuous fun θ => f (torusMap c (fun _ => r) θ) :=
  hf.comp_continuous (continuous_torusMap c r) (torusMap_mem_closedBall c hr)

theorem torusIntegrable_kernel' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall c r)) (hz : z ∈ ball c r) :
    TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * f ζ) c (fun _ => r) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  refine Continuous.mul ?_ (continuous_comp_torusMap' hr.le hf)
  refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr hz θ i
  exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const

theorem cauchy' : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : ℝ), 0 < r →
    SepHol f (closedBall c r) → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ) = (2 * π * I) ^ n * f z := by
  intro n
  induction n with
  | zero =>
    intro f c r _ _ z _
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | succ n ih =>
    intro f c r hr hf z hz
    rw [torusIntegral_succ (torusIntegrable_kernel' hr hf.1 hz)]
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr).mp hz 0
    have hz' : Fin.tail z ∈ ball (fun i => c (Fin.succ i)) r :=
      (mem_ball_pi_iff hr).mpr fun i => (mem_ball_pi_iff hr).mp hz i.succ
    have hcons : ∀ x ∈ closedBall (c 0) r, ∀ y ∈ closedBall (fun i => c (Fin.succ i)) r,
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ closedBall c r := by
      intro x hx y hy
      refine (mem_closedBall_pi_iff hr.le).mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * f (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * f (Fin.cons x (Fin.tail z)))) (sphere (c 0) r) := by
      intro x hx
      have hxc : x ∈ closedBall (c 0) r := sphere_subset_closedBall hx
      have hS : SepHol (fun y => f (Fin.cons x y)) (closedBall (fun i => c (Fin.succ i)) r) := by
        refine ⟨?_, fun ζ hζ j => ?_⟩
        · exact hf.1.comp (differentiable_cons_right x).continuous.continuousOn
            (fun y hy => hcons x hxc y hy)
        · have h1 := hf.2 (Fin.cons x ζ) (hcons x hxc ζ hζ) j.succ
          have e : (fun t => f (Fin.cons x (Function.update ζ j t) : Fin (n + 1) → ℂ)) =
              fun t => f (Function.update (Fin.cons x ζ : Fin (n + 1) → ℂ) j.succ t) := by
            funext t
            rw [Fin.cons_update]
          show DifferentiableAt ℂ (fun t => f (Fin.cons x (Function.update ζ j t) : Fin (n + 1) → ℂ)) (ζ j)
          rw [e]
          simpa only [Fin.cons_succ] using h1
      have htail := ih (fun y => f (Fin.cons x y)) (fun i => c (Fin.succ i)) r hr hS (Fin.tail z) hz'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at htail
      rw [htail]
      ring
    rw [circleIntegral.integral_congr hr.le key, circleIntegral.integral_const_mul]
    have hd : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) := by
      intro x hx
      have h1 := hf.2 (Fin.cons x (Fin.tail z)) (hcons x hx _ (ball_subset_closedBall hz')) 0
      simp only [Fin.update_cons_zero, Fin.cons_zero] at h1
      exact h1.differentiableWithinAt
    have h1 := hd.circleIntegral_sub_inv_smul hz0
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

variable {n : ℕ}

theorem integrableOn_fctl' {c : Fin n → ℂ} {r : ℝ} {f : (Fin n → ℂ) → ℂ}
    (hc : Continuous fun θ => f (torusMap c (fun _ => r) θ)) (g : C(Cube n, ℂ)) :
    IntegrableOn (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  exact ((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul hc

def fctlCLM' (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ)
    (hc : Continuous fun θ => f (torusMap c (fun _ => r) θ)) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (integrableOn_fctl' hc g) (integrableOn_fctl' hc g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul hc).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

theorem fctlCLM'_kern {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : SepHol f (closedBall c r)) (hz : z ∈ ball c r) :
    fctlCLM' c r f (continuous_comp_torusMap' hr.le hf.1) (kern c r z) = (2 * π * I) ^ n * f z := by
  rw [← cauchy' n f c r hr hf z hz]
  show fctl c r f (kern c r z) = _
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  simp only [jac, kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul]
  ring

theorem osgFin (U : Set (Fin n → ℂ)) (hU : IsOpen U) (f : (Fin n → ℂ) → ℂ) (hf : SepHol f U) :
    AnalyticOnNhd ℂ f U := by
  intro z0 hz0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z0 hz0
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : closedBall z0 (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hS : SepHol f (closedBall z0 (ε / 2)) :=
    ⟨hf.1.mono hsub, fun ζ hζ i => hf.2 ζ (hsub hζ) i⟩
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have han : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ *
      fctlCLM' z0 (ε / 2) f (continuous_comp_torusMap' hr.le hS.1) (kern z0 (ε / 2) z)) z0 :=
    analyticAt_const.mul (((fctlCLM' z0 (ε / 2) f _).analyticAt _).comp (kern_analyticAt z0 hr))
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  rw [fctlCLM'_kern hr hS hz, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end UpperTheory.Esk.OrbitalSingularIntegrals

open UpperTheory.Esk.OrbitalSingularIntegrals in
theorem UpperTheory.Esk.pf_Osg : UpperTheory.Esk.Osg := by
  intro I _ _ U hU f hf hsep
  set n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let Φ : (Fin n → ℂ) → (I → ℂ) := fun w i => w (e i)
  have hΦ : Continuous Φ := continuous_pi fun i => continuous_apply (e i)
  let g : (Fin n → ℂ) → ℂ := fun w => f (Φ w)
  let V : Set (Fin n → ℂ) := Φ ⁻¹' U
  have hV : IsOpen V := hU.preimage hΦ
  have hupd : ∀ (w : Fin n → ℂ) (j : Fin n) (t : ℂ), Φ (Function.update w j t) = Function.update (Φ w) (e.symm j) t := by
    intro w j t
    funext i
    by_cases h : i = e.symm j
    · subst h
      simp [Φ]
    · have h' : e i ≠ j := fun h' => h (by rw [← h']; simp)
      simp [Φ, h, h']
  have hg : SepHol g V := by
    refine ⟨hf.comp hΦ.continuousOn (fun w hw => hw), fun w hw j => ?_⟩
    have h1 := hsep (Φ w) hw (e.symm j)
    have e1 : (fun t => g (Function.update w j t)) = fun t => f (Function.update (Φ w) (e.symm j) t) := by
      funext t
      simp only [g, hupd]
    rw [e1]
    simpa [Φ] using h1
  have hA := osgFin V hV g hg
  let Ψ : (I → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm j)
  have hΨ : ∀ z, Φ (Ψ z) = z := by
    intro z
    funext i
    simp [Φ, Ψ]
  intro z hz
  have hmem : Ψ z ∈ V := by
    show Φ (Ψ z) ∈ U
    rw [hΨ]
    exact hz
  have h2 := (hA (Ψ z) hmem).comp (Ψ.analyticAt z)
  have hfe : g ∘ Ψ = f := by
    funext w
    simp only [Function.comp, g, hΨ]
  rwa [hfe] at h2
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.RSubPowApply
namespace UpperTheory.Esk.CommutingOperatorTraces

open Module Module.End

variable {J V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

noncomputable def E (T : J → Module.End ℂ V) (s : J → ℂ) : Submodule ℂ V :=
  ⨅ j, (T j).maxGenEigenspace (s j)

lemma mapsTo_E (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (i : J) : Set.MapsTo (T i) (E T s) (E T s) := by
  intro x hx
  simp only [E, SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
  intro j
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hT j i) (s j) (hx j)

lemma mapsTo_prod (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) : Set.MapsTo (W.map T).prod (E T s) (E T s) := by
  induction W with
  | nil => intro x hx; simpa using hx
  | cons a W ih =>
    intro x hx
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact mapsTo_E T hT s a (ih hx)

noncomputable def R (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (j : J) : Module.End ℂ (E T s) :=
  (T j).restrict (mapsTo_E T hT s j)

lemma R_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (j : J) (x : E T s) : ((R T hT s j x : E T s) : V) = T j x := rfl

lemma R_comm (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (i j : J) : Commute (R T hT s i) (R T hT s j) := by
  show R T hT s i * R T hT s j = R T hT s j * R T hT s i
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp only [Module.End.mul_apply, R_apply]
  exact LinearMap.congr_fun (hT i j) x

lemma R_prod_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) (x : E T s) : (((W.map (R T hT s)).prod x : E T s) : V) = (W.map T).prod x := by
  induction W with
  | nil => simp
  | cons a W ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, R_apply, ih]

lemma R_sub_pow_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i)
    (s : J → ℂ) (j : J) (n : ℕ) (x : E T s) :
    ((((R T hT s j - algebraMap ℂ _ (s j)) ^ n) x : E T s) : V) = ((T j - s j • 1) ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    rw [← ih]
    simp [R_apply, Algebra.algebraMap_eq_smul_one]

lemma R_nil (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ) (j : J) :
    IsNilpotent (R T hT s j - algebraMap ℂ _ (s j)) := by
  rw [Module.End.isNilpotent_iff_of_finite]
  intro x
  have hx := x.2
  simp only [E] at hx
  obtain ⟨k, hk⟩ := (Module.End.mem_iInf_maxGenEigenspace_iff T s (x : V)).mp hx j
  refine ⟨k, Subtype.ext ?_⟩
  rw [R_sub_pow_apply, hk]
  rfl

lemma trace_R_prod (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) : LinearMap.trace ℂ (E T s) (W.map (R T hT s)).prod =
      (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
  induction W with
  | nil => simp [LinearMap.trace_one]
  | cons a W ih =>
    have hc : Commute (W.map (R T hT s)).prod (R T hT s a) := by
      apply Commute.list_prod_left
      intro y hy
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy
      exact R_comm T hT s b a
    simp only [List.map_cons, List.prod_cons]
    rw [← hc.eq, Module.End.mul_eq_comp,
      LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent (s a) hc (R_nil T hT s a), ih]
    ring

lemma trace_restrict (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) (h : Set.MapsTo (W.map T).prod (E T s) (E T s)) :
    LinearMap.trace ℂ (E T s) ((W.map T).prod.restrict h) =
      (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
  have : (W.map T).prod.restrict h = (W.map (R T hT s)).prod := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [R_prod_apply]
    rfl
  rw [this, trace_R_prod]

lemma exists_eigvec (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (hs : E T s ≠ ⊥) : ∃ f : V, f ≠ 0 ∧ ∀ j, T j f = s j • f := by
  classical
  let P : Set (Submodule ℂ V) :=
    {U | U ≠ ⊥ ∧ U ≤ E T s ∧ ∀ j, ∀ x ∈ U, T j x ∈ U}
  have hP : (E T s) ∈ P := ⟨hs, le_rfl, fun j x hx => mapsTo_E T hT s j hx⟩
  obtain ⟨U, ⟨hU0, hUE, hUT⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min P ⟨_, hP⟩
  obtain ⟨x, hxU, hx0⟩ := (Submodule.ne_bot_iff U).mp hU0
  refine ⟨x, hx0, fun j => ?_⟩

  have hsub : ∀ n : ℕ, ∀ y ∈ U, ((T j - s j • 1) ^ n) y ∈ U := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      have h1 := ih y hy
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact U.sub_mem (hUT j _ h1) (U.smul_mem _ h1)
  let U' : Submodule ℂ V := U ⊓ (T j).eigenspace (s j)
  have hU'P : U' ∈ P := by
    refine ⟨?_, inf_le_left.trans hUE, ?_⟩
    · have hxE : x ∈ E T s := hUE hxU
      simp only [E] at hxE
      have hex := (Module.End.mem_iInf_maxGenEigenspace_iff T s x).mp hxE j
      let k := Nat.find hex
      have hk : ((T j - s j • 1) ^ k) x = 0 := Nat.find_spec hex
      have hk0 : k ≠ 0 := by
        intro h0
        rw [h0, pow_zero, Module.End.one_apply] at hk
        exact hx0 hk
      obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hne : ((T j - s j • 1) ^ k') x ≠ 0 := by
        have := Nat.find_min hex (show k' < k by omega)
        exact this
      rw [Submodule.ne_bot_iff]
      refine ⟨((T j - s j • 1) ^ k') x, ⟨hsub k' x hxU, ?_⟩, hne⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h2 : ((T j - s j • 1) ^ k) x = 0 := hk
      rw [hk', pow_succ', Module.End.mul_apply] at h2
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h2
      exact sub_eq_zero.mp h2
    · intro i y hy
      refine ⟨hUT i y hy.1, ?_⟩
      have hy2 : T j y = s j • y := (Module.End.mem_eigenspace_iff).mp hy.2
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := LinearMap.congr_fun (hT j i) y
      simp only [Module.End.mul_apply] at this
      rw [this, hy2, map_smul]
  have hle : U' ≤ U := inf_le_left
  have hUU : U' = U := by
    by_contra hne
    exact hmin U' hU'P (lt_of_le_of_ne hle hne)
  have hxU' : x ∈ U' := hUU ▸ hxU
  exact (Module.End.mem_eigenspace_iff).mp hxU'.2

end UpperTheory.Esk.CommutingOperatorTraces

open UpperTheory.Esk.CommutingOperatorTraces in
theorem UpperTheory.Esk.pf_Sys : UpperTheory.Esk.Sys := by
  intro J V _ _ _ T hT
  classical
  have hind : iSupIndep (E T) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hT j i) φ)
  have htop : ⨆ s, E T s = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T
      (fun i j _ => hT i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (T i))
  have hfin : {s | E T s ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have htr : ∀ W : List J, LinearMap.trace ℂ V (W.map T).prod =
      ∑ s ∈ hfin.toFinset, (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
    intro W
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin (mapsTo_prod T hT · W)]
    exact Finset.sum_congr rfl fun s _ => trace_restrict T hT s W _
  refine ⟨hfin.toFinset, fun s => Module.finrank ℂ (E T s), ?_, ?_, ?_, htr⟩
  · intro s
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · exact exists_eigvec T hT s
    · rintro ⟨f, hf0, hf⟩ hbot
      have hfE : f ∈ E T s := by
        simp only [E, Submodule.mem_iInf]
        intro j
        apply Module.End.eigenspace_le_maxGenEigenspace
        exact (Module.End.mem_eigenspace_iff).mpr (hf j)
      rw [hbot, Submodule.mem_bot] at hfE
      exact hf0 hfE
  · intro s hs
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hs
    exact Submodule.one_le_finrank_iff.mpr hs
  · have h0 := htr []
    simp only [List.map_nil, List.prod_nil, LinearMap.trace_one, mul_one] at h0
    exact_mod_cast h0.symm
end
