module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Unimod

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Unfold
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldAbsAlt
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LintFibre
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldAbs
noncomputable section

namespace PI.VolStabS

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]

instance subMeasurableMul (H : Subgroup G) : MeasurableMul H where
  measurable_const_mul c := by
    exact (((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(c : G) * x, H.mul_mem c.2 x.2⟩ : H))
  measurable_mul_const c := by
    exact (((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(x : G) * c, H.mul_mem x.2 c.2⟩ : H))

instance subMeasurableInv (H : Subgroup G) : MeasurableInv H where
  measurable_inv := by
    exact ((measurable_inv.comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(x : G)⁻¹, H.inv_mem x.2⟩ : H))

theorem countable_subgroupOf {Γ H : Subgroup G} [Countable Γ] :
    Countable ((Γ ⊓ H).subgroupOf H) := by
  refine Function.Injective.countable
    (f := fun x : (Γ ⊓ H).subgroupOf H =>
      (⟨((x : H) : G), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩ : Γ)) ?_
  intro a b hab
  have e : ((a : H) : G) = ((b : H) : G) := congrArg (fun z : Γ => (z : G)) hab
  exact Subtype.ext (Subtype.ext e)

variable [MulAction G Y]

def orbS (Γ : Subgroup G) (y0 : Y) : Set Y := {x | ∃ γ ∈ Γ, γ • y0 = x}

def repO (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : G :=
  Classical.choose (x.2 : ∃ γ ∈ Γ, γ • y0 = (x : Y))

theorem repO_mem (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x ∈ Γ := by
  exact (Classical.choose_spec x.2).1

theorem repO_smul (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x • y0 = x := by
  exact (Classical.choose_spec x.2).2

def cntN (Γ : Subgroup G) (A : Set G) (g : G) : ℝ≥0∞ :=
  ∑' γ : Γ, A.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g)

def cfun (Γ : Subgroup G) (A : Set G) (y0 : Y) (g : G) : ℝ≥0∞ :=
  ∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹)

theorem meas_cfun (Γ : Subgroup G) (y0 : Y) [Countable (orbS Γ y0)] {A : Set G}
    (hA : MeasurableSet A) : Measurable (cfun Γ A y0) := by
  unfold cfun
  exact Measurable.tsum fun x =>
    (measurable_const.indicator hA).comp ((measurable_const_mul (repO Γ y0 x)).comp measurable_inv)

theorem sum_rep_eq {Γ H : Subgroup G} (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (u : G → ℝ≥0∞) :
    ∑' x : orbS Γ y0, ∑' δ : (Γ ⊓ H).subgroupOf H, u (repO Γ y0 x * ((δ : H) : G)) =
      ∑' γ : Γ, u γ := by
  classical
  let F : orbS Γ y0 × (Γ ⊓ H).subgroupOf H → Γ := fun p =>
    ⟨repO Γ y0 p.1 * ((p.2 : H) : G), Γ.mul_mem (repO_mem Γ y0 p.1)
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 p.2.2)).1⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨x, δ⟩ ⟨x', δ'⟩ he
      have he' : repO Γ y0 x * ((δ : H) : G) = repO Γ y0 x' * ((δ' : H) : G) := congrArg Subtype.val he
      have hδ : ((δ : H) : G) • y0 = y0 := (hH _).1 (δ : H).2
      have hδ' : ((δ' : H) : G) • y0 = y0 := (hH _).1 (δ' : H).2
      have hx : (x : Y) = x' := by
        calc (x : Y) = repO Γ y0 x • y0 := (repO_smul Γ y0 x).symm
          _ = repO Γ y0 x • (((δ : H) : G) • y0) := by rw [hδ]
          _ = (repO Γ y0 x * ((δ : H) : G)) • y0 := (mul_smul _ _ _).symm
          _ = (repO Γ y0 x' * ((δ' : H) : G)) • y0 := by rw [he']
          _ = repO Γ y0 x' • (((δ' : H) : G) • y0) := mul_smul _ _ _
          _ = repO Γ y0 x' • y0 := by rw [hδ']
          _ = x' := repO_smul Γ y0 x'
      have hxx : x = x' := Subtype.ext hx
      subst hxx
      have e : ((δ : H) : G) = ((δ' : H) : G) := mul_left_cancel he'
      exact Prod.ext rfl (Subtype.ext (Subtype.ext e))
    · intro γ
      have hd : (repO Γ y0 ⟨(γ : G) • y0, γ, γ.2, rfl⟩)⁻¹ * γ ∈ H := by
        rw [hH, mul_smul, inv_smul_eq_iff, repO_smul]
      refine ⟨(⟨(γ : G) • y0, γ, γ.2, rfl⟩, ⟨⟨_, hd⟩, Subgroup.mem_subgroupOf.2
        (Subgroup.mem_inf.2 ⟨Γ.mul_mem (Γ.inv_mem (repO_mem Γ y0 _)) γ.2, hd⟩)⟩), ?_⟩
      apply Subtype.ext
      exact mul_inv_cancel_left _ _
  calc _ = ∑' p : orbS Γ y0 × (Γ ⊓ H).subgroupOf H, u (repO Γ y0 p.1 * ((p.2 : H) : G)) :=
        (ENNReal.tsum_prod (f := fun x (δ : (Γ ⊓ H).subgroupOf H) => u (repO Γ y0 x * ((δ : H) : G)))).symm
    _ = ∑' γ : Γ, u γ := (Equiv.ofBijective F hF).tsum_eq (fun γ : Γ => u γ)

end Abs

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs2

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y]

theorem lint_fibre {Γ H : Subgroup G} [Countable Γ] (μ' : Measure H) [μ'.IsMulLeftInvariant]
    [μ'.IsInvInvariant] (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0) [Countable (orbS Γ y0)]
    {A : Set G} (hA : MeasurableSet A)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ')
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρi : ∀ γ ∈ Γ, ∀ g, ρ (γ * g) = ρ g) (s : G) :
    ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
  have : Countable ((Γ ⊓ H).subgroupOf H) := countable_subgroupOf
  have : MeasurableSMul ((Γ ⊓ H).subgroupOf H) H :=
    { measurable_const_smul := fun c => measurable_const_mul (c : H)
      measurable_smul_const := fun x => (measurable_mul_const x).comp measurable_subtype_coe }
  have : SMulInvariantMeasure ((Γ ⊓ H).subgroupOf H) H μ' :=
    ⟨fun c t _ => measure_preimage_mul μ' (c : H) t⟩
  have hg : Measurable fun k : H => s * (k : G)⁻¹ :=
    (measurable_const_mul s).comp (measurable_inv.comp measurable_subtype_coe)
  set F : H → ℝ≥0∞ := fun k =>
    cfun Γ A y0 (s * (k : G)⁻¹) * ρ ((s * (k : G)⁻¹)⁻¹) with hF
  have hFm : Measurable F := by
    rw [hF]
    exact ((meas_cfun Γ y0 hA).comp hg).mul (hρ.comp hg.inv)
  have hinv : ∫⁻ k, F k⁻¹ ∂μ' = ∫⁻ k, F k ∂μ' := by
    exact (Measure.measurePreserving_inv μ').lintegral_comp hFm
  have h1 : ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k, F k ∂μ' := by
    rw [← hinv]
    refine lintegral_congr fun k => ?_
    simp only [hF, InvMemClass.coe_inv, inv_inv]
  have hmem : ∀ δ : (Γ ⊓ H).subgroupOf H, ((δ : H) : G) ∈ Γ := fun δ =>
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 δ.2)).1
  have hcoe : ∀ (δ : (Γ ⊓ H).subgroupOf H) (k : H),
      ((δ • k : H) : G) = ((δ : H) : G) * (k : G) := fun _ _ => rfl
  have hpt : ∀ k : H, ∑' δ : (Γ ⊓ H).subgroupOf H, F (δ • k) =
      cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) := by
    intro k
    have hδ : ∀ δ : (Γ ⊓ H).subgroupOf H, F (δ • k) =
        (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * (((δ : H) : G) * ((k : G) * s⁻¹)))) * ρ ((k : G) * s⁻¹) := by
      intro δ
      rw [← hρi _ (hmem δ) ((k : G) * s⁻¹)]
      simp only [hF, hcoe, cfun, mul_inv_rev, inv_inv, mul_assoc]
    have hrep := sum_rep_eq (Γ := Γ) y0 hH
      (fun g => A.indicator (fun _ => (1 : ℝ≥0∞)) (g * ((k : G) * s⁻¹)))
    simp only [mul_assoc] at hrep
    rw [tsum_congr hδ, ENNReal.tsum_mul_right, ENNReal.tsum_comm, hrep, cntN]
  calc ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ'
      = ∫⁻ k, F k ∂μ' := h1
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕', F (δ • k) ∂μ' :=
      h𝓕'.lintegral_eq_tsum'' F
    _ = ∫⁻ k in 𝓕', ∑' δ : (Γ ⊓ H).subgroupOf H, F (δ • k) ∂μ' :=
      (lintegral_tsum fun δ => (hFm.comp (measurable_const_smul δ)).aemeasurable).symm
    _ = ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' :=
      lintegral_congr hpt

end Abs2

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs3

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y] [MeasurableSpace Y]

theorem unfold_abs {Γ H : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (μ' : Measure H) [μ'.IsMulLeftInvariant] [μ'.IsInvInvariant]
    (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (ν : Measure Y) (Φ : Y → ℝ≥0∞) (hΦ : AEMeasurable Φ ν)
    (hΨ : Measurable fun g : G => Φ (g • y0))
    (hcov : ν {y | ¬ ∃ g : G, g • y0 = y} = 0)
    (hcomp : ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : Y → G,
      (∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ k, f (s y * (k : G)) ∂μ' ∂ν)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ') :
    ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ = μ' 𝓕' * ∫⁻ y, Φ y ∂ν := by
  classical

  haveI hcnt : Countable (orbS Γ y0) := by
    have hsub : orbS Γ y0 ⊆ Set.range (fun γ : Γ => (γ : G) • y0) := by
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := hx
      exact ⟨⟨γ, hγ⟩, rfl⟩
    exact ((Set.countable_range _).mono hsub).to_subtype
  have hr : ∀ x : orbS Γ y0, repO Γ y0 x • y0 = (x : Y) := fun x => by
    unfold repO
    exact (Classical.choose_spec x.2).2

  obtain ⟨F0, hF0sub, hF0m, hF0ae⟩ := h𝓕.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hc0m : Measurable (cntN Γ F0) := by
    unfold cntN
    exact Measurable.tsum fun γ =>
      (measurable_const.indicator hF0m).comp (measurable_const_mul (γ : G))
  have hcfm : Measurable (cfun Γ F0 y0) := by
    unfold cfun
    exact Measurable.tsum fun x =>
      (measurable_const.indicator hF0m).comp ((measurable_const_mul _).comp measurable_inv)
  have hc0i : ∀ γ ∈ Γ, ∀ g : G, cntN Γ F0 (γ * g) = cntN Γ F0 g := by
    intro γ hγ g
    unfold cntN
    refine Eq.trans ?_ ((Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq
      (fun δ : Γ => F0.indicator (fun _ => (1 : ℝ≥0∞)) ((δ : G) * g)))
    congr 1
    funext δ
    simp [mul_assoc]

  have hsub_ae : ∀ᵐ g ∂μ, ∀ γ : Γ, (γ : G) * g ∈ 𝓕 → (γ : G) * g ∈ F0 := by
    rw [ae_all_iff]
    intro γ
    have h1 : ∀ᵐ x ∂μ, x ∈ 𝓕 → x ∈ F0 := by
      filter_upwards [hF0ae.mem_iff] with x hx h
      exact hx.2 h
    exact (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h1
  have hcov0 : ∀ᵐ g ∂μ, ∃ γ : Γ, (γ : G) * g ∈ F0 := by
    filter_upwards [h𝓕.ae_covers, hsub_ae] with g hg hs
    obtain ⟨γ, hγ⟩ := hg
    exact ⟨γ, hs γ hγ⟩
  have hdis : ∀ᵐ g ∂μ, ∀ γ δ : Γ, γ ≠ δ → ¬ ((γ : G) * g ∈ 𝓕 ∧ (δ : G) * g ∈ 𝓕) := by
    rw [ae_all_iff]
    intro γ
    rw [ae_all_iff]
    intro δ
    by_cases hγδ : γ = δ
    · exact ae_of_all _ fun g h => absurd hγδ h
    · have h0 : μ ((γ⁻¹ • 𝓕) ∩ (δ⁻¹ • 𝓕)) = 0 := h𝓕.aedisjoint (fun h => hγδ (inv_injective h))
      rw [ae_iff]
      refine measure_mono_null ?_ h0
      intro g hg
      simp only [Set.mem_setOf_eq, Classical.not_imp, not_not] at hg
      obtain ⟨-, h1, h2⟩ := hg
      constructor
      · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact h1
      · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact h2
  have hc01 : ∀ᵐ g ∂μ, cntN Γ F0 g = 1 := by
    filter_upwards [hcov0, hdis] with g hg hd
    obtain ⟨γ, hγ⟩ := hg
    unfold cntN
    rw [tsum_eq_single γ]
    · simp [hγ]
    · intro δ hδ
      have hn : (δ : G) * g ∉ F0 := fun h => hd δ γ hδ ⟨hF0sub h, hF0sub hγ⟩
      simp [hn]
  have hc01i : ∀ᵐ g ∂μ, cntN Γ F0 g⁻¹ = 1 :=
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae hc01
  set Z : Set G := {g | cntN Γ F0 g ≠ 1} with hZ
  have hZm : MeasurableSet Z := hc0m (measurableSet_singleton 1).compl

  let s : Y → G := fun y => if h : ∃ g : G, g • y0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y := fun y h => by
    simp only [s, dif_pos h]
    exact h.choose_spec
  have hsk : ∀ y, (∃ g : G, g • y0 = y) → ∀ k : H, Φ ((s y * (k : G)) • y0) = Φ y := by
    intro y hy k
    rw [mul_smul, (hH k).1 k.2, hs y hy]
  have hsm : ∀ y, Measurable fun k : H => s y * (k : G) :=
    fun y => (measurable_const_mul _).comp measurable_subtype_coe
  have hyae : ∀ᵐ y ∂ν, ∃ g : G, g • y0 = y := ae_iff.2 hcov

  have hmx : ∀ x : orbS Γ y0, Measurable fun h : G => Φ (h⁻¹ • (x : Y)) := by
    intro x
    have e : (fun h : G => Φ (h⁻¹ • (x : Y))) =
        (fun g : G => Φ (g • y0)) ∘ (fun h => h⁻¹ * repO Γ y0 x) := by
      funext h
      simp [Function.comp, mul_smul, hr x]
    rw [e]
    exact hΨ.comp ((measurable_mul_const _).comp measurable_inv)
  have key : ∀ x : orbS Γ y0, ∫⁻ g, F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0) ∂μ =
      ∫⁻ h in F0, Φ (h⁻¹ • (x : Y)) ∂μ := by
    intro x
    refine (lintegral_inv_eq_self (μ := μ) _).symm.trans ?_
    refine (lintegral_mul_left_eq_self (μ := μ) _ (repO Γ y0 x)⁻¹).symm.trans ?_
    rw [← lintegral_indicator hF0m]
    refine lintegral_congr fun h => ?_
    have e2 : repO Γ y0 x * ((repO Γ y0 x)⁻¹ * h)⁻¹⁻¹ = h := by group
    have e3 : ((repO Γ y0 x)⁻¹ * h)⁻¹ • y0 = h⁻¹ • (x : Y) := by
      rw [mul_inv_rev, inv_inv, mul_smul, hr x]
    show F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * ((repO Γ y0 x)⁻¹ * h)⁻¹⁻¹) *
      Φ (((repO Γ y0 x)⁻¹ * h)⁻¹ • y0) = _
    rw [e2, e3]
    by_cases hh : h ∈ F0 <;> simp [hh]
  have hL : ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ =
      ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ := by
    rw [setLIntegral_congr hF0ae.symm, lintegral_tsum fun x => (hmx x).aemeasurable]
    have e1 : (fun g => cfun Γ F0 y0 g * Φ (g • y0)) = fun g =>
        ∑' x : orbS Γ y0, F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0) := by
      funext g
      unfold cfun
      rw [ENNReal.tsum_mul_right]
    rw [e1, lintegral_tsum (f := fun x g => F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) *
      Φ (g • y0)) fun x => (((measurable_const.indicator hF0m).comp
      ((measurable_const_mul _).comp measurable_inv)).mul hΨ).aemeasurable]
    exact tsum_congr fun x => (key x).symm
  rw [hL]
  apply le_antisymm
  ·
    have hρm : Measurable (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) :=
      measurable_const.indicator hZm.compl
    have hρi : ∀ γ ∈ Γ, ∀ g, (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (γ * g) =
        (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g := by
      intro γ hγ g
      simp only [Set.indicator, Set.mem_compl_iff, hZ, Set.mem_setOf_eq, hc0i γ hγ g]
    have eq1 : ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ = ∫⁻ g, cfun Γ F0 y0 g *
        (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹ * Φ (g • y0) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hc01i] with g hg
      have hgZ : g⁻¹ ∈ Zᶜ := by simp [hZ, hg]
      rw [Set.indicator_of_mem hgZ, mul_one]
    rw [eq1, hcomp (fun g => cfun Γ F0 y0 g * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹ * Φ (g • y0))
      ((hcfm.mul (hρm.comp measurable_inv)).mul hΨ) s hs,
      ← lintegral_const_mul'' _ hΦ]
    apply lintegral_mono_ae
    filter_upwards [hyae] with y hy
    have e4 : ∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ *
        Φ ((s y * (k : G)) • y0) ∂μ' = (∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) *
        (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ') * Φ y := by
      have hm1 : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) *
          (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ :=
        (hcfm.comp (hsm y)).mul ((hρm.comp measurable_inv).comp (hsm y))
      rw [← lintegral_mul_const _ hm1]
      exact lintegral_congr fun k => by rw [hsk y hy k]
    rw [e4, lint_fibre μ' y0 hH hF0m 𝓕' h𝓕' _ hρm hρi (s y)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) *
          (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ'
        ≤ ∫⁻ k in 𝓕', 1 ∂μ' := by
          refine lintegral_mono fun k => ?_
          by_cases hk : cntN Γ F0 ((k : G) * (s y)⁻¹) = 1
          · have hm : (k : G) * (s y)⁻¹ ∈ Zᶜ := by simp [hZ, hk]
            rw [Set.indicator_of_mem hm, hk, mul_one]
          · have hm : (k : G) * (s y)⁻¹ ∉ Zᶜ := by simp [hZ, hk]
            rw [Set.indicator_of_notMem hm, mul_zero]
            exact zero_le_one
      _ = μ' 𝓕' := by rw [setLIntegral_one]
  ·
    have hιm : Measurable (Z.indicator fun _ : G => (1 : ℝ≥0∞)) := measurable_const.indicator hZm
    have eq1 : ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ = ∫⁻ g, (cfun Γ F0 y0 g +
        ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹) * Φ (g • y0) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hc01i] with g hg
      have hgZ : g⁻¹ ∉ Z := by simp [hZ, hg]
      rw [Set.indicator_of_notMem hgZ, mul_zero, add_zero]
    have hfm : Measurable fun g => (cfun Γ F0 y0 g + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹) * Φ (g • y0) :=
      (hcfm.add (measurable_const.mul (hιm.comp measurable_inv))).mul hΨ
    rw [eq1, hcomp _ hfm s hs, ← lintegral_const_mul'' _ hΦ]
    apply lintegral_mono_ae
    filter_upwards [hyae] with y hy
    have hinm : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) +
        ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ :=
      (hcfm.comp (hsm y)).add (measurable_const.mul ((hιm.comp measurable_inv).comp (hsm y)))
    have e4 : ∫⁻ k, (cfun Γ F0 y0 (s y * (k : G)) + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹) *
        Φ ((s y * (k : G)) • y0) ∂μ' = (∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) +
        ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ') * Φ y := by
      rw [← lintegral_mul_const _ hinm]
      exact lintegral_congr fun k => by rw [hsk y hy k]
    rw [e4]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hfib := lint_fibre μ' y0 hH hF0m 𝓕' h𝓕' (fun _ => (1 : ℝ≥0∞)) measurable_const
      (fun _ _ _ => rfl) (s y)
    simp only [mul_one] at hfib
    have hinv : ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ' =
        ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
      refine Eq.trans ?_ (lintegral_inv_eq_self (μ := μ')
        (fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹)))
      refine lintegral_congr fun k => ?_
      simp [mul_inv_rev]
    have hbm : Measurable fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) :=
      hιm.comp ((measurable_mul_const _).comp measurable_subtype_coe)
    have hm2 : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) := hcfm.comp (hsm y)
    have hm3 : Measurable fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ :=
      (hιm.comp measurable_inv).comp (hsm y)
    have hm4 : Measurable fun k : H => cntN Γ F0 ((k : G) * (s y)⁻¹) :=
      hc0m.comp ((measurable_mul_const _).comp measurable_subtype_coe)
    rw [lintegral_add_left hm2, hfib, lintegral_const_mul _ hm3, hinv]
    calc μ' 𝓕' = ∫⁻ k in 𝓕', 1 ∂μ' := by rw [setLIntegral_one]
      _ ≤ ∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) +
          ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
          refine lintegral_mono fun k => ?_
          by_cases hk : (k : G) * (s y)⁻¹ ∈ Z
          · rw [Set.indicator_of_mem hk]
            simp
          · rw [Set.indicator_of_notMem hk, mul_zero, add_zero]
            have : cntN Γ F0 ((k : G) * (s y)⁻¹) = 1 := by simpa [hZ] using hk
            rw [this]
      _ = (∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) ∂μ') +
          ∞ * ∫⁻ k in 𝓕', (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
          rw [lintegral_add_left hm4, lintegral_const_mul _ hbm]
      _ ≤ (∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) ∂μ') +
          ∞ * ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
          gcongr
          first
          | exact Measure.restrict_le_self
          | exact setLIntegral_le_lintegral _ _
          | exact le_rfl

end Abs3

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

section Inst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem inclR_comp_sigma :
    (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).comp (σ : E →+* E) = (sigR (AF F) σ).comp (inclR (F := F) (AF F)) := by
  ext e
  simp [inclR, sigR]

def ratEl (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) : HFinIn (AF F) σ J :=
  ⟨⟨Formalism.UG.bc (inclR (F := F) (AF F)) g, Formalism.UG.P.bc_mem _ _ _ (inclR_comp_sigma σ) J g hg⟩,
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)⟩

def GamA : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

def ratElA (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) : HA (AF F) σ J :=
  (ratEl σ J g hg : HR (AF F) σ J)

theorem ratElA_mem (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    ratElA σ J g hg ∈ GamA σ J := (ratEl σ J g hg).2

theorem ratElA_smul (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) {a : ℕ}
    (X : Fin a → Fin M → E) :
    ratElA σ J g hg • ratTup (F := F) (AF F) X =
      ratTup (F := F) (AF F) (fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X i)) := by
  funext i j
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) (g : Matrix (Fin M) (Fin M) E) (X i) j).symm

instance nontrivAF : Nontrivial (AF F) := by
  haveI : Nontrivial (Ainf F) := by
    first
    | exact inferInstance
    | (haveI : Nonempty (NumberField.InfinitePlace F) := inferInstance; exact Pi.nontrivial)
  first
  | exact inferInstance
  | exact inferInstanceAs (Nontrivial (Ainf F × Af F))
  | exact (Prod.nontrivial_left : Nontrivial (Ainf F × Af F))

theorem ratTup_injective {a : ℕ} : Function.Injective (ratTup (F := F) (E := E) (M := M) (n := a) (AF F)) := by
  intro X X' h
  funext i j
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective
    (congrFun (congrFun h i) j)

end Inst

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem gram_orbit_equiv {a : ℕ} (X0 : Fin a → Fin M → E)
    (hW : ∀ X : Fin a → Fin M → E, gramE σ J X = gramE σ J X0 →
      ∃ g ∈ Formalism.UG.UJ (σ : E →+* E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i) = X i) :
    ∃ e : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} ≃
        orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
      ∀ X, (e X : Fin a → Fin M → AF F ⊗[F] E) = ratTup (F := F) (AF F) (X : Fin a → Fin M → E) := by
  let f : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} →
      orbS (GamA σ J) (ratTup (F := F) (AF F) X0) := fun X =>
    ⟨ratTup (F := F) (AF F) (X : Fin a → Fin M → E), by
      obtain ⟨g, hg, hgX⟩ := hW X X.2
      refine ⟨ratElA σ J g hg, ratElA_mem σ J g hg, ?_⟩
      rw [ratElA_smul]
      congr 1
      funext i
      exact hgX i⟩
  have hinj : Function.Injective f := fun X X' h =>
    Subtype.ext (ratTup_injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, ⟨γ, hγ, rfl⟩⟩
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.1
      (Subgroup.mem_subgroupOf.1 (show (show HR (AF F) σ J from γ) ∈ HFinIn (AF F) σ J from hγ))
    have hγe : γ = ratElA σ J g hg := Subtype.ext hgγ.symm
    have hg' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
        (g : Matrix (Fin M) (Fin M) E) = J := hg
    refine ⟨⟨fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i), ?_⟩, ?_⟩
    · show gramE σ J _ = gramE σ J X0
      ext i j
      show Formalism.UG.hform (σ : E →+* E) J _ _ = Formalism.UG.hform (σ : E →+* E) J _ _
      rw [Formalism.UG.P.hform_mulVec, hg']
    · apply Subtype.ext
      show ratTup (F := F) (AF F) _ = γ • ratTup (F := F) (AF F) X0
      rw [hγe, ratElA_smul]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun X => rfl⟩

end Main

section Of

theorem unfold_of (hW : Witt) (hFT : FinTheta) (hI : InvInv) (hMO : MeasOrb) (hMG : MeasGrp) :
    Unfold := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C
    𝓕' h𝓕' φ hφ0 hadm hθ
  haveI : MeasurableMul (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  haveI : MeasurableInv (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2
  haveI : μ.IsHaarMeasure := hμ
  haveI : μ'.IsHaarMeasure := hμ'H
  haveI : μ.IsInvInvariant := (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1 μ hμ
  haveI : μ'.IsInvInvariant :=
    (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2 ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  haveI : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  haveI hΓc : Countable (GamA σ J) := um_countable_HFinIn F E σ M J
  obtain ⟨e, he⟩ := gram_orbit_equiv σ J X0 (hW F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet)
  have hsub : orbS (GamA σ J) (ratTup (F := F) (AF F) X0) ⊆
      Set.range (fun γ : (GamA σ J) =>
        (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) X0) := by
    rintro x ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, e⟩
  haveI hcO : Countable (orbS (GamA σ J)
      (ratTup (F := F) (AF F) X0)) := ((Set.countable_range _).mono hsub).to_subtype
  have hmφ : Measurable fun g : HA (AF F) σ J => φ (g • ratTup (F := F) (AF F) X0) := by
    have := hMO F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet _ hadm
    have h2 := Complex.measurable_re.comp this
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have hint : Integrable (fun X => (φ X : ℂ)) νX := by
    obtain ⟨d, b, Φinf, Φf, Φv, h1, h2, h3, h4⟩ := id hadm
    obtain ⟨⟨μinf, hμinf⟩, k1⟩ := hν.2
    obtain ⟨⟨νinf, hνinf⟩, k2⟩ := k1 μinf hμinf
    obtain ⟨⟨μv, hμv⟩, k3⟩ := k2 νinf hνinf
    obtain ⟨⟨νv, hνv⟩, k4⟩ := k3 μv hμv
    obtain ⟨⟨fI, hfI⟩, k5⟩ := k4 νv hνv
    obtain ⟨⟨fV, hfV⟩, k6⟩ := k5 fI hfI
    exact (k6 fV hfV d b _ Φinf Φf Φv h1 h2 h3 h4).1
  have hφae : AEMeasurable φ νX := by
    have h2 := Complex.measurable_re.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have key : ∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ =
      μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX :=
    unfold_abs (Γ := GamA σ J) (H := stabT (AF F) σ J X0) μ μ' (ratTup (F := F) (AF F) X0) (fun k => MulAction.mem_stabilizer_iff) νX
      (fun X => ENNReal.ofReal (φ X)) hφae.ennreal_ofReal hmφ.ennreal_ofReal hμ'C.1 hμ'C.2 𝓕 h𝓕 𝓕' h𝓕'
  have hθS : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) =
      ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0},
        ENNReal.ofReal (φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin a → Fin M → E))) := by
    intro h
    rw [← e.tsum_eq (fun x => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))))]
    exact tsum_congr fun X => by rw [he X]
  have hfin : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ≠ ⊤ := by
    intro h
    have hF := hFT F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet (fun X => (φ X : ℂ)) hadm h
    rw [hθS h]
    refine ENNReal.tsum_coe_ne_top_iff_summable.2 (summable_of_hasFiniteSupport ?_)
    refine (hF.preimage Subtype.val_injective.injOn).subset ?_
    intro X hX
    simp only [Function.mem_support] at hX
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Ne, Complex.ofReal_eq_zero]
    intro hz
    apply hX
    change φ (h⁻¹ • ratTup (AF F) (X : Fin a → Fin M → E)) = 0 at hz
    simp [hz]
  have hθm : Measurable fun h : HA (AF F) σ J => ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) := by
    refine Measurable.tsum fun x => ?_
    have hx : (fun h : HA (AF F) σ J => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))) =
        fun h => ENNReal.ofReal (φ ((h⁻¹ * repO _ _ x) • ratTup (F := F) (AF F) X0)) := by
      funext h
      rw [mul_smul, repO_smul]
    rw [hx]
    exact (hmφ.comp (measurable_inv.mul_const _)).ennreal_ofReal
  have hθeq : ∀ h, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h =
      (((∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
        ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))).toReal : ℝ) : ℂ) := by
    intro h
    unfold thetaS
    rw [← Complex.ofReal_tsum, hθS h, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    congr 1
    exact tsum_congr fun X => (ENNReal.toReal_ofReal (hφ0 _)).symm
  have hI1 : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ =
      (((∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ).toReal
          : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hθeq), integral_complex_ofReal,
      integral_toReal hθm.aemeasurable (Filter.Eventually.of_forall fun h => (hfin h).lt_top)]
  have hI2 : ∫ X, (φ X : ℂ) ∂νX = (((∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
      hφae.aestronglyMeasurable]
  rw [hI1] at hθ ⊢
  rw [hI2, key]
  rw [key] at hθ
  have hL0 : (μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal ≠ 0 := fun h0 => hθ (by rw [h0]; simp)
  have hR0 : ∫⁻ X, ENNReal.ofReal (φ X) ∂νX ≠ 0 := fun h => hL0 (by simp [h])
  have hμ'top : μ' 𝓕' ≠ ⊤ := fun h => hL0 (by rw [h, ENNReal.top_mul hR0]; simp)
  refine ⟨hμ'top, ?_⟩
  rw [ENNReal.toReal_mul, Complex.ofReal_mul, Complex.real_smul]

end Of

end PI.VolStabS
