module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParsevalContinuousPeriodicAdelicRationalQuotient

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralMulConjEqOfLintegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetLIntegralAverageAbelianQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMulRightInvariantOfCovolumeOne
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace GlobalTheory.UnipAvg

theorem tsum_eq_tsum_quotient {A : Type*} [Group A] (S : Subgroup A) (f : A → ℝ≥0∞) :
    ∑' a, f a = ∑' q : A ⧸ S, ∑' s : S, f (q.out * s) := by
  have key : ∀ (q : A ⧸ S) (s : S), (QuotientGroup.mk (q.out * s) : A ⧸ S) = q := fun q s => by
    rw [QuotientGroup.mk_mul_of_mem _ s.2, QuotientGroup.out_eq']
  let e : (A ⧸ S) × S → A := fun p => p.1.out * p.2
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨q, s⟩ ⟨q', s'⟩ h
      simp only [e] at h
      have hq : q = q' := by rw [← key q s, ← key q' s', h]
      subst hq
      simp only [Prod.mk.injEq, true_and]
      exact Subtype.ext (mul_left_cancel h)
    · intro a
      refine ⟨(QuotientGroup.mk a, ⟨(QuotientGroup.mk a : A ⧸ S).out⁻¹ * a, ?_⟩), ?_⟩
      · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      · simp [e]
  rw [← (Equiv.ofBijective e he).tsum_eq]
  exact ENNReal.tsum_prod (f := fun (q : A ⧸ S) (s : S) => f (q.out * s))

section Unimodular

variable {U : Type*} [Group U] [MeasurableSpace U] [MeasurableMul₂ U] [MeasurableInv U]

theorem isMulRightInvariant_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1) :
    ν.IsMulRightInvariant := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  refine ⟨fun u => ?_⟩
  have hD' : IsFundamentalDomain U₀ ((· * u) ⁻¹' D) ν :=
    hD.preimage_of_equiv (quasiMeasurePreserving_mul_right ν u) (e := id) Function.bijective_id
      (fun g x => mul_assoc (g : U) x u)
  have h1 : (ν.map (· * u)) D = 1 := by
    have := (MeasurableEquiv.mulRight u).map_apply (μ := ν) D
    simp only [MeasurableEquiv.coe_mulRight] at this
    rw [this, hD'.measure_eq hD, hνD]
  haveI : SigmaFinite (ν.map (· * u)) := (MeasurableEquiv.mulRight u).sigmaFinite_map
  have h := measure_eq_div_smul (ν.map (· * u)) ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  rw [h, h1, hνD]; simp

theorem isInvInvariant_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1) :
    ν.IsInvInvariant := by
  haveI := isMulRightInvariant_of_covolume_one ν U₀ hD hνD
  have h := measure_eq_div_smul ν.inv ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  rw [hνD, div_one] at h
  set c := ν.inv D with hc
  have h2 : ν = (c * c) • ν := by
    calc ν = ν.inv.inv := (Measure.inv_inv ν).symm
      _ = (c • ν).inv := by rw [← h]
      _ = c • ν.inv := Measure.map_smul c measurable_inv.aemeasurable
      _ = (c * c) • ν := by rw [h, smul_smul]
  have h3 : c * c = 1 := by
    have := congrArg (fun m : Measure U => m D) h2
    simpa [hνD] using this.symm
  have h4 : c = 1 := by
    rcases lt_trichotomy c 1 with hlt | heq | hgt
    · have : c * c < 1 := lt_of_le_of_lt (by simpa using mul_le_mul_right hlt.le c) hlt
      exact absurd h3 this.ne
    · exact heq
    · have : 1 < c * c := lt_of_lt_of_le hgt (by simpa using mul_le_mul_right hgt.le c)
      exact absurd h3 this.ne'
  exact ⟨by rw [h, h4, one_smul]⟩


omit [MeasurableInv U] in
theorem tsum_setLIntegral_eq_index (ν : Measure U) [ν.IsMulLeftInvariant]
    (U₀ L : Subgroup U) [Countable U₀] (hle : U₀ ≤ L) {D : Set U} (hD : IsFundamentalDomain U₀ D ν)
    (ψ : U → ℝ≥0∞) :
    ∑' l : L, ∫⁻ u in D, ψ (l * u) ∂ν = ∑' _q : L ⧸ U₀.subgroupOf L, ∫⁻ u, ψ u ∂ν := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  rw [tsum_eq_tsum_quotient (U₀.subgroupOf L)]
  refine tsum_congr fun q => ?_
  rw [← lintegral_mul_left_eq_self ψ ((q.out : L) : U), hD.lintegral_eq_tsum'',
    ← (Subgroup.subgroupOfEquivOfLe hle).toEquiv.tsum_eq]
  refine tsum_congr fun b => lintegral_congr fun u => ?_
  congr 1
  exact mul_assoc _ _ _

end Unimodular

section Average

variable {G U : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [Group U] [MeasurableSpace U] [MeasurableMul₂ U] [MeasurableInv U]


omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableInv U] in
theorem tsum_setLIntegral_eq_cosets (ι : U →* G) (hι : Function.Injective ι) (ν : Measure U) [ν.IsMulLeftInvariant]
    (Γ : Subgroup G) (U₀ : Subgroup U) [Countable U₀] (hle : U₀ ≤ Γ.comap ι) {D : Set U}
    (hD : IsFundamentalDomain U₀ D ν) (φ : G → ℝ≥0∞) :
    ∑' γ : Γ, ∫⁻ u in D, φ (γ * ι u) ∂ν =
      ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∑' _k : Γ.comap ι ⧸ U₀.subgroupOf (Γ.comap ι),
        ∫⁻ u, φ ((q.out : Γ) * ι u) ∂ν := by
  rw [tsum_eq_tsum_quotient (ι.range.subgroupOf Γ)]
  refine tsum_congr fun q => ?_
  rw [← tsum_setLIntegral_eq_index ν U₀ _ hle hD (fun u => φ ((q.out : Γ) * ι u))]
  let e : Γ.comap ι → ι.range.subgroupOf Γ := fun l => ⟨⟨ι l, l.2⟩, ⟨l, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro l l' h
      exact Subtype.ext (hι (congrArg (fun s : ι.range.subgroupOf Γ => ((s : Γ) : G)) h))
    · rintro ⟨⟨γ, hγ⟩, ⟨l, hl⟩⟩
      have hl' : ι l = γ := hl
      subst hl'
      exact ⟨⟨l, hγ⟩, rfl⟩
  rw [← (Equiv.ofBijective e he).tsum_eq]
  refine tsum_congr fun l => lintegral_congr fun u => ?_
  simp [e, mul_assoc]

theorem tsum_setLIntegral_inv (ι : U →* G) (hι : Function.Injective ι) (hιm : Measurable ι) (ν : Measure U)
    [ν.IsMulLeftInvariant] [ν.IsInvInvariant]
    (Γ : Subgroup G) (U₀ : Subgroup U) [Countable U₀] (hle : U₀ ≤ Γ.comap ι) {D : Set U}
    (hD : IsFundamentalDomain U₀ D ν)
    (hconj : ∀ γ ∈ Γ, ∃ c : U → U, MeasurePreserving c ν ν ∧ ∀ u, ι (c u) = γ⁻¹ * ι u * γ)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) :
    ∑' γ : Γ, ∫⁻ u in D, φ ((ι u)⁻¹ * γ) ∂ν = ∑' γ : Γ, ∫⁻ u in D, φ (γ * ι u) ∂ν := by
  haveI : (ι.range.subgroupOf Γ).Normal := ⟨by
    rintro ⟨n, hn⟩ ⟨u, hu⟩ g
    obtain ⟨c, -, hc⟩ := hconj (g : G)⁻¹ (Γ.inv_mem g.2)
    have hu' : ι u = n := hu
    exact ⟨c u, by rw [hc, hu']; simp⟩⟩
  have h1 : ∑' γ : Γ, ∫⁻ u in D, φ ((ι u)⁻¹ * γ) ∂ν = ∑' γ : Γ, ∫⁻ u in D, (fun x => φ x⁻¹) (γ * ι u) ∂ν := by
    rw [← (Equiv.inv Γ).tsum_eq]
    simp
  rw [h1, tsum_setLIntegral_eq_cosets ι hι ν Γ U₀ hle hD (fun x => φ x⁻¹),
    tsum_setLIntegral_eq_cosets ι hι ν Γ U₀ hle hD,
    ← (Equiv.inv (Γ ⧸ ι.range.subgroupOf Γ)).tsum_eq]
  refine tsum_congr fun q => tsum_congr fun _ => ?_
  set t : Γ := (Equiv.inv (Γ ⧸ ι.range.subgroupOf Γ) q).out with ht
  have hmem : t * q.out ∈ ι.range.subgroupOf Γ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ht]
    simp
  obtain ⟨v, hv⟩ := hmem
  have hv' : ι v = (t : G) * (q.out : Γ) := hv
  obtain ⟨c, hcm, hc⟩ := hconj (t : G)⁻¹ (Γ.inv_mem t.2)
  calc ∫⁻ u, φ ((t : G) * ι u)⁻¹ ∂ν = ∫⁻ u, φ (ι u * (t : G)⁻¹) ∂ν := by
        rw [← lintegral_inv_eq_self (μ := ν) (fun u => φ (ι u * (t : G)⁻¹))]
        simp
    _ = ∫⁻ u, φ ((t : G)⁻¹ * ι (c u)) ∂ν := by
        refine lintegral_congr fun u => ?_
        rw [hc]; congr 1; group
    _ = ∫⁻ u, φ ((t : G)⁻¹ * ι u) ∂ν :=
        hcm.lintegral_comp (f := fun u => φ ((t : G)⁻¹ * ι u)) (hφ.comp (hιm.const_mul _))
    _ = ∫⁻ u, φ ((t : G)⁻¹ * ι (v * u)) ∂ν :=
        (lintegral_mul_left_eq_self (fun u => φ ((t : G)⁻¹ * ι u)) v).symm
    _ = _ := by
        refine lintegral_congr fun u => ?_
        rw [map_mul, hv']; congr 1; group


omit [MeasurableInv G] in
theorem lintegral_mul_tsum_weight (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {β : G → ℝ≥0∞} (hβm : Measurable β)
    (hβ : ∀ f : G → ℝ≥0∞, ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g, β g * f g ∂μ) (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (w : G) :
    ∫⁻ g, ρ g * ∑' γ : Γ, β (γ * w * g) ∂μ = ∫⁻ g, ρ g ∂μ := by
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (f := fun (γ : Γ) g => ρ g * β (γ * w * g))
      fun γ => (hρ.mul (hβm.comp (measurable_const_mul _))).aemeasurable,
    ← lintegral_mul_left_eq_self ρ w⁻¹, h𝓕.lintegral_eq_tsum']
  refine tsum_congr fun γ => ?_
  rw [hβ, ← lintegral_mul_left_eq_self _ ((γ : G) * w)⁻¹]
  refine lintegral_congr fun g => ?_
  rw [mul_comm, mul_inv_cancel_left]
  congr 2
  change _ = w⁻¹ * (((γ⁻¹ : Γ) : G) * g)
  simp [mul_assoc]

theorem setLIntegral_average (ι : U →* G) (hι : Function.Injective ι) (hιm : Measurable ι)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] (U₀ : Subgroup U) (hle : ∀ b ∈ U₀, ι b ∈ Γ) (Γ₁ : Set G)
    (hcov : ∀ γ ∈ Γ, ∃ a ∈ Γ₁, ∃ b ∈ U₀, γ = a * ι b)
    (hconj : ∀ a ∈ Γ₁, ∃ c : U → U, MeasurePreserving c ν ν ∧ ∀ u, ι (c u) = a⁻¹ * ι u * a)
    {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (F : G → ℝ≥0∞) (hF : Measurable F) (hinv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) :
    ∫⁻ g in 𝓕, F g ∂μ = ∫⁻ g in 𝓕, ∫⁻ u in D, F (ι u * g) ∂ν ∂μ := by
  haveI : Countable U₀ := (show Function.Injective (fun b : U₀ => (⟨ι b, hle b b.2⟩ : Γ)) from
    fun b b' h => Subtype.ext (hι (congrArg Subtype.val h))).countable
  haveI := isMulRightInvariant_of_covolume_one ν U₀ hD hνD
  haveI := isInvInvariant_of_covolume_one ν U₀ hD hνD
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hconj' : ∀ γ ∈ Γ, ∃ c : U → U, MeasurePreserving c ν ν ∧ ∀ u, ι (c u) = γ⁻¹ * ι u * γ := by
    intro γ hγ
    obtain ⟨a, ha, b, -, rfl⟩ := hcov γ hγ
    obtain ⟨c, hcm, hc⟩ := hconj a ha
    refine ⟨fun u => b⁻¹ * c u * b,
      (measurePreserving_mul_right ν b).comp ((measurePreserving_mul_left ν b⁻¹).comp hcm), fun u => ?_⟩
    simp only [map_mul, map_inv, hc]; group
  obtain ⟨β, hβm, hβ⟩ : ∃ β : G → ℝ≥0∞, Measurable β ∧
      ∀ f : G → ℝ≥0∞, ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g, β g * f g ∂μ := by
    refine ⟨(toMeasurable μ 𝓕).indicator 1, measurable_one.indicator (measurableSet_toMeasurable μ 𝓕), fun f => ?_⟩
    rw [← restrict_congr_set h𝓕.nullMeasurableSet.toMeasurable_ae_eq,
      ← lintegral_indicator (measurableSet_toMeasurable μ 𝓕)]
    refine lintegral_congr fun g => ?_
    by_cases hg : g ∈ toMeasurable μ 𝓕 <;> simp [hg]
  have hA : ∀ w : G, ∫⁻ g in 𝓕, F (w * g) ∂μ = ∫⁻ g in 𝓕, F g * ∑' γ : Γ, β (w⁻¹ * γ * g) ∂μ := by
    intro w
    simp_rw [← ENNReal.tsum_mul_left]
    rw [lintegral_tsum (f := fun (γ : Γ) g => F g * β (w⁻¹ * γ * g))
      fun γ => (hF.mul (hβm.comp (measurable_const_mul _))).aemeasurable, hβ,
      ← lintegral_mul_left_eq_self _ w⁻¹, h𝓕.lintegral_eq_tsum'']
    refine tsum_congr fun γ => lintegral_congr fun g => ?_
    change β (w⁻¹ * (γ * g)) * F (w * (w⁻¹ * (γ * g))) = _
    rw [mul_inv_cancel_left, hinv _ γ.2, mul_comm, mul_assoc]
  have hm1 : Measurable fun p : G × U => ∑' γ : Γ, β ((ι p.2)⁻¹ * γ * p.1) :=
    Measurable.tsum fun γ => hβm.comp (((hιm.comp measurable_snd).inv.mul_const _).mul measurable_fst)
  have hm2 : Measurable fun p : G × U => ∑' γ : Γ, β (γ * ι p.2 * p.1) :=
    Measurable.tsum fun γ => hβm.comp (((hιm.comp measurable_snd).const_mul _).mul measurable_fst)
  symm
  calc ∫⁻ g in 𝓕, ∫⁻ u in D, F (ι u * g) ∂ν ∂μ = ∫⁻ u in D, ∫⁻ g in 𝓕, F (ι u * g) ∂μ ∂ν :=
        lintegral_lintegral_swap (hF.comp ((hιm.comp measurable_snd).mul measurable_fst)).aemeasurable
    _ = ∫⁻ u in D, ∫⁻ g in 𝓕, F g * ∑' γ : Γ, β ((ι u)⁻¹ * γ * g) ∂μ ∂ν := lintegral_congr fun u => hA _
    _ = ∫⁻ g in 𝓕, ∫⁻ u in D, F g * ∑' γ : Γ, β ((ι u)⁻¹ * γ * g) ∂ν ∂μ :=
        (lintegral_lintegral_swap ((hF.comp measurable_fst).mul hm1).aemeasurable).symm
    _ = ∫⁻ g in 𝓕, ∫⁻ u in D, F g * ∑' γ : Γ, β (γ * ι u * g) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        have hleft : ∀ γ : Γ, Measurable (fun u : U => β ((ι u)⁻¹ * γ * g)) := fun γ =>
          hβm.comp ((hιm.inv.mul_const (γ : G)).mul_const g)
        have hright : ∀ γ : Γ, Measurable (fun u : U => β (γ * ι u * g)) := fun γ =>
          hβm.comp ((hιm.const_mul (γ : G)).mul_const g)
        rw [lintegral_const_mul (F g) (Measurable.tsum hleft),
          lintegral_const_mul (F g) (Measurable.tsum hright),
          lintegral_tsum (f := fun (γ : Γ) u => β ((ι u)⁻¹ * γ * g))
            fun γ => (hleft γ).aemeasurable,
          lintegral_tsum (f := fun (γ : Γ) u => β (γ * ι u * g))
            fun γ => (hright γ).aemeasurable,
          tsum_setLIntegral_inv ι hι hιm ν Γ U₀ hle hD hconj' (fun x => β (x * g))
            (hβm.comp (measurable_mul_const g))]
    _ = ∫⁻ u in D, ∫⁻ g in 𝓕, F g * ∑' γ : Γ, β (γ * ι u * g) ∂μ ∂ν :=
        lintegral_lintegral_swap ((hF.comp measurable_fst).mul hm2).aemeasurable
    _ = ∫⁻ _u in D, ∫⁻ g in 𝓕, F g ∂μ ∂ν := by
        refine lintegral_congr fun u => ?_
        rw [hβ, hβ F, ← lintegral_mul_tsum_weight μ Γ h𝓕 hβm hβ (fun g => β g * F g) (hβm.mul hF) (ι u)]
        simp_rw [mul_assoc]
    _ = ∫⁻ g in 𝓕, F g ∂μ := by simp [hνD]

end Average

section Additive

variable {G A : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A]

end Additive

end GlobalTheory.UnipAvg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetLIntegralAverageAbelianQuotient
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace GlobalTheory.UnipAvg

section Covolume

variable {U : Type*} [Group U] [MeasurableSpace U] [MeasurableMul₂ U] [MeasurableInv U]

theorem measurePreserving_mulEquiv_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    (c : U ≃* U) (hc : Measurable c) (hc' : Measurable c.symm)
    (h₁ : ∀ b ∈ U₀, c b ∈ U₀) (h₂ : ∀ b ∈ U₀, c.symm b ∈ U₀) : MeasurePreserving c ν ν := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  let e : U ≃ᵐ U := ⟨c.toEquiv, hc, hc'⟩
  haveI : SigmaFinite (ν.map c) := e.sigmaFinite_map
  haveI : (ν.map c).IsMulLeftInvariant := ⟨fun g => by
    rw [map_map (measurable_const_mul g) hc]
    conv_rhs => rw [← map_mul_left_eq_self ν (c.symm g), map_map hc (measurable_const_mul _)]
    congr 1
    ext x
    simp⟩
  have h := measure_eq_div_smul (ν.map c) ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  have hq : QuasiMeasurePreserving c ν ν := ⟨hc.aemeasurable, by rw [h]; exact smul_absolutelyContinuous⟩
  have hD' : IsFundamentalDomain U₀ (c ⁻¹' D) ν :=
    hD.preimage_of_equiv hq (e := fun b : U₀ => (⟨c.symm b, h₂ b b.2⟩ : U₀))
      ⟨fun b b' hb => Subtype.ext (c.symm.injective (congrArg Subtype.val hb)),
        fun b => ⟨⟨c b, h₁ b b.2⟩, Subtype.ext (c.symm_apply_apply b)⟩⟩
      (fun b x => by
        change c (c.symm b * x) = b * c x
        simp)
  have h1 : (ν.map c) D = 1 := by
    have : (ν.map c) D = ν (c ⁻¹' D) := e.map_apply (μ := ν) D
    rw [this, hD'.measure_eq hD, hνD]
  refine ⟨hc, ?_⟩
  rw [h, h1, hνD]; simp

theorem setLIntegral_mul_right_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    (f : U → ℝ≥0∞) (hf : ∀ b ∈ U₀, ∀ u, f (b * u) = f u) (v : U) :
    ∫⁻ u in D, f (u * v) ∂ν = ∫⁻ u in D, f u ∂ν := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  haveI := isMulRightInvariant_of_covolume_one ν U₀ hD hνD
  have hD' : IsFundamentalDomain U₀ ((· * v) ⁻¹' D) ν :=
    hD.preimage_of_equiv (quasiMeasurePreserving_mul_right ν v) (e := id) Function.bijective_id
      (fun g x => mul_assoc (g : U) x v)
  rw [hD.setLIntegral_eq hD' (fun u => f (u * v)) (fun b x => by
    change f ((b : U) * x * v) = _
    rw [mul_assoc, hf _ b.2])]
  exact (measurePreserving_mul_right ν v).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.mulRight v).measurableEmbedding f D

end Covolume

theorem setLIntegral_add_left_of_periodic {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    (ν : Measure A) [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀] {D : Set A}
    (hD : IsAddFundamentalDomain A₀ D ν) (f : A → ℝ≥0∞) (hf : ∀ b ∈ A₀, ∀ y, f (b + y) = f y) (t : A) :
    ∫⁻ y in D, f (t + y) ∂ν = ∫⁻ y in D, f y ∂ν := by
  haveI : VAddInvariantMeasure A₀ A ν := ⟨fun γ s _ => measure_preimage_add ν (γ : A) s⟩
  have hD' : IsAddFundamentalDomain A₀ ((t + ·) ⁻¹' D) ν :=
    hD.preimage_of_equiv (measurePreserving_add_left ν t).quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => add_left_comm t (g : A) x)
  rw [hD.setLIntegral_eq hD' (fun u => f (t + u)) (fun b x => by
    change f (t + ((b : A) + x)) = _
    rw [add_left_comm, hf _ b.2])]
  exact (measurePreserving_add_left ν t).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft t).measurableEmbedding f D

theorem exists_covolume_one_of_cocompact {U : Type*} [Group U] [TopologicalSpace U] [IsTopologicalGroup U]
    [LocallyCompactSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (U₀ : Subgroup U) [DiscreteTopology U₀] {K : Set U} (hK : IsCompact K) (hcov : ∀ u, ∃ b ∈ U₀, b * u ∈ K) :
    ∃ (ν : Measure U) (D : Set U), SigmaFinite ν ∧ ν.IsMulLeftInvariant ∧ IsFundamentalDomain U₀ D ν ∧ ν D = 1 := by
  haveI := countable_of_discrete_subgroup U₀
  obtain ⟨D, -, -, hD⟩ := exists_isFundamentalDomain_subgroup U₀
  let m : Measure U := haar
  haveI : SMulInvariantMeasure U₀ U m := ⟨fun γ s _ => measure_preimage_mul m (γ : U) s⟩
  have h0 : m D ≠ 0 := (hD m).measure_ne_zero (NeZero.ne m)
  have h1 : m D ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := m)))
    rw [(hD m).measure_eq_tsum K]
    refine le_trans (measure_mono fun u hu => ?_) (measure_iUnion_le _)
    obtain ⟨b, hb, hbu⟩ := hcov u
    exact mem_iUnion.2 ⟨(⟨b, hb⟩ : U₀)⁻¹, mem_inv_smul_set_iff.2 hbu, hu⟩
  haveI : ((m D)⁻¹ • m).IsHaarMeasure := IsHaarMeasure.smul m (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0)
  exact ⟨(m D)⁻¹ • m, D, inferInstance, inferInstance, hD _, by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]⟩

theorem setLIntegral_average_abelian_quotient : ∀ (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (Γ U : Subgroup G) [DiscreteTopology Γ], IsClosed (U : Set G) → (∀ γ ∈ Γ, ∀ u ∈ U, γ⁻¹ * u * γ ∈ U) → (∃ K : Set G, IsCompact K ∧ ∀ u ∈ U, ∃ γ ∈ Γ, γ ∈ U ∧ γ * u ∈ K) → ∀ (ι : A → G), (∀ x y, ι (x + y) = ι x * ι y) → Measurable ι → (∀ x, ι x ∈ U) → ∀ (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀], (∀ b ∈ A₀, ι b ∈ Γ) → ∀ (D : Set A), IsAddFundamentalDomain A₀ D ν → ν D = 1 → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (Φ : G → ENNReal), Measurable Φ → (∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) → (∀ u ∈ U, ∃ y : A, ∀ g, Φ (u * g) = Φ (ι y * g)) → ∫⁻ g in 𝓕, Φ g ∂μ = ∫⁻ g in 𝓕, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂μ := by
  intro G A _ _ _ _ _ _ _ _ _ _ _ _ μ _ _ Γ U _ hU hnorm ⟨K, hK, hcov⟩ ι hadd hιm hιU ν _ _ A₀ _ hA₀ D hD hνD 𝓕 h𝓕
    Φ hΦ hinv hact
  haveI := countable_of_discrete_subgroup Γ
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : DiscreteTopology (Γ.subgroupOf U) :=
    DiscreteTopology.of_continuous_injective (f := fun b : Γ.subgroupOf U => (⟨(b : U), b.2⟩ : Γ))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun b b' h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h)))
  haveI := countable_of_discrete_subgroup (Γ.subgroupOf U)
  obtain ⟨m, E, _, _, hE, hmE⟩ := exists_covolume_one_of_cocompact (Γ.subgroupOf U)
    (hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK) (fun u => by
      obtain ⟨γ, h1, h2, h3⟩ := hcov u u.2
      exact ⟨⟨γ, h2⟩, h1, h3⟩)
  have hconj : ∀ a ∈ (Γ : Set G), ∃ c : U → U, MeasurePreserving c m m ∧
      ∀ u, U.subtype (c u) = a⁻¹ * U.subtype u * a := by
    intro a ha
    have ha' : ∀ u ∈ U, a * u * a⁻¹ ∈ U := fun u hu => by simpa using hnorm a⁻¹ (Γ.inv_mem ha) u hu
    let c : U ≃* U :=
      { toFun := fun u => ⟨a⁻¹ * u * a, hnorm a ha u u.2⟩
        invFun := fun u => ⟨a * u * a⁻¹, ha' u u.2⟩
        left_inv := fun u => Subtype.ext (by simp only; group)
        right_inv := fun u => Subtype.ext (by simp only; group)
        map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    exact ⟨c, measurePreserving_mulEquiv_of_covolume_one m _ hE hmE c
      (((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk)
      (((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk)
      (fun b hb => Γ.mul_mem (Γ.mul_mem (Γ.inv_mem ha) hb) ha)
      (fun b hb => Γ.mul_mem (Γ.mul_mem ha hb) (Γ.inv_mem ha)), fun _ => rfl⟩
  rw [setLIntegral_average U.subtype Subtype.val_injective measurable_subtype_coe μ m Γ (Γ.subgroupOf U)
    (fun b hb => hb) Γ (fun γ hγ => ⟨γ, hγ, 1, one_mem _, by simp⟩) hconj hE hmE h𝓕 Φ hΦ hinv]
  refine lintegral_congr fun g => ?_
  calc ∫⁻ u in E, Φ (U.subtype u * g) ∂m = ∫⁻ _y in D, ∫⁻ u in E, Φ ((u : G) * g) ∂m ∂ν := by simp [hνD]
    _ = ∫⁻ y in D, ∫⁻ u in E, Φ ((u : G) * (ι y * g)) ∂m ∂ν := by
        refine lintegral_congr fun y => ?_
        rw [← setLIntegral_mul_right_of_covolume_one m _ hE hmE (fun u => Φ ((u : G) * g))
          (fun b hb u => by rw [Subgroup.coe_mul, mul_assoc, hinv (b : G) hb]) ⟨ι y, hιU y⟩]
        simp only [Subgroup.coe_mul, mul_assoc]
    _ = ∫⁻ u in E, ∫⁻ y in D, Φ ((u : G) * (ι y * g)) ∂ν ∂m :=
        lintegral_lintegral_swap (hΦ.comp ((measurable_subtype_coe.comp measurable_snd).mul
          ((hιm.comp measurable_fst).mul_const g))).aemeasurable
    _ = ∫⁻ _u in E, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂m := by
        refine lintegral_congr fun u => ?_
        obtain ⟨t, ht⟩ := hact u u.2
        rw [← setLIntegral_add_left_of_periodic ν A₀ hD (fun y => Φ (ι y * g))
          (fun b hb y => by rw [hadd, mul_assoc, hinv _ (hA₀ b hb)]) t]
        simp only [ht, hadd, mul_assoc]
    _ = ∫⁻ y in D, Φ (ι y * g) ∂ν := by simp [hmE]

end GlobalTheory.UnipAvg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetLIntegralAverageAbelianQuotientStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setLIntegral_average_abelian_quotient_alt : ∀ (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (Γ U : Subgroup G) [DiscreteTopology Γ], IsClosed (U : Set G) → (∀ γ ∈ Γ, ∀ u ∈ U, γ⁻¹ * u * γ ∈ U) → (∃ K : Set G, IsCompact K ∧ ∀ u ∈ U, ∃ γ ∈ Γ, γ ∈ U ∧ γ * u ∈ K) → ∀ (ι : A → G), (∀ x y, ι (x + y) = ι x * ι y) → Measurable ι → (∀ x, ι x ∈ U) → ∀ (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀], (∀ b ∈ A₀, ι b ∈ Γ) → ∀ (D : Set A), IsAddFundamentalDomain A₀ D ν → ν D = 1 → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (Φ : G → ENNReal), Measurable Φ → (∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) → (∀ u ∈ U, ∃ y : A, ∀ g, Φ (u * g) = Φ (ι y * g)) → ∫⁻ g in 𝓕, Φ g ∂μ = ∫⁻ g in 𝓕, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂μ := by
  first | exact @GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient | exact GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient | (intros; apply GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient <;> assumption)
end
end

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.MirTower

section Polar

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem memLp_two_of_lintegral {μ : Measure X} {f : X → ℂ} (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤) : MemLp f 2 μ := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hf]
  simpa using h.lt_top

theorem integral_mul_conj_eq {μ : Measure X} {f f' : X → ℂ} (hf : MemLp f 2 μ) (hf' : MemLp f' 2 μ) :
    Integrable (fun x => f x * conj (f' x)) μ ∧ ∫ x, f x * conj (f' x) ∂μ =
      (((∫⁻ x, ‖f x + 1 * f' x‖ₑ ^ 2 ∂μ).toReal : ℂ) - (∫⁻ x, ‖f x + (-1) * f' x‖ₑ ^ 2 ∂μ).toReal +
        Complex.I * ((∫⁻ x, ‖f x + Complex.I * f' x‖ₑ ^ 2 ∂μ).toReal -
          (∫⁻ x, ‖f x + (-Complex.I) * f' x‖ₑ ^ 2 ∂μ).toReal)) / 4 := by
  have hm : ∀ c : ℂ, MemLp (fun x => f x + c * f' x) 2 μ := fun c => hf.add (hf'.const_mul c)
  have hi : ∀ c : ℂ, Integrable (fun x => ((‖f x + c * f' x‖ ^ 2 : ℝ) : ℂ)) μ := fun c =>
    ((memLp_two_iff_integrable_sq_norm (hm c).aestronglyMeasurable).1 (hm c)).ofReal
  have he : ∀ c : ℂ, ((∫⁻ x, ‖f x + c * f' x‖ₑ ^ 2 ∂μ).toReal : ℂ) = ∫ x, ((‖f x + c * f' x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
    intro c
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x + c * f' x‖ ^ 2)
      (Filter.Eventually.of_forall fun w => by positivity) ((hm c).aestronglyMeasurable.norm.pow 2)]
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hp : (fun x => f x * conj (f' x)) = fun x =>
      (((‖f x + 1 * f' x‖ ^ 2 : ℝ) : ℂ) - (‖f x + (-1) * f' x‖ ^ 2 : ℝ) +
        Complex.I * ((‖f x + Complex.I * f' x‖ ^ 2 : ℝ) - (‖f x + (-Complex.I) * f' x‖ ^ 2 : ℝ))) / 4 := by
    funext x
    simp only [Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp <;> ring
  rw [hp]
  refine ⟨(((hi 1).sub (hi (-1))).add (((hi _).sub (hi _)).const_mul _)).div_const _, ?_⟩
  rw [integral_div, integral_add, integral_const_mul, integral_sub (hi _) (hi _), integral_sub (hi _) (hi _)]
  · simp only [he]
  · exact (hi 1).sub (hi (-1))
  · exact ((hi _).sub (hi _)).const_mul _

theorem integral_mul_conj_eq_of_lintegral {μ : Measure X} {ν : Measure Y} {f f' : X → ℂ} {h h' : Y → ℂ}
    (hf : Measurable f) (hf' : Measurable f') (hh : Measurable h) (hh' : Measurable h')
    {v : X → ℝ≥0} {w : Y → ℝ≥0} (hv : Measurable v) (hw : Measurable w)
    (H : ∀ c d : ℂ, ∫⁻ x, ‖c * f x + d * f' x‖ₑ ^ 2 * v x ∂μ = ∫⁻ y, ‖c * h y + d * h' y‖ₑ ^ 2 * w y ∂ν)
    (h1 : ∫⁻ x, ‖f x‖ₑ ^ 2 * v x ∂μ ≠ ⊤) (h2 : ∫⁻ x, ‖f' x‖ₑ ^ 2 * v x ∂μ ≠ ⊤) :
    Integrable (fun x => f x * conj (f' x) * (v x : ℝ)) μ ∧ Integrable (fun y => h y * conj (h' y) * (w y : ℝ)) ν ∧
      ∫ x, f x * conj (f' x) * (v x : ℝ) ∂μ = ∫ y, h y * conj (h' y) * (w y : ℝ) ∂ν := by
  have e1 : ∀ φ : X → ℂ, Measurable φ →
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂(μ.withDensity fun x => v x) = ∫⁻ x, ‖φ x‖ₑ ^ 2 * v x ∂μ := fun φ hφ => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hv.coe_nnreal_ennreal (hφ.enorm.pow_const 2)]
    simp only [Pi.mul_apply, mul_comm]
  have e2 : ∀ φ : Y → ℂ, Measurable φ →
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂(ν.withDensity fun x => w x) = ∫⁻ x, ‖φ x‖ₑ ^ 2 * w x ∂ν := fun φ hφ => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hw.coe_nnreal_ennreal (hφ.enorm.pow_const 2)]
    simp only [Pi.mul_apply, mul_comm]
  have H1 := H 1 0
  have H2 := H 0 1
  simp only [one_mul, zero_mul, add_zero, zero_add] at H1 H2
  obtain ⟨a1, a2⟩ := integral_mul_conj_eq (μ := μ.withDensity fun x => v x)
    (memLp_two_of_lintegral hf.aestronglyMeasurable (by rwa [e1 f hf]))
    (memLp_two_of_lintegral hf'.aestronglyMeasurable (by rwa [e1 f' hf']))
  obtain ⟨b1, b2⟩ := integral_mul_conj_eq (μ := ν.withDensity fun x => w x)
    (memLp_two_of_lintegral hh.aestronglyMeasurable (by rwa [e2 h hh, ← H1]))
    (memLp_two_of_lintegral hh'.aestronglyMeasurable (by rwa [e2 h' hh', ← H2]))
  have H3 : ∀ d : ℂ, ∫⁻ x, ‖f x + d * f' x‖ₑ ^ 2 ∂(μ.withDensity fun x => v x) =
      ∫⁻ y, ‖h y + d * h' y‖ₑ ^ 2 ∂(ν.withDensity fun x => w x) := fun d => by
    rw [e1 (fun x => f x + d * f' x) (hf.add (hf'.const_mul d)), e2 (fun y => h y + d * h' y) (hh.add (hh'.const_mul d))]
    simpa only [one_mul] using H 1 d
  simp only [H3] at a2
  rw [← b2, integral_withDensity_eq_integral_smul hv, integral_withDensity_eq_integral_smul hw] at a2
  rw [integrable_withDensity_iff_integrable_smul hv] at a1
  rw [integrable_withDensity_iff_integrable_smul hw] at b1
  simp only [NNReal.smul_def, Complex.real_smul, mul_comm ((_ : ℝ) : ℂ)] at a1 b1 a2
  exact ⟨a1, b1, a2⟩

end Polar

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem secondCountable_GA : SecondCountableTopology (GA E a) := by
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem dot_algebraMap {ι : Type} [Fintype ι] (ξ c : ι → E) :
    dot ξ (fun t => algebraMap E (Ad E) (c t)) = algebraMap E (Ad E) (∑ t, ξ t * c t) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dot, map_sum, map_mul]

theorem good_left_mirU (hψ : StdPsi ψ) {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) {γ : GL (Fin a) E}
    (hγ : γ ∈ mirU E a m) (g : GA E a) : f (ratGL E a γ * g) = f g := by
  obtain ⟨u, hu, g₀, hg₀, rfl, h1, -⟩ := exists_peel (Nat.le_succ m) hγ
  rw [map_mul, mul_assoc, invariant_colGen (ratGL E a) f (fun k hk y g => by
    rw [ratGL_blkU, hf.law k hk, dot_algebraMap, hψ.rat, one_mul]) hu]
  refine hf.left g₀ (fun i k h => ?_) g
  by_cases hk : m < (k : ℕ)
  · exact h1 i k hk
  · exact hg₀ i k (by omega) (by change (k : ℕ) ≤ i; omega)

theorem good_comb {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ m f) (hf' : Good ψ m f') (c d : ℂ) :
    Good ψ m (fun g => c * f g + d * f' g) := by
  refine ⟨(continuous_const.mul hf.cont).add (continuous_const.mul hf'.cont), ?_, ?_, ?_⟩
  · intro γ hγ g
    rw [hf.left γ hγ, hf'.left γ hγ]
  · intro k hk y g
    rw [hf.law k hk, hf'.law k hk]
    ring
  · intro r h0 hr g
    have p1 := per_blk (r := r) (m := m) (f := fun g => c * f g) (continuous_const.mul hf.cont)
      (fun x g => by rw [hf.left _ (isMir_blkU x)]) g
    have p2 := per_blk (r := r) (m := m) (f := fun g => d * f' g) (continuous_const.mul hf'.cont)
      (fun x g => by rw [hf'.left _ (isMir_blkU x)]) g
    have := GlobalTheory.T.quotientAverage_add_of_periodic _ (ratV E (UnipotentBlockColumnIndex a r m)) (isCoLat_ratV E _) _ _ p1 p2
    rw [avg_const_mul, avg_const_mul, hf.van r h0 hr, hf'.van r h0 hr] at this
    simpa using this

theorem good_smul {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) (c : ℂ) : Good ψ m (fun g => c * f g) := by
  simpa using good_comb hf hf c 0

theorem sum_eLast_mul {m : ℕ} (hm : m + 1 < a) (φ : Fin a → E) :
    ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * φ s.1.1 = φ ⟨m, by omega⟩ := by
  rw [Finset.sum_eq_single (⟨(⟨m, by omega⟩, ⟨m + 1, hm⟩), by simp⟩ : UnipotentBlockColumnIndex a (m + 1) (m + 1))]
  · simp [eLast]
  · intro s _ hs
    rw [eLast, if_neg, zero_mul]
    intro e
    have := s.2
    exact hs (Subtype.ext (Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))))
  · simp

theorem exists_transversal {m : ℕ} (hm : m + 1 < a) :
    ∃ (γ : {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E // ξ ≠ 0} → GL (Fin a) E)
      (e : ratMirU E a m × {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E // ξ ≠ 0} ≃ ratMirU E a (m + 1)),
      (∀ ξ, IsMir (m + 1) (γ ξ) ∧ (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * (γ ξ).val s.1.1 t.1.1) = ξ.1) ∧
        ∀ p, (e p : GA E a) = p.1 * ratGL E a (γ p.2) := by
  choose γ hγ hrow using fun ξ : {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E // ξ ≠ 0} => mir_exists_row E a m hm ξ.1 ξ.2
  have hγU : ∀ ξ, γ ξ ∈ mirU E a (m + 1) := fun ξ i k hi _ => hγ ξ i k (Or.inl hi)
  let i₀ : Fin a := ⟨m, by omega⟩
  have hrow' : ∀ ξ (t : UnipotentBlockColumnIndex a (m + 1) (m + 1)), (γ ξ).val i₀ t.1.1 = ξ.1 t := fun ξ t => by
    rw [← hrow ξ t, sum_eLast_mul hm (fun i => (γ ξ).val i t.1.1)]
  have hδ : ∀ δ ∈ mirU E a m, ∀ ξ (t : UnipotentBlockColumnIndex a (m + 1) (m + 1)), (δ * γ ξ).val i₀ t.1.1 = ξ.1 t := by
    intro δ hδ ξ t
    rw [Units.val_mul, mul_apply_congr (hγU ξ) (x' := 1) (fun l hl => hδ i₀ l le_rfl (by change (l : ℕ) ≤ m; omega)) t.2.1,
      Matrix.one_mul, hrow']
  let φ : ratMirU E a m × {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E // ξ ≠ 0} → ratMirU E a (m + 1) := fun p =>
    ⟨p.1 * ratGL E a (γ p.2), mul_mem (Subgroup.map_mono (mirU_mono (Nat.le_succ m)) p.1.2) ⟨_, hγU _, rfl⟩⟩
  refine ⟨γ, Equiv.ofBijective φ ⟨?_, ?_⟩, fun ξ => ⟨hγ ξ, funext (hrow ξ)⟩, fun _ => rfl⟩
  · rintro ⟨⟨_, δ, hδ1, rfl⟩, ξ⟩ ⟨⟨_, δ', hδ2, rfl⟩, ξ'⟩ h
    have h1 : δ * γ ξ = δ' * γ ξ' :=
      GlobalTheory.ThetaUnfold.ratGL_injective (by simpa only [map_mul] using congrArg Subtype.val h)
    have h2 : ξ = ξ' := Subtype.ext (funext fun t => by rw [← hδ δ hδ1 ξ t, h1, hδ δ' hδ2])
    subst h2
    obtain rfl := mul_right_cancel h1
    rfl
  · rintro ⟨_, x, hx, rfl⟩
    let ξ₀ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E := fun t => x.val i₀ t.1.1
    have hl : ∀ l : Fin a, (l : ℕ) < m + 1 → ∃ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), t.1.1 = l := fun l hl =>
      ⟨⟨(l, ⟨m + 1, hm⟩), hl, le_rfl, le_rfl⟩, rfl⟩
    have h0 : ξ₀ ≠ 0 := fun h => by
      have := mul_apply_congr ((mirU E a (m + 1)).inv_mem hx) (x := x.val) (x' := 0) (i := i₀) (k := i₀) (fun l h' => by
        obtain ⟨t, rfl⟩ := hl l h'
        exact congrFun h t) (Nat.lt_succ_self m)
      simp at this
    have h1 : x * (γ ⟨ξ₀, h0⟩)⁻¹ ∈ mirU E a m := by
      intro i k hi hk
      by_cases him : m + 1 ≤ (i : ℕ)
      · exact (mirU E a (m + 1)).mul_mem hx ((mirU E a (m + 1)).inv_mem (hγU _)) i k him hk
      · obtain rfl : i = i₀ := Fin.ext (by change (i : ℕ) = m; omega)
        rw [Units.val_mul, mul_apply_congr ((mirU E a (m + 1)).inv_mem (hγU _)) (x' := (γ ⟨ξ₀, h0⟩).val) (fun l h' => by
          obtain ⟨t, rfl⟩ := hl l h'
          exact (hrow' ⟨ξ₀, h0⟩ t).symm) (Nat.lt_succ_of_le hk), Units.mul_inv]
    refine ⟨⟨⟨_, _, h1, rfl⟩, ⟨ξ₀, h0⟩⟩, Subtype.ext ?_⟩
    change ratGL E a _ * ratGL E a _ = _
    rw [← map_mul, inv_mul_cancel_right]

section Step

variable [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] (μ : Measure (GA E a)) [SFinite μ] [μ.IsMulLeftInvariant]

theorem lintegral_step (hψ : StdPsi ψ) {m : ℕ} (hm : m + 1 < a) {𝓕 𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratMirU E a (m + 1)) 𝓕 μ) (h𝓕' : IsFundamentalDomain (ratMirU E a m) 𝓕' μ)
    (w : GA E a → ℝ≥0∞) (hw : Measurable w) (hwΓ : ∀ γ ∈ mirU E a (m + 1), ∀ g, w (ratGL E a γ * g) = w g)
    (hwU : ∀ k, m < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, w (blkU y * g) = w g)
    {f : GA E a → ℂ} (hf : Good ψ (m + 1) f) :
    ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕', ‖colT ψ (m + 1) f g‖ₑ ^ 2 * w g ∂μ := by
  haveI : T2Space (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Ad E))
  haveI : T2Space (GA E a) := Units.isEmbedding_embedProduct.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E)) := inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Ad E))
  haveI : LocallyCompactSpace (GA E a) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI := secondCountable_GA (E := E) (a := a)
  haveI : DiscreteTopology (ratMirU E a (m + 1)) := discrete_of_le_range (Subgroup.map_le_range _ _)
  haveI : Countable (ratMirU E a (m + 1)) := GlobalTheory.countable_of_discrete_subgroup _
  letI : MeasurableSpace (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) := borel _
  haveI : BorelSpace (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) := ⟨rfl⟩
  have hL := isCoLat_ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))
  haveI := hL.1
  haveI : Countable (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) := GlobalTheory.countable_of_discrete_addSubgroup _
  obtain ⟨ν, D, hν, hD, hνD⟩ := exists_fundamentalDomain_mass_one _ _ hL
  have hT := GlobalTheory.CuspRep.Generic.good_colT hψ hm hf
  have hnorm : ∀ k, m + 1 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, ‖f (blkU y * g)‖ₑ = ‖f g‖ₑ := fun k hk y g => by
    rw [hf.law k hk, enorm_mul, ← ofReal_norm (ψ _), hψ.norm, ENNReal.ofReal_one, one_mul]
  have havg := GlobalTheory.T.setLIntegral_average_abelian_quotient_alt (GA E a) (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) μ (ratMirU E a (m + 1)) (lateU (Ad E) a (m + 1))
    (isClosed_lateU _) (by rintro _ ⟨γ, hγ, rfl⟩ u hu; exact conj_mem_lateU (map_mem_mirU _ hγ) hu)
    (by
      obtain ⟨K, hK, h⟩ := exists_compact_lateU (E := E) (a := a) (m + 1)
      refine ⟨K, hK, fun u hu => ?_⟩
      obtain ⟨γ, h1, h2, h3⟩ := h u hu
      exact ⟨_, ⟨γ, mirU_mono (Nat.zero_le _) h1, rfl⟩, h2, h3⟩)
    blkU blkU_add (continuous_posU (isNil_blk a (m + 1) (m + 1))).measurable (blkU_mem_lateU le_rfl) ν (ratV E _)
    (by rintro _ ⟨c, rfl⟩; exact ⟨blkU c, blkU_mem_mirU _ c, ratGL_blkU c⟩) D hD hνD 𝓕 h𝓕
    (fun g => ‖f g‖ₑ ^ 2 * w g) ((hf.cont.measurable.enorm.pow_const 2).mul hw)
    (by rintro _ ⟨γ, hγ, rfl⟩ g; simp only [good_left_mirU hψ hf hγ, hwΓ γ hγ])
    (fun u hu => by
      obtain ⟨v, hv, y, rfl⟩ := exists_eq_colGen_mul_blkU hu
      refine ⟨y, fun g => ?_⟩
      rw [mul_assoc]
      exact invariant_colGen (MonoidHom.id _) (fun g => ‖f g‖ₑ ^ 2 * w g) (fun k hk z g => by
        simp only [MonoidHom.id_apply, hnorm k hk, hwU k (by omega)]) hv _)
  obtain ⟨γ, e, hγ, he⟩ := exists_transversal (E := E) hm
  rw [havg, ← GlobalTheory.ThetaUnfold.lintegral_unfold μ _ _ (fun ξ => ratGL E a (γ ξ)) e he h𝓕 h𝓕'
    (fun g => ‖colT ψ (m + 1) f g‖ₑ ^ 2 * w g)
    (by rintro _ ⟨δ, hδ, rfl⟩ g; simp only [good_left_mirU hψ hT hδ, hwΓ δ (mirU_mono (Nat.le_succ m) hδ)])
    ((hT.cont.measurable.enorm.pow_const 2).mul hw).aemeasurable]
  refine lintegral_congr fun g => ?_
  have hper : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g)) :=
    per_blk hf.cont (fun c g => hf.left _ (isMir_blkU c) g) g
  have h0 : coefF ψ (m + 1) 0 f g = 0 := by
    have e0 : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E, ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := fun x => by
      simp [dot]
    simp only [coefF, e0, one_mul]
    exact hf.van (m + 1) (Nat.succ_pos m) le_rfl g
  have hc : ∀ ξ, colT ψ (m + 1) f (ratGL E a (γ ξ) * g) = coefF ψ (m + 1) ξ.1 f g := fun ξ => by
    rw [colT, coefF_ratGL_mul E a ψ hψ m f hf.cont hf.left _ (hγ ξ).1, (hγ ξ).2]
  have hwγ : ∀ ξ, w (ratGL E a (γ ξ) * g) = w g := fun ξ => hwΓ _ (fun i k hi _ => (hγ ξ).1 i k (Or.inl hi)) g
  simp only [hwU (m + 1) (Nat.lt_succ_self m), hc, hwγ]
  rw [lintegral_mul_const _ (hper.1.measurable.enorm.pow_const 2), ENNReal.tsum_mul_right,
    ← GlobalTheory.T.parseval_continuous_periodic_adelicRationalQuotient E _ ψ hψ _ hper ν D hν hD hνD]
  congr 1
  refine (tsum_subtype_eq_of_support_subset (f := fun ξ => ‖coefF ψ (m + 1) ξ f g‖ₑ ^ 2) (s := {ξ | ξ ≠ 0}) ?_).symm
  rintro ξ hξ rfl
  simp [h0] at hξ

theorem lintegral_tower (hψ : StdPsi ψ) {m : ℕ} (hm : m < a ∨ m = 0) {𝓕 𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratMirU E a m) 𝓕 μ) (h𝓕' : IsFundamentalDomain (ratMirU E a 0) 𝓕' μ)
    (w : GA E a → ℝ≥0∞) (hw : Measurable w) (hwΓ : ∀ γ ∈ mirU E a m, ∀ g, w (ratGL E a γ * g) = w g)
    (hwU : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, w (blkU y * g) = w g)
    {f : GA E a → ℂ} (hf : Good ψ m f) :
    ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕', ‖whit ψ m f g‖ₑ ^ 2 * w g ∂μ := by
  haveI := secondCountable_GA (E := E) (a := a)
  haveI : ∀ n, DiscreteTopology (ratMirU E a n) := fun n => discrete_of_le_range (Subgroup.map_le_range _ _)
  induction m generalizing f 𝓕 with
  | zero =>
    haveI : Countable (ratMirU E a 0) := GlobalTheory.countable_of_discrete_subgroup _
    haveI : SMulInvariantMeasure (ratMirU E a 0) (GA E a) μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : GA E a) s⟩
    refine h𝓕.setLIntegral_eq h𝓕' _ ?_
    rintro ⟨_, γ, hγ, rfl⟩ g
    change ‖f (ratGL E a γ * g)‖ₑ ^ 2 * w (ratGL E a γ * g) = _
    rw [good_left_mirU hψ hf hγ, hwΓ γ hγ]
  | succ m ih =>
    have h1 : m + 1 < a := by omega
    obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratMirU E a m)
    rw [lintegral_step μ hψ h1 h𝓕 (hD μ) w hw hwΓ (fun k hk => hwU k (by omega)) hf, whit_succ]
    exact ih (Or.inl (by omega)) (hD μ) (fun γ hγ => hwΓ γ (mirU_mono (Nat.le_succ m) hγ))
      (GlobalTheory.CuspRep.Generic.good_colT hψ h1 hf)

theorem integral_tower (hψ : StdPsi ψ) {m : ℕ} (hm : m < a ∨ m = 0) {𝓕 𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratMirU E a m) 𝓕 μ) (h𝓕' : IsFundamentalDomain (ratMirU E a 0) 𝓕' μ)
    (w : GA E a → ℝ≥0) (hw : Measurable w) (hwΓ : ∀ γ ∈ mirU E a m, ∀ g, w (ratGL E a γ * g) = w g)
    (hwU : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, w (blkU y * g) = w g)
    {f f' : GA E a → ℂ} (hf : Good ψ m f) (hf' : Good ψ m f')
    (h1 : ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ ≠ ⊤) (h2 : ∫⁻ g in 𝓕, ‖f' g‖ₑ ^ 2 * w g ∂μ ≠ ⊤) :
    IntegrableOn (fun g => f g * conj (f' g) * (w g : ℝ)) 𝓕 μ ∧
      IntegrableOn (fun g => whit ψ m f g * conj (whit ψ m f' g) * (w g : ℝ)) 𝓕' μ ∧
      ∫ g in 𝓕, f g * conj (f' g) * (w g : ℝ) ∂μ = ∫ g in 𝓕', whit ψ m f g * conj (whit ψ m f' g) * (w g : ℝ) ∂μ := by
  refine integral_mul_conj_eq_of_lintegral hf.cont.measurable hf'.cont.measurable
    (GlobalTheory.CuspRep.Generic.whit_good hψ m hm hf).1.cont.measurable
    (GlobalTheory.CuspRep.Generic.whit_good hψ m hm hf').1.cont.measurable hw hw (fun c d => ?_) h1 h2
  rw [lintegral_tower μ hψ hm h𝓕 h𝓕' (fun g => w g) hw.coe_nnreal_ennreal (fun γ hγ g => by rw [hwΓ γ hγ])
      (fun k hk y g => by rw [hwU k hk]) (good_comb hf hf' c d),
    GlobalTheory.CuspRep.Generic.whit_add hψ m hm (good_smul hf c) (good_smul hf' d),
    GlobalTheory.CuspRep.Generic.whit_smul, GlobalTheory.CuspRep.Generic.whit_smul]

end Step

end GlobalTheory.MirTower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.MirTower
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.MirTower

theorem unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (𝓕 𝓕₀ : Set (GA E a)), IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕 μ → IsFundamentalDomain (ratMirU E a 0) 𝓕₀ μ → ∀ (w : GA E a → ℝ≥0), Measurable w → (∀ γ ∈ mirU E a (a - 1), ∀ g, w (ratGL E a γ * g) = w g) → (∀ (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), w (blkU y * g) = w g) → (∀ f, Good ψ (a - 1) f → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕₀, ‖whit ψ (a - 1) f g‖ₑ ^ 2 * w g ∂μ) ∧ ∀ f f', Good ψ (a - 1) f → Good ψ (a - 1) f' → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → ∫⁻ g in 𝓕, ‖f' g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → IntegrableOn (fun g => f g * conj (f' g) * (w g : ℝ)) 𝓕 μ ∧ IntegrableOn (fun g => whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ)) 𝓕₀ μ ∧ ∫ g in 𝓕, f g * conj (f' g) * (w g : ℝ) ∂μ = ∫ g in 𝓕₀, whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ) ∂μ := by
  intro E _ _ a _ _ μ _ ψ hψ 𝓕 𝓕₀ h𝓕 h𝓕₀ w hw hwΓ hwU

  have hm : a - 1 < a ∨ a - 1 = 0 := by omega

  have : SecondCountableTopology (GA E a) := secondCountable_GA

  have : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Ad E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GA E a) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  set_option synthInstance.maxHeartbeats 100000 in
  have : SFinite μ := inferInstance
  refine ⟨fun f hf => ?_, fun f f' hf hf' h1 h2 => ?_⟩
  · exact lintegral_tower μ hψ hm h𝓕 h𝓕₀ (fun g => (w g : ℝ≥0∞)) (by fun_prop)
      (fun γ hγ g => by simp only [hwΓ γ hγ g]) (fun k _ y g => by simp only [hwU k y g]) hf
  · exact integral_tower μ hψ hm h𝓕 h𝓕₀ w hw hwΓ (fun k _ y g => hwU k y g) hf hf' h1 h2

end GlobalTheory.MirTower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolicStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.MirTower
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_mirabolic_alt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (𝓕 𝓕₀ : Set (GA E a)), IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕 μ → IsFundamentalDomain (ratMirU E a 0) 𝓕₀ μ → ∀ (w : GA E a → ℝ≥0), Measurable w → (∀ γ ∈ mirU E a (a - 1), ∀ g, w (ratGL E a γ * g) = w g) → (∀ (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), w (blkU y * g) = w g) → (∀ f, Good ψ (a - 1) f → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕₀, ‖whit ψ (a - 1) f g‖ₑ ^ 2 * w g ∂μ) ∧ ∀ f f', Good ψ (a - 1) f → Good ψ (a - 1) f' → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → ∫⁻ g in 𝓕, ‖f' g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → IntegrableOn (fun g => f g * conj (f' g) * (w g : ℝ)) 𝓕 μ ∧ IntegrableOn (fun g => whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ)) 𝓕₀ μ ∧ ∫ g in 𝓕, f g * conj (f' g) * (w g : ℝ) ∂μ = ∫ g in 𝓕₀, whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ) ∂μ := by
  first | exact @GlobalTheory.MirTower.unfold_mirabolic | exact GlobalTheory.MirTower.unfold_mirabolic | (intros; apply GlobalTheory.MirTower.unfold_mirabolic <;> assumption)
end
