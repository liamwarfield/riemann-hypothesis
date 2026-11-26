module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMapMulRightEqSmul
open MeasureTheory

namespace GlobalTheory.IwasawaShape

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableInv G] in
theorem lintegral_mul_left_of_map {ρ : Measure G} {p : G} (h : ρ.map (fun g => p * g) = ρ) (f : G → ENNReal)
    (hf : Measurable f) : ∫⁻ x, f (p * x) ∂ρ = ∫⁻ x, f x ∂ρ := by
  have e := lintegral_map (μ := ρ) hf (measurable_const_mul p)
  rw [h] at e
  exact e.symm

theorem exists_map_mul_right_eq_smul (P : Subgroup G) (hP : MeasurableSet (P : Set G)) (ρ : Measure G)
    [SigmaFinite ρ] (h0 : ρ (P : Set G)ᶜ = 0) (hinv : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ)
    (T : Set G) (hT : MeasurableSet T) (hT0 : ρ T ≠ 0) (hT1 : ρ T ≠ ⊤) (l : G) (hl : l ∈ P) :
    ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ρ.map (fun g => g * l) = D • ρ := by
  classical
  have e : MeasurableEmbedding (Subtype.val : P → G) := MeasurableEmbedding.subtype_coe hP
  have : MeasurableMul₂ P := ⟨e.measurable_comp_iff.1
    ((measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd))⟩
  have : MeasurableInv P := ⟨e.measurable_comp_iff.1 measurable_subtype_coe.inv⟩
  set ρ' : Measure P := ρ.comap Subtype.val with hρ'
  have hmap : ρ'.map Subtype.val = ρ := by
    rw [hρ', e.map_comap, Subtype.range_coe_subtype, Measure.restrict_eq_self_of_ae_mem]
    exact ae_iff.2 h0
  have inj : ∀ α β : Measure P, α.map Subtype.val = β.map Subtype.val → α = β := fun α β h => by
    rw [← e.comap_map α, ← e.comap_map β, h]
  have : SigmaFinite ρ' :=
    SigmaFinite.of_map ρ' measurable_subtype_coe.aemeasurable (by rw [hmap]; infer_instance)
  have : ρ'.IsMulLeftInvariant := ⟨fun s => inj _ _ (by
    rw [Measure.map_map measurable_subtype_coe (measurable_const_mul s)]
    have hc : (Subtype.val ∘ fun x : P => s * x) = (fun g : G => (s : G) * g) ∘ Subtype.val := rfl
    rw [hc, ← Measure.map_map (measurable_const_mul _) measurable_subtype_coe, hmap, hinv s s.2])⟩
  let l' : P := ⟨l, hl⟩
  set ν' : Measure P := ρ'.map (fun x => x * l') with hν'
  have : ν'.IsMulLeftInvariant := ⟨fun s => by
    rw [hν', Measure.map_map (measurable_const_mul s) (measurable_mul_const l')]
    have hc : ((fun x : P => s * x) ∘ fun x => x * l') = (fun x => x * l') ∘ (fun x => s * x) := by
      funext x; simp [Function.comp, mul_assoc]
    rw [hc, ← Measure.map_map (measurable_mul_const l') (measurable_const_mul s), map_mul_left_eq_self]⟩
  have : SigmaFinite ν' := SigmaFinite.of_map ν' (measurable_mul_const l'⁻¹).aemeasurable (by
    rw [hν', Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
    have hc : ((fun x : P => x * l'⁻¹) ∘ fun x => x * l') = id := by funext x; simp
    rw [hc, Measure.map_id]; infer_instance)
  have hρT' : ρ' (Subtype.val ⁻¹' T) = ρ T := by
    rw [hρ', e.comap_apply, Set.image_preimage_eq_inter_range]
    exact measure_inter_conull (by rw [Subtype.range_coe_subtype]; exact h0)
  have hEq := measure_eq_div_smul ν' ρ' (s := Subtype.val ⁻¹' T) (by rw [hρT']; exact hT0)
    (by rw [hρT']; exact hT1)
  set D := ν' (Subtype.val ⁻¹' T) / ρ' (Subtype.val ⁻¹' T) with hD
  have hmapD : ρ.map (fun g => g * l) = D • ρ := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_map (measurable_mul_const l) measurable_subtype_coe]
    have hc : ((fun g : G => g * l) ∘ Subtype.val) = Subtype.val ∘ (fun x : P => x * l') := rfl
    rw [hc, ← Measure.map_map measurable_subtype_coe (measurable_mul_const l'), ← hν', hEq,
      Measure.map_smul D e.measurable.aemeasurable, hmap]
  have huniv : (ρ.map fun g => g * l) Set.univ ≠ 0 := by
    rw [Measure.map_apply (measurable_mul_const l) MeasurableSet.univ, Set.preimage_univ]
    exact fun h => hT0 (measure_mono_null (Set.subset_univ _) h)
  have hD0 : D ≠ 0 := by
    intro h
    apply huniv
    rw [hmapD, h, zero_smul, Measure.coe_zero, Pi.zero_apply]
  have hD1 : D ≠ ⊤ := by
    intro h
    have : SigmaFinite (ρ.map fun g => g * l) :=
      SigmaFinite.of_map _ (measurable_mul_const l⁻¹).aemeasurable (by
        rw [Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
        have hc : ((fun g : G => g * l⁻¹) ∘ fun g => g * l) = id := by funext x; simp
        rw [hc, Measure.map_id]; infer_instance)
    obtain ⟨n, hn⟩ : ∃ n, (ρ.map fun g => g * l) (spanningSets (ρ.map fun g => g * l) n) ≠ 0 := by
      by_contra hne
      push Not at hne
      apply huniv
      rw [← iUnion_spanningSets (ρ.map fun g => g * l)]
      exact measure_iUnion_null hne
    have hlt := measure_spanningSets_lt_top (ρ.map fun g => g * l) n
    set Sn := spanningSets (ρ.map fun g => g * l) n
    rw [hmapD, Measure.smul_apply, smul_eq_mul, h] at hn hlt
    rcases eq_or_ne (ρ Sn) 0 with h' | h'
    · exact hn (by rw [h', mul_zero])
    · rw [ENNReal.top_mul h'] at hlt
      exact lt_irrefl _ hlt
  exact ⟨D, hD0, hD1, hmapD⟩

theorem exists_lintegral_eq_mul (μ ρ κ : Measure G) [SigmaFinite μ] [SFinite ρ] [IsProbabilityMeasure κ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (hμ : μ ≠ 0) (P K : Set G)
    (hKl : ∀ k ∈ K, κ.map (fun g => k * g) = κ) (hPl : ∀ p ∈ P, ρ.map (fun g => p * g) = ρ)
    (hPr : ∀ p ∈ P, ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ρ.map (fun g => g * p) = D • ρ)
    (hdec : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) (T : Set G) (hT : MeasurableSet T)
    (hTK : ∀ k ∈ K, ∀ g, k⁻¹ * g ∈ T ↔ g ∈ T) (hT0 : ρ T ≠ 0) (hT1 : ρ T ≠ ⊤) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂μ = c * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ := by
  classical
  have hind : Measurable (T.indicator (1 : G → ENNReal)) := measurable_one.indicator hT
  have ind_ne_top : ∀ x, T.indicator (1 : G → ENNReal) x ≠ ⊤ := fun x => by
    by_cases hx : x ∈ T <;> simp [Set.indicator_apply, hx]
  have hLm : ∀ φ : G → ENNReal, Measurable φ →
      Measurable fun h => T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ :=
    fun φ hφ => (hind.comp measurable_inv).mul
      ((hφ.comp (by fun_prop : Measurable fun y : (G × G) × G => y.1.2 * y.1.1 * y.2)).lintegral_prod_right').lintegral_prod_right'

  have key : ∀ h : G, ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ = D * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ := by
    intro h
    obtain ⟨p0, hp0, k0, hk0, rfl⟩ := hdec h
    obtain ⟨D, hD0, hDt, hD⟩ := hPr p0 hp0
    refine ⟨D, hD0, hDt, fun φ hφ => ?_⟩
    have hF : Measurable fun x => ∫⁻ k, φ (x * k) ∂κ := (hφ.comp measurable_mul).lintegral_prod_right'
    have e1 : ∀ q, ∫⁻ k, φ (q * (p0 * k0) * k) ∂κ = ∫⁻ k, φ (q * p0 * k) ∂κ := by
      intro q
      have := lintegral_mul_left_of_map (hKl k0 hk0) (fun k => φ (q * p0 * k))
        (hφ.comp (measurable_const_mul _))
      simpa only [mul_assoc] using this
    simp_rw [e1]
    have := lintegral_map (μ := ρ) hF (measurable_mul_const p0)
    rw [hD, lintegral_smul_measure, smul_eq_mul] at this
    exact this.symm

  have mix : ∀ φ : G → ENNReal, Measurable φ →
      ρ T * ∫⁻ g, φ g ∂μ = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ ∂μ := by
    intro φ hφ
    have s1 : ∫⁻ g, φ g ∂μ = ∫⁻ g, ∫⁻ k, φ (g * k) ∂κ ∂μ := by
      rw [lintegral_lintegral_swap (f := fun g k => φ (g * k)) (by exact (hφ.comp measurable_mul).aemeasurable)]
      simp_rw [lintegral_mul_right_eq_self]
      rw [lintegral_const, measure_univ, mul_one]
    have s2 : ∀ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) ∂ρ = ρ T := by
      intro g
      obtain ⟨p0, hp0, k0, hk0, rfl⟩ := hdec g
      have e : ∀ q, T.indicator (1 : G → ENNReal) ((p0 * k0)⁻¹ * q) = T.indicator 1 (p0⁻¹ * q) := by
        intro q
        have hm : (p0 * k0)⁻¹ * q ∈ T ↔ p0⁻¹ * q ∈ T := by
          rw [mul_inv_rev, mul_assoc]; exact hTK k0 hk0 _
        simp only [Set.indicator_apply, hm, Pi.one_apply]
      simp_rw [e]
      have := lintegral_mul_left_of_map (hPl p0 hp0) (fun x => T.indicator (1 : G → ENNReal) (p0⁻¹ * x))
        (hind.comp (measurable_const_mul _))
      simp only [inv_mul_cancel_left] at this
      rw [← this, lintegral_indicator_one hT]
    have hW1 : ∫⁻ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ ∂μ
        = ρ T * ∫⁻ g, φ g ∂μ := by
      have e : ∀ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ
          = ρ T * ∫⁻ k, φ (g * k) ∂κ := by
        intro g
        exact (lintegral_mul_const _ (hind.comp (measurable_const_mul g⁻¹))).trans (congrArg (· * _) (s2 g))
      simp_rw [e]
      rw [lintegral_const_mul' _ _ hT1, ← s1]
    have hmF : Measurable fun x : G × G =>
        T.indicator (1 : G → ENNReal) (x.1⁻¹ * x.2) * ∫⁻ k, φ (x.1 * k) ∂κ :=
      (hind.comp (measurable_fst.inv.mul measurable_snd)).mul
        (((hφ.comp measurable_mul).lintegral_prod_right').comp measurable_fst)
    have hmG : Measurable fun x : G × G =>
        T.indicator (1 : G → ENNReal) x.2⁻¹ * ∫⁻ k, φ (x.1 * x.2 * k) ∂κ :=
      (hind.comp measurable_snd.inv).mul
        ((hφ.comp (by fun_prop : Measurable fun y : (G × G) × G => y.1.1 * y.1.2 * y.2)).lintegral_prod_right')
    have hW2 : ∫⁻ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ ∂μ
        = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ ∂μ := by
      rw [lintegral_lintegral_swap (f := fun g q => T.indicator (1 : G → ENNReal) (g⁻¹ * q) *
        ∫⁻ k, φ (g * k) ∂κ) (by exact hmF.aemeasurable)]
      have e : ∀ q, ∫⁻ g, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂μ
          = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ k, φ (q * h * k) ∂κ ∂μ := by
        intro q
        refine (lintegral_mul_left_eq_self (μ := μ) (fun g => T.indicator (1 : G → ENNReal) (g⁻¹ * q) *
          ∫⁻ k, φ (g * k) ∂κ) q).symm.trans ?_
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      simp_rw [e]
      rw [lintegral_lintegral_swap (f := fun q h => T.indicator (1 : G → ENNReal) h⁻¹ *
        ∫⁻ k, φ (q * h * k) ∂κ) (by exact hmG.aemeasurable)]
      exact lintegral_congr fun h => lintegral_const_mul' _ _ (ind_ne_top _)
    rw [← hW1, hW2]

  obtain ⟨S, hS, hS0, hS1⟩ : ∃ S, MeasurableSet S ∧ μ S ≠ 0 ∧ μ S ≠ ⊤ := by
    by_contra hne
    push Not at hne
    apply hμ
    have hz : ∀ n, μ (spanningSets μ n) = 0 := fun n => by
      by_contra hn
      exact (measure_spanningSets_lt_top μ n).ne (hne _ (measurableSet_spanningSets μ n) hn)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
    exact measure_iUnion_null hz
  have hφ0 : Measurable (S.indicator (1 : G → ENNReal)) := measurable_one.indicator hS
  have hμS : ∫⁻ g, S.indicator (1 : G → ENNReal) g ∂μ = μ S := lintegral_indicator_one hS
  have mix0 := mix _ hφ0
  rw [hμS] at mix0
  have hL0 : ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ ≠ 0 := by
    intro h0
    have : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, S.indicator (1 : G → ENNReal) (q * h * k) ∂κ ∂ρ ∂μ = 0 := by
      refine (lintegral_congr fun h => ?_).trans lintegral_zero
      obtain ⟨D, -, -, hD⟩ := key h
      rw [hD _ hφ0, h0, mul_zero, mul_zero]
    rw [this] at mix0
    exact mul_ne_zero hT0 hS0 mix0
  have hLt : ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ ≠ ⊤ := by
    intro ht
    have : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, S.indicator (1 : G → ENNReal) (q * h * k) ∂κ ∂ρ ∂μ
        = (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) * ⊤ := by
      rw [← (lintegral_mul_const ⊤ (hind.comp measurable_inv) : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ⊤ ∂μ = (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) * ⊤)]
      refine lintegral_congr fun h => ?_
      obtain ⟨D, hD0, -, hD⟩ := key h
      rw [hD _ hφ0, ht, ENNReal.mul_top hD0]
    rw [this] at mix0
    rcases eq_or_ne (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) 0 with hz | hz
    · rw [hz, zero_mul] at mix0
      exact mul_ne_zero hT0 hS0 mix0
    · rw [ENNReal.mul_top hz] at mix0
      exact ENNReal.mul_ne_top hT1 hS1 mix0
  refine ⟨μ S / ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ,
    (ENNReal.div_pos_iff.2 ⟨hS0, hLt⟩).ne', ENNReal.div_ne_top hS1 hL0, fun φ hφ => ?_⟩
  have E : ρ T * ((∫⁻ g, φ g ∂μ) * ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ)
      = ρ T * (μ S * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ) := by
    rw [← mul_assoc]
    rw [mix _ hφ]
    rw [← lintegral_mul_const _ (hLm _ hφ)]
    rw [← mul_assoc]
    rw [mix0]
    rw [← lintegral_mul_const _ (hLm _ hφ0)]
    refine lintegral_congr fun h => ?_
    obtain ⟨D, -, -, hD⟩ := key h
    rw [hD _ hφ, hD _ hφ0]
    ring
  have E' := (ENNReal.mul_right_inj hT0 hT1).1 E
  rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  exact (ENNReal.eq_div_iff hL0 hLt).2 (by rw [mul_comm]; exact E')

end GlobalTheory.IwasawaShape
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubmoduleSkewBlockFinrankLe
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

def skewOpsBlock (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    Submodule ℝ (F →L[ℂ] F) where
  carrier := {M | ∀ x z, ⟪M x, z⟫_ℂ + ⟪x, M z⟫_ℂ = 0}
  zero_mem' := by intro x z; simp
  add_mem' := by
    intro a b ha hb x z
    have h1 := ha x z
    have h2 := hb x z
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    linear_combination h1 + h2
  smul_mem' := by
    intro c a ha x z
    have h1 := ha x z
    have e : ∀ y, (c • a) y = (c : ℂ) • a y := fun y => by
      simp [Complex.coe_smul]
    simp only [e, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    linear_combination (c : ℂ) * h1

theorem finrank_skewOpsBlock_le (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] :
    Module.finrank ℝ (skewOpsBlock F) ≤ Module.finrank ℂ F ^ 2 := by
  let J : (F →L[ℂ] F) →ₗ[ℝ] (F →L[ℂ] F) :=
    { toFun := fun M => Complex.I • M
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun c a => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  have hJ : Function.Injective J := by
    intro a b h
    exact smul_right_injective _ Complex.I_ne_zero h
  have hd : Disjoint (skewOpsBlock F) ((skewOpsBlock F).map J) := by
    rw [Submodule.disjoint_def]
    rintro a ha ⟨b, hb, rfl⟩
    have hb0 : b = 0 := by
      ext x
      have h1 := ha x (b x)
      have h2 := hb x (b x)
      have e : ∀ y, J b y = Complex.I • b y := fun y => rfl
      simp only [e, inner_smul_left, inner_smul_right, Complex.conj_I] at h1
      have h3 : ⟪b x, b x⟫_ℂ = 0 := by
        linear_combination (Complex.I / 2) * h1 + (1 / 2 : ℂ) * h2 +
          ((⟪b x, b x⟫_ℂ - ⟪x, b (b x)⟫_ℂ) / 2) * Complex.I_mul_I
      simpa using h3
    rw [hb0, map_zero]
  haveI : FiniteDimensional ℝ (F →L[ℂ] F) := FiniteDimensional.complexToReal _
  have h1 := Submodule.finrank_add_finrank_le_of_disjoint hd
  rw [← (Submodule.equivMapOfInjective J hJ (skewOpsBlock F)).finrank_eq,
    finrank_real_of_complex] at h1
  have h2 : Module.finrank ℂ (F →L[ℂ] F) = Module.finrank ℂ F ^ 2 := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := F) (F' := F)).finrank_eq,
      Module.finrank_linearMap, sq]
  omega

theorem exists_submodule_skew_block_finrank_le (n : ℕ)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    ∃ U : Submodule ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      Module.finrank ℝ U ≤ Module.finrank ℂ E ^ 2 ∧
      ∀ T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        (∀ x ∈ E, ∀ z ∈ E, ⟪T x, z⟫_ℂ + ⟪x, T z⟫_ℂ = 0) →
          E.starProjection ∘L T ∘L E.starProjection ∈ U := by
  let Φ : (E →L[ℂ] E) →ₗ[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => E.subtypeL ∘L M ∘L E.orthogonalProjection
      map_add' := fun a b => by ext1 x; rfl
      map_smul' := fun c a => by ext1 x; rfl }
  haveI : FiniteDimensional ℝ (E →L[ℂ] E) := FiniteDimensional.complexToReal _
  refine ⟨(skewOpsBlock E).map Φ,
    (Submodule.finrank_map_le Φ _).trans (finrank_skewOpsBlock_le E), ?_⟩
  intro T hT
  refine ⟨E.orthogonalProjection ∘L T ∘L E.subtypeL, ?_, ?_⟩
  · intro x z
    have := hT x x.2 z z.2
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Submodule.inner_orthogonalProjection_eq_of_mem_left,
      Submodule.inner_orthogonalProjection_eq_of_mem_right]
    exact this
  · ext1 x; rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarProjectionInfOrthogonalEqOfMemOrthogonal
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem starProjection_inf_orthogonal_eq_sub {n : ℕ}
    (A A' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : A' ≤ A) (y : EuclideanSpace ℂ (Fin n))
    (hy : y ∈ A) : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.mem_inf.2
      ⟨A.sub_mem hy (h (A'.starProjection_apply_mem y)), A'.sub_starProjection_mem_orthogonal y⟩
  · intro w hw
    rw [sub_sub_cancel]
    exact Submodule.inner_right_of_mem_orthogonal (A'.starProjection_apply_mem y)
      (Submodule.mem_inf.1 hw).2

theorem starProjection_inf_orthogonal_eq_of_mem_orthogonal {n : ℕ}
    (C C' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : C' ≤ C) (v : EuclideanSpace ℂ (Fin n))
    (hv : v ∈ C'ᗮ) : (C ⊓ C'ᗮ).starProjection v = C.starProjection v := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · refine Submodule.mem_inf.2 ⟨C.starProjection_apply_mem v, ?_⟩
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (h hz)]
    exact Submodule.inner_right_of_mem_orthogonal hz hv
  · intro w hw
    exact C.starProjection_inner_eq_zero v w (Submodule.mem_inf.1 hw).1

theorem infDist_le_norm_block_mul (n : ℕ)
    (A A' B B' C C' : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (D T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hD : ∀ x, ‖D x‖ = ‖x‖) (hA : A' ≤ A) (hC : C' ≤ C)
    (hB : ∀ x ∈ B, ∀ z ∈ C', ⟪z, D x⟫_ℂ = 0) (hB' : ∀ x ∈ B', ∀ z ∈ C, ⟪z, D x⟫_ℂ = 0)
    (hdim : Module.finrank ℂ C + Module.finrank ℂ B' = n)
    (hT : ∀ y ∈ A, T y ∈ B) (hT' : ∀ y ∈ A', T y ∈ B') (y : EuclideanSpace ℂ (Fin n))
    (hy : y ∈ A) :
    Metric.infDist (T y) (B' : Set (EuclideanSpace ℂ (Fin n))) ≤
      ‖(C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection‖ * ‖y‖ := by
  have hmap : B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = Cᗮ := by
    have hinj : Function.Injective (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
      intro a b hab
      have h0 : ‖D (a - b)‖ = 0 := by
        rw [map_sub]
        simp only [ContinuousLinearMap.coe_coe] at hab
        rw [hab, sub_self, norm_zero]
      rwa [hD, norm_eq_zero, sub_eq_zero] at h0
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      rw [Submodule.mem_orthogonal]
      intro z hz
      exact hB' x hx z hz
    · rw [← (Submodule.equivMapOfInjective _ hinj B').finrank_eq]
      symm
      apply Submodule.finrank_add_finrank_orthogonal'
      rw [finrank_euclideanSpace_fin]
      exact hdim
  have hy1 : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y :=
    starProjection_inf_orthogonal_eq_sub A A' hA y hy
  have hy1A : (A ⊓ A'ᗮ).starProjection y ∈ A := by
    rw [hy1]
    exact A.sub_mem hy (hA (A'.starProjection_apply_mem y))
  set w := D (T ((A ⊓ A'ᗮ).starProjection y)) with hw_def
  have hw : w ∈ C'ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact hB _ (hT _ hy1A) z hz
  obtain ⟨b, hb, hbw⟩ : ∃ b ∈ B', D b = Cᗮ.starProjection w := by
    have hmem : Cᗮ.starProjection w ∈
        B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
      rw [hmap]
      exact Cᗮ.starProjection_apply_mem w
    obtain ⟨b, hb, hbw⟩ := hmem
    exact ⟨b, hb, hbw⟩
  have hmemB' : T (A'.starProjection y) + b ∈ B' :=
    B'.add_mem (hT' _ (A'.starProjection_apply_mem y)) hb
  calc Metric.infDist (T y) (B' : Set (EuclideanSpace ℂ (Fin n)))
      ≤ dist (T y) (T (A'.starProjection y) + b) := Metric.infDist_le_dist_of_mem hmemB'
    _ = ‖T ((A ⊓ A'ᗮ).starProjection y) - b‖ := by
      rw [dist_eq_norm, hy1, map_sub]
      congr 1
      abel
    _ = ‖w - Cᗮ.starProjection w‖ := by
      rw [← hD, map_sub, hbw]
    _ = ‖C.starProjection w‖ := by
      rw [Submodule.starProjection_orthogonal_val, sub_sub_cancel]
    _ = ‖(C ⊓ C'ᗮ).starProjection w‖ := by
      rw [starProjection_inf_orthogonal_eq_of_mem_orthogonal C C' hC w hw]
    _ = ‖((C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection) y‖ := rfl
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAndNcardLeProdOfLevels
open Finset

namespace GlobalTheory

theorem card_le_prod_of_separated_levels {α β : Type} (S : Set α) (lv : β → ℕ)
    (r : β → α → α → Prop) (B : β → ℝ) (hr : ∀ b, Equivalence (r b)) (s : Finset β) :
    (∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S →
      (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) →
      (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b) →
    ∀ T : Finset α, (↑T : Set α) ⊆ S → (∀ x ∈ T, ∀ y ∈ T, (∀ b ∈ s, r b x y) → x = y) →
      (T.card : ℝ) ≤ ∏ b ∈ s, B b := by
  classical
  induction s using Finset.induction_on_max_value lv with
  | empty =>
    intro _ T _ hT
    have : T.card ≤ 1 := Finset.card_le_one.2 fun x hx y hy => hT x hx y hy (by simp)
    simpa using this
  | insert a s ha hmax ih =>
    intro hp T hTS hT
    have hps : ∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S →
        (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) →
        (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b := by
      intro b hb T' h1 h2 h3
      refine hp b (mem_insert_of_mem hb) T' h1 ?_ h3
      intro x hx y hy b' hb' hlt
      rcases mem_insert.1 hb' with rfl | hb'
      · exact absurd (hmax b hb) (by omega)
      · exact h2 x hx y hy b' hb' hlt
    have hBa : 0 ≤ B a := by
      simpa using hp a (mem_insert_self _ _) ∅ (by simp) (by simp) (by simp)
    rw [prod_insert ha]
    rcases T.eq_empty_or_nonempty with rfl | ⟨x0, -⟩
    · have := ih hps ∅ (by simp) (by simp)
      simp only [card_empty, Nat.cast_zero] at this ⊢
      positivity
    haveI : Nonempty α := ⟨x0⟩
    let q : α → Set α := fun x => {y | ∀ b ∈ s, r b x y}
    have hq : ∀ x y, q x = q y ↔ ∀ b ∈ s, r b x y := by
      intro x y
      constructor
      · intro h
        have : y ∈ q y := fun b _ => (hr b).refl y
        rw [← h] at this
        exact this
      · intro h
        ext z
        exact ⟨fun hz b hb => (hr b).trans ((hr b).symm (h b hb)) (hz b hb),
          fun hz b hb => (hr b).trans (h b hb) (hz b hb)⟩
    let ρ : α → α := fun x => Function.invFunOn q (↑T : Set α) (q x)
    have hρ : ∀ x ∈ T, ρ x ∈ T ∧ q (ρ x) = q x := fun x hx =>
      Function.invFunOn_pos (f := q) (s := (↑T : Set α)) ⟨x, hx, rfl⟩
    have him : ((T.image ρ).card : ℝ) ≤ ∏ b ∈ s, B b := by
      refine ih hps _ ?_ ?_
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_coe.1 hz)
        exact hTS (hρ x hx).1
      · intro z hz w hw h
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
        obtain ⟨y, hy, rfl⟩ := mem_image.1 hw
        have h' := (hq _ _).2 h
        rw [(hρ x hx).2, (hρ y hy).2] at h'
        simp only [ρ, h']
    have hfib : ∀ z ∈ T.image ρ, ((T.filter (fun x => ρ x = z)).card : ℝ) ≤ B a := by
      intro z _
      have key : ∀ x ∈ T.filter (fun x => ρ x = z), ∀ y ∈ T.filter (fun x => ρ x = z),
          ∀ b ∈ s, r b x y := by
        intro x hx y hy
        obtain ⟨hx, hx'⟩ := mem_filter.1 hx
        obtain ⟨hy, hy'⟩ := mem_filter.1 hy
        rw [← hq, ← (hρ x hx).2, ← (hρ y hy).2, hx', hy']
      refine hp a (mem_insert_self _ _) _ ?_ ?_ ?_
      · intro x hx
        exact hTS (mem_filter.1 (mem_coe.1 hx)).1
      · intro x hx y hy b' hb' hlt
        rcases mem_insert.1 hb' with rfl | hb'
        · exact absurd hlt (lt_irrefl _)
        · exact key x hx y hy b' hb'
      · intro x hx y hy h
        refine hT x (mem_filter.1 hx).1 y (mem_filter.1 hy).1 ?_
        intro b hb
        rcases mem_insert.1 hb with rfl | hb
        · exact h
        · exact key x hx y hy b hb
    rw [Finset.card_eq_sum_card_image ρ T]
    push_cast
    calc ∑ z ∈ T.image ρ, ((T.filter (fun x => ρ x = z)).card : ℝ)
        ≤ ∑ _z ∈ T.image ρ, B a := sum_le_sum hfib
      _ = B a * ((T.image ρ).card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ B a * ∏ b ∈ s, B b := mul_le_mul_of_nonneg_left him hBa

theorem finite_and_ncard_le_prod_of_levels :
    ∀ (α β : Type) (S : Set α) (s : Finset β) (lv : β → ℕ) (r : β → α → α → Prop) (B : β → ℝ), (∀ b, Equivalence (r b)) → (∀ x ∈ S, ∀ y ∈ S, (∀ b ∈ s, r b x y) → x = y) → (∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S → (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) → (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b) → S.Finite ∧ ((S.ncard : ℕ) : ℝ) ≤ ∏ b ∈ s, B b := by
  intro α β S s lv r B hr hinj hp
  have h : ∀ T : Finset α, (↑T : Set α) ⊆ S → (T.card : ℝ) ≤ ∏ b ∈ s, B b := fun T hT =>
    card_le_prod_of_separated_levels S lv r B hr s hp T hT
      fun x hx y hy => hinj x (hT hx) y (hT hy)
  have hS : S.Finite := by
    by_contra hinf
    obtain ⟨n, hn⟩ := exists_nat_gt (∏ b ∈ s, B b)
    obtain ⟨T, hT, hc⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have := h T hT
    rw [hc] at this
    linarith
  refine ⟨hS, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hS]
  exact h _ (by simp)

end GlobalTheory
end
