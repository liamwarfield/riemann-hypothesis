module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPToLiftReal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolEqIndexMulMass
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VolIndex

open GlobalTheory.Mass GlobalTheory.Mass.Levels

theorem latLev_le_range {D : D7} (V : HSp D) : latLev V ≤ (Lev.finE V).range := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
  obtain ⟨g, rfl⟩ := hπ.surjective b
  refine ⟨g, ?_⟩
  change Lev.finE V g =
    ((swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π g) : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D))
  rw [coe_swapPts, hπ g]
  rfl

theorem vol_eq_index_mul_mass : ∀ (D : D7) (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), V.SigOK → V.IsPosDef → K ≤ GlobalTheory.Mass.Levels.latLev V → K.relIndex (GlobalTheory.Mass.Levels.latLev V) ≠ 0 → IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) → IsMeasDef V K ν 𝓕 → (ν 𝓕).toReal = (K.relIndex (GlobalTheory.Mass.Levels.latLev V) : ℝ) * GlobalTheory.Mass.unitaryMass D.sp.cm.sig V.gram (GlobalTheory.Mass.Levels.latStab V) := by
  intro D V K ν 𝓕 hW hs hK hi ho hν
  have hd : Formalism.UG.IsTotDef D.sp.cm.sig V.gram := GlobalTheory.DefiniteQuotient.isTotDef_of_posDef V fun τ => by
    have := hW (Formalism.BasicNotions.TH.tauE D τ)
    rw [hs] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  obtain ⟨hc, hL⟩ := latStab_compact_open V
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := hν.1.1
  have h1 : ν (K.comap (Lev.finE V)) = 1 := measure_comap_finE hν.1
  have hidx : (K.comap (Lev.finE V)).relIndex ((latLev V).comap (Lev.finE V)) = K.relIndex (latLev V) := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self (latLev_le_range V)]
  have : ((K.comap (Lev.finE V)).subgroupOf ((latLev V).comap (Lev.finE V))).FiniteIndex := ⟨hidx.trans_ne hi⟩
  have h2 := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure (K.comap (Lev.finE V)) ((latLev V).comap (Lev.finE V))
    (Subgroup.comap_mono hK) ho.measurableSet ν
  rw [hidx, h1, mul_one] at h2
  have hn0 : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hi
  have hnt : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have h3 := hπ.measure_toReal hcm.1 (hcm.2 V) hd hc hL (((K.relIndex (latLev V) : ℕ) : ENNReal)⁻¹ • ν)
    (by
      rw [← toLev_latLev, comap_toLev V _ hπ, Measure.smul_apply, ← h2, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hn0 hnt)
    (hν.2.mono (Measure.smul_absolutelyContinuous))
  rw [← h3, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hi)]

end GlobalTheory.VolIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainEqSum
open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory.ClassIntegral

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

def dcoset (Γ K : Subgroup G) (g : G) : Set G := {x | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g * k}

theorem measurableSet_dcoset (Γ K : Subgroup G) [Countable Γ] (hK : MeasurableSet (K : Set G)) (g : G) :
    MeasurableSet (dcoset Γ K g) := by
  have : dcoset Γ K g = ⋃ γ : Γ, (fun y => ((γ : G) * g)⁻¹ * y) ⁻¹' (K : Set G) := by
    ext x
    simp only [dcoset, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, by simpa [mul_assoc] using hk⟩
    · rintro ⟨γ, h⟩
      exact ⟨γ, γ.2, _, h, by group⟩
  rw [this]
  exact MeasurableSet.iUnion fun γ => (measurable_const_mul _) hK

omit [MeasurableSpace G] [MeasurableMul G] in
theorem tsum_indicator_eq (Γ K : Subgroup G) (g x : G) :
    ∑' γ : Γ, ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x) =
      (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * (dcoset Γ K g).indicator 1 x := by
  classical
  by_cases hx : x ∈ dcoset Γ K g
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    obtain ⟨δ, hδ, k, hk, rfl⟩ := hx
    rw [← (Equiv.mulRight (⟨δ, hδ⟩ : Γ)⁻¹).tsum_eq]
    have := tsum_subtype {γ : Γ | g⁻¹ * (γ : G) * g ∈ K} (fun _ => (1 : ENNReal))
    refine Eq.trans ?_ this.symm
    refine tsum_congr fun γ => ?_
    have e : g⁻¹ * ((γ : G) * δ⁻¹ * (δ * g * k)) = g⁻¹ * γ * g * k := by group
    simp only [Set.indicator, Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, Equiv.coe_mulRight,
      Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe, Pi.one_apply, Set.mem_setOf_eq, e,
      K.mul_mem_cancel_right hk]
  · rw [Set.indicator_of_notMem hx, mul_zero, ENNReal.tsum_eq_zero]
    intro γ
    apply Set.indicator_of_notMem
    intro h
    apply hx
    refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, h, ?_⟩
    simp only [Subgroup.smul_def, smul_eq_mul]
    group

theorem measure_dcoset (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1) (g : G) {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * μ.restrict 𝓕 (dcoset Γ K g) = 1 := by
  have i1 : MeasurableConstSMul Γ G :=
    ⟨fun γ => by simpa [Subgroup.smul_def, smul_eq_mul] using measurable_const_mul (γ : G)⟩
  have i2 : SMulInvariantMeasure Γ G μ :=
    ⟨fun γ s _ => by
      have : ((fun x => γ • x) ⁻¹' s) = ((fun x => (γ : G) * x) ⁻¹' s) := by
        ext x; simp [Subgroup.smul_def, smul_eq_mul]
      rw [this, measure_preimage_mul]⟩
  have hT : MeasurableSet ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)) := (measurable_const_mul _) hK
  have hf : Measurable (((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal)) :=
    measurable_one.indicator hT
  have hC := measurableSet_dcoset Γ K hK g
  rw [← lintegral_indicator_one hC, ← lintegral_const_mul _ (measurable_one.indicator hC)]
  simp only [← tsum_indicator_eq]
  have hmeas : ∀ γ : Γ, Measurable fun x : G =>
      ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x) :=
    fun γ => hf.comp (measurable_const_smul γ)
  rw [lintegral_tsum fun γ => (hmeas γ).aemeasurable,
    ← h𝓕.lintegral_eq_tsum'', lintegral_indicator_one hT, measure_preimage_mul, hK1]

theorem tsum_one_mul_eq_one {α : Type} {m : ENNReal} (h : (∑' _ : α, (1 : ENNReal)) * m = 1) :
    m ≠ ⊤ ∧ m.toReal = (Nat.card α : ℝ)⁻¹ := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at h
  have hN0 : (∑' _ : α, (1 : ENNReal)) ≠ 0 := by intro h0; rw [h0] at h; simp at h
  have hN : (∑' _ : α, (1 : ENNReal)) ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.top_mul hm0] at h; simp at h
  have hm : m ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.mul_top hN0] at h; simp at h
  have : Finite α := by
    by_contra hα
    have : Infinite α := not_finite_iff_infinite.mp hα
    exact hN (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero)
  refine ⟨hm, ?_⟩
  have := Fintype.ofFinite α
  rw [tsum_fintype] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_eq_nat_card] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at h'
  exact eq_inv_of_mul_eq_one_right h'

theorem integral_fundamentalDomain_eq_sum : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant], MeasurableSet (K : Set G) → μ K = 1 → ∀ {ι : Type} [Fintype ι] (g : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g i * k) → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, (∀ γ ∈ Γ, ∀ k ∈ K, ∀ x, Φ (γ * x * k) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∑ i, ((Nat.card {γ : Γ // (g i)⁻¹ * (γ : G) * g i ∈ K} : ℂ))⁻¹ * Φ (g i) := by
  intro G _ _ _ Γ K _ μ _ hK hK1 ι _ g hcov 𝓕 h𝓕 Φ hΦ
  have hm := fun i => tsum_one_mul_eq_one (measure_dcoset Γ K μ hK hK1 (g i) h𝓕)
  have hC := fun i => measurableSet_dcoset Γ K hK (g i)
  have hpt : Φ = fun x => ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x := by
    funext x
    obtain ⟨j, hj, huniq⟩ := hcov x
    rw [Finset.sum_eq_single j]
    · rw [Set.indicator_of_mem (s := dcoset Γ K (g j)) hj]
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hj
      exact hΦ γ hγ k hk _
    · intro i _ hij
      have hx : x ∉ dcoset Γ K (g i) := fun h => hij (huniq i h)
      exact Set.indicator_of_notMem hx _
    · intro h; exact absurd (Finset.mem_univ j) h
  have hint : ∀ i, Integrable ((dcoset Γ K (g i)).indicator (fun _ => Φ (g i))) (μ.restrict 𝓕) :=
    fun i => (integrable_indicator_iff (hC i)).mpr (integrableOn_const (hm i).1)
  constructor
  · rw [IntegrableOn, hpt]
    exact MeasureTheory.integrable_finsetSum _ fun i _ => hint i
  · calc ∫ x in 𝓕, Φ x ∂μ
        = ∫ x in 𝓕, ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x ∂μ := by
          conv_lhs => rw [hpt]
      _ = _ := by
          rw [MeasureTheory.integral_finsetSum _ fun i _ => hint i]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_indicator_const _ (hC i), Measure.real, (hm i).2, Complex.real_smul]
          push_cast
          rfl

end GlobalTheory.ClassIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogInvOneSubLeTwoMulAbs
open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory

theorem abs_log_inv_one_sub_le_two_mul_abs (y : ℝ) (hy : |y| ≤ 1 / 2) :
    |Real.log (1 - y)⁻¹| ≤ 2 * |y| := by
  have h1 := le_abs_self y
  have h2 := neg_abs_le y
  have h0 := abs_nonneg y
  have hpos : 0 < 1 - y := by linarith
  rw [abs_le]
  constructor
  · rw [Real.log_inv]
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have h3 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    have h4 : (1 - y)⁻¹ ≤ 1 + 2 * |y| := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith [mul_nonneg h0 (show (0:ℝ) ≤ |y| - y by linarith), mul_nonneg h0 (show (0:ℝ) ≤ 1 / 2 - |y| by linarith)]
    linarith

theorem tprod_inv_one_sub_pos_and_le_exp :
    ∀ {ι : Type} (y : ι → ℝ) (B : ℝ), (∀ a, |y a| ≤ 1 / 2) → Summable (fun a => |y a|) →
      ∑' a, |y a| ≤ B →
      0 < ∏' a, (1 - y a)⁻¹ ∧ ∏' a, (1 - y a)⁻¹ ≤ Real.exp (2 * B) := by
  intro ι y B hy hs hB
  have hb : ∀ a, |Real.log (1 - y a)⁻¹| ≤ 2 * |y a| :=
    fun a => abs_log_inv_one_sub_le_two_mul_abs _ (hy a)
  have hs2 : Summable (fun a => 2 * |y a|) := hs.mul_left 2
  have hsl : Summable (fun a => Real.log (1 - y a)⁻¹) :=
    Summable.of_norm_bounded hs2 (fun a => by simpa only [Real.norm_eq_abs] using hb a)
  have hp := hsl.hasSum.rexp
  have he : (Real.exp ∘ fun a => Real.log (1 - y a)⁻¹) = fun a => (1 - y a)⁻¹ := by
    funext a
    have h1 := le_abs_self (y a)
    have h2 := hy a
    exact Real.exp_log (inv_pos.mpr (by linarith))
  rw [he] at hp
  rw [hp.tprod_eq]
  refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr ?_⟩
  calc ∑' a, Real.log (1 - y a)⁻¹ ≤ ∑' a, 2 * |y a| :=
        hsl.tsum_le_tsum (fun a => (le_abs_self _).trans (hb a)) hs2
    _ = 2 * ∑' a, |y a| := tsum_mul_left
    _ ≤ 2 * B := by linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpNegLeNormTprodOneSubInv
open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory

theorem exp_neg_le_norm_tprod_one_sub_inv {ι : Type} (x : ι → ℂ) (B : ℝ)
    (h : ∀ a, ‖x a‖ ≤ 1 / 2) (hs : Summable (fun a => ‖x a‖)) (hB : ∑' a, ‖x a‖ ≤ B) :
    Real.exp (-B) ≤ ‖∏' a, (1 - x a)⁻¹‖ := by
  have hlow : ∀ a, 1 / 2 ≤ ‖1 - x a‖ := by
    intro a
    have h1 := norm_sub_norm_le (1 : ℂ) (x a)
    rw [norm_one] at h1
    linarith [h a]
  have hne : ∀ a, 1 - x a ≠ 0 := by
    intro a h0
    have := hlow a
    rw [h0, norm_zero] at this
    linarith
  have heq : ∀ a, (1 - x a)⁻¹ = 1 + x a * (1 - x a)⁻¹ := by
    intro a
    have := hne a
    field_simp
    ring
  have hsum : Summable (fun a => ‖x a * (1 - x a)⁻¹‖) := by
    refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_) (hs.mul_right 2)
    rw [norm_mul, norm_inv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [inv_le_comm₀ (by linarith [hlow a]) (by norm_num)]
    linarith [hlow a]
  have hm : Multipliable (fun a => (1 - x a)⁻¹) := by
    have := multipliable_one_add_of_summable hsum
    simpa only [← heq] using this
  have hfac : ∀ a, Real.exp (-‖x a‖) ≤ ‖(1 - x a)⁻¹‖ := by
    intro a
    rw [norm_inv, Real.exp_neg]
    refine inv_anti₀ (by linarith [hlow a]) ?_
    have h1 := norm_sub_le (1 : ℂ) (x a)
    rw [norm_one] at h1
    linarith [Real.add_one_le_exp ‖x a‖]
  have ht := (continuous_norm.tendsto _).comp hm.hasProd
  refine ge_of_tendsto' ht (fun s => ?_)
  have hsle : ∑ a ∈ s, ‖x a‖ ≤ B :=
    (hs.sum_le_tsum s (fun a _ => norm_nonneg _)).trans hB
  calc Real.exp (-B) ≤ Real.exp (∑ a ∈ s, -‖x a‖) := by
        rw [Finset.sum_neg_distrib]
        exact Real.exp_le_exp.2 (neg_le_neg hsle)
    _ = ∏ a ∈ s, Real.exp (-‖x a‖) := Real.exp_sum _ _
    _ ≤ ∏ a ∈ s, ‖(1 - x a)⁻¹‖ :=
        Finset.prod_le_prod₀ (fun a _ => (Real.exp_pos _).le) (fun a _ => hfac a)
    _ = _ := by simp only [Function.comp, norm_prod]

end GlobalTheory
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem norm_char_finite {H : Type} [Group H] [Finite H] (χ : H →* ℂˣ) (x : H) : ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  have h : ((χ x : ℂˣ) : ℂ) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Nat.card_pos.ne'

instance finite_kP (PP : Pl D.host.E) : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot

theorem norm_levFn {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (L : LevDat D.host.E ℂ n) : ‖((levFn β L x : ℂˣ) : ℂ)‖ = 1 := by
  unfold levFn
  simp only [Units.val_mul, Units.coe_prod, norm_mul, norm_prod, norm_char_finite, Finset.prod_const_one, mul_one]
  unfold ext1
  split_ifs
  · exact norm_char_finite _ _
  · simp

theorem isOpen_level (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  classical
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem exists_finLift (V : HSp D) (u : Bridge.Gf V) : ∃ k : GA D V, k ∈ GfC V ∧ (finHom V).rangeRestrict k = u := by
  obtain ⟨_, g, rfl⟩ := u
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V g)
  have hk : k ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩
  exact ⟨⟨k, hk⟩, k1, Subtype.ext k2⟩

def finLift (V : HSp D) (u : Bridge.Gf V) : GA D V := (exists_finLift V u).choose

theorem finLift_mem (V : HSp D) (u : Bridge.Gf V) : finLift V u ∈ GfC V := (exists_finLift V u).choose_spec.1

theorem finLift_spec (V : HSp D) (u : Bridge.Gf V) : (finHom V).rangeRestrict (finLift V u) = u :=
  (exists_finLift V u).choose_spec.2

theorem mem_grpOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : GA D V) :
    (finHom V).rangeRestrict k ∈ grpOf V β L ↔ Lev.finE V k ∈ lev D.sp.cm V.gram β L := Iff.rfl

theorem integral_eq_classSum_of_hom {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableMul G] (π : G →* H)
    (Γ : Subgroup G) [Countable Γ] (J : Subgroup H) (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet ((J.comap π : Subgroup G) : Set G)) (h1 : μ (J.comap π) = 1) {I : Type} [Fintype I] {y : I → H}
    (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (s : I → G) (hs : ∀ j, π (s j) = y j) {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (Φ : G → ℂ) (hΦ : ∀ γ ∈ Γ, ∀ k, π k ∈ J → ∀ x, Φ (γ * x * k) = Φ x) :
    ∫ x in 𝓕, Φ x ∂μ = ∑ j, ((Nat.card (Bridge.stab (π.comp Γ.subtype) J (y j)) : ℂ))⁻¹ * Φ (s j) := by
  have key := (GlobalTheory.ClassIntegral.integral_fundamentalDomain_eq_sum Γ (J.comap π) μ hK h1 s ?_ 𝓕 h𝓕 Φ hΦ).2
  · rw [key]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 3
    refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => ?_)
    rw [Bridge.mem_stab, Subgroup.mem_comap, map_mul, map_mul, map_inv, hs]
    rfl
  · intro x
    refine (existsUnique_congr fun j => ?_).1 (hy (π x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, ((γ : G) * s j)⁻¹ * x, ?_, by group⟩
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, hs, e]
      have : π (γ : G) = (π.comp Γ.subtype) γ := rfl
      rw [this, inv_mul_cancel_left]
      exact k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, ⟨_, hk⟩, by rw [map_mul, map_mul, hs]; rfl⟩

theorem integral_eq_classSum (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V (lev D.sp.cm V.gram β L) ν 𝓕) {I : Type} [Fintype I]
    {y : I → Bridge.Gf V} (hy : Bridge.IsReps (Bridge.ratF V) (grpOf V β L) y) (Φ : GA D V → ℂ)
    (hΦ : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ x, Φ (γ * x * k) = Φ x) :
    ∫ x in 𝓕, Φ x ∂ν =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF V) (grpOf V β L) (y j)) : ℂ))⁻¹ * Φ (finLift V (y j)) := by
  haveI := hν.1.1
  haveI : MeasurableMul (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA _ _
  haveI : BorelSpace (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have e : (grpOf V β L).comap (finHom V).rangeRestrict = (lev D.sp.cm V.gram β L).comap (Lev.finE V) :=
    Subgroup.ext fun k => mem_grpOf V β L k
  refine integral_eq_classSum_of_hom (finHom V).rangeRestrict (GQ V) (grpOf V β L) ν ?_ ?_ hy _
    (fun j => finLift_spec V (y j)) hν.2 Φ fun γ hγ k hk x => hΦ γ hγ k ((mem_grpOf V β L k).1 hk) x
  · rw [e]; exact (isOpen_level V β L).measurableSet
  · rw [e]; exact GlobalTheory.Mass.Levels.measure_comap_finE hν.1

section Schur

variable {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem isMultiplicityInner_of_model (H : HMod (MMap M)) {N : ℂ} (h : ∀ x y, inner ℂ x y = N * ipM M μ 𝓕 (H.e x) (H.e y)) (x y : H.H) :
    IsMultIP M μ 𝓕 (H.e x) (H.e y) (ipM M μ 𝓕 (H.e x) (H.e y)) := by
  have h1 : ∀ x y : H.H, inner ℂ x y ≠ 0 → ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := fun x y hxy => by
    by_contra hc
    apply hxy
    rw [h, ipM, dite_eq_right hc, mul_zero]
  refine ipM_spec _ _ _ _ _ ?_
  by_cases hx : x = 0
  · subst hx
    exact ⟨0, fun v v' => by simp⟩
  by_cases hxy : inner ℂ x y = 0
  · obtain ⟨c, hc⟩ := h1 x (x + y) (by rw [inner_add_right, hxy, add_zero]; exact inner_self_ne_zero.2 hx)
    obtain ⟨c', hc'⟩ := h1 x x (inner_self_ne_zero.2 hx)
    refine ⟨c - c', fun v v' => ?_⟩
    have e : (fun g => star (H.e x v g) * H.e y v' g) =
        fun g => star (H.e x v g) * H.e (x + y) v' g - star (H.e x v g) * H.e x v' g := by
      funext g; simp [mul_add]
    rw [e]
    exact ⟨(hc v v').1.sub (hc' v v').1, by rw [integral_sub (hc v v').1 (hc' v v').1, (hc v v').2, (hc' v v').2, sub_mul]⟩
  · exact h1 x y hxy

end Schur

theorem one_le_weylDimU {p : ℕ} (lam : Fin p → ℤ) (h : ∀ i j, i ≤ j → lam j ≤ lam i) : 1 ≤ weylDimU lam := by
  refine Finset.prod_induction _ (1 ≤ ·) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun i _ => ?_
  refine Finset.prod_induction _ (1 ≤ ·) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.1 hj).2
  have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
  have h2 : (0 : ℚ) ≤ ((lam i - lam j : ℤ) : ℚ) := by exact_mod_cast sub_nonneg.2 (h i j hij.le)
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem sig_add (i : Fin D.R.m) (ρ : D.what₂.Tau) : pW D i ρ + qW D i ρ = D.R.r := by
  have := D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D ρ)
  have h1 := D.R.m_add_three_le_k
  have h2 := i.2
  unfold pW qW
  rw [this]
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem one_le_dimK (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : 1 ≤ dimK _ _ (kapAt (Wc D i) σ ρ) := by
  have h := Formalism.L2.NTheta.holOK_kapW (D.hc (lab σ ρ)) _ _ (sig_add i ρ)
  exact one_le_mul_of_one_le_of_one_le (one_le_weylDimU _ h.1) (one_le_weylDimU _ h.2.1)

theorem hookOf_pos (n : ℕ) (a : ℕ → ℕ) : 0 < hookOf n a := by
  refine Finset.prod_pos fun x hx => ?_
  have hx' := (YoungDiagram.mem_cells _).1 hx
  have h1 := YoungDiagram.mem_iff_lt_rowLen.1 (show (x.1, x.2) ∈ _ from hx')
  have h2 := YoungDiagram.mem_iff_lt_colLen.1 (show (x.1, x.2) ∈ _ from hx')
  omega

theorem sigmaFinite_haar {p q : ℕ} (m : Measure (UpqT p q)) (hm : m.IsHaarMeasure) : SigmaFinite m := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  infer_instance

theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℕ) := by
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := fun h => w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have : 2 ≤ Ideal.absNorm w.asIdeal := by omega
  exact_mod_cast this

theorem sum_bound {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K) → Prop) {κ : Type} [Fintype κ]
    (u : {w // p w} × κ → ℝ) (h0 : ∀ a, 0 ≤ u a) (h : ∀ a, u a ≤ (((Ideal.absNorm a.1.1.asIdeal : ℕ) : ℝ) ^ 2)⁻¹) :
    (∀ a, u a ≤ 1 / 2) ∧ Summable u ∧ ∑' a, u a ≤ Fintype.card κ * (Module.finrank ℚ K : ℝ) := by
  obtain ⟨hs, hb⟩ := GlobalTheory.PrimeSquareSum.summable_absNorm_inv_sq K
  set N : HeightOneSpectrum (𝓞 K) → ℝ := fun w => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹
  have hN : ∀ w, 0 ≤ N w := fun w => by positivity
  have hs1 : Summable fun w : {w // p w} => N w.1 := hs.subtype _
  have hb1 : ∑' w : {w // p w}, N w.1 ≤ (Module.finrank ℚ K : ℝ) := (Summable.tsum_subtype_le N _ hN hs).trans hb
  have hs2 : Summable fun a : {w // p w} × κ => N a.1.1 :=
    (summable_prod_of_nonneg fun a => hN _).2 ⟨fun _ => Summable.of_finite, by
      simpa [tsum_fintype] using hs1.mul_left (Fintype.card κ : ℝ)⟩
  have hs3 : Summable u := Summable.of_nonneg_of_le h0 h hs2
  refine ⟨fun a => (h a).trans ?_, hs3, (hs3.tsum_le_tsum h hs2).trans ?_⟩
  · have := two_le_absNorm a.1.1
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith)
  · rw [hs2.tsum_prod]
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb1 (Nat.cast_nonneg _)

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

theorem finrank_F_le (D : D7) : Module.finrank ℚ D.host.F ≤ 2 * D.R.f := by
  rw [← finrank_E]
  exact LinearMap.finrank_le_finrank_of_injective (f := (IsScalarTower.toAlgHom ℚ D.host.F D.host.E).toLinearMap)
    (algebraMap D.host.F D.host.E).injective

theorem eulerOff_lower (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ)
    (hx : ∀ w a, ‖x w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2)) :
    Real.exp (-(D.R.r * (2 * D.R.f))) ≤ ‖eulerOff D S x‖ := by
  obtain ⟨h1, h2, h3⟩ := sum_bound (OffS D S) (κ := Fin D.R.r) (fun a => ‖x a.1.1 a.2‖) (fun _ => norm_nonneg _) fun a => by
    refine (hx _ _).trans ?_
    have ht : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast D.R.rank_add_five_le
    have := two_le_absNorm a.1.1
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  rw [finrank_E, Fintype.card_fin] at h3
  exact GlobalTheory.exp_neg_le_norm_tprod_one_sub_inv _ _ h1 h2 (by exact_mod_cast h3)

theorem abs_quadTerm_le (v : HeightOneSpectrum (𝓞 D.host.F)) {i : ℕ} (hi : 2 ≤ i) :
    |quadTerm D v i| ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ := by
  have h := two_le_absNorm v
  have hs : |quadSign D v| = 1 := by unfold quadSign; split_ifs <;> simp
  rw [quadTerm, abs_div, abs_pow, hs, one_pow, one_div, abs_of_pos (by positivity)]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) hi)

theorem quad_bound (p : HeightOneSpectrum (𝓞 D.host.F) → Prop) :
    0 < ∏' a : {v // p v} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D a.1.1 a.2.1)⁻¹ ∧
      ∏' a : {v // p v} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D a.1.1 a.2.1)⁻¹ ≤ Real.exp (2 * (D.R.r * (2 * D.R.f))) := by
  obtain ⟨h1, h2, h3⟩ := sum_bound p (κ := Finset.Ioc D.R.t D.R.nV) (fun a => |quadTerm D a.1.1 a.2.1|)
    (fun _ => abs_nonneg _) fun a => abs_quadTerm_le _ (by
      have := (Finset.mem_Ioc.1 a.2.2).1
      have := D.R.rank_add_five_le
      omega)
  refine GlobalTheory.tprod_inv_one_sub_pos_and_le_exp _ _ h1 h2 (h3.trans ?_)
  rw [Fintype.card_coe, Nat.card_Ioc, show D.R.nV - D.R.t = D.R.r by unfold Ranks.nV; omega]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast finrank_F_le D) (Nat.cast_nonneg _)

theorem dOff_bound (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    0 < dOff D S ∧ dOff D S ≤ Real.exp (2 * (D.R.r * (2 * D.R.f))) := quad_bound _

theorem dLoc_bound (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    0 < ∏ v ∈ S, dLoc D v ∧ ∏ v ∈ S, dLoc D v ≤ Real.exp (2 * (D.R.r * (2 * D.R.f))) := by
  have h := quad_bound (D := D) (· ∈ S)
  have e : ∏' a : {v // v ∈ S} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D a.1.1 a.2.1)⁻¹ = ∏ v ∈ S, dLoc D v := by
    rw [tprod_fintype, Fintype.prod_prod_type, ← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => Finset.prod_coe_sort (Finset.Ioc D.R.t D.R.nV) fun i => (1 - quadTerm D v i)⁻¹
  rwa [e] at h

section Smooth

open Formalism.QuantumDeterminants

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}

theorem exp_mem_UH {X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) (hX : Xᴴ * G + G * X = 0) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UH G := by
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : (t • X)ᴴ = G * (-(t • X)) * G⁻¹ := by
    have h2 : Xᴴ = G * (-X) * G⁻¹ := by
      rw [Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
        Matrix.mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * G * NormedSpace.exp (t • X) = G
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hG, Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp (t • X)).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  rw [Matrix.mul_assoc (G * _), Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem prod_mem_UH (l : List (Matrix (Fin n) (Fin n) ℂ)) (h : ∀ g ∈ l, g ∈ UH G) : l.prod ∈ UH G := by
  induction l with
  | nil => show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G; simp
  | cons a l ih =>
    have ha : aᴴ * G * a = G := h a (by simp)
    have hl : l.prodᴴ * G * l.prod = G := ih fun g hg => h g (by simp [hg])
    show (a * l.prod)ᴴ * G * (a * l.prod) = G
    calc (a * l.prod)ᴴ * G * (a * l.prod) = l.prodᴴ * (aᴴ * G * a) * l.prod := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [ha, hl]

theorem conj_mem_lie {g X : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit g) (h : gᴴ * G * g = G) (hX' : Xᴴ * G + G * X = 0) :
    (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = 0 := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  calc (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = gᴴ * Xᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * X * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * G + G * X) * g := by rw [h1, h2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX']; simp

theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

theorem smoothVec_rep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsUnit G) (hπ : ∀ a ∈ UH G, ∀ b ∈ UH G, ∀ w, π (a * b) w = π a (π b w)) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} π w) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) :
    SmoothVec {X | Xᴴ * G + G * X = 0} π (π g w) := by
  intro k Xs hXs
  have hg' : gᴴ * G * g = G := hg
  have hu : IsUnit g := isUnit_of_mul_isUnit_right (hg'.symm ▸ hG : IsUnit (gᴴ * G * g))
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * G + G * X = 0} := fun i => conj_mem_lie hu hg' (hXs i)
  have hP : ∀ (Ys : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Ys i ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * G + G * X = 0}) →
      ∀ t : Fin k → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • Ys i)).prod ∈ UH G := fun Ys hYs t =>
    prod_mem_UH _ fun g hg => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact exp_mem_UH hG (hYs i) _
  have hc : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := fun X t => by
    rw [← Matrix.exp_conj' _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
  have h1 := ((π g).restrictScalars ℝ).contDiff.comp (hw k _ hY)
  convert h1 using 2 with t
  show _ = π g _
  rw [← hπ _ (hP _ hXs t) _ hg, ← hπ _ hg _ (hP _ hY t), ← prod_conj hu, List.map_ofFn]
  simp only [hc, Function.comp_def]

theorem conj_mem_UJ {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) : P * g * P⁻¹ ∈ UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hg' : gᴴ * G * g = G := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [h, hg', ← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem rep_mem_sm {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ UH (gramAt D V τ)) (w : M.H τ) (hw : w ∈ M.sm τ) :
    M.rep τ g w ∈ M.sm τ := by
  have hP := M.fr_unit τ
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self _))).mul hP
  have hπ : ∀ a ∈ UH (gramAt D V τ), ∀ b ∈ UH (gramAt D V τ), ∀ w, M.rep τ (a * b) w = M.rep τ a (M.rep τ b w) := by
    intro a ha b hb w
    have h := (M.ds τ).2.2.1.1.2 _ (conj_mem_UJ hP (M.fr_gram τ) ha) _ (conj_mem_UJ hP (M.fr_gram τ) hb)
    have e : M.fr τ * a * (M.fr τ)⁻¹ * (M.fr τ * b * (M.fr τ)⁻¹) = M.fr τ * (a * b) * (M.fr τ)⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (M.fr τ)⁻¹, nonsing_inv_mul _ hd, Matrix.one_mul]
    unfold DSModel.rep
    rw [← e, h]
    rfl
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (smoothVec_rep hG hπ hx hg)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end Smooth

theorem HMod_mem {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ} (h : M.Is V ip)
    (x : M.H) : M.e x ∈ V := h.2.1.le (LinearMap.mem_range_self _ x)

theorem HMod_onto {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ} (h : M.Is V ip)
    {z : X} (hz : z ∈ V) : ∃ x, M.e x = z := h.2.1.ge hz

end GlobalTheory.AdelicScalar

end
