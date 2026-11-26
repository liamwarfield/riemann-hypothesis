module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Rowsex
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory

namespace PositivityTheory.Rg.BcB.E2.P

theorem rowsex : KerBasic → VecEx → VecNorm → VecInner → RowsEx := by
  intro hK hE hN hI X ι _ Φ T hΦ hT
  have hΨ : ∀ i j, Tst ((fun i j => adj (Φ j i)) i j : X.G → ℂ) := fun i j => (hK X (Φ j i) (hΦ j i)).2.2.2.1
  obtain ⟨k', hc, hv⟩ := hE X ι (fun i j => adj (Φ j i)) hΨ
  obtain ⟨C, Ω, hC, hΩ, hb⟩ := hN X ι (fun i j => adj (Φ j i)) hΨ
  refine ⟨fun i x => k' x i, ⟨hc, ?_, ?_, ⟨C, Ω, hC, hΩ, fun i x => hb x i _ (hv x i)⟩⟩⟩
  · intro i γ hγ x
    refine PiLp.ext fun l => Lp.ext ?_
    filter_upwards [hv (γ * x) i l, hv x i l] with z h1 h2
    rw [h1, h2]
    exact ((hK X _ (hΨ l i)).2.2.1 γ hγ z x).2
  · intro u i
    filter_upwards [hT u i] with x hx
    rw [hx]
    exact ((hI X ι Φ x i (k' x i) u hΦ).2 (hv x i)).symm

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Tonelli
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P.Tonelli

theorem enorm_sq {S : Type} [MeasurableSpace S] {ν : Measure S} (g : Lp ℂ 2 ν) :
    ‖g‖ₑ ^ 2 = ∫⁻ s, ‖(g : S → ℂ) s‖ₑ ^ 2 ∂ν := by
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  · norm_num
  · exact Lp.aestronglyMeasurable g

end PositivityTheory.Rg.BcB.E2.P.Tonelli

namespace PositivityTheory.Rg.BcB.E2.P

theorem tonelli : Tonelli := by
  intro Y S _ _ m _ ν _ F f W hf hW hfin
  have hmeas : Measurable (Function.uncurry fun y s => W y * ‖f y s‖ₑ ^ 2) :=
    (hW.comp measurable_fst).mul (hf.1.enorm.pow_const 2)
  refine ae_lt_top hmeas.lintegral_prod_left' ?_
  rw [← lintegral_lintegral_swap hmeas.aemeasurable]
  refine ne_of_eq_of_ne (lintegral_congr fun y => ?_) hfin
  have hy : Measurable fun s => f y s := hf.1.comp measurable_prodMk_left
  rw [lintegral_const_mul _ (hy.enorm.pow_const 2), Tonelli.enorm_sq]
  congr 1
  exact lintegral_congr_ae ((hf.2 y).mono fun s hs => by simp only [hs])

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Aeeq
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

open MeasureTheory
open scoped Pointwise

theorem aeeq : AeEq := by
  intro X u u' hu hu' hi hi' hae
  have : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  have : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set A : Set X.G := {x | u x ≠ u' x} with hA
  have hAo : IsOpen A := isOpen_ne_fun hu hu'
  have hAF : X.μ (A ∩ X.F) = 0 := by
    have h1 : X.ν A = 0 := ae_iff.1 hae
    rw [Ctx.ν, Measure.restrict_apply hAo.measurableSet] at h1
    exact h1
  have hinv : ∀ γ : X.Γ, γ • A = A := by
    intro γ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show u (((γ⁻¹ : X.Γ) : X.G) * x) ≠ u' (((γ⁻¹ : X.Γ) : X.G) * x) ↔ u x ≠ u' x
    rw [hi _ (γ⁻¹).2, hi' _ (γ⁻¹).2]
  have hμA : X.μ A = 0 := X.fd.measure_zero_of_invariant A hinv hAF
  have hAe : A = ∅ := (hAo.measure_eq_zero_iff X.μ).1 hμA
  funext x
  by_contra h
  have hx : x ∈ A := h
  rw [hAe] at hx
  exact hx

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Unfold
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory

namespace PositivityTheory.Rg.BcB.E2.P.Unfold

theorem unfolded (hk : KerBasic) (X : Ctx) (φ u : X.G → ℂ) (hφ : Tst φ) (hu : Continuous u)
    (hinv : ∀ γ ∈ X.Γ, ∀ x, u (γ * x) = u x) (x : X.G) :
    ∫ y, ker X.Γ φ x y * u y ∂X.ν = ∫ y, φ y * u (x * y) ∂X.μ := by
  have : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  have : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set g : X.G → ℂ := fun z => φ (x⁻¹ * z) * u z with hg
  have hgc : Continuous g := (hφ.1.comp (continuous_const.mul continuous_id)).mul hu
  have hgs : HasCompactSupport g :=
    HasCompactSupport.mul_right (hφ.2.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hgi : Integrable g X.μ := hgc.integrable_of_hasCompactSupport hgs
  have hpt : ∀ z, ker X.Γ φ x z * u z = ∑' γ : X.Γ, g (γ • z) := by
    intro z
    have h1 : ∀ γ : X.Γ, g (γ • z) = φ (x⁻¹ * (γ : X.G) * z) * u z := by
      intro γ
      have h2 : γ • z = (γ : X.G) * z := rfl
      simp only [hg, h2, hinv γ γ.2 z, mul_assoc]
    simp only [h1]
    rw [tsum_mul_right, ker, tsum_eq_finsum ((hk X φ hφ).1 x z)]
  have hmeas : ∀ γ : X.Γ, Continuous fun z => g (γ • z) := fun γ =>
    hgc.comp (continuous_const.mul continuous_id)
  have hfin : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν ≠ ⊤ := by
    have h3 : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν = ∫⁻ z, ‖g z‖ₑ ∂X.μ :=
      (X.fd.lintegral_eq_tsum'' fun z => ‖g z‖ₑ).symm
    rw [h3]
    exact hgi.2.ne
  simp only [hpt]
  rw [integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) hfin]
  refine (X.fd.integral_eq_tsum'' g hgi).symm.trans ?_
  rw [← integral_mul_left_eq_self g x]
  simp [hg]

end PositivityTheory.Rg.BcB.E2.P.Unfold

namespace PositivityTheory.Rg.BcB.E2.P

theorem unfold : KerBasic → ConvCont → Unfold := by
  intro hk hc X φ u hφ hu hinv
  exact ⟨fun x => Unfold.unfolded hk X φ u hφ hu hinv x, hc X φ u hφ hu.locallyIntegrable⟩

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Locint
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.E2.P

namespace Locint

theorem enorm_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm
      _ ≤ 1 + x ^ 2 := le_add_self

end Locint

theorem locint : Tonelli → LocInt := by
  intro hT X S _ ν _ F f hF hrep
  let K := CompactExhaustion.choice X.G
  have hfin : ∀ n, ∀ᵐ s ∂ν, ∫⁻ y, (K n).indicator 1 y * ‖f y s‖ₑ ^ 2 ∂X.μ < ⊤ := by
    intro n
    have hK : IsCompact (K n) := K.isCompact n
    have hW : Measurable ((K n).indicator (1 : X.G → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
    apply hT X.G S X.μ ν F f _ hrep hW
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
    refine ne_top_of_le_ne_top (b := ∫⁻ y, (K n).indicator (fun _ => ENNReal.ofReal C ^ 2) y ∂X.μ) ?_ ?_
    · rw [lintegral_indicator_const hK.measurableSet]
      exact ENNReal.mul_ne_top (by simp) hK.measure_lt_top.ne
    · refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ K n
      · simp only [Set.indicator_of_mem hy, Pi.one_apply, one_mul]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC y hy)
      · simp [Set.indicator_of_notMem hy]
  rw [← ae_all_iff] at hfin
  filter_upwards [hfin] with s hs
  have hm : Measurable fun y => f y s := hrep.1.of_uncurry_right
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hk
  refine IntegrableOn.mono_set ?_ hn
  have hKn : IsCompact (K n) := K.isCompact n
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have heq : (fun y => (K n).indicator 1 y * ‖f y s‖ₑ ^ 2) = (K n).indicator (fun y => ‖f y s‖ₑ ^ 2) := by
    ext y; by_cases hy : y ∈ K n <;> simp [hy]
  have h2 := hs n
  rw [heq, lintegral_indicator hKn.measurableSet] at h2
  show ∫⁻ y, ‖f y s‖ₑ ∂(X.μ.restrict (K n)) < ⊤
  calc ∫⁻ y, ‖f y s‖ₑ ∂(X.μ.restrict (K n)) ≤ ∫⁻ y, (1 + ‖f y s‖ₑ ^ 2) ∂(X.μ.restrict (K n)) :=
        lintegral_mono fun y => Locint.enorm_le_one_add_sq _
    _ = X.μ (K n) + ∫⁻ y, ‖f y s‖ₑ ^ 2 ∂(X.μ.restrict (K n)) := by
        rw [lintegral_add_left measurable_const]; simp
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hKn.measure_lt_top, h2⟩

end PositivityTheory.Rg.BcB.E2.P

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Imports
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

theorem point : Point := by
  unfold PositivityTheory.Rg.BcB.E2.Point
  intro B _ _ _ _ S _ _ e p hp
  by_contra hne
  push Not at hne
  choose b hb using hne
  let c : S → B := fun s => b s - algebraMap ℂ B (p (b s))
  have hpc : ∀ s, p (c s) = 0 := fun s => by
    simp only [c, map_sub]
    rw [AlgHomClass.commutes]
    simp
  have hec : ∀ s, e (c s) s ≠ 0 := fun s => by
    have h1 : e (c s) s = e (b s) s - p (b s) := by
      simp only [c, map_sub, ContinuousMap.sub_apply]
      rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, smul_eq_mul, mul_one]
    rw [h1]
    exact sub_ne_zero.2 (hb s)
  let g : S → B := fun s => star (c s) * c s
  have hpg : ∀ s, p (g s) = 0 := fun s => by simp [g, hpc]
  have heg : ∀ s t, e (g s) t = ((‖e (c s) t‖ ^ 2 : ℝ) : ℂ) := fun s t => by
    simp only [g, map_mul, map_star, ContinuousMap.mul_apply, ContinuousMap.star_apply]
    rw [Complex.ofReal_pow]
    exact Complex.conj_mul' _
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun s => {t : S | e (c s) t ≠ 0})
    (fun s => isOpen_compl_singleton.preimage (e (c s)).continuous)
    (fun t _ => Set.mem_iUnion.2 ⟨t, hec t⟩)
  let G : B := ∑ s ∈ F, g s
  let v : S → ℝ := fun t => ∑ s ∈ F, ‖e (c s) t‖ ^ 2
  have hpG : p G = 0 := by simp [G, hpg]
  have heG : ∀ t, e G t = (v t : ℂ) := fun t => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, v, map_sum, ContinuousMap.sum_apply, heg]
    push_cast
    rfl
  have hv : ∀ t, 0 < v t := fun t => by
    obtain ⟨s, hsF, hs⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ t))
    have hs' : e (c s) t ≠ 0 := hs
    exact Finset.sum_pos' (fun i _ => by positivity) ⟨s, hsF, pow_pos (norm_pos_iff.2 hs') 2⟩
  have hvM : ∀ t, v t ≤ ‖e G‖ := fun t => by
    have h1 := ContinuousMap.norm_coe_le_norm (e G) t
    rw [heG, Complex.norm_real, Real.norm_of_nonneg (hv t).le] at h1
    exact h1
  have hM : 0 ≤ ‖e G‖ := norm_nonneg _
  have key := hp (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G)
  have hp1 : p (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G) = 1 := by simp [hpG]
  rw [hp1, norm_one] at key
  have hlt : ‖e (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G)‖ < 1 := by
    rw [ContinuousMap.norm_lt_iff _ one_pos]
    intro t
    have ht : e (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G) t = ((1 - v t / (‖e G‖ + 1) : ℝ) : ℂ) := by
      simp only [map_sub, map_one, map_smul, ContinuousMap.sub_apply, ContinuousMap.one_apply,
        ContinuousMap.smul_apply, heG, smul_eq_mul]
      push_cast
      ring
    rw [ht, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    have h2 : v t / (‖e G‖ + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith [hvM t]
    have h3 : 0 < v t / (‖e G‖ + 1) := div_pos (hv t) (by linarith)
    constructor <;> linarith
  linarith

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.MulLeWeightedSquares
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Fdata

lemma mul_le_weighted_squares (a b W : ℝ≥0∞) (h0 : W ≠ 0) (ht : W ≠ ⊤) : a * b ≤ W⁻¹ * a ^ 2 + W * b ^ 2 := by
  rcases le_or_gt a (W * b) with h | h
  · calc a * b ≤ W * b * b := by gcongr
      _ = W * b ^ 2 := by rw [pow_two, mul_assoc]
      _ ≤ _ := le_add_self
  · have hb : b ≤ W⁻¹ * a := by
      calc b = W⁻¹ * (W * b) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
        _ ≤ W⁻¹ * a := by gcongr
    calc a * b ≤ a * (W⁻¹ * a) := by gcongr
      _ = W⁻¹ * a ^ 2 := by ring
      _ ≤ _ := le_self_add

end Fdata

theorem fdata : RowsEx → RowsEig → FData := by
  intro hRx hRe X ι _ K _ _ _ J B _ _ _ _ R a₀ Φ g W S _ ν _ χ V hJ hΦ hT hS hne hW hW' hWc hg hg'
  obtain ⟨T₁, hT₁, hT₁J⟩ := hT 1
  obtain ⟨k, hk⟩ := hRx X ι (Φ 1) T₁ (hΦ 1) hT₁
  set L : Lp ℂ 2 ν →L[ℂ] X.Hs ι := J.comp V with hL
  have hLn : ∀ h, ‖L h‖ = ‖h‖ := fun h => (hJ _).trans (hS.iso h)
  have hL1 : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by rw [hLn, one_mul]
  set A := ContinuousLinearMap.adjoint L with hA
  have hAn : ∀ v, ‖A v‖ ≤ ‖v‖ := fun v => by
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      _ ≤ 1 * ‖v‖ := by
          gcongr
          rw [hA, LinearIsometryEquiv.norm_map]
          exact hL1
      _ = ‖v‖ := one_mul _
  have hAe : ∀ v, ‖A v‖ₑ ≤ ‖v‖ₑ := fun v => by
    rw [← ofReal_norm, ← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hAn v)
  have hin : ∀ v h, inner ℂ (A v) h = inner ℂ v (L h) := fun v h =>
    ContinuousLinearMap.adjoint_inner_left L h v
  have hT1L : ∀ h, T₁ (L h) = J (R a₀ (V h)) := fun h => by
    show T₁ (J (V h)) = _
    rw [hT₁J, one_mul]
  have hmem : ∀ b (h : Lp ℂ 2 ν), MemLp (fun s => χ s b * h s) 2 ν := fun b h =>
    MemLp.of_le_mul (c := ‖R b‖) (Lp.memLp h)
      ((hS.meas b).aestronglyMeasurable.mul (Lp.aestronglyMeasurable h))
      (Filter.Eventually.of_forall fun s => by rw [norm_mul]; gcongr; exact hS.bdd b s)
  have hwt : ∀ i, ∫⁻ x, W x * ‖A (k i x)‖ₑ ^ 2 ∂X.ν ≠ ⊤ := by
    intro i
    obtain ⟨C, Ω, hC, hΩ, hkC⟩ := hk.norm
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (hWc Ω hΩ)) ?_
    rw [← lintegral_const_mul' _ _ hC]
    refine lintegral_mono fun x => ?_
    calc W x * ‖A (k i x)‖ₑ ^ 2 ≤ W x * ‖k i x‖ₑ ^ 2 := by gcongr; exact hAe _
      _ ≤ W x * (C * cnt X.Γ Ω x) := by gcongr; exact hkC i x
      _ = C * (W x * cnt X.Γ Ω x) := by ring
  refine ⟨fun i x => A (k i x), ?_⟩
  refine ⟨fun i => A.continuous.comp (hk.cont i), fun i γ hγ x => by simp only [hk.inv i γ hγ x], ?_, hwt, ?_, ?_, ?_⟩
  ·
    intro hF0
    have hA0 : ∀ i x, A (k i x) = 0 := fun i x => congrFun (congrFun hF0 i) x
    have h0 : ∀ h, T₁ (L h) = 0 := fun h => by
      refine PiLp.ext fun i => ?_
      rw [PiLp.zero_apply]
      refine Lp.ext ?_
      filter_upwards [hk.rep (L h) i, Lp.coeFn_zero ℂ 2 X.ν] with x h1 h2
      rw [h1, h2, ← hin, hA0, inner_zero_left]
      rfl
    set h1 : Lp ℂ 2 ν := (memLp_const (1 : ℂ)).toLp _ with hh1
    set h' : Lp ℂ 2 ν := (hmem a₀ h1).toLp _ with hh'
    have hV : V h' = R a₀ (V h1) := hS.mul _ h1 _ (MemLp.coeFn_toLp _)
    have hJ0 : J (V h') = 0 := by rw [hV, ← hT1L, h0]
    have hn : ‖h'‖ = 0 := by rw [← hS.iso, ← hJ, hJ0, norm_zero]
    have hz : h' = 0 := norm_eq_zero.1 hn
    have hae : ∀ᵐ s ∂ν, False := by
      filter_upwards [hne, MemLp.coeFn_toLp (hmem a₀ h1), MemLp.coeFn_toLp (memLp_const (1 : ℂ) (μ := ν) (p := 2)),
        Lp.coeFn_zero ℂ 2 ν] with s hs e1 e2 e3
      apply hs
      have : (h' : S → ℂ) s = 0 := by rw [hz, e3]; rfl
      rw [hh', e1, hh1, e2] at this
      simpa using this
    exact hS.ne (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hae))
  ·
    intro c x i h
    set h' : Lp ℂ 2 ν := (hmem (c * a₀) h).toLp _ with hh'
    have hV : V h' = R (c * a₀) (V h) := hS.mul _ h _ (MemLp.coeFn_toLp _)
    obtain ⟨Tc, hTc, hTcJ⟩ := hT c
    have key : Tc (T₁ (L h)) = T₁ (L h') := by
      rw [hT1L, hT1L, hTcJ, hV]
      congr 1
      show (R (c * a₀) * R a₀) (V h) = (R a₀ * R (c * a₀)) (V h)
      rw [← map_mul, ← map_mul, mul_comm]
    have e := hRe X ι (Φ c) Tc T₁ k (L h) (L h') (hΦ c) hTc hk key x i
    simp only [hin]
    rw [e, ← hin, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (hmem (c * a₀) h)] with s hs
    rw [hs, RCLike.inner_apply']
    ring
  ·
    intro n i
    have hgm : AEStronglyMeasurable (fun x => (g n i : X.G → ℂ) x) X.ν := Lp.aestronglyMeasurable _
    refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hgm, ?_⟩
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hg' n i, hwt i⟩) ?_
    have hm : AEMeasurable (fun x => (W x)⁻¹ * ‖(g n i : X.G → ℂ) x‖ₑ ^ 2) X.ν :=
      hW.inv.aemeasurable.mul (hgm.enorm.pow_const 2)
    rw [← lintegral_add_left' hm]
    refine lintegral_mono fun x => ?_
    rw [RCLike.enorm_conj]
    exact Fdata.mul_le_weighted_squares _ _ _ (hW' x).1 (hW' x).2
  ·
    intro n h
    have e : ∀ i, ∫ x, conj ((g n i : X.G → ℂ) x) * inner ℂ (A (k i x)) h ∂X.ν = inner ℂ (g n i) (T₁ (L h) i) := by
      intro i
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hk.rep (L h) i] with x hx
      rw [hx, hin, RCLike.inner_apply']
    simp only [e]
    rw [← PiLp.inner_apply, hT1L]
    exact inner_eq_zero_symm.1 (hg n _)

end PositivityTheory.Rg.BcB.E2.P
end
