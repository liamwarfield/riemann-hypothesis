module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormula

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationHaarBase
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationHaarBase
open MeasureTheory Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreShift

theorem comp_shift_props {V : Type} [TopologicalSpace V] [T2Space V] {W : Set V} (hW : IsOpen W)
    {T T' : V → V} (hT : ContinuousOn T W) (hT' : ContinuousOn T' W)
    (hmem : ∀ v, T v ∈ W ↔ v ∈ W) (hmem' : ∀ v, T' v ∈ W ↔ v ∈ W)
    (hinv : ∀ v ∈ W, T' (T v) = v) {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ W) :
    Continuous (fun v => φ (T v)) ∧ HasCompactSupport (fun v => φ (T v)) ∧
      tsupport (fun v => φ (T v)) ⊆ W := by
  have hC : IsCompact (T' '' tsupport φ) := hc.isCompact.image_of_continuousOn (hT'.mono hs)
  have hCW : T' '' tsupport φ ⊆ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hmem' w).2 (hs hw)
  have hsup : ∀ v, v ∉ T' '' tsupport φ → φ (T v) = 0 := by
    intro v hv
    by_contra h
    have h1 : T v ∈ tsupport φ := subset_tsupport _ h
    exact hv ⟨T v, h1, hinv v ((hmem v).1 (hs h1))⟩
  have hts : tsupport (fun v => φ (T v)) ⊆ T' '' tsupport φ := by
    refine closure_minimal ?_ hC.isClosed
    intro v hv
    by_contra h
    exact hv (hsup v h)
  refine ⟨continuous_of_tsupport fun v hv => ?_, HasCompactSupport.intro hC hsup, hts.trans hCW⟩
  exact ContinuousAt.comp (g := φ) hφ.continuousAt (hT.continuousAt (hW.mem_nhds (hCW (hts hv))))

theorem continuous_lintegral {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y}
    {ι : X → Y} {U : Set V} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) {φ : V → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (h0 : ∀ v, 0 ≤ φ v) :
    Continuous fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by
  obtain ⟨hi, hc1⟩ := h.2.2 φ hφ hc hs
  have hcont : Continuous fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
    ENNReal.continuous_ofReal.comp (continuousOn_univ.1 hc1)
  exact hcont.congr fun b =>
    ofReal_integral_eq_lintegral_ofReal (hi b (Set.mem_univ b)) (Filter.Eventually.of_forall h0)

theorem setLIntegral_eq_lintegral {V : Type} [MeasurableSpace V] {μ : Measure V} {W : Set V}
    (hW : MeasurableSet W) {a : V → ℝ≥0∞} (ha : ∀ v, v ∉ W → a v = 0) :
    ∫⁻ v in W, a v ∂μ = ∫⁻ v, a v ∂μ := by
  rw [← lintegral_indicator hW]
  congr 1
  funext v
  by_cases hv : v ∈ W
  · rw [Set.indicator_of_mem hv]
  · rw [Set.indicator_of_notMem hv, ha v hv]

theorem lintegral_shift {V X Y : Type} [TopologicalSpace V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure V} {ν : Measure X} [ν.IsAddHaarMeasure] {f : V → Y} {g : V → X}
    {ι : X → Y} (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {U W : Set V} (hW : IsOpen W) (hWU : W ⊆ U) {fib : X → Measure V}
    (hF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) {T : X → V → V}
    (hTm : ∀ s, Measurable (T s)) (hTμ : ∀ s, μ.map (T s) = μ)
    (hTc : ∀ s, ContinuousOn (T s) W) (hTW : ∀ s v, T s v ∈ W ↔ v ∈ W)
    (hinv : ∀ s, ∀ v ∈ W, T (-s) (T s v) = v) (hgT : ∀ s, ∀ v ∈ W, g (T s v) = g v + s)
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ W)
    (h0 : ∀ v, 0 ≤ φ v) (s c : X) :
    ∫⁻ v, ENNReal.ofReal (φ (T s v)) ∂(fib c) = ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib (c + s)) := by
  obtain ⟨hφs, hcs, hss⟩ :=
    comp_shift_props hW (hTc s) (hTc (-s)) (hTW s) (hTW (-s)) (hinv s) hφ hc hs
  have hψm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hψ0 : ∀ v, v ∉ W → ENNReal.ofReal (φ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]
  have hψs0 : ∀ v, v ∉ W → ENNReal.ofReal (φ (T s v)) = 0 :=
    fun v hv => hψ0 _ fun h => hv ((hTW s v).1 h)
  have hD := continuous_lintegral hF hφ hc (hs.trans hWU) h0
  have hD' := continuous_lintegral hF hφs hcs (hss.trans hWU) (fun v => h0 _)
  have hDs : Continuous fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib (b + s)) :=
    hD.comp (continuous_add_const s)
  refine GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts X ν Set.univ isOpen_univ _ _ hD'.continuousOn hDs.continuousOn
    (fun S hS _ => ?_) c (Set.mem_univ c)
  have hSm := hS.measurableSet
  have hS'm : MeasurableSet ((fun x : X => x - s) ⁻¹' S) :=
    (continuous_sub_right s).measurable hSm
  have e1 := GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage hι hg hf hW hWU hF
    (fun v => ENNReal.ofReal (φ (T s v))) (hψm.comp (hTm s)) hψs0 S hSm
  have e2 := GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage hι hg hf hW hWU hF
    (fun v => ENNReal.ofReal (φ v)) hψm hψ0 _ hS'm
  have hAm : Measurable ((g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
      fun v => ENNReal.ofReal (φ v)) := hψm.indicator (hg.measurable hS'm)
  have hA0 : ∀ v, v ∉ W → (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
      (fun v => ENNReal.ofReal (φ v)) v = 0 :=
    fun v hv => Set.indicator_apply_eq_zero.2 fun _ => hψ0 v hv
  have hB0 : ∀ v, v ∉ W → (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v = 0 :=
    fun v hv => Set.indicator_apply_eq_zero.2 fun _ => hψs0 v hv
  have hcomp : ∀ v, (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v =
      (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator (fun v => ENNReal.ofReal (φ v)) (T s v) := by
    intro v
    by_cases hv : v ∈ W
    · have hiff : T s v ∈ g ⁻¹' ((fun x : X => x - s) ⁻¹' S) ↔ v ∈ g ⁻¹' S := by
        simp only [Set.mem_preimage, hgT s v hv, add_sub_cancel_right]
      by_cases hvS : v ∈ g ⁻¹' S
      · rw [Set.indicator_of_mem hvS, Set.indicator_of_mem (hiff.2 hvS)]
      · rw [Set.indicator_of_notMem hvS, Set.indicator_of_notMem (fun h => hvS (hiff.1 h))]
    · rw [hB0 v hv, hA0 _ fun h => hv ((hTW s v).1 h)]
  have hmid : ∫⁻ v in W, (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v ∂μ =
      ∫⁻ v in W, (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
        (fun v => ENNReal.ofReal (φ v)) v ∂μ := by
    rw [setLIntegral_eq_lintegral hW.measurableSet hB0,
      setLIntegral_eq_lintegral hW.measurableSet hA0]
    simp only [hcomp]
    rw [← lintegral_map hAm (hTm s), hTμ s]
  have hpre : (fun x : X => x + s) ⁻¹' ((fun x : X => x - s) ⁻¹' S) = S := by
    ext x
    simp
  have htr := (measurePreserving_add_right ν s).setLIntegral_comp_preimage hS'm hD.measurable
  rw [hpre] at htr
  rw [← e1, hmid, e2, ← htr]

theorem fib_ne_zero : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [ν.IsAddHaarMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U W : Set V), IsOpen W → W ⊆ U → W.Nonempty → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ T : X → V → V, (∀ s, Measurable (T s)) → (∀ s, μ.map (T s) = μ) → (∀ s, ContinuousOn (T s) W) → (∀ s v, T s v ∈ W ↔ v ∈ W) → (∀ s, ∀ v ∈ W, T (-s) (T s v) = v) → (∀ s, ∀ v ∈ W, g (T s v) = g v + s) → ∀ b : X, fib b ≠ 0 := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf U W hW hWU hne fib hF T hTm hTμ
    hTc hTW hinv hgT b hb
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨φ, hφ, hc, hs, h0, -, h1⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump
    (isCompact_singleton (x := v₀)) hW (Set.singleton_subset_iff.2 hv₀)
  have hzero : ∀ c, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) = 0 := by
    intro c
    have key := lintegral_shift hι hg hf hW hWU hF hTm hTμ hTc hTW hinv hgT hφ hc hs h0 (c - b) b
    rw [add_sub_cancel] at key
    rw [← key, hb]
    simp
  have hm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have h2 := hF.2.1 _ hm
  simp only [hzero, lintegral_zero] at h2
  have h3 : ∫⁻ v in W, ENNReal.ofReal (φ v) ∂μ = 0 :=
    le_antisymm (h2 ▸ lintegral_mono_set hWU) bot_le
  have hae := (ae_restrict_iff' hW.measurableSet).1 ((lintegral_eq_zero_iff hm).1 h3)
  have hOpen : IsOpen ({v | 0 < φ v} ∩ W) := (isOpen_lt continuous_const hφ).inter hW
  have hpos : 0 < μ ({v | 0 < φ v} ∩ W) :=
    hOpen.measure_pos μ ⟨v₀, by simp [h1 v₀ rfl], hv₀⟩
  have hnull := ae_iff.1 hae
  refine hpos.ne' (measure_mono_null ?_ hnull)
  intro v hv
  rw [Set.mem_setOf_eq]
  intro hcon
  have h4 := hcon hv.2
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h4
  exact absurd hv.1 (not_lt.2 h4)

end GlobalTheory.CompanionTheory.SW.FibreShift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationHaarBaseStatement
open MeasureTheory Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disintegration_haar_base : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [ν.IsAddHaarMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U W : Set V), IsOpen W → W ⊆ U → W.Nonempty → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ T : X → V → V, (∀ s, Measurable (T s)) → (∀ s, μ.map (T s) = μ) → (∀ s, ContinuousOn (T s) W) → (∀ s v, T s v ∈ W ↔ v ∈ W) → (∀ s, ∀ v ∈ W, T (-s) (T s v) = v) → (∀ s, ∀ v ∈ W, g (T s v) = g v + s) → ∀ b : X, fib b ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero | exact GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMeasureByInvariantSubgroup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMeasureByInvariantSubgroup
open MeasureTheory Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Shear

theorem lintegral_shear_eq : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V]
    [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V]
    (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant]
    [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f →
    (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ →
    ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by
  intro V A _ _ _ _ _ _ _ _ μ lam _ _ _ _ j hj f hf hfinv K hK hK0 hKtop ψ hψ
  classical
  have hind : Measurable (K.indicator (1 : A → ℝ≥0∞)) := measurable_one.indicator hK
  have hind_ne : ∀ a, K.indicator (1 : A → ℝ≥0∞) a ≠ ⊤ := fun a => by
    rw [Set.indicator_apply]
    split_ifs <;> simp
  have hfneg : ∀ v a, f (v + -j a) = f v := fun v a => by
    rw [← map_neg]
    exact hfinv v (-a)
  have sA : ∀ a, ∫⁻ v, ψ (v + j a + j (f v)) ∂μ = ∫⁻ v, ψ (v + j (f v)) ∂μ := fun a =>
    (lintegral_add_right_eq_self (μ := μ) (fun v => ψ (v + j a + j (f v))) (-(j a))).symm.trans
      (lintegral_congr fun v => by simp only [neg_add_cancel_right, hfneg])
  have sB : ∀ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂lam =
      ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂lam := fun v =>
    (lintegral_add_right_eq_self (μ := lam) (fun a => K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v))) (-(f v))).symm.trans
      (lintegral_congr fun a => by simp only [map_add (f := _), map_neg, add_assoc, neg_add_cancel, add_zero])
  have sC : ∀ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂μ = ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂μ :=
    fun a => (lintegral_add_right_eq_self (μ := μ) (fun v => K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a)) (-(j a))).symm.trans
      (lintegral_congr fun v => by simp only [neg_add_cancel_right, hfneg])
  have sD : ∀ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂lam = lam K * ψ v := fun v => by
    have hm : Measurable fun a => K.indicator (1 : A → ℝ≥0∞) (a + -f v) := hind.comp (measurable_add_const (-f v))
    rw [lintegral_mul_const _ hm, lintegral_add_right_eq_self (μ := lam) (K.indicator (1 : A → ℝ≥0∞)) (-f v),
      lintegral_indicator_one hK]
  have hm1 : Measurable fun p : A × V => K.indicator (1 : A → ℝ≥0∞) p.1 * ψ (p.2 + j p.1 + j (f p.2)) :=
    (hind.comp measurable_fst).mul
      (hψ.comp ((measurable_snd.add (hj.comp measurable_fst)).add (hj.comp (hf.comp measurable_snd))))
  have hm2 : Measurable fun p : V × A => K.indicator (1 : A → ℝ≥0∞) (p.2 + -f p.1) * ψ (p.1 + j p.2) :=
    (hind.comp (measurable_snd.add (hf.comp measurable_fst).neg)).mul
      (hψ.comp (measurable_fst.add (hj.comp measurable_snd)))
  have hm3 : Measurable fun p : A × V => K.indicator (1 : A → ℝ≥0∞) (p.1 + -f p.2) * ψ p.2 :=
    (hind.comp (measurable_fst.add (hf.comp measurable_snd).neg)).mul (hψ.comp measurable_snd)
  have key : lam K * ∫⁻ v, ψ (v + j (f v)) ∂μ = lam K * ∫⁻ v, ψ v ∂μ := by
    calc lam K * ∫⁻ v, ψ (v + j (f v)) ∂μ
        = ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ∫⁻ v, ψ (v + j a + j (f v)) ∂μ ∂lam := by
          simp_rw [sA]
          rw [lintegral_mul_const _ hind, lintegral_indicator_one hK]
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂μ ∂lam := by
          refine lintegral_congr fun a => ?_
          rw [lintegral_const_mul' _ _ (hind_ne a)]
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂lam ∂μ :=
          lintegral_lintegral_swap hm1.aemeasurable
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂lam ∂μ := lintegral_congr fun v => sB v
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂μ ∂lam :=
          lintegral_lintegral_swap hm2.aemeasurable
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂μ ∂lam := lintegral_congr fun a => sC a
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂lam ∂μ :=
          lintegral_lintegral_swap hm3.aemeasurable
      _ = ∫⁻ v, lam K * ψ v ∂μ := lintegral_congr fun v => sD v
      _ = lam K * ∫⁻ v, ψ v ∂μ := lintegral_const_mul' _ _ hKtop
  exact (ENNReal.mul_right_inj hK0 hKtop).mp key

end GlobalTheory.CompanionTheory.Shear
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMeasureByInvariantSubgroupStatement
open MeasureTheory Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_measure_by_invariant_subgroup : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V] [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V] (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant] [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f → (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ → ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq | exact GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq | (intros; apply GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFibreMeasureLocal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos

section Alg

variable {A : Type} [CommRing A] (s : A →+* A) {ι : Type} [Fintype ι] (J : Matrix ι ι A)

theorem hf_add_right (x y z : ι → A) : hform s J x (y + z) = hform s J x y + hform s J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hf_add_left (x y z : ι → A) : hform s J (x + y) z = hform s J x z + hform s J y z := by
  simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hf_smul_right (a : A) (x y : ι → A) : hform s J x (a • y) = a * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_smul_left (a : A) (x y : ι → A) : hform s J (a • x) y = s a * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_zero_right (x : ι → A) : hform s J x 0 = 0 := by
  simp [hform]

theorem hf_swap (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (x y : ι → A) :
    s (hform s J x y) = hform s J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hs, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_shift (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (u x : ι → A) (c : A)
    (hxx : hform s J x x = 0) :
    hform s J (u + c • x) (u + c • x) =
      hform s J u u + c * s (hform s J x u) + s c * hform s J x u := by
  rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right,
    hf_smul_right, hxx, hf_swap s J hs hJ x u]
  ring

end Alg

section Shift

variable {K : Type} [CommRing K] (s : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
  (x : Fin M → K)

def bet (Y : Fin 1 → Fin M → K) : K := hform s J x (Y 0)

def jx : K →+ (Fin 1 → Fin M → K) where
  toFun a := fun _ => a • x
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [add_mul]

def cS (h r : K) (Y : Fin 1 → Fin M → K) : K := h * r * Ring.inverse (s (bet s J x Y))

def Tm (h r : K) (Y : Fin 1 → Fin M → K) : Fin 1 → Fin M → K := Y + jx x (cS s J x h r Y)

variable {s J x}

theorem bet_add_jx (hxx : hform s J x x = 0) (Y : Fin 1 → Fin M → K) (a : K) :
    bet s J x (Y + jx x a) = bet s J x Y := by
  show hform s J x (Y 0 + a • x) = hform s J x (Y 0)
  rw [hf_add_right, hf_smul_right, hxx, mul_zero, add_zero]

theorem cS_add_jx (hxx : hform s J x x = 0) (h r : K) (Y : Fin 1 → Fin M → K) (a : K) :
    cS s J x h r (Y + jx x a) = cS s J x h r Y := by
  simp only [cS, bet_add_jx hxx]

theorem bet_Tm (hxx : hform s J x x = 0) (h r : K) (Y : Fin 1 → Fin M → K) :
    bet s J x (Tm s J x h r Y) = bet s J x Y :=
  bet_add_jx hxx _ _

theorem Tm_neg (hxx : hform s J x x = 0) (h r : K) (Y : Fin 1 → Fin M → K) :
    Tm s J x h (-r) (Tm s J x h r Y) = Y := by
  have h1 : cS s J x h (-r) (Tm s J x h r Y) = -cS s J x h r Y := by
    simp only [cS, bet_Tm hxx]
    ring
  rw [Tm, h1, Tm, map_neg, add_neg_cancel_right]

theorem hf_Tm (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j)
    (hxx : hform s J x x = 0) {h r : K} (h2 : h + h = 1) (hh : s h = h) (hr : s r = r)
    {Y : Fin 1 → Fin M → K} (hY : IsUnit (bet s J x Y)) :
    hform s J (Tm s J x h r Y 0) (Tm s J x h r Y 0) = hform s J (Y 0) (Y 0) + r := by
  have hT : Tm s J x h r Y 0 = Y 0 + cS s J x h r Y • x := rfl
  have hsb : IsUnit (s (bet s J x Y)) := hY.map s
  have e1 : Ring.inverse (s (bet s J x Y)) * s (bet s J x Y) = 1 :=
    Ring.inverse_mul_cancel _ hsb
  have e2 : s (Ring.inverse (s (bet s J x Y))) * bet s J x Y = 1 := by
    have := congrArg s e1
    rwa [map_mul, hs, map_one] at this
  have hb : hform s J x (Y 0) = bet s J x Y := rfl
  rw [hT, hf_shift s J hs hJ _ _ _ hxx, hb]
  simp only [cS, map_mul, hh, hr]
  linear_combination (h * r) * e1 + (h * r) * e2 + r * h2

theorem linIndep_of_isUnit {Y : Fin 1 → Fin M → K} (hY : IsUnit (bet s J x Y)) :
    LinearIndependent K Y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 : c 0 • Y 0 = 0 := by simpa using hc
  have h1 : c 0 * bet s J x Y = 0 := by
    have := congrArg (hform s J x) h0
    rwa [hf_smul_right, hf_zero_right] at this
  rw [Subsingleton.elim i 0]
  exact hY.mul_left_eq_zero.1 h1

end Shift

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_bet (s : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K) :
    Continuous (bet s J x) := by
  unfold bet hform
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul ((continuous_apply j).comp (continuous_apply 0))

theorem continuous_jx {M : ℕ} (x : Fin M → K) : Continuous (jx x) := by
  refine continuous_pi fun _ => continuous_pi fun i => ?_
  exact continuous_id.mul continuous_const

theorem isOpen_isUnit (hU : IsOpenEmbedding (Units.val : Kˣ → K)) : IsOpen {r : K | IsUnit r} := by
  have := hU.isOpen_range
  convert this using 1
  ext r
  simp [IsUnit]

theorem continuousOn_Tm (hU : IsOpenEmbedding (Units.val : Kˣ → K)) {s : K →+* K}
    (hsc : Continuous s) {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K) (h r : K) :
    ContinuousOn (Tm s J x h r) {Y | IsUnit (bet s J x Y)} := by
  have h1 : ContinuousOn (fun Y => Ring.inverse (s (bet s J x Y))) {Y | IsUnit (bet s J x Y)} :=
    (GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse hU).comp
      (hsc.comp (continuous_bet s J x)).continuousOn (fun Y hY => IsUnit.map s hY)
  have h2 : ContinuousOn (cS s J x h r) {Y | IsUnit (bet s J x Y)} :=
    continuousOn_const.mul h1
  exact continuousOn_id.add ((continuous_jx x).comp_continuousOn h2)

variable [MeasurableSpace K] [BorelSpace K]

theorem measurable_ringInverse (hU : IsOpenEmbedding (Units.val : Kˣ → K)) :
    Measurable (Ring.inverse : K → K) := by
  classical
  have h1 : Measurable (({r : K | IsUnit r}).piecewise (Ring.inverse : K → K) (fun _ => 0)) :=
    (GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse hU).measurable_piecewise continuousOn_const
      (isOpen_isUnit hU).measurableSet
  convert h1 using 1
  funext r
  by_cases hr : IsUnit r
  · simp [Set.piecewise, hr]
  · simp [Set.piecewise, hr, Ring.inverse_non_unit]

end Top

theorem map_shift_eq {V A : Type} [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V]
    [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V]
    (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant]
    [lam.IsAddRightInvariant] (j : A →+ V) (hj : Measurable j) (f : V → A) (hf : Measurable f)
    (hinv : ∀ v a, f (v + j a) = f v) (C : Set A) (hC : MeasurableSet C) (h0 : lam C ≠ 0)
    (h1 : lam C ≠ ⊤) : μ.map (fun v => v + j (f v)) = μ := by
  have hT : Measurable fun v => v + j (f v) := measurable_id.add (hj.comp hf)
  ext B hB
  rw [Measure.map_apply hT hB]
  have key := GlobalTheory.T.quotient_measure_by_invariant_subgroup V A μ lam j hj f hf hinv C hC h0 h1 (B.indicator 1)
    (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB] at key
  rw [← key, ← lintegral_indicator_one (hT hB)]
  refine lintegral_congr fun v => ?_
  by_cases hv : v + j (f v) ∈ B
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show v ∈ (fun v => v + j (f v)) ⁻¹' B from hv)]
    rfl
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (show v ∉ (fun v => v + j (f v)) ⁻¹' B from hv)]

section Meas

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem measurable_cS (hU : IsOpenEmbedding (Units.val : Kˣ → K)) {s : K →+* K}
    (hsc : Continuous s) {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K) (h r : K) :
    Measurable (cS s J x h r) :=
  ((measurable_ringInverse hU).comp (hsc.comp (continuous_bet s J x)).measurable).const_mul _

theorem measurable_Tm (hU : IsOpenEmbedding (Units.val : Kˣ → K)) {s : K →+* K}
    (hsc : Continuous s) {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K) (h r : K) :
    Measurable (Tm s J x h r) :=
  measurable_id.add ((continuous_jx x).measurable.comp (measurable_cS hU hsc J x h r))

theorem map_Tm (hU : IsOpenEmbedding (Units.val : Kˣ → K)) {s : K →+* K}
    (hsc : Continuous s) {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K)
    (hxx : hform s J x x = 0) (h r : K) (μ : Measure (Fin 1 → Fin M → K)) [μ.IsAddHaarMeasure] :
    μ.map (Tm s J x h r) = μ := by
  obtain ⟨C, hCc, hC0⟩ := exists_compact_mem_nhds (0 : K)
  let lam : Measure K := Measure.addHaar
  exact map_shift_eq μ lam (jx x) (continuous_jx x).measurable (cS s J x h r)
    (measurable_cS hU hsc J x h r) (fun Y a => cS_add_jx hxx h r Y a) C hCc.measurableSet
    (Measure.measure_pos_of_mem_nhds lam hC0).ne' hCc.measure_lt_top.ne

end Meas

theorem fibre_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ 1)) (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J 1 μ ν m → ∀ X : Fin 1 → Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → gramR R σ J X = 0 → ∀ S : HermR R σ 1, m S ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hL μ ν m hμ hν hm X hX hX0 S
  haveI : IsTopologicalRing R := hL.1
  haveI : LocallyCompactSpace R := hL.2.1
  haveI : SecondCountableTopology R := hL.2.2.1
  haveI : T2Space R := hL.2.2.2.1
  obtain ⟨tK1, tK2, tK3, tK4, tsc, -, -, tK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fin 1 → Fin M → R ⊗[F] E) := tK8 1 M
  obtain ⟨h1, h2, h3, h4, h5⟩ := HermTop.herm_top F E σ hσ R 1
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g, hgc, hg⟩ := h5 M J hJ
  have hU := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hL
  have hss : ∀ a, sigR R σ (sigR R σ a) = a := HermTop.sigR_sigR R (HermTop.sigma_sigma hσ)
  have hJJ : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    simp only [JR, Matrix.map_apply, HermTop.sigR_inclR, hJ.1]
  obtain ⟨hf, hf2, hfs⟩ : ∃ hf : R ⊗[F] E, hf + hf = 1 ∧ sigR R σ hf = hf := by
    refine ⟨inclR R (algebraMap F E (1 / 2)), ?_, ?_⟩
    · rw [← map_add (f := _), ← map_add (f := _)]
      norm_num
    · rw [HermTop.sigR_inclR, σ.commutes]
  have hxx : hform (sigR R σ) (JR R J) (X 0) (X 0) = 0 := congrFun (congrFun hX0 0) 0
  have hXeq : (fun _ : Fin 1 => X 0) = X := by
    funext a
    rw [Subsingleton.elim a 0]
  obtain ⟨y, hy⟩ := GlobalTheory.T.hermitian_form_primitive_vector_pairing F E σ hσ M J hJ R hL (X 0) (by rw [hXeq]; exact hX)
  have hgen := GlobalTheory.T.disintegration_haar_base (Fin 1 → Fin M → R ⊗[F] E) (HermR R σ 1)
    (Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) μ ν (gramR R σ J) g Subtype.val Subtype.val_injective hgc hg
    {Y | LinearIndependent (R ⊗[F] E) Y} {Y | IsUnit (bet (sigR R σ) (JR R J) (X 0) Y)}
    ((isOpen_isUnit hU).preimage (continuous_bet _ _ _))
    (fun Y hY => linIndep_of_isUnit hY)
    ⟨fun _ => y, by
      show IsUnit (hR R σ J (X 0) y)
      rw [hy]
      exact isUnit_one⟩
    m hm (fun S Y => Tm (sigR R σ) (JR R J) (X 0) hf ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) Y)
    (fun S => measurable_Tm hU tsc _ _ _ _)
    (fun S => map_Tm hU tsc _ _ hxx _ _ μ)
    (fun S => continuousOn_Tm hU tsc _ _ _ _)
    (fun S Y => by
      show IsUnit (bet _ _ _ _) ↔ IsUnit (bet _ _ _ _)
      rw [bet_Tm hxx])
    (fun S Y _ => Tm_neg hxx _ _ Y)
    (fun S Y hY => by
      apply Subtype.ext
      rw [← hg, AddSubgroup.coe_add, ← hg]
      ext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      exact hf_Tm hss hJJ hxx hf2 hfs (S.2 0 0) hY)
  exact hgen S

end GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFibreMeasureLocalStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_fibre_measure_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ 1)) (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J 1 μ ν m → ∀ X : Fin 1 → Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → gramR R σ J X = 0 → ∀ S : HermR R σ 1, m S ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos.fibre_ne_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos.fibre_ne_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos.fibre_ne_zero <;> assumption)
end
