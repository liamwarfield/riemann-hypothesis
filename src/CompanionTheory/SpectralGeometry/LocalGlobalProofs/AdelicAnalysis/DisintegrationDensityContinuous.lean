module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.AutomorphicTheory.ThetaDilations.SqPosOfNe
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreFam

section Top

variable {V : Type} [TopologicalSpace V]

theorem exists_bump [LocallyCompactSpace V] [T2Space V] {K O : Set V} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧ (∀ v, 0 ≤ φ v) ∧
      (∀ v, φ v ≤ 1) ∧ ∀ v ∈ K, φ v = 1 := by
  obtain ⟨f, hf1, hfc, hfs, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  exact ⟨f, f.continuous, hfc, hfs, fun v => (hf01 v).1, fun v => (hf01 v).2, fun v hv => hf1 hv⟩

theorem exists_exhaustion [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} (hU : IsOpen U) :
    ∃ K W : ℕ → Set V, (∀ n, IsCompact (K n)) ∧ (∀ n, IsOpen (W n)) ∧ (∀ n, W n ⊆ K n) ∧
      (∀ n, K n ⊆ U) ∧ Monotone K ∧ Monotone W ∧ (⋃ n, K n) = U ∧ (⋃ n, W n) = U := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let E := CompactExhaustion.choice U
  have hint : ⋃ n, interior (E n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ n, E n := by
      rw [E.iUnion_eq]
      exact Set.mem_univ x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n + 1, E.subset_interior_succ n hn⟩
  refine ⟨fun n => (↑) '' E n, fun n => (↑) '' interior (E n),
    fun n => (E.isCompact n).image continuous_subtype_val,
    fun n => hU.isOpenMap_subtype_val _ isOpen_interior, fun n => Set.image_mono interior_subset,
    fun n => by
      rintro _ ⟨x, -, rfl⟩
      exact x.2,
    fun m n hmn => Set.image_mono (E.subset hmn),
    fun m n hmn => Set.image_mono (interior_mono (E.subset hmn)), ?_, ?_⟩
  · rw [← Set.image_iUnion, E.iUnion_eq, Set.image_univ, Subtype.range_coe]
  · rw [← Set.image_iUnion, hint, Set.image_univ, Subtype.range_coe]

end Top

section Meas

variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]

theorem le_lintegral_bump [T2Space V] (m : Measure V) {K : Set V} (hK : IsCompact K) {φ : V → ℝ}
    (h0 : ∀ v, 0 ≤ φ v) (h1 : ∀ v ∈ K, φ v = 1) : m K ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂m := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [← lintegral_indicator_one hKm]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ K
  · simp [Set.indicator_apply, hv, h1 v hv]
  · simp [Set.indicator_apply, hv]

theorem lintegral_bump_le (m : Measure V) {O : Set V} (hO : IsOpen O) {φ : V → ℝ}
    (h1 : ∀ v, φ v ≤ 1) (hs : tsupport φ ⊆ O) : ∫⁻ v, ENNReal.ofReal (φ v) ∂m ≤ m O := by
  rw [← lintegral_indicator_one hO.measurableSet]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ O
  · simpa [Set.indicator_apply, hv] using h1 v
  · have hz : φ v = 0 := by
      by_contra hne
      exact hv (hs (subset_tsupport φ hne))
    simp [Set.indicator_apply, hv, hz]

variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

def BumpFamily (U : Set V) (B : Set X) (fib : X → Measure V) : Prop :=
  (∀ b, b ∉ B → fib b = 0) ∧
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∀ b ∈ B, Integrable φ (fib b)) ∧ ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) B

theorem BumpFamily.measurable_lintegral {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) {φ : V → ℝ} (hc : Continuous φ)
    (hcs : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (h0 : ∀ v, 0 ≤ φ v) :
    Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by
  classical
  obtain ⟨h0B, hφ⟩ := h
  obtain ⟨hint, hcont⟩ := hφ φ hc hcs hs
  have heq : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =
      B.piecewise (fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b))) (fun _ => 0) := by
    funext b
    by_cases hb : b ∈ B
    · simp only [Set.piecewise_eq_of_mem, hb]
      rw [ofReal_integral_eq_lintegral_ofReal (hint b hb) (ae_of_all _ h0)]
    · simp [Set.piecewise, hb, h0B b hb]
  rw [heq]
  exact (ENNReal.continuous_ofReal.comp_continuousOn hcont).measurable_piecewise continuousOn_const
    hB.measurableSet

theorem BumpFamily.measurable_open [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) {O : Set V} (hO : IsOpen O) (hOU : O ⊆ U) :
    Measurable fun b => fib b O := by
  obtain ⟨K, W, hKc, -, -, hKO, hKmono, -, hKU, -⟩ := exists_exhaustion hO
  have hφ : ∀ n, ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧ (∀ v, 0 ≤ φ v) ∧
      (∀ v, φ v ≤ 1) ∧ ∀ v ∈ K n, φ v = 1 := fun n => exists_bump (hKc n) hO (hKO n)
  choose φ hφc hφcs hφs hφ0 hφ1 hφK using hφ
  have hmeas : ∀ n, Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ n v) ∂(fib b) := fun n =>
    h.measurable_lintegral hB (hφc n) (hφcs n) ((hφs n).trans hOU) (hφ0 n)
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr fun b => ?_)
  have hlow : Filter.Tendsto (fun n => fib b (K n)) Filter.atTop (𝓝 (fib b O)) := by
    have h2 := tendsto_measure_iUnion_atTop (μ := fib b) hKmono
    rw [hKU] at h2
    exact h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => le_lintegral_bump (fib b) (hKc n) (hφ0 n) (hφK n))
    (fun n => lintegral_bump_le (fib b) hO (hφ1 n) (hφs n))

theorem BumpFamily.lt_top [LocallyCompactSpace V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hU : IsOpen U) {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) (b : X) :
    fib b K < ∞ := by
  by_cases hb : b ∈ B
  · obtain ⟨φ, hc, hcs, hs, h0, -, hK1⟩ := exists_bump hK hU hKU
    have hint := (h.2 φ hc hcs hs).1 b hb
    exact lt_of_le_of_lt (le_lintegral_bump (fib b) hK h0 hK1) hint.lintegral_lt_top
  · rw [h.1 b hb]
    simp

theorem BumpFamily.measurable_apply [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) (hU : IsOpen U) (hc : ∀ b, fib b Uᶜ = 0)
    {A : Set V} (hA : MeasurableSet A) : Measurable fun b => fib b A := by
  obtain ⟨K, W, hKc, hWo, hWK, hKU, -, hWmono, -, hWU⟩ := exists_exhaustion hU
  have hWn : ∀ n, Measurable fun b => fib b (A ∩ W n) := by
    intro n
    haveI : ∀ b, IsFiniteMeasure ((fib b).restrict (W n)) := fun b =>
      isFiniteMeasure_restrict.mpr
        (ne_of_lt (lt_of_le_of_lt (measure_mono (hWK n)) (h.lt_top hU (hKc n) (hKU n) b)))
    have hmeas : Measurable fun b => (fib b).restrict (W n) := by
      refine Measurable.measure_of_isPiSystem (S := {s : Set V | IsOpen s}) BorelSpace.measurable_eq
        isPiSystem_isOpen ?_ ?_
      · intro s hs
        have hso : IsOpen s := hs
        simp only [Measure.restrict_apply hso.measurableSet]
        exact h.measurable_open hB (hso.inter (hWo n))
          (Set.inter_subset_right.trans ((hWK n).trans (hKU n)))
      · simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact h.measurable_open hB (hWo n) ((hWK n).trans (hKU n))
    have h2 := (Measure.measurable_coe hA).comp hmeas
    simpa [Function.comp_def, Measure.restrict_apply hA] using h2
  have hlim : ∀ b, Filter.Tendsto (fun n => fib b (A ∩ W n)) Filter.atTop (𝓝 (fib b A)) := by
    intro b
    have hmono : Monotone fun n => A ∩ W n := fun m n hmn => Set.inter_subset_inter_right _ (hWmono hmn)
    have h2 := tendsto_measure_iUnion_atTop (μ := fib b) hmono
    rw [← Set.inter_iUnion, hWU, measure_inter_conull (hc b)] at h2
    exact h2
  exact measurable_of_tendsto_metrizable hWn (tendsto_pi_nhds.mpr hlim)

end Meas

theorem fibre_family_basic : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g →
    (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V,
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib →
    (∀ b, IsLocallyFiniteMeasure (fib b)) ∧ (∀ b, b ∉ B → fib b = 0) ∧
    (∀ A : Set V, MeasurableSet A → Measurable fun b => fib b A) ∧
    ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B →
      ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hfv B hB fib hF
  classical
  obtain ⟨hfib0, -, hbump⟩ := hF
  have hU : IsOpen (g ⁻¹' B) := hB.preimage hg
  have hmemι : ∀ b w, w ∈ f ⁻¹' {ι b} → g w = b := by
    intro b w hw
    apply hι
    rw [← hfv w]
    exact hw
  have hfibB : ∀ b, b ∉ B → fib b = 0 := by
    intro b hb
    have hempty : f ⁻¹' {ι b} ∩ g ⁻¹' B = ∅ := by
      refine Set.subset_empty_iff.mp fun w hw => (hb ?_).elim
      rw [← hmemι b w hw.1]
      exact hw.2
    have h0 := hfib0 b
    rw [hempty, Set.compl_empty] at h0
    exact Measure.measure_univ_eq_zero.mp h0
  have hBF : BumpFamily (g ⁻¹' B) B fib := ⟨hfibB, hbump⟩
  refine ⟨?_, hfibB, ?_, ?_⟩
  · intro b
    refine ⟨fun v => ?_⟩
    by_cases hb : b ∈ B
    · by_cases hgv : g v = b
      · have hvU : v ∈ g ⁻¹' B := by
          rw [Set.mem_preimage, hgv]
          exact hb
        obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds (hU.mem_nhds hvU)
        exact ⟨K, hKn, hBF.lt_top hU hKc hKU b⟩
      · refine ⟨g ⁻¹' {b}ᶜ, (isClosed_singleton.preimage hg).isOpen_compl.mem_nhds hgv, ?_⟩
        have h0 : fib b (g ⁻¹' {b}ᶜ) = 0 := by
          exact measure_mono_null (show g ⁻¹' {b}ᶜ ⊆ (f ⁻¹' {ι b} ∩ g ⁻¹' B)ᶜ from
            fun w hw hw' => hw (hmemι b w hw'.1)) (hfib0 b)
        rw [h0]
        exact ENNReal.zero_lt_top
    · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      rw [hfibB b hb]
      simp
  · intro A hA
    exact hBF.measurable_apply hB hU (fun b => measure_mono_null
      (show (g ⁻¹' B)ᶜ ⊆ (f ⁻¹' {ι b} ∩ g ⁻¹' B)ᶜ from fun w hw hw' => hw hw'.2) (hfib0 b)) hA
  · intro C D hC hD hDB
    have hC' : IsCompact (C ∩ g ⁻¹' D) := hC.inter_right (hD.isClosed.preimage hg)
    have hC'U : C ∩ g ⁻¹' D ⊆ g ⁻¹' B := fun w hw => hDB hw.2
    obtain ⟨φ, hc, hcs, hs, h0, -, h1⟩ := exists_bump hC' hU hC'U
    obtain ⟨hint, hcont⟩ := hbump φ hc hcs hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hcont.mono hDB)
    refine ⟨Real.toNNReal M, fun b hb => ?_⟩
    calc fib b C = fib b (C ∩ (f ⁻¹' {ι b} ∩ g ⁻¹' B)) := (measure_inter_conull (hfib0 b)).symm
      _ ≤ fib b (C ∩ g ⁻¹' D) := by
          refine measure_mono (show C ∩ (f ⁻¹' {ι b} ∩ g ⁻¹' B) ⊆ C ∩ g ⁻¹' D from
            fun w hw => ⟨hw.1, ?_⟩)
          show g w ∈ D
          rw [hmemι b w hw.2.1]
          exact hb
      _ ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := le_lintegral_bump (fib b) hC' h0 h1
      _ = ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
          (ofReal_integral_eq_lintegral_ofReal (hint b (hDB hb)) (ae_of_all _ h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hM b hb))
      _ = (Real.toNNReal M : ℝ≥0∞) := rfl

end GlobalTheory.CompanionTheory.SW.FibreFam
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuousStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_family_locallyFinite_measurable_bdd_on_compact : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → (∀ b, IsLocallyFiniteMeasure (fib b)) ∧ (∀ b, b ∉ B → fib b = 0) ∧ (∀ A : Set V, MeasurableSet A → Measurable fun b => fib b A) ∧ ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B → ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic | exact GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic | (intros; apply GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompacts
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompacts
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW

theorem not_lt_of_setLIntegral_compact_eq {X : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν]
    [ν.IsOpenPosMeasure] {B : Set X} (hB : IsOpen B) {D D' : X → ℝ≥0∞}
    (hD : ContinuousOn D B) (hD' : ContinuousOn D' B)
    (h : ∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν)
    {b : X} (hb : b ∈ B) : ¬ D b < D' b := by
  intro hlt
  obtain ⟨c1, h1, h12⟩ := exists_between hlt
  obtain ⟨c2, hc, h2⟩ := exists_between h12
  have hDa : ContinuousAt D b := hD.continuousAt (hB.mem_nhds hb)
  have hD'a : ContinuousAt D' b := hD'.continuousAt (hB.mem_nhds hb)

  have hN : {x | D x < c1} ∩ {x | c2 < D' x} ∩ B ∈ 𝓝 b :=
    Filter.inter_mem (Filter.inter_mem (hDa.eventually (gt_mem_nhds h1))
      (hD'a.eventually (lt_mem_nhds h2))) (hB.mem_nhds hb)
  obtain ⟨S, hSn, hSN, hS⟩ := local_compact_nhds hN
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hpos : ν S ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hSn).ne'
  have htop : ν S ≠ ∞ := hS.measure_lt_top.ne
  have hle1 : ∫⁻ x in S, D x ∂ν ≤ c1 * ν S := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hSm).2
      (Filter.Eventually.of_forall fun x hx => (hSN hx).1.1.le))
  have hle2 : c2 * ν S ≤ ∫⁻ x in S, D' x ∂ν := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hSm).2
      (Filter.Eventually.of_forall fun x hx => (hSN hx).1.2.le))
  have hmid : c1 * ν S < c2 * ν S := (ENNReal.mul_lt_mul_iff_left hpos htop).2 hc
  exact (hle1.trans_lt (hmid.trans_le hle2)).ne (h S hS fun x hx => (hSN hx).2)

theorem eq_of_setLIntegral_compact_eq :
    ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
      [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν]
      [ν.IsOpenPosMeasure] (B : Set X), IsOpen B → ∀ D D' : X → ℝ≥0∞, ContinuousOn D B →
      ContinuousOn D' B →
      (∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν) →
      ∀ b ∈ B, D b = D' b := by
  intro X _ _ _ _ _ _ ν _ _ B hB D D' hD hD' h b hb
  exact le_antisymm
    (not_lt.1 (not_lt_of_setLIntegral_compact_eq ν hB hD' hD (fun S hS hSB => (h S hS hSB).symm) hb))
    (not_lt.1 (not_lt_of_setLIntegral_compact_eq ν hB hD hD' h hb))

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompactsStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts : ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (B : Set X), IsOpen B → ∀ D D' : X → ℝ≥0∞, ContinuousOn D B → ContinuousOn D' B → (∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν) → ∀ b ∈ B, D b = D' b := by
  first | exact @GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq | exact GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq | (intros; apply GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsFibreFamilyTransport
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW

theorem isFibreFamily_transport :
    ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (V' : Type) [TopologicalSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V'] (f' : V' → Y) (g' : V' → X), Continuous g' → (∀ v, f' v = ι (g' v)) → ∀ (e : V ≃ₜ V') (τ : X ≃ₜ X), (∀ v, g' (e v) = τ (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (μ.map e) f' ι (g' ⁻¹' (τ '' B)) (ν.map τ) (τ '' B) (fun b => (fib (τ.symm b)).map e) := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf V' _ _ _ _ _ _ f' g' hg' hf' e τ hc B hB fib h
  obtain ⟨h1, h2, h3⟩ := h
  have hU : e ⁻¹' (g' ⁻¹' (τ '' B)) = g ⁻¹' B := by
    ext v
    simp only [Set.mem_preimage, hc v, τ.injective.mem_set_image]
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have hτ : MeasurableEmbedding τ := τ.measurableEmbedding
  refine ⟨?_, ?_, ?_⟩
  · intro b
    have hset : e ⁻¹' (f' ⁻¹' {ι b} ∩ g' ⁻¹' (τ '' B))ᶜ = (f ⁻¹' {ι (τ.symm b)} ∩ g ⁻¹' B)ᶜ := by
      rw [Set.preimage_compl, Set.preimage_inter, hU]
      congr 2
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hf, hf', hι.eq_iff, hc v]
      exact ⟨fun hh => by rw [← hh, τ.symm_apply_apply], fun hh => by rw [hh, τ.apply_symm_apply]⟩
    show ((fib (τ.symm b)).map e) _ = 0
    rw [hemb.map_apply, hset]
    exact h1 _
  · intro φ hφ
    have hr : (μ.map e).restrict (g' ⁻¹' (τ '' B)) = (μ.restrict (g ⁻¹' B)).map e := by
      rw [← hU]
      exact (hemb.restrict_map μ _)
    rw [hr, hemb.lintegral_map, h2 (fun v => φ (e v)) (hφ.comp e.measurable), hτ.lintegral_map]
    refine lintegral_congr fun b => ?_
    simp only [τ.symm_apply_apply, hemb.lintegral_map, Function.comp]
  · intro φ hφ hcs hts
    have hts' : tsupport (φ ∘ e) ⊆ g ⁻¹' B := by
      rw [tsupport_comp_eq_preimage, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨hi, hcont⟩ := h3 (φ ∘ e) (hφ.comp e.continuous)
      (hcs.comp_isClosedEmbedding e.isClosedEmbedding) hts'
    have hm : Set.MapsTo τ.symm (τ '' B) B := by
      rintro _ ⟨x, hx, rfl⟩
      simpa using hx
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [hemb.integrable_map_iff]
      exact hi _ (hm hb)
    · have : (fun b => ∫ v, φ v ∂((fib (τ.symm b)).map e))
          = (fun b => ∫ v, (φ ∘ e) v ∂(fib b)) ∘ τ.symm := by
        funext b
        exact hemb.integral_map φ
      rw [this]
      exact hcont.comp τ.symm.continuous.continuousOn hm

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FibreFamilySmul
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.Rescale

theorem isFibreFamily_rescale (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y)
    (ι : X → Y) (U : Set V) (B : Set X) (fib : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) (a c : ℝ≥0) (hc : c ≠ 0) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (a • μ) f ι U (c • ν) B (fun b => (a / c) • fib b) := by
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h ⊢
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · rw [Measure.smul_apply, h.1 b, smul_zero]
  · simp only [Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [h.2.1 φ hφ, lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul,
      mul_comm c, div_mul_cancel₀ a hc]
  · obtain ⟨h1, h2⟩ := h.2.2 φ hφc hφs hφU
    refine ⟨fun b hb => (h1 b hb).smul_measure_nnreal, ?_⟩
    have e : (fun b => ∫ v, φ v ∂((a / c) • fib b)) = fun b => ((a / c : ℝ≥0) : ℝ) • ∫ v, φ v ∂fib b := by
      funext b
      rw [integral_smul_nnreal_measure, NNReal.smul_def]
    rw [e]
    exact h2.const_smul ((a / c : ℝ≥0) : ℝ)

end GlobalTheory.CompanionTheory.SW.Rescale
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureProdOfAddGroups
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureProdOfAddGroups
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.HaarTransport

theorem map_addEquiv_haar (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [IsTopologicalAddGroup V] [AddCommGroup V'] [TopologicalSpace V'] [LocallyCompactSpace V']
    [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V']
    [IsTopologicalAddGroup V'] (μ : Measure V) [μ.IsAddHaarMeasure] (μ' : Measure V')
    [μ'.IsAddHaarMeasure] (e : V ≃+ V') (he : Continuous e) (hes : Continuous e.symm) :
    (∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ') ∧
      ∀ (L : Set V) (L' : Set V'), IsCompact L → IsOpen L → L.Nonempty →
        (∀ v, e v ∈ L' ↔ v ∈ L) → μ L = μ' L' → μ.map e = μ' := by
  let E : V ≃ₜ+ V' := { e with continuous_toFun := he, continuous_invFun := hes }
  haveI hH : (μ.map e).IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  have ha := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ'
  have ha0 : Measure.addHaarScalarFactor (μ.map e) μ' ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  generalize Measure.addHaarScalarFactor (μ.map e) μ' = a at ha ha0
  have hemb : MeasurableEmbedding e :=
    (Homeomorph.mk e.toEquiv he hes).measurableEmbedding
  refine ⟨⟨a, ha0, ha⟩, ?_⟩
  · intro L L' hLc hLo hLn hL hmass
    have hpre : e ⁻¹' L' = L := by ext v; exact hL v
    have hpos : μ L ≠ 0 := (hLo.measure_pos μ hLn).ne'
    have hfin : μ L ≠ ∞ := hLc.measure_lt_top.ne
    have hLm : μ.map e L' = μ L := by
      rw [hemb.map_apply, hpre]
    have hval : μ L = (a : ℝ≥0∞) * μ L := by
      have h1 := congrArg (fun m => m L') ha
      simp only [Measure.smul_apply, hLm] at h1
      rw [← hmass] at h1
      simpa [ENNReal.smul_def] using h1
    have ha1 : (a : ℝ≥0∞) = 1 := by
      have h2 : (a : ℝ≥0∞) * μ L = 1 * μ L := by rw [one_mul]; exact hval.symm
      exact (ENNReal.mul_left_inj hpos hfin).1 h2
    have ha1' : a = 1 := by exact_mod_cast ha1
    rw [ha, ha1', one_smul]

end GlobalTheory.CompanionTheory.SW.HaarTransport
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureProdOfAddGroupsStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open : ∀ (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] [AddCommGroup V'] [TopologicalSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V'] [IsTopologicalAddGroup V'] (μ : Measure V) [μ.IsAddHaarMeasure] (μ' : Measure V') [μ'.IsAddHaarMeasure] (e : V ≃+ V'), Continuous e → Continuous e.symm → (∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ') ∧ ∀ (L : Set V) (L' : Set V'), IsCompact L → IsOpen L → L.Nonempty → (∀ v, e v ∈ L' ↔ v ∈ L) → μ L = μ' L' → μ.map e = μ' := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar | exact GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar | (intros; apply GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarModularCharacterOfContinuousAction
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarModularCharacterOfContinuousAction
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW


open scoped Pointwise in
theorem exists_continuous_modulus_of_continuous_action :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
      [IsTopologicalAddGroup V] (μ : Measure V) [μ.IsAddHaarMeasure] (Q : Type) [Group Q]
      [TopologicalSpace Q] [IsTopologicalGroup Q] [DistribMulAction Q V] [ContinuousSMul Q V],
      ∃ χ : Q →* ℝ≥0, Continuous χ ∧ ∀ q : Q, μ.map (fun v => q • v) = χ q • μ := by
  intro V _ _ _ _ _ _ _ _ μ _ Q _ _ _ _ _
  letI : SMul Q (Set V) := Set.smulSet

  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : V)
  have hKint : (interior K).Nonempty := ⟨0, mem_interior_iff_mem_nhds.2 hK0⟩
  have hKtop : μ K ≠ ∞ := hK.measure_lt_top.ne
  have hKpos : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have : μ.Regular := Measure.regular_of_isAddLeftInvariant hK hKint hKtop
  set Δ : Q →* ℝ≥0 := distribHaarChar V with hΔ
  have hmul : ∀ (g : Q) (s : Set V), (Δ g : ℝ≥0∞) * μ s = μ (g • s) := fun g s =>
    distribHaarChar_mul μ g s

  have hup : ∀ b : ℝ≥0, 1 < b → ∀ᶠ q in 𝓝 (1 : Q), Δ q < b := by
    intro b hb
    have hb' : (1 : ℝ≥0∞) < b := by exact_mod_cast hb
    have hlt : μ K < (b : ℝ≥0∞) * μ K := by
      calc μ K = 1 * μ K := (one_mul _).symm
        _ < b * μ K := (ENNReal.mul_lt_mul_iff_left hKpos hKtop).2 hb'
    obtain ⟨O, hKO, hO, hOμ⟩ := Set.exists_isOpen_lt_of_lt K _ hlt
    have hN : IsOpen {p : Q × V | p.1 • p.2 ∈ O} := hO.preimage continuous_smul
    obtain ⟨u, v, hu, -, h1u, hKv, huv⟩ :=
      generalized_tube_lemma (isCompact_singleton : IsCompact ({1} : Set Q)) hK hN (by
        rintro ⟨q, k⟩ ⟨hq, hk⟩
        simp only [Set.mem_singleton_iff] at hq
        subst hq
        simpa using hKO hk)
    filter_upwards [hu.mem_nhds (h1u (Set.mem_singleton 1))] with q hq
    have hsub : q • K ⊆ O := by
      rintro _ ⟨k, hk, rfl⟩
      exact huv (Set.mk_mem_prod hq (hKv hk))
    have h2 : (Δ q : ℝ≥0∞) * μ K < b * μ K := by
      rw [hmul]
      exact (measure_mono hsub).trans_lt hOμ
    exact_mod_cast (ENNReal.mul_lt_mul_iff_left hKpos hKtop).1 h2
  have hcont1 : ContinuousAt Δ 1 := by
    rw [ContinuousAt, map_one]
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => hup b hb⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Filter.Eventually.of_forall fun q => distribHaarChar_pos
    · have hb : 1 < a⁻¹ := (one_lt_inv₀ (pos_iff_ne_zero.2 ha0)).2 ha
      have ht : Filter.Tendsto (fun q : Q => q⁻¹) (𝓝 1) (𝓝 1) := by
        simpa using (continuous_inv.tendsto (1 : Q))
      filter_upwards [ht.eventually (hup _ hb)] with q hq
      rw [map_inv] at hq
      exact (inv_lt_inv₀ distribHaarChar_pos (pos_iff_ne_zero.2 ha0)).1 hq
  have hcont : Continuous Δ := continuous_of_continuousAt_one Δ hcont1
  refine ⟨⟨⟨fun q => Δ q⁻¹, by simp⟩, fun a b => by
    simp only [_root_.mul_inv_rev]
    rw [map_mul, mul_comm]⟩, hcont.comp continuous_inv, fun q => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_smul q).measurable hs]
  show _ = ((Δ q⁻¹ : ℝ≥0) • μ) s
  rw [smul_apply, ENNReal.smul_def, smul_eq_mul, Set.preimage_smul]
  exact (hmul q⁻¹ s).symm

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarModularCharacterOfContinuousActionStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_modular_character_of_continuous_action : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] (μ : Measure V) [μ.IsAddHaarMeasure] (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DistribMulAction Q V] [ContinuousSMul Q V], ∃ χ : Q →* ℝ≥0, Continuous χ ∧ ∀ q : Q, μ.map (fun v => q • v) = χ q • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_continuous_modulus_of_continuous_action | exact GlobalTheory.CompanionTheory.SW.exists_continuous_modulus_of_continuous_action | (intros; apply GlobalTheory.CompanionTheory.SW.exists_continuous_modulus_of_continuous_action <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteFieldQuadraticFormPointCount
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteFieldQuadraticFormPointCount
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.QuadricCount

open ComplexConjugate

variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def quadForm (B : Matrix ι ι k) (x : ι → k) : k :=
  (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x))

theorem quadForm_add (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k} (hB : B.IsSymm) (y z : ι → k) :
    quadForm B (y + z) = quadForm B y + quadForm B z + y ⬝ᵥ (B *ᵥ z) := by
  have hs : z ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
  unfold quadForm
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hs]
  field_simp
  ring

theorem sum_char_dot (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {w : ι → k} (hw : w ≠ 0) :
    ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  obtain ⟨c, hc⟩ := (AddChar.ne_one_iff).mp hψ
  have hi' : w i ≠ 0 := hi
  have he : (Pi.single i (c / w i) : ι → k) ⬝ᵥ w = c := by
    rw [single_dotProduct]
    field_simp
  have hS : ψ c * ∑ y : ι → k, ψ (y ⬝ᵥ w) = ∑ y : ι → k, ψ (y ⬝ᵥ w) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (Pi.single i (c / w i) : ι → k)) _ _ ?_
    intro x
    rw [Equiv.coe_addRight, add_dotProduct, he, AddChar.map_add_eq_mul, mul_comm]
  have h0 : (ψ c - 1) * ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by
    rw [sub_mul, hS, one_mul, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

theorem gauss_mul_conj (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k}
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {t : k} (ht : t ≠ 0) :
    (∑ x, ψ (t * quadForm B x)) * conj (∑ x, ψ (t * quadForm B x)) =
      (Fintype.card k : ℂ) ^ Fintype.card ι := by
  classical
  have inner : ∀ z : ι → k, ∑ y : ι → k, ψ (t * (y ⬝ᵥ (B *ᵥ z))) =
      if z = 0 then (Fintype.card k : ℂ) ^ Fintype.card ι else 0 := by
    intro z
    split_ifs with hz
    · subst hz
      simp
    · have hw : t • (B *ᵥ z) ≠ 0 := by
        intro h
        have h' : B *ᵥ z = 0 := (smul_eq_zero.mp h).resolve_left ht
        exact hz (Matrix.eq_zero_of_mulVec_eq_zero hdet h')
      have := sum_char_dot ψ hψ hw
      simpa [dotProduct_smul, smul_eq_mul] using this
  have step : ∀ y : ι → k, ∑ x, ψ (t * quadForm B x) * conj (ψ (t * quadForm B y)) =
      ∑ z, ψ (t * quadForm B z) * ψ (t * (y ⬝ᵥ (B *ᵥ z))) := by
    intro y
    refine (Fintype.sum_equiv (Equiv.addLeft y) _ _ ?_).symm
    intro z
    rw [Equiv.coe_addLeft, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, quadForm_add h2 hB]
    congr 1
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  simp_rw [step]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, inner]
  simp [quadForm]

theorem norm_gauss (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k}
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {M : ℕ} (hM : Fintype.card ι = 2 * M) {t : k}
    (ht : t ≠ 0) : ‖∑ x, ψ (t * quadForm B x)‖ = (Fintype.card k : ℝ) ^ M := by
  have h := gauss_mul_conj ψ hψ h2 hB hdet ht
  rw [Complex.mul_conj', hM] at h
  have h' : ‖∑ x, ψ (t * quadForm B x)‖ ^ 2 = ((Fintype.card k : ℝ) ^ M) ^ 2 := by
    rw [← pow_mul, mul_comm M 2]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'

theorem count_mul_card (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (B : Matrix ι ι k) (s : k) :
    (Nat.card {x : ι → k // quadForm B x = s} : ℂ) * (Fintype.card k : ℂ) =
      ∑ t : k, ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) := by
  classical
  have hprim := AddChar.IsPrimitive.of_ne_one hψ
  have h1 : ∀ x : ι → k, ∑ t : k, ψ (t * (quadForm B x - s)) =
      if quadForm B x = s then (Fintype.card k : ℂ) else 0 := by
    intro x
    rw [AddChar.sum_mulShift _ hprim]
    simp [sub_eq_zero]
  have h2 : ∑ t : k, ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) =
      ∑ x : ι → k, ∑ t : k, ψ (t * (quadForm B x - s)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [h2]
  simp_rw [h1]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero, nsmul_eq_mul]

theorem card_quadric_even (k : Type) [Field k] [Fintype k] (hchar : ringChar k ≠ 2)
    (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M)
    (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) (s : k) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 :=
    AddChar.exists_apply_ne_zero.mpr one_ne_zero
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℕ := Nat.card {x : ι → k // quadForm B x = s} with hNdef
  have hcount := count_mul_card ψ hψ1 B s
  rw [← hNdef, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at hcount
  have hzero : ψ (-((0 : k) * s)) * ∑ x, ψ ((0 : k) * quadForm B x) =
      (Fintype.card k : ℂ) ^ (2 * M) := by
    simp [hM]
  rw [hzero] at hcount
  have hbound : ‖∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x)‖ ≤
      ((Fintype.card k : ℝ) - 1) * (Fintype.card k : ℝ) ^ M := by
    have hterm : ∀ t ∈ Finset.univ.erase (0 : k),
        ‖ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x)‖ ≤ (Fintype.card k : ℝ) ^ M := by
      intro t ht
      rw [norm_mul, AddChar.norm_apply, one_mul,
        norm_gauss ψ hψ1 h2 hB hdet hM (Finset.ne_of_mem_erase ht)]
    have := norm_sum_le_of_le _ hterm
    refine this.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      nsmul_eq_mul, Nat.cast_sub Fintype.card_pos]
    simp
  have hreal : ((((N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) : ℝ)) : ℂ) =
      ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) := by
    push_cast
    rw [hcount]
    ring
  have habs : |(N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M)| ≤
      ((Fintype.card k : ℝ) - 1) * (Fintype.card k : ℝ) ^ M := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal]
    exact hbound
  have hpow : (Fintype.card k : ℝ) ^ (2 * M) =
      (Fintype.card k : ℝ) ^ (2 * M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) =
      ((N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)) * (Fintype.card k : ℝ) := by
    rw [hpow]
    ring
  rw [hfac, abs_mul, abs_of_pos hq] at habs
  have hqM : (0 : ℝ) ≤ (Fintype.card k : ℝ) ^ M := by positivity
  have hfin : |(N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| * (Fintype.card k : ℝ) ≤
      (Fintype.card k : ℝ) ^ M * (Fintype.card k : ℝ) := by
    nlinarith
  exact le_of_mul_le_mul_right hfin hq

theorem quadric_count_even : ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M :=
  fun k _ _ h ι _ _ M hM hM1 B hB hd s => card_quadric_even k h ι M hM hM1 B hB hd s

end GlobalTheory.CompanionTheory.SW.QuadricCount
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteFieldQuadraticFormPointCountStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_field_quadratic_form_point_count : ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even | exact GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even | (intros; apply GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierInversionSchwartzBruhat
section -- merged from CompanionTheory.AutomorphicTheory.ThetaDilations.WeilImplicationNonarchQuadratic
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt

open CompanionTheory.PlacePermOperatorBicommutantSpan

theorem c_fou_sb : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) :=
  fun _ _ _ _ _ _ h _ hφ => fou_sb h hφ

end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierInversionSchwartzBruhat
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.FouSB

theorem fou_sb : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_fou_sb

end GlobalTheory.CompanionTheory.SW.FouSB
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierInversionSchwartzBruhatStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_inversion_schwartz_bruhat : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FouSB.fou_sb | exact GlobalTheory.CompanionTheory.SW.FouSB.fou_sb | (intros; apply GlobalTheory.CompanionTheory.SW.FouSB.fou_sb <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuadraticSetupInvariantUnderIsometry
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuadraticSetupInvariantUnderIsometry
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem qsetup_conj_majorant (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gi : InfinitePlace F → Matrix ι ι ℝ) (h : QSetup M B ρ P)
    (hg : ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) :
    QSetup M B ρ (fun w => (gi w)ᵀ * P w * gi w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hb : ∀ w, (B.map (ρ w)).det ≠ 0 := by
    intro w
    have e : (B.map (ρ w)).det = ρ w B.det := ((ρ w).map_det B).symm
    rw [e]
    exact (map_ne_zero _).2 h4
  have hd : ∀ w, (gi w).det ≠ 0 := by
    intro w h0
    have e := congrArg Matrix.det (hg w)
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at e
    exact hb w e.symm
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · intro w
    have hinj : Function.Injective (gi w).mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hd w)))
    have := (h6 w).conjTranspose_mul_mul_same hinj
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · intro w
    set g := gi w with hgdef
    set b := B.map (ρ w) with hbdef
    have hbu : IsUnit b.det := isUnit_iff_ne_zero.2 (hb w)
    have hgw : gᵀ * b * g = b := hg w
    have e1 : (b⁻¹ * gᵀ * b) * g = 1 := by
      rw [Matrix.mul_assoc b⁻¹ gᵀ b, Matrix.mul_assoc b⁻¹, hgw,
        Matrix.nonsing_inv_mul _ hbu]
    have e2 : g * (b⁻¹ * gᵀ * b) = 1 := mul_eq_one_comm.1 e1
    have e3 : (g * b⁻¹ * gᵀ) * b = 1 := by
      rw [← e2]; simp only [Matrix.mul_assoc]
    have e4 : g * b⁻¹ * gᵀ = b⁻¹ := (Matrix.inv_eq_left_inv e3).symm
    calc gᵀ * P w * g * b⁻¹ * (gᵀ * P w * g)
        = gᵀ * P w * (g * b⁻¹ * gᵀ) * P w * g := by simp only [Matrix.mul_assoc]
      _ = gᵀ * (P w * b⁻¹ * P w) * g := by rw [e4]; simp only [Matrix.mul_assoc]
      _ = b := by rw [h7 w, hgw]

end GlobalTheory.CompanionTheory.SW.ThW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuadraticSetupInvariantUnderIsometryStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_setup_invariant_under_isometry : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (gi : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → (∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) → QSetup M B ρ (fun w => (gi w)ᵀ * P w * gi w) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.qsetup_conj_majorant | exact GlobalTheory.CompanionTheory.SW.ThW.qsetup_conj_majorant | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.qsetup_conj_majorant <;> assumption)
end
end
