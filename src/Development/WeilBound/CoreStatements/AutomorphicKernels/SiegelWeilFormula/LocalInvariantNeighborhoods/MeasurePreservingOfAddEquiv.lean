module

public import Mathlib

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalInvariantNeighborhoods.MeasurePreservingOfAddEquiv
namespace PositivityTheory.SiegelWeilFormula.OswLocFin

open MeasureTheory

theorem measurePreserving_of_addEquiv {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    (e : G ≃+ G) (he : Continuous e) (he' : Continuous e.symm) (B : Set G) (hB : IsCompact B)
    (hB' : (interior B).Nonempty) (heB : e ⁻¹' B = B) :
    MeasureTheory.MeasurePreserving e μ μ := by
  have hm : Measurable e := he.measurable
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he he'
  obtain ⟨c, hcμ⟩ : ∃ c : NNReal, μ.map e = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map e) μ⟩
  have hBm : MeasurableSet B := hB.isClosed.measurableSet
  have hval : μ.map e B = μ B := by rw [Measure.map_apply hm hBm, heB]
  have hpos : μ B ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ hB').ne'
  have hfin : μ B ≠ ⊤ := hB.measure_lt_top.ne
  have hc : c = 1 := by
    have h1 := congrArg (fun ν : Measure G => ν B) hcμ
    simp only [Measure.smul_apply, hval, ENNReal.smul_def, smul_eq_mul] at h1
    have h2 : (c : ENNReal) * μ B = 1 * μ B := by rw [one_mul]; exact h1.symm
    have h3 : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h2
    exact_mod_cast h3
  refine ⟨hm, ?_⟩
  rw [hcμ, hc, one_smul]

end PositivityTheory.SiegelWeilFormula.OswLocFin
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalInvariantNeighborhoods.NhdsInv
namespace PositivityTheory.SiegelWeilFormula.OswLocFin

open Filter Topology

theorem exists_nhds_invariant {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {Φ : G → ℂ} (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    ∃ U ∈ nhds (0 : G), ∀ Y, ∀ Z ∈ U, Φ (Y + Z) = Φ Y := by
  obtain ⟨hlc, hcs⟩ := hΦ
  have hT : ∀ x : G, {z : G | Φ (x + z) = Φ x} ∈ 𝓝 (0 : G) := by
    intro x
    have hopen : IsOpen {z : G | Φ (x + z) = Φ x} :=
      (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
    exact hopen.mem_nhds (by simp)
  choose V₁ hV₁ hV₁s using fun x => exists_nhds_zero_half (hT x)
  choose V₂ hV₂ hV₂s using fun x => exists_nhds_half_neg (hT x)
  have hU : ∀ x : G, {y : G | y - x ∈ V₁ x ∩ V₂ x} ∈ 𝓝 x := by
    intro x
    have ht : Tendsto (fun y : G => y - x) (𝓝 x) (𝓝 (x - x)) := (continuous_sub_right x).tendsto x
    rw [sub_self] at ht
    exact ht (Filter.inter_mem (hV₁ x) (hV₂ x))
  obtain ⟨t, -, hcover⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x => {y : G | y - x ∈ V₁ x ∩ V₂ x}) (fun x _ => hU x)
  refine ⟨⋂ x ∈ t, V₁ x ∩ V₂ x, (Filter.biInter_finset_mem t).mpr fun x _ =>
    Filter.inter_mem (hV₁ x) (hV₂ x), fun Y Z hZ => ?_⟩
  have hZ' : ∀ x ∈ t, Z ∈ V₁ x ∩ V₂ x := Set.mem_iInter₂.mp hZ
  by_cases hY : Y ∈ tsupport Φ
  · obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (hcover hY)
    have hx' : Y - x ∈ V₁ x ∩ V₂ x := hx
    have h1 : Φ (x + (Y - x + Z)) = Φ x := hV₁s x _ hx'.1 Z (hZ' x hxt).1
    have h2 : Φ (x + (Y - x + 0)) = Φ x := hV₁s x _ hx'.1 0 (mem_of_mem_nhds (hV₁ x))
    rw [show x + (Y - x + Z) = Y + Z by abel] at h1
    rw [show x + (Y - x + 0) = Y by abel] at h2
    rw [h1, h2]
  · by_cases hYZ : Y + Z ∈ tsupport Φ
    · obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (hcover hYZ)
      have hx' : Y + Z - x ∈ V₁ x ∩ V₂ x := hx
      have h1 : Φ (x + (Y + Z - x - Z)) = Φ x := hV₂s x _ hx'.2 Z (hZ' x hxt).2
      have h2 : Φ (x + (Y + Z - x + 0)) = Φ x := hV₁s x _ hx'.1 0 (mem_of_mem_nhds (hV₁ x))
      rw [show x + (Y + Z - x - Z) = Y by abel] at h1
      rw [show x + (Y + Z - x + 0) = Y + Z by abel] at h2
      rw [h1, h2]
    · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYZ]

end PositivityTheory.SiegelWeilFormula.OswLocFin
end
