module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.KFinDecayOfDecInf
open Formalism.FourierDecayAlt.ThreeDimData

namespace GlobalTheory.GapSizeCheck

theorem decay_range (k r : ℕ) (h : ℝ) (h120 : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) :
    120 * ((2 * r + k + 1 : ℕ) : ℝ) * (((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1)) ≤ h := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs : Real.sqrt ((r : ℝ) + 1) ≤ (r : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn1 : (r : ℝ) + 1 ≤ n := by rw [hn]; push_cast; linarith
  have : ((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1) ≤ n * n :=
    mul_le_mul hn1 (hs.trans hn1) (Real.sqrt_nonneg _) (by linarith)
  nlinarith



end GlobalTheory.GapSizeCheck
end

section -- merged from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.UnimodularStandardLattice
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Survey.UnimodularStandardLattice

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
theorem mem_stdLat (v : Fin n → E) : v ∈ stdLat E n ↔ ∀ j, ∃ b : 𝓞 E, (b : E) = v j := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one]

set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma mem_range_algebraMap_iff_isIntegral_int (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma complexConj_mem_integers_iff (x : E) :
    IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range ↔
      x ∈ (algebraMap (𝓞 E) E).range := by
  rw [mem_range_algebraMap_iff_isIntegral_int, mem_range_algebraMap_iff_isIntegral_int]
  refine ⟨fun h => ?_, fun h => h.map (IsCMField.complexConj E)⟩
  simpa using h.map (IsCMField.complexConj E).symm


set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
theorem _root_.GlobalTheory.Survey.UnimodularStandardLattice.unimod_std :
    (⟨_root_.Formalism.L2.Pj.stdLat E n⟩ : _root_.Formalism.L2.Pj.GenLat E n).Unimod := by
  unfold _root_.Formalism.L2.Pj.GenLat.Unimod _root_.Formalism.L2.Pj.stdLat
  intro v
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    ← RingHom.mem_range]
  constructor
  · intro hv w hw
    exact Subring.sum_mem _ fun j _ =>
      Subring.mul_mem _ ((complexConj_mem_integers_iff (v j)).2 (hv j)) (hw j)
  · intro h i
    have hs := h (Pi.single i 1) fun j => by
      rw [Pi.single_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hs
    exact (complexConj_mem_integers_iff (v i)).1 hs


variable {H : Host E} {Dw : Datum H} {l : Level H}

end GlobalTheory.Survey.UnimodularStandardLattice
end
end
