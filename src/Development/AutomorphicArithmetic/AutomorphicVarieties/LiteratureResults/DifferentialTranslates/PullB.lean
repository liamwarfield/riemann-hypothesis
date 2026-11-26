module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullB
noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem pullB : PullB := by
  intro V F _ _ _ _ _ _ Y hY hC l hl q w hw
  obtain ⟨hlsm, hlpos, _⟩ := hl
  have hφY : ∀ p ∈ Y, l p • p ∈ Y := fun p hp => hC _ (hlpos p hp) p hp
  have hφ : ∀ p ∈ Y, ContDiffAt ℝ ∞ (fun x => l x • x) p := fun p hp =>
    (hlsm.contDiffAt (hY.mem_nhds hp)).smul contDiffAt_id
  have hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w (l p • p) := fun p hp =>
    hw.contDiffAt (hY.mem_nhds (hφY p hp))
  refine ⟨?_, ?_⟩
  · intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply altSmooth V V F q (pull l w) p
    intro v
    have hcomp : ContDiffAt ℝ ∞ (fun y => w (l y • y)) p :=
      ContDiffAt.comp (g := w) (f := fun x => l x • x) p (hwat p hp) (hφ p hp)
    have h := applySmooth V V F q (fun y => w (l y • y))
      (fun i y => fderiv ℝ (fun x => l x • x) y (v i)) p hcomp
      (fun i => ((hφ p hp).fderiv_right (by simp)).clm_apply contDiffAt_const)
    exact h
  · intro p hp
    exact extDeriv_pullback ((hwat p hp).differentiableAt (by simp)) (hφ p hp)
      (by simpa using (WithTop.coe_le_coe.mpr le_top : (2 : WithTop ℕ∞) ≤ ∞))

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Poincare
open UpperTheory.V.Lit.Dr
open Set ContinuousAlternatingMap
open scoped ContDiff

theorem UpperTheory.V.Lit.Dr.poincare :
    Poincare := by
  intro V F _ _ _ _ _ _ Y hY hconv q w hw hd
  rcases Y.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨0, contDiffOn_empty, fun p hp => hp.elim⟩
  have hseg : ContDiff ℝ ∞ (fun z : V × ℝ => p₀ + z.2 • (z.1 - p₀)) := by fun_prop
  set U : Set (V × ℝ) := (fun z : V × ℝ => p₀ + z.2 • (z.1 - p₀)) ⁻¹' Y with hU
  have hUo : IsOpen U := hY.preimage hseg.continuous
  have hmem : ∀ p ∈ Y, ∀ t ∈ Icc (0 : ℝ) 1, p₀ + t • (p - p₀) ∈ Y :=
    fun p hp t ht => hconv.add_smul_sub_mem hp₀ hp ht
  let Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F :=
    fun z => z.2 ^ q • (w (p₀ + z.2 • (z.1 - p₀))).curryLeft (z.1 - p₀)
  have hΦ : ContDiffOn ℝ ∞ Φ U := by
    have h1 : ContDiffOn ℝ ∞ (fun z : V × ℝ => w (p₀ + z.2 • (z.1 - p₀))) U :=
      hw.comp hseg.contDiffOn fun z hz => hz
    have h2 : ContDiffOn ℝ ∞ (fun z : V × ℝ => (w (p₀ + z.2 • (z.1 - p₀))).curryLeft) U :=
      (curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap.contDiff.comp_contDiffOn h1
    exact (contDiff_snd.pow q).contDiffOn.smul
      (h2.clm_apply (contDiff_fst.sub contDiff_const).contDiffOn)
  refine ⟨fun p => ∫ t in (0 : ℝ)..1, Φ (p, t),
    paramSmooth V _ Y U Φ hY hUo (fun z hz => hmem z.1 hz.1 z.2 hz.2) hΦ, fun p hp => ?_⟩
  obtain ⟨hc, hD⟩ := paramDeriv V _ p U Φ hUo (hmem p hp) hΦ
  have hI := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one
  have hI' := ((alternatizeUncurryFinCLM ℝ V F).continuous.comp_continuousOn hc).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) zero_le_one
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p₀ + r • (p - p₀)))
      (alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => Φ (x, t)) p)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hm := hmem p hp t ht
    exact poinPt V F q w p₀ p t
      ((hw.contDiffAt (hY.mem_nhds hm)).differentiableAt (by simp)) (hd _ hm)
  have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hI'
  rw [(alternatizeUncurryFinCLM ℝ V F).intervalIntegral_comp_comm hI, ← hD.fderiv] at h3
  refine Eq.trans h3 ?_
  simp
end
