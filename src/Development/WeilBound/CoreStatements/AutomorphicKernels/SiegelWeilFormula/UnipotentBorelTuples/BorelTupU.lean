module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.TChart
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylTheta.TWeylOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnitaryChartEquiv.CEquivApply

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnipotentBorelTuples.TranslationInvariantFunctionalHaar
noncomputable section

open scoped Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

namespace PositivityTheory.SiegelWeilFormula.TW.Twu

variable {F : Type} [Field F] [NumberField F]

theorem schr_zero_left (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (y : κ → AF F) (φ : (κ → AF F) → ℂ) :
    schr ψ (0, y) φ = fun x => ψ (x ⬝ᵥ y) * φ x := by
  funext x
  simp [schr]

theorem schr_zero_right (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (a : κ → AF F) (φ : (κ → AF F) → ℂ) :
    schr ψ (a, 0) φ = fun x => φ (x + a) := by
  funext x
  simp [schr]

theorem translation_invariant_functional_haar (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm κ)
    (hinv : ∀ a : κ → AF F, ∀ φ ∈ schA F κ, l (fun x => φ (x + a)) = l φ) :
    ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * ∫ x, φ x ∂μ := by
  obtain ⟨S, S', hS, hSf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ κ μ hμ (fun _ => 1)
  have hl' : l ∘ₗ S' ∈ (adeleClass F).adm κ := hS.adm' l hl
  have hchar : ∀ (y : κ → AF F), ∀ φ ∈ schA F κ,
      (l ∘ₗ S') (fun x => ψ (x ⬝ᵥ y) * φ x) = (l ∘ₗ S') φ := by
    intro y φ hφ
    have hφ₁m : S' φ ∈ schA F κ := hS.pres' φ hφ
    have hφeq : S (S' φ) = φ := hS.right φ hφ
    have htr : schr ψ (-y, 0) (S' φ) ∈ schA F κ := by
      rw [schr_zero_right]
      exact GlobalTheory.SchwartzTranslate.schA_translate F (-y) hφ₁m
    have key : S (schr ψ (-y, 0) (S' φ)) = fun x => ψ (x ⬝ᵥ y) * φ x := by
      rw [hS.Heisenberg₂ _ _ hφ₁m, hφeq, ← schr_zero_left]
      congr 1
      ext i <;> simp
    rw [← key, LinearMap.comp_apply, hS.left _ htr, LinearMap.comp_apply, schr_zero_right]
    exact hinv (-y) (S' φ) hφ₁m
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ (l ∘ₗ S') hl' hchar
  refine ⟨c, fun φ hφ => ?_⟩
  have h1 : l φ = (l ∘ₗ S') (S φ) := by
    rw [LinearMap.comp_apply, hS.left φ hφ]
  rw [h1, hc _ (hS.pres φ hφ), hSf φ hφ 0]
  simp

end PositivityTheory.SiegelWeilFormula.TW.Twu

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.TowU

namespace PositivityTheory.SiegelWeilFormula.TW.Twu

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open PositivityTheory.SiegelWeilFormula.TBij.Adp PositivityTheory.SiegelWeilFormula.KTunit

theorem uniq : Uniq := by
  classical
  intro F E _ _ _ _ _ σ d ν hν Λ hΛ hinv
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨τ, S0, S0', C, hop, hT⟩ := Tunit.T_chart d
  by_cases hC : C = 0
  · refine ⟨0, fun Φ hΦ => ?_⟩
    have h0 : d.T Φ = 0 := funext fun X => by rw [hT Φ hΦ X, hC, zero_mul]; rfl
    rw [(TBij.tBij F E σ d).2.2 Φ hΦ h0, map_zero, zero_mul]
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = schr d.B.ψ (c0 d τ w) (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ, LinearEquiv.symm_apply_apply]
  have rhoS' : ∀ w, ∀ φ ∈ schA F d.κ, S0' (schr d.B.ψ (c0 d τ w) φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  letI : MeasurableSpace (d.κ → AF F) := borel _
  obtain ⟨hμ, hint⟩ := map_haar d τ ν hν
  obtain ⟨c, hc⟩ := translation_invariant_functional_haar d.B.ψ hψ d.κ (ν.map (cmap d τ)) hμ (Λ ∘ₗ S0') (hop.adm' Λ hΛ) (by
    intro a φ hφ
    have e0 := coordinates_frame d τ (cinv d τ a)
    have ea : (fun k => d.crd (cinv d τ a) (τ k)) = a := cmap_cinv d τ a
    rw [ea] at e0
    rw [← schr_zero_right, ← e0, LinearMap.comp_apply, LinearMap.comp_apply, rhoS' _ φ hφ]
    exact hinv _ _ (hop.pres' φ hφ))
  refine ⟨c / C, fun Φ hΦ => ?_⟩
  have h1 := hc (S0 Φ) (hop.pres Φ hΦ)
  rw [LinearMap.comp_apply, hop.left Φ hΦ] at h1
  rw [h1, ← hint]
  have e2 : ∫ Z, d.T Φ Z ∂ν = C * ∫ Z, S0 Φ (cmap d τ Z) ∂ν := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun Z => hT Φ hΦ Z)
  rw [e2]
  field_simp

end PositivityTheory.SiegelWeilFormula.TW.Twu

end
