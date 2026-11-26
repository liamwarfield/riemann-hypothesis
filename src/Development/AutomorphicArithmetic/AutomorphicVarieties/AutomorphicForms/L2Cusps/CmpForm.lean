module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotMk

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpForm
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.KernelIndexFullLattice

theorem cmpForm_holds : CmpForm := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ
  have hRep : (toLp μ₁ (cuspVecL μ₁ φ) : RightCosetSpace (Γ1 E a) → ℂ)
      =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] cuspQuot φ.2.1.isLeftInvariant := by
    rw [toLp_cuspVecL]
    exact coeFn_cuspToL2 μ₁ φ
  have hQuot : (cmp hp (cuspVecL μ₁ φ) : Quot (latticeGL E a) → ℂ)
      =ᵐ[quotMeasure (latticeGL E a) μ] cuspQuot φ.2.1.isLeftInvariant ∘ quotMap E a :=
    (Lp.coeFn_compMeasurePreserving _ hp).trans (hp.quasiMeasurePreserving.ae_eq_comp hRep)
  filter_upwards [ae_quotMeasure_iff.1 hQuot] with g hg
  calc
    lift (latticeGL E a) (cmp hp (cuspVecL μ₁ φ)) g =
        cuspQuot φ.2.1.isLeftInvariant (quotMap E a (mk (latticeGL E a) g)) := hg
    _ = φ.1 g := by
      rw [quotMk_holds E a g, cuspQuot_mk, coe_retractOne, ← (Reduction.centralSection E a).map_inv]
      exact apply_mul_centralSection_of_mem hφ _ _

end UpperTheory.V.KernelIndexFullLattice
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpEquiv
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem cmpEquiv_holds : CmpEquiv := by
  intro E _ _ _ a μ _ _ μ₁ _ hp g v
  have hquot (q : Quot (latticeGL E a)) :
      quotMap E a (rmul (latticeGL E a) g q) =
        RightCosetSpace.rightMul (Γ1 E a) (retractOne g) (quotMap E a q) := by
    refine Quotient.inductionOn q fun x => ?_
    simp only [rmul_mk, quotMk_holds E a, RightCosetSpace.rightMul_mk, retractOne_mul]
  have hcmp (w : CuspL2 μ₁) :
      (cmp hp w : Quot (latticeGL E a) → ℂ) =ᵐ[quotMeasure (latticeGL E a) μ]
        (toLp μ₁ w : RightCosetSpace (Γ1 E a) → ℂ) ∘ quotMap E a :=
    Lp.coeFn_compMeasurePreserving (toLp μ₁ w) hp
  have hpres := measurePreserving_rmul (Γ := latticeGL E a) (μ := μ) g
  have htranslated := hpres.quasiMeasurePreserving.ae (hcmp v)
  have hrep :
      (toLp μ₁ (cuspRepT μ₁ (retractOne g) v) : RightCosetSpace (Γ1 E a) → ℂ)
        =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] fun x =>
          (toLp μ₁ v : RightCosetSpace (Γ1 E a) → ℂ)
            (RightCosetSpace.rightMul (Γ1 E a) (retractOne g) x) := by
    rw [toLp_cuspRepT]
    exact RightCosetSpace.coeFn_rightTranslate _ μ₁ (retractOne g) (toLp μ₁ v)
  apply Lp.ext
  filter_upwards [coeFn_R g (cmp hp v), htranslated, hcmp (cuspRepT μ₁ (retractOne g) v),
    hp.quasiMeasurePreserving.ae hrep] with q hR hleft hright hrepq
  simp only [Function.comp_apply] at hleft hright
  rw [hR, hleft, hright, hrepq, hquot]

end UpperTheory.V.KernelIndexFullLattice
end
