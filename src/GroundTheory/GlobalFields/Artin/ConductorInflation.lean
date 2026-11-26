module

public import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
public import GroundTheory.GlobalFields.Artin.InflationTower

@[expose] public section

section -- merged from GroundTheory.GlobalFields.Artin.Conductor
noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

section Transport

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {L₁ : Type*} [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [Algebra F L₁] [ValuativeExtension F L₁] [FiniteDimensional F L₁] [IsGalois F L₁]
  {L₂ : Type*} [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [Algebra F L₂] [ValuativeExtension F L₂] [FiniteDimensional F L₂] [IsGalois F L₂]

end Transport

section Local

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))

theorem exists_smul_eq_of_liesOver (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] : ∃ σ : Gal(L/K), w' = σ • w := by
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal w'.asIdeal Gal(L/K)
  exact ⟨σ, HeightOneSpectrum.ext (by rw [SemiLocal.smul_asIdeal, hσ])⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end Local

section Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]




end Ideal

end GroundTheory.Global
end
end

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

section LocalInflation

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

variable {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M] [IsGalois K M] [Algebra M L]
  [IsScalarTower K M L]

end LocalInflation

section GlobalInflation

variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]

section Tower

variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 L))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal]

theorem completionMap_completionMap (a : v.adicCompletion K) :
    SemiLocal.completionMap u w (SemiLocal.completionMap v u a) =
      SemiLocal.completionMap v w a := by
  have h := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    ((SemiLocal.continuous_completionMap u w).comp (SemiLocal.continuous_completionMap v u))
    (SemiLocal.continuous_completionMap v w) (funext fun x ↦ ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply, SemiLocal.completionMap_algebraMap]
    rw [IsScalarTower.algebraMap_apply K F (u.adicCompletion F),
      SemiLocal.completionMap_algebraMap, IsScalarTower.algebraMap_apply F L (w.adicCompletion L),
      IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      ← IsScalarTower.algebraMap_apply K F L]

theorem isScalarTower_adicCompletion :
    IsScalarTower (v.adicCompletion K) (u.adicCompletion F) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun a ↦ (completionMap_completionMap v u w a).symm

attribute [local instance] isScalarTower_adicCompletion

variable [IsGalois K F] [IsGalois K L]

end Tower

variable [IsGalois K F] [IsGalois K L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end GlobalInflation

end GroundTheory.Global
