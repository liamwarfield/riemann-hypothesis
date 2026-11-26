module

public import GroundTheory.GlobalFields.Artin.LogCharpoly

@[expose] public section

section -- merged from GroundTheory.GlobalFields.Artin.InflationTower
noncomputable section

open IsDedekindDomain NumberField
open scoped Pointwise

namespace GroundTheory.Global

section Average

variable {G H : Type*} [Group G] [Group H]

end Average

variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [IsGalois K F] [IsGalois K L]


omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in
theorem algebraMap_restrictNormalHom_smul (σ : Gal(L/K)) (x : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F σ • x) =
      σ • algebraMap (𝓞 F) (𝓞 L) x := by
  apply RingOfIntegers.coe_injective
  change algebraMap F L ((σ.restrictNormal F) (x : F)) = σ (algebraMap F L (x : F))
  exact AlgEquiv.restrictNormal_commutes σ F x








theorem IsArithFrobAt.restrictNormalHom {φ : Gal(L/K)} {Q : Ideal (𝓞 L)}
    (h : IsArithFrobAt (𝓞 K) φ Q) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom F φ) (Q.under (𝓞 F)) := by
  intro x
  rw [Ideal.under_under]
  change algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F φ • x -
    x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) ∈ Q
  rw [map_sub, map_pow, algebraMap_restrictNormalHom_smul]
  exact h _

end GroundTheory.Global
end
end

section -- merged from GroundTheory.GlobalFields.Artin.Places
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField

namespace GroundTheory.Global.Artin

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

instance : MulAction Gal(L/K) (HeightOneSpectrum (𝓞 L)) where
  smul σ w := ⟨σ • w.asIdeal, Ideal.IsPrime.smul σ, fun h ↦ w.ne_bot (by
    rw [← inv_smul_smul σ w.asIdeal, h, Ideal.smul_bot])⟩
  one_smul w := HeightOneSpectrum.ext (one_smul _ w.asIdeal)
  mul_smul σ τ w := HeightOneSpectrum.ext (mul_smul σ τ w.asIdeal)

end Action

section FixedField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))

end FixedField

section Finite

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))




end Finite

end GroundTheory.Global.Artin
end
end
