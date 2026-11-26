module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompat

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

namespace UpperTheory.V.Z.Ord.ExtensionCharacterAlt

section Poly

variable {C : Type*} [Field C]

end Poly

section Emb

variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]

end Emb

section Grp

variable {J T M : Type*} [Fintype J] [Fintype T] [DecidableEq T] [CommGroup M]

end Grp

section Ker

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {C : Type} [CommGroup C] [TopologicalSpace C] [T2Space C]

end Ker

section Nm

open GroundTheory.Global.SemiLocal

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {l : ℕ} [Fact l.Prime]
  {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L v)

end Nm

section Pow

variable {l : ℕ} [Fact l.Prime]

end Pow

section Const

open GroundTheory.Global.SemiLocal

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {l : ℕ} [Fact l.Prime]
  {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L v)

end Const

section Res

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω]
  [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]

end Res

end UpperTheory.V.Z.Ord.ExtensionCharacterAlt
