module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnlSph
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.RcChars
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PRepNew

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.RecSph
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af
open UpperTheory.V UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end WD

end UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.TorsionFreeOfField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpoEqZeroOfPow
open NumberField IsDedekindDomain Matrix UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc)
open UpperTheory.V.TR (infGL CuspSub)

namespace GlobalTheory.HenQ

theorem expo_eq_zero_of_pow {K : Type} [Field K] [NumberField K] [IsTotallyReal K] (ξ : Formalism.L2.Host.HChar K) {N : ℕ}
    (hN : 0 < N) (h : ξ ^ N = 1) (v : InfinitePlace K) : TR.expo ξ v = 0 := by
  classical
  have key : ∀ k : ℕ, ∀ z, TR.dchi (ξ ^ k) z = (k : ℂ) * TR.dchi ξ z := by
    intro k
    induction k with
    | zero => intro z; simp [TR.dchi_one]
    | succ k ih => intro z; rw [pow_succ, TR.dchi_mul, ih]; push_cast; ring
  have h1 := key N (Pi.single v 1)
  rw [h, TR.dchi_one] at h1
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  exact (mul_eq_zero.1 h1.symm).resolve_left hN'

end GlobalTheory.HenQ
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open UpperTheory.V UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform

local instance (priority := high + 1) torsionFreeOfField (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] :
    Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

end UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform
end
end
