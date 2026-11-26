module

public import Development.AutomorphicArithmetic.ResidueCharacters.LenUnitInvariantsLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConst
public import Development.AutomorphicArithmetic.ResidueCharacters.ConclusionSplitOfHub
public import Development.AutomorphicArithmetic.ResidueCharacters.PlaceTypeConj
public import Development.AutomorphicArithmetic.ResidueCharacters.LocAll
public import Development.AutomorphicArithmetic.ResidueCharacters.NumRow
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

theorem closed_of_all (𝒞 : FamClass) {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), P Fm CH) :
    Closed 𝒞 P :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => h Fm CH⟩⟩

end UpperTheory.N
