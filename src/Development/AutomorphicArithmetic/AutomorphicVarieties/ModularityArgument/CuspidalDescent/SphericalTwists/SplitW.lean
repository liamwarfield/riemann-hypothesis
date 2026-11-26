module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.LgAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.SplitW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.MonodromyFreeOfEigenvalueRatio
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V

def UpperTheory.V.Z.Desc.W.StEq {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (ι : Qbar l ≃+* ℂ) (σ : Submodule ℂ (UA L n → ℂ))
    (ρ : G L Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (u : s.St) (τ : SmIrr (GLw n (s.w u))), ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal →
    IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) τ.ρ → ∀ rc, IsRec (s.hw u) rc →
      IsWDOf ι ρ (rc (algNorm τ))

def UpperTheory.V.Z.Desc.W.SphEq {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {n : ℕ} (ι : Qbar l ≃+* ℂ) (σ : Submodule ℂ (UA L n → ℂ)) (ρ : G L Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : Plc L, IsSplitAt w → ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (τ : SmIrr (GLw n w)) (b : Multiset ℂˣ),
    IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → GlobalTheory.LFun.HasSatGL w τ.ρ b →
      Af.FrobEig ι ρ w (Af.algSat n (normV w) b)

open UpperTheory.V.Z.Desc.W

namespace UpperTheory.V.Hi.Up

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {Q : QData V} {c : Coef l} {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r}

end UpperTheory.V.Hi.Up
