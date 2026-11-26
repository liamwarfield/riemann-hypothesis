module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointPurity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.NiceFour

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Af
open UpperTheory.V.Published
structure Hypotheses' : Prop where
  litN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis
  cohC : ClozelCohC
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : _root_.UpperTheory.Gal.SV.GaloisRepExistsTotallyRealGL2
  smoR : StrongMultOneReal
  gkR : GelfandKazhdanReal
  admR : AdmissibleReal
  bc : Br.QuadBC0
  newform : NewformRep
end UpperTheory.V.Af
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.CuspRep
open Formalism.MainNotions.N Polynomial
namespace UpperTheory.V.W
section Abstract
variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
variable {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (J : Ideal B.B)
end Abstract
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
variable {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid (HidaSetting.Lev.frame V) c.O n}
namespace UniversalOrdinaryDeterminantRing
variable (B : UniversalOrdinaryDeterminantRing r)
variable {B}
variable (B) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)
def PointTheoremBaseObject : Prop :=
  ∀ (x : B.Pt) (h : HidaSetting.Wt s n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), 2 ≤ n → n ≤ 4 → x.Arith h →
    x.IsRep ρ → Continuous ρ → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) →
    (∀ v : Vl l L, HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) ∧
      ∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    J ≤ RingHom.ker x
structure HidaPropsAlt (Λ : LamObj r) : Prop where
  ring : B.RingProps Λ J
  dense : B.Dense J
  pt : B.PointTheoremBaseObject ι J
  end1 : B.arithmeticPointPurityDense ι J
  end2 : B.arithmeticPointClassicalityDense ι J
  twist : B.TwistOk J
structure ModularAlt (Λ : LamObj r) : Prop extends toHidaProps : B.HidaPropsAlt ι J Λ where
  p1 : B.P1core J
  p3 : B.P3core J
end UniversalOrdinaryDeterminantRing
end U
def ModUAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 1 ≤ n → ∀ (r : Resid (HidaSetting.Lev.frame V) c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ),
      ∃ J : Ideal B.B, B.ModularAlt ι J Λ
end UpperTheory.V.W
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open UpperTheory.V.W (Plc Lp)
namespace UpperTheory.V.Z.Sym
structure AdInAlt {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)) : Prop where
  cont : Continuous r
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r
  irr : IrrOpen r
  gap : 2 ≤ m
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, r s = 1
  away : ∃ τ : Fin 2 → G L Ω →* (Qbar l)ˣ, (∀ i, Continuous (τ i)) ∧ TypeAway r τ
  above : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
    ∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
      ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
        κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k
def UnitaryThreeAutomorphyDense : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω) (N w : ℕ) (χ' η θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    FieldPairCharacterTripleConditions K L c N w χ' η θ j → χ' ≠ η → ∀ M : ℕ, M ≠ 0 → 2 * l ∣ M → UnrSplit L M →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, χ' (galEmb ℚ L Ω s) = 1) →
    ∀ B : ℕ, ∃ m ≥ B, m ≡ j [MOD l - 1] ∧ ∃ r : G L Ω →* GL (Fin 3) (Qbar l), IrrOpen r ∧
      _root_.UpperTheory.V.Sd.IsSeedAlt ι c (fun i => (![cycBar ℚ Ω l ^ j * χ', 1, (cycBar ℚ Ω l ^ j * χ')⁻¹] i).comp (galEmb ℚ L Ω))
        (fun i => (![χ', 1, χ'⁻¹] i).comp (galEmb ℚ L Ω)) ![(m : ℤ), 0, -(m : ℤ)] (cycBar L Ω l)⁻¹ r
end UpperTheory.V.Z.Sym
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsModular
noncomputable abbrev UpperTheory.V.U3.Dat.IsModularDense := @UpperTheory.V.Z.Win.Dn.IsModularA
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThmS6CoreS
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia
namespace UpperTheory.V.Aut
structure BPrime_s (K : Type) [Field K] [NumberField K] [IsCMField K] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : G ℚ Ω → Matrix (Fin 3) (Fin 3) (Qbar l)) : Prop where
  opens : ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ (eta4 Ω).ker → MatIrr U a
  cyc : MatIrr ((eta4 Ω).ker ⊓ (cycZ ℚ Ω l).ker) a
  aut : _root_.UpperTheory.V.Af.AutOnAlt K ι (-1) a
def ThmS6_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∃ g₁ : Gam Ω S, F.Marked g₁ ∧
    ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (u : Gam Ω S →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
      Module.Finite c.O (wpart c.O u 0) ∧
      ∀ (ξ : Sring (O := c.O) u →ₐ[c.O] PadicAlgCl l) (r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r → TypeI F.η r →
        _root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat
def ThmS6Core_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∃ g₁ : Gam Ω S, F.Marked g₁ ∧
    ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (u : Gam Ω S →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
      Module.Finite c.O (wpart c.O u 0) ∧
      ∀ (ξ : Sring (O := c.O) u →ₐ[c.O] PadicAlgCl l) (r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r → TypeI F.η r →
        _root_.UpperTheory.V.Af.AutOnAlt K ι (-1) fun s => (r (toGS Ω _ s)).mat
end UpperTheory.V.Aut
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SdStmt
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix
namespace UpperTheory.V.Sd
def Seed2Alt : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω) (N w : ℕ) (χ' η θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    FieldPairCharacterTripleConditions K L c N w χ' η θ j → ∀ (κ : G K Ω →* (Qbar l)ˣ) (ka : G L Ω →* (Qbar l)ˣ), IsTwist ι c κ →
    (∀ (s : G L Ω) (s' : G K Ω), galEmb ℚ L Ω s = galEmb ℚ K Ω s' → ka s = κ s') →
    ∀ B : ℕ, ∃ m ≥ B, m ≡ j [MOD l - 1] ∧ ∃ σ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous σ ∧
      Matrix.GeneralLinearGroup.det.comp σ = η * θ ∧ ResSum σ ![cycBar ℚ Ω l ^ j * χ' * η, (cycBar ℚ Ω l ^ j * χ')⁻¹] ∧
      _root_.UpperTheory.V.Sd.IsSeedAlt ι c (fun i => (![cycBar ℚ Ω l ^ j * χ', (cycBar ℚ Ω l ^ j * χ')⁻¹] i).comp (galEmb ℚ L Ω))
        (fun i => (![χ', χ'⁻¹] i).comp (galEmb ℚ L Ω)) ![(m : ℤ), -(m : ℤ)] ka (σ.comp (galEmb ℚ L Ω))
end UpperTheory.V.Sd
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutEnd2Ao
noncomputable section

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V.Z.Win UpperTheory.GalN.V UpperTheory.V.Base

namespace UpperTheory.V.Z.Win.Dn

def AutEnd2C {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ)
    (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (e : ℕ) (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A]
    (r : G ℚ Ω →* UpperTheory.V.U3.GG (m := 3) (R := A)),
    UpperTheory.V.Pr.OrdPt l η Ψ σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l),
      (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (W σ).val.trace = 0 →
      (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitAQ ι W

def AutEnd2Ao {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ)
    (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (e : ℕ) (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A]
    (r : G ℚ Ω →* UpperTheory.V.U3.GG (m := 3) (R := A)),
    UpperTheory.V.Pr.OrdPt l η Ψ σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l),
      (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (W σ).val.trace = 0 →
      (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitAQ ι W

end UpperTheory.V.Z.Win.Dn
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut
namespace UpperTheory.V.Pr
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
section Ord
variable (l : ℕ) {O : Type} [CommRing O] [IsLocalRing O] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω)
  (B : ValuationSubring Ω)
end Ord
variable {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω)
def AutEnd3Alt (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A]
    (r : G ℚ Ω →* GG (m := 3) (R := A)),
    OrdPt l η Ψ σ g₁ B r →
    (∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ η.ker → MatIrr U (mats (UnitaryThreeInertia.push A.val r))) →
    ∀ [Algebra K Ω] (ρ : G K Ω →* GL (Fin 3) (Qbar l)),
      (∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s)).mat) →
      _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw ρ (cycBar K Ω l)⁻¹)
def HostEndAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ →
  ∀ σ : G ℚ Ω, IsCC σ → ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 →
  ∃ g₁, Marks (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ ∧
    FinEnd l (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B ∧
    _root_.UpperTheory.V.Pr.AutEnd3Alt c (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B K ι
def GdEndAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ)
    (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 →
  ∃ g₁, Marks D.η D.Ψ D.cc g₁ ∧ FinEnd l D.η D.Ψ D.cc g₁ B ∧ _root_.UpperTheory.V.Pr.AutEnd3Alt c D.η D.Ψ D.cc g₁ B K ι ∧
    _root_.UpperTheory.V.Z.Win.Dn.AutEnd2Ao c D.η D.Ψ D.cc g₁ B e ι
end UpperTheory.V.Pr
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicTensorInductionOfLocalPlaces
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem neu_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L} {j : GLw n w →* UA L n}
    (hj : ∀ x ∈ locU n w, x = j (cLoc w x)) {g y : UA L n} (hg : cLoc w g = 1) (hy : y ∈ locU n w) : Commute g y := by
  have h1 : (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = 1 := by
    rw [hj _ (GlobalTheory.DefU.LocRet.ret w n g).2]
    have : cLoc w (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = cLoc w g := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl g
    rw [this, hg, map_one]
  have h2 := GlobalTheory.DefU.LocRet.commute_ret g ⟨y, hy⟩
  rwa [h1, inv_one, one_mul] at h2
private theorem ne_J {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {St : Type} [Fintype St] [DecidableEq St]
    {wt : St → Plc L} (hinj : Function.Injective fun u => (wt u).under (𝓞 (Lp L))) (j : ∀ u, GLw n (wt u) →* UA L n)
    (h1 : ∀ u g, j u g ∈ locU n (wt u)) (h2 : ∀ u g, cLoc (wt u) (j u g) = g) (h3 : ∀ u, ∀ x ∈ locU n (wt u), x = j u (cLoc (wt u) x)) :
    ∃ J : GV n wt →* UA L n, (∀ u g, J (Pi.mulSingle u g) = j u g) ∧ (∀ g, J g ∈ GlobalTheory.UnitaryBC.finU (E := L) (n := n)) ∧
      (∀ g u, cLoc (wt u) (J g) = g u) ∧
      (∀ g (v : Plc L), (∀ u, v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L))) → cLoc v (J g) = 1) ∧
      ∀ g k, (∀ u, cLoc (wt u) k = 1) → Commute k (J g) := by
  have h4 : ∀ u g (v : Plc L), v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L)) → cLoc v (j u g) = 1 := fun u g v hv =>
    GlobalTheory.DefU.LocRet.mem_locU_ne (h1 u g) hv
  have hc : Pairwise fun a b => ∀ x y, Commute (j a x) (j b y) := fun a b hab x y =>
    neu_comm (h3 b) (h4 a x _ fun e => hab (hinj e).symm) (h1 b y)
  let J := MonoidHom.noncommPiCoprod j hc
  have hJ : ∀ u g, J (Pi.mulSingle u g) = j u g := fun u g => MonoidHom.noncommPiCoprod_mulSingle j u g
  have key : ∀ P : Subgroup (UA L n), (∀ u g, j u g ∈ P) → ∀ g, J g ∈ P := fun P hP g => by
    have : J.range ≤ P := by
      rw [MonoidHom.noncommPiCoprod_range]
      exact iSup_le fun u => by rintro _ ⟨g, rfl⟩; exact hP u g
    exact this ⟨g, rfl⟩
  refine ⟨J, hJ, key _ fun u g => (h1 u g).1, fun g u => ?_, fun g v hv => key (cLoc v).ker (fun u g => h4 u g v (hv u)) g,
    fun g k hk => ?_⟩
  · have : (cLoc (wt u)).comp J = Pi.evalMonoidHom (fun u => GLw n (wt u)) u := MonoidHom.pi_ext fun i x => by
      rw [MonoidHom.comp_apply, hJ, Pi.evalMonoidHom_apply]
      by_cases h : u = i
      · subst h
        rw [h2, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]
        exact h4 i x _ fun e => h (hinj e)
    exact DFunLike.congr_fun this g
  · exact (Subgroup.mem_centralizer_singleton_iff.1
      (key (Subgroup.centralizer {k}) (fun u g => Subgroup.mem_centralizer_singleton_iff.2
        (neu_comm (h3 u) (hk u) (h1 u g)).symm.eq) g)).symm
private theorem automorphic_tensor_induction_of_local_places {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n m : ℕ}
    {St : Type} {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))
    (j : ∀ u, GLw n (wt u) →* UA L n) (J : GV n wt →* UA L n)
    (hJ : ∀ u g, J (by classical exact MonoidHom.mulSingle (fun u => GLw n (wt u)) u g) = j u g)
    (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) (hT : _root_.UpperTheory.V.Hi.IsTypeAlt ht τ₀ χ)
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) (τ : ∀ u, SmIrr (GLw n (wt u)))
    (hτ : ∀ u, IsoSum ((RU L n).comp (j u)) σ (τ u)) (F : Fin m → UA L n → ℂ) (hF0 : F ≠ 0) (hF1 : ∀ i, F i ∈ σ)
    (hF2 : ∀ (k : KT n wt) i, ∑ a, τ₀ k i a • RU L n (J k) (F a) = F i) :
    ∀ u rc, _root_.UpperTheory.Zero.LLC.IsRecT (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (τ u))) := by
  haveI : Nontrivial σ := Submodule.nontrivial_iff_ne_bot.2 hσ.ne_bot
  let ρ : Representation ℂ (GV n wt) σ :=
    (⟨σ, fun g v hv => hσ.stable (J g) v hv⟩ : Subrepresentation ((RU L n).comp J)).toRepresentation
  have hρ : ∀ g (y : σ), (ρ g y : UA L n → ℂ) = RU L n (J g) y := fun _ _ => rfl
  refine (hT.2 σ ρ τ fun u => ?_).1 ⟨fun i => ⟨F i, hF1 i⟩, fun h => hF0 (funext fun i => congrArg Subtype.val (congrFun h i)),
    fun k i => Subtype.ext ?_⟩
  · refine UpperTheory.isoSum_of_injective_equivariant_family _ _ _ _ _ ⊤ σ (τ u) Unit (fun _ => σ.subtype) (hτ u) (fun _ _ _ => Submodule.mem_top)
      (fun _ y _ => y.2) (fun _ g y _ => ?_) fun y _ h => Subtype.ext (h ())
    exact (hρ _ y).trans (by rw [hJ]; rfl)
  · change σ.subtype (∑ a, τ₀ k i a • ρ k ⟨F a, hF1 a⟩) = F i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hF2 k i]
    rfl
theorem UpperTheory.V.Hi.partUR2Type_alt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ →
    ∀ τ : ∀ u : s.St, SmIrr (GLw n (s.w u)), (∀ u : s.St, IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) (τ u).ρ) → ∀ (u : s.St) rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (τ u))) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ he σ hσ hY χ hT τ hτ
  letI : DecidableEq s.St := fun a b => Classical.propDecidable _
  obtain ⟨hw, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  choose j h1 h2 _ h3 using fun u : s.St => (secU l L Ω s n hn (wt s u) (hsp _ (by
    rw [hw]
    exact s.split _ (Or.inr (Or.inl u.2))))).1
  obtain ⟨J, hJ, j1, j2, j3, -⟩ := ne_J (wt := wt s)
    (fun a b hab => Subtype.ext ((hw _).symm.trans (hab.trans (hw _)))) j h1 h2 h3
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hFσ⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have f1 := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ he _ fun _ => rfl).1
  have hex : ∃ i ℓ, toForm ι e (F i) ℓ ≠ 0 := by
    by_contra h
    exact hF0 (funext fun i => f1 (F i) (hB.1 i trivial) fun ℓ => by
      by_contra h'
      exact h ⟨i, ℓ, h'⟩)
  obtain ⟨i₀, ℓ, hℓ⟩ := hex
  have j4 : ∀ g (v : Plc L), v.under (𝓞 (Lp L)) ∉ s.St → cLoc v (J g) = 1 := fun g v hv =>
    j3 g v fun a h => hv (by rw [h, hw]; exact a.2)
  refine automorphic_tensor_induction_of_local_places (fun u : s.St => s.hw u) j J (fun u g => ?_) _ χ hT hσ τ
    (fun u => UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ (j u) (h1 u) (h2 u) (h3 u) (τ u) (hτ u)) (fun i => toForm ι e (F i) ℓ)
    (fun h => hℓ (congrFun h i₀)) (fun i => hFσ i ℓ) fun k i => ?_
  · exact hJ u g
  · refine partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ he F hB (J k) (j1 _) (fun v => j4 _ _ ?_) k (fun u => (j2 _ u).symm) ?_
      (fun w hw' => ?_) (fun q => j4 _ _ fun h => Q.notS q (Or.inr (Or.inl h))) i ℓ
    · rw [hw]
      exact fun h => s.St_l _ h v.2
    · rw [j4 _ _ (by rw [hw]; exact s.v0_St)]
      exact one_mem _
    · rw [j4 _ _ fun h => hw' (V.sub (Or.inr (Or.inl h)))]
      exact one_mem _
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PlDefs
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd
namespace UpperTheory.V.Z.Sym.Pl
def LinkedEndEAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N), 1 ≤ e → Even N →
  ∀ (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), l * N ∣ M →
    (∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ η.ker → B'.valuation (M : Ω) < 1) →
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), B.valuation (l : Ω) < 1 → Φ.Ok C₀ → Φ.Big C₀ →
    Pr.SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    Pr.FinPt c.O Φ 3 ∧ _root_.UpperTheory.V.Pr.AutPtAlt k 3 ι (cycBar L Ω l)⁻¹ ∧ ∃ ka, Sd.IsAlgChar ι ka ∧ _root_.UpperTheory.V.Pr.AutPtAlt k 2 ι ka
end UpperTheory.V.Z.Sym.Pl
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceSmall
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp
private theorem charpoly_flag' {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) : (Pr.gm r s).charpoly = Pr.chPoly κ s := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (Pr.gm r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]
theorem UpperTheory.V.Th.nice_zero_of_rank_two_or_three_irreducible_free :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r} (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), (n = 2 ∨ n = 3) → _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ → U3.MatIrr ⊤ (W.mat ρ) → Th.Free V.frame (fun v => x.psi v) → (∃ v a b g, r.psib v a g ≠ r.psib v b g) → _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B ι x ρ hn hA hirr hfree ⟨v, hne⟩
  have hp : n.Prime := by
    rcases hn with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  have h3 : n ≤ 3 := by omega
  obtain ⟨-, A, _, j, φ, hj, hred, hlift⟩ := Th.Det.redB x ρ hA.rep
  haveI : V.frame.G'.Normal := MonoidHom.normal_ker _
  haveI : CompactSpace V.frame.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ V.frame.η_open).isCompact
  have key := Th.Det.irrSmall hp V.frame.G' ρ j φ r.chib (V.frame.φ v) (x.psi v) (r.psib v) hirr hj hred
    (hA.flag v) (hlift v) (hfree v) hne
  refine ⟨hA, hfree, ?_, ?_⟩
  · have h := key ⊤ (by simp)
    rwa [top_inf_eq] at h
  · obtain ⟨g, hg, hfr⟩ := hfree v
    exact Th.Det.n3small h3 V.frame.G' ρ hA.cont key
      ⟨V.frame.φ v g, hg, fun i => x.psi v i g, hfr, charpoly_flag' _ _ (hA.flag v) g⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeForUp
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace UpperTheory.V.Hi.LvR
section Gen
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))
end Gen
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))
variable (Q0 : QData V0) (Q : QData V) (hS : V0.S' ⊆ V.S')
theorem type_for_r_up_of_type_for (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ht : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt (rUp h) ι τ₀ := by
  intro t' ht'
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  have hk : ∀ i, (p0 h).ker ≤ (t' i).ker := fun i g hg => by
    refine teich_ext _ _ ?_ (ht' i g).2 (one_pow _)
    rw [(ht' i g).1, rUp_chib, MonoidHom.mem_ker.1 hg, map_one]
    simp
  let t : Fin n → V0.frame.G₀ →* c.Oˣ := fun i => (p0 h).liftOfSurjective (surjective_levelChangeBaseGroupHom h) ⟨t' i, hk i⟩
  have e : ∀ i g, t i (p0 h g) = t' i g := fun i g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have := ht t fun i g => by
    obtain ⟨x, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    rw [e, ← rUp_chib]
    exact ht' i x
  have e2 : ∀ (u : s.St) i, (t' i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype) =
      (t i).comp (V0.pr.comp (Ine (F := L) (s.A u)).subtype) := fun u i => MonoidHom.ext fun x =>
    (e i (V.pr x)).symm.trans (congrArg (t i) (levelChangeBaseGroupHom_apply_projection h hp x))
  simp only [e2]
  exact this
end UpperTheory.V.Hi.LvR
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceFour
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp
private theorem exists_place_above_prime_alt (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  haveI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) (Ideal.span {(l : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (RingHom.injective_int _)]; exact bot_le)
  have hm : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hl.out.ne_zero (by exact_mod_cast hm)
private theorem charpoly_eq_prod_flag_characters {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) :
    (W.mat r s).charpoly = ∏ i, ((X : Polynomial k) - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (W.mat r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  refine h3.trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]
private theorem continuous_linear_closed {G κ : Type} [TopologicalSpace G] [Field κ] [TopologicalSpace κ] [IsTopologicalRing κ] [T1Space κ] {n : ℕ}
    (a : G → Matrix (Fin n) (Fin n) κ) (ha : Continuous a) : Pr.LinClosed a := by
  intro f
  have h : (fun g => f (a g)) = fun g => ∑ i, ∑ j, a g i j * f (Matrix.single i j 1) := by
    funext g
    conv_lhs => rw [Matrix.matrix_eq_sum_single (a g)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul]
    simp
  have hc : Continuous fun g => f (a g) := by
    rw [h]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (ha.matrix_elem i j).mul continuous_const
  exact isClosed_singleton.preimage hc
private theorem absolute_irreducible_rank_four (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (two : (2 : ResidueField O) ≠ 0) (χ : Fin 4 → F.G₀ →* (ResidueField O)ˣ)
    (K : Type) [Field K] [IsAlgClosed K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K] (twoK : (2 : K) ≠ 0)
    (ρ : F.G₀ →* GL (Fin 4) K) (hρ : Continuous ρ) (hb : U3.MatIrr ⊤ (W.mat ρ))
    (A : Type) [CommRing A] (j : A →+* K) (φ : A →+* ResidueField O) (hj : Function.Injective j) (hred : Pr.RedTo ρ j φ χ)
    (u : F.G₀) (hg : u ∈ F.G') (a : Fin 4 → Kˣ) (hu : (W.mat ρ u).charpoly = ∏ i, (X - C (a i : K))) (hfr : Pr.FreeRatios a)
    (hc : ∀ η : F.G₀ →* (ResidueField O)ˣ, η ^ 2 = 1 → (F.eps O (ResidueField O)).ker ≤ η.ker → (∀ i, ∃ j, η * χ i = χ j) → η = 1)
    (hd : ∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (χ i / χ j) ^ n ≠ 1) : Th.TypeI F ρ ∧ Th.N3 F ρ := by
  classical
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  haveI hN : F.G'.Normal := MonoidHom.normal_ker _
  have hm : Continuous (W.mat ρ) := Units.continuous_val.comp hρ
  have hfa : ∀ s t, s ≠ t → ¬ IsOfFinOrder (a s / a t) := fun s t hst h => by
    obtain ⟨m, hm0, hm1⟩ := isOfFinOrder_iff_pow_eq_one.1 h
    rw [div_pow, div_eq_one] at hm1
    exact hfr s t hst m hm0 hm1
  have hsep := Ws.charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder _ 4 _ a hu hfa
  have hcomm : commutator F.G₀ ≤ F.G' := Abelianization.commutator_subset_ker _
  have hI : Th.TypeI F ρ := by
    by_contra hI
    obtain ⟨V, S, hV0, hV1, hNS, hS, hSi⟩ := Ws.exists_stabilizer_index_dvd_of_not_irreducible_restriction K F.G₀ 4 (W.mat ρ) hb F.G' hcomm
      ⟨_, hg, by simpa using hsep 1 one_pos⟩ hI
    obtain ⟨η, hη, hSη, hcp⟩ := Ws.exists_sign_twist_charpoly_of_not_irreducible_restriction K F.G₀ twoK (W.mat ρ) hb S (hcomm.trans hNS) hSi fun h =>
      (h V fun s hs => (hS s).1 hs).elim hV0 hV1
    haveI : S.FiniteIndex := ⟨fun h => by simp [h] at hSi⟩
    have hSo : IsOpen (S : Set F.G₀) := by
      refine S.isOpen_of_isClosed_of_finiteIndex ?_
      have h1 := Ws.isClosed_setOf_matrix_stabilizes_submodule F.G₀ K 4 _ (continuous_linear_closed _ hm) V
      convert h1 using 1
      ext s
      exact hS s
    have hk := Ws.sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit l hl F.G₀ (F.ε.comp F.η.ker.subtype) (F.ε_cont.comp continuous_subtype_val) η
      (Subgroup.isOpen_mono hSη hSo) (hNS.trans hSη)
    have h1 := hc (W.pushCh (Int.castRingHom (ResidueField O)) η) ?_ ?_
      (Th.Det.perm4 K (ResidueField O) A F.G₀ 4 ρ j φ χ η hj hred hcp)
    · refine hη (MonoidHom.ext fun s => ?_)
      rcases Int.units_eq_one_or (η s) with h | h
      · exact h
      · have h2 := congrArg Units.val (DFunLike.congr_fun h1 s)
        simp only [MonoidHom.comp_apply, h] at h2
        exact absurd (by simp at h2; linear_combination -h2) two
    · ext s
      rcases Int.units_eq_one_or (η s) with h | h <;> simp [h]
    · intro s hs
      have h2 : η s = 1 := hk s fun h => by
        have h3 := h.map ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O))
        have h4 : ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O)) ((F.ε.comp F.η.ker.subtype) s : ℤ_[l]) = 1 :=
          congrArg Units.val (MonoidHom.mem_ker.1 hs)
        rw [map_sub, h4, map_one, sub_self] at h3
        exact not_isUnit_zero h3
      simp [MonoidHom.mem_ker, h2]
  refine ⟨hI, ?_⟩
  have hsp : Submodule.span K (Set.range ((W.mat ρ).comp F.G'.subtype)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hI N fun s hs => hN ⟨s, hs⟩
  have hsp' : Submodule.span K (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hb N fun s _ => hN s
  have hnc := Ws.exists_noncommuting_images_in_finiteIndex_normal_subgroup K (ResidueField O) A F.G₀ (W.mat ρ) j φ χ hj hred hsp' hd F.G' _ hg hsep
  refine Ws.exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex F.G₀ F.G' (fun s => (W.mat ρ s).charpoly.Separable) fun V hV σ => ?_
  exact AlgebraTools.regCosetFour K F.G' twoK ((W.mat ρ).comp F.G'.subtype)
    (fun f => isClosed_singleton.preimage (f.continuous_eval.comp
      (continuous_pi fun p => (hm.comp continuous_subtype_val).matrix_elem p.1 p.2)))
    hsp ⟨⟨_, hg⟩, a, hu, hfa⟩ (fun N _ h2 h3 => hnc N h2 h3) V hV σ
theorem UpperTheory.V.Th.nice0four_alt :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {r : W.Resid V.frame c.O 4} {B : W.UniversalOrdinaryDeterminantRing r} (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin 4) (Qbar l)), _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ → U3.MatIrr ⊤ (W.mat ρ) → Th.Free V.frame (fun v => x.psi v) → (∀ η : V.frame.G₀ →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (V.frame.eps c.O (ResidueField c.O)).ker ≤ η.ker → (∀ i, ∃ j, η * r.chib i = r.chib j) → η = 1) → (∃ i j, ∀ m : ℕ, 0 < m → m ≤ 4 → (r.chib i / r.chib j) ^ m ≠ 1) → _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ := by
  intro l hl L Ω _ _ _ _ _ _ s V c r B ι x ρ hA hb hF hc hd
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (Base.dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  have two : (2 : ResidueField c.O) ≠ 0 := fun h =>
    s.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 (by exact_mod_cast h)))
  obtain ⟨w⟩ : Nonempty V.frame.Vl := (exists_place_above_prime_alt (W.Lp L) l).elim fun v hv => ⟨⟨v, hv⟩⟩
  obtain ⟨g, hg, hfr⟩ := hF w
  obtain ⟨-, A, _, j, φ, hj, hred, -⟩ := Th.Det.redB x ρ hA.rep
  obtain ⟨h1, h2⟩ := absolute_irreducible_rank_four l s.odd V.frame c.O two r.chib (Qbar l) two_ne_zero ρ hA.cont hb A j φ hj hred _ hg _
    (charpoly_eq_prod_flag_characters _ _ (hA.flag w) g) hfr hc hd
  exact ⟨hA, hF, h1, h2⟩
end
end
