module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdVan2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FlagWD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocCharDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanKeep
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Hi
section Type_
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {St : Type} {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))
def IsTypeAlt {m : ℕ} (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) : Prop :=
  IsOpen (τ₀.ker : Set (KT n wt)) ∧
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [Nontrivial M] (ρ : Representation ℂ (GV n wt) M) (σ : ∀ u, SmIrr (GLw n (wt u))),
    (∀ u, IsoSum (M := M) (by classical exact ρ.comp (MonoidHom.mulSingle (fun u => GLw n (wt u)) u)) ⊤ (σ u)) →
    ((∃ F : Fin m → M, F ≠ 0 ∧ ∀ (k : KT n wt) i, ∑ j, τ₀ k i j • ρ k (F j) = F i) ↔
      ∀ u rc, _root_.UpperTheory.Zero.LLC.IsRecT (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (σ u))))
end Type_
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
namespace CaseU
variable (l L) (n : ℕ)
variable {l L}
variable (s : HidaSetting l L Ω)
variable {s} (V : s.Lev)
variable {V} (Q : QData V)
variable {n} {c : Coef l} {m : ℕ}
variable (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ)
def TypeForAlt (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : Prop :=
  ∀ t, r.IsTeich t → _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u)
    ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀)
    fun u i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))
variable (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
structure UnitaryPointProperties (lam : Wt L l n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop where
  form : ∃ P, V.frame.IsForm c.O n ρ P
  type : ∀ t, r.IsTeich t → ∀ u : s.St, ∃ g : GL (Fin n) (Qbar l), ∀ x ∈ V.frame.Iu u,
    ((g * ρ x * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Matrix.diagonal fun i => algebraMap c.O (Qbar l) (t i x)
  cusp : Af.IsIrr ρ → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (ρ.comp V.pr) π ∧ HasWt ι s π lam
  aut : ∃ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ ∧ (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ) ∧
    (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) ∧
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) ∧
    (∀ w, IsSplitAt w → ∃ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
    ∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧
      fixd τ.ρ (Kc _ n 1) ≠ ⊥
variable {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
variable {r} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)
structure UnitaryHeckeData : Type where
  m : ℕ
  τ₀ : KT n (wt s) →* GL (Fin m) c.O
  type : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀
  θ : (hset Q τ₀).X.I.T →* Λ.Λˣ
  theta : IsTheta Q τ₀ Λ θ
  isWt : (hset Q τ₀).IsWt θ
  a : (hset Q τ₀).Op → c.O
  res : IsRes Q r τ₀ a
variable {Q ι Λ} (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev)
abbrev UnitaryHeckeData.M := (hset Q R.τ₀).MK R.θ R.a K
def UnitaryHeckeData.IsJ (J : Ideal B.B) : Prop := (hset Q R.τ₀).IsJ R.θ R.a K B.u.D B.u.ψ (Λ.toPair B.u) J
end CaseU
end UpperTheory.V.Hi
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.W UpperTheory.V.Ws.Eb
namespace UpperTheory.V.Th
section Abstract
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {K : Type} [Field K] {n : ℕ}
end Abstract
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} {B : UniversalOrdinaryDeterminantRing r}
structure AutomorphicPointGalois (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous ρ
  rep : x.IsRep (ρ.comp V.pr)
  arith : ∃ h, x.Arith h
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (ρ.comp V.pr)
  unr0 : ∀ g ∈ V.frame.I0, ρ g = 1
  flag : ∀ v : V.frame.Vl, HasFlag (ρ.comp (V.frame.φ v)) (x.psi v)
structure AutomorphicPointLocallyGeneric (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop extends toAPt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ where
  free : Free V.frame fun v => x.psi v
  irr : TypeI V.frame ρ
  n3 : N3 V.frame ρ
end U
def DenseThresholdMainCase : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 2 ≤ n → n ≤ 4 → ∀ (r : Resid V.frame c.O n), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
      (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ → OrdZero r ρ fun v => x.psi v
def AdjointLiftingTheorem : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 2 ≤ n → n ≤ 4 → ∀ (r : Resid V.frame c.O n), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
      (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ → Par x → AdZero V ρ
end UpperTheory.V.Th
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.Top
namespace UpperTheory.V.Aut
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
def IsAut4Alt (ι : PadicAlgCl l ≃+* ℂ) (r : G ℚ Ω →* M4 (PadicAlgCl l)) : Prop := _root_.UpperTheory.V.Z.Win.IsAutQA ι r.toHomUnits
def SymplecticFourImageDense : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t →
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → OfCase D h e ψ →
      D.Fin0 ∧ D.NoEnd ∧ ∃ ι : PadicAlgCl l ≃+* ℂ, D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι)
end UpperTheory.V.Aut
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V.Af
namespace UpperTheory.GalN.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
section Conv
variable {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
theorem mkCsd'_alt [IsCMField F] (h : AutCsd0 ι r) (u : Continuous r → _root_.UpperTheory.V.Z.Win.WitA ι r) : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r := ⟨h, u⟩
theorem autCsd0_of_isAutCsdA [IsCMField F] (h : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) : AutCsd0 ι r := h.1
omit [NumberField F] in
theorem isAutomorphicOverImagQuad_of_isAutQA (h : _root_.UpperTheory.V.Z.Win.IsAutQA ι r) : IsAutomorphicOverImagQuad ι r := fun hc K _ _ _ _ _ _ h2 hi => (h hc K h2 hi).1
omit [NumberField F] in
theorem isAutQA_of_isAutomorphicOverImagQuad_of_witAQ (h : IsAutomorphicOverImagQuad ι r) (u : Continuous r → _root_.UpperTheory.V.Z.Win.WitAQ ι r) : _root_.UpperTheory.V.Z.Win.IsAutQA ι r :=
  fun hc K _ _ _ _ _ _ h2 hi => ⟨h hc K h2 hi, u hc K h2 hi⟩
end Conv
end UpperTheory.GalN.V
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsSeed
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
namespace UpperTheory.V.Sd
section Sym
variable (R : Type) [CommRing R]
variable {Γ k : Type} [Group Γ] [Field k]
end Sym
section Cong
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {n : ℕ}
end Cong
section Gal
variable {Ω : Type} [Field Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
variable {F : Type} [Field F] [NumberField F] [Algebra F Ω]
variable [CharZero Ω] [IsAlgClosure ℚ Ω]
structure IsSeedAlt {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω)
    (ψ τ : Fin n → G L Ω →* (Qbar l)ˣ) (m : Fin n → ℤ) (ka : G L Ω →* (Qbar l)ˣ) (r : G L Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  irr : IsIrr r
  pair : ∃ P : GL (Fin n) (Qbar l), (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∧ IsPair c r 1 P
  res : ResSum r ψ
  away : TypeAway r τ
  above : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → OrdAt r m ψ A
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw r ka)
end Gal
end UpperTheory.V.Sd
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAutI
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg
open IsLocalRing Matrix Formalism.MainNotions.N GlobalTheory.GalOfCusp
namespace UpperTheory.V.U3
namespace Dat
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)
def IsAutIAlt [IsCMField K] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l))
    (hr : HasMult D.η r) : Prop :=
  _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (D.rhoK r hr) (cycBar K Ω l)⁻¹)
end Dat
end UpperTheory.V.U3
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointClassicality
noncomputable abbrev UpperTheory.V.W.UniversalOrdinaryDeterminantRing.arithmeticPointClassicalityDense := @UpperTheory.Gal.projectedFormsSystemPart.IrrArithPointsAutomorphicAway
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfBridge
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
namespace UpperTheory.V.Af
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
def AutOnAlt (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Qbar l ≃+* ℂ) (j : ℤ)
    (a : G ℚ Ω → Matrix (Fin n) (Fin n) (Qbar l)) : Prop :=
  ∃ (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω) (ρ : G K Ω →* GL (Fin n) (Qbar l)),
    (∀ s : G K Ω, (ρ s : Matrix (Fin n) (Fin n) (Qbar l)) = a (s.restrictScalars ℚ)) ∧ _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw ρ (cycBar K Ω l ^ j))
end UpperTheory.V.Af
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrDesc
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
namespace UpperTheory.V.Pr
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
def AutPtAlt (k : GalLink η Ψ σ g₁ B M L Φ) (n : ℕ) (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] [IsLocalHom (algebraMap c.O A)]
    (ρ : Fr.NRep Φ n A), IsLiftA c.O ρ →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g).val = algebraMap c.O A (Ψ (k.j v g) ^ Fr.w n i).val) →
    ∀ r : G L Ω →* GL (Fin n) (Qbar l), (∀ s, (r s).val = (ρ.r (k.p0 s)).map A.val) → IsIrr r → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw r ka)
end
end UpperTheory.V.Pr
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedRig
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
namespace UpperTheory.V.Th
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
def RigPtAlt (k : GalLink η Ψ σ g₁ B M L Φ) (n : ℕ) (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] [IsLocalHom (algebraMap c.O A)]
    (ρ : Fr.NRep Φ n A), IsLiftA c.O ρ →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g).val = algebraMap c.O A (Ψ (k.j v g) ^ Fr.w n i).val) →
    ∀ r : G L Ω →* GL (Fin n) (Qbar l), (∀ s, (r s).val = (ρ.r (k.p0 s)).map A.val) → IsIrr r → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw r ka) →
      FreeAt l r → RigOver r ka
end
def RigPtOfAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (_ : CReal k c₁ f n ka), W.Large L c₁ → IsKa σ M ι n ka → _root_.UpperTheory.V.Th.RigPtAlt k n ι ka
def LinkedRigAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → Φ.Big C₀ →
    SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    _root_.UpperTheory.V.Th.RigPtAlt k 3 ι (cycBar L Ω l)⁻¹ ∧ ∃ ka, IsKa σ M ι 2 ka ∧ _root_.UpperTheory.V.Th.RigPtAlt k 2 ι ka
end UpperTheory.V.Th
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdVan2
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open UpperTheory.V.HV GlobalTheory.GalOfCusp
namespace UpperTheory.V.Th
def OrdVan2Alt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
    (x : B.Pt) (h : s.Wt n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), V.S' = s.S → 2 ≤ n → n ≤ 4 →
    r.V0ok → x.Arith h → x.D = GDet.ofRep (mat ρ) → Continuous ρ → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (ρ.comp V.pr) →
    Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → V.frame.IsForm c.O n ρ P → (∀ g ∈ V.frame.I0, ρ g = 1) →
    (∀ (v : Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    RegDet V.frame c.O ρ P → ∀ z, IsOrdCoc V.frame ρ P r.Ip x.psi z → ∃ Y, ∀ g, z g = dY V.frame (mat ρ) Y g
end UpperTheory.V.Th
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocFlagWD
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Loc.flag_weil_deligne_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → FlagWD := by
  intro hN L Ω _ _ _ _ _ l _ _ ι n w hw A h a ha r hr hh ω ψ hψ ⟨M, hM⟩ HT P hD O _ _ _ Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨d, hJ, -⟩ := hD O Bw hj
  have hc := fun i => (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hN h hw ι a ha (ω i) (hh i) (ψ i) (hψ i)).1 O Bw hj
  obtain ⟨F₁, F₂⟩ := UpperTheory.V.Loc.PstExact.flag T ι Bw h hj r (fun i => GlobalTheory.TripleGal.rk1 (ψ i)) M
    (fun g => (hM g).1) (fun g i => ((hM g).2 i).trans (by simp [GlobalTheory.TripleGal.rk1]))
  refine ⟨d, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
  · have e := F₁ τ _ _ (hJ τ LL' τ' hτ) fun i => (hc i).2.1 τ LL' τ' hτ
    have e' : (Finset.univ.val.map fun j => hh j τ) = HT τ := by
      rw [e, Finset.sum, ← Multiset.sum_map_singleton (Finset.univ.val.map fun j => hh j τ), Multiset.map_map]
      rfl
    beta_reduce
    rw [e']
    exact hJ τ LL' τ' hτ
  · rw [(F₂ (hN.aut.berger.isPstAt T Bw r (Units.continuous_val.comp hr) d)).2 s]
    exact Finset.prod_congr rfl fun i _ => (hc i).2.2 s
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnramifiedOfSplitDistinctCharacters
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
theorem UpperTheory.V.Z.Sym.Al.unramified_of_split_distinct_characters :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (ψ : Fin n → (Kw w)ˣ →* ℂˣ), IsSplitAt w → CompSub π w ψ →
        (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) → (∀ i i', i ≠ i' → ψ i ≠ ψ i' ∧ ψ i ≠ ψ i' * absPow (Kw w) 1) → IsUnramU π w := by
  intro H L _ _ _ n π w ψ hw hc hu hne
  obtain ⟨hsm, τ, ⟨-, f, hf0, hfπ, hf⟩, hsq⟩ := hc
  obtain ⟨hs1, hs2, -, -⟩ := secSpec L n w hw
  have hker : ∀ x, f x = 0 → x = 0 := by
    let S : Subrepresentation τ.ρ := ⟨LinearMap.ker f, by
      intro g x hx
      have h := hf ⟨secW n w g, hs1 g⟩ x
      have h' : f (τ.ρ g x) = RU L n (secW n w g) (f x) := by
        rw [← h]
        show f (τ.ρ g x) = f (τ.ρ (cLoc w (secW n w g)) x)
        rw [hs2 g]
      rw [LinearMap.mem_ker] at hx ⊢
      rw [h', hx, map_zero]⟩
    have hS : S = ⊥ := by
      rcases (τ.irred.eq_bot_or_eq_top S) with h | h
      · exact h
      · refine absurd (LinearMap.ext fun x => ?_) hf0
        have : x ∈ S.toSubmodule := by rw [h]; trivial
        exact this
    intro x hx
    have : x ∈ S.toSubmodule := hx
    rw [hS] at this
    exact this
  obtain ⟨ω, rfl, hω⟩ : ∃ ω : Fin n → (Kw w)ˣ →* ℂˣ,
      ψ = (fun i => ω i * absPow (Kw w) (((n : ℂ) - 1) / 2)) ∧ ∀ i, IsSmoothChar (ω i) := by
    refine ⟨fun i => ψ i * absPow (Kw w) (-(((n : ℂ) - 1) / 2)), funext fun i => ?_,
      fun i => (hsm i).mul (isSmoothChar_of_isUnram (isUnram_absPow _ _))⟩
    have h0 : absPow (Kw w) 0 = 1 := by
      ext x
      simp [absPow]
    rw [mul_assoc, ← absPow_add, neg_add_cancel, h0, mul_one]
  have hneω : ∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow (Kw w) 1 := fun i j hij =>
    ⟨fun h => (hne i j hij).1 (by simp only [h]), fun h => (hne i j hij).2 (by
      simp only []
      rw [h, mul_right_comm])⟩
  have hE : Nonempty (τ.ρ.Equiv (UpperTheory.V.Hi.PS ω)) :=
    (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient H (Kw w) n ω hω hneω).2 _ τ.ρ τ.irred hsq
  obtain ⟨E⟩ := hE
  obtain ⟨v₀, hv₀, hfix⟩ := locSph (Kw w) n _ hu
  obtain ⟨v, rfl⟩ := E.surjective v₀
  have hv : v ≠ 0 := by
    rintro rfl
    exact hv₀ (map_zero E)
  have hτ : ∀ u ∈ KO (Kw w) (Fin n), τ.ρ u v = v := fun u hu' => by
    apply E.injective
    have h1 := LinearMap.congr_fun (E.isIntertwining' u) v
    exact h1.trans (hfix u hu')
  refine ⟨f v, hfπ v, fun h => hv (hker v h), fun x hx hK => ?_⟩
  have h := hf ⟨x, hx⟩ v
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL] at hK
  rw [← h]
  show f (τ.ρ (cLoc w x) v) = f v
  rw [hτ _ hK]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroSDefs
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
def Step_spCount_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ c : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (c i)) → (∀ i, res (c i) = res (G.chi i)) →
    FiniteDimensional ℂ ↥(G.etaSp (jacU G.e (prinSeries c))) ∧
      Module.finrank ℂ ↥(G.etaSp (jacU G.e (prinSeries c))) ≤ 1
def Step_spOrd_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → ∀ c : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (c i)) →
    ∀ σ : Equiv.Perm (Fin n), IsSubquotient π (prinSeries (fun i => c (σ i))) → IsSubquotient π (prinSeries c)
def Step_spPiSub_alt : Prop :=
  _root_.UpperTheory.TNZ.Grp.Step_spOrd_alt (k := k) (n := n) → _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis →
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
    (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) →
    ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, IsSmoothChar (ν a j)) →
    (∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) →
    (multiProd G.e (G.twD τ)).IsIrreducible →
    IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries (G.cOf ν))
def Step_spSupp_alt : Prop :=
  _root_.UpperTheory.TNZ.Grp.Step_spOrd_alt (k := k) (n := n) → _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) →
      ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, IsSmoothChar (ν a j)) →
      (∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) →
      IsSubquotient (piTensor τ) (jacU G.e π) → IsSubquotient π (prinSeries (G.cOf ν))
def Step_spTop_alt : Prop :=
  SpecialLatticeProp → G.SphericalVectorUniqueness → G.Step_spCount_alt → G.SpecialLiftProp → G.NonzeroBasicTwistOfSpecialForm → G.SpecialRestrictionProp → G.SpecialRepresentationEtaProp →
    _root_.UpperTheory.TNZ.Grp.Step_spOrd_alt (k := k) (n := n) → G.Step_spPiSub_alt → G.Step_spSupp_alt → _root_.UpperTheory.TNZ.Step_cuspSupp_alt → _root_.UpperTheory.TNZ.Step_prodIrr_alt → TensorProductVectors →
    G.Step_suppProd_alt
end Grp
end UpperTheory.TNZ
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPCuspSupp
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.CuspidalSupport₂
variable {k : Type} [Field k]
end UpperTheory.TNZ.CuspidalSupport₂
namespace UpperTheory.TNZ
open CuspidalSupport₂ in
theorem step_cuspSupp_alt : _root_.UpperTheory.TNZ.Step_cuspSupp_alt := by
  intro hL k _ _ _ _ d X _ _ σ hs hi η hη hdv
  obtain ⟨v, hv0, hv⟩ := hdv
  set τ := twist σ (detChar (Fin d) η⁻¹) with hτ
  have hτs : IsSmooth τ := isSmooth_twist hs hη.inv.detChar
  have hτi : τ.IsIrreducible := isIrreducible_twist hi _
  have hadm : IsAdmissible τ := (hL.bz k).1 (Fin d) X τ hτs hτi
  have hI : fixed τ (iwahori k (Fin d)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    have hg := hv h.1 (iwahori_le_KO k _ h.2)
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    show (detChar (Fin d) η⁻¹ h.1 : ℂ) • σ h.1 v = v
    rw [hg, smul_smul, detChar_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul]
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm hτi hI
  let χ : Fin d → kˣ →* ℂˣ := fun i => unrChar k (α i)
  have h1 := hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k d χ)
  have h2 := isSubquotient_twist h1 (detChar (Fin d) η)
  rw [hτ, twist_twist_inv] at h2
  have hχs : ∀ i, IsSmoothChar (χ i) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar (k := k) (α i))
  let φ := multiProdTwistEquiv (Equiv.sigmaUnique (Fin d) fun _ => Fin 1)
    (fun i => detRep (Fin 1) (χ i)) hη
  have h3 := h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hfam : (fun i => twist (detRep (Fin 1) (χ i)) (detChar (Fin 1) η)) =
      fun i => detRep (Fin 1) (η * χ i) := funext fun i => twist_detRep_one _ _
  rw [hfam] at h3
  refine ⟨fun j => η * χ j, fun j => ⟨hη.mul (hχs j), fun u hu => ?_⟩, hi,
    fun j => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hη.mul (hχs j))⟩, _, h3⟩
  show η u * unrChar k (α j) u = η u
  rw [isUnram_unrChar (k := k) (α j) u hu, mul_one]
end UpperTheory.TNZ
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPProdIrr
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
namespace UpperTheory.TNZ.ProductIrreducible₂
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem isIrreducible_multiProd_stdBlocks_of_ne_on_units (hL : _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) k) (X b)),
      (∀ b, IsSmooth (σ b)) → (∀ b, (σ b).IsIrreducible) → ∀ η : Fin s → kˣ →* ℂˣ,
      (∀ b c, b ≠ c → ∃ u : kˣ, valuation k (u : k) = 1 ∧ η b u ≠ η c u) →
      ∀ μ : ∀ b, Fin (d b) → kˣ →* ℂˣ,
      (∀ b j, IsSmoothChar (μ b j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ b j u = η b u) →
      (∀ b, IsCuspSupport (σ b) (fun _ => 1) (fun j => detRep (Fin 1) (μ b j))) →
        (multiProd (stdBlocks d hd) σ).IsIrreducible := by
  intro s
  induction s with
  | zero =>
    intros
    exact GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _
  | succ s ih =>
    intro N d hd X _ _ σ hs hi η hη μ hμ hcs
    have e : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ _)
    subst e
    obtain ⟨E⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hτi : (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ).IsIrreducible :=
      ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs _) (fun i => hi _)
        (fun i => η i.succ) (fun b c hbc => hη _ _ fun h => hbc (Fin.succ_injective _ h))
        (fun i => μ i.succ) (fun i => hμ _) (fun i => hcs _)
    have hτs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ) :=
      isSmooth_parInd _ _
    obtain ⟨h', x, hx, hxc⟩ := GlobalTheory.LocGL.SupportRing.hasSupport_multiProd hL.zel (d := fun i : Fin s => d i.succ) rfl
      (fun i => σ i.succ) (fun i => hs _) (fun i => hi _) (fun i => hasSupport_of_isCuspSupport (hcs i.succ)) hτi
    have hP := hL.disj k (d 0) (∑ i : Fin s, d i.succ) (d 0) h'
      { V := X 0, π := σ 0, smooth := hs 0, irr := hi 0 }
      { V := _, π := multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ, smooth := hτs,
        irr := hτi }
      (fun _ => 1) (fun b => (x b).1) (fun a => GlobalTheory.SplitRead.Irr.ofDet 1 (μ 0 a) (hμ 0 a).1)
      (fun b => GlobalTheory.SplitRead.Irr.ofIrrRep (x b).2.rep) (hcs 0) hxc ?_
    · exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hP
    · intro a b hab j _ hφ
      have hxb : x b ∈ ∑ i : Fin s, Finset.univ.val.map fun a =>
          IrrGL.of (detRep (Fin 1) (μ i.succ a)) ((hcs i.succ).2.1 a).2.2.1 ((hcs i.succ).2.1 a).2.1 := by
        rw [← hx]
        exact Multiset.mem_map_of_mem x (Finset.mem_univ_val b)
      obtain ⟨c, -, hc⟩ := Multiset.mem_sum.1 hxb
      obtain ⟨j', -, hj'⟩ := Multiset.mem_map.1 hc
      obtain ⟨u, hu, hne⟩ := hη 0 c.succ (Fin.succ_ne_zero c).symm
      apply hne
      rw [← (hμ 0 a).2 u hu, ← (hμ c.succ j').2 u hu]
      exact eq_on_units (x b) hab (μ 0 a) (μ c.succ j') (hμ 0 a).1 _ _ hj' j hφ u hu
end UpperTheory.TNZ.ProductIrreducible₂
namespace UpperTheory.TNZ
theorem step_prodIrr_alt : _root_.UpperTheory.TNZ.Step_prodIrr_alt := by
  unfold _root_.UpperTheory.TNZ.Step_prodIrr_alt
  intro hC hL k _ _ _ _ s N d hd X _ _ σ hs hi η hη hdv hne
  have H := fun b => hC hL k (d b) (X b) (σ b) (hs b) (hi b) (η b) (hη b) (hdv b)
  choose μ hμ hcs using H
  exact _root_.UpperTheory.TNZ.ProductIrreducible₂.isIrreducible_multiProd_stdBlocks_of_ne_on_units hL s N d hd X σ hs hi η hne μ hμ hcs
end UpperTheory.TNZ
end
end
end
