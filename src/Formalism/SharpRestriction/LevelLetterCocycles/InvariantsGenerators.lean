module

public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.SemisimpleDecompositionOf
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def H0FixedPoints (W : LocWach PD LL O v n) : Prop :=
  ∀ T : LocLat G Qp LL O, Nonempty (↥(invariantLattice T) ≃ₗ[O] ↥(fixDD W T))

def FontCore (W : LocWach PD LL O v n) : Prop :=
  (∀ (T T' : LocLat G Qp LL O) (f : W.DD T →ₗ[W.EE] W.DD T'),
    (∀ x, f (W.φD T x) = W.φD T' (f x)) → (∀ g x, f (W.γD T g x) = W.γD T' g (f x)) →
      ∃! F : LatHom T.L T'.L, ∀ x, W.map F x = f x) ∧
  (∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := Qp) (O := O) ι π →
    Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧
      ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x) ∧
  (∃ ψ : W.EE →ₗ[O] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧
    (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧
    (∀ j < PD.p, ∀ a, ψ (algebraMap (LetA O n) W.EE (1 + letπ) ^ j * W.φE a) = if j = 0 then a else 0) ∧
    ∀ x, ∃ c : Fin PD.p → W.EE, x = ∑ j : Fin PD.p, algebraMap (LetA O n) W.EE (1 + letπ) ^ (j : ℕ) * W.φE (c j)) ∧
  ∀ T : LocLat G Qp LL O, ∃ ψ : W.DD T →ₗ[O] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧
    (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x)

theorem herrLat_iff (W : LocWach PD LL O v n) : HerrLat W ↔
    (∀ T : LocLat G Qp LL O, Function.Surjective (W.clK T) ∧
      ∀ p, W.clK T p = 0 ↔ ∃ m : W.DD T, (∀ δ ∈ W.DelF, W.γD T δ m = m) ∧
        (p : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m)) ∧
    W.ClKNat ∧ H0FixedPoints W ∧ FontCore W := Iff.rfl

end Core

def H0InvariantsUnramified (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), H0FixedPoints ((HW l).W K 1 LL hA.2.2)

def FieldOfNormsSequence (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.HerrComplexNaturality.FN D HW F

def H0InvariantsTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FieldOfNormsSequence D HW F → H0InvariantsUnramified D HW F

def LitFont (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), FontCore ((HW l).W K 1 LL hA.2.2)

def HerrLatticeDescription (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm16 D HW F

def HerrLatticeHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F ∧ H0InvariantsUnramified D HW F ∧ LitFont D HW F

def HerrLatticeTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := HerrLatticeHypotheses D HW F → HerrLatticeDescription D HW F

theorem herr_lattice_of_fon (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrLatticeTheorem D HW F := by
  rintro ⟨h, h0, hF⟩ l _ K LL hA
  have h1 := (h l K 1 LL hA.2.2).1 (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hA.2.1)
  refine (herrLat_iff _).2 ⟨fun T => ⟨(h1 T).1, (h1 T).2.1⟩, ?_, h0 l K LL hA, hF l K LL hA⟩
  intro T T' f pr pr' hp
  exact ((h1 T).2.2 T' f pr pr' hp).symm

def LitSub (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), HerrSub ((HW l).W K 1 LL hA.2.2)

def HerrExtensionEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
    Formalism.MainNotions.tableLineDegreeTwo.HerrExt ((HW l).W K 1 LL hA.2.2) ((F l).E K 1 LL hA.2.2).tie

def HerrLatticeFurtherConditions (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm17 D HW F

theorem herr_lattice_rest_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrLatticeFurtherConditions D HW F ↔ LitSub D HW F ∧ HerrExtensionEtale D HW F :=
  ⟨fun H => ⟨fun l _ K LL hA => (H l K LL hA).1, fun l _ K LL hA => (H l K LL hA).2⟩,
    fun H l _ K LL hA => ⟨H.1 l K LL hA, H.2 l K LL hA⟩⟩

def SenOperatorLetter (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm21 D HW F

def SenOperatorTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm → SenOperatorLetter D HW F

end Formalism.MainNotions.InvariantsGenerators
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RestPt
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

structure RestPt {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop where

  ng0 : D.nd.l i ≠ D.host.g 0
  ng1 : D.nd.l i ≠ D.host.g 1

  good : GoodR D.nd i r

  chi1 : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw),
    Formalism.WeaklyAdmissibleFiltrations.IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)

  block : EmbeddingTypes.ambBlock i r ρ π

  chi : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ), 1 ≤ c → c ≤ D.R.t →
    Formalism.WeaklyAdmissibleFiltrations.IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c)))

  g3 : AbsIrreducibleDistinct D i r

  cont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))

  rho : IsRhoOf D.nd i π (ρ π)

  ss : IsSSRep (rhoChiK D i (ρ π))

  eps : TruncatedSeriesCountingIdentities.CyclotomicInertiaImage i

  shape : TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible i

end Formalism.MainNotions.N

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FiltrationPropertiesEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm

def AdmTools (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def FiltrationPropertiesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmTools D HW F Cm → FiltrationPropertiesEtale D HW F Cm

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def Pi0LatticeCondition (W : LocWach PD LL O v n) : Prop := ∀ g : W.Gam, ∃ u ∈ W.AΔ, W.γA g W.π₀ = W.π₀ * u

end Core

def GammaPreservesUniformiser (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Pi0LatticeCondition ((HW l).W K 1 LL h.2.2)

def AdmPi0 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def UniformiserGammaTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmPi0 D HW F → GammaPreservesUniformiser D HW F

def AdmSat (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def SaturationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm5 D HW F
def SaturationTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmSat D HW F → SaturationArcLifting D HW F
def SaturationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm8 D HW F
def SaturationTheoremEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmSat D HW F → SaturationEtale D HW F

def FirstFiltrationHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F ∧ Formalism.MainNotions.HerrComplexNaturality.HerrNaturality D HW F

def FirstFiltrationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm6 D HW F
def FirstFiltrationTheoremCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FirstFiltrationHypotheses D HW F → FirstFiltrationArcLifting D HW F
def FirstFiltrationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm9 D HW F
def FirstFiltrationTheoremEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FirstFiltrationHypotheses D HW F → FirstFiltrationEtale D HW F

def SecondFiltrationHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P7 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.Pr2b D HW F

def SecondFiltrationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm7 D HW F
def SecondFiltrationTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SecondFiltrationHypotheses D HW F ∧ FirstFiltrationArcLifting D HW F → SecondFiltrationArcLifting D HW F
def SecondFiltrationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm10 D HW F
def FamilyMassExplicitOfVolumeAgreement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SecondFiltrationHypotheses D HW F ∧ FirstFiltrationEtale D HW F → SecondFiltrationEtale D HW F

def KillerAtLevels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.KillerLevL D.loc D.locA HW F

def AdmKillLev (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def KillerLevelsTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmKillLev D HW F Cm → KillerAtLevels D HW F

def KillerBoundWithConstant (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm8 D HW F C

def AdmKillA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := KillerAtLevels D HW F ∧ GammaPreservesUniformiser D HW F

def KillerWithConstantTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := AdmKillA D HW F → KillerBoundWithConstant D HW F C

def KillerAtLevelsSecondForm (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm11 D HW F

def KillerWachCoordinatesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := GammaPreservesUniformiser D HW F → KillerAtLevelsSecondForm D HW F

def RelayArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm11 D HW F

def AdmRelayA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.ConclusionH D HW F ∧ Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F ∧
    SaturationArcLifting D HW F ∧ FirstFiltrationArcLifting D HW F ∧ SecondFiltrationArcLifting D HW F

def RelayTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmRelayA D HW F → RelayArcLifting D HW F

def ArcLiftingCoordinates (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm12 D HW F Cm

def AdmArcA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.ConclusionH D HW F ∧
    Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F ∧ Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ SaturationArcLifting D HW F

def ArcCoordinatesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmArcA D HW F Cm → ArcLiftingCoordinates D HW F Cm

def SplittingArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm13 D HW F Cm

def AdmSplitA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P8 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ Formalism.MainNotions.LiftingTheory.adm23 D HW F ∧
    Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass D HW F ∧ FirstFiltrationArcLifting D HW F ∧ RelayArcLifting D HW F ∧ ArcLiftingCoordinates D HW F Cm

def SplittingTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmSplitA D HW F Cm → SplittingArcLifting D HW F Cm

def UniversalComponentCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm14 D HW F Cm

def AdmUnivA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := SaturationArcLifting D HW F ∧ KillerAtLevels D HW F ∧ GammaPreservesUniformiser D HW F ∧ ArcLiftingCoordinates D HW F Cm

def H1fBaseChangeFree (D : D7) : Prop := Formalism.MainNotions.WachCoordinates.adm13 D

def H1fBaseChangeTheorem (D : D7) : Prop := H1fBaseChangeFree D

end Formalism.MainNotions.UnusedSlot80
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_letS (c : ZMod n) (x : W.DD T) : x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  unfold letS
  rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem mem_DelS (x : W.DD T) : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold DelS
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_NcS (c : ZMod n) (x : W.DD T) :
    x ∈ NcS W T c ↔ x ∈ W.N T ∧ (∀ δ ∈ W.DelF, W.γD T δ x = x) ∧ (letE c : LetA O n) • x = x := by
  unfold NcS
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, mem_DelS, mem_letS, and_assoc]

theorem mem_PiNS (π' : LetA O n) (k : ℕ) (x : W.DD T) :
    x ∈ PiNS W T π' k ↔ (∃ y ∈ W.N T, π' ^ k • y = x) ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold PiNS
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_DelS]
  unfold Formalism.MainNotions.DeltaInvariantLattices.aN
  rw [Submodule.mem_map]
  rfl

theorem mem_LamPS (Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (x : W.DD T) :
    x ∈ LamPS W T Eπ h' c ↔ Eπ ^ h' • x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1)) ∧
      (∀ δ ∈ W.DelF, W.γD T δ x = x) ∧ (letE c : LetA O n) • x = x := by
  unfold LamPS
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_comap,
    mem_DelS, mem_letS, and_assoc]
  rfl

theorem mem_InvS (π' Eπ : LetA O n) (h' k : ℕ) (c : ZMod n) (x : W.DD T) :
    x ∈ InvS W T π' Eπ h' k c ↔ x ∈ LamPS W T Eπ h' c ∧ W.γD T W.gamK x - x ∈ PiNS W T π' k := by
  unfold InvS
  rw [Submodule.mem_inf, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]

theorem PiNS_le_N (π' : LetA O n) (k : ℕ) {x : W.DD T} (hx : x ∈ PiNS W T π' k) : x ∈ W.N T := by
  obtain ⟨⟨y, hy, rfl⟩, -⟩ := (mem_PiNS W T π' k x).1 hx
  exact (W.N T).smul_mem _ hy

theorem γD_letE (g : W.Gam) (c : ZMod n) (x : W.DD T) :
    W.γD T g ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T g x := by
  rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]

theorem φD_letE (c : ZMod n) (x : W.DD T) :
    W.φD T ((letE (c - 1) : LetA O n) • x) = (letE c : LetA O n) • W.φD T x := by
  rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, Formalism.MainNotions.LiftingTheory.wmap_φA_letE]

theorem map_letA_smul {T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x :=
  Formalism.MainNotions.LiftingTheory.wmap_map_smul W f a x

theorem map_comp_zero {T' T'' : LocLat G Qp LL O} (ι : LatHom T.L T'.L) (π : LatHom T'.L T''.L)
    (h0 : ∀ y, π.f (ι.f y) = 0) (x : W.DD T) : W.map π (W.map ι x) = 0 := by
  rw [← W.map_comp]
  have hext : ∀ g₁ g₂ : LatHom T.L T''.L, g₁.f = g₂.f → g₁ = g₂ := by
    rintro ⟨f1, _, _, _⟩ ⟨f2, _, _, _⟩ h
    cases h
    rfl
  have hg : latAdd (latComp π ι) (latComp π ι) = latComp π ι := by
    apply hext
    ext y
    simp [latAdd, latComp, h0]
  have := W.map_latAdd (latComp π ι) (latComp π ι) x
  rw [hg] at this
  exact left_eq_add.mp this

end Local

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def HypB (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool)
    (size Mi hi : ZMod n → ℕ) : Prop :=
  11 ≤ PD.p ∧ TruncatedSeriesCountingBounds.HidaSetting PD W T₁ T₂ F b w S η m up size Mi hi ∧ 20 * w ≤ b ∧ 20 * η ≤ b ∧
    20 * S ≤ b ∧ ∃ i, ¬ TruncatedSeriesCountingBounds.Thick b η size i

def Alt (b η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : Prop :=
  ∀ i, up (i + 1) ≠ up i ∧
    ¬ (TruncatedSeriesCountingBounds.Thick b η size i ∧ TruncatedSeriesCountingBounds.Thick b η size (i + 1) ∧ TruncatedSeriesCountingBounds.Thick b η size (i + 2))

def One (b η R : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : Prop :=
  (∀ i, up i = up 0) ∧ ∀ i, ¬ ∀ t : ℕ, t < R → TruncatedSeriesCountingBounds.Thick b η size (i + t)

def Sg (l b w S η : ℕ) (size : ZMod n → ℕ) : ℝ :=
  (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + S + η) / l +
    Real.logb l (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 1

def bandI (l b w S η : ℕ) (size : ZMod n → ℕ) (Cb : ℝ) : ℝ :=
  if TruncatedSeriesCountingBounds.Band l b S η size (Real.logb l (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb then 1 else 0

def arcOf [NeZero n] (b w S η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : ArcLiftingSetup.ArcP n where
  G₀ := w + S
  S := S
  η := η
  h := TruncatedSeriesCountingBounds.hB b w S η size
  j := 1
  ty := fun i => if up i then .up (size i) else .down (size i)
  cuts := Finset.univ.filter fun c => ¬ TruncatedSeriesCountingBounds.Thick b η size (c + 1)
  len := fun c => sInf {d : ℕ | 1 ≤ d ∧
    ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}

def kapC (l : ℕ) (A : ArcLiftingSetup.ArcP n) (c : ZMod n) : ℕ :=
  A.len c + ∑ i ∈ (A.JS c).erase 0, (A.len c + 1 + padicValInt l i)

def ExpIn (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (Z : Finset (G → T₂.V)) (e : ℕ) : Prop :=
  ∀ c ∈ latticeFiniteCocycles PD T₂.L, ((PD.p : O) ^ e) • c ∈ F.ImF PD ⊔ Submodule.span O (Z : Set (G → T₂.V))

def ExtYCore (PD : PeriodData G Qp K₀ K B BdR) (W : LocWach PD LL O v n) : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ cc ∈ latticeFiniteCocycles PD T.L,
    ∃ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
      IsCrys PD Y.ρ ∧ Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc

end Core

structure AdmBoundsB (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR CA CB CK : ℝ) : Prop where
  p2 : Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F
  p3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm
  p4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm
  p5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F
  p9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F
  a2 : ArcLiftingSetup.adm2 D HW F CR CA CB CK
  a5 : ArcLiftingSetup.adm5 D HW F
  sP : ArcLiftingSetup.SaturationFrobeniusPullback D HW F
  kLev : ArcLiftingSetup.KillerLevL D.loc D.locA HW F
  kMod : ArcLiftingSetup.KillerModL D.loc D.locA HW F
  a9 : ArcLiftingSetup.adm9 D
  a10 : ArcLiftingSetup.adm10 D
  a11 : ArcLiftingSetup.adm11 D HW F
  a12 : ArcLiftingSetup.adm12 D HW F Cm
  a13 : ArcLiftingSetup.adm13 D HW F Cm
  a14 : ArcLiftingSetup.adm14 D HW F Cm
  a15 : ArcLiftingSetup.adm15 D

theorem admBoundsB_of_adm {D : D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {Cm : CmpOf D.loc D.locA HW F}
    {CR CA CB CK Ckap : ℝ} (h : ArcLiftingSetup.admitted D HW F Cm CR CA CB CK Ckap) : AdmBoundsB D HW F Cm CR CA CB CK :=
  ⟨fun l _ K s LL g => (h.1.1 l K s LL g).2.1, fun l _ K s LL g => (h.1.1 l K s LL g).2.2.1,
    fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.1, fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.2.1,
    fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.2.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.2.2.1, h.2.2.2.2.1.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1⟩

end Formalism.MainNotions.N.Ln17
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

def LetterConditionLocal (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (y : ℕ), 1 ≤ y →
  ∀ (dop : W.DD T →ₗ[O] W.DD T), (∀ z, W.π₀ • dop z = W.γ T z - z) →
  ∀ (cc : ℤ → O), (∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1) →
  ∀ X : Finset ℤ,
    (∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i → IsJumpV PD T.ρ τ a → 1 ≤ j → j ≤ y →
      a + (j : ℤ) ∈ X) →
    ∀ z : W.DD T, Formalism.MainNotions.LiftingTheory.InNΔi W T i (qA W ^ y • z) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T i
        (Polynomial.aeval dop (∏ x ∈ X, (Polynomial.X - Polynomial.C (cc x))) z)

def LetterConditionGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    LetterConditionLocal ((HW l).W K s LL h)

end Formalism.MainNotions.N
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.MixedPositionHypothesis
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

def quotA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L),
    IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → F.Onto →
    ∀ τ (X : Set ℤ), JumpsInV (P.PD K) T₁.ρ τ X → JumpsInV (P.PD K) T₂.ρ τ X

def normA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    (∀ τ (X : Set ℤ), JumpsInV (P.PD K) T₁.ρ τ X → JumpsInV (P.PD K) T₂.ρ τ X) →
    ∃ (η₁ h' : ℕ) (b' : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ), η₁ ≤ η ∧ h' ≤ h + S + 1 ∧
      HypN P K LL T₁ T₂ F S η₁ m h' up b'

end Local

def quotR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → quotA (D.loc l) K LL

def normR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → normA (D.loc l) K LL

def dvdR : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → eK K ∣ l - 1

def p9R (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
    ∃ (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
      (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
      Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E

def splitR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
    (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
    ∀ κ ∈ latticeFiniteCocycles ((D.loc l).PD K) T.L,
      (l ^ (rhoA l (eK K) h' + sigA l (sK l K) h') : ℕ) • κ ∈
        (⨆ c, JZ ((HW l).W K 1 LL hG) T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c) ⊔ latticeCoboundaries T.L

def univR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (S η m h' : ℕ)
      (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
      HypN (D.loc l) K LL T₁ T₂ F S η m h' up b →
      ∀ c : ZMod (finrank ℚ_[l] ↥(K0 K)), ∃ s₀ : Finset (↥(GK K) → T₂.V),
        s₀.card ≤ eK K * (eK K + 1) * m ∧
        (s₀ : Set (↥(GK K) → T₂.V)) ⊆ latticeFiniteCocycles ((D.loc l).PD K) T₂.L ∧
        ∀ x ∈ JZ ((HW l).W K 1 LL hG) T₂ π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c,
          (l ^ (sigA l (sK l K) h' + y2K l K h' S η) : ℕ) • x ∈
            F.ImF ((D.loc l).PD K) ⊔ Submodule.span ↥(OL LL) (s₀ : Set (↥(GK K) → T₂.V))

theorem YA_split (l e s h' S η : ℕ) :
    YA l e s h' S η = (rhoA l e h' + sigA l s h') + (sigA l s h' +
      (2 * sigA l s h' + kapA l e h' S + rhoA l e h' + max (2 * sigA l s h') (ycA l h' η))) := by
  unfold YA
  ring

theorem YA_mono (l e s h' S : ℕ) {η₁ η : ℕ} (h : η₁ ≤ η) : YA l e s h' S η₁ ≤ YA l e s h' S η := by
  rw [YA_split, YA_split]
  unfold ycA
  gcongr

theorem annihilation_of_scaled_spans {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] [Fintype ι] [DecidableEq M]
    (J : ι → Submodule O M) (B Im : Submodule O M) (s : ι → Finset M) (hB : B ≤ Im) (a b : ℕ) (p : M)
    (hp : a • p ∈ (⨆ c, J c) ⊔ B) (hU : ∀ c, ∀ x ∈ J c, b • x ∈ Im ⊔ Submodule.span O (s c : Set M)) :
    b • a • p ∈ Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := by
  classical
  have key : (⨆ c, J c) ≤
      (Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im).comap
        (b • LinearMap.id : M →ₗ[O] M) := by
    refine iSup_le fun c y hy => ?_
    have h1 := hU c y hy
    have hle : Im ⊔ Submodule.span O (s c : Set M) ≤
        Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := by
      refine sup_le le_sup_right (le_sup_of_le_left (Submodule.span_mono ?_))
      intro z hz
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_coe.1 hz⟩)
    show b • y ∈ (Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im)
    exact hle h1
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hp
  rw [← hxy, smul_add]
  have hx' : b • x ∈ Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := key hx
  exact Submodule.add_mem _ hx' (Submodule.mem_sup_right (nsmul_mem (hB hy) b))


set_option maxHeartbeats 2000000 in
theorem killR_of_steps (D : D7) (HW : HWOf D.loc) (hd : dvdR) (hq : quotR D) (hn : normR D)
    (h9 : p9R D HW) (hS : splitR D HW) (hU : univR D HW) : killR D := by
  classical
  unfold killR
  intro l _ hl K LL hG
  unfold killA
  intro T₁ T₂ F r S η m h up b hA
  have hjmp : ∀ τ (X : Set ℤ), JumpsInV ((D.loc l).PD K) T₁.ρ τ X → JumpsInV ((D.loc l).PD K) T₂.ρ τ X :=
    hq l hl K LL hG T₁ T₂ F hA.1 hA.2.1 hA.2.2.1
  obtain ⟨η₁, h', b', hη, hh', hN⟩ := hn l hl K LL hG T₁ T₂ F r S η m h up b hA hjmp
  have hc2 := hN.2.1
  have hj2 := hN.2.2.2.2.1
  have hηb := hN.2.2.2.2.2.1
  have hbS := hN.2.2.2.2.2.2.1
  have hh1 := hN.2.2.2.2.2.2.2.1
  obtain ⟨π', E, h9'⟩ := h9 l hl K LL hG T₂ hc2
  have hjmp2 : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro τ a ha
    have hmem := hj2 τ a ha
    have h1 := hηb τ
    have h2 := hbS τ
    rcases hmem with hmem | hmem
    · unfold deep at hmem
      split_ifs at hmem
      · obtain ⟨x1, x2⟩ := hmem
        constructor <;> omega
      · obtain ⟨x1, x2⟩ := hmem
        constructor <;> omega
    · obtain ⟨x1, x2⟩ := hmem
      constructor <;> omega
  have hSp := hS l hl K LL hG π' E h9' T₂ h' hh1 hc2 hjmp2
  choose s₀ hs₀card hs₀sub hs₀J using fun c => hU l hl K LL hG π' E h9' T₁ T₂ F S η₁ m h' up b' hN c
  have hB : latticeCoboundaries T₂.L ≤ F.ImF ((D.loc l).PD K) := by
    unfold LatHom.ImF
    exact le_sup_right
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : NeZero (finrank ℚ_[l] ↥(K0 K)) := by
    first
    | infer_instance
    | exact ⟨Module.finrank_pos.ne'⟩
    | exact ⟨(Formalism.MainNotions.N.Ln34.max_unramified_finrank_pos K).ne'⟩
    | exact ⟨(Formalism.MainNotions.N.PreambleDegrees.finrank_maxUnramifiedSubfield_padicFinExt_pos K).ne'⟩
    | (haveI := Formalism.MainNotions.WachCoordinates.Br.finiteDimensional_max_unramified K; exact ⟨Module.finrank_pos.ne'⟩)
    | (haveI := FiniteDimensional.left ℚ_[l] ↥(K0 K) ↥K.1; exact ⟨Module.finrank_pos.ne'⟩)
  refine ⟨sK l K, h', Nat.mul_div_cancel' (hd l hl K LL hG), hh1, hh', Finset.univ.biUnion s₀, ?_, ?_, ?_⟩
  · calc (Finset.univ.biUnion s₀).card ≤ ∑ c, (s₀ c).card := Finset.card_biUnion_le
      _ ≤ ∑ _c : ZMod (finrank ℚ_[l] ↥(K0 K)), eK K * (eK K + 1) * m :=
        Finset.sum_le_sum fun c _ => hs₀card c
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
        ring
  · intro x hx
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hx)
    exact hs₀sub c hc
  · intro p hp
    have hk := annihilation_of_scaled_spans _ _ _ s₀ hB _ _ p (hSp p hp) (fun c x hx => hs₀J c x hx)
    have hY : (l ^ YA l (eK K) (sK l K) h' S η₁ : ℕ) • p ∈
        Submodule.span ↥(OL LL) ((Finset.univ.biUnion s₀ : Finset _) : Set (↥(GK K) → T₂.V)) ⊔
          F.ImF ((D.loc l).PD K) := by
      rw [YA_split, pow_add, mul_comm, mul_smul]
      exact hk
    have e1 : YA l (eK K) (sK l K) h' S η =
        (YA l (eK K) (sK l K) h' S η - YA l (eK K) (sK l K) h' S η₁) + YA l (eK K) (sK l K) h' S η₁ :=
      (Nat.sub_add_cancel (YA_mono l (eK K) (sK l K) h' S hη)).symm
    rw [e1, pow_add, mul_smul]
    exact nsmul_mem hY _

end Formalism.MainNotions.N.Ln34

end
end
