module

public import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ExportFamilies
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero
public import Formalism.SharpRestriction.LevelLetterCocycles.Step1KillXList
public import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmaDN0OfAdmits
public import Formalism.SharpRestriction.LevelLetterCocycles.WachQuotientCyclicDecomposition

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingAll
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
    (W : LocWach PD LL O v n)


open Classical in
def SecondPropositionRingInput (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Prop :=
  IsUnit (algebraMap (LetA O n) W.EE π') ∧ IsUnit (algebraMap (LetA O n) W.EE Eπ) ∧
  (∃ g ∈ W.AΔ, W.γA W.gamK π' = π' * g) ∧
  ∃ ν ∈ W.AΔ, ν * W.γA W.gamK (Eπ ^ h') = Eπ ^ h' ∧
  ∃ (N : ℕ) (f : ℕ → LetA O n) (cc : ℕ → O),
    (∀ k, f k ∈ W.AΔ) ∧
    (letE c : LetA O n) * ∏ k ∈ Finset.range N, f k = (letE c : LetA O n) * (π' * Eπ ^ (2 * h')) ∧
    (∀ k < N, ∀ a ∈ W.AΔ, ∃ (a₀ : O) (b : LetA O n), b ∈ W.AΔ ∧
      (letE c : LetA O n) * a = (letE c : LetA O n) * (algebraMap O (LetA O n) a₀ + f k * b)) ∧
    (∀ k < N, ∀ a ∈ W.AΔ, ∃ b ∈ W.AΔ,
      (letE c : LetA O n) * (ν * W.γA W.gamK ((∏ j ∈ Finset.range k, f j) * a) -
          algebraMap O (LetA O n) (cc k) * ((∏ j ∈ Finset.range k, f j) * a)) =
        (letE c : LetA O n) * ((∏ j ∈ Finset.range (k + 1), f j) * b)) ∧
    ((Finset.range N).filter fun k => cc k = 1).card ≤ finrank K₀ K + 1

end Local

def secondPropositionRingAll (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ c, SecondPropositionRingInput ((HW l).W K 1 LL hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def SecondRingHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → secondPropositionRingAll D HW

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ThetaScalarFamilyOfEigenvalue
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions Filter Topology

theorem export_link_of_family {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TwistedPlaces.OrbitValuationBound Fm) : LinkN Fm := by
  obtain ⟨C, x0, hx⟩ := h
  refine ⟨C, x0, fun x hx0 i hsha j hj hS => ?_⟩
  have hp := hx x hx0 i
  unfold TwistedPlaces.aux₃ at hp
  exact hp hsha hS j hj

theorem linkN_of {eps : ℝ} (Fm : FamP eps) (hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm) (hS : Formalism.MainNotions.TwistedPlaces.KudlaFamilyStatement Fm) :
    LinkN Fm := export_link_of_family Fm (hS hA)

def ThetaScalarNonzero (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ D.what₂.isot j σ,
    D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = lam • f

theorem thetaT_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) (hI : DirectSum.IsInternal (D.what₂.isot j))
    (h : ThetaScalarNonzero D μ j) : Function.Injective (D.what₂.thetaT μ j) := by
  classical
  choose lam hlam0 hlam using h
  set T : Module.End ℂ (D.what₂.Mj j) := (D.what₂.thetaP μ j).comp (D.what₂.thetaT μ j) with hTdef
  have hsub : ∀ σ, D.what₂.isot j σ ≤ Module.End.eigenspace T (lam σ) := by
    intro σ f hf
    rw [Module.End.mem_eigenspace_iff]
    exact hlam σ f hf
  have htop : (⊤ : Submodule ℂ (D.what₂.Mj j)) ≤ ⨆ (c : ℂ) (_ : c ≠ 0), Module.End.eigenspace T c := by
    rw [← hI.submodule_iSup_eq_top]
    refine iSup_le fun σ => le_trans (hsub σ) ?_
    exact le_iSup₂_of_le (lam σ) (hlam0 σ) le_rfl
  have hind : iSupIndep (Module.End.eigenspace T) := by
    first
      | exact Module.End.eigenspaces_iSupIndep T
      | exact Module.End.eigenspaces_independent T
  have hdis : Disjoint (Module.End.eigenspace T 0) ⊤ := (hind 0).mono_right htop
  have hker : LinearMap.ker T = ⊥ := by
    rw [← Module.End.eigenspace_zero]
    exact disjoint_top.mp hdis
  have hTinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
  exact Function.Injective.of_comp (f := D.what₂.thetaP μ j) hTinj

def LamPos (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT,
    (∀ f ∈ D.what₂.isot j σ, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = ((D.what₂.lamP μ j σ : ℝ) : ℂ) • f) ∧
    (D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ)

end Formalism.MainNotions.N

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FinLev
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def FinLev (W : LocWach PD LL O v n) : Prop :=
  ∀ (a : ZMod n) (e : ℕ) (H : ℕ → ℕ), ∃ D : ℕ, ∀ u ∈ W.AΔ, ∃ (c : Fin D → O) (w : LetA O n),
    w ∈ W.AΔ ∧ (letE a : LetA O n) * u =
      letE a * ∑ j : Fin D, algebraMap O (LetA O n) (c j) * W.π₀ ^ (j : ℕ) +
        W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * (letE a * w)

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.StrictSesLetter
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.Strict

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

section Funct

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (f : V →ₗ[LL] V')

theorem crisMap_mulVB (c : K₀) (z : V ⊗[Qp] B) :
    crisMap B f (mulVB (LL := LL) (V := V) (B := B) c z) = mulVB (LL := LL) (V := V') (B := B) c (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [crisMap, mulVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_DcrisL_iff (τ₀ : K₀ →ₐ[Qp] LL) (z : V ⊗[Qp] B) :
    z ∈ DcrisL PD ρ τ₀ ↔ z ∈ Dcris PD ρ ∧ ∀ c : K₀, mulVB (LL := LL) (V := V) (B := B) c z = τ₀ c • z := by
  simp [DcrisL, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

end Funct

section SES

variable {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end SES

section P4Y

variable {PD} {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end P4Y

section Rec

theorem p4YL (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F) :
    Formalism.MainNotions.ArcLiftingSetup.AtCaseA fun l _ K LL hG => Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hG) := by
  intro l _ K LL hG hCA h5
  exact hL l K LL hCA h5

end Rec

end Formalism.MainNotions.UnusedSlot80.Strict

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ExistsGoodPlacesEveryConjugate
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions.N.TwAll

section Conj

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem psiAt_side_zpow {Γ A : Type} [Group Γ] [CommGroup A] (b b' : Bool) (ψ : Γ →* A) (a : ℤ) :
    ∃ a' : ℤ, a'.natAbs = a.natAbs ∧ Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b' (ψ ^ a) = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ ^ a') := by
  cases b <;> cases b'
  · exact ⟨a, rfl, rfl⟩
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · exact ⟨a, rfl, rfl⟩

end Conj

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def TwGoodAll (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) → TwGoodOne D I i b Q k' (ψ ^ a)

def rawPack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D := ⟨C.twI w, C.Q w, C.k' w, C.psi' w⟩

def IntegralHeckeEveryConjugate (D : D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.pin bkP) i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp E i j b (IntegralHeckeForms.SgJ D.nexp E i j b)) →
    ∀ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b),
      (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) (S j b)) →
    ∀ A : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ),
      ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) →
        IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.pin bkP) E N0 i eps' S A Q k' (ψ' ^ a)

end Formalism.MainNotions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Kill

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end Kill

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section C6

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end C6

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.LatticeVariant

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}



end All

end Formalism.MainNotions.LatticeVariant

namespace Formalism.MainNotions.IntegralHeckeForms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}


variable (Y) in
def goodTwistExistsAllCoprimePowers (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    ∀ a : ℤ, a.natAbs.Coprime (X.l i) → GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

end All

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

end Formalism.MainNotions

namespace Formalism.MainNotions.N.TwAll

open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

section Tame

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

end Tame

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.N.TwAll

section DensityAveraging

variable {D : D7}

end DensityAveraging

end Formalism.MainNotions.N.KillingConditions

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RToolModDStab
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section DStab

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem γD_smul' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  show W.γD T g (a • x) = letγ (W.γ₀ g) a • W.γD T g x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

theorem rToolMod_geom (a : LetA O n) (m : ℕ) : ∃ g : LetA O n, (1 + a) ^ m = 1 + a * g := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨1 + g + a * g, by rw [pow_succ, hg]; ring⟩

theorem rToolMod_unit (hπ : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1))
    (t : LetA O n) (m : ℕ) : IsUnit ((1 + W.π₀ * t) ^ m) := by
  obtain ⟨w, hw⟩ := hπ
  have hp : 2 ≤ PD.p := by
    by_contra h
    have hv := W.v_l
    rcases (show PD.p = 0 ∨ PD.p = 1 by omega) with h0 | h0 <;> rw [h0] at hv
    · rw [Nat.cast_zero, AddValuation.map_zero] at hv
      exact WithTop.top_ne_coe (show (⊤ : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) from hv)
    · rw [Nat.cast_one, AddValuation.map_one] at hv
      have h01 : ((0 : ℚ) : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) := hv
      exact absurd (WithTop.coe_inj.mp h01) (by norm_num)
  have hp1 : PD.p - 1 ≠ 0 := by omega
  refine IsUnit.pow m ?_
  refine Pi.isUnit_iff.mpr fun i => ?_
  refine PowerSeries.isUnit_iff_constantCoeff.mpr ?_
  simp [hw, letπ, zero_pow hp1]

theorem rToolMod_qi_q (hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (m : ℕ)
    (x : W.DD T) :
    Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ m • (Formalism.MainNotions.LiftingTheory.qp W ^ m • x) = x := by
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ m) x, smul_smul, map_pow, ← mul_pow,
    Ring.inverse_mul_cancel _ hqU, one_pow, one_smul]

theorem rToolMod_dStab [NeZero n] (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) : DerivationPreservesQLattice W := by
  unfold DerivationPreservesQLattice
  intro hA T' hT i k x hx
  obtain ⟨hbij, hs, hp2⟩ := hA
  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hbij).finrank_eq, Module.finrank_self]
  obtain ⟨-, -, h9⟩ := hP9 T' hT hs hp2
  obtain ⟨hring, hmod⟩ := h9 hfin
  obtain ⟨-, hmod2⟩ := hmod
  obtain ⟨hπΔ, -, ⟨w₁, hw₁⟩, -, -, -, ⟨w₂, hw₂⟩, -⟩ := hring
  have hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := hπΔ
  have hEat : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      Formalism.MainNotions.LiftingTheory.qp W := by
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp]
  have hγπ : W.γA W.gam W.π₀ = W.π₀ + (w₂ : LetA O n) * W.π₀ * Formalism.MainNotions.LiftingTheory.qp W := by
    rw [← hEat, ← hw₂]; ring
  have hγq : W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      Formalism.MainNotions.LiftingTheory.qp W * (1 + W.π₀ * (w₂ : LetA O n)) := by
    have e1 : W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) = W.γA W.gam W.π₀ + ((PD.p : ℕ) : LetA O n) := by
      simp only [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast]
    rw [e1, hγπ]
    simp only [Formalism.MainNotions.LiftingTheory.qp]
    ring
  have hΔq : ∀ δ ∈ W.DelF, W.γA δ (Formalism.MainNotions.LiftingTheory.qp W) = Formalism.MainNotions.LiftingTheory.qp W := by
    intro δ hδ
    simp only [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast, hΔπ δ hδ]
  have ha : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw₁, map_mul, map_pow]
    exact (w₁.isUnit.map _).mul (W.EE_π.pow _)
  have hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
    haveI := W.EE_complete
    have hI : ((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) ∈
        Ideal.span {((PD.p : ℕ) : W.EE)} := Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    have hJ : ((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) ∈
        (⊥ : Ideal W.EE).jacobson := by
      first
        | exact IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)}) hI
        | exact IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)}) hI
        | exact HenselianRing.jac (I := Ideal.span {((PD.p : ℕ) : W.EE)}) hI
    have h1 := Ideal.mem_jacobson_bot.mp hJ 1
    have hinv := Ring.mul_inverse_cancel _ ha
    have h2 : algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W) = algebraMap (LetA O n) W.EE W.π₀ *
        (((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) * 1 + 1) := by
      simp only [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast]
      linear_combination (-((PD.p : ℕ) : W.EE)) * hinv
    rw [h2]; exact ha.mul h1
  obtain ⟨e, he⟩ : ∃ e, e = Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := ⟨_, rfl⟩
  have hcan1 : ∀ z : W.DD T', W.π₀ • (e • z) = z := by
    intro z
    rw [he, ← algebraMap_smul W.EE W.π₀, smul_smul, Ring.mul_inverse_cancel _ ha, one_smul]
  have hcan2 : ∀ z : W.DD T', e • (W.π₀ • z) = z := by
    intro z
    rw [he, ← algebraMap_smul W.EE W.π₀ z, smul_smul, Ring.inverse_mul_cancel _ ha, one_smul]
  have hinj : ∀ z₁ z₂ : W.DD T', W.π₀ • z₁ = W.π₀ • z₂ → z₁ = z₂ := by
    intro z₁ z₂ h; rw [← hcan2 z₁, h, hcan2]
  have hcomm : ∀ (b : LetA O n) (z : W.DD T'), b • (e • z) = e • (b • z) := by
    intro b z
    rw [← algebraMap_smul W.EE b (e • z), ← algebraMap_smul W.EE b z, smul_smul, smul_smul, mul_comm]
  have hγE : ∀ δ ∈ W.DelF, W.γE δ e = e := by
    intro δ hδ
    have h3 : W.γE δ (algebraMap (LetA O n) W.EE W.π₀) = algebraMap (LetA O n) W.EE W.π₀ := by
      rw [W.γE_ext]; exact congrArg (algebraMap (LetA O n) W.EE) (hΔπ δ hδ)
    rw [he]
    calc W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀))
        = W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)) *
          (algebraMap (LetA O n) W.EE W.π₀ * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)) := by
          rw [Ring.mul_inverse_cancel _ ha, mul_one]
      _ = W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) * algebraMap (LetA O n) W.EE W.π₀) *
          Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := by rw [map_mul, h3]; ring
      _ = Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := by
          rw [Ring.inverse_mul_cancel _ ha, map_one, one_mul]
  have hγsm : ∀ (g : W.Gam) (b : LetA O n) (z : W.DD T'),
      W.γD T' g (b • z) = W.γA g b • W.γD T' g z := γD_smul' W T'
  have hdOp : ∀ z, Formalism.MainNotions.CrystallineLiftingInputs.dOp W T' z = e • (W.γD T' W.gam z - z) := fun z => by rw [he]; rfl
  have hγy : ∀ (m : ℕ) (z : W.DD T'), W.γD T' W.gam (Formalism.MainNotions.LiftingTheory.qp W ^ m • z) =
      (1 + W.π₀ * (w₂ : LetA O n)) ^ m • (Formalism.MainNotions.LiftingTheory.qp W ^ m • W.γD T' W.gam z) := by
    intro m z
    rw [hγsm, map_pow, hγq, mul_pow, smul_smul, mul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ m)]
  obtain ⟨⟨hEx, hΔx⟩, hq⟩ := hx
  have hγE_i : W.γA W.gam (letE i : LetA O n) = letE i := by
    funext j
    show W.γ₀ W.gam ((letE i : LetA O n) j) = (letE i : LetA O n) j
    simp only [letE, Pi.single_apply]
    split_ifs <;> simp
  unfold Formalism.MainNotions.CrystallineLiftingInputs.InQN Formalism.MainNotions.CrystallineLiftingInputs.DL
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hEγ : (letE i : LetA O n) • W.γD T' W.gam x = W.γD T' W.gam x := by
      rw [← hγE_i, ← hγsm, hEx]
    rw [hdOp, hcomm, smul_sub, hEγ, hEx]
  · intro δ hδ
    rw [hdOp, W.γD_smul, hγE δ hδ, map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hΔx δ hδ]
  · split_ifs at hq ⊢ with hk
    · obtain ⟨g, hg⟩ := rToolMod_geom (W.π₀ * (w₂ : LetA O n)) k.toNat
      have hu := rToolMod_unit W ⟨w₁, hw₁⟩ (w₂ : LetA O n) k.toNat
      have hpg : W.π₀ * ((w₂ : LetA O n) * g) = (1 + W.π₀ * (w₂ : LetA O n)) ^ k.toNat - 1 := by
        rw [hg]; ring
      have hyΔ : Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x ∈ W.NΔ T' :=
        show Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x ∈ W.N T' ∧ ∀ δ ∈ W.DelF,
            W.γD T' δ (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x) = Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x from
          ⟨hq, fun δ hδ => by rw [hγsm, map_pow, hΔq δ hδ, hΔx δ hδ]⟩
      obtain ⟨x', ⟨hx'N, -⟩, hx'⟩ := hmod2 _ hyΔ
      have hx'' : W.γD T' W.gam (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x) - Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x =
          W.π₀ • x' := hx'
      have key : Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • Formalism.MainNotions.CrystallineLiftingInputs.dOp W T' x = (↑hu.unit⁻¹ : LetA O n) •
          (x' - ((w₂ : LetA O n) * g) • (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x)) := by
        apply hinj
        rw [hdOp, smul_comm W.π₀ (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat), hcan1,
          smul_comm W.π₀ (↑hu.unit⁻¹ : LetA O n), smul_sub W.π₀, ← hx'', hγy, smul_smul W.π₀, hpg,
          sub_smul, one_smul]
        simp only [smul_sub, smul_smul, ← mul_assoc, hu.val_inv_mul, one_mul]
        abel
      rw [key]
      exact (W.N T').smul_mem _ ((W.N T').sub_mem hx'N ((W.N T').smul_mem _ hq))
    · obtain ⟨y, hyN, rfl⟩ := hq
      obtain ⟨g, hg⟩ := rToolMod_geom (W.π₀ * (w₂ : LetA O n)) (-k).toNat
      have hpg : W.π₀ * ((w₂ : LetA O n) * g) = (1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat - 1 := by
        rw [hg]; ring
      have hyΔ' : ∀ δ ∈ W.DelF, W.γD T' δ y = y := by
        intro δ hδ
        have h1 := hΔx δ hδ
        rw [hγsm, map_pow, hΔq δ hδ] at h1
        rw [← rToolMod_qi_q W T' hqU (-k).toNat (W.γD T' δ y), h1, rToolMod_qi_q W T' hqU]
      have hyΔ : y ∈ W.NΔ T' :=
        show y ∈ W.N T' ∧ ∀ δ ∈ W.DelF, W.γD T' δ y = y from ⟨hyN, hyΔ'⟩
      obtain ⟨x', ⟨hx'N, -⟩, hx'⟩ := hmod2 _ hyΔ
      have hx'' : W.γD T' W.gam y - y = W.π₀ • x' := hx'
      refine ⟨(1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat • x' + ((w₂ : LetA O n) * g) • y,
        (W.N T').add_mem ((W.N T').smul_mem _ hx'N) ((W.N T').smul_mem _ hyN), ?_⟩
      apply hinj
      rw [hdOp, hcan1, hγy, smul_comm W.π₀ (Formalism.MainNotions.LiftingTheory.qp W ^ (-k).toNat), smul_add W.π₀,
        smul_comm W.π₀ ((1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat), ← hx'', smul_smul W.π₀, hpg,
        sub_smul, one_smul]
      simp only [smul_sub, smul_add, smul_smul, mul_comm]
      abel

end DStab

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DualLemmaOfDeterminant
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LengthCokerLe
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

def π0N (T : LocLat G Qp LL O) (i : ZMod n) : Submodule O ↥(NDl W T i) :=
  ((NDl W T i).map (W.π₀ • (LinearMap.id : W.DD T →ₗ[O] W.DD T))).comap (NDl W T i).subtype

def IsRed (T : LocLat G Qp LL O) (i : ZMod n) {r : ℕ} (red : ↥(NDl W T i) →ₗ[O] (Fin r → O)) : Prop :=
  Function.Surjective red ∧ LinearMap.ker red = π0N W T i

theorem length_coker_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}
    (QQ : Matrix (Fin r) (Fin r) O) (l : O) (hl : l ≠ 0) (V : ℕ) (hd : QQ.det ∣ l ^ V) :
    Module.length O ((Fin r → O) ⧸ LinearMap.range (Matrix.toLin' QQ)) ≤
      (V : ℕ∞) * Module.length O (O ⧸ Ideal.span {l}) := by
  classical
  have hdet0 : QQ.det ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hd
    exact pow_ne_zero V hl hd
  have hL := Formalism.KernelCokernelLengths.length_theorems_all_hold.1 O (Fin r → O) (Matrix.toLin' QQ) (by rwa [LinearMap.det_toLin'])
  rw [hL, LinearMap.det_toLin', ← Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow l hl V]
  have hle : Ideal.span {l ^ V} ≤ Ideal.span {QQ.det} := Ideal.span_singleton_le_span_singleton.2 hd
  first
    | exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    | exact Module.length_le_of_surjective (Ideal.Quotient.factorₐ O hle).toLinearMap
        (Ideal.Quotient.factor_surjective hle)

theorem lemmaDN_core {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) {r : ℕ} (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O))
    (hsurj : Function.Surjective red) (hker : LinearMap.ker red = π0N W T₂ i) {m' : ℕ} (hm' : m' ≤ m)
    (g : Fin m' → W.DD T₂) (hgN : ∀ j, g j ∈ NDl W T₂ i) (cols : Fin r → ↥(NDl W T₂ i))
    (hcols : ∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
      ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j)
    (V : ℕ) (hV : V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m)
    (hdet : (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V) :
    ∃ s : Finset (W.DD T₂), s.card ≤ m ∧ (↑s : Set (W.DD T₂)) ⊆ NDl W T₂ i ∧
      ∃ L kO : ℕ, Module.length O (↥(NDl W T₂ i) ⧸
          ((NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            (PhiPullΔ W T₂ i).map
              ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            Submodule.span O (↑s : Set (W.DD T₂))).comap (NDl W T₂ i).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧
        (L : ℝ) ≤ lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S * kO := by
  classical
  obtain ⟨hdom, hdvr, -⟩ := hS.2.2.2.1
  haveI := hdom
  haveI := hdvr
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  haveI : NeZero PD.p := ⟨by omega⟩
  have hpL : ((PD.p : ℕ) : LL) ≠ 0 := (hζ.neZero').out
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hpL
    have := congrArg (algebraMap O LL) h
    rwa [map_natCast, map_zero] at this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := by
    first
      | exact hϖ.maximalIdeal_eq
      | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hlen1 : Module.length O (O ⧸ Ideal.span {ϖ}) = 1 := by
    rw [← hm]
    first
      | exact Module.length_eq_one_iff.2
          (isSimpleModule_iff_isCoatom.2 (IsLocalRing.maximalIdeal.isMaximal O).out)
      | exact Module.length_eq_one_iff.2
          (isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal O)))
  have hlenp : Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) = (k : ℕ∞) := by
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit,
      Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow ϖ hϖ.ne_zero k, hlen1, mul_one]
  let s : Finset (W.DD T₂) := Finset.univ.image g
  refine ⟨s, ?_, ?_, V * k, k, ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simpa using hm')
  · intro x hx
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨j, rfl⟩ := hx
    exact hgN j
  · set X := (((NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            (PhiPullΔ W T₂ i).map
              ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            Submodule.span O (↑s : Set (W.DD T₂))).comap (NDl W T₂ i).subtype) with hX
    have hkerX : LinearMap.ker red ≤ X := by
      rw [hker]
      exact Submodule.comap_mono (le_sup_left.trans le_sup_left)
    have hcolX : ∀ k', cols k' ∈ X := by
      intro k'
      rw [hX, Submodule.mem_comap, Submodule.coe_subtype]
      rcases hcols k' with h | ⟨j, hj⟩
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right h)
      · rw [hj]
        exact Submodule.mem_sup_right (Submodule.subset_span (by simp [s]))
    let QQ : Matrix (Fin r) (Fin r) O := Matrix.of fun l k' => red (cols k') l
    let e := LinearMap.quotKerEquivOfSurjective red hsurj
    let f : (Fin r → O) →ₗ[O] (↥(NDl W T₂ i) ⧸ X) := (Submodule.factor hkerX) ∘ₗ e.symm.toLinearMap
    have hf : Function.Surjective f := (Submodule.factor_surjective hkerX).comp e.symm.surjective
    have hrange : LinearMap.range (Matrix.toLin' QQ) ≤ LinearMap.ker f := by
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker]
      have hv : Matrix.toLin' QQ v = red (∑ k', v k' • cols k') := by
        ext l'
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_smul, QQ, mul_comm]
      have he : e.symm (red (∑ k', v k' • cols k')) =
          Submodule.Quotient.mk (∑ k', v k' • cols k') := by
        rw [LinearEquiv.symm_apply_eq]
        first
          | rfl
          | exact (LinearMap.quotKerEquivOfSurjective_apply_mk red hsurj _).symm
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hv, he,
        Submodule.factor_mk, Submodule.Quotient.mk_eq_zero]
      first
        | rw [Submodule.factor_mk, Submodule.Quotient.mk_eq_zero]
        | (change Submodule.Quotient.mk (p := X) (∑ k', v k' • cols k') = 0
           rw [Submodule.Quotient.mk_eq_zero])
      exact Submodule.sum_mem _ fun k' _ => Submodule.smul_mem _ _ (hcolX k')
    let g' := (LinearMap.range (Matrix.toLin' QQ)).liftQ f hrange
    have hg' : Function.Surjective g' := by
      intro z
      obtain ⟨y, rfl⟩ := hf z
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    calc Module.length O (↥(NDl W T₂ i) ⧸ X)
        ≤ Module.length O ((Fin r → O) ⧸ LinearMap.range (Matrix.toLin' QQ)) :=
          Module.length_le_of_surjective g' hg'
      _ ≤ (V : ℕ∞) * Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) :=
          length_coker_le QQ _ hp0 V hdet
      _ = ((V * k : ℕ) : ℕ∞) := by rw [hlenp, Nat.cast_mul]
  · unfold Formalism.WeaklyAdmissibleFiltrations.lenOl
    exact hlenp
  · have hp1 : (1 : ℝ) < (PD.p : ℝ) := by exact_mod_cast (by omega : 1 < PD.p)
    have hcD : 0 ≤ Formalism.MainNotions.RamifiedCoefficientChains.cD PD.p (hpar n b S + η) := by
      unfold Formalism.MainNotions.RamifiedCoefficientChains.cD
      have h1 : 0 < (PD.p : ℝ) - 1 := by linarith
      have h2 : 0 ≤ ((hpar n b S + η : ℕ) : ℝ) + 1 := by positivity
      have := div_nonneg h2 h1.le
      linarith
    have hfl := Nat.floor_le hcD
    have hV' : (V : ℝ) ≤ (finrank LL T₂.V : ℝ) * S + 2 * m * Formalism.MainNotions.RamifiedCoefficientChains.cD PD.p (hpar n b S + η) := by
      have h := (Nat.cast_le (α := ℝ)).2 hV
      push_cast at h
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [h, hfl, hm0]
    unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.lenC
    push_cast
    exact mul_le_mul_of_nonneg_right hV' (Nat.cast_nonneg k)

def DetColsE : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (r : ℕ) (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O)) (_ : IsRed W T₂ i red)
        (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → W.DD T₂) (_ : ∀ j, g j ∈ NDl W T₂ i)
        (cols : Fin r → ↥(NDl W T₂ i)),
        (∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
          ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j) ∧
        ∃ V : ℕ, V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m ∧
          (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V

theorem lemmaDN_of_detE (h : DetColsE W) : LemmaDN W := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨r, red, hred, m', hm', g, hgN, cols, hcols, V, hV, hdet⟩ := h d T₁ T₂ F b S η m hS i hi
  obtain ⟨hsurj, hker⟩ := hred
  exact lemmaDN_core W hS i red hsurj hker hm' g hgN cols hcols V hV hdet

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD
end
end

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem evaluation_add (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f + g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f + Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  funext i
  exact PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero' hz) f g

theorem evalZero_mul (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f * g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  funext i
  exact PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hz) f g

theorem evalZero_X_eq_pi0 (hz : PowerSeries.constantCoeff W.π₀₁ = 0) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W PowerSeries.X = W.π₀ := by
  funext i
  show PowerSeries.subst W.π₀₁ PowerSeries.X = W.π₀ i
  rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hz)]
  rfl

theorem evalZero_C (c : O) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C c) = algebraMap O (LetA O n) c := by
  funext i
  show PowerSeries.subst W.π₀₁ (PowerSeries.C c) = _
  rw [PowerSeries.subst_C]
  rfl

def AdaptData (T : LocLat G Qp LL O) (i : ZMod n) (h η m : ℕ) (e' : Fin (finrank LL T.V) → W.DD T)
    (m' : ℕ) (u : Fin m' → ℤ) : Prop :=
  Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T (i - 1) e' ∧ m' ≤ m ∧ ∃ hmr : m' ≤ finrank LL T.V,
    (∀ j, -(η : ℤ) ≤ u j ∧ u j ≤ η) ∧
    (∀ j (hj : e' (Fin.castLE hmr j) ∈ W.N T),
      ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (W.cmp T ⟨_, hj⟩)) ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (u j)) ∧
    ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i →
      Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut.lowSum (PD := PD) T τ h η ≤ ∑ j, ((h : ℤ) + u j)

def AdaptBas : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ),
        AdaptData W T₂ i (b i + S) η m e' m' u

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfLeafLemmas
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem local_theorem_of_leaf_lemmas (hG : GenStep) (hL : LiftStep) (hd : DvdStep) (hq : QuotStep)
    (hn : NormStep) (h9 : DeltaInvariantUniformizer) (he : ExtStep) (hw : WStep) (hk : KerLamStep) (hl : NinLamStep)
    (hg : GradNStep) (hf : FrobPiNStep) (hγ : GamPiStep) (ho : OneGenStep)
    (hUL : UnivLinkStep) (hR : InvLiftStep) (hC : ClassMapStep) (hH : FrameStep)
    (hMFL : ModelFLinkStep) (hP5 : ExpansionFormHypothesis) (hML : ModelLStep) (hMQL : ModelQLinkStep)
    (hU1L : FirstFrameOfModels) (hkp : KapPiStep) (hU2L : SecondPropositionOfRank) (hU2R : SecondRankHypothesis)
    (hD : DownSlotOfModels) (hUp : UpSlotOfModels) (hMx : MixedSlotOfModels) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → DdRFull D → DiRank D HW F Cm →
        IntegralityFromMetric D HW F Cm CA CB CK C := by
  intro D HW F Cm CA CB CK C hC160 hFont hdr hrk hA
  have hMQ : ModelQStep := modelQStep_of hMQL hML
  have hU2 : SecondPropositionHypothesis := second_proposition_of_models hU2L hMQ hU2R hML
  have hMF := modelFStep_of hMFL hP5 D HW F Cm CA CB CK hdr hrk hA
  have hU1 := first_frame_of_models hU1L hML D HW F Cm CA CB CK hdr hrk hA hMF
  have hUniv : univR D HW :=
    hUL D HW F hA.2.2.2.2.1 hd (hR D HW F Cm CA CB CK hA) (hC D HW F Cm CA CB CK hA)
      (hH D HW F Cm CA CB CK hA) hMF hU1 (hkp D HW F Cm CA CB CK hA) (hU2 D HW F Cm CA CB CK hA)
      (hD D HW F Cm CA CB CK hA hMF) (hUp D HW F Cm CA CB CK hA hMF) (hMx D HW F Cm CA CB CK hA hdr hrk hMF)
  have hKill : killR D :=
    killR_of_steps D HW hd (hq D hA.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.2.1) (hn D)
      (h9 D HW F Cm hA.1)
      (splitR_of_steps D HW F hA.2.1 hA.2.2.2.2.1 (he D HW F Cm CA CB CK hA) (hw D HW F Cm CA CB CK hA)
        (hk D HW F Cm CA CB CK hA hFont) (hl D HW F Cm CA CB CK hA) (hg D HW F Cm CA CB CK hA)
        (hf D HW F Cm CA CB CK hA) (hγ D HW F Cm CA CB CK hA) (ho D HW F Cm CA CB CK hA))
      hUniv
  exact local_theorem_of_good_extensions D C hC160 (local_form_of_three_inputs D (hG D HW F Cm CA CB CK hA) (hL D HW F Cm CA CB CK hA) hKill)

end Formalism.MainNotions.N.Ln34

end
end
