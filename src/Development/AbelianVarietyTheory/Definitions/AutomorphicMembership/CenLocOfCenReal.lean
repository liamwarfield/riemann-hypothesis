module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistAllPowersOfGaloisCohomologyClassField
public import Formalism.LocalToGlobal.CarriedPlMap
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AutomorphicArithmetic.CharacterBoxes.ExS

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev RowP : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (hX : B.fields.Ok)
    (z : Dat (w.st Z) w.I hX T Wt) (p0 : BaseLevelRowSide (w.D Z)), Read z.R.toRealDat z.F.lv2 p0 → Prop

def OverRows (p : RowP) : Prop :=
  EvLgG fun K B f T => KPx B f → ∀ w : ColW B f T, ColPin w → ∀ Z Wt hX z p0 Y, Holds z.R z.F → z.R.toRealDat.ExAt →
    GlobalTheory.RealGeo.InGeo z.geo → GrpTrue Z.N f → GrpAt (w.st Z) w.I → p K B f T w Z Wt hX z p0 Y

def CenLoc (D : D7) (M : MtFam D) : Prop :=
  ∀ i : D.nd.Loc, ∃ L : G0g D.nd → GAf D.host.E D.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
      ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt (D.nd.mu i) (D.nd.j i)),
        (M.loc i).real (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) z x) =
          GlobalTheory.PendOf.actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M.loc i).real x)

def SumTw (D : D7) (M : MtFam D) : Prop :=
  ∀ w, TwistedAt D w → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), GlobalTheory.CoefDuty.ClassSum (M (D.what₂.muTw w) j h1 h2)

structure ParIn (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (Rw : RowSide D) : Type 1 where
  T : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : LabTrue D T
  chr : CharSide D cf
  cg : CGTrue hL D T
  A : AUSide D
  au : AUTrue hL D T A
  row : RowTrue hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR


open GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings in
structure LiftAt (D : D7) (Rw : RowSide D) (j : ℕ) (σ : D.what₂.FT) (π : D.nbc.AU j) (μ : D.naut.CG 1) : Prop where
  csd : D.naut.csd μ
  unr : ∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)
  sph : SphericalInertData.SphInert D.nd D.naut D.nbc j π
  loc : ∀ w, IsSplitPl D.host w → D.nbc.locAU j π w =
    D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w)
  eta : ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧ D.naut.infG D.naut.etaTinv (embTauBar D τ) = {(1 / 2 : ℂ)}
  inf : ∀ τ, D.nbc.infW j (D.nbc.wtAU j π) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = (hcSigma (D.hc τ)).map (· - 1 / 2) +
      isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) ∧
    D.nbc.infW j (D.nbc.wtAU j π) (embTauBar D τ) = (hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) +
      isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (embTauBar D τ)

def LiftAll (D : D7) (Rw : RowSide D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∃ π μ, LiftAt D Rw j σ π μ

def RowLoc (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) : Prop :=
  ∀ w : PlE D.host, IsSplitPl D.host w → (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) → D.naut.unr (Rw.locR σ w) ∧
    ∀ α ∈ D.naut.frobEig (Rw.locR σ w), ‖α‖ < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)

structure ParLaws (D : D7) : Prop where
  tie0 : SumRepresentations.tie0 D
  an : SumRepresentations.adm5 D
  temp : SumRepresentations.adm7 D
  lab : SumRepresentations.tieLab D
  one : GlobalTheory.RowCopy.HeckeSplitOne D
  cancel : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)

end GlobalTheory.HeightCounting.Up

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
namespace GlobalTheory.Mem.LiteralAutomorphy

open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Published

structure LitLoc : Prop where
  bz : BernsteinZelevinskyFiniteness
  bern : BernsteinUnitaryProductIrreducible
  geo : GeometricLemma
  zel : ZelevinskyPolynomialRing
  disj : TotallyDisjointProductIrreducible
  mp : MoyPrasadJacquetIso
  theta : MinguezThetaGL
  temp : TemperedProductOfSquareIntegrable
  seg : EssSquareIntegrableSegments
  sq : SquareIntegrableSegment
  unit : UnitaryDualGL
  gen : GenericUnlinkedGL
  multi : LanglandsMultisegments
  exh : LanglandsExhaustionGL
  cos : StandardCosocleGL
  llc : LocalLanglandsExists
  conv : LocalConverseGL
  dzc : DepthZeroCuspidalLL
  dzi : DepthZeroInduction
  dzt : DepthZeroTypeInertia
  brauer : BrauerDegreeZero
  chev : ChevalleyUnits
  green : GreenRegularCharacters

structure LitAut : Prop where
  decay : CuspRapidDecay
  hc : HarishChandraFinite
  fin : AutomorphicFormsFiniteGL
  js : JacquetShalika
  cusp : CuspidalSpectrumGL
  mw : DiscreteSpectrumResidual
  bc : BaseChangeIsobaric
  gk : GelfandKazhdanDual
  gal : GaloisRepOfPolarizedPair
  car : CaraianiLocalGlobalDual
  ctemp : CaraianiTempered
  pur : ClozelPurity
  coh : ClozelCohomological
  art : GlobalArtinReciprocity
  ray : RayClassFieldSt
  chA : HeckeLAdicCharacterAbove
  chW : AlgebraicCharacterWD
  berger : DeRhamPotSemistable

structure LitCoh : Prop where
  pt : PoitouTateNormalised
  lf : LocalFiniteness
  lt : LocalTateDuality
  le : LocalEulerChar
  gf : GlobalFiniteness
  ge : GlobalEulerChar
  uo : UnramifiedOrthogonality
  gw : GreenbergWiles
  lfK : LocalFinitenessK
  ltK : LocalTateDualityK
  leK : LocalEulerCharK
  bk : BlochKatoLocal

structure LitCM : Prop where
  hb : HilbertBlumenthal
  gm : GrothendieckDeformation
  dr : AbelianDeRham
  dual : AbelianDualCrystal
  per : PeriodComparison
  gmp : GaussManinPeriods
  st : SerreTateGoodReductionSt
  cm : EllipticMainTheoremCM
  hj : HilbertClassFieldJ
  dri : SiegelKlingenDeligneRibet
  pz : PartialZetaFunctionalEquation
  fe : HeckeTateFunctionalEquation

structure LitN : Prop where
  loc : LitLoc
  aut : LitAut
  coh : LitCoh
  cm : LitCM

end GlobalTheory.Mem.LiteralAutomorphy
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
noncomputable section

namespace GlobalTheory.HeightCounting.Up.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

theorem used_loc {D : D7} (i : D.nd.Loc) : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

end GlobalTheory.HeightCounting.Up.Model

end
end
