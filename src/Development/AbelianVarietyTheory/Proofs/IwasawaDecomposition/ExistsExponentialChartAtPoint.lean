module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Formalism.LocalToGlobal.CarriedPlMap
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AutomorphicArithmetic.CharacterBoxes.ExS
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpectralStagePointRowPlacementTransfer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem unitOn_injective : Function.Injective (unitOn (R := ℂ)) := by
  intro c c' h
  ext
  have := congrArg (fun u : Γ(Sp ℂ, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (u : Γ(Sp ℂ, ⊤))) h
  simpa [unitOn] using this

theorem unitOn_one : unitOn (1 : ℂˣ) = 1 := by simp [unitOn]

theorem map_nsmul_eq_pow {g : ℕ} {Q : Type} [Monoid Q] (f : (Fin g → ℂ) → Q) (hf : ∀ v w, f (v + w) = f v * f w)
    (h0 : f 0 = 1) (N : ℕ) (u : Fin g → ℂ) : f ((N : ℂ) • u) = f u ^ N := by
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [Nat.cast_succ, add_smul, one_smul, hf, ih, pow_succ]

theorem pow_eq_one_of_map {g : ℕ} {Q : Type} [Monoid Q] (f : (Fin g → ℂ) → Q) (hf : ∀ v w, f (v + w) = f v * f w)
    (h0 : f 0 = 1) {N : ℕ} (hN : 0 < N) {v : Fin g → ℂ} (hv : f v = 1) : f ((N : ℂ)⁻¹ • v) ^ N = 1 := by
  rw [← map_nsmul_eq_pow f hf h0, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), one_smul, hv]

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
  GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide

section Clauses

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def HeckeRd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat R Sb (idxOf D j) k P α Rr → ∀ x : Fin (R.nW (idxOf D j)) → D.what₂.LL,
    (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (hL j k P x)) =
      hkNorm R (idxOf D j) k P • heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) Rr
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x))

def LvlPsi (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  (∀ g : G, g ∈ F.P0 ↔ (R.eG.trans cG) g ∈ Formalism.IndefR.NX.U D.nd) ∧
    ∀ (u : F.P0) (hu : (R.eG.trans cG) u ∈ Formalism.IndefR.NX.U D.nd),
      (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = (((F.ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)

end Clauses

section Rat

variable {D : D7}

def FormsC (S : RatDat D.ntw) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm ∧ FiniteDimensional S.Ks (FmK S j) ∧
    ∃ T : Finset (S.WL j), (∀ x ∈ T, x ∈ (S.A j).MK) ∧
      (∀ x ∈ (S.A j).MK, x ∈ (S.A j).WK ∧ x ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j))) ∧
      ∀ x ∈ (S.A j).WK, x ∈ Submodule.span S.Ks (T : Set (S.WL j))

def StabC (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK

def IntC (S : RatDat D.ntw) (Sb : Finset (PlE D.host)) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ j k P, 1 ≤ j → j ≤ D.R.m → IsSplitPl D.host P → P ∉ Sb → k ≤ D.R.r → ∃ n : ℕ,
    ∀ x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), x ∈ goodL D S θ j →
      (normV P) ^ n • hL j k P x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j))

def SpanC (S : RatDat D.ntw) (Sb : Finset (PlE D.host)) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → goodL D S θ j ≤
    ⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D S θ j ⊓ ⨅ (k : ℕ) (P : PlE D.host)
      (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ Sb), Module.End.eigenspace (hL j k P) ((eig j σ k P : ↥D.LL0) : D.what₂.LL)

def lowSet (D : D7) : Set (PlE D.host) := {v | ∃ p ∈ lowAll D, p ≠ 0 ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal}

theorem lowSet_finite (D : D7) : (lowSet D).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion (s := (((lowAll D).filter (· ≠ 0) : Finset ℕ) : Set ℕ)) (Finset.finite_toSet _)
    fun p hp => GlobalTheory.RowTie.placesOver_finite_of_ne_zero D.host.E p (Finset.mem_filter.1 hp).2) ?_
  rintro v ⟨p, hp, hp0, hv⟩
  exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hp, hp0⟩)) hv

def SbD (D : D7) : Finset (PlE D.host) := (lowSet_finite D).toFinset

theorem overSet_SbD (D : D7) : OverSet D (SbD D) (lowAll D) := by
  intro v hv
  obtain ⟨p, hp, -, hv⟩ := (lowSet_finite D).mem_toFinset.1 hv
  exact ⟨p, hp, hv⟩

end Rat

section State

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def kKsOf (x : St P) : x.m.z.core.Q.c.F →+* ↥(Dof x).LL0 :=
  (algebraMap x.m.z.core.Q.c.F (Dof x).what₂.LL).codRestrict (Dof x).LL0 x.m.z.fieldValues_mem_fixedField

theorem hkOf (x : St P) (y : x.m.z.core.Q.c.F) :
    ((kKsOf x y : ↥(Dof x).LL0) : (Dof x).what₂.LL) = algebraMap x.m.z.core.Q.c.F (Dof x).what₂.LL y := rfl

abbrev SOf (x : St P) : RatDat (Dof x).ntw := ratDatR x.m.z.R x.m.z.cG (kKsOf x) (hkOf x)

end State

end GlobalTheory.HeightCounting.RatSide
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.SideCopy

structure CopyAll (D D' : D7) (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) : Prop where
  cp : CopyTw D D' ι e
  jL : HEq D.ntw.jL D'.ntw.jL
  s2 : HEq D.ntw.s2 D'.ntw.s2
  lamG : HEq D.ntw.lamG D'.ntw.lamG
  Xv : HEq D.ntw.Xv D'.ntw.Xv
  qs : HEq D.ntw.qs D'.ntw.qs
  pl : HEq D.naut.plGw D'.naut.plGw

structure SameFrame {D D' : D7} (cf : CharFrame D) (cf' : CharFrame D') : Prop where
  mu0 : HEq cf.mu0 cf'.mu0
  eta : HEq cf.eta cf'.eta
  del : HEq cf.del cf'.del
  del' : HEq cf.del' cf'.del'

structure RingPart (D : D7) (cf : CharFrame D) (low : Finset ℕ) where
  twF : TwFrameC D
  tw : TwistFrameLowIndexCompatibility D twF low
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y
  deltaRead : DeltaRead D cf

def RingPart.of {D : D7} {cf : CharFrame D} {Rw low Pq S hL eig θ} (B : SideB D cf Rw low Pq S hL eig θ) : RingPart D cf low :=
  ⟨B.twF, B.tw, B.chiD, B.chi, B.eta_eq, B.ringSpec_normalisedCharacter_eq, B.del_eq, B.iCq_embO, B.embO_star, B.deltaRead⟩

def PsiStd (D : D7) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ u : Formalism.IndefR.NX.U D.nd, embLL0 D ((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) =
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (Complex.exp (2 * Real.pi * Complex.I / (D.host.g kv.1 : ℂ)) ^ (NX.xiRed D kv * NX.supSum D.R.r
      (((u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val)⁻¹

def PsiLaw (D : D7) (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ i b (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
    ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      readLL0 S i b ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0)

def SameUnits {D D' : D7} (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ)
    (c' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (b : Bool) (P : PlE D.host) (P' : PlE D'.host), HEq i i' → HEq P P' → HEq (c' i' b P') (c i b P)

def RowEig (D : D7) (S : RatDat D.ntw) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT) : Prop :=
  ∀ i (s : D.ntw.Sig i) k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
    algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i (D.ntw.side i s) P) ^ k *
        (show FractionRing (D.ntw.O i) from readLL0 S i (D.ntw.side i s) (eig (D.ntw.jS i s) (rowS i s) k P))



set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sigSpan_copy {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyAll D D' ι e)
    (hs : D.ntw.SigSpan) : D'.ntw.SigSpan := by
  have transfer {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
      {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
      (g : GlobalTheory.TwistChoice.SameGalois N N')
      (t : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X')
      (b : HEq X.B X'.B) (ab : HEq X.acgB X'.acgB)
      (mb : HEq X.modB X'.modB) (hk : HEq X.hk X'.hk)
      (s : X.SigSpan) : X'.SigSpan := by
    obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := g
    obtain ⟨xcc, xTw, xl, xO0, xcrO0, xalgO0, xtopO0, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, xS0, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := t
    cases D; cases D'
    dsimp only at a1 a2 a3
    subst a1; subst a2; subst a3
    cases N; cases N'
    dsimp only at nOm ninstOm nalgOm nplOm nPlG
    subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
    cases X; cases X'
    dsimp only at xcc xTw xl xO0 xcrO0 xalgO0 xtopO0 xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xS0 xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth b ab mb hk
    subst xcc; subst xTw; subst xl; subst xO0; subst xcrO0; subst xalgO0; subst xtopO0; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xS0; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
    subst b; subst ab; subst mb; subst hk
    exact s
  exact transfer h.cp.gal h.cp.set h.cp.B h.cp.acgB h.cp.modB h.cp.hk hs

end GlobalTheory.HeightCounting.SideCopy

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationGeometric
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

attribute [local instance] GlobalTheory.Mem.R3.TwIn.grp GlobalTheory.Mem.R3.TwIn.fin GlobalTheory.Mem.R3.TwIn.alg

namespace GlobalTheory.Mem.R3.SelRealIn

open _root_.Formalism.L2.SG.RowsJoinPinned Formalism.IndefR.AutomorphicEvaluation _root_.Formalism.L2.Theta GlobalTheory.Mem.Top.Bl

section Gen
open _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem nexp_upd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (n : NExpRealS R cG S)
    (lam : type_of% R.lam3) (err : type_of% R.err0) :
    ∃ (Sx : RatDat D.ntw) (n' : NExpRealS ((R.updS R.kap lam).withErr err) cG Sx), HEq Sx S ∧ HEq n'.eF n.eF ∧ HEq n'.fi n.fi :=
  ⟨S, ⟨n.fi, n.geq, n.rho, n.chi, n.eF, n.bsup, n.act⟩, HEq.rfl, HEq.rfl, HEq.rfl⟩
end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}



end GlobalTheory.Mem.R3.SelRealIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsEOfHeq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isE_of_heq {𝒮 : Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {D : D7}
    (e : w.D Z = D) (O : Obj D) {O' : Obj2 (w.D Z)} (hO : HEq (ofObj O) O') (x : Wit 𝒮 K w Z O') (hx : EntC x.ker) :
    ∃ q : WPt 𝒮 K, q.Is D O ∧ EntC q.x.ker := by
  subst e
  obtain rfl := eq_of_heq hO
  exact ⟨⟨B, f, T, w, Z, O, x⟩, rfl, hx⟩

theorem exists_isE_pt {𝒮 : Slots} (H : WitMv 𝒮) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {O : Obj2 (w.D Z)} (x : Wit 𝒮 K w Z O) (hx : EntC x.ker) (Y : Lay (w.D Z)) (hY : layObj Y = O) (p : LedPart K.C Y) :
    ∃ q : WPt 𝒮 K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker := by
  obtain ⟨y, hy⟩ := H K B f T w Z O x (nPrime p.L) p.ht hx
  exact exists_isE_of_heq (Db.D_setDivZ w Z (nPrime p.L) p.ht) (Obj.ofPt p.pt)
    (hY ▸ heq_of_eq (pointObj_pt p)) y hy

theorem witExE_of_witMv : ∀ 𝒮 : Slots, WitMv 𝒮 → WitExE 𝒮 := fun 𝒮 H _ β hβ =>
  positionOf_ind (P := GoodE 𝒮) (R := fun K X _ _ c => ∀ (Y : Lay X.toD7) (_ : layObj Y = c.O) (p : LedPart K.C Y),
      ∃ q : WPt 𝒮 K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker)
    (fun _ _ _ _ _ _ _ g => g.1.elim fun b hb => exists_isE_pt H (b.wit g.2) hb) hβ β.Y β.hY β.p

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedSideRealizationHolds
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.SelSideW

theorem plMap_refl {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.Host.CT.plMap (RingEquiv.refl E) P = P := by
  ext x
  exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x


open Classical in
theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  rw [show Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id from funext plMap_refl, Finset.image_id]


open Classical in
theorem qe_image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {S S' : Set ℕ} (hS : S = S') {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)} (hsel : HEq sel sel')
    {tup : D.what₂.Tup → Formalism.L2.DIV.Tup X.F X.E X.K S} {tup' : D.what₂.Tup → Formalism.L2.DIV.Tup X'.F X'.E X'.K S'} (htup : HEq tup tup')
    (μ : D.what₂.Tup) :
    (Col.QE sel (tup μ : DIV.Chr X.F X.E X.K)).image (Host.CT.plMap s.iE) =
      (Col.QE sel' (tup' μ : DIV.Chr X'.F X'.E X'.K)).image (Host.CT.plMap s'.iE) := by
  subst hX
  subst hS
  cases hs
  cases hsel
  cases htup
  rfl


open Classical in
theorem qe_image_std {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt)
    {L : SizeData₂ (w.D Z)} {hT : GatTies (w.D Z)} {Gi : Formalism.MainNotions.G.Inst (w.D Z) L} {Gl : Formalism.MainNotions.G.LatInst (w.D Z)}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.D Z)} {cX : ExtraC} {ex : Extra (w.D Z) L hT Gi Gl Kc Yd cX}
    (t : Formalism.L2.Ker.KerEntTied ex) (h : TC.StdKer w.I w.l Z t) (μ : (w.D Z).what₂.Tup) :
    (Col.QE t.sel (t.tup μ : DIV.Chr t.X.F t.X.E t.X.K)).image (Host.CT.plMap t.seam.iE) = w.I.Q μ := by
  rw [qe_image_congr h.X_eq h.seam h.S h.sel h.tup μ]
  exact image_refl _ rfl _

end GlobalTheory.Mem.R3.SelSideW

namespace GlobalTheory.Mem.R3.SelSideW


end GlobalTheory.Mem.R3.SelSideW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedLowerMapHolds
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabRatInjective
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.R3.GamDvd

attribute [local instance] starE

section Stab

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)

def stabRat (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : MulAction.stabilizer (FormG Λ) d →* autO d.1.N where
  toFun g := ⟨(g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n), g.1.1.2,
    congrArg (fun e : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) => e.1.N) ((MulAction.mem_stabilizer_iff).1 g.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem stabRat_injective (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : Function.Injective (stabRat Λ d) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hγ : (g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) = 1 := congrArg Subtype.val hg
  have hbe := congrArg (fun e : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) => e.1.be) ((MulAction.mem_stabilizer_iff).1 g.2)
  have hM : ∀ w : SG, ((g.1.2 : GLG (E := X.E) (n := n) (SG := SG)) w : Matrix (Fin n) (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) = 1 := by
    intro w
    refine Matrix.ext_of_mulVec_single fun i => ?_
    obtain ⟨x, -, hx⟩ := d.2.be_surj w (Pi.single i 1)
    have e := congrFun (congrFun hbe w) x
    change ((g.1.2 : GLG (E := X.E) (n := n) (SG := SG)) w : Matrix (Fin n) (Fin n) _).mulVec
      (d.1.be w ((g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n).symm x)) = d.1.be w x at e
    rw [hγ] at e
    change ((g.1.2 : GLG (E := X.E) (n := n) (SG := SG)) w : Matrix (Fin n) (Fin n) _).mulVec (d.1.be w x) = d.1.be w x at e
    rw [hx] at e
    rw [e, Matrix.one_mulVec]
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hγ
  · exact Subtype.ext (funext fun w => Units.ext (hM w))

theorem card_stab_dvd (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    Nat.card (MulAction.stabilizer (FormG Λ) d) ∣ Nat.card (autO d.1.N) :=
  Subgroup.card_dvd_of_injective (stabRat Λ d) (stabRat_injective Λ d)

end Stab

section Fam

variable {B : Base} {px : PreX B.toPre} (I : TC B px) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL))
  (tr : TrI B px)

theorem gamDvd_DGam :
    (∀ (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.R t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.R t).S.Gam c) ∣ DGam B.fields.E B.R) ∧
    ∀ (j : Fin B.R.m) (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.L j t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.L j t).S.Gam c) ∣ DGam B.fields.E B.R := by
  refine ⟨fun t c => ?_, fun j t c => ?_⟩
  · rw [Fintype.card_eq_nat_card]
    exact (card_stab_dvd _ (Quotient.out c)).trans
      (dvd_DGam (posStar_of_ok hX) B.R (pred_mem_gamRanks B.R) (Quotient.out c).2.lat (Quotient.out c).2.uni)
  · rw [Fintype.card_eq_nat_card]
    exact (card_stab_dvd _ (Quotient.out c)).trans
      (dvd_DGam (posStar_of_ok hX) B.R (nV_mem_gamRanks B.R) (Quotient.out c).2.lat (Quotient.out c).2.uni)

theorem gamDvd (l : I.Laws) (Z : Later B (I.cols l)) :
    (∀ (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.R t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.R t).S.Gam c) ∣ ((I.rec7 l Z).mem (I.rec7 l Z).u₀).C.DGam) ∧
    ∀ (j : Fin B.R.m) (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.L j t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.L j t).S.Gam c) ∣ ((I.rec7 l Z).mem (I.rec7 l Z).u₀).C.DGam :=
  gamDvd_DGam I hX U Xg tr

end Fam

end GlobalTheory.Mem.R3.GamDvd
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.SelRowPin

theorem amb_of_eq {D : D7} {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {m : ℕ} {A : FamIn D.what₂.LL Gp Pl0 T m}
    {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    {X : RowSide D EE} {Fm Fm' : AmbForm D X} {P : Subgroup Gp} {ψ : P →* D.what₂.LLˣ} {tup tup' : T → D.what₂.Tup}
    {jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)}
    {jA' : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup' t)}
    (hF : Fm = Fm') (h : tup = tup') (hj : HEq jA jA') :
    (∃ J, AmbTie D A X Fm' P ψ tup' jA' J) → ∃ J, AmbTie D A X Fm P ψ tup jA J := by
  subst hF; subst h; cases hj; exact id


end GlobalTheory.Mem.R3.SelRowPin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullAddInjective
noncomputable section

namespace GlobalTheory.PolFan.OrbMark

variable {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

def pullAdd (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) : LinearMap.BilinForm ℤ X :=
  u.compl₁₂ f.toIntLinearMap f.toIntLinearMap

@[simp] theorem pullAdd_apply (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) (x y : X) : pullAdd f u x y = u (f x) (f y) := rfl

theorem pullAdd_injective {f : X →+ Y} (hf : Function.Surjective f) : Function.Injective (pullAdd f) :=
  fun u u' h => LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    exact LinearMap.congr_fun₂ h a b

def pullAddLin (f : X →+ Y) : LinearMap.BilinForm ℤ Y →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pullAdd f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.PolFan.OrbMark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchubGamApply
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric
open Classical

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def flagRoot {H : Host E} (Dw : Datum H) (x : Root Dw.mult) :
    MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : x.1 (H.rt : E) = H.rt0 then
    X (⟨x.1, h⟩, ⟨x.2, by have h1 : (x.2 : ℕ) < Dw.mult x.1 := x.2.2; have h2 := GlobalTheory.PointChern.mult_of_mem Dw h; omega⟩)
  else
    -X (⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩,
      ⟨Dw.p + (Dw.q - 1 - x.2), by have h1 : (x.2 : ℕ) < Dw.mult x.1 := x.2.2; have h2 := GlobalTheory.PointChern.mult_of_not_mem Dw h; omega⟩)

def flagMap {H : Host E} (Dw : Datum H) :
    MvPolynomial (Root Dw.mult) ℝ →ₐ[ℝ] MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  aeval (flagRoot Dw)

def flagLin (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) : MvPolynomial (ι × Fin N) ℝ →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ Formalism.DegreeFormula.dimFl ι N) • ∑ σ : ι → Equiv.Perm (Fin N),
    (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • lcoeff ℝ (Formalism.DegreeFormula.permExp σ)

theorem flagLin_apply (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : MvPolynomial (ι × Fin N) ℝ) :
    flagLin ι N P = Formalism.DegreeFormula.degFl ι N P := by
  simp [flagLin, Formalism.DegreeFormula.degFl, LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]

def schubGam {H : Host E} (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ :=
  flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) ∘ₗ (flagMap Dw).toLinearMap ∘ₗ
    LinearMap.mulRight ℝ (fibrePoint Dw.mult) ∘ₗ (chernRoots Dw.mult).toLinearMap

theorem schubGam_apply {H : Host E} (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    schubGam Dw P = Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (flagMap Dw (chernRoots Dw.mult P * fibrePoint Dw.mult)) := by
  simp [schubGam, flagLin_apply]

def admitted (H : Host E) (Dw : Datum H) (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P, Θ (GlobalTheory.PointChern.relPoly τ k * P) = 0) ∧
  (∀ (τ : E →+* ℂ) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Θ ((X (τ, 0) - 1) * P) = 0) ∧
  (∀ (τ : E →+* ℂ) (k : ℕ), Dw.mult τ < k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (X (τ, k) * P) = 0) ∧
  (∀ d : (E →+* ℂ) × ℕ →₀ ℕ, (d.sum fun x i => x.2 * i) ≠ Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) →
    Θ (monomial d 1) = 0)

end GlobalTheory.Schubert
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionGeometryScalarsTransferSetDivision
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionGeometryScalarsTransferSetDivision
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.OxMove

set_option linter.style.haveILetI false

open _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

section General

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev JW (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Type :=
  ∀ i : Fin D.R.m, (Fin ((R.toCx3 F).dW false i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)

def wpW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (i : Fin D.R.m) (c : A3.fam3.base3.Ix) :
    Submodule D.what₂.LL (Fin ((R.toCx3 F).dW false i) → D.what₂.LL) := (by with_unfolding_all exact (((cxW R F u).WpK false i c) :))

def overW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (j : JW R F) (σ : D.what₂.FT) (c : A3.fam3.base3.Ix) : Prop :=
  ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) σ ≤
    Submodule.span ℂ ((j i) '' (wpW R F u i c : Set (Fin ((R.toCx3 F).dW false i) → D.what₂.LL)))

def lamW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (j : JW R F)
    (l : ℕ → D.what₂.FT → (D.what₂.LL →+* ℂ) → ℝ) : Prop :=
  ∃ lab : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, (∃ c, overW R F u j σ c) → overW R F u j σ (lab σ)) ∧
    ∀ (i : Fin D.R.m) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
      (D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
        l ((i : ℕ) + 1) σ e = Real.log (R.lam3 i A3.A.μ0 (lab σ) (InfinitePlace.mk e))) ∧
      (D.what₂.isot ((i : ℕ) + 1) σ = ⊥ → l ((i : ℕ) + 1) σ e = 0)

end General

section Copy

variable {B : Base} {C : Cols B} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {Ks : Type} [Field Ks] [NumberField Ks]

abbrev mv (a : Late B C) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) : Late B C := Db.setDivZ a N h


set_option maxHeartbeats 4000000 in
theorem lamAre_copy (a : Late B C) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ)
    [iK : Algebra Ks a.D.what₂.LL] {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) (F : Face3 a.D A)
    {X0 : BaseLevelRowSide a.D} {Y : R3.Read (A3 := A) R.toRealDat F.lv2 X0} (Z : R3.ReadL R F X0 Y) (X : DivX a.D)
    (X' : DivX (mv a N h).D) (hX : HEq X'.logLam X.logLam) {X0' : BaseLevelRowSide (mv a N h).D} :
    letI := alg (mv a N h) iK
    ∀ {Y' : R3.Read (A3 := famInThreeCoefficientChange (mv a N h) A) (real3 (mv a N h) R).toRealDat (face3 (mv a N h) F).lv2 X0'}
      (Z' : R3.ReadL (real3 (mv a N h) R) (face3 (mv a N h) F) X0' Y'), HEq Z'.jW Z.jW → LamAre Z X → LamAre Z' X' := by
  letI := alg (mv a N h) iK
  intro Y' Z' hj hl
  have h1 : lamW R F (R.EEp3, R.toRealDat.EEat, R.Wp3) ((by with_unfolding_all exact (Z.jW :))) X.logLam := (by with_unfolding_all exact (hl :))
  have ej : ((by with_unfolding_all exact (Z.jW :)) : JW R F) = (by with_unfolding_all exact (Z'.jW :)) := eq_of_heq ((by with_unfolding_all exact (hj.symm :)))
  have el : X.logLam = (by with_unfolding_all exact (X'.logLam :)) := eq_of_heq ((by with_unfolding_all exact (hX.symm :)))
  have h2 := cast (congr (congrArg₂ (lamW R F) (parts_eq (mv a N h) R F) ej) el) h1
  exact (by with_unfolding_all exact (h2 :))

end Copy


set_option maxHeartbeats 4000000 in
theorem oAt_setDiv : ∀ (Γ : GeoP) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (O : Obj2 (w.D Z)) (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h → ∀ (t : RowsT K w Z Wt O.p0) (t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0), R3.Rw.RowsSame t t' → OAt (geoCl Γ) t O.X → Nonempty (OAt (geoCl Γ) t' O'.X) := by
  intro Γ K B f T w Z Wt N h O O' hO t t' hs hp
  have hOX : O'.X = (by with_unfolding_all exact ((divTr (D := w.D Z) N h O.X) :)) := by subst hO; exact (by with_unfolding_all exact ((Eq.refl (divTr (D := w.D Z) N h O.X)) :))
  clear hO
  generalize O'.X = X' at hOX
  revert t'
  generalize O'.p0 = p0'
  intro t' hs
  subst hOX
  cases t' with | mk hX' r' => ?_
  cases r' with | mk z' holds' Y' Zr' => ?_
  cases z' with | @mk Xg' tr' core' alg' alg_eq' R' => ?_
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  have hj := hs.jW
  clear hs
  change Xg' = t.r.z.Xg at hXg
  change tr' = t.r.z.tr at htr
  subst hXg htr
  change HEq core' _ at hcore
  have hc := eq_of_heq hcore
  subst hc
  have ha : alg' = GlobalTheory.Mem.R3.Tr.alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(Db.setDivZ Z N h).W, (Db.setDivZ Z N h).V, (Db.setDivZ Z N h).S, (Db.setDivZ Z N h).N, (Db.setDivZ Z N h).G⟩ t.r.z.alg := by
    apply Algebra.algebra_ext
    intro r
    apply (w.st (Db.setDivZ Z N h)).B.embLL.injective
    exact (by with_unfolding_all exact (((alg_eq' r).trans (t.r.z.alg_eq r).symm) :))
  subst ha
  change HEq R' _ at hR
  have hR2 := eq_of_heq hR
  subst hR2
  refine ⟨⟨?_, ?_⟩⟩
  · exact (by with_unfolding_all exact ((GeoCl.step (Γ := Γ) (D := (w.st Z).toD7) N h hp.geo) :))
  · exact (by with_unfolding_all exact ((lamAre_copy (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) N h (iK := t.r.z.alg) t.r.z.R t.r.z.F t.r.Z O.X
      (((divTr (D := w.D Z) N h O.X))) (((HEq.refl O.X.logLam))) (X0' := (p0')) (Y' := (Y')) ((Zr')) ((hj)) hp.lam) : _))

end GlobalTheory.Mem.OxMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionGeometryScalarsTransferSetDivisionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionGeometryScalars_transfer_setDivision : ∀ (Γ : GeoP) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (O : Obj2 (w.D Z)) (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h → ∀ (t : RowsT K w Z Wt O.p0) (t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0), R3.Rw.RowsSame t t' → OAt (geoCl Γ) t O.X → Nonempty (OAt (geoCl Γ) t' O'.X) := by
  first | exact @GlobalTheory.Mem.OxMove.oAt_setDiv | exact GlobalTheory.Mem.OxMove.oAt_setDiv | (intros; apply GlobalTheory.Mem.OxMove.oAt_setDiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormBaseChangeDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TraitCmp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), IsCN R → P.TorsionIso →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (g : R →+* W), Function.Injective g → ¬ IsLocalHom g →
    ∀ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap g)) (P' : PELUnif (maximalIdeal W) t'),
      ∃ ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X, Function.Surjective ρ ∧
        ∀ (y : P.D.toPre.X) (r : R) (r' : W), PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (ρ y) r' → Associated (g r) r' := by
  intro E _ _ _ H R _ _ _ t P hR hT W _ _ _ hW g hg hnl t' m P'
  obtain ⟨ρ, hs, hτ⟩ := GlobalTheory.T.characters_restrict_linear_to_trait_uniformisation E H R t P hR hT W hW g hg hnl t' m P'
  exact ⟨ρ, hs, GlobalTheory.T.associated_psi_coordinates_of_tau_units E H R t P W g hg t' P' ρ hτ⟩

end GlobalTheory.TraitCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalPullSemilinearOfIsTwInv
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace OrbMark

theorem eval_pull_semilinear_of_isTwInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)),
    IsTwInv H φ →
    ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
      [Module.Finite (𝓞 E) Y] (τ : 𝓞 E ≃+* 𝓞 E), τ H.w0 = H.w0 → ∀ (f : X →+ Y), Function.Surjective f →
      (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
      ∀ B : Y → Y → ℝ, φ.eval X (fun x y => B (f x) (f y)) = φ.eval Y B := by
  intro E _ _ _ H φ htw X Y _ _ _ _ _ _ τ hτ f hf hsm B
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  let r₁ : (Fin n → 𝓞 E) →ₗ[𝓞 E] Y :=
    { toFun := fun a => f (r (twv τ.symm a))
      map_add' := fun a b => by
        have e : twv τ.symm (a + b) = twv τ.symm a + twv τ.symm b := funext fun _ => map_add τ.symm _ _
        rw [e, map_add (f := _), map_add (f := _)]
      map_smul' := fun c a => by
        rw [twv_smul, map_smul, hsm, RingEquiv.apply_symm_apply]
        rfl }
  have hr₁ : ∀ a, r₁ (twv τ a) = f (r a) := fun a => by
    show f (r (twv τ.symm (twv τ a))) = f (r a)
    rw [twv_symm_twv]
  have hs₁ : Function.Surjective r₁ := fun y => by
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, rfl⟩ := hr x
    exact ⟨twv τ a, hr₁ a⟩
  rw [φ.eval_eq hr, φ.eval_eq hs₁]
  have h := htw τ hτ n fun a b => B (r₁ a) (r₁ b)
  have e : (fun a b : Fin n → 𝓞 E => B (f (r a)) (f (r b))) = fun a b => B (r₁ (fun i => τ (a i))) (r₁ (fun i => τ (b i))) := by
    funext a b
    exact congrArg₂ B (hr₁ a).symm (hr₁ b).symm
  rw [e]
  exact h

end OrbMark

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

theorem charpolyRev_conj_of_mul_eq_one {R : Type*} [CommRing R] {r : Type*} [Fintype r] [DecidableEq r]
    (M P Q : Matrix r r R) (hQP : Q * P = 1) : (Q * M * P).charpolyRev = M.charpolyRev := by
  have hQP' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : (1 : Matrix r r (Polynomial R)) - (Polynomial.X : Polynomial R) • (Q * M * P).map Polynomial.C =
      Q.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * P.map Polynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP',
      Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
    ← Matrix.det_mul, hQP', Matrix.det_one, one_mul]

theorem curvPoly_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : curvPoly G v =
      ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) • (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

end GlobalTheory.PointChern

namespace GlobalTheory.PointChern

theorem gram_eq_changeFrame {r : Type} [Fintype r] (c : ℝ) (hc : 0 < c) (g K : Matrix r r ℂ) :
    (c : ℂ) • (g * K * gᴴ) = (((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᵀ * K * (((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᴴᵀ := by
  have h1 : ((((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᴴᵀ) = ((Real.sqrt c : ℝ) : ℂ) • gᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have h2 : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  rw [h1, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h2]

theorem chernTop_changeFrame : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G K g : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (c : ι → ℝ) (v : ReciprocityTheory.L2DbarEstimates.V n), (∀ τ, 0 < c τ) → (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) v) → (∀ τ, IsUnit (g v τ).det) → (∀ τ, MContDiffAt 2 (fun w => K w τ) v) → (∀ τ, IsUnit (K v τ).det) → (∀ᶠ w in 𝓝 v, ∀ τ, G w τ = (c τ : ℂ) • (g w τ * K w τ * (g w τ)ᴴ)) → chernTop R G v = chernTop R K v := by
  intro n ι m R G K g c v hc hg hgu hK hKu hG
  have key : ∀ τ, curvPoly (fun u => G u τ) v = ((((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ)⁻¹).map C *
      curvPoly (fun u => K u τ) v * ((((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ)).map C := by
    intro τ
    set A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin (m τ)) ℂ :=
      fun u => ((Real.sqrt (c τ) : ℝ) : ℂ) • (g u τ)ᵀ with hAdef
    have hent : ∀ a b, (fun x => A x a b) = fun x => ((Real.sqrt (c τ) : ℝ) : ℂ) * g x τ b a := fun a b => rfl
    have hA : MContDiffAt 2 A v := fun a b => by
      rw [hent]
      exact contDiffAt_const.mul ((hg τ b a).contDiffAt.restrict_scalars ℝ)
    have hAu : IsUnit (A v).det := by
      simp only [hAdef, Matrix.det_smul, Matrix.det_transpose]
      refine IsUnit.mul (IsUnit.pow _ (Ne.isUnit ?_)) (hgu τ)
      exact_mod_cast (Real.sqrt_pos.2 (hc τ)).ne'
    have hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0 := by
      have hev : ∀ᶠ x in 𝓝 v, ∀ a b, AnalyticAt ℂ (fun w => g w τ b a) x :=
        eventually_all.2 fun a => eventually_all.2 fun b => (hg τ b a).eventually_analyticAt
      filter_upwards [hev] with x hx η
      ext a b
      rw [mdbar_apply, hent, GlobalTheory.dbar_eq_zero (((hx a b).differentiableAt).const_mul _)]
      rfl
    have hGe : (fun u => G u τ) =ᶠ[𝓝 v] fun u => (A u)ᵀ * K u τ * (A u)ᴴᵀ :=
      hG.mono fun u hu => by show G u τ = _; rw [hu τ]; exact gram_eq_changeFrame _ (hc τ) _ _
    have hcurv : ∀ ξ η, curv (fun u => G u τ) v ξ η = (A v)⁻¹ * curv (fun u => K u τ) v ξ η * A v :=
      fun ξ η => by rw [curv_congr hGe, curv_changeFrame (hK τ) (hKu τ) hA hAu hA0]
    clear_value A
    rw [curvPoly_eq_sum, curvPoly_eq_sum]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, hcurv]
    subst hAdef
    rfl
  have key2 : ∀ τ k, chernPoly (fun u => G u τ) v k = chernPoly (fun u => K u τ) v k := by
    intro τ k
    have hu : IsUnit (((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ).det := by
      simp only [Matrix.det_smul, Matrix.det_transpose]
      refine IsUnit.mul (IsUnit.pow _ (Ne.isUnit ?_)) (hgu τ)
      exact_mod_cast (Real.sqrt_pos.2 (hc τ)).ne'
    rw [chernPoly, chernPoly, key, show ∀ (Q M P : Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Fin n × Fin n) ℂ)), -(Q * M * P) = Q * (-M) * P from fun Q M P => by rw [Matrix.mul_neg, Matrix.neg_mul], charpolyRev_conj_of_mul_eq_one]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [chernTop, key2]

end GlobalTheory.PointChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChangeStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topChernDensity_invariant_holomorphic_frameChange : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G K g : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (c : ι → ℝ) (v : ReciprocityTheory.L2DbarEstimates.V n), (∀ τ, 0 < c τ) → (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) v) → (∀ τ, IsUnit (g v τ).det) → (∀ τ, MContDiffAt 2 (fun w => K w τ) v) → (∀ τ, IsUnit (K v τ).det) → (∀ᶠ w in 𝓝 v, ∀ τ, G w τ = (c τ : ℂ) • (g w τ * K w τ * (g w τ)ᴴ)) → chernTop R G v = chernTop R K v := by
  first | exact @GlobalTheory.PointChern.chernTop_changeFrame | exact GlobalTheory.PointChern.chernTop_changeFrame | (intros; apply GlobalTheory.PointChern.chernTop_changeFrame <;> assumption)
end
end
