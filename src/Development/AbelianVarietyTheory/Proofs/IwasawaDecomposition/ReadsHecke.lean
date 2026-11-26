module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateBlockUpperOfEigenfunctionUnipotentType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsStandardChainData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardCodeWordStagesFiniteGroupEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompositeIntertwinerEqThetaLiftGoodProjector
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Lean

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
noncomputable section

namespace GlobalTheory.LevCmp

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def Eig {V : Type} [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (κ : GAf L n) (c : ℂ) : Prop := ∀ g, F (g * κ) = c • F g

def FrameAut (θ : GAf L n ≃* GAf L n) : Prop :=
  (∀ κ, θ κ ∈ Umax L n ↔ κ ∈ Umax L n) ∧ ∀ v κ, TrivOutside {v} (θ κ) ↔ TrivOutside {v} κ

def cx {K : Type} [Field K] (e : K →+* ℂ) {J : Subgroup (GAf L n)} (χ : J →* Kˣ) : J →* ℂˣ := (Units.map e.toMonoidHom).comp χ

theorem cx_apply {K : Type} [Field K] (e : K →+* ℂ) {J : Subgroup (GAf L n)} (χ : J →* Kˣ) (κ : J) :
    ((cx e χ κ : ℂˣ) : ℂ) = e (χ κ : Kˣ) := rfl

def LevEq (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (J' : Subgroup (GAf L n)) (χ' : J' →* ℂˣ) : Prop :=
  J = J' ∧ ∀ κ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩

def WtMatch {K : Type} [Field K] (e : K →+* ℂ) {W W' : Type} [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W'),
    ∀ γ, LinearMap.toMatrix b' b' (ρ' γ) = (LinearMap.toMatrix b b (ρ γ)).map e

end Gen

variable {D : D7}

def SideRead (i : D.ntw.Tw) (b : Bool) (k : ℕ) (e : NX.Kk D i k →+* ℂ) : Prop :=
  ∀ x : ↥D.LL0, e (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x)) = embLL0 D x

def ReadsHecke {i : D.ntw.Tw} {k : ℕ} (e : NX.Kk D i k →+* ℂ) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (χ : HChar D.host.E) : Prop :=
  ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map (e.comp (NX.ofOk D i k)).toMonoidHom).comp ψ) χ


variable (D) in
def GalOf (χ : HChar D.host.E) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) ∧ ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀) χ


variable (D) in
def GPlaces : Prop :=
  (∀ k v, D.naut.plGw k v ∈ placesOver D.host.E (D.host.g k) ∧ ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw k v) ∧
    (∀ u ∈ gPl D, ∃ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.v = u ∧ s.w = D.naut.plGw k v) ∧
    ∃ k, Nonempty (D.nd.PlG k)


variable (D) in
def ParaShape (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) : Prop :=
  ∀ v ∈ qPl D η, ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
    NG.IsCompAt η s ξ ∧ NG.LevelPara J χ s D.R.r ξ


variable (D) in
def GrpShape (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)) : Prop :=
  NG.IsProdLevel J ∧
    (∀ v ∈ qPl D η, ∃ s : SplitPlace D.host.E, s.v = v ∧ ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s D.R.r (s.loc _ κ))) ∧
    (∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v →
      ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.UniRT s D.R.r (s.loc _ κ))) ∧
    ∀ κ, TrivOutside (gPl D ∪ qPl D η)ᶜ κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)

abbrev cell (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m) :=
  X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA

abbrev eta (cf : CharFrame D) (xi : D.what₂.Tup → HChar D.host.E) (v : D.what₂.places.Pl) (j : Fin D.R.m) : HChar D.host.E :=
  cf.mu0 j * xi (D.what₂.muTw v)

abbrev mtAt (M : MtFam D) (v : D.what₂.places.Pl) (j : Fin D.R.m) : MtReal D (D.what₂.muTw v) (j.1 + 1) :=
  M (D.what₂.muTw v) (j.1 + 1) (by omega) (by omega)

def CellWt {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) : Prop := WtMatch e (cell X b hA j).ρ m.wt.ρ

def Joint (η : HChar D.host.E) {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m) : Prop :=
  ∃ (θ : GAf D.host.E D.R.nV ≃* GAf D.host.E D.R.nV) (J₁ : Subgroup (GAf D.host.E D.R.nV)) (e : NX.Kk D i k →+* ℂ)
    (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ω : (cell X b hA j).W →ₛₗ[e] V),
    FrameAut θ ∧ SideRead i b k e ∧ Function.Injective ω ∧
    (∀ v ∈ qPl D η, ∃ s : SplitPlace D.host.E, s.v = v ∧ ∀ κ, TrivOutside {s.v} κ → NG.ParaRT s D.R.r (s.loc _ κ) → κ ∈ J₁) ∧
    (∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v →
      ∀ κ, TrivOutside {s.v} κ → NG.UniRT s D.R.r (s.loc _ κ) → κ ∈ J₁) ∧
    ∀ κ ∈ J₁, ∃ c c' : ℂ, (∀ x, Eig (m.real x) (θ κ) c) ∧ (∀ f, Eig (fun g => ω (((cell X b hA j).real f).1 g)) (θ κ) c') ∧
      ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → TrivOutside {s.v} κ →
        c ^ (D.host.g kk - 1) = c' ^ (D.host.g kk - 1)

end GlobalTheory.LevCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def sgTw (x : St P) (N : TwNew (Dof x)) : SameGrp (B := B) (C := w.C) x.o.Z (oTw x N).Z where
  e _ := Equiv.refl _
  pl _ _ := rfl
  e0 _ := rfl

def datTw (x : St P) (N : TwNew (Dof x)) : Dat (w.st (oTw x N).Z) w.I P.hX T P.Wt :=
  DatCopy.copy (a := x.o.Z) (oTw x N).Z (sgTw x N) x.m.z

def sideTw (x : St P) (N : TwNew (Dof x)) : Side0 (oTw x N) where
  cen := x.s.cen
  tie := x.s.tie
  is := x.s.is
  RR := x.s.RR
  frames := x.s.frames
  jEE := x.s.jEE
  basis := x.s.basis
  norm := x.s.norm

theorem fitsTw (x : St P) (N : TwNew (Dof x)) : (oTw x N).Fits := ⟨x.fits.div, x.fits.grp, ⟨(by with_unfolding_all exact (x.fits.grpAt.pl :)), (by with_unfolding_all exact (x.fits.grpAt.idem :)), (by with_unfolding_all exact (x.fits.grpAt.cen :))⟩,
  fun eR h => ⟨(by with_unfolding_all exact ((x.fits.cen ((eR)) ((h))).amb : _)), (by with_unfolding_all exact ((x.fits.cen ((eR)) ((h))).mt : _))⟩⟩

def stTw (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) : St P :=
  ⟨oTw x N, fitsTw x N, x.G_eq, x.etaF, x.bk, m, hc, hh, sideTw x N, r, hp⟩

end GlobalTheory.HeightCounting.Up

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwistChoice

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev thTw (D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) : TwNew D :=
  ⟨D.ntw, D.nexp, D.nStage_trivialCharacter_coeff_eq, th, D.ntwbr, D.ntwbr_ind⟩

theorem carried_thTw (D0 D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) (h : Carried D0 D) :
    Carried D0 (thTw D th).toD7 :=
  ⟨⟨{ h.exp.gal with }, { h.exp.set with }, { h.exp.frm with }, h.exp.br, h.exp.av⟩, h.emb⟩

end GlobalTheory.HeightCounting.Up

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralLocalStableIntegral
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.CenAtLoc

theorem mapCoef_mem_center' {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) (z : MonoidAlgebra R G)
    (hz : ∀ a, z * a = a * z) :
    Formalism.MainNotions.PairedCharacterCondition.mapCoef f z ∈ Subalgebra.center S (MonoidAlgebra S G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    have e : MonoidAlgebra.of S G m = MonoidAlgebra.mapRingHom G f (MonoidAlgebra.of R G m) := by
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]
    rw [e]
    show MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _ =
      MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _
    rw [← map_mul, ← map_mul, hz]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem zlStable_of_allT {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G}
    {ψ1 : P1 →* D.what₂.LLˣ} {X0 : BaseLevelRowSide D} {tp : D.what₂.Tup → T} {eG : G ≃* G0g D.nd}
    (h : AllT D A P0 ψ0 P1 ψ1 X0 tp eG) : GlobalTheory.PendOf.ZLStable D := by
  intro i z hz x
  have hc := mapCoef_mem_center' D.what₂.embLL z hz
  have key : ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ x : D.what₂.MtL μ j, ∃ y : D.what₂.MtL μ j,
      D.what₂.jMt μ j y = D.ntypes.cenMt μ j ⟨_, hc⟩ (D.what₂.jMt μ j x) := by
    intro μ j h1 h2 x
    obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
    let a : MonoidAlgebra D.what₂.LL G := MonoidAlgebra.ofCoeff (Finsupp.equivMapDomain eG.symm.toEquiv z.coeff)
    have ha : ∀ g : G, D.what₂.embLL (a.coeff g) =
        ((⟨_, hc⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g) := by
      intro g
      simp [a, Formalism.MainNotions.PairedCharacterCondition.mapCoef, Finsupp.equivMapDomain_apply]
    obtain ⟨-, -, h3⟩ := h.cen μ ⟨_, hc⟩ a ha
    have := h3 k ((h.eMt k μ).symm x)
    refine ⟨h.eMt k μ (((A.fam.L k (tp μ)).S.lvlOp (A.fam.L k (tp μ)).r (A.fam.lvlA P0 ψ0).P (A.fam.lvlA P0 ψ0).ψ a).mulVec ((h.eMt k μ).symm x)), ?_⟩
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  obtain ⟨y, hy⟩ := key (D.nd.mu i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 x
  refine ⟨y, ?_⟩
  rw [hy]
  unfold NTypes.onMt
  rw [dite_eq_left hc]

end GlobalTheory.CenAtLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure CopyN (D : D7) {D' : D7} (N : TwNew D') (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) : Prop where
  cp : GlobalTheory.TwInputs.Move.CopyTw D N.toD7 ι e
  ThetaPsi : HEq D.ntw.ThetaPsi N.tw.ThetaPsi
  topO : HEq D.ntw.topO N.tw.topO
  finLam : HEq D.ntw.finLam N.tw.finLam
  jL : HEq D.ntw.jL N.tw.jL
  s2 : HEq D.ntw.s2 N.tw.s2
  lamG : HEq D.ntw.lamG N.tw.lamG
  Xv : HEq D.ntw.Xv N.tw.Xv
  qs : HEq D.ntw.qs N.tw.qs
  res : HEq D.ntw.res N.tw.res
  eLL0 : ∀ g g', HEq g g' → e (N.ex.eLL0 g') = D.nexp.eLL0 g
  twPsi : HEq D.nexp.twPsi N.ex.twPsi
  twDel : HEq D.nexp.twDel N.ex.twDel
  eH : HEq D.nexp.eH N.ex.eH

theorem CopyN.carried {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyN D N ι e) :
    Carried D N.toD7 := by
  refine ⟨h.cp.toSameExport, fun i i' hi x x' hx => ?_⟩
  have hx' : x = e x' := Subtype.ext (D.what₂.embLL.injective
    (hx.trans ((congrArg N.toD7.what₂.embLL (h.cp.LL0 x')).symm.trans (h.cp.embLL _))))
  subst hx'
  exact ⟨h.cp.emb0 i i' hi x', h.cp.emb0b i i' hi x'⟩

end GlobalTheory.HeightCounting.Up

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedDataReciprocity
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsTwTied
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EMtTied
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.Col2.EMt

theorem eMtTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch) (C : ColsTiedSym (I.rec7 l Z)) (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)), (∀ u F G, inner ℂ ((I.rec7 l Z).eMt u F) ((I.rec7 l Z).eMt u G) = I.ipMt l u I.mu0 F G) → (∀ u (a : (I.rec7 l Z).what₂.Tup), a ≠ (I.rec7 l Z).what₂.mu0 → ∀ F G, inner ℂ ((I.rec7 l Z).eMtTw u a F) ((I.rec7 l Z).eMtTw u a G) = I.ipMt l u a F G) → Formalism.L2.Rows.EMtTied (I.rec7 l Z) C t := by
  intro B X I hOk hP l Z l0 nch tp C t h0 h1
  refine ⟨fun u F G => ?_, fun u a ha F G => ?_⟩
  · rw [h0 u F G]
    exact (GlobalTheory.Mem.Col2.IpMt.ipMt_tie I hOk hP l Z u I.mu0 (C.forms u).jM (C.forms u).per.2.1 (C.forms u).per.2.2).1 F G
  · rw [h1 u a ha F G]
    exact (GlobalTheory.Mem.Col2.IpMt.ipMt_tie I hOk hP l Z u a (t.ptE.jM u a) (t.ptE.per u a ha).2.1 (t.ptE.per u a ha).2.2).1 F G

end GlobalTheory.Mem.Col2.EMt

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

theorem WPt.colsTwTied : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), q.O.ex.tw = q.w.tw q.Z ∧ ∃ tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes q.x.n.tp q.x.col.C (q.w.tw q.Z), TC.StdTw q.w.I q.w.l q.Z q.w.l0 tw ∧ Formalism.L2.Rows.EMtTied (q.w.D q.Z) q.x.col.C tw := by
  intro 𝒮 K q
  refine ⟨?_, ?_⟩
  · exact congrArg (fun s : Σ (Gt : GatTies (q.w.D q.Z)) (cmp : LatCmp (q.w.D q.Z)) (tw : TwForms (q.w.D q.Z)),
      KerFam (q.w.D q.Z) Gt cmp tw (ofObj q.O).Gy => s.2.2.1) q.x.ker_eq
  · obtain ⟨tw, htw⟩ := GlobalTheory.T.trueColumnChoice_exists_standardChainData q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ q.x.n.tp q.x.col.C q.x.n.xi q.x.col.std q.x.col.stdLv
    exact ⟨tw, htw, GlobalTheory.Mem.Col2.EMt.eMtTied q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ q.x.n.tp q.x.col.C tw q.x.what₂.emt0 q.x.what₂.emt⟩

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtraTiedCol
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Top.Bl.WPt.extraTied_col : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), Formalism.L2.Forms.ColsExtraTiedS q.x.col.full q.O.ex ∧ ∃ g : Formalism.L2.G.GroupCompatibilityAll (q.w.D q.Z) q.O.gatT q.O.ex.cmp, HEq g q.x.col.g ∧ g.herm = q.x.col.full.1.to0 ∧ g.forms = fun u => (q.x.col.C.forms u).to0 := by
  intro 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  obtain ⟨L, gatT, Gx, Gy, K', X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def,
    errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kt, div, thT, obj, ox, real,
    dsig_eq, hgauge, good⟩ := x
  obtain ⟨⟨C, std, stdLv, full, stdDt, Gt, cmp', g, herm_eq, forms_eq, gpl⟩, isRec, om⟩ := col
  dsimp only at hlev herrX ker_eq ⊢
  cases ker_eq
  exact ⟨⟨⟨hlev, herrX, gpl⟩, kt.iw, kt.iw_pos⟩, g, HEq.rfl, herm_eq, forms_eq⟩
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl


theorem ColW.cf_eq {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) :
    Fr.at (w.st Z) f = TC.cf w.I w.l Z := by
  have h := w.C_eq
  have : Fr.at (w.st Z) w.I.C = TC.cf w.I w.l Z := rfl
  rw [← this, h]


end GlobalTheory.Mem.Top.Bl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevels
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped ComplexOrder
open Formalism.L2.Indef Formalism.IndefR.Cx

noncomputable section

namespace GlobalTheory.Mem.R3.IotaRd

open Formalism.IndefR.Cx.CxData

theorem theta_eq_proj {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A) (b : Bool)
    (eV : ∀ t, (Fin ((lv (fc X.zs) b).nV t) → K) →ₗ[K] A.FR t) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv b) (hDn : X.DnLev cv b) (hUp : X.UpLev cv b) (hC : X.CoordinatesInGoodPart cr cv b)
    (hV : ∀ t F, eV t F ∈ cv.v0R X.zs b t)
    (hO : ∀ t F (x : Fin ((lv (fc X.zs) b).dQ t) → K),
      cv.hR t (cr.toR X.zs b t x) (eV t F) = cv.hR t (cr.toR X.zs b t x) (cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F)))
    (t : Bs.Tup) (F : Fin ((lv (fc X.zs) b).nV t) → K) :
    X.Θ t (X.jR t (eV t F)) = X.Θ t (X.jR t (cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F))) := by
  set q : A.FR t := cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F) with hq
  have hdV : eV t F - q ∈ cv.v0R X.zs b t := sub_mem (hV t F) (hC t _)
  have hdo : ∀ x, cv.hR t (cr.toR X.zs b t x) (eV t F - q) = 0 := by
    intro x; rw [map_sub, hO t F x, sub_self]
  have hjV : X.jR t (eV t F - q) ∈ X.V0C cv b t := Submodule.subset_span ⟨_, hdV, rfl⟩
  have hΘE : X.Θ t (X.jR t (eV t F - q)) ∈ X.EEl b := hDn t ⟨_, hjV, rfl⟩
  have horth : ∀ e ∈ X.EEl b, ⟪e, X.Θ t (X.jR t (eV t F - q))⟫_ℂ = 0 := by
    intro e he
    rw [← LinearMap.adjoint_inner_left]
    have h1 : LinearMap.adjoint (X.Θ t) e ∈
        Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) := by
      rw [hRL t]
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_range_self _ e, hUp t (Submodule.mem_map_of_mem he)⟩
    have h2 : Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) ≤
        (Submodule.span ℂ {X.jR t (eV t F - q)})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hJ, hdo x, map_zero]
    have h3 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 h1)
    rwa [inner_eq_zero_symm] at h3
  have h0 : X.Θ t (X.jR t (eV t F - q)) = 0 := inner_self_eq_zero.1 (horth _ hΘE)
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.Mem.R3.IotaRd

namespace GlobalTheory.Mem.R3.IotaRd

open Formalism.IndefR.Cx.CxData Formalism.IndefR.Links.EvTie

theorem sharp_downTo' (D : D7) (μ) (j : ℕ) : (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RowSide.sharp D).downTo μ j).comp (D.what₂.io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [ih]; rfl

theorem sharp_iota' (D : D7) (μ) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [sharp_downTo']; rfl

theorem rowSideDef3_both : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → RowSideDef3 D A3.A (RowSide.sharp D) F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s1Of R F)) Y.tup Z.eRR Y.jA ∧ RowSideDef3 D A3.A X0.s F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s0Of R F)) Y.tup Z.eRR0 Y.jA0 := by
  intro hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  obtain ⟨h1, h0⟩ := GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector hCusp D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  have hC := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok
  have hout : ∀ t y, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).Θ t ((R.toCx3 F).jR t y)) = R.Th t (R.jX t y) :=
    fun t y => rfl
  have hb : ∀ t (P : Subgroup G) (ψ : P →* D.what₂.LLˣ), BlockHyp (A3.A.fam.R t) (A3.A.fam.lvl P ψ) A3.A.fam.v0 1 :=
    fun t P ψ => ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
  have hrow : ∀ t (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) x, rowForm A3.A P ψ t ((rV0 D A3.A P ψ t) *ᵥ x) =
      (A3.A.fam.R t).S.basis.equivFun.symm ((A3.A.fam.R t).vE (A3.A.fam.lvl P ψ) *ᵥ x) := by
    intro t P ψ x
    unfold rowForm rV0
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, BlockDat.lf_lvl_vE (hb t P ψ)]
  have k1 : ∀ t x, R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t (rV0 D A3.A F.P1 F.ψ1 t *ᵥ x))) =
      Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding
        ((A3.indefDown (s1Of R F)).ι t *ᵥ ((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x)))) := by
    intro t x
    have e := theta_eq_proj (R.toCx3 F) F.cr F.cv true (F.eV (R.toCx3 F).zs) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1
      (hC.levs true).2.2 (definite_coordinates_in_good_part _ true) (evTie_of_ok hOk F _).1 (evTie_of_ok hOk F _).2 t x
    have k := ((R.toCx3 F).key_row F.cr true (hC.what₂ true).1 (hC.ratMu true) t
      (((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x))).trans ((R.toCx3 F).iC_cpt' F.cr true t _)
    exact (congrArg (fun y => R.Th t (R.jX t y)) (hrow t F.P1 F.ψ1 x)).trans
      ((hout t _).symm.trans (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)) (e.trans k.symm)))
  have k0 : ∀ t x, R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t (rV0 D A3.A F.P0 F.ψ0 t *ᵥ x))) =
      Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding
        ((A3.indefDown (s0Of R F)).ι t *ᵥ ((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x)))) := by
    intro t x
    let eV0 : ∀ t, (Fin ((lv (F.fc (R.toCx3 F).zs) false).nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A3.fam3.amb3.FR t := fun t =>
      ((A3.A.fam.R t).S.basis.equivFun.symm : (Fin (A3.A.fam.R t).S.dim → D.what₂.LL) →ₗ[D.what₂.LL] (A3.A.fam.R t).S.Forms) ∘ₗ
        ((A3.A.fam.R t).vE (A3.A.fam.lvl F.P0 F.ψ0)).mulVecLin
    have e := theta_eq_proj (R.toCx3 F) F.cr F.cv false eV0 hC.jIsoR (hC.levs false).1 (hC.levs false).2.1
      (hC.levs false).2.2 (definite_coordinates_in_good_part _ false) (fun t y => ⟨y, rfl⟩)
      (fun t y x => evTie_block (A3.A.fam.R t) (A3.A.fam.lvl F.P0 F.ψ0) ((R.toCx3 F).zs.Z t)
        (BlockDat.HZ_det hOk.ok2.conj (hOk.ok2.what₂ t) (fun χ hχ => hOk.ok2.irr χ hχ)) x y) t x
    have k := ((R.toCx3 F).key_row F.cr false (hC.what₂ false).1 (hC.ratMu false) t
      (((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x))).trans ((R.toCx3 F).iC_cpt' F.cr false t _)
    exact (congrArg (fun y => R.Th t (R.jX t y)) (hrow t F.P0 F.ψ0 x)).trans
      ((hout t _).symm.trans (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)) (e.trans k.symm)))
  refine ⟨⟨Y.formsA, Y.latA, ?_⟩, ⟨Y.formsAtBottomLevel, Y.latA0, ?_⟩⟩
  · intro t x
    apply Y.Ish.jE.injective
    apply Subtype.val_injective
    have e1 := h1 t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec x)
    have e2 := Z.jEE (((A3.indefDown (s1Of R F)).ι t).mulVec (((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t).mulVec x))
    rw [k1] at e1
    rw [sharp_iota']
    exact e1.trans e2.symm
  · intro t x
    apply Y.Iz.jE.injective
    apply Subtype.val_injective
    have e1 := h0 t ((rV0 D A3.A F.P0 F.ψ0 t).mulVec x)
    have e2 := Z.jEE0 (((A3.indefDown (s0Of R F)).ι t).mulVec (((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t).mulVec x))
    rw [k0] at e1
    exact e1.trans e2.symm

end GlobalTheory.Mem.R3.IotaRd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevelsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowSide_definition_both_levels : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → RowSideDef3 D A3.A (RowSide.sharp D) F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s1Of R F)) Y.tup Z.eRR Y.jA ∧ RowSideDef3 D A3.A X0.s F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s0Of R F)) Y.tup Z.eRR0 Y.jA0 := by
  first | exact @GlobalTheory.Mem.R3.IotaRd.rowSideDef3_both | exact GlobalTheory.Mem.R3.IotaRd.rowSideDef3_both | (intros; apply GlobalTheory.Mem.R3.IotaRd.rowSideDef3_both <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowRatWOfRowTest
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem rowRatW_of_rowTest :
    (AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) → RowRatW :=
  by
    intro H
    have h := (StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans H
    apply h.trans
    apply StepW.of_all
    intro K B f T w hK hF G Z hX Wt z a b _ c d _ _ _ _
    exact G Z hX Wt z a b c d

end GlobalTheory.Mem.LiteralAutomorphy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothProjectiveRefinementPolyFan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothProjectiveRefinementPolyFan
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem GlobalTheory.PolFan.exists_smooth_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ' γ → ψ.LinearOn γ := by
  intro E _ _ _ H q ψ hD hψ hT
  obtain ⟨φ, lab, hφ, hφT, hlT, hSL, hsub⟩ := GlobalTheory.T.exists_invariant_simplicial_labelled_fan_refinement E H q ψ hD hψ hT
  obtain ⟨φ', h1, h2, h3, hsub'⟩ := GlobalTheory.T.exists_invariant_smooth_refinement_polyFan E H q φ lab hD hφ hφT hlT hSL
  exact ⟨φ', h1, h2, h3, fun X _ _ _ _ hX m γ hγ => (hsub'.trans hsub).linearOn hX hγ.isCell⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothProjectiveRefinementPolyFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_smoothProjective_refinement_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ' γ → ψ.LinearOn γ := by
  first | exact @GlobalTheory.PolFan.exists_smooth_refinement | exact GlobalTheory.PolFan.exists_smooth_refinement | (intros; apply GlobalTheory.PolFan.exists_smooth_refinement <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLargeGrid
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem evLgG_gridA_of_exGrid : ExGrid → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) := by
  classical
  intro h
  obtain ⟨CF0, hCF⟩ := h
  refine ⟨CF0, fun CF hC => ?_⟩
  refine ⟨1 / 100, by norm_num, fun eps C8 C5 c6 Cb _ _ _ _ => ?_⟩
  obtain ⟨x₀, hx⟩ := hCF eps CF hC
  refine ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ =>
    ⟨x₀, fun K _ _ _ hKe hKx _ => ?_⟩⟩⟩⟩
  have hS := fun (P : Pre) (f : Fr P) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) (hΞ : Ξ.Finite) =>
    hx K.s hKe hKx P f Ξ hΞ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f _ _ Ξ => if hΞ : Ξ.Finite then Classical.choose (hS P f Ξ hΞ) else ∅, ?_, ?_, ?_⟩
  · intro B f F z hz
    simp at hz
  · intro B f F F₀ Ξ z hz
    by_cases hΞ : Ξ.Finite
    · simp only [dif_pos hΞ] at hz
      exact (Classical.choose_spec (hS B f Ξ hΞ)).1 z hz
    · simp [dif_neg hΞ] at hz
  · intro B f T _ hHas _ _ C W V S N G
    have hfin := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
    have hspec := (Classical.choose_spec (hS B.toPre f (T.set f) hfin)).2
    refine hspec ⟨B, C, W, V, S, N, G⟩ f (T.set f) rfl HEq.rfl HEq.rfl ?_
    intro z hz
    have h2 := hHas.2 z
    simp only [dif_pos hfin] at h2
    exact h2 hz

end GlobalTheory.Mem.LiteralAutomorphy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelation
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

section Gen

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}


variable (R) in
def EigVec (i : Fin D.R.m) (k : ℕ) (Q : PlE D.host) (Rr : Finset (GA D (Wc D i))) (c : ↥D.LL0) (v : (R.HW i (sg0 D A3.A)).H) : Prop :=
  hkNorm R i k Q • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e v) =
    D.what₂.embLL ((c : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e v

theorem eigAd_iff_eigVec (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : EigAd Y Sb eig ↔
    ∀ (i : Fin D.R.m) σ k Q α Rr, HkDat R Sb i k Q α Rr → D.nd.goodRow σ → ∀ y ∈ D.what₂.isot (i.1 + 1) σ,
      EigVec R i k Q Rr (eig (i.1 + 1) σ k Q) (Y.mj.eW i y) := Iff.rfl

theorem EigVec.congr {i : Fin D.R.m} {k : ℕ} {Q : PlE D.host} {Rr : Finset (GA D (Wc D i))} {c : ↥D.LL0}
    {v v' : (R.HW i (sg0 D A3.A)).H} (h : EigVec R i k Q Rr c v) (e : HEq v' v) : EigVec R i k Q Rr c v' := eq_of_heq e ▸ h

end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (L : LocAll (lay0 (Dof x)))

theorem eigVec_loc {i k Q Rr c v} (h : EigVec x.m.z.R i k Q Rr c v) :
    EigVec (datL x L).R i k Q Rr c v := by
  with_unfolding_all exact h

end GlobalTheory.HeightCounting.Fin3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceSquare
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory


set_option maxHeartbeats 4000000 in
open GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.BigTop.Fun in
theorem Mem.LiteralAutomorphy.trSq_holds : GlobalTheory.Mem.LiteralAutomorphy.TrSq := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι h M σ hs
  obtain ⟨⟨hpre, -, -, ⟨f, f', hff, hC, hC'⟩, hbase, hxi, -, -⟩, hg, -, -⟩ := h
  clear S S' W W'
  obtain ⟨B, C₁, W₁, V₁, S₁, N₁, G₁⟩ := X
  obtain ⟨B', C₂, W₂, V₂, S₂, N₂, G₂⟩ := X'
  cases B; cases B'
  dsimp only at hpre
  subst hpre
  obtain rfl := eq_of_heq hff
  have hv0 : G'.pl.v0 = G.pl.v0 := eq_of_heq hg.v0
  have hw : G'.pl.w = G.pl.w := eq_of_heq hg.w
  have hchi : G'.ch.chiH = G.ch.chiH := eq_of_heq hg.chiH
  have hx : L'.xiH μ₀' = L.xiH μ₀ := by have := eq_of_heq (hxi μ₀'); rwa [hbase] at this
  have e_levQ : levQ G'.pl = levQ G.pl := by
    unfold levQ Places.S0 condExp; rw [hv0]; exact (Eq.refl (levQ G.pl))
  have e_condE : SqNum.condE G'.pl = SqNum.condE G.pl := by
    unfold SqNum.condE Places.S0 condExp; rw [hv0, hw]; exact (Eq.refl (SqNum.condE G.pl))
  have e_condF : condF G'.pl = condF G.pl := by
    unfold condF Places.S0 condExp; rw [hv0]; exact (Eq.refl (condF G.pl))
  have hmu : L'.C.mu0 = L.C.mu0 := by rw [hC, hC']; exact (Eq.refl f'.mu0)
  have heta : L'.C.eta = L.C.eta := by rw [hC, hC']; exact (Eq.refl f'.eta)
  have hd1 : L'.C.del = L.C.del := by rw [hC, hC']; exact (Eq.refl f'.del)
  have hd2 : L'.C.del' = L.C.del' := by rw [hC, hC']; exact (Eq.refl f'.del')
  have e_nu : ∀ i j, nuH G' μ₀' i j = nuH G μ₀ i j := by
    intro i j; unfold nuH; rw [hmu, hx, hchi]; exact (Eq.refl (nuH G μ₀ i j))
  have e_beta : ∀ i j, betaH G' i j = betaH G i j := by
    intro i j; unfold betaH; rw [heta, hchi]; exact (Eq.refl (betaH G i j))
  have e_alpha : ∀ i j, alphaH L' μ₀' i j = alphaH L μ₀ i j := by
    intro i j; unfold alphaH; rw [hmu, hx, heta]; exact (Eq.refl (alphaH L μ₀ i j))
  have e_del : ∀ c, delOf L' c = delOf L c := by
    intro c; unfold delOf; rw [hd1, hd2]; exact (Eq.refl (delOf L c))
  have eT : ∀ i j s χ x, IsTor G' i j s χ x ↔ IsTor G i j s χ x := by
    intro i j s χ x; unfold IsTor; rw [e_condF]; exact (Iff.refl (IsTor G i j s χ x))

  let hk1 : ∀ {N : ℕ}, Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) N → Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) N :=
    fun h => { f := ((h.f)), n := ((h.n)), unitary := ((h.unitary)), cont := ((h.cont)), aut := ((h.aut)), norm := ((h.norm)), par := ((h.par)), unr := ((h.unr)) }
  let wt1 : ∀ {δ : ℂ} {a d : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) a d → ℂ}, Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ a d e0 →
      Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ a d ((e0)) :=
    fun w => { chV := hk1 w.chV, chV' := hk1 w.chV', ep := w.ep, ep' := w.ep', ep_pm := w.ep_pm, nz := ((w.nz)), Om := ((w.Om)), maps := ((w.maps)), add := ((w.add)), smul := ((w.smul)), one := ((w.one)), mul := ((w.mul)), lift := ((w.lift)), inert := ((w.inert)), split := ((w.split)) }
  let pt1 : ∀ {δ t0 : ℂ} {Q : ℕ}, GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q → GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q :=
    fun P => { a := P.a, d := P.d, a_le := P.a_le, d_even := P.d_even, W := wt1 P.W, crv := ((P.crv)), pt0 := ((P.pt0)), e0 := ((P.e0)), vac := ((P.vac)), n := ((P.n)), wt := ((P.wt)), F := ((P.F)), pres := ((P.pres)), fix := ((P.fix)), J := ((P.J)), J_le := ((P.J_le)), idx_ne := ((P.idx_ne)), idx_le := ((P.idx_le)), eig := ((P.eig)) }

  let hk2 : ∀ {N : ℕ}, Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) N → Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) N :=
    fun h => { f := ((h.f)), n := ((h.n)), unitary := ((h.unitary)), cont := ((h.cont)), aut := ((h.aut)), norm := ((h.norm)), par := ((h.par)), unr := ((h.unr)) }
  let wt2 : ∀ {δ : ℂ} {a d : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) a d → ℂ}, Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ a d e0 →
      Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ a d ((e0)) :=
    fun w => { chV := hk2 w.chV, chV' := hk2 w.chV', ep := w.ep, ep' := w.ep', ep_pm := w.ep_pm, nz := ((w.nz)), Om := ((w.Om)), maps := ((w.maps)), add := ((w.add)), smul := ((w.smul)), one := ((w.one)), mul := ((w.mul)), lift := ((w.lift)), inert := ((w.inert)), split := ((w.split)) }
  let pt2 : ∀ {δ t0 : ℂ} {Q : ℕ}, GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q → GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q :=
    fun P => { a := P.a, d := P.d, a_le := P.a_le, d_even := P.d_even, W := wt2 P.W, crv := ((P.crv)), pt0 := ((P.pt0)), e0 := ((P.e0)), vac := ((P.vac)), n := ((P.n)), wt := ((P.wt)), F := ((P.F)), pres := ((P.pres)), fix := ((P.fix)), J := ((P.J)), J_le := ((P.J_le)), idx_ne := ((P.idx_ne)), idx_le := ((P.idx_le)), eig := ((P.eig)) }

  have btr1 : ∀ {δ t0 : ℂ} {Q : ℕ} (i j : Fin (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩).R.m)
      (P P' : GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q), IsBottom G μ₀ i j (SqNum.condE G.pl) P P' →
        IsBottom G' μ₀' i j (SqNum.condE G'.pl) (pt1 P) (pt1 P') := by
    intro δ t0 Q i j P P' h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨(h1), ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_beta, e_nu]; exact (h2)
    · rw [e_alpha, e_nu]; exact (h3)
    · rw [e_condE]; exact (h4)
    · rw [e_condE]; exact (h5)
    · rw [e_condE]; exact (h6)

  have btr2 : ∀ {δ t0 : ℂ} {Q : ℕ} (i j : Fin (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩).R.m)
      (P P' : GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q), IsBottom G' μ₀' i j (SqNum.condE G'.pl) P P' →
        IsBottom G μ₀ i j (SqNum.condE G.pl) (pt2 P) (pt2 P') := by
    intro δ t0 Q i j P P' h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    rw [e_beta, e_nu] at h2
    rw [e_alpha, e_nu] at h3
    rw [e_condE] at h4 h5 h6
    exact ⟨(h1), (h2), (h3), (h4), (h5), (h6)⟩
  refine ⟨fun hb => ?_, fun i j s c x y h1 h2 h3 h4 => ?_⟩
  · obtain ⟨δ, t0, hb⟩ := hb
    rw [e_levQ] at hb
    obtain ⟨δ', t0', hb'⟩ := hs.norms ⟨δ, t0, fun ij => by
      obtain ⟨P, P', hP, -, -⟩ := hb ((ij))
      exact ⟨pt2 P, pt2 P', btr2 ((ij.1)) ((ij.2)) P P' hP, trivial, trivial⟩⟩
    refine ⟨δ', t0', fun ij => ?_⟩
    rw [e_levQ]
    obtain ⟨P, P', hP, n1, n2⟩ := hb' ((ij))
    exact ⟨pt1 P, pt1 P', btr1 ij.1 ij.2 P P' hP, (n1), (n2)⟩
  · rw [eT, e_nu] at h3
    rw [eT, e_nu, e_del] at h4
    exact hs.toric ((i)) ((j)) s c x y h1 ((h2)) ((h3)) ((h4))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridExistenceOfPieces
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem gridKey_heq_of_eq_preData_components (P P' : Pre) (h : P = P') (v : Pl P.host.F) (v' : Pl P'.host.F) (w : Pl P.host.F → Pl P.host.E)
    (w' : Pl P'.host.F → Pl P'.host.E) (c : ℕ → HChar P.host.E) (c' : ℕ → HChar P'.host.E) (hv : HEq v v') (hw : HEq w w')
    (hc : HEq c c') :
    HEq ((v, w v, fun a : Fin P.R.m => c (a.1 + 1)) : GKey P) ((v', w' v', fun a : Fin P'.R.m => c' (a.1 + 1)) : GKey P') := by
  subst h; subst hv; subst hw; subst hc; rfl

theorem gkeyOf_heq {X X' : Stages} {T T' : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {L' : Formalism.IndefR.Links.LevCh X'.toD7 T'} {sc : GlobalTheory.ChiGrid.Consts}
    {G : GridData L sc} {G' : GridData L' sc} (h : GAgree G G') (hp : X'.B.toPre = X.B.toPre) : HEq (gkeyOf G') (gkeyOf G) :=
  gridKey_heq_of_eq_preData_components _ _ hp _ _ _ _ _ _ h.v0 h.w h.chiH

end GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Mem.LiteralAutomorphy


set_option maxHeartbeats 3200000 in
theorem exGrid_of : WeilEx → IsEx → NFAll → NFSq → CarryG → CarryW → CarryS → TrEasy → TrPhase → TrJet → TrBot → TrSq → KeyFin →
    GKeyFin → ExGrid := by
  classical
  intro h1 h2 h3 h4 cG cW cS t1 t2 t3 t4 t5 kF gF
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  obtain ⟨a4, h4⟩ := h4
  refine ⟨max a1 (max a2 (max a3 a4)), fun ε CF hC => ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x2, h2⟩ := h2 ε CF (le_of_max_le_left (le_of_max_le_right hC))
  obtain ⟨x3, h3⟩ := h3 ε CF (le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hC)))
  obtain ⟨x4, h4⟩ := h4 ε CF (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hC)))
  refine ⟨max x1 (max x2 (max x3 x4)), fun s he hx P f Ξ hΞ => ?_⟩
  have hx1 := le_of_max_le_left hx
  have hx2 := le_of_max_le_left (le_of_max_le_right hx)
  have hx3 := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hx))
  have hx4 := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hx))
  have per : ∀ (κ : Key P) (γ : GKey P), ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
      ∀ (X : Stages) (f' : Fr X.B.toPre), X.B.toPre = P → HEq f' f → ∀ large₂ : SizeData₂ X.toD7, large₂.sc = s → GlobalTheory.SqTop.Rec large₂ →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) [Field Ks]
        [NumberField Ks] [Algebra Ks X.toD7.what₂.LL] (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F →
        R.C = Fr.at X f' → TwistPlacesOffPrimeQZero R.toLevCh → HEq (keyOf R.toLevCh) κ → ∀ G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩,
        HEq (gkeyOf G₀) γ → (∀ z ∈ S, z ∈ Set.range X.toD7.what₂.embLL) →
        ∃ G : GridData R.toLevCh ⟨1, CF, s.b⟩, gkeyOf G = gkeyOf G₀ ∧ Full R G := by
    intro κ γ
    by_cases H : ∃ (X : Stages) (f' : Fr X.B.toPre) (_ : X.B.toPre = P) (_ : HEq f' f) (large₂ : SizeData₂ X.toD7) (_ : large₂.sc = s)
        (_ : GlobalTheory.SqTop.Rec large₂) (Γ : Type) (_ : Group Γ) (_ : Fintype Γ) (Pl0 T : Type)
        (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks)
        (_ : Algebra Ks X.toD7.what₂.LL) (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A) (G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩),
        HidaSetting large₂ R F ∧ R.C = Fr.at X f' ∧ TwistPlacesOffPrimeQZero R.toLevCh ∧ HEq (keyOf R.toLevCh) κ ∧ HEq (gkeyOf G₀) γ
    swap
    · exact ⟨∅, by simp, fun X f' a b large₂ c r Γ _ _ Pl0 T A Ks _ _ _ R F d e g i G₀ j _ =>
        absurd ⟨X, f', a, b, large₂, c, r, Γ, _, _, Pl0, T, A, Ks, _, _, _, R, F, G₀, d, e, g, i, j⟩ H⟩
    obtain ⟨X0, f0, a0, b0, Lg0, rfl, r0, Γ0, _, _, Pl00, T0, A0, Ks0, _, _, _, R0, F0, G00, d0, e0, g0, i0, j0⟩ := H
    obtain ⟨W0, hW0, ⟨S0⟩⟩ := h1 _ Lg0 he hx1 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G00
    obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS, hIs⟩ := h2 _ Lg0 he hx2 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G00 W0 hW0 S0
    obtain ⟨N, hN, hAll⟩ := h3 _ Lg0 he hx3 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 _ hIs rfl
    obtain ⟨N2, hN2, hSq⟩ := h4 _ Lg0 he hx4 r0 T0 R0.toLevCh A0.μ0 d0.core.lev G00
    obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N)) ℚ N) := ⟨Module.finBasis ℚ N⟩
    obtain ⟨b2⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N2)) ℚ N2) := ⟨Module.finBasis ℚ N2⟩
    refine ⟨(Finset.univ.image fun i => ((b i : N) : ℂ)) ∪ Finset.univ.image fun i => ((b2 i : N2) : ℂ), ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
    intro X f' a b' large₂ hs hr Γ _ _ Pl0 T A Ks _ _ _ R F d e' g i G₀ j hz

    have rng : ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (bK : Module.Basis (Fin (Module.finrank ℚ K)) ℚ K),
        (∀ i, ((bK i : K) : ℂ) ∈ Set.range X.toD7.what₂.embLL) → Set.range (algebraMap K ℂ) ⊆ Set.range X.toD7.what₂.embLL := by
      intro K _ bK hK
      rintro _ ⟨y, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← bK.sum_repr y, map_sum]
      refine X.toD7.what₂.embLL.fieldRange.sum_mem fun i _ => ?_
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact X.toD7.what₂.embLL.fieldRange.mul_mem (SubfieldClass.ratCast_mem _ _) (hK i)
    have r1 := rng N b fun i => hz _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have r2 := rng N2 b2 fun i => hz _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have hk : HEq (keyOf R.toLevCh) (keyOf R0.toLevCh) := i.trans i0.symm
    have hpre : X.B.toPre = X0.B.toPre := a.trans a0.symm
    have key : ∀ (P P' : Pre) (_ : P = P') (k : Key P) (k' : Key P'), HEq k k' → ∀ x ∈ k, ∃ y ∈ k', HEq x.1 y.1 ∧ HEq x.2 y.2 := by
      rintro P _ rfl k k' h x hx
      obtain rfl := eq_of_heq h
      exact ⟨x, hx, HEq.rfl, HEq.rfl⟩
    have hι : ∀ t : T, ∃ t0 : T0, HEq (R.xiH t) (R0.xiH t0) ∧ HEq (R.Q t) (R0.Q t0) := fun t => by
      obtain ⟨_, ⟨t0, rfl⟩, h⟩ := key _ _ hpre _ _ hk _ ⟨t, rfl⟩
      exact ⟨t0, h⟩
    choose ι hι using hι
    have one : ∀ (P P' : Pre) (_ : P = P'), HEq (1 : HChar P.host.E) (1 : HChar P'.host.E) := by rintro P _ rfl; rfl
    have hb : ι A.μ0 = A0.μ0 := d0.core.lev.xi_inj (by
      rw [d0.core.lev.xi_base]
      have := (hι A.μ0).1
      rw [d.core.lev.xi_base] at this
      exact eq_of_heq (this.symm.trans (one _ _ hpre)))
    have hL : LAgree R0.toLevCh R.toLevCh A0.μ0 A.μ0 ι :=
      ⟨hpre, d0.core.lev, d.core.lev, ⟨f0, f', b'.trans b0.symm, e0, e'⟩, hb, fun t => (hι t).1, fun t => (hι t).2, d0.betaX,
        d.betaX⟩
    obtain ⟨G, hG⟩ := cG _ _ _ _ _ _ _ _ _ hL _ G00
    obtain ⟨W, hW, hWA⟩ := cW _ _ _ _ _ Γ Pl0 A Ks R _ ι hL d.core.chain d.core.models _ G00 G hG W0
    obtain ⟨S', hS'⟩ := cS _ _ _ _ _ _ _ _ _ hL _ G00 G hG W0 W hWA S.toGridChoice
    have hA : Agree S.toGridChoice S' A0.μ0 A.μ0 ι := ⟨hL, hG, hWA, hS'⟩
    have h2' := h2 _ large₂ (hs ▸ he) (hs ▸ hx2) Γ Pl0 T A Ks R F d
    rw [hs] at h2'
    obtain ⟨M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hS2, hIs'⟩ := h2' G W hW S'
    have gk : gkeyOf G = gkeyOf G₀ := eq_of_heq ((gkeyOf_heq hG hpre).trans (j0.trans j.symm))
    refine ⟨G, gk, W, M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hIs', ?_, ?_⟩
    · obtain ⟨u1, u2, u3⟩ := t1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N (algebraMap N ℂ)
      have hAll' : AllIn (algebraMap N ℂ) S' A.μ0 := ⟨u1 hAll.chars, u2 hAll.root,
        t2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.phase, t3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.jet, u3 hAll.ratios,
        t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.bot⟩
      subst hS2
      exact hAll'.numbersIn.mono r1
    · exact (t5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N2 _ hSq).mono r2
  obtain ⟨𝒦, hK, H⟩ := kF P Ξ hΞ
  obtain ⟨𝒢, hG, HG⟩ := gF P 1
  choose S hS HS using per
  refine ⟨hK.toFinset.biUnion fun κ => hG.toFinset.biUnion fun γ => S κ γ, ?_, ?_⟩
  · intro z hz
    obtain ⟨κ, -, hz⟩ := Finset.mem_biUnion.1 hz
    obtain ⟨γ, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS κ γ z hz
  intro X f' Ξ' hP hf hΞ' hz large₂ hs hRec Γ _ _ Pl0 T A Ks _ _ _ R F st hCf ho htw G₀
  subst hP
  obtain rfl := eq_of_heq hΞ'
  obtain ⟨κ, hκ, hk⟩ := H X T R.toLevCh A.μ0 rfl st.core.lev htw
  obtain ⟨γ, hγ, hg⟩ := HG X T R.toLevCh _ G₀ rfl rfl
  exact HS κ γ X f' rfl hf large₂ hs hRec Γ Pl0 T A Ks R F st hCf ho hk G₀ hg fun z hz' =>
    hz z (Finset.mem_biUnion.2 ⟨κ, hK.mem_toFinset.2 hκ, Finset.mem_biUnion.2 ⟨γ, hG.mem_toFinset.2 hγ, hz'⟩⟩)

end GlobalTheory.Mem.LiteralAutomorphy

end
end
