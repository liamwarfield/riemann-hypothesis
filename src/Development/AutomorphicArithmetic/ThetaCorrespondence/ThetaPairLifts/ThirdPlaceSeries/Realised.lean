module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal
public import Development.AutomorphicArithmetic.ResidueCharacters.ConclusionSplitOfHub

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
namespace GlobalTheory.BigTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC}
variable {ex : Extra D L hT Gi Gl Kc Y cX}
namespace PtAt
variable {Csz : ℝ}
set_option maxHeartbeats 1000000 in
def ofReal_alt (P : IndefiniteRowSideFullHecke ex) (Del h0 : ℕ) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs))
    (gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
      ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam)
    {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (B : _root_.Formalism.IndefR.RealTBAlt Rc P.toRowSideFamily Dcf Spf (P.zsc Del h0 Csz) S)
    (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) : PtAt ex Csz :=
  { P := P, Del := Del, h0 := h0, hDel := hDel, hh0 := hh0, Dcf := Dcf, Spf := Spf, gamDvd := gamDvd
    T := B.T, alg := B.alg, R := B.Q.Rl
    charW := B.Q.charW, zs := B.Q.zs, s0 := B.Q.s0, s1 := B.Q.s1, dc := B.Q.dc, stdChar := B.Q.stdChar, signs := B.Q.signs
    cG := B.Q.cG, Sx := B.Q.Sx, nexp := B.Q.nexp, stdV := B.Q.stdV, stdX := B.Q.stdX, host := B.Q.host, err_eq := B.Q.err_eq
    vpos := B.Q.vpos
    κ := B.κ, v₀ := B.v₀, fw := B.fw, bar := B.bar, O := B.O, pins := B.pins, rhoGeo := B.rhoGeo, equivAll := B.equivAll
    cTie := B.cTie, phase := B.phase
    qGuard := Qp.qGuard, hF := Qp.hF, phsOne := Qp.phsOne, prXunit := Qp.prXunit, grpRecPin := Qp.grpRecPin, fdiag := Qp.fdiag
    eGtie := Qp.eGtie, betaStd := Qp.betaStd
    tupT := Qr.tupT, hm := Qr.hm, Tp := Qr.Tp, tupXi := Qr.recR.tupXi, tupAt := Qr.recR.tupAt, tupTie := Qr.tupTie
    tupT_tup := Qr.tupT_tup, muEq := Qr.muEq }
variable (p : PtAt ex Csz)
def RealisedCondition : Prop :=
  ∃ (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc)
    (B : _root_.Formalism.IndefR.RealTBAlt Rc p.P.toRowSideFamily p.Dcf p.Spf (p.P.zsc p.Del p.h0 Csz) S) (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q),
    _root_.Formalism.IndefR.IndefiniteRealisationCompatible Qp Qr ∧ _root_.GlobalTheory.BigTop.PtAt.ofReal_alt p.P p.Del p.h0 p.hDel p.hh0 p.Dcf p.Spf p.gamDvd B Qp Qr = p
structure CompatibilityConditions : Prop where
  real : p.RealisedCondition
  core : GlobalTheory.BigOn.CoreTies L ex.errX p.T p.R.toRealDat
  pb : p.T.pb = p.R.C.P.pb
  types : GlobalTheory.DimPartsCompare.TameTie D p.R.C.W.om
  series : Nonempty (GlobalTheory.SeriesTie.ExportTie p.nexp p.v₀)
  level : p.LevelTie
  data : p.DataTie
  psiVal : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (p.Tp.psi w).ValuesIn 0 D.what₂.embLL
  ray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (Formalism.L2.Host.embLL0 D).fieldRange
  roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange
  rayQ : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel p.R.toRealDat t)
  twist : GlobalTheory.EX.DQ.TwAllAt D ex.nch ex.xd
structure PointConditions' : Prop where
  exAt : p.R.toRealDat.ExAt
  jEvBar : JEvBar p.T p.R.toRealDat p.κ
  geoAct : GeoAct p.T p.R.toRealDat p.κ p.v₀
  evInj : EvInj p.T p.R.toRealDat p.v₀
  ioExt : IoExt p.R.toRealDat
  oneMap : ∀ i, OneMapRowR p.T p.R.toRealDat p.κ p.v₀ p.O (phEff p.R) i
  prim : PrimRows3 p.R p.F
  sep : p.P.A3.fam3.TypesSep3
  ok : p.P.A3.fam3.Ok3 1
  framesOK : Formalism.IndefR.Mi.FramesOKg2 p.R
  divRows : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I
  psi : PsiPPTie D p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.I.eG
  d0 : D.what₂.D0 = (p.P.A3.A.fam.R p.P.A3.A.fam.μ0).dZ (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) (p.P.Zs.Z p.P.A3.A.fam.μ0)
  export_ : p.ExportRow
  goodFT : Formalism.BasicNotions.GoodFTAll D
  w1 : ∀ w, (p.R.toCx3 p.F).W1 p.F.cr (p.N 0 0) w → w ∈ p.R.twPl
  ties : p.CompatibilityConditions
section OfReal
variable {P : IndefiniteRowSideFullHecke ex} {Del h0 : ℕ} {hDel : D.s.Del = (Del : ℚ)} {hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
  {gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
    ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {B : _root_.Formalism.IndefR.RealTBAlt Rc P.toRowSideFamily Dcf Spf (P.zsc Del h0 Csz) S}
  {Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q} {Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q}
end OfReal
namespace Realised
variable {p} (h : p.RealisedCondition)
include h
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.induction {Q : PtAt ex Csz → Prop}
    (hQ : ∀ (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc)
      (B : _root_.Formalism.IndefR.RealTBAlt Rc p.P.toRowSideFamily p.Dcf p.Spf (p.P.zsc p.Del p.h0 Csz) S) (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q),
      _root_.Formalism.IndefR.IndefiniteRealisationCompatible Qp Qr → Q (_root_.GlobalTheory.BigTop.PtAt.ofReal_alt p.P p.Del p.h0 p.hDel p.hh0 p.Dcf p.Spf p.gamDvd B Qp Qr)) : Q p :=
  let ⟨Rc, S, B, Qp, Qr, a, e⟩ := h
  Eq.subst (motive := Q) e (hQ Rc S B Qp Qr a)
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.exists_frame : ∃ Rc : _root_.Formalism.L2.RecTAlt ex, p.R.C = Rc.T.n.cf ∧ HEq p.Tp Rc.T.n.tp ∧ p.R.ψ = Rc.T.theta.W.ψ :=
  h.induction (Q := fun p => ∃ Rc : _root_.Formalism.L2.RecTAlt ex, p.R.C = Rc.T.n.cf ∧ HEq p.Tp Rc.T.n.tp ∧ p.R.ψ = Rc.T.theta.W.ψ)
    fun Rc _ B Qp Qr _ => ⟨Rc, Qp.cfEq, Qr.tpEq, B.Q.psiPin⟩
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.valLL0 : Formalism.L2.Host.ValLL0 D p.R.C := by
  obtain ⟨Rc, e, -⟩ := h.exists_frame
  exact e ▸ Rc.T.chrVal
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.psiChoice : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp := by
  obtain ⟨Rc, e, e', -⟩ := h.exists_frame
  have := Rc.T.chrPsi
  revert e'
  generalize p.Tp = t
  generalize p.R.C = c at e t ⊢
  subst e
  intro e'
  exact eq_of_heq e' ▸ this
end Realised
theorem CompatibilityConditions.eSer {p : PtAt ex Csz} (h : p.CompatibilityConditions) : GlobalTheory.GLq.ESerTie D := h.types.eSerTie
end PtAt
def EventuallyAtPoints {eps : ℝ} (Fm : FamP eps) (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → Q x hx i p
theorem EventuallyAtPoints.of_forall {eps : ℝ} {Fm : FamP eps} {Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : ∀ x hx i p, p.PointConditions' → Q x hx i p) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q := ⟨0, fun x hx _ => h x hx⟩
theorem EventuallyAtPoints.and {eps : ℝ} {Fm : FamP eps} {Q Q' : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q) (h' : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q') : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => Q x hx i p ∧ Q' x hx i p :=
  let ⟨a, h⟩ := h
  let ⟨b, h'⟩ := h'
  ⟨max a b, fun x hx hle i p hp => ⟨h x hx ((le_max_left _ _).trans hle) i p hp, h' x hx ((le_max_right _ _).trans hle) i p hp⟩⟩
def LambdaLowerBound₂ : Prop := Closed FamHyp fun Fm CH => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ C, (p.S true).L6 (p.N C CH)
end GlobalTheory.BigTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {D : D7}
section Package
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word) (g : Geo D)
variable {R P u g}
end Package
section Read
variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)
end Read
section Real
open GlobalTheory.MiS
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
abbrev pk_z := W.Q.Rl.toRealDat
abbrev complexLevelStructure : LevelP (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ℂ := (_root_.GlobalTheory.Fam.pk_z W).levR W.Q.F.lv2 true
def LevelCondition (u : D.what₂.Word) (μ : D.what₂.Tup) (x : GA D D.sp.X') (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (μ = D.what₂.mu0 → LevG (W.R.T.cols.forms u).clsP.toG x J χ) ∧ ∀ h : μ ≠ D.what₂.mu0, LevG (W.R.T.tw.pt.cls u μ h) x J χ
def ReadsCoefficients (u : D.what₂.Word) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (μ : D.what₂.Tup) (G : D.what₂.Amb μ)
    (f : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : Prop :=
  (∀ h : μ = D.what₂.mu0, ReadsG (W.R.T.cols.forms u).clsP.toG (W.R.T.cols.forms u).valP.eW j x
    ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) G h)) f) ∧
  ∀ h : μ ≠ D.what₂.mu0, ReadsG (W.R.T.tw.pt.cls u μ h) (W.R.T.tw.pt.val u μ h).eW j x ((D.eMtTw u μ).symm G) f
def leadingLinearMap (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ) :=
  (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)))
def LeadingReadAt (u : D.what₂.Word) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') : Prop :=
  GlobalTheory.Core.Rk.Top.IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j ∧ x ∈ GfC D.sp.X' ∧ ∀ t : W.P.T,
    _root_.GlobalTheory.Fam.LevelCondition W u (W.P.I.tup t) x (levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) ∧
    ∀ (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL) (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL),
      HEq F F' → _root_.GlobalTheory.Fam.ReadsCoefficients W u j x (W.P.I.tup t) (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F)) (_root_.GlobalTheory.Fam.leadingLinearMap W t F')
def LeadingReadStatement : Prop := ∃ x, ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt W u j x
def tailCoefficient (u : D.what₂.Word) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (μ : D.what₂.Tup)
    (ψ : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ) (f : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : ℂ :=
  if h : ∃ G, _root_.GlobalTheory.Fam.ReadsCoefficients W u j x μ G f then
    if h0 : μ = D.what₂.mu0 then
      (D.mem u).P.Ptil (Eq.rec (motive := fun C _ => C.cls D.R.m → C.Y D.R.m → ℂ)
        (Eq.rec (motive := fun ν _ => (D.chTw u ν).cls D.R.m → (D.chTw u ν).Y D.R.m → ℂ) ψ h0) (D.memberColumns_twistedChain_base u))
        ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) h.choose h0))
    else (D.PTw u μ).Ptil ψ ((D.eMtTw u μ).symm h.choose)
  else 0
structure FamilyCharacter (u : D.what₂.Word) where
  g : Geo D
  j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)
  row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g t
  col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))
variable {W} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
abbrev FamilyCharacter.c : Comm D := commOf (_root_.GlobalTheory.Fam.pk_z W) u f.g
abbrev FamilyCharacter.t (t : W.P.T) : Tup f.c :=
  tupOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u f.g t (f.row t) (f.col t) fun ψ F => _root_.GlobalTheory.Fam.tailCoefficient W u f.j f.g.bT (W.P.I.tup t) ψ F.1
end Real
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MiTop
section Alg
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}
end Alg
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
abbrev rJ_z : Set (GA D (D.sp.Y 0)) :=
  levS (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))
abbrev realCharacter : GA D (D.sp.Y 0) → ℂ :=
  Formalism.IndefR.Lev.levChi (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))
abbrev BaseRowSpace : Submodule ℂ (SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) := MultT W.Q.Rl.θ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)
def rowFormOfVector (e : W.Q.Rl.HE.H) : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) := PiTensorProduct.lift (W.Q.Rl.HE.e e)
def rowFormOfTuple (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  _root_.GlobalTheory.MiTop.rowFormOfVector W (W.Q.Rl.Th t (W.Q.Rl.jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)))
abbrev formsAtZero (u : D.what₂.Word) : Formalism.L2.Forms.Forms0 D u := (W.R.T.cols.forms u).to0
structure BottomData (u : D.what₂.Word) where
  B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)
  b : GA D (D.sp.Y 0)
  a₀ : GA D (D.sp.X 0)
  a : GA D (D.sp.X 0)
  k : GA D (D.sp.Y 0)
variable {W}
structure BottomData.Pin {u : D.what₂.Word} (d : _root_.GlobalTheory.MiTop.BottomData W u) (z : GA D (D.sp.Y 0)) : Prop where
  adapted : d.B.Adapted (W.S.tr u).wt
  h0 : IsTransportAdelicCorrection (W.S.tr u) d.a₀
  fin : d.a ∈ GfC (D.sp.X 0)
  cen : d.a ∈ Subgroup.center (GA D (D.sp.X 0))
  lev : d.k ∈ _root_.GlobalTheory.MiTop.rJ_z W
  eq : embA d.B.d d.B.o (d.a₀ * d.a) * d.b =
    (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * d.k)
def BottomData.per {u : D.what₂.Word} (d : _root_.GlobalTheory.MiTop.BottomData W u) (φ : D.what₂.Mu u)
    (T : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) (y : (D.mem u).C.Y 0) (v : SmT (W.Q.Rl.MY 0)) : ℂ :=
  d.B.lev.per W.Q.Rl.ψ ((chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) (rTrans d.b (T v))
def BottomData.Rel {u : D.what₂.Word} (d : _root_.GlobalTheory.MiTop.BottomData W u) (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (c : W.P.T → ℂ) : Prop :=
  ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∃ p : D.what₂.Mu u → ℂ, ∀ (φ₀ φ : D.what₂.Mu u) (t : W.P.T)
    (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
    (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ α α' : ℂ,
    α * p φ₀ + α' * (c t * D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))) = 0 →
      ∀ y v, α * d.per (U φ₀) T y v + α' * d.per (U φ) (_root_.GlobalTheory.MiTop.rowFormOfTuple W t F') y v = 0
variable (W)
def UnitCoefficients (c : W.P.T → ℂ) : Prop :=
  (∀ t, c t ≠ 0) ∧ ∀ w (k : D.what₂.LL), D.what₂.embLL k = c (W.Q.Rl.mu w) / c W.P.A3.A.μ0 → vw w k = 0
def JointCondition : Prop :=
  ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u, ∃ (d : _root_.GlobalTheory.MiTop.BottomData W u) (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ)
    (c : W.P.T → ℂ), d.Pin z ∧ 0 < r ∧ (∀ φ, ‖U φ‖ = r * ‖φ‖) ∧ _root_.GlobalTheory.MiTop.UnitCoefficients W c ∧ d.Rel U c
def IsPairing' (u : D.what₂.Word) (t : GA D (D.sp.Y 0)) (f : GA D (D.sp.Y 0) → ℂ) (T : Cu W.S.X u W.S.Y.hK) (b : ℂ) : Prop :=
  ∃ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq t f ∧
    b = ⟪star φ, PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) T⟫_ℂ
structure BottomHypotheses : Prop where
  hyp : _root_.GlobalTheory.MiS.HypothesisAtPackage W
  pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation W.Q
  see : _root_.Formalism.IndefR.IndefiniteRealisationExtends W.Q
  used : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t)
  idE : GlobalTheory.Core.Mi.IdE W.S.X
  gap : GlobalTheory.Count.GapGe W.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  fin : Formalism.L2.SG.PackageTie2.FinX W.S.Y
def columnOfCoordinates (u : D.what₂.Word) (x : Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) : D.what₂.Mu u :=
  ∑ i, x i • D.jN u (W.P.I.eNu u (Pi.single i 1))
def ColumnCoordinateCondition : Prop :=
  ∀ u, Function.Bijective (_root_.GlobalTheory.MiTop.columnOfCoordinates W u) ∧ (∀ x, _root_.GlobalTheory.MiTop.columnOfCoordinates W u (cpt D.what₂.embLL x) = D.jN u (W.P.I.eNu u x)) ∧
    ∃ r : ℝ, 0 < r ∧ ∀ x, fnorm (W.P.Dc.Xc (W.P.I.wU u) W.P.A3.fam3.base3.v0)
      (Formalism.L2.SG.JoinSI.cjv (Formalism.L2.SG.JoinSI.twQ W.P) x) = r * ‖_root_.GlobalTheory.MiTop.columnOfCoordinates W u x‖
def IsColumnForm (u : D.what₂.Word) (T : Cu W.S.X u W.S.Y.hK) (φ : D.what₂.Mu u) : Prop :=
  Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK T = (D.eMu u φ).1
def PairingFormCondition (v : (W.Q.Rl.MY 0).Vec) : Prop :=
  ∃ κ : ℂ, κ ≠ 0 ∧ ∀ e ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EEl true, ∀ (u : D.what₂.Word) (m : (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Mem), HEq m (W.P.I.wU u) →
    ∀ (x : Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) (x' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.a m) → ℂ), HEq x x' →
    ∀ T b, _root_.GlobalTheory.MiTop.IsColumnForm W u T (_root_.GlobalTheory.MiTop.columnOfCoordinates W u x) →
      _root_.GlobalTheory.MiTop.IsPairing' W u (show GA D (D.sp.Y 0) from W.Q.tS) (_root_.GlobalTheory.MiTop.rowFormOfVector W (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) e) (PiTensorProduct.tprod ℂ v)) T b →
      ⟪W.Q.sEE e, (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Sp.Pu m (Formalism.L2.SG.JoinSI.cjv (Formalism.L2.SG.JoinSI.twQ W.P) x')⟫_ℂ =
        cj (Formalism.L2.SG.JoinSI.twQ W.P) (κ * b)
def IsShiftOperator (z : GA D (D.sp.Y 0)) (V : W.Q.Rl.HE.H →ₗ[ℂ] W.Q.Rl.HE.H) : Prop :=
  (∀ e v, _root_.GlobalTheory.MiTop.rowFormOfVector W (V e) v = rTrans (show GA D (Yc D 0) from z) (_root_.GlobalTheory.MiTop.rowFormOfVector W e v)) ∧ (∀ e, ‖V e‖ = ‖e‖) ∧
    ∀ e, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) →
      W.Q.Rl.HE.e (V e) ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)
def BottomRelation (z : GA D (D.sp.Y 0)) {u : D.what₂.Word} (d : _root_.GlobalTheory.MiTop.BottomData W u) : Prop :=
  ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ (φ φ' : D.what₂.Mu u), ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ T' ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ α α' : ℂ,
    (∀ y v, α * d.per φ T y v + α' * d.per φ' T' y v = 0) →
    ∀ (v : SmT (W.Q.Rl.MY 0)) C C' b b', _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → _root_.GlobalTheory.MiTop.IsColumnForm W u C' (R φ') →
      _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T v) C b →
      _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T' v) C' b' → α * b + α' * b' = 0
end GlobalTheory.MiTop
namespace GlobalTheory.MiTop
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure PointSummands (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : _root_.Formalism.L2.RecTAlt O.ex
  S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R
  P : RowSideFamily O.ex
  pin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  ok1 : P.A3.fam3.Ok3 1
  B : _root_.Formalism.IndefR.RealTBAlt R P Dcf Spf (GlobalTheory.Fc.zsc P DH.1.1 DH.1.2 c) S
  Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q
  psi : PsiPPTie D P.P0 P.ψ0 P.Ps P.ψs P.I.eG
  pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q
  muDef : ∀ C CH : ℝ, (B.Q.Rl.toCx3 B.Q.F).MuDef B.Q.F.cr (B.Q.Rl.num B.Q.F C CH) B.Q.Rl.mu
  recPins : _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr
def FiringPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b =>
  b.B.Q.Rl.toRealDat.ExAt ∧ JEvBar b.B.T b.B.Q.Rl.toRealDat b.B.κ ∧ GeoAct b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ ∧
    EvInj b.B.T b.B.Q.Rl.toRealDat b.B.v₀
def summandRealBound : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows b.B
def ThresholdPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b =>
  RecTie.ThetaFireRow (RecTie.toLiftReal b.B.Q.Rl.toRealDat b.B.Q.F.lv2 b.Rr.tupT b.Rr.hm b.Rr.hTop b.Rr.hinj) b.Rr.IL
def FramePointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx b.B.Q
def VisibleExamplePointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => _root_.Formalism.IndefR.IndefiniteRealisationExtends b.B.Q
def summandPrimitive : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3
def DivisorPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun D O _ b =>
  DivRows3 D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.Zs b.P.S0 b.P.S1 O.ex.p0 b.P.C b.P.NuC b.P.I
def summandDegreeZero : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun D _ _ b =>
  D.what₂.D0 = (b.P.A3.A.fam.R b.P.A3.A.fam.μ0).dZ (b.P.A3.A.fam.lvl b.P.P0 b.P.ψ0) (b.P.Zs.Z b.P.A3.A.fam.μ0)
def NormJumpPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ O _ b => _root_.Formalism.IndefR.NX.RealExpansionMajorant b.B.Q b.B.Q.cG b.B.Q.Sx b.B.Q.nexp O.ex.nch
def IotaPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ∀ x : b.S.X.B.I.E, HEq (b.S.X.ιE x) x
def summandL3Bound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH)
def summandNormBound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).ON (b.B.Q.Rl.num b.B.Q.F C CH)
def summandL6Bound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr true).L6 (b.B.Q.Rl.num b.B.Q.F C CH)
def summandFunctionalBound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH)
def SmallPointSummands (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b =>
  (∀ w, (b.B.Q.Rl.toCx3 b.B.Q.F).W1 b.B.Q.F.cr (b.B.Q.Rl.num b.B.Q.F C CH) w → w ∈ b.B.Q.Rl.twPl) ∧
    (b.B.Q.Rl.toCx3 b.B.Q.F).SEEIso b.B.Q.sEE ∧ PassIn3 b.B.Q.Rl b.B.Q.F C CH
end GlobalTheory.Fc.Ind
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpinAtMem
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpinAtMem
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.OPinAt
theorem mtInput_at_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) : ∃ tup Q, MtInput D a.all.gal.mt tup Q := by
  have key : ∀ (D' : D7), D' = withLoc a.nt.L → ∀ M' : MtFam D', HEq (mtL a.nt.L a.nt.M) M' →
      ∃ tup Q, MtInput D' M' tup Q := by
    rintro _ rfl M' hM
    obtain rfl := eq_of_heq hM
    exact ⟨_, _, mtInput_mtL a.nt.L a.nt.M _ _ a.nt.mt⟩
  exact key D a.nt.eq _ a.mt_eq
theorem labTie_nt_of_labTie {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp)
    (h : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) :
    GlobalTheory.SerSys.LabTie a.nt.D fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩ := by
  have key : ∀ (D' : D7), D' = withLoc a.nt.L →
      (GlobalTheory.SerSys.LabTie D' fun k => @GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩) →
      GlobalTheory.SerSys.LabTie a.nt.D fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩ := by
    rintro _ rfl h'
    exact fun k => ⟨(h' k).1, (h' k).2⟩
  exact key D a.nt.eq h
end GlobalTheory.HeightCounting.Up.OPinAt
open GlobalTheory.HeightCounting.Up.OPinAt in
theorem GlobalTheory.HeightCounting.Up.oPin_at_mem : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => _root_.GlobalTheory.CoefDuty.OPinAlt c.a := by
  intro hL
  refine EvG.imp GlobalTheory.T.twistedPlace_innerProduct_classSum_rows fun K _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c hne _ hcp => ?_
  obtain ⟨m⟩ := hne
  have hs := H kp w hcp Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt
  obtain ⟨tup, Q, hin⟩ := _root_.GlobalTheory.HeightCounting.Up.OPinAt.mtInput_at_alt c.a
  have hsum := hs c.a.all.gal.mt tup Q m.ad hin
  have hlab : GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
    fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩
  exact
    { large := m.large
      inner := classSum_loc_of_sumTw hsum
      lab := _root_.GlobalTheory.HeightCounting.Up.OPinAt.labTie_nt_of_labTie c.a hlab
      gen := fun k => m.zeta k }
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpinAtMemStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_duty_pin_at_each_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => _root_.GlobalTheory.CoefDuty.OPinAlt c.a := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.oPin_at_mem | exact _root_.GlobalTheory.HeightCounting.Up.oPin_at_mem | (intros; apply _root_.GlobalTheory.HeightCounting.Up.oPin_at_mem <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UsedAll
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mi
namespace GlobalTheory.MiS.Check
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem used_all_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) : Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t) := by
  rcases W.Q.charW.tup.mu_used t with h | ⟨w, h⟩
  · rw [h]; exact used_base W.P
  · right
    have e : W.Q.Rl.mu = W.P.S0.μ := mu_eq_of_heq W.P W.Q.zs _ W.Q.s0
    refine ⟨D.plEq.symm w, ?_⟩
    rw [W.P.tied.div.tup.muAt, Equiv.apply_symm_apply, ← h, e]
    rfl
end GlobalTheory.MiS.Check
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPins3RealTOf
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.Mem.R3
set_option maxHeartbeats 4000000 in
theorem realPins3_realTOf_alt : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt a.x Rc S), HEq (a.Zsc (zsOf t.r.z.R t.r.z.F)).F0 (F0K K.s (w.D Z)) → _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput y) := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a Rc S y h
  rw [_root_.Formalism.IndefR.Pins3.realPins3_iff_twPl_iff_W1]
  have hr := t.r.z.twisted_places_eq_complex_side_of_eq_nonzero_index (F0K K.s (w.D Z)) t.exact.symm t.r.z.R.kap a.lam a.err a.Dc a.Sp a.Zsc 0 0 (eq_of_heq h)
  show ∀ v, v ∈ a.x.R.twPl ↔ (a.x.R.toCx3 a.x.F).W1 a.x.F.cr (a.x.R.num a.x.F 0 0) v
  clear y h
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  dsimp only at hr ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact hr
end GlobalTheory.Mem.R3
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPinsRealTOf
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3
set_option maxHeartbeats 4000000 in
theorem realPins_realTOf_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), x.R.C = Rc.T.n.cf → (∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i)) → (open Classical in x.R.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE)) → y.tS ∈ Formalism.L2.Theta.GfC (Yc D 0) → Formalism.IndefR.AutomorphicEvaluation.ConjLevel y.tS⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (y.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (y.ιS k)) → Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt x.R.toRealDat x.F.lv2 S.X y.instEq y.tS → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) := by
  intro D L hT Gi Gl K Yd cX ex x Rc S y hC hD hPg hfin hLev hRow
  exact
    { cfEq := hC
      qGuard := x.pins.keep.guard
      hF := x.Y.hF
      phsOne := x.pins.phs
      prXunit := x.pins.keep.prX
      grpRecPin := x.pins.keep.grp
      fdiag := hD
      pgEq := hPg
      tSfin := hfin
      tSpin := fun _ => ⟨hLev, hRow⟩
      eGtie := rfl
      betaStd := x.pins.keep.beta
      bR_read := fun _ _ => rfl }
end GlobalTheory.Mem.R3
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
namespace GlobalTheory.AdmIface
theorem main_alt_alt : ∀ D : D7, (Formalism.MainNotions.SumRepresentations.adm1 D → ∀ i, BCEx D.nd D.naut i) ∧ (Formalism.MainNotions.SumRepresentations.adm5 D → ChebSplit D.nd ∧ GlobalTheory.RowCopy.IsobaricCuspidalStrongMultiplicityOne D.nd D.naut ∧ GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut) ∧ (Formalism.MainNotions.SumRepresentations.Conclusion42 D → ∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i) ∧ (_root_.Formalism.MainNotions.SumRepresentations.adm7_alt D ↔ _root_.UpperTheory.GalN.TempCSDo D) ∧ (Formalism.MainNotions.SumRepresentations.adm3 D ↔ ∀ i, GlobalTheory.ThetaExh.SplitLift D.nd D.naut i) ∧ (Formalism.MainNotions.SumRepresentations.adm8 D ↔ Rows.IsotInternal D.what₂) := by
  intro D
  refine ⟨?_, ?_, ?_, Iff.rfl, ?_, Iff.rfl⟩
  · intro h i
    exact h i
  · rintro ⟨h1, h2, h3, -⟩
    refine ⟨?_, h1, h2⟩
    intro S
    rw [dense_iff_closure_eq]
    have := h3 (S : Set (PlE D.host)) S.finite_toSet
    simpa only [Finset.mem_coe] using this
  · intro h i σ P hP
    have hne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
      intro h0
      apply hP.1
      rw [h0, Submodule.map_bot]
    obtain ⟨-, ⟨Sig, hS, hB⟩, -⟩ := h i σ hne
    exact ⟨Sig, hS, hB P hP⟩
  · constructor
    · intro h i σ P hP w hw
      exact h i σ P hP w hw
    · intro h i σ P hP w hw
      exact h i σ P hP w hw
end GlobalTheory.AdmIface
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeExJoinPin
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
namespace GlobalTheory.Mem.JPin
set_option maxHeartbeats 4000000 in
theorem seeEx_joinPin_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc (S.toRealSpectralMatching Rc)) (c : ℝ), Holds x.R x.F → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → _root_.Formalism.IndefR.IndefiniteRealisationExtends (_root_.GlobalTheory.Mem.R3.realisationOfInput y) ∧ _root_.GlobalTheory.Mem.JTop.JoinPinAlt (_root_.GlobalTheory.Mem.R3.realisationOfInput y) := by
  intro D L hT Gi Gl K Yd cX ex x Rc P S y c _ hS hE hR
  have hι : y.ιS = (iotaX P.X P.inst).toMulEquiv :=
    (GlobalTheory.Mem.JIota.heq_iota_iff D P.X P.inst y.ιS).1 y.ιS_eq
  have hinj : Function.Injective x.R.HE.e := x.pins.char.base.models.HE.1
  have hread : ∀ y1, x.Y.eE (D.jEE (x.Z.eRR y1)) = Tw.out (s := twAt D.what₂.embLL x.A3.A.v0) (E := x.R.HE.H)
      ((x.R.toCx3 x.F).iC x.F.cr true x.A3.A.μ0 (cpt x.A3.A.v0.embedding y1)) := by
    intro y1
    have h1 := x.Y.eE_read (D.jEE (x.Z.eRR y1))
    rw [x.Z.jEE y1] at h1
    exact hinj ((PiTensorProduct.lift : Mult.MMap (x.R.MY 0) ≃ₗ[ℂ] _).injective h1).symm
  refine ⟨⟨⟨y.tS, hS.fin, ?_, ?_⟩, c, ?_⟩, x.Y.eE, ?_, ?_⟩
  · show ConjLevel y.tS⁻¹ (JR x.R.toRealDat x.F.lv2) (chiR x.R.toRealDat x.F.lv2) (y.ιS ⁻¹' concreteLevelAdelicSubset P.X)
      (fun k => adelicCharacterOfHidaSetting P.X (y.ιS k))
    rw [hι]
    exact hS.conj
  · exact hS.mat
  · show EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G y.ιS y.tS c
    rw [hι]
    exact hE
  · intro y1 y' h
    obtain rfl := eq_of_heq h
    exact hread y1
  · intro hF
    have hj : _root_.Formalism.L2.SG.JoinSI.spectralRowIsometry (S.toRealSpectralMatching Rc) hF = S.j :=
      _root_.Formalism.L2.SG.JoinSI.isometryOfJoin_eq_of_conj_compat (S.toRealSpectralMatching Rc) hF S.j fun F => S.rowPin F
    rw [hj]
    exact hR
end GlobalTheory.Mem.JPin
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionSplitOfHub
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem conclusion_split_alt (Pr : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂)
    (i : D.nd.Loc) (hg : D.nd.l i ∉ TwistedPlaces.gset D) (N : ℕ) (hC : CycAt N i) (hL : EmbeddingTypes.hypL i)
    (hdecl : ∀ ep, (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.ambTypeD (D := D) i ep)
    (hK : LiftK (D.loc (D.nd.l i)) ∧ InvariantsKilledOverCyclotomic (D.loc (D.nd.l i)) ∧ TBK (D.loc (D.nd.l i))) :
    ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.RowsAreConj i dc ∧ ∀ π ∈ D.nd.Zgood i,
      EmbeddingTypes.ShaBoundTheoremB i (X.ρ i) π dc (eL (D.nd.l i) N (Formalism.MainNotions.N.hN L))
        (fun _ => c0L (D.nd.l i) N (GlobalTheory.HubX.hOf L) (4 * D.R.n * D.R.nV))
        (cBL (D.nd.l i) N ⌊2 * L.sc.b⌋₊ (4 * D.R.n * D.R.nV) D.R.t) ∧
      (∀ u ∈ dc.col, (Br.h0W i u (X.ρ i) π : ℝ) ≤
        (D.R.r : ℝ) * (c0L (D.nd.l i) N (GlobalTheory.HubX.hOf L) (4 * D.R.n * D.R.nV) : ℕ)) ∧
      ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1 := by
  have fa := S.facts
  have hAJ : _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L := fa.admJ L S.par
  have hJ : AdmissibleParameterJ.JumpConditions L := _root_.GlobalTheory.JumpStatement.holds_all_alt D L hAJ
  have hJ' := hJ
  obtain ⟨⟨ep, hep⟩, hJb, hJc, -, hJe, hJf, -⟩ := hJ'
  have hfam := S.canon.fam
  have hg0 : D.nd.l i ≠ D.host.g 0 := hL.2.2.2.1
  have hg1 : D.nd.l i ≠ D.host.g 1 := hL.2.2.2.2
  obtain ⟨⟨dc, hdc⟩, hType⟩ := hdecl ep
  refine ⟨dc, hdc.2, fun π hπ => ?_⟩
  have hZ : π ∈ D.nd.Z i := LargeLevelLemmas.zgoodSubsetZ i hπ
  have sp := _root_.GlobalTheory.T.set_pt_of_setup_not_twisted Pr D L P nch HW F Cm X C₂ S i hg π hπ
  have hρ := hfam.cont i π
  obtain ⟨sub, acont, a56⟩ := amb_of_setPt i X π dc sp hρ
  obtain ⟨g1, g2, g3, g4, _, g5x, g6, bk, cont, ss, dec, eps, tie, shape, font, hH2, cft⟩ := sp
  have hG2 := _root_.GlobalTheory.T.admG2_of_setup_jumps Pr D L P nch HW F Cm X C₂ S ep hep i
  have hG5 := _root_.GlobalTheory.T.admG5_of_setup Pr D L P nch HW F Cm X C₂ S i hg π hπ
  have hcr := _root_.GlobalTheory.T.decomposition_fontaine_at_places_over_l D i (X.r i) (X.ρ i) π fa.Conclusion1.1 font (hfam.good i) hρ dec hg0 hg1
  have hjp := GlobalTheory.T.decomposition_local_above D L ep hep hJb hJc hJe hJf i (X.r i) (X.ρ i) π (hfam.good i) hZ dec
  have hW : JumpsNoZero i (WpO D.nd i (X.ρ i) π) (GlobalTheory.HubX.hOf L) :=
    fun w hw C => ⟨(hcr w hw C).2.2.1, fun τ => hjp w hw C τ _ (Or.inl rfl)⟩
  have hT2 : JumpsNoZero i (T2O D.nd i (X.ρ i) π) (GlobalTheory.HubX.hOf L) :=
    fun w hw C => ⟨(hcr w hw C).2.2.2, fun τ => hjp w hw C τ _ (Or.inr rfl)⟩
  obtain ⟨lc, lr⟩ := lift_exponent_admissible_cols_rows_of_crystalline L i N hK.1 hC X dc hfam.good ep hep hJe font
    (fun w hw C x => (hG2 hg0 hg1 w hw C).2.1 x) (fun w hw C x => (hcr w hw C).2.1 x)
  have hH0 := invariants_length_admissible_of_nonzero_jumps i N hK.2.1 hC (X.ρ i) π dc _ hρ hT2
  obtain ⟨ht, hWin⟩ := GlobalTheory.T.hodgeTateJumpWindow_of_jumpSets D L hJ S.par67
  have tb9 := block_condition_at_places_of_jump_window i N hK.2.2 hC (X.r i) π _ ht (hWin i (X.r i) (hfam.good i) π)
  have tb : EmbeddingTypes.admTB i (X.r i) π dc _ := fun w hw _ C hC' => tb9 w hw C hC'
  obtain ⟨l51, l52, _⟩ := GlobalTheory.charpoly_span_and_hom_relations_of_admissible D i (X.r i) (X.ρ i) π g1
  have h78 := _root_.GlobalTheory.T.ambT2_of_deRham_family Pr.font D L (withDc X i dc) fa.g2.1 hJ.1 hJc hfam i hg π hπ
  rw [withDc_dc] at h78
  have hcB : ∀ k, GlobalTheory.HubLoc.cBnum (D.nd.l k) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ (withDc X i dc).cB k := by
    intro k
    show _ ≤ X.cB k
    rw [S.canon.cB]; exact le_rfl
  have hCl := _root_.GlobalTheory.closingFamilyX_alt_alt Pr.font Pr.fin D HW F L (withDc X i dc)
    (fun L' h => _root_.GlobalTheory.JumpStatement.holds_all_alt D L' h) hAJ S.par67 fa.Conclusion1.1 fa.large.2.1 hfam hcB
  have dual := hCl.2.2.1 i hg π hπ
  have h1f := hCl.2.2.2 i π
  rw [withDc_dc] at dual h1f
  have a51 := GlobalTheory.T.admissibleAtGoodPoints_of_coefRing_taken_at_live GlobalTheory.Published.cheb_holds D X fa.large.2.2 (GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred D fa.rhoBar) hfam i π hπ
  have bka : LargeLevelLemmas.BlochKatoAnnihilators i := GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar Pr.bk Pr.tate Pr.euler D i
  have fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i := GlobalTheory.T.tateFinitenessAll_of_localTateDuality Pr.tate D i
  have hA : EmbeddingTypes.admitted i (X.r i) (X.ρ i) π dc ep _ _ _ :=
    ⟨g1, hG2, g3, g4, hG5, g5x, g6, a56, a51, l51, l52, ⟨bk, bka⟩, lc, lr, hH0, tb, GlobalTheory.T.unramifiedTrivialH1f_of_decl D i dc, cont, ss, dec, eps,
      tie, shape, font, hH2, fin, cft, h78.2.2.2, dual, h78.1, h78.2.1, h78.2.2.1, h1f, sub, acont, hType⟩
  obtain ⟨-, -, hB⟩ := GlobalTheory.T.splitCase_bound_at_point_of_admitted_items_alt Pr.artin Pr.tate Pr.euler D i (X.r i) (X.ρ i) π dc ep _ _ _ hA (fun _ _ _ => g2) hL hdc hZ
  exact ⟨hB, fun u hu => length_invariants_Wprime_divisible_le_of_nonzero_jumps i N hK.2.1 hC (X.ρ i) π _ (GlobalTheory.NLink.AmbSub.WpO_cont i (X.ρ i) π hρ) hW u
    ((dc.cover u).1 (Or.inr hu)), fun v hv => (g5x v (Or.inr hv)).2.2.1 hv⟩
end UpperTheory.N
end
end
end
