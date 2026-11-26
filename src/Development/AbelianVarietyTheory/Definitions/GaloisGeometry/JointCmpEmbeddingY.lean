module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemberChainFormsLevelPrimeEqMember
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypChi
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FinIdx
public import Formalism.LocalToGlobal.GroupLattices.Joint0

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
noncomputable section

namespace GlobalTheory.TwV

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.SecondKernelSeries
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)
open GlobalTheory.TwU (StepCharts ChainCharts AdData AdPins AdTie AdLawAt AdDatum latCo ratA ssRec)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def castSt {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : StepCharts C i hi) : StepCharts C' i hi := h ▸ S

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in
structure Joint (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv}
    (H : CmpJHyp ex.cmp I) (X : LabIn I) where
  Gd : GroupCompatibilityAll D hT ex.cmp
  St : ChainCharts D u μ
  A : AdData t u μ St
  dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt
  a : 𝓞 D.host.E
  pins : AdPins A dtU
  tie : AdTie A dtU a
  st : ∀ j (hj : j + 1 ≤ D.R.m), St (j + 1) hj = castSt (X.onCh j hj) (StepCharts.ofStepIn (I.at' j hj).st)
  e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0
  jointCmpEmbeddingY : (D.mem u).C.Y 0 ≃ (D.chTw u μ).Y 0
  e0Tw : ∀ φ c y, D.e0Tw u μ φ (e0 c) (jointCmpEmbeddingY y) = φ c y
  one : OneHyp ((Gd.forms u).cls0).toChart.lev (lev0At Gd u w hg).A ((Gd.forms u).cls0).toChart.y
  cls0 : ∀ c (La : (D.gat u w hg).P.Tup), (D.gat u w hg).P.IsLatTup La → X.c0.cls c La = e0 (levelZeroClass one c La)
  lev0 : ∀ β : (St 0 (Nat.zero_le _)).Ch, ((St 0 _).K β).lev.Lb = (Gd.forms u).cls0.lev.Lb ∧
    ((St 0 _).K β).lev.Uloc = (Gd.forms u).cls0.lev.Uloc ∧ ((St 0 _).K β).lev.U = (Gd.forms u).cls0.lev.U ∧
    ∀ (κ : ((St 0 _).K β).lev.U) (κ' : (Gd.forms u).cls0.lev.U), κ.1 = κ'.1 → ((St 0 _).K β).lev.chi κ = (Gd.forms u).cls0.lev.chi κ'
  ch0 : Subsingleton (St 0 (Nat.zero_le _)).Ch
  y0 : ∀ c, ∃ κ : (Gd.forms u).cls0.lev.U, ((St 0 (Nat.zero_le _)).y (e0 c)).1 = ((Gd.forms u).cls0.y c).1 * κ.1 ∧ (Gd.forms u).cls0.lev.chi κ = 1 ∧
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ q ∈ Dx.Qp μ, ((q : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) → bc (prV (E := D.host.E) v) κ.1 = 1
  fr0 : ∀ y, (St 0 (Nat.zero_le _)).eY (jointCmpEmbeddingY y) = (Gd.forms u).val0.eY y
  iw : ∀ j hj β v, ((I.at' j hj).st.loc β).iw v = (lev0At Gd u w hg).A.iw v
  oneB : ∀ j hj β β', ((I.at' j hj).st.loc β).B = ((I.at' j hj).st.loc β').B
  pos : ∀ j hj, (I.at' j hj).st.pos = hT.gat_pos u w hg
  tw : ∀ j hj β (x : UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm),
    Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 → ((I.at' j hj).st.tw β).ch x = D.chiD (dtU y) ^ cTw D (j + 1)
  rel : ∀ (N : ℕ) (M M' : SDLat D.host.E N), ∀ g ∈ Formalism.L2.Herm.UstdAf D.sp.cm N, Formalism.L2.Herm.Carries g M.1 M'.1 →
    ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y g → D.relDet N M M' = QuotientGroup.mk (dtU y)
  base : ∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)
  sharp : ∀ j < D.R.m, FormsSharpAt t u μ j
  dgen : IsDgen D t.cD
  tied : LatTied hT Gi Gl
  away : D.what₂.places.resChar w ∉ Dx.Qp μ
  cop : Nat.Coprime (Ideal.absNorm t.cc) (D.what₂.places.resChar w)
  empty : ∀ j, D.R.m < j → IsEmpty (Lv.comp j)
  alg : ∀ j hj β, SplAlg ((I.at' j hj).st.loc β)
  alg0 : SplAlg (lev0At Gd u w hg).A
  lbB : ∀ j hj β, LbAtB ((I.at' j hj).st.loc β) ((I.at' j hj).st.K β).lev.Lb
  lb0 : LbAtB (lev0At Gd u w hg).A (lev0At Gd u w hg).Lb
  pl : ∀ j hj β v, ((I.at' j hj).st.loc β).pl v = (lev0At Gd u w hg).A.pl v
  kin : ∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y

section Sys

variable {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} (H : CmpJHyp ex.cmp I) (X : LabIn I)
  [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg)

abbrev sysS : Sys (D.what₂.places.resChar w) :=
  sysAt (chainAt H hT) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg))
    (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT))
    (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le)

instance : IsFractionRing (sysS H X std).G.O (sysS H X std).G.Kf := Lt.fracAt Gl u w hg

variable {H X} {t : KerEntTied ex} (J : Joint t H X)

abbrev Joint.cp : ChartPts (sysS H X std) D :=
  cpAt (chainAt H hT) std _ _ _ _ _ (Lt.dGT_spec (kaAt X H hT)) _ I (lev0At J.Gd u w hg).A (lev0At J.Gd u w hg).J (lev0At J.Gd u w hg).Lb
    (lev0At J.Gd u w hg).Uloc

abbrev Joint.fd : FData (sysS H X std) D :=
  fdAtL (chainAt H hT) std _ _ _ _ _ (Lt.dGT_spec (kaAt X H hT)) _ I (lev0At J.Gd u w hg) J.a ∅

abbrev Joint.rho : ∀ v : (sysS H X std).Pl, D.host.E →+* (sysS H X std).G.P.Qq v := fun v => (lev0At J.Gd u w hg).A.iw v

def Joint.chart (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) : (J.St j hj).Ch := (J.St j hj).chOf (clsAt X H j La.1 La.2)

def Joint.IsPt (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j)
    (x : UPts (sigD D) (gramN D j hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  ∃ hr : ((sysS H X std).Pj j).m + 1 = D.R.N j, x.1 = Formalism.L2.PairingIndexBounds.F.reGL (finCongr hr) ((J.cp std).y j La)

def Joint.pt (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) : UPts (sigD D) (gramN D j hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  Classical.epsilon (J.IsPt std j hj La)


open Classical in
def Joint.xi0 (Xi : AdDatum J.St) (j : ℕ) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1))
    (z : Formalism.L2.Col.HomE D.host.E (((sysS H X std).Pj j).m + 1) (((sysS H X std).Pj (j + 1)).m + 1)) : ℂ :=
  if h : j + 1 ≤ D.R.m ∧ ((sysS H X std).Pj j).m + 1 = D.R.N j ∧ ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) then
    Xi j h.1 (J.chart std j _ La) (J.chart std (j + 1) h.1 La') (J.pt std j _ La) (J.pt std (j + 1) h.1 La')
      (homRe h.2.1 h.2.2 (Formalism.L2.Col.inFr ((J.fd std).trG j La).symm ((J.fd std).trG (j + 1) La').symm z))
  else 0

def Joint.Dict : Prop :=
  ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 →
    J.IsPt std j hj La (J.pt std j hj La) ∧
    (∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D j hj), ∃ κ : ((J.St j hj).K (J.chart std j hj La)).lev.U,
      (J.pt std j hj La).1 = ratA D.host.F γ * ((J.St j hj).y (clsAt X H j La.1 La.2)).1 * κ.1) ∧
    HEq ((J.fd std).kerN j La) (latK D.sp (gramN D j hj) J.a (J.pt std j hj La).1 ((J.St j hj).K (J.chart std j hj La)).lev.Lb) ∧
    (J.fd std).dt j La = Matrix.GeneralLinearGroup.det (J.pt std j hj La).1


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Joint.At where
  E : CEmbC (sysS H X std).G
  lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]
  hK : ∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (ex.cmp.embW u w hg z) = lam ⟨D.what₂.embLL z, hz⟩
  g : GL3Theta.G1 (D.what₂.places.resChar w)
  hLT : LTIso g
  curve : CurveIn D (D.what₂.places.resChar w) t.cc t.δ g t.B t.χ lam
  hfin : ∀ j c, ((sysS H X std).Lv.lev j c).FinClasses
  hst : FinStab (sysS H X std).Lv
  Xi : AdDatum J.St
  muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ
  law : AdLawAt J.A J.dtU J.a Xi muT

variable {std J} (S : J.At std)

abbrev Joint.At.Y : Pend (sysS H X std) :=
  pendG (sysS H X std) S.E S.hfin S.hst S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT

def Joint.At.Pair : Prop := GlobalTheory.TwU.PairOK (sysS H X std) (J.fd std) t.B t.χ (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (J.rho std)

def Joint.At.Move : Prop := GlobalTheory.TwU.MoveTie (sysS H X std) S.E.toCEmb (J.fd std) t.χ S.lam (J.xi0 std S.Xi) S.muT (J.rho std)

def Joint.At.Away : Prop := ∀ v, ∀ j < D.R.m,
  GlobalTheory.TwU.AwayTie (sysS H X std) S.E.toCEmb (J.fd std) t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (J.rho std) v j

def Joint.At.Pos : Prop := GlobalTheory.TwU.LamPos (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) S.lam (J.rho std)

def Joint.At.Scal : Prop := Lt.ScalGLt (sysS H X std) S.hfin (J.fd std) t.χ S.muT S.lam

def Joint.At.K1 : Prop :=
  Lt.ThetaSeriesDataHypothesesBelowMaximalLevel (sysS H X std) S.E S.hfin (hT.gat_pos u w hg) (J.fd std) t.χ S.lam (t.rd u μ).lev (J.xi0 std S.Xi) S.muT

def Joint.At.Law : Prop :=
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  GlobalTheory.TwU.KapLawLt (sysS H X std) ℂ_[D.what₂.places.resChar w] (thFOf (sysS H X std) (hT.gat_pos u w hg)
    (FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT)))

def Joint.At.Del (j : ℕ) : Prop :=
  ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) →
    ∃ cK : ℂ_[D.what₂.places.resChar w], ‖cK‖ = 1 ∧
      KernelDifferenceAtLevel (Y := S.Y) t u μ (kaAt X H hT).cls (kaAt X H hT).cmp ι (rdJ I X.onCh ι) (srOf S.Y) j cK

end Sys

def AllSites (Q : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv}
    {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] {std : Lt.StdAtW D Gl u w hg} {t : KerEntTied ex}
    {J : Joint t H X}, J.At std → Prop) : Prop :=
  ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv}
    {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] {std : Lt.StdAtW D Gl u w hg} {t : KerEntTied ex}
    {J : Joint t H X} (S : J.At std), Q S

def JointsAt (t : KerEntTied ex) (μ : D.what₂.Tup) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ →
    ∃ (Lv : Levels (Gl.Fl u w hg)) (I : CmpJIn ex.tw u μ w hg Lv) (H : CmpJHyp ex.cmp I) (X : LabIn I), Nonempty (Joint t H X)

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartTies3Site
noncomputable section

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem formsLev_re {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J' T f bad) (v : HeightOneSpectrum (𝓞 F)) :
    ((S.Uloc v).comap (reGL h _).toMonoidHom ≤ levelVL σ J v (reL h.symm S.Lb)) ∧
    ((T : 𝓞 F) ∉ v.asIdeal → SelfDualAt σ J v (reL h.symm S.Lb)) ∧
    (v ∉ bad → (T : 𝓞 F) ∉ v.asIdeal → levelVL σ J v (reL h.symm S.Lb) ≤ (S.Uloc v).comap (reGL h _).toMonoidHom) := by
  subst h
  obtain rfl : J' = J := by ext x y; exact hJ x y
  rw [reL_rfl]
  refine ⟨fun x hx => ?_, fun hT => ?_, fun hb hT x hx => ?_⟩
  · have hx' : reGL rfl _ x ∈ S.Uloc v := hx
    rw [Formalism.L2.Forms.reGL_rfl] at hx'
    exact S.Uloc_lev v hx'
  · exact self_dual_lattice_at F E a σ J' v S.Lb T S.Lb_fin (fun x hx y hy => S.Lb_int y hy x hx) (fun y hy => S.Lb_dual y hy) hT
  · show reGL rfl _ x ∈ S.Uloc v
    rw [Formalism.L2.Forms.reGL_rfl, S.Uloc_hyp v hb hT]
    exact hx

end Gen

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}


set_option maxHeartbeats 4000000 in
theorem hypTJC_site (Z : SiteD X0 u w hg M) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)
    (hT : ∀ i hi, ¬ D.what₂.places.resChar w ∣ (Z.Fo i hi).T) (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (Z.Fo i hi).Ch) :
    HypTJC ((Z.loc Fl ht i hi).t β) :=
  hypTJC_of_le ((Z.loc Fl ht i hi).t β)
    (fun w' _ => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').1)
    (fun w' h => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').2.1 (T_not_mem hg.1 (hT i hi) w' h))


set_option maxHeartbeats 4000000 in
theorem hypTJ_site (Z : SiteD X0 u w hg M) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)
    (hT : ∀ i hi, ¬ D.what₂.places.resChar w ∣ (Z.Fo i hi).T)
    (hbad : ∀ i hi, ∀ w' ∈ (Z.Fo i hi).bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal)
    (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (Z.Fo i hi).Ch) : HypTJ ((Z.loc Fl ht i hi).t β) :=
  hypTJ_of_ge ((Z.loc Fl ht i hi).t β)
    (fun w' h => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').2.2 (fun hb => hbad i hi w' hb h) (T_not_mem hg.1 (hT i hi) w' h))
    (fun w' h => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').2.1 (T_not_mem hg.1 (hT i hi) w' h))

variable {Tw : TwForms D} {μ : D.what₂.Tup}

end GlobalTheory.Port

end

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
noncomputable section

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.CmpJ.AgreeLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ChiDRat (D : D7) : Prop := ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ)

set_option maxHeartbeats 2000000 in
theorem chRat_ofChiD (h : ChiDRat D) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    {S : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad} (Y : DetTie S) (c : ℤ)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((DetTw.ofChiD Y c).ch x : ℂˣ) : ℂ) := by
  obtain ⟨r, hr⟩ := h (Y.dt x)
  refine ⟨r ^ c, ?_⟩
  rw [map_zpow₀, hr]
  show _ = (((D.chiD (Y.dt x)) ^ c : ℂˣ) : ℂ)
  rw [Units.val_zpow_eq_zpow_val]

set_option maxHeartbeats 2000000 in
theorem chRat_mem (h : ChiDRat D) {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) :
    ∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = (((formsInMem F dt i hi).tw β).ch (((formsInMem F dt i hi).K β).y cl) : ℂ) := by
  by_cases h' : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h']
    intro β cl
    exact chRat_ofChiD h _ _ _
  · rw [formsInMem_mid F dt i hi (by omega)]
    intro β cl
    exact chRat_ofChiD h _ _ _

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

theorem fillRec (ex : Extra D L hT Gi Gl Kc Dx cX) : ∀ u w hg, FillTie hT u w hg (Gl.Fl u w hg) := by
  intro u w hg v s b hb
  have h1 := ex.fills_all u w hg v s (b + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h2 : wj D (b + 1) (hT.gat_pos u w hg ⟨v, s⟩) = (((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (show b + 1 - 1 < D.R.m by simpa using hb), D.hcW_e]
    rfl
  rw [h2] at h1
  have e : ((((Gl.Fl u w hg).w v (b + 1) s : ℤ) : ℚ) : ℝ) =
      ((wG D.R ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩) (b + 1) : ℚ) : ℝ) := by
    rw [Rat.cast_intCast, h1]
    unfold wG G.kaJ
    push_cast
    ring
  exact Rat.cast_injective e

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

section Gen

variable {L : Type} [Field L] [NumberField L]

end Gen

variable {D : D7}

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

end GlobalTheory.Port

end

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
noncomputable section

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unit_of_root {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    (x : K) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) : ∃ o : Oˣ, algebraMap O K (o : O) * x = 1 := by
  have hint : IsIntegral O x :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hx]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hy1 : y ^ k * y = 1 := by
    apply IsFractionRing.injective O K
    rw [← pow_succ, map_pow, hy, hx, map_one]
  refine ⟨⟨y ^ k, y, hy1, by rw [mul_comm]; exact hy1⟩, ?_⟩
  show algebraMap O K (y ^ k) * x = 1
  rw [← hy, ← map_mul, hy1, map_one]

theorem exists_char {G₀ LL O K : Type} [Group G₀] [Field LL] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (emb : LL →+* ℂ) (e : LL →+* K) (χ : G₀ →* ℂˣ) (hrat : ∀ a, ∃ r : LL, emb r = (χ a : ℂ))
    (hfin : ∃ n : ℕ, 0 < n ∧ ∀ a, χ a ^ n = 1) :
    ∃ ψ : G₀ →* Oˣ, ∀ a (r : LL), emb r = (χ a : ℂ) → algebraMap O K (ψ a : O) * e r = 1 := by
  have ex : ∀ a : G₀, ∃ o : Oˣ, ∀ r : LL, emb r = (χ a : ℂ) → algebraMap O K (o : O) * e r = 1 := by
    intro a
    obtain ⟨r, hr⟩ := hrat a
    obtain ⟨n, hn, hc⟩ := hfin
    have hrn : r ^ n = 1 := emb.injective (by
      rw [map_pow, hr, map_one, ← Units.val_pow_eq_pow_val, hc, Units.val_one])
    obtain ⟨o, ho⟩ := unit_of_root (O := O) (e r) n hn (by rw [← map_pow, hrn, map_one])
    exact ⟨o, fun r' hr' => by rw [emb.injective (hr'.trans hr.symm)]; exact ho⟩
  choose f hf using ex
  refine ⟨MonoidHom.mk' f ?_, fun a r hr => hf a r hr⟩
  intro a b
  obtain ⟨ra, hra⟩ := hrat a
  obtain ⟨rb, hrb⟩ := hrat b
  have h1 := hf (a * b) (ra * rb) (by rw [map_mul, hra, hrb, map_mul, Units.val_mul])
  have h2 := hf a ra hra
  have h3 := hf b rb hrb
  have h4 : algebraMap O K ((f a * f b : Oˣ) : O) * e (ra * rb) = 1 := by
    rw [Units.val_mul, map_mul, map_mul]
    calc _ = (algebraMap O K (f a : O) * e ra) * (algebraMap O K (f b : O) * e rb) := by ring
      _ = 1 := by rw [h2, h3, one_mul]
  have hne : e (ra * rb) ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact Units.ext (IsFractionRing.injective O K (mul_right_cancel₀ hne (h1.trans h4.symm)))

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}


set_option maxHeartbeats 4000000 in
def kap (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) (p : ℕ) :
    awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p →* (Fo.K β).lev.U :=
  ((glue (epsP D.host.F p D.host.E) (isIdempotentElem_placeIdempotent D.host.F p D.host.E)).comp
    (((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _).toMonoidHom.comp
      (awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p).subtype).prod 1)).codRestrict (Fo.K β).lev.U (by
    intro a
    have ha := (mem_awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p a.1).1 a.2
    refine ((Fo.K β).lev.U_eq _).2 ⟨glue_mem_UJ (epsP D.host.F p D.host.E) (isIdempotentElem_placeIdempotent D.host.F p D.host.E) _
      (epsP_sig D.host.F p D.host.E (sigD D)) _
      (reGL_mem_UPts (rankN D (i + 1) hi) (sigD D) (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi) _ a.1 ha.1)
      (Subgroup.one_mem _), fun v => ?_⟩
    by_cases hv : ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
    · show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) ∈ _
      rw [bc_glue_one _ _ _ (epsP_over D.host.F p D.host.E v hv)]
      show bc (prV (E := D.host.E) v) 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) ∈ _
      rw [bc_glue_zero _ _ _ (epsP_off D.host.F p D.host.E v hv)]
      show bc (prV (E := D.host.E) v) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _ a.1) ∈ _
      rw [bc_reGL]
      exact ha.2 v hv)

theorem kap_over (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) (p : ℕ) (a : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) (kap Fo β p a).1 = 1 := by
  show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) = 1
  rw [bc_glue_one _ _ _ (epsP_over D.host.F p D.host.E v hv)]
  exact map_one _

theorem kap_off (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) (p : ℕ) (a : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ((p : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    bc (prV (E := D.host.E) v) (kap Fo β p a).1 =
      bc (prV (E := D.host.E) v) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _ a.1) := by
  show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) = _
  rw [bc_glue_zero _ _ _ (epsP_off D.host.F p D.host.E v hv)]
  rfl


set_option maxHeartbeats 4000000 in
theorem chi_kap (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) (p : ℕ) (a : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p)
    (κ : (Fo.K β).lev.U)
    (hκp : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → bc (prV (E := D.host.E) v) κ.1 = 1)
    (hκo : ∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((p : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal →
      bc (prV (E := D.host.E) w') κ.1 = bc (prV (E := D.host.E) w') (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _ a.1)) :
    (Fo.K β).lev.chi κ = (Fo.K β).lev.chi (kap Fo β p a) := by
  have h1 : (Fo.K β).lev.chi (κ * (kap Fo β p a)⁻¹) = 1 := by
    refine (Fo.K β).lev.chi_triv _ fun v _ => ?_
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    by_cases hv : ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
    · rw [hκp v hv, kap_over Fo β p a v hv, inv_one, one_mul]
    · rw [hκo v hv, kap_off Fo β p a v hv, mul_inv_cancel]
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1


set_option maxHeartbeats 4000000 in
theorem psiEx_of (Fo : FormsIn M (i + 1) hi) (e : D.what₂.LL →+* (D.gat u w hg).Kf)
    (hfr : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hrat : ∀ β, ChiRatAll (Fo.K β).lev D.what₂.embLL)
    (hfin : ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (Fo.K β).lev.chi κ ^ n = 1) : PsiEx Fo e := by
  intro β
  obtain ⟨n, hn, hc⟩ := hfin β
  obtain ⟨ψ, hψ⟩ := exists_char (O := (D.gat u w hg).O) D.what₂.embLL e
    ((Fo.K β).lev.chi.comp (kap Fo β (D.what₂.places.resChar w))) (fun a => hrat β _) ⟨n, hn, fun a => hc _⟩
  refine ⟨ψ, fun a κ hκp hκo => ?_⟩
  obtain ⟨r, hr⟩ := hrat β κ
  exact ⟨r, hr, hψ a r (hr.trans (congrArg (fun z : ℂˣ => (z : ℂ)) (chi_kap Fo β _ a κ hκp hκo)))⟩

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem finite_glk (v : HeightOneSpectrum (𝓞 F)) : Finite (GL (Fin n) (kv F v)) := by
  have : Finite (kv F v) := Formalism.UG.P.glint_finite_residueField v
  have : Finite (Matrix (Fin n) (Fin n) (kv F v)) := inferInstanceAs (Finite (Fin n → Fin n → kv F v))
  exact Finite.of_injective (fun u : GL (Fin n) (kv F v) => (u : Matrix (Fin n) (Fin n) (kv F v))) (fun _ _ h => Units.ext h)


open Classical in
theorem chi_fin_of_glevH {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp}
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (L : GLevH S G H lam) (hgp : ∀ a, gp a ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∀ κ, S.chi κ ^ m = 1 := by
  have hfin : ∀ a, {v : HeightOneSpectrum (𝓞 F) | (gp a : 𝓞 F) ∈ v.asIdeal}.Finite :=
    fun a => Formalism.L2.G.finite_setOf_mem_asIdeal (Nat.cast_ne_zero.2 (hgp a))
  have hN : ∀ v : HeightOneSpectrum (𝓞 F), 0 < Nat.card (GL (Fin n) (kv F v)) := fun v =>
    haveI := finite_glk (n := n) v
    Nat.card_pos
  refine ⟨∏ a : Fin 2, ∏ v ∈ (hfin a).toFinset, Nat.card (GL (Fin n) (kv F v)),
    Finset.prod_pos fun a _ => Finset.prod_pos fun v _ => hN v, fun κ => ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, L.chi_eq κ, Units.val_one, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun a _ => ?_
  have hsup : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => ∏ᶠ (h : (gp a : 𝓞 F) ∈ v.asIdeal),
      (((lam a v h (L.red a v h κ) : ℂˣ) : ℂ))⁻¹) ⊆ ((hfin a).toFinset : Set (HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    rw [Function.mem_mulSupport, finprod_eq_dif] at hv
    by_cases h : (gp a : 𝓞 F) ∈ v.asIdeal
    · exact Finset.mem_coe.2 ((Set.Finite.mem_toFinset (hfin a)).2 h)
    · rw [dite_eq_right h] at hv
      exact absurd rfl hv
  rw [finprod_eq_prod_of_mulSupport_subset _ hsup, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun v hv => ?_
  have h : (gp a : 𝓞 F) ∈ v.asIdeal := (Set.Finite.mem_toFinset (hfin a)).1 hv
  rw [finprod_eq_dif, dite_eq_left h]
  have hd : Nat.card (GL (Fin n) (kv F v)) ∣ ∏ a : Fin 2, ∏ v ∈ (hfin a).toFinset, Nat.card (GL (Fin n) (kv F v)) :=
    (Finset.dvd_prod_of_mem _ hv).trans (Finset.dvd_prod_of_mem (fun a : Fin 2 => ∏ v ∈ (hfin a).toFinset, Nat.card (GL (Fin n) (kv F v)))
      (Finset.mem_univ a))
  obtain ⟨q, hq⟩ := hd
  have h1 : (L.red a v h κ) ^ Nat.card (GL (Fin n) (kv F v)) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have := finite_glk (n := n) v
    exact pow_card_eq_one'
  have h2 : ((lam a v h (L.red a v h κ) : ℂˣ) : ℂ) ^ Nat.card (GL (Fin n) (kv F v)) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one]
  rw [hq, inv_pow, pow_mul, h2, one_pow, inv_one]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem chi_fin_top (F : FormsTiedSym D u Ch chOf) (j : ℕ) (hj : j ≤ D.R.m) (h : j = D.R.m) :
    ∃ m : ℕ, 0 < m ∧ ∀ κ, (F.cls j hj (Or.inr h)).lev.chi κ ^ m = 1 := by
  subst h
  exact chi_fin_of_glevH F.glevM fun a => (D.host.g_prime a).ne_zero


set_option maxHeartbeats 2000000 in
theorem finMem_of (F : FormsTiedSym D u Ch chOf) (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) :
    ∀ β, ∃ m : ℕ, 0 < m ∧ ∀ κ, ((formsInMem F dt i hi).K β).lev.chi κ ^ m = 1 := by
  by_cases h : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h]
    intro β
    exact chi_fin_top F (i + 1) hi h
  · rw [formsInMem_mid F dt i hi (by omega)]
    intro β
    exact chi_fin_of_glevH (F.glevC (i + 1) _ _ β) fun a => (D.host.g_prime a).ne_zero

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv Formalism.L2.G.Cmp
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ} {LL : Type} [Field LL]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}


end GlobalTheory.Port

end

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
noncomputable section

section
namespace GlobalTheory.Port

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.KAat Formalism.L2.Ker
open GlobalTheory.TwU (StepCharts ChainCharts AdData AdPins AdTie latCo)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Site

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Tw : TwForms D} {μ : D.what₂.Tup}

def SiteD.inTw (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) :
    CmpJIn Tw u μ w hg (Z.lv Fl ht) := Formalism.MainNotions.G.KAat.inTw fun j hj => Z.st Fl ht Gt j hj

def ValAll (Tw : TwForms D) (St : ChainCharts D u μ) : Prop :=
  ∀ i hi, ValuationCompatibleChart (Tw.fm u μ) (St i hi).eY (fun _ => True) (St i hi).chOf (St i hi).K


set_option maxHeartbeats 2000000 in
def foOf (Hh : Formalism.L2.Herm.SymmetricHermitianColumns D) (St : ChainCharts D u μ) (hv : ValAll Tw St) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    FormsIn (Tw.fm u μ) (j + 1) hj where
  T := (St (j + 1) hj).T
  bad := (St (j + 1) hj).bad
  eY := (St (j + 1) hj).eY
  okW := fun _ => True
  Ch := (St (j + 1) hj).Ch
  chOf := (St (j + 1) hj).chOf
  lat := (St (j + 1) hj).lat
  K := (St (j + 1) hj).K
  val := by
    unfold ValAll at hv
    exact hv (j + 1) hj
  tw := fun _ => DetTw.ofChiD (detTieOf Hh _) (cTw D (j + 1))

end Site

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in
structure JIn (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) where
  Gd : GroupCompatibilityAll D hT ex.cmp
  Hh : Formalism.L2.Herm.SymmetricHermitianColumns D
  rel : Formalism.L2.Herm.SymmetricRelativeDeterminant D Hh
  St : ChainCharts D u μ
  A : AdData t u μ St
  a : 𝓞 D.host.E
  pins : AdPins A Hh.dt
  tie : AdTie A Hh.dt a
  val : ValAll ex.tw St
  fin : ∀ i hi, Finite (St i hi).Ch
  ord : ∀ i hi β, ∃ n : ℕ, 0 < n ∧ ∀ κ, ((St i hi).K β).lev.chi κ ^ n = 1
  base : ∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)
  joint0 : Joint0 Gd.herm.lev0 u (Gd.forms u)
  e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0
  jointCmpEmbeddingY : (D.mem u).C.Y 0 ≃ (D.chTw u μ).Y 0
  e0Tw : ∀ φ c y, D.e0Tw u μ φ (e0 c) (jointCmpEmbeddingY y) = φ c y
  lev0 : ∀ β : (St 0 (Nat.zero_le _)).Ch, ((St 0 _).K β).lev.Lb = (Gd.forms u).cls0.lev.Lb ∧
    ((St 0 _).K β).lev.Uloc = (Gd.forms u).cls0.lev.Uloc ∧ ((St 0 _).K β).lev.U = (Gd.forms u).cls0.lev.U ∧
    ∀ (κ : ((St 0 _).K β).lev.U) (κ' : (Gd.forms u).cls0.lev.U), κ.1 = κ'.1 → ((St 0 _).K β).lev.chi κ = (Gd.forms u).cls0.lev.chi κ'
  ch0 : Subsingleton (St 0 (Nat.zero_le _)).Ch
  y0 : ∀ c, ∃ κ : (Gd.forms u).cls0.lev.U, ((St 0 (Nat.zero_le _)).y (e0 c)).1 = ((Gd.forms u).cls0.y c).1 * κ.1 ∧
    (Gd.forms u).cls0.lev.chi κ = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ q ∈ Dx.Qp μ, ((q : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) →
      bc (prV (E := D.host.E) v) κ.1 = 1
  fr0 : ∀ y, (St 0 (Nat.zero_le _)).eY (jointCmpEmbeddingY y) = (Gd.forms u).val0.eY y
  rat : ∀ j, j < D.R.m → (ex.tw.fm u μ).KRat j
  kin : ∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y
  chiD : ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ)

end GlobalTheory.Port
end

end
end
