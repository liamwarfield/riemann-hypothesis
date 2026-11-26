module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {D : D7}
section Real
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
def QAllAlt (PP : Pl D.host.E) : Prop := ∃ t, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t
structure PackageHypotheses : Prop where
  bot : _root_.GlobalTheory.MiTop.BottomHypotheses W
  lev : _root_.GlobalTheory.MiS.LevelHypothesis W
  ex : (_root_.GlobalTheory.Fam.pk_z W).ExAt
  hTop : ∀ t, LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e) =
    MultT (_root_.GlobalTheory.Fam.pk_z W).θ (_root_.GlobalTheory.Fam.pk_z W).MX (levS _ (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t))
  gap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D
  fin : Finite W.P.T
  sel : ∀ PP PP', _root_.GlobalTheory.Fam.QAllAlt W PP → _root_.GlobalTheory.Fam.QAllAlt W PP' → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP'
  aa : ∀ PP : Pl D.host.E, (_root_.GlobalTheory.Fam.QAllAlt W PP ∨ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ ∃ u, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
variable {W} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
structure FamilyCharacter.RowOK : Prop where
  meas : GeoMeas (_root_.GlobalTheory.Fam.pk_z W) f.g
  last : f.c.VolLast
  x : ∀ j, j ≤ D.R.m → (f.g.x j).Is
  row : ∀ t, (f.row t).Is
  same : ∀ t t', (f.row t).Same (f.row t')
structure FamilyCharacter.ColOK : Prop where
  kom : ∀ t j, j < D.R.m → IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1)) ((f.col t).kom j)
  ker : ∀ t j, j < D.R.m → ∀ α γ, ((f.t t).ker j α γ).Is f.c.ψ f.c.θ (f.c.x j) (f.c.x (j + 1))
  e : ∀ t j α, ∀ g ∈ ((f.col t).e j α).support, g ∈ GfC (Yc D j)
  eT : ∀ t n h β, ∀ g ∈ ((f.col t).eT n h β).support, g ∈ GfC D.sp.X'
  stabK : ∀ t j, j < D.R.m → ∀ ψ ∈ (f.col t).Ram j, (f.t t).K j ψ ∈ (f.col t).Ram (j + 1)
  stabS : ∀ t j, j ≤ D.R.m → ∀ ψ ∈ (f.col t).Ram j, (f.col t).S j ψ ∈ (f.col t).Ram j
structure CommutingVectorTie (v : VCom f.c) : Prop where
  b : ∀ j, v.b j = f.g.b j
  bT : v.bT = f.g.bT ∧ v.NT = f.g.LT
  gP : ∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  tP : ∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal
  moves : ∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) →
    GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (v.N j) P
  movesT : ∀ P, GlobalTheory.FinPl.Moves D.sp.X' f.g.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX f.g.LT P
  Ψ : ∀ j, j + 1 < D.R.m → ∃ o, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧ ∀ P a a', v.Ψ j P a a' = comb f.c.ψ _ _ o
    ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) (pureTensorO f.c.ψ f.c.θ (Yc D j) (Yc D (j + 1))
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P))
  ΨT : ∀ j h, ∃ o, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧ ∀ P, v.ΨT j h P = comb f.c.ψ _ _ o
    (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P))
  nz : (∀ j, j + 1 < D.R.m → ∃ P, v.Ψ j P 1 1 ≠ 0) ∧ ∀ j h, ∃ P, v.ΨT j h P ≠ 0
def IsDivisorGlobal (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (j : ℕ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V)
    (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ) (d : WO (Yc D j) V →₀ ℂ) : Prop :=
  GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) d ∧
    IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β
      (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ∅ (fun _ => 1) vac
      (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ d vac)
def IsDivisorRational (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (j : ℕ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V)
    (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ) (d : WO (Yc D j) V →₀ ℂ) : Prop :=
  GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) d ∧
    IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β
      (datY _ D.R.r D.R.t j (r_le_Y j) ∅ ((_root_.GlobalTheory.Fam.pk_z W).Q t) (LevelP.triv _ _ _) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1))
      ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) vac (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ d vac)
def RationalVectorCondition {t : W.P.T} (w : VTup (f.t t)) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ d, _root_.GlobalTheory.Fam.IsDivisorRational W t j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d →
    ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (· ∈ w.Q) g →
      (f.t t).om j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d g) =
        comb f.c.ψ _ _ (w.eQ j) ((f.t t).om j (f.g.b j, f.g.b (j + 1)) g)) ∧
  ∀ j h d, _root_.GlobalTheory.Fam.IsDivisorRational W t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d →
    ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX (· ∈ w.Q) g →
      (f.t t).omT j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d g) =
        comb f.c.ψ _ _ (w.eQT j h) ((f.t t).omT j h (f.g.b (j + 1), f.g.bT) g)
structure LocalGroupReading {v : VCom f.c} {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) : Prop where
  idem : ∀ i, Formalism.L2.NTheta.IsIdemAt (G i).q.e (pl i).1 ∧ (G i).q.v = (pl i).1.under (𝓞 D.host.F)
  mu : ∀ i j, 1 ≤ j → j ≤ D.R.m → (ofSplit (G i).q).IsComp (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ ((G i).S.μ j)
  frame : ∀ i j c (hc : j + c = (G i).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((G i).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G i).q) (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).βY j)
      ((((G i).FY j c hc).β * (((G i).S.T (Fin D.R.t)).bas j c hc).val).submatrix id
        fun a => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm a))
  frameTop : ∀ i, ∃ e : Ix (Fin D.R.k ⊕ Fin ((G i).s + 1)) (Fin D.R.t) ((G i).s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G i).q) D.sp.X' f.g.bT (_root_.GlobalTheory.Fam.pk_z W).βX ((G i).FT.β.submatrix id e.symm)
  lev : ∀ (g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP PP.1)),
    (g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H ↔ ∀ i, ∃ x : (G i).S.P.J, ∀ (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1) ∧
    ∀ (hg : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H) (x : ∀ i, (G i).S.P.J), (∀ i (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x i : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1) →
      (_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g, hg⟩ = ∏ i, (G i).S.P.lam (x i)
end Real
section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
structure ValidRealPackage (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop where
  ok : I.Ok
  pins : Nonempty (TC.Pins B X)
  tw : I.IsTw
  std : Nonempty (I.StdC l Z W.R.T.cols)
  chr : ∀ j : Fin B.R.m, ChrEq ((_root_.GlobalTheory.Fam.pk_z W).mu0 ((j : ℕ) + 1)) (I.C.mu0 j)
  top : _root_.GlobalTheory.Fam.LeadingReadStatement W
end True
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
variable (Y : Cov p i)
def RowsTAlt : Prop := p.PointConditions' ∧ RecTied D L
def EventuallyAtAllPoints {eps : ℝ} (Fm : FamP eps) (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p : Pt Fm x hx ι), _root_.GlobalTheory.CovTop.RowsTAlt p → Q x hx ι p
theorem EventuallyAtAllPoints.and {eps : ℝ} {Fm : FamP eps} {Q Q' : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop}
    (h : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm Q) (h' : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm Q') : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun x hx ι p => Q x hx ι p ∧ Q' x hx ι p := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  exact ⟨max a b, fun x hx hle ι p hp =>
    ⟨h x hx ((le_max_left _ _).trans hle) ι p hp, h' x hx ((le_max_right _ _).trans hle) ι p hp⟩⟩
def LiftsCondition (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
    (PP C : ℝ), Prop) : Prop :=
  Closed FamHyp fun Fm _ => ∃ C : ℝ, 0 ≤ C ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun x hx ι p => ∀ i, Q Fm x hx ι p i (Fm.parT x hx ι).PP C
def CoversCondition (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
    (_Y : Cov p i) (PP C : ℝ), Prop) : Prop :=
  _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x hx ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m →
    ∀ Y : Cov p i, GoodCov p i Y → Q Fm x hx ι p i Y PP C
def GramCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => GramAt p i
def LiftRecursive : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => RecAt p i
def LiftTruncation : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => CutAt p i
def LiftBadSet : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => BadAt p i
def LiftLambdaBound : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => LamAt p i C
def SizeCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i PP C => SizeAt p i PP C
def MeasureCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => MeasAt p i C
def LiftRational : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => RatAt p i
def CoreBound' : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => CoreAt p i C
def LiftLowBound : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => LowAt p i C
def AnchorCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => AnchorAt p i C
def LowDefectCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → LowAt p i C
def DeepExistence : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 < (Fm.D x ι).R.m →
  ∃ Y : Cov p i, GoodCov p i Y
def DeepGoodness : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => DeepGoodAt p i Y
def RingCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => RingAt p i Y
def MapsCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => MapsAt p i Y
def CoverRank : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => RkAt p i Y PP
def MinimalGenerator : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => GminAt p i Y PP
def FlatDegreeCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => FlatDegAt p i Y
def FlatnessCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ C => FlatAt p i Y C
def UniformLowerBound : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ C => UAt p i Y C
def SumBoundCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => SumAt p i Y
def CoverDegree : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → DegAt p i Y u1
def ShareCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → ShareAt p i Y PP u1
def HeightCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → HeightAt p i Y PP C u1
def CoverHeightSum : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → HSAt p i Y PP C u1
def CovolumeBoundOfX : Prop := Closed FamHyp fun Fm CH =>
  ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH)
end GlobalTheory.CovTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Record
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)
end Record
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
def AtPtsAlt (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop) : Prop :=
  Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => More p → Q Fm x hx i p
def ForallTwoRuns (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (r : TwoRuns p.T p.P.Gp),
    RunsOk (fw2 p) r → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → Q Fm x hx i p r h
def ForallRecordObjects (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (c : OnConst),
    Obj p c → Prop) : Prop :=
  Closed FamHyp fun Fm _ => ∃ c0 : ℝ, ∀ c : OnConst, c0 ≤ c.C → OnPage.ConstBad c →
    _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => More p → ∀ (r : TwoRuns p.T p.P.Gp) (O : Obj p c), RecAt p (Fm.parT x hx i) r O → Q Fm x hx i p c O
def TwoRunsStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun _ _ _ _ p => ∃ r : TwoRuns p.T p.P.Gp, RunsOk (fw2 p) r ∧ OwnPin r
def RationalityStatement' : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun _ _ _ _ p => TwistedRational (R2 p) (F2 p) fun _ => 1
def ExportedStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ v ∈ p.R.twPl, ∀ j,
  GlobalTheory.TwistIndex.ExportTie p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)
def MaximalityStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i p => ∀ v ∈ p.R.twPl, ∀ j,
  GlobalTheory.TraceClassRank.SpanOverClasses (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)
def GeometricStatement' : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ p _ O => LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O ∧ LeafData O ∧ HasIndexBound O ∧
  ∀ C CH, LeafDepthGood ((R2 p).num (F2 p) C CH) O ∧ LeafDepthRam ((R2 p).num (F2 p) C CH) O ∧
    LeafDepth2 ((R2 p).num (F2 p) C CH) O ∧ LeafDepthLevel ((R2 p).num (F2 p) C CH) O
def TwistStatement' : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => HasTwistBound O
def ShareStatement : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => LeafShareI O
def BadPlacesStatement : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => LeafBadShare O
def ExponentStatement : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ p _ O => ∀ C CH, HasExpBound ((R2 p).num (F2 p) C CH) O
def PageStatement : Prop := _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafPage O ∧ LeafSizes O ∧ LeafX O ∧ LeafBad O ∧
  LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O ∧ O.b = (Fm.L x i).sc.b ∧ 0 ≤ p.Z.E1u ∧
    ∀ C CH, ErrorConstantMatchesDefinition ((R2 p).num (F2 p) C CH) O C
def SurjectiveOntoX : Prop := Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => More p → ∀ C, C0 ≤ C → (p.S false).ON (p.N C CH)
section Checks
section Cell
end Cell
end Checks
end GlobalTheory.BigOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRows
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLiftsBijectiveBase
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLiftsBijectiveBase
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn.SplitRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
theorem lUnif_of_rows_alt (p : PtAt ex Csz) (h : p.PointConditions') : (R2 p).LUnif := h.prim.unif
theorem split_lifts_bijective_of_split_data (p : PtAt ex Csz) (h : p.PointConditions') : ((R2 p).toCx (F2 p)).H5 (F2 p).cr false := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  have h5 := hR.lifts0.1
  rw [GlobalTheory.CharRealise.toCx3_eq_one p.R p.F p.phsOne] at h5
  exact h5
theorem rat_theta_of_split_data (p : PtAt ex Csz) (h : p.PointConditions') : ((R2 p).toCx (F2 p)).RATth (F2 p).cr false := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  have hr := hR.ratTh
  rw [GlobalTheory.CharRealise.toCx3_eq_one p.R p.F p.phsOne] at hr
  exact hr
theorem level_proviso_of_split_data (p : PtAt ex Csz) (h : p.PointConditions') : (lv ((F2 p).fc ((R2 p).toCx (F2 p)).zs) false).Proviso := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  have hv := hR.proviso0
  rw [GlobalTheory.CharRealise.toCx3_eq_one p.R p.F p.phsOne] at hv
  exact hv
theorem base_links_of_split_data (p : PtAt ex Csz) (h : p.PointConditions') : BaseLinks (R2 p) (F2 p) :=
  ⟨_root_.GlobalTheory.BigOn.SplitRows.split_lifts_bijective_of_split_data p h, _root_.GlobalTheory.BigOn.SplitRows.rat_theta_of_split_data p h, _root_.GlobalTheory.BigOn.SplitRows.level_proviso_of_split_data p h⟩
theorem rank_conditions_of_split_data (p : PtAt ex Csz) (h : p.PointConditions') : RankRows (S2 p) := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  exact ⟨(indefiniteDataAtBaseLevel hR).D_pos, fun j => (indefiniteDataAtBaseLevel hR).dW_eq (hR.wf false) j⟩
end Point
theorem uniform_and_base_links_and_rank_of_split_data : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    p.PointConditions' → (R2 p).LUnif ∧ BaseLinks (R2 p) (F2 p) ∧ RankRows (S2 p) :=
  fun _ _ _ _ _ _ _ _ _ _ p h => ⟨_root_.GlobalTheory.BigOn.SplitRows.lUnif_of_rows_alt p h, _root_.GlobalTheory.BigOn.SplitRows.base_links_of_split_data p h, _root_.GlobalTheory.BigOn.SplitRows.rank_conditions_of_split_data p h⟩
end GlobalTheory.BigOn.SplitRows
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLiftsBijectiveBaseStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l_unif_base_links_rank_of_pt_split : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → (R2 p).LUnif ∧ BaseLinks (R2 p) (F2 p) ∧ RankRows (S2 p) := by
  first | exact @_root_.GlobalTheory.BigOn.SplitRows.uniform_and_base_links_and_rank_of_split_data | exact _root_.GlobalTheory.BigOn.SplitRows.uniform_and_base_links_and_rank_of_split_data | (intros; apply _root_.GlobalTheory.BigOn.SplitRows.uniform_and_base_links_and_rank_of_split_data <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OmpinsOnto
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OmpinsOnto
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end
theorem ompins_onto_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' →
    BarTie (fw2 p) ∧ (∀ i, OMPins p.T (R2 p) p.κ p.v₀ (om2 p) i) ∧
      ∀ i, PhaseTie p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i :=
  fun _ _ _ _ _ _ _ _ _ _ p what₂ => ⟨conjugateReadingsVanishing_splitPart p, thetaRowData_pins_splitPart p, phaseCompatible_splitPart_of_liftUniformisation p what₂.prim.unif⟩
end GlobalTheory.BigOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OmpinsOntoStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bar_tie_om_pins_phase_tie_of_pt_split : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → BarTie (fw2 p) ∧ (∀ i, OMPins p.T (R2 p) p.κ p.v₀ (om2 p) i) ∧ ∀ i, PhaseTie p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i := by
  first | exact @_root_.GlobalTheory.BigOn.ompins_onto_alt | exact _root_.GlobalTheory.BigOn.ompins_onto_alt | (intros; apply _root_.GlobalTheory.BigOn.ompins_onto_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRows
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.BigOn
theorem links2_of_rows_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    p.PointConditions' → SingleIndexPlacesAreTwisted p → Links2 p := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hr hw
  obtain ⟨hU, hB, hR⟩ := _root_.GlobalTheory.T.l_unif_base_links_rank_of_pt_split D L hT Gi Gl Kc Y cX ex Csz p hr
  obtain ⟨hBar, hPin, hPh⟩ := _root_.GlobalTheory.T.bar_tie_om_pins_phase_tie_of_pt_split D L hT Gi Gl Kc Y cX ex Csz p hr
  exact ⟨GlobalTheory.T.char_R2_of_exAt_of_singleIndexPlacesTwisted D L hT Gi Gl Kc Y cX ex Csz p hr.exAt hw, hr.ok.ok2, hU, hB, hR, hBar, hPin, hPh⟩
end GlobalTheory.BigOn
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.links2_of_single_index_twisted : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → SingleIndexPlacesAreTwisted p → Links2 p := by
  first | exact @_root_.GlobalTheory.BigOn.links2_of_rows_alt | exact _root_.GlobalTheory.BigOn.links2_of_rows_alt | (intros; apply _root_.GlobalTheory.BigOn.links2_of_rows_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
def TwistSelectionFunctions {eps : ℝ} (Fm : FamP eps) : Type _ :=
  Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.RecTAlt (Fm.ex x hx i)
def TwistSelection (𝒞 : FamClass) : Type _ := ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → _root_.Formalism.L2.TwistSelectionFunctions Fm
theorem TwistSelectionFunctions.tiedRec {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataRecursive (Fm.ex x hx i) :=
  ⟨s.1, fun x hx h i => ⟨s.2 x hx h i⟩⟩
end Formalism.L2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
def pointOfRealisation (pin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt Rc.T P) {Del h0 : ℕ} (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) {c : ℝ}
    (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf (zscOf P Del h0 c) S) (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) : PtAt ex c where
  P := rowSideOfCompatibleThetaPair P
  Del := Del
  h0 := h0
  hDel := hDel
  hh0 := hh0
  Dcf := Dcf
  Spf := Spf
  gamDvd := pin.gamDvd
  T := B.T
  alg := B.alg
  R := B.Q.Rl
  charW := B.Q.charW
  zs := B.Q.zs
  s0 := B.Q.s0
  s1 := B.Q.s1
  dc := B.Q.dc
  stdChar := B.Q.stdChar
  signs := B.Q.signs
  cG := B.Q.cG
  Sx := B.Q.Sx
  nexp := B.Q.nexp
  stdV := B.Q.stdV
  stdX := B.Q.stdX
  host := B.Q.host
  err_eq := B.Q.err_eq
  vpos := B.Q.vpos
  κ := B.κ
  v₀ := B.v₀
  fw := B.fw
  bar := B.bar
  O := B.O
  pins := B.pins
  rhoGeo := B.rhoGeo
  equivAll := B.equivAll
  cTie := B.cTie
  phase := B.phase
  qGuard := Qp.qGuard
  hF := Qp.hF
  phsOne := Qp.phsOne
  prXunit := Qp.prXunit
  grpRecPin := Qp.grpRecPin
  fdiag := Qp.fdiag
  eGtie := Qp.eGtie
  betaStd := Qp.betaStd
  tupT := Qr.tupT
  hm := Qr.hm
  Tp := Qr.Tp
  tupXi := Qr.recR.tupXi
  tupAt := Qr.recR.tupAt
  tupTie := Qr.tupTie
  tupT_tup := Qr.tupT_tup
  muEq := Qr.muEq
def PointSummands.pt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : PtAt O.ex c :=
  _root_.GlobalTheory.Fc.Ind.pointOfRealisation b.pin b.DH.2.1 b.DH.2.2 b.B b.pins b.Rr
def conditionOnPoint (G : PtP) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun D O c b => G D O c b.pt
def RowPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => b.pt.PointConditions'
end GlobalTheory.Fc.Ind
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
open GlobalTheory.ChainOnto
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
def com_z : Com D where
  θ := (_root_.GlobalTheory.Fam.pk_z W).θ
  ψ := (_root_.GlobalTheory.Fam.pk_z W).ψ
  μ := (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0
  η := (_root_.GlobalTheory.Fam.pk_z W).eta
  Pg := (_root_.GlobalTheory.Fam.pk_z W).Pg
  P := _root_.GlobalTheory.Fam.complexLevelStructure W
  chi := (_root_.GlobalTheory.Fam.pk_z W).chi
def inverseLevelCardinality : ENNReal := ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ENNReal))⁻¹
def stageOfSpaceY (j : ℕ) : PiLocalization₂ D where
  V := Yc D j
  par := parB (Ptw D) (min j D.R.m)
  M := (_root_.GlobalTheory.Fam.pk_z W).MY j
  Λ := (_root_.GlobalTheory.Fam.pk_z W).ΛY j
  β := (_root_.GlobalTheory.Fam.pk_z W).βY j
  L := (_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 j (_root_.GlobalTheory.Fam.complexLevelStructure W)
  ν := _root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j
  fd := (_root_.GlobalTheory.Fam.pk_z W).fdY W.P.A3.A.μ0 j
def stageOfSpaceX : PiLocalization₂ D where
  V := D.sp.X'
  par := parB (Ptw D) D.R.m
  M := (_root_.GlobalTheory.Fam.pk_z W).MX
  Λ := (_root_.GlobalTheory.Fam.pk_z W).ΛX
  β := (_root_.GlobalTheory.Fam.pk_z W).βX
  L := datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0
  ν := _root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0
  fd := (_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0
variable {W} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
def transitionBetweenSpacesY (j : ℕ) : Step (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)) where
  ω := (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j
  f := (f.row W.P.A3.A.μ0).vP j
  It := (_root_.GlobalTheory.Fam.pk_z W).ItY j
  io := (f.row W.P.A3.A.μ0).io j
def transitionToSpaceX (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : Step (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)) (_root_.GlobalTheory.BaseChain.stageOfSpaceX W) where
  ω := omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h
  f := (f.row W.P.A3.A.μ0).vT j h
  It := f.c.ItT j h
  io := (f.row W.P.A3.A.μ0).ioT j h
end GlobalTheory.BaseChain
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
def col0_alt (t : W.P.T) (φ : D.what₂.Mu u) : (f.t t).Col 0 := D.e0Tw u (W.P.I.tup t) (D.eMu u φ).1
def descentToLevelZero (n : ℕ) (h : 2 * n + 2 * 0 + 2 = D.R.m) (t : W.P.T) (F : (f.t t).CT) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h F)).1
def LinkVanishes (d : _root_.GlobalTheory.MiTop.BottomData W u) : Prop :=
  ∀ n (h₀ : 0 + 2 * n + 2 = D.R.m) t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧
    ∀ G y v, (f.t t).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f t φ) G y v = d.per φ G.1 y v
def LinkTailCondition : Prop :=
  ∀ n (h : 2 * n = D.R.m) t φ (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
    (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ G : (f.t t).CT, G.1 = _root_.GlobalTheory.Fam.leadingLinearMap W t F' →
    (f.t t).tail (2 * n) h ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t φ)) G =
      D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))
def LinkDescends : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m) t (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL),
    ∃ G : (f.t t).CT, G.1 = _root_.GlobalTheory.Fam.leadingLinearMap W t F' ∧ _root_.GlobalTheory.MiTop.descentToLevelZero f n h t G = _root_.GlobalTheory.MiTop.rowFormOfTuple W t F'
def LinkSurjective : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m), ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∃ G : (f.t W.P.A3.A.μ0).CT, _root_.GlobalTheory.MiTop.descentToLevelZero f n h W.P.A3.A.μ0 G = T
def LinkCommutes : Prop :=
  ∀ n (h : 2 * n = D.R.m), ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (s : ℂ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧ s ≠ 0 ∧
    ∀ t φ F, (f.t t).tail (2 * n) h ((f.t t).up n (_root_.GlobalTheory.MiTop.col0_alt f t φ)) F =
      s * (f.t t).tail (2 * n) h ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t (S φ))) F
variable (W)
def CoveredCondition : Prop :=
  ∀ w (p : ℕ), p.Prime → (∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q (W.Q.Rl.mu w), ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (p : 𝓞 D.what₂.LL) ∉ w.asIdeal
open _root_.Formalism.L2.Host in
theorem served' : _root_.GlobalTheory.MiTop.CoveredCondition W := by
  rintro w p hp ⟨PP, hP, h1⟩ h2
  have lev := W.Q.charW.base.lev
  have hr : ¬ (W.Q.Rl.xiH (W.Q.Rl.mu w)).UnrAt PP := (lev.Q_ram _ PP).2 (Or.inl hP)
  have hl : Formalism.EigenvalueLevelCeiling.plc w = p :=
    (Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hp).1
      ((ringChar.spec _ p).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2))
  by_cases hw : w ∈ W.Q.Rl.twPl
  · obtain ⟨ψ, Q, hψ, e⟩ := W.Q.charW.tup.mu_on w hw
    have e' : W.Q.Rl.xiH (W.Q.Rl.mu w) = W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    have key : ∀ q : ℕ, q.Prime → OverP D.host q PP → q = p := fun q hq ho => by
      by_contra hne
      have hc : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((p : ℕ) : 𝓞 D.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
      obtain ⟨a, b, hab⟩ := hc
      have ho' : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := ho
      exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ ho') (PP.asIdeal.mul_mem_left _ h1)))
    have hd : (W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP := by
      unfold CharFrame.delAt
      split_ifs with hh
      · refine W.Q.Rl.C.isDel'.unr PP fun ho => D.host.pde_ne ?_
        rw [← hh, hl, key _ D.host.pde'_prime ho]
      · exact W.Q.Rl.C.isDel.unr PP fun ho => hh (by rw [hl, key _ D.host.pde_prime ho])
    refine hr fun x hx => ?_
    have a1 := hd x hx
    have a2 := hψ.atl PP (hl ▸ h1) x
    rw [e']
    change (W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1
    rw [a1, a2, mul_one]
  · have e : W.Q.Rl.mu w = W.P.A3.A.μ0 := W.Q.charW.tup.mu_off w hw
    refine hr fun x _ => ?_
    rw [e, show W.Q.Rl.xiH W.P.A3.A.μ0 = 1 from lev.xi_base]
    rfl
theorem not_mem_Q_base' (PP : HeightOneSpectrum (𝓞 D.host.E)) : PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 := by
  intro hP
  have lev := W.Q.charW.base.lev
  refine (lev.Q_ram _ PP).2 (Or.inl hP) fun x _ => ?_
  rw [show W.Q.Rl.xiH W.P.A3.A.μ0 = 1 from lev.xi_base]
  rfl
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamCol
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.MiS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdForm
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
def TwStdAlt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  ∃ (l0 : I.Law0 l) (t : SymmetricTwistedColumnsAtPrimes W.R.T.n.tp W.R.T.cols (I.tw l l0 Z)),
    ex.tw = I.tw l l0 Z ∧ HEq W.R.T.tw t ∧ I.StdTw l Z l0 t
def FamilyColumnCondition {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : (I.rec7 l Z).what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) : Prop :=
  ∃ c₀, PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ f.g.x f.g.vac c₀ ∧ ∀ t : W.P.T,
    (∃ (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) (ι : ∀ j, (f.col t).Ch j → Ch₀ j) (w : _),
      PinChL (_root_.GlobalTheory.Fam.pk_z W) f.g (f.col t) c₀ A ι w) ∧
    ∃ UT ε, PinTopL (_root_.GlobalTheory.Fam.pk_z W) f.g (_root_.GlobalTheory.Fam.complexLevelStructure W) (t := t) (f.col t) UT ε
end GlobalTheory.AdForm
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.BigOn.Exp.TupLe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def AllPtsAlt (Q : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}, PtAt ex Csz → Fin D.R.m → Prop) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts)
    (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz) (j : Fin D.R.m), p.PointConditions' → More p → Q p j
open Classical in
def PlacesCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ ex _} p j => ∀ w : D.what₂.places.Pl, D.plEq w ∈ p.R.twPl →
  IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w) →
  ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ →
  ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w) →
  p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
    (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi →
  SplitSet (p.R.Q (p.R.mu (D.plEq w))) ∧
    (∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) ∧
    idem (p.R.Q (p.R.mu (D.plEq w))) + cA D (idem (p.R.Q (p.R.mu (D.plEq w)))) =
      idem ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
          (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q) +
        cA D (idem ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
          (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q))
open Classical in
def FlatCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)) (ψ : Twist D Circle) (t : p.P.T),
  B.Good → BaseOf (R2 p) j B → ψ.Good → B.admitted ψ.Q → (R2 p).xi t = B.de.chi * ψ.chi →
  idem ((R2 p).Q t) + cA D (idem ((R2 p).Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) →
  ∃ (z : GA D (Vc D j)) (c : ℂ), SuppAt (idem ((R2 p).Q t)) (Vc D j) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime (R2 p) t) c ∧
    (princ B).vecFlat ψ = c • (R2 p).ωP j t (z⁻¹, 1) ((R2 p).vP j t)
def TraceCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (ρ : Setup D.ntw), ρ.Good → RealPin p.R p.cG ρ → ρ.LevelOf D.nexp →
  ∀ (i : D.ntw.Tw) (b : Bool) (ψ : Twist D Circle) (ω : PairRep (Vc D j) (Wc D j)), ψ.Good → (ρ.B i j b).admitted ψ.Q →
    (ρ.B i j b).IsWeil ψ.chi ω → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (series (ρ.B i j b).F ω ((princ (ρ.B i j b)).vecFlat ψ) h P) =
        series (ρ.B i j b).F ω ((ρ.B i j b).vecFlat ψ) h P
def CoefficientCondition' : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf (R2 p) j B →
  ∀ c : ℂ, c ≠ 0 → IsScale p.R p.v₀ B c → ∀ u : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ,
    (∀ τ, (u τ : ((R2 p).MW j (sg0 D p.P.A3.A)).sm τ) = p.v₀ j _ τ) → ∀ O' : Subring ℂ, IsCoefRing D.what₂.embLL (labLL D) O' →
    ∀ h ∈ GfC (Vc D j), ∀ v, InCoefLat (R2 p) j h v →
      ∃ P ∈ B.coefLat D.what₂.embLL (labLL D) O' (finPt (Vc D j) h), (R2 p).ioP j (PiTensorProduct.tprod ℂ u) v = c • P
def SmallnessCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf (R2 p) j B →
  ∀ O O' : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → IsCoefRing D.what₂.embLL (labLL D) O' →
    ∀ (h : GA D (Vc D j)), ∀ P ∈ B.coefLat D.what₂.embLL (labLL D) O' (finPt (Vc D j) h),
      P ∈ Submodule.span O' (B.coefLat (embLL0 D) (labLL0 D) O (finPt (Vc D j) h) : Set (PolF D (Wc D j).rank (Vc D j).rank))
section Units
variable {O K : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]
end Units
section Read
variable {D : D7} {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)
  {L : Type} [Field L] [Algebra (D.ntw.O i) L] (e : L →+* ℂ) (he : ∀ c : D.ntw.O i, e (algebraMap _ L c) = ρ.eO i b c)
end Read
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
variable {p w j}
end Point
section Move
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
include hρ
end Move
section Assembly
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}
theorem realTw_le_alt (s1 : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition) (s2 : _root_.GlobalTheory.BigOn.Exp.TupLe.FlatCondition) (s3 : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition) (s4 : _root_.GlobalTheory.BigOn.Exp.TupLe.CoefficientCondition') (s5 : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition) (hr : p.PointConditions') (hm : More p)
    (hL : Links2 p) (hw : D.plEq w ∈ p.R.twPl)
    (hok : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin p.R p.cG ρ) (hlev : ρ.LevelOf D.nexp)
    (hB0 : BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)))
    (e : FractionRing (ex.nch.Oe w) →+* ℂ) (h1 : ∀ x, e (ex.nch.embW w x) = D.what₂.embLL x)
    (h2 : ∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
      e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a)
    (c1 : ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w))
    (c2 : p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi)
    {ν : ℂ} (hν : IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν) (hR : RatAt p w j hρ ν) {rd : Can p w j} (hc : IsCan p rd) :
    realTw p rd ≤ twLat p w j hρ ν := by
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hK := GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.isKsForm_of_iso (p.nexp.fi j) (p.fw.ks j)
  obtain ⟨Z⟩ := hm.2.2.series
  have hF : Faithful (rdAt p w j hρ ν) := realRd_faithful _ _ _ _ _ _ _ _ _ _ p.nexp p.v₀ ρ hρ _ j _ ν hν.1 hL.2.2.1
    p.charW.base.models.HW (Z.vec j) hK
  obtain ⟨p1, p2, p3⟩ := s1 _ _ _ _ _ _ _ _ _ _ p j hr hm w hw hok ρ hρ hpin c1 c2
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  have hB := hρ.base (ex.nch.twI w) j (ex.nch.sd w)
  obtain ⟨z, cz, hz, hcz, hfl⟩ := s2 _ _ _ _ _ _ _ _ _ _ p j hr hm _ _ ((R2 p).mu (D.plEq w)) hB hB0 ht hadm c2 p3
  have hzf : z ∈ GfC (Vc D j) := GlobalTheory.TwTraceCx.mem_GfC_of_suppAt p1 hz
  have hω : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).IsWeil
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi
      ((R2 p).ωP j ((R2 p).mu (D.plEq w))) := by
    have e0 : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).mu *
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi =
        (R2 p).toLevCh.mu ((R2 p).mu (D.plEq w)) ((j : ℕ) + 1) := by
      rw [Base.mu, hB0.mu0, mul_assoc, ← c2]
      rfl
    rw [Base.IsWeil, e0, hB0.ψ, hB0.eta]
    exact hC.thP.ωP j _
  have hN : IsUnit ((GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w)) : ℕ) : ex.nch.Oe w) := by
    have hcop : Nat.Coprime (D.ntw.l (ex.nch.twI w)) (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
      have := GlobalTheory.NormUnit.coprime_absNorm _ (D.ntw.lPrime _).out P (p2 P hP)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    simpa using (GlobalTheory.NormUnit.isUnit_natCast_of_coprime (D.ntw.O_l _) hcop).map (algebraMap _ (ex.nch.Oe w))
  have hO' : IsCoefRing D.what₂.embLL (labLL D) (imO ex.nch w e) := by
    refine ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => ?_⟩
    obtain ⟨b, hb⟩ := mem_of_ringOfIntegers (O := ex.nch.Oe w) (ex.nch.embW w) a
    exact ⟨b, by rw [RingHom.comp_apply, hb, h1]⟩
  obtain ⟨ν0, c, hs, n, hn, hνc⟩ := hν
  rw [p.phsOne j, map_one, one_mul] at hνc
  have c0 : c ≠ 0 := fun h => ν0 (by rw [h, zero_pow hn] at hνc; exact pow_eq_zero_iff hn |>.1 hνc)
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hs
  refine le_of_comb hρ hc hR hF hK e h1 h2 hN ?_
  rintro x ⟨h, hh, v, hv, hx⟩
  obtain ⟨P, hP, hio⟩ := s4 _ _ _ _ _ _ _ _ _ _ p j hr hm _ hB hB0 c c0 hs u hu _ hO' h hh v hv
  have hP' := s5 _ _ _ _ _ _ _ _ _ _ p j hr hm _ hB hB0 _ _ (hρ.isCoefRing (ex.nch.twI w) (ex.nch.sd w)) hO' h P hP
  have hhz : h * z ∈ GfC (Vc D j) := mul_mem hh hzf
  refine ⟨ν⁻¹ * c * cz⁻¹, unitOff_mul (unitOff_root hn ?_) (unitOff_inv hcz),
    series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
      ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).vecFlat
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))) (h * z) P, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hνc, inv_mul_cancel₀ (pow_ne_zero _ c0)]
  · clear hP hio
    induction hP' using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨s, h', P', hd, g, hg, a, ea⟩ := series_eq_gen hρ _ j _ hok hω hhz (lat_translate_of_prime hρ _ j _ p1 p2 hz hQ)
      rw [ea]
      exact Submodule.smul_mem _ (⟨_, ⟨algebraMap _ _ a, h2 a⟩⟩ : imO ex.nch w e) (Submodule.subset_span ⟨s, h', P', hd, hg⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ a b => rw [map_add]; exact add_mem a b
    | smul a y _ hy =>
      rw [show a • y = (a : ℂ) • y from rfl, map_smul]
      exact Submodule.smul_mem _ a hy
  · have e1 : adForm (R2 p) j x (p.v₀ j _) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
        (ser (R2 p) j ((R2 p).mu (D.plEq w)) ((R2 p).vP j ((R2 p).mu (D.plEq w))) u h v) :=
      ((congrArg (adForm (R2 p) j x) (funext hu)).symm.trans (hx u)).trans (one_smul _ _)
    have e2 : ser (R2 p) j ((R2 p).mu (D.plEq w)) ((R2 p).vP j ((R2 p).mu (D.plEq w))) u h v = (c * cz⁻¹) •
        series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
          ((princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecFlat
            (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))) (h * z) P := by
      rw [mul_comm, mul_smul, ← map_smul, ← hio]
      refine Eq.trans ?_ (congrArg (cz⁻¹ • ·) (hB0.series_eq_ser _ _ u (h * z) v)).symm
      rw [hfl]
      funext g
      have e3 := GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class _ _ _ _ _ _ (R2 p) _ hC j ((R2 p).mu (D.plEq w)) z⁻¹ cz (inv_mem hzf) u (h * z) v g
      rw [mul_inv_cancel_right] at e3
      refine Eq.trans ?_ (congrArg (cz⁻¹ * ·) e3).symm
      exact (inv_mul_cancel_left₀ hcz.1 _).symm
    rw [e1, e2, map_smul, s3 _ _ _ _ _ _ _ _ _ _ p j hr hm ρ hρ hpin hlev _ _ _ _ ht hadm hω, smul_smul, mul_assoc]
end Assembly
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InGeoGeoHalf
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InGeoGeoHalf
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option autoImplicit false
noncomputable section
theorem GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x)
    (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p → ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m),
    RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j → InGeo (geoHalf p) := by
  intro hDec eps Fm x hx i p hR _hM t j h0
  have hJ : JEvExists p.T p.R.toRealDat p.κ p.v₀ :=
    GlobalTheory.ConjReading.jEvExists p.T p.R.toRealDat p.κ p.v₀ p.O h0.core.lev h0.core.models p.fw p.pins
  exact
    { jEvExists := hJ
      jEvBar := hR.jEvBar
      evInj := hR.evInj
      jUnif := GlobalTheory.ReadingSpan.jUnif hDec _ _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ h0.core.lev h0.core.models h0.tieIn
        hR.ties.pb hJ hR.jEvBar hR.evInj h0.size
      geoAct := hR.geoAct
      latFull := GlobalTheory.IntCuspLat.latFull_of_tie p.fw
      dimMatch := p.fw.dimMatch }
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InGeoGeoHalfStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inGeo_half_of_ratHyp0 : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p → ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m), RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j → InGeo (geoHalf p) := by
  first | exact @_root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 | exact _root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 | (intros; apply _root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 <;> assumption)
end
end
end
