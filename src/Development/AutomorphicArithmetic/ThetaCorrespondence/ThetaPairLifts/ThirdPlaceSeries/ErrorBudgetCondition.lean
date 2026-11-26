module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFromPageEstimate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.CovHt
section Steps
open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i)
end Steps
def ShortAlt : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → ShortAt p i Y PP C u1
def GeometricCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → GeomAt p i Y u1
def MultiplicityConstantCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → MultAt p i Y PP C u1
def ErrorBudgetCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → BudgetAt p i Y PP C u1
end GlobalTheory.CovHt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFrames
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFrames
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem sdY_frames_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) :
    _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j < D.R.m → IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ∧ Formalism.L2.DIV.IsFrame ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) := by
  intro h j hj
  have hL := h.bot.hyp.2.2.2.1.lev.βY j hj
  refine ⟨GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL, ?_⟩
  obtain ⟨c, hc⟩ := hL
  exact hc.1
end GlobalTheory.Fam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFramesStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_and_frame_of_pkHyp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j < D.R.m → IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ∧ Formalism.L2.DIV.IsFrame ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) := by
  first | exact @_root_.GlobalTheory.Fam.sdY_frames_alt | exact _root_.GlobalTheory.Fam.sdY_frames_alt | (intros; apply _root_.GlobalTheory.Fam.sdY_frames_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GServT
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.L2.G.ServT
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2
structure SelectionServed (𝒞 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒞) : Prop where
  twU : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ LC, WeilJacquetShalikaLaw.CmpV (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw (reW (Fm.Gy x i) LC) ∧ SysTw (Fm.D x i) (Fm.L x i)
      (Fm.Gx x i) Fm.GK (Fm.X x i) (reW (Fm.Gy x i) LC) (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err 1
  pdv : Closed 𝒞 fun Fm _ => ∀ (hc : 𝒞 Fm) (x : ℝ) (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    ((((sel Fm hc).2 x hx h0 i).T.ker.ent.UnUnit ∧ OrbitPlaces.KmapRat ((sel Fm hc).2 x hx h0 i).T.ker.ent ∧
        OrbitPlaces.KFi (Fm.D x i) (Fm.ex x hx i).tw ∧ OrbitPlaces.Stab0 (Fm.D x i)) ∧
      ∃ (ep : _) (be : _) (sg : _),
        OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.Gx x i) Fm.GK ∧
        OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i)
          (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg))
theorem sumOverPrimesService_of_servT {𝒞 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒞) (h : _root_.Formalism.L2.G.ServT.SelectionServed 𝒞 sel) : SumOverPrimesHypotheses 𝒞 := by
  refine ⟨h.twU, closed_imp_class h.pdv ?_⟩
  intro eps Fm CH hc hp
  refine ⟨(sel Fm hc).1, ?_⟩
  intro x hx0 hx i
  exact ⟨((sel Fm hc).2 x hx hx0 i).T.ker.ent, hp hc x hx hx0 i⟩
theorem closed_servF_of_servT_of_dGamSize {𝒞 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒞) (hD : Closed 𝒞 fun Fm _ => DGamSize Fm) (h : _root_.Formalism.L2.G.ServT.SelectionServed 𝒞 sel) :
    Closed 𝒞 fun Fm _ => WeilJacquetShalikaLaw.ServF Fm :=
  sum_over_primes_service 𝒞 hD (_root_.Formalism.L2.G.ServT.sumOverPrimesService_of_servT sel h)
end Formalism.L2.G.ServT
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtremalVectorsSplitPart
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
end Gen
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
theorem ioExt_R2 (h : p.PointConditions') : IoExt (R2 p) := h.ioExt
theorem one_map_R2 (h : p.PointConditions') (i : Fin D.R.m) : OneMapRowR p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i := by
  have := oneMapRowR_charOf (κ := p.κ) (v₀ := p.v₀) p.O (F2 p) (phEff p.R) i (h.oneMap i)
  rw [phEff_eq_one] at this
  exact this
theorem twistedRational_R2_F2 (h : p.PointConditions') (hm : More p) : GlobalTheory.RealIndexBound.TwistedRational (R2 p) (F2 p) fun _ => 1 := by
  have hL : Links2 p := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p h hm.1
  exact GlobalTheory.T.twistedClassSums_rational_of_rayClassFields D _ _ _ _ p.T (R2 p) (F2 p) p.κ p.v₀ (fw2 p) (om2 p) hL.1 (_root_.GlobalTheory.BigOn.ioExt_R2 p h) hL.2.2.1
    hL.2.2.2.2.2.2.1 (splitPartRealisation_satisfies_qGuard p) (_root_.GlobalTheory.BigOn.one_map_R2 p h) hL.2.2.2.1 hL.2.2.2.2.1 hm.2.2.rayQ
end Point
theorem bigOn_ratSt : _root_.GlobalTheory.BigOn.RationalityStatement' :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ _ _ p h hm => _root_.GlobalTheory.BigOn.twistedRational_R2_F2 p h hm⟩⟩⟩
end GlobalTheory.BigOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoversOfLifts
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.CovSz
theorem covers_and_alt
    {Q Q' : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP)
    (h' : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => Q' Fm x hx ι p i Y PP) :
    _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP ∧ Q' Fm x hx ι p i Y PP := by
  refine (Formalism.MainNotions.Closed.and h h').imp fun Fm CH _ hh => ?_
  obtain ⟨⟨C, hC, a, ha⟩, ⟨C', hC', b, hb⟩⟩ := hh
  exact ⟨C, hC, max a b, fun x hx hle ι p hp i hi Y hY =>
    ⟨ha x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY, hb x hx ((le_max_right _ _).trans hle) ι p hp i hi Y hY⟩⟩
theorem covers_of_lifts_alt
    {P : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (PP C : ℝ), Prop}
    {Q : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : _root_.GlobalTheory.CovTop.LiftsCondition P)
    (hQ : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (C : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → P Fm x hx ι p i (Fm.parT x hx ι).PP C → (i : ℕ) + 1 < (Fm.D x ι).R.m →
      ∀ Y : Cov p i, GoodCov p i Y → Q Fm x hx ι p i Y (Fm.parT x hx ι).PP) :
    _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP := by
  refine h.imp fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY => hQ Fm x hx ι p i C hp (ha x hx hle ι p hp i) hi Y hY⟩
theorem covers_of_covers_of_imp
    {Q R : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP)
    (hQ : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (PP : ℝ), Q Fm x hx ι p i Y PP → R Fm x hx ι p i Y PP) :
    _root_.GlobalTheory.CovTop.CoversCondition fun Fm x hx ι p i Y PP _ => R Fm x hx ι p i Y PP := by
  refine h.imp fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY => hQ Fm x hx ι p i Y _ (ha x hx hle ι p hp i hi Y hY)⟩
end GlobalTheory.CovTop.CovSz
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkPlaces
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkPlaces
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PkPlaces
theorem pk_places_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (∃ e : AE D, IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg ∪ ∅)) ∧ ∀ t, Disjoint (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) ∧ (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) ∧ (∃ e : AE D, IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t)) ∧ ∃ e : AE D, IsIdemSum e (∅ ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW
  have hl : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  have hQQ : ∀ t, ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ¬ Lev.IsConjPl PP PP' :=
    fun t PP h PP' h' => ((hl.Q_pl t) PP h).2 PP' h'
  have hnc : ∀ t, ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t, ¬ Lev.IsConjPl PP PP' := by
    intro t PP h PP' h' hc
    have ha := (GlobalTheory.StepLifts.places_apart _ hl t).1
    rcases Finset.mem_union.1 h with h | h
    · exact ha PP h PP' (Finset.mem_union.1 h') hc
    · rcases Finset.mem_union.1 h' with h' | h'
      · refine ha PP' h' PP (Or.inr h) ?_
        rw [GlobalTheory.GoodPrimes.isConjPl_iff] at hc ⊢
        rw [hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
      · exact hQQ t PP h PP' h' hc
  refine ⟨?_, fun t => ⟨(GlobalTheory.StepLifts.places_apart _ hl t).2, ?_, ?_, ?_⟩⟩
  · rw [Finset.union_empty]
    exact GlobalTheory.CentralShift.exists_idemSum _ fun PP h PP' h' =>
      (GlobalTheory.StepLifts.places_apart _ hl W.P.A3.A.μ0).1 PP h PP' (Or.inl h')
  · intro PP h PP' h' e
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact Finset.disjoint_left.1 (GlobalTheory.StepLifts.places_apart _ hl t).2 h (e' ▸ h')
    · exact (GlobalTheory.StepLifts.places_apart _ hl t).1 PP h PP' (Or.inr h') (GlobalTheory.GoodPrimes.isConjPl_iff.2 e')
  · exact GlobalTheory.CentralShift.exists_idemSum _ (hnc t)
  · rw [Finset.empty_union]
    exact GlobalTheory.CentralShift.exists_idemSum _ (hQQ t)
end GlobalTheory.PkPlaces
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkPlacesStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_places_disjoint_idempotents_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (∃ e : AE D, IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg ∪ ∅)) ∧ ∀ t, Disjoint (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) ∧ (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) ∧ (∃ e : AE D, IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t)) ∧ ∃ e : AE D, IsIdemSum e (∅ ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t) := by
  first | exact @_root_.GlobalTheory.PkPlaces.pk_places_alt | exact _root_.GlobalTheory.PkPlaces.pk_places_alt | (intros; apply _root_.GlobalTheory.PkPlaces.pk_places_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Sizes
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Sizes
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum.SizeTZ
section Free
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
end Free
variable {D : D7}
variable {L : SizeData₂ D} {P : ParameterChoice' D L}
theorem parameters_scale_rank_gap_bounds : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (lenT p i PP : ℝ) * zBase (Fm.L x ι) ^ 12 ≤ unitE p ∧ 1 ≤ (Fm.L x ι).sc.L ∧ lrd (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ (nCol (dat p i) : ℝ) ≤ 20 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ^ 2 ∧ 1 ≤ (Fm.D x ι).R.f ∧ 1 ≤ (Fm.D x ι).R.r := fun h =>
  Closed.imp h fun Fm _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i =>
    ⟨(lenT_mul_le_b p i (Fm.parT x hx ι)).1.trans (h x hx hle ι p hp i).2.1, one_le_scL _, lrd_le (Fm.params x hx ι),
      (lenT_mul_le_b p i (Fm.parT x hx ι)).2,
      le_trans one_le_two (two_le_f _), le_trans (by norm_num) (six_le_r _)⟩⟩
end GlobalTheory.RefSum.SizeTZ
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lenT_zBase_unitE_nCol_bounds : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (lenT p i PP : ℝ) * zBase (Fm.L x ι) ^ 12 ≤ unitE p ∧ 1 ≤ (Fm.L x ι).sc.L ∧ lrd (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ (nCol (dat p i) : ℝ) ≤ 20 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ^ 2 ∧ 1 ≤ (Fm.D x ι).R.f ∧ 1 ≤ (Fm.D x ι).R.r := by
  first | exact @_root_.GlobalTheory.RefSum.SizeTZ.parameters_scale_rank_gap_bounds | exact _root_.GlobalTheory.RefSum.SizeTZ.parameters_scale_rank_gap_bounds | (intros; apply _root_.GlobalTheory.RefSum.SizeTZ.parameters_scale_rank_gap_bounds <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistStOf
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.TwistBoundAtPlace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
theorem twistSt_of_alt (hE : _root_.GlobalTheory.BigOn.ExportedStatement) (hG : _root_.GlobalTheory.BigOn.GeometricStatement')
    (hK : _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) : _root_.GlobalTheory.BigOn.TwistStatement' := by
  obtain ⟨a, ha, H⟩ := (hE.and hG).and hK
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK'⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, E1⟩, ⟨c1, G1⟩⟩, ⟨c2, K1⟩⟩ := hK' Fm CH hc hL
  obtain ⟨x0, T0⟩ := hc.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max c1 c2, fun c hcC hb => ?_⟩
  obtain ⟨x2, G2⟩ := G1 c ((le_max_left _ _).trans hcC) hb
  obtain ⟨x3, K2⟩ := K1 c ((le_max_right _ _).trans hcC) hb
  refine ⟨max (max x0 x1) (max x2 x3), fun x hx hle i p hp hM r O hR => ?_⟩
  have h0 : x0 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have h1 : x1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  obtain ⟨-, N0, S, hTG⟩ := T0 x h0 hx i
  exact hasTwistBound_at p hR (E1 x hx h1 i p hp hM) (G2 x hx h2 i p hp hM r O hR).1 (K2 x hx h3 i p hp hM r O hR) hTG
end GlobalTheory.BigOn.TwistBoundAtPlace
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoStOfPageSt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn
section Comparison₂
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Comparison₂
theorem geoSt_of_pageSt_alt : _root_.GlobalTheory.BigOn.PageStatement → _root_.GlobalTheory.BigOn.GeometricStatement' := by
  intro hP
  obtain ⟨CK, xa, HR⟩ := runsHold_of_ties
  obtain ⟨xb, HL⟩ := leaves_sup_span_data CK
  obtain ⟨Cd, HD⟩ := leafDepth_all_record
  refine ((hP.and (GlobalTheory.T.runNumericalConditions_hold_along_family xa)).and (GlobalTheory.T.runNumericalConditions_hold_along_family xb)).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨c0, hc0⟩, ⟨ya, hya⟩⟩, ⟨yb, hyb⟩⟩ := H
  refine ⟨max c0 Cd, fun c hc hbad => ?_⟩
  obtain ⟨x0, hx0⟩ := hc0 c ((le_max_left _ _).trans hc) hbad
  refine ⟨max x0 (max ya yb), fun x hx hle i p hrows hmore r O hrec => ?_⟩
  have h0 : x0 ≤ x := (le_max_left _ _).trans hle
  have ha : ya ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have hb : yb ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨hPg, hSz, -, -, -, -, hOb, -, -⟩ := hx0 x hx h0 i p hrows hmore r O hrec
  obtain ⟨pna, hx3, hkb, hxe, -⟩ := hya x hx ha i
  obtain ⟨pnb, -, -, -, -⟩ := hyb x hx hb i
  have hcore := hmore.2.1
  have hown := hrec.2
  have hch := (_root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hrows hmore.1).1
  have hRH := HR _ _ _ _ _ _ _ (F2 p) _ _ _ _ _ _ (Fm.ex x hx i).kap_def _ _ hcore hrec.1.ok hown pna
  obtain ⟨hSup, hSpan, hS, hData⟩ := HL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 hcore hown pnb hRH hch.grp
    hch.tup.mu_conj hch.tup.mu_off hch.tup.mu_ne
  refine ⟨hSup, hSpan, hS, hData, hasIndexBound_of_runs CK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 hcore hown hRH hSup hSpan
    hOb, fun C CH' => ?_⟩
  exact HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 _ hPg hSz hx3 hkb (indefinitePoint_splitPartContent_eq_forcedContent p C CH')
    ((le_max_right _ _).trans hc) (le_of_eq pna.2.1.symm) hxe
end GlobalTheory.BigOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceSt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceSt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TraceFlatLevel
open GlobalTheory.TraceLevelPf
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end GlobalTheory.TraceFlatLevel
namespace GlobalTheory.BigOn.Exp.TupLe
theorem traceSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm ρ hρ hpin hlev i b ψ ω hψ hQ hω h P
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B i j b) := { baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin i j b with }
  refine GlobalTheory.TraceFlatLevel.traceLevel_flat (R2 p) j (ρ.B i j b) (hρ.base i j b) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG i j b)) (fun g P h h' a c => ?_) (fun g => mem_level_iff hm.2.2 hlev i j b g)
    (fun u hu => ?_) ψ hψ hQ ω hω h P
  · have e1 := hpin.grp i j b (p.cG (p.R.eG g)) P h h' a c
    rw [MulEquiv.symm_apply_apply] at e1
    exact e1
  · refine (level_chi hm.2.2 hρ hlev i j b u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceStStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupLe_traceSt : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.traceSt_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.traceSt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.traceSt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QBaseEmpty
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QBaseEmpty
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
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem cH_ne_zero_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ 0 := by
  unfold _root_.GlobalTheory.BaseChain.inverseLevelCardinality
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
theorem inverse_level_cardinality_ne_infinity (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ ⊤ := by
  unfold _root_.GlobalTheory.BaseChain.inverseLevelCardinality
  have hpos : 0 < Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H := Nat.card_pos
  exact ENNReal.inv_ne_top.2 (by exact_mod_cast hpos.ne')
theorem Q_base_eq_empty (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 = ∅ :=
  Finset.eq_empty_of_forall_notMem (_root_.GlobalTheory.MiTop.not_mem_Q_base' (W := W))
theorem stageX_is_at_m (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (_ : _root_.GlobalTheory.Fam.PackageHypotheses W) : (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Is (_root_.GlobalTheory.BaseChain.com_z W) D.R.m := by
  have lev := W.Q.charW.base.lev
  have hM := (W.Q.charW.base.models.νX W.P.A3.A.μ0)
  obtain ⟨c, hc⟩ := lev.βX
  refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_, rfl, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1,
    ⟨_, hc, fun P _ hN => ?_⟩, ⟨r_le_X, (_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, ?_⟩, ?_, ?_⟩
  · show D.sp.X'.sig τ = _
    rw [D.X'_posDef τ, D.sp.X'_rank]; simp [sigYD, Ranks.rankY, Ranks.rankX']
  · rw [one_pow, Nat.cast_one] at hN
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hN)
  · show Lev.datY _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) _ _ _ _ = _
    rw [_root_.GlobalTheory.BaseChain.Q_base_eq_empty W]; rfl
  · exact @MeasureTheory.Measure.IsHaarMeasure.smul _ _ _ _ _ hM.1.1 _ _ (_root_.GlobalTheory.BaseChain.cH_ne_zero_alt W) (_root_.GlobalTheory.BaseChain.inverse_level_cardinality_ne_infinity W)
  · exact hM.2.mono (MeasureTheory.Measure.smul_absolutelyContinuous)
end GlobalTheory.BaseChain
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QBaseEmptyStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChain_stageX_is_of_pkHyp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Is (_root_.GlobalTheory.BaseChain.com_z W) D.R.m := by
  first | exact @_root_.GlobalTheory.BaseChain.stageX_is_at_m | exact _root_.GlobalTheory.BaseChain.stageX_is_at_m | (intros; apply _root_.GlobalTheory.BaseChain.stageX_is_at_m <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoPath
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn.OntoPath
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem onto_path_alt : _root_.GlobalTheory.BigOn.TwoRunsStatement → _root_.GlobalTheory.BigOn.RationalityStatement' → _root_.GlobalTheory.BigOn.GeometricStatement' → (_root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) → _root_.GlobalTheory.BigOn.TwistStatement' →
    _root_.GlobalTheory.BigOn.ShareStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement → _root_.GlobalTheory.BigOn.ExponentStatement → _root_.GlobalTheory.BigOn.PageStatement → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  intro hRuns hRat hGeo hRank hTw hSh hBad hExp hPage
  have H := ((((((((hRuns.and hRat).and hGeo).and hRank).and hTw).and hSh).and hBad).and hExp).and hPage)
  refine Closed.imp H ?_
  intro eps Fm CH _ H _
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨xR, hR⟩, ⟨xQ, hQ⟩⟩, ⟨cG, hG⟩⟩, ⟨cK, hK⟩⟩, ⟨cT, hT⟩⟩, ⟨cS, hS⟩⟩, ⟨cB, hB⟩⟩, ⟨cE, hE⟩⟩, ⟨cP, hP⟩⟩ := H
  set c0 : ℝ := max (max (max (max cG cK) (max cT cS)) (max (max cB cE) cP)) 1 with hc0
  let c : OnConst := ⟨c0, 14, 66 * c0 + 4⟩
  have hcb : OnPage.ConstBad c := ⟨le_rfl, le_rfl⟩
  have l1 : cG ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l2 : cK ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l3 : cT ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l4 : cS ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l5 : cB ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l6 : cE ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l7 : cP ≤ c.C := le_trans (by simp) (le_max_left _ _)
  obtain ⟨x1, h1⟩ := hG c l1 hcb
  obtain ⟨x2, h2⟩ := hK c l2 hcb
  obtain ⟨x3, h3⟩ := hT c l3 hcb
  obtain ⟨x4, h4⟩ := hS c l4 hcb
  obtain ⟨x5, h5⟩ := hB c l5 hcb
  obtain ⟨x6, h6⟩ := hE c l6 hcb
  obtain ⟨x7, h7⟩ := hP c l7 hcb
  refine ⟨2 * max c.CE 0, by positivity,
    max (max (max xR xQ) (max x1 x2)) (max (max x3 x4) (max (max x5 x6) x7)), ?_⟩
  intro x hx hx0 i p hp hm C hCC
  have a0 : max xR xQ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx0)
  have b0 : max x1 x2 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx0)
  have c1 : max x3 x4 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx0)
  have d0 : max (max x5 x6) x7 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx0)
  obtain ⟨r, hr, hown⟩ := hR x hx (le_trans (le_max_left _ _) a0) i p hp hm
  have hrat := hQ x hx (le_trans (le_max_right _ _) a0) i p hp hm
  have hct := hm.2.1
  obtain ⟨O, hO⟩ := exists_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ (Fm.parT x hx i) (Fm.ex x hx i).kap_def
    (Fm.ex x hx i).errX r c hct.canon hct.halfEX hr
  have hrec : RecAt p (Fm.parT x hx i) r O := ⟨hO, hown⟩
  obtain ⟨gSup, gSpan, gLem, gData, gIdx, gDepth⟩ := h1 x hx (le_trans (le_max_left _ _) b0) i p hp hm r O hrec
  have kRank := h2 x hx (le_trans (le_max_right _ _) b0) i p hp hm r O hrec
  have tTw := h3 x hx (le_trans (le_max_left _ _) c1) i p hp hm r O hrec
  have sSh := h4 x hx (le_trans (le_max_right _ _) c1) i p hp hm r O hrec
  have bBad := h5 x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  have eExp := h6 x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  obtain ⟨pPage, pSizes, pX, pBad, pLev, pY, -, pE1u, pTie⟩ :=
    h7 x hx (le_trans (le_max_right _ _) d0) i p hp hm r O hrec
  have hL : Links2 p := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hm.1
  obtain ⟨hC, hOk, hU, hBL, hRR, -⟩ := hL
  have hI := GlobalTheory.ClassSumIdentity.leafIdentity_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hrat
  have hT2 := GlobalTheory.BaseTwistIncl.leafTW2_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hBL hrat
  obtain ⟨dG, dR, d2, dL⟩ := gDepth c.CE CH
  obtain ⟨err, herr⟩ := GlobalTheory.T.twistedPlacesBoundChain_twoRunChain _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1
    ((R2 p).num (F2 p) c.CE CH) c.CE hOk hC.grp.levels hC.grp.chiW hC.models hC.tup.mu_conj hC.thP.thG hU hBL hrat hRR
    pLev pY gSup gSpan gLem gIdx gData kRank hI hT2 tTw sSh bBad dG dR d2 dL pPage pSizes pX pBad (eExp c.CE CH) le_rfl
    (pTie c.CE CH)
  obtain ⟨hon, hD⟩ := GlobalTheory.T.onClauses_with_error_of_splitPart _ _ _ _ _ _ _ _ _ _ p c.CE CH err herr
  have hDpos : 0 < (p.S false).D := by rw [hD]; exact hRR.1
  have hJ : ∀ w ∈ (p.S false).Tw, ∀ j, 0 ≤ p.Z.J0 ((p.S false).μ w) w j := (eExp C CH).1
  exact on_of_onWith_canonical _ _ _ (p.S false) p.Z c.CE C CH CH err hDpos pE1u
    (le_trans (mul_le_mul_of_nonneg_left (le_max_left c.CE 0) zero_le_two) hCC) hJ (fun w j => p.err_eq w j) hon
end GlobalTheory.BigOn.OntoPath
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesSt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesSt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TupLe
variable {D : D7}
open Classical in
theorem placesSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm w hw hok ρ hρ hpin _ _
  have hPA := placesAt (j := j) hw hρ hpin
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hXs : SplitSet (p.R.Q (p.R.mu (D.plEq w))) := by
    obtain ⟨-, e, he, -⟩ := hC.thP.vP j (p.R.mu (D.plEq w))
    exact SplitSet.mono ⟨e, he⟩ Finset.subset_union_right
  have hl : ∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    rcases (hPA.2 P).1 (Or.inl hP) with hD | hQ
    · have h1 : P ∈ (↑(D.ntw.pD (ex.nch.twI w)) : Set (Pl D.host.E)) := hD
      rw [D.ntw.pD_eq] at h1
      have hlp := (D.ntw.lPrime (ex.nch.twI w)).out
      refine not_mem_of_coprime h1 ?_
      split_ifs with h
      · exact (Nat.coprime_primes hlp D.host.pde'_prime).2 (by rw [h]; exact D.host.pde_ne)
      · exact (Nat.coprime_primes hlp D.host.pde_prime).2 h
    · exact fun hlP => Finset.disjoint_left.1 hok.2.1 hQ (D.ntw.twistExcludedPlaces_contains_residueChar _ hlP)
  refine ⟨hXs, hl, ?_⟩
  obtain ⟨-, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  obtain ⟨R, -, hR, hRs⟩ := hadm.1.split
  have hYs := hRs.mono hR
  have hXC : ∀ P, P ∈ p.R.Q (p.R.mu (D.plEq w)) ∪ (p.R.Q (p.R.mu (D.plEq w))).image Formalism.L2.DIV.conjPl ↔
      (P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w) := fun P => by
    rw [← hPA.2 P, Finset.mem_union, Finset.mem_image]
    refine or_congr Iff.rfl (exists_congr fun P' => and_congr Iff.rfl ?_)
    rw [lev_isConjPl_iff, eq_comm]
  have hne : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w → Formalism.L2.DIV.conjPl P ≠ P := fun P hP e => by
    rcases Finset.mem_union.1 ((hXC P).2 hP) with h | h
    · exact Finset.disjoint_left.1 (disjoint_conj hXs) h (Finset.mem_image.2 ⟨P, h, e⟩)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl] at e
      exact Finset.disjoint_left.1 (disjoint_conj hXs) hP' (Finset.mem_image.2 ⟨P', hP', e.symm⟩)
  have hcl : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w →
      Formalism.L2.DIV.conjPl P ∈ D.ntw.pD (ex.nch.twI w) ∨ Formalism.L2.DIV.conjPl P ∈ ex.nch.Q w := fun P hP => by
    rw [← hXC] at hP ⊢
    rcases Finset.mem_union.1 hP with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl]
      exact Finset.mem_union_left _ hP'
  have hY : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q =
      half (ρ.ch (ex.nch.twI w)) (D.ntw.pD (ex.nch.twI w)) ∪ half (ρ.ch (ex.nch.twI w)) (ex.nch.Q w) := by
    rw [hρ.delta]
    rfl
  rw [hY] at hYs ⊢
  exact idem_add_cA_eq hXs hYs fun P =>
    (hXC P).trans (mem_half_closure ((hρ.ch _).pair) hcl hne P).symm
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesStStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_places_statement : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.placesSt_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.placesSt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.placesSt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankAtPlacesRec
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.TraceClassRank
section General
open scoped TensorProduct
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}
end General
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
theorem rank_at_twisted_places_of_rec_span (hR : p.PointConditions') (hm : More p) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hrec : RecAt p Tp r O)
    (hMax : ∀ v ∈ p.R.twPl, ∀ j,
      GlobalTheory.TraceClassRank.SpanOverClasses (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt D v))
    (hSp : LeafSpan O) (hD : LeafData O)
    (hCmp : ∀ v ∈ p.R.twPl, ∀ j,
      letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
      GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (hrec.1.ok.laws v).p (fw2 p) j (r.lev j)
        (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt D v)) :
    GlobalTheory.TraceClassRank.RankAtPlaces O := by
  obtain ⟨hC, hOk, hLU, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hm.1
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.1.tied
  have hX := hOk.irr
  have h1 := hC.grp.levels
  have hU : (F2 p).P0 ≤ (mirIncl (R2 p)).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩
  have hProj : LeafProj O := (level_of_tied ⟨z, act, y, ht⟩ hX h1).2.2
  have hd : ∀ j, FormsDetermined (R2 p) j := fun j =>
    formsDetermined_of (GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj.of_char GlobalTheory.LowTypeRestriction.resInj _ _ hC) hC.models.HW hLU
  have hComm : ∀ j (g : Mir (R2 p)), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j := fun j g => by
    obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
    letI : Algebra (r.used v₁).full.J.Q.c.F D.what₂.LL := p.alg
    exact tie_e_comm_rho (ht v₁ j).1 (ht v₁ j).2 hOk.irr g
  have key : ∀ v ∈ p.R.twPl, ∀ j, (O.ThJ v j).FG ∧
      O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j) := fun v hv j => by
    letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
    have hv' : v ∈ (R2 p).twPl := hv
    have hdel : ∀ x, ((((R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range := fun x => by
      obtain ⟨a, ha⟩ := Formalism.L2.Pj.FO_le _ (hm.2.1.delAt_mem (Formalism.EigenvalueLevelCeiling.plc v) x)
      exact ⟨a, ha⟩
    have hty := GlobalTheory.T.baseTupleThetaSpan_hasType _ _ _ _ _ _ (R2 p) (F2 p) ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ j hLU (hd j) v hv'
      hC.tup.mu_on hdel (fun u => chi_eq_one h1 hC.grp.chiW j u.2)
    exact tie_thetaJ (ht v j).1 (ht v j).2 (mirIncl_injective _) hU (hd j) (hMax v hv j) hty (hrec.1.ok.run v hv' j)
      (hCmp v hv j)
  exact GlobalTheory.T.eigenlattice_local_containment_at_pairs _ _ _ _ _ _ O hSp hD hProj hComm fun w hw =>
    ⟨fun j => key w hw j, fun j => key _ (conjPl_mem_twPl hC hw) j⟩
end Point
end GlobalTheory.BigOn
theorem GlobalTheory.BigOn.rankLocSt_of_max_geo_runs : _root_.GlobalTheory.BigOn.MaximalityStatement → _root_.GlobalTheory.BigOn.GeometricStatement' → (_root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j, letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg; GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)) → (_root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) := by
  intro hM hG hC
  refine ((hM.and hG).and hC).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨x1, H1⟩, ⟨c0, H2⟩⟩, ⟨x3, H3⟩⟩ := H
  refine ⟨c0, fun c hc hb => ?_⟩
  obtain ⟨x2, H2'⟩ := H2 c hc hb
  refine ⟨max x1 (max x2 x3), fun x hx hle i p hR hm r O hrec => ?_⟩
  have hle1 : x1 ≤ x := (le_max_left _ _).trans hle
  have hle2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have hle3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  have hg := H2' x hx hle2 i p hR hm r O hrec
  exact _root_.GlobalTheory.BigOn.rank_at_twisted_places_of_rec_span hR hm hrec (H1 x hx hle1 i p hR hm) hg.2.1 hg.2.2.2.1 (H3 x hx hle3 i p hR hm r hrec.1.ok hrec.2)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilTupleRoot
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilTupleRoot
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.TupRoot
variable {D : D7}
end GlobalTheory.TupRoot
open GlobalTheory.TupRoot in
theorem GlobalTheory.TupRoot.weil_tuple_root_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ t, ∃ ζ : ℕ → ℂ, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ (∀ j, j + 1 < D.R.m → f.g.b j ∈ GfC _ → f.g.b (j + 1) ∈ GfC _ → ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, ∀ g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → (_root_.GlobalTheory.Fam.pk_z W).ωY t j (a * f.g.b j, a' * f.g.b (j + 1)) g = ζ j • (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) g) ∧ (∀ j h g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → omT (_root_.GlobalTheory.Fam.pk_z W) t j h (f.g.b (j + 1), f.g.bT) g = ζ (j + 1) • omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) g) ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t j ^ n = (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0 j ^ n := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP _hR t
  have hc := hP.bot.hyp.2.2.2.1
  have hL := hc.lev
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  have hxi : ChrEq ((_root_.GlobalTheory.Fam.pk_z W).xi t) ((_root_.GlobalTheory.Fam.pk_z W).xiH t) := hL.xi t
  have hb : (_root_.GlobalTheory.Fam.pk_z W).xi W.P.A3.A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi W.P.A3.A.μ0))
  have hstep : ∀ k, Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta k =
      ((Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta k).1 * (_root_.GlobalTheory.Fam.pk_z W).xi t,
        (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta k).2 * (_root_.GlobalTheory.Fam.pk_z W).xi t) := by
    intro k
    unfold Lift.chrStep
    split_ifs <;> simp [Formalism.IndefR.Links.LevCh.mu, Lift.tup, hb, mul_right_comm]
  have hpow : ∀ x, (_root_.GlobalTheory.Fam.pk_z W).xi t x ^ n = 1 := pow_eq_one_of_chrEq hxi hn
  have hinf : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → (_root_.GlobalTheory.Fam.pk_z W).xi t x = 1 := eq_one_of_finPart hxi hn0 hn
  choose xr hxr using fun k => GlobalTheory.RecDict.exists_isDetRoot D (Yc D k) (f.g.b k)
  obtain ⟨xT, hxT⟩ := GlobalTheory.RecDict.exists_isDetRoot D D.sp.X' f.g.bT
  let w : ℕ → Circle := fun k => if k + 1 < D.R.m then ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr k))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t (xr (k + 1))
    else ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr k))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t xT
  refine ⟨fun k => (w k : ℂ), ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨n, hn0, ?_⟩
    have h1 : w k ^ n = 1 := by
      simp only [w]
      split_ifs <;> rw [mul_pow, inv_pow, hpow, hpow, inv_one, one_mul]
    have := congrArg (fun z : Circle => (z : ℂ)) h1
    simpa using this
  · intro j hj _ _ a ha a' ha' g hg
    have hW0 := hc.chain.ωY W.P.A3.A.μ0 j hj
    have hWt := hc.chain.ωY t j hj
    rw [hstep] at hWt
    obtain ⟨z, hz⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Yc D j) a
    obtain ⟨y, hy1, hy⟩ := GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ a ha z hz
    obtain ⟨z', hz'⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Yc D (j + 1)) a'
    obtain ⟨y', hy1', hy'⟩ := GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ a' ha' z' hz'
    rw [twist_eq hW0 hWt (GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ hy (hxr j))
      (GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ hy' (hxr (j + 1))) hg]
    have e : ((_root_.GlobalTheory.Fam.pk_z W).xi t (y * xr j))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t (y' * xr (j + 1)) = w j := by
      simp only [w, if_pos hj, map_mul, hinf _ hy1, hinf _ hy1', one_mul]
    rw [e]
  · intro j h g hg
    have hW0 := isWeil_rec (idx_top h) _ (hc.chain.ωX W.P.A3.A.μ0)
    have hWt := isWeil_rec (idx_top h) _ (hc.chain.ωX t)
    rw [hstep] at hWt
    have e := twist_eq hW0 hWt (hxr (j + 1)) hxT hg
    have hw : w (j + 1) = ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr (j + 1)))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t xT := by
      simp only [w]
      rw [if_neg (by omega)]
    show _ = ((w (j + 1) : Circle) : ℂ) • _
    rw [hw]
    exact e
  · intro j
    refine ⟨n, hn0, ?_⟩
    have hν : (_root_.GlobalTheory.Fam.pk_z W).xi t ^ n = 1 := MonoidHom.ext fun x => by simpa using hpow x
    simp only [Formalism.IndefR.Links.LevCh.mu, Lift.tup, hb, mul_one, mul_pow, hν]
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilTupleRootStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_of_unity_theta_twist_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ t, ∃ ζ : ℕ → ℂ, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ (∀ j, j + 1 < D.R.m → f.g.b j ∈ GfC _ → f.g.b (j + 1) ∈ GfC _ → ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, ∀ g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → (_root_.GlobalTheory.Fam.pk_z W).ωY t j (a * f.g.b j, a' * f.g.b (j + 1)) g = ζ j • (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) g) ∧ (∀ j h g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → omT (_root_.GlobalTheory.Fam.pk_z W) t j h (f.g.b (j + 1), f.g.bT) g = ζ (j + 1) • omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) g) ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t j ^ n = (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0 j ^ n := by
  first | exact @_root_.GlobalTheory.TupRoot.weil_tuple_root_alt | exact _root_.GlobalTheory.TupRoot.weil_tuple_root_alt | (intros; apply _root_.GlobalTheory.TupRoot.weil_tuple_root_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread)
namespace GlobalTheory.RefSum
section Free
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
end Free
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
def WtPtAlt : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → WtAt p i PP C u1
def NumPtAlt : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → NumAt p i PP C
end GlobalTheory.RefSum
end
end
end
