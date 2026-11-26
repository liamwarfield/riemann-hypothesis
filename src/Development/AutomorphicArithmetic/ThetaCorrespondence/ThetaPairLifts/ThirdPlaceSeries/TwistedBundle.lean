module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfRead
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatTensorSwapIsIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelThetaSeriesSpanOverClassRepresentatives
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesBaseTwistedUniversalRational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormFieldSquareClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Pack
open _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure RealPackage {D : D7} {O : Obj D} (R : _root_.Formalism.L2.RecTAlt O.ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) : Type 1 where
  P : RowSideFamily O.ex
  Dc : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Sp : ∀ Zs, SPer (Dc Zs)
  Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3
  B : _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Zsc S
def realPackageOfBundle {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S :=
  ⟨b.P, b.C.c.face, b.C.Sp, GlobalTheory.Fc.zsc b.P b.DH.1.1 b.DH.1.2 c, b.B⟩
def realPackageOfRealInput {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {x : R3.TwIn O.ex} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R S) :
    _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S := ⟨R3.divisionPairOfAdelicFormsFaceColumnsData x, x.F.Dc, x.F.Sp, x.F.Zsc, _root_.GlobalTheory.Mem.R3.boundedRealisationOfInput y⟩
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure TwistedBundle {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) : Type 1 where
  intersectionNumber_baseChange : R3.Holds x.R x.F
  y : _root_.GlobalTheory.Mem.R3.RealInAlt x b.R b.S
  r : _root_.GlobalTheory.Mem.R3.RecursiveInput y
  eq : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y
  HD : _root_.Formalism.L2.HostDatumWithTies b.R.T.toTiedDataS
end Pack
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
def WPt.saturationAtWeightedPoint (q : WPt p.s K) :
    SAt (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2 q.x.what₂.r.Y.eE fun u => (q.x.col.C.forms u).to0 := q.x.sx.1
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure BundleWitness (q : WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) : Type 1 where
  x : R3.TwIn q.O.ex
  a : R3.TwArgs q.O.ex q.x.what₂
  ax : HEq a.x x
  y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x
  recPin : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q b.R
  s : ∃ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (b.R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP),
    HEq sP q.saturationAtWeightedPoint.P ∧ HEq sS q.saturationAtWeightedPoint.S ∧ b.S = sS.toRealSpectralMatching b.R
  pt : HEq y.y.tS q.saturationAtWeightedPoint.t ∧ y.y.cS = q.saturationAtWeightedPoint.c
  sx : HEq y.y.Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core_data_of_point.row.kKs q.core_data_of_point.row.hk)
  eF : HEq y.y.nexp.eF q.core_data_of_point.row.nexp.eF
  fi : HEq y.y.nexp.fi q.core_data_of_point.row.nexp.fi
  uS : y.y.uS = 1
  parts : (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput y.r).PartsRow
  cW : HEq b.C.c.W q.B.wts ∧ HEq b.C.c.Xg q.x.what₂.r.z.Xg
  d3b : HEq y.HD.d3b q.x.pin.d3b
  side : _root_.Formalism.L2.SelectedSideOfRealRecord b.R (R3.divisionPairOfAdelicFormsFaceColumnsData x) (_root_.GlobalTheory.Mem.R3.realisationOfInput y.y) (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput y.r) y.HD q.core_data_of_point.a.Pq
  colPins : _root_.Formalism.L2.DIV.ColumnCharactersCompatible b.C.toS
def BundleLinkage (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : GlobalTheory.Fc.LkT _root_.GlobalTheory.Fc.BundleCondition :=
  linkOf (𝒮 := p.s) (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ q _ b => Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := p) q b)
end GlobalTheory.Mem.Top.Bl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Fc
section Def
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling _root_.Formalism.L2 _root_.Formalism.L2.Indef _root_.Formalism.L2.DIV _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
open GlobalTheory.EX GlobalTheory.EX.OB
abbrev qRealOfBundle {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) :
    _root_.Formalism.IndefR.IndefiniteRealisation b.R b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c) b.S b.B.T.Q.c.F := b.B.Q
def DefiniteSideCondition : _root_.GlobalTheory.Fc.R1.DefiniteSideType := fun D O c b C CH =>
  ∀ (hok1 : b.P.A3.fam3.Ok3 1) (hsep : b.P.A3.fam3.TypesSep3)
    (hP : CovolumeOntoIsometryConditions (_root_.GlobalTheory.Fc.qRealOfBundle b).Rl (faceT b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c)) (_root_.GlobalTheory.Fc.qRealOfBundle b).sEE (hkCan b.P.A3) C CH) (hI : PassIn3 (_root_.GlobalTheory.Fc.qRealOfBundle b).Rl (faceT b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c)) C CH)
    (lam0 C0 ce Sw C1 : ℝ) (H : ∀ u, (ofRecord D O.L b.DH.1.1 b.DH.1.2).NumFacts (letterOf D O.L b.DH.1.1 b.DH.1.2 u) O.L.Nc lam0 C0 ce c Sw C1)
    (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((b.C.toS.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs).a w) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.toIndefData O.ex.p0 (b.C.toS.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs)),
    DivTied3 D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.base.toIndefData
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.toIndefData O.ex.p0 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.col NuC I →
    HEq I b.P.I → ∀ u, RowsU b.C.toS.c (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI) (RecNums.ofNum (ofRecord D O.L b.DH.1.1 b.DH.1.2) (Equiv.refl _)
          (letterOf D O.L b.DH.1.1 b.DH.1.2 u) (D.mem u).A.T O.L.Nc lam0 C0 ce c Sw C1 (H u)) (I.wU u) (Cons.nuOf O.L u (I.eNu u))
end Def
end GlobalTheory.Fc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
def PlacedConditions : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
    (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg),
    f.c.Is ∧ v.Is ∧ _root_.GlobalTheory.Fam.CommutingVectorTie f v ∧ ShapeOff v o ∧ GPin G ∧ _root_.GlobalTheory.Fam.LocalGroupReading f G pl ∧ _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G ∧ PrimTop (c := f.c) v.tP o.ζ₀
theorem PlacedConditions.placed (h : _root_.GlobalTheory.MiTop.PlacedConditions f B) : _root_.GlobalTheory.MiTop.PlacedAlt f B := by
  obtain ⟨k, a1, a2, a3, a4, ι, v, o, n, G, pl, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  exact ⟨k, a1, a2, a3, a4, ι, v, o, n, G, pl, h1, h2, h3, h4, h5, h6, h7⟩
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAllUsedPart
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.FourBoundsAtBundles
theorem tupAllUsed_part_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : Formalism.L2.DIV.TupAllUsed b.P := by
  intro t
  rcases b.pt.charW.tup.mu_used t with h | ⟨w, hw⟩
  · left
    subst h
    exact b.P.tied.div.tup.mu0
  · right
    refine ⟨D.plEq.symm w, ?_⟩
    have e1 := b.pt.tupAt (D.plEq.symm w)
    rw [Equiv.apply_symm_apply] at e1
    have e2 := b.pt.tupTie (D.what₂.muAt (D.plEq.symm w)) (Or.inr ⟨_, rfl⟩)
    rw [e1, hw] at e2
    exact e2
theorem p_div_of_div3g {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) (h : GlobalTheory.Cp.DivRows3G b.P) : _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b :=
  Formalism.L2.DIV.DivRows3G.toRows (_root_.GlobalTheory.Fc.FourBoundsAtBundles.tupAllUsed_part_alt b)
    ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩
end GlobalTheory.Fc.FourBoundsAtBundles
namespace GlobalTheory.Fc.FourBoundsAtBundles
end GlobalTheory.Fc.FourBoundsAtBundles
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatDegreeStatement
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.CovTop.FlatDegProof
theorem flatDeg_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.FlatDegreeCondition := by
  intro hP
  have hS : FlatDegreeSt := _root_.UpperTheory.Lit.Flat.flat_tensor_swap_isIso hP hP.q2 hP.q4
  exact ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, le_rfl, 0, fun x hx _ ι p _ i _ Y hY => flatDegAt_of_st p i Y hY hS⟩⟩⟩
end GlobalTheory.CovTop.FlatDegProof
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatDeg_of_scholzeWeinstein_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.FlatDegreeCondition := by
  first | exact @_root_.GlobalTheory.CovTop.FlatDegProof.flatDeg_alt_alt | exact _root_.GlobalTheory.CovTop.FlatDegProof.flatDeg_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.FlatDegProof.flatDeg_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MaxSt
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem maxSt_alt : _root_.GlobalTheory.BigOn.MaximalityStatement := by
  refine Formalism.MainNotions.Closed.of_all fun Fm _ => ⟨0, fun x hx _ i p hR hM v hv j => ?_⟩
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC := hL.1
  have hv' : v ∈ (R2 p).twPl := hv
  have hdel : ∀ y, ((((R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 y : ℂˣ) : ℂ) ∈ (Fm.D x i).what₂.embLL.range := fun y => by
    obtain ⟨z, hz⟩ := FO_le _ (hM.2.1.delAt_mem (Formalism.EigenvalueLevelCeiling.plc v) y)
    exact ⟨z, hz⟩
  exact GlobalTheory.TraceClassRank.spanOverClasses_of
    (GlobalTheory.T.baseThetaKernel_series_unique _ _ _ _ _ _ (R2 p) (F2 p) ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ j v hv' hC.tup.mu_on)
    (GlobalTheory.T.kernel_thetaSeries_span_over_class_representatives _ _ _ _ _ _ (R2 p) (F2 p) ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ j v hv' hC.tup.mu_on hdel
      _ _ _)
end GlobalTheory.BigOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupleFreeLevelLeCompact
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLev
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
def relaxedLevelSubgroup (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i =>
      KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0)).comap (_root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj)
def baseLevelSubgroup (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (j : ℕ) (hj : j + 1 = B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) then
    _root_.GlobalTheory.PenLev.relaxedLevelSubgroup h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥
theorem relax_le_gfc (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α ≤ GfC _ :=
  fun _ hg => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2
theorem base_level_subgroup_le_gfc (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (j : ℕ) (hj : j + 1 = B.R.m) : _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj ≤ GfC _ := by
  unfold _root_.GlobalTheory.PenLev.baseLevelSubgroup
  split_ifs
  · exact _root_.GlobalTheory.PenLev.relax_le_gfc _ _ _ _
  · exact bot_le
theorem mem_relax_iff' (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α ↔ g ∈ J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) ∧ g ∈ GfC _ ∧
      ∀ i, _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ := by
  simp only [_root_.GlobalTheory.PenLev.relaxedLevelSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, and_assoc]
theorem base_level_subgroup_eq_relax (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) (hJ : J.Reads) (α : J.Ch j) :
    ∃ (t₀ : W.P.T) (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀) (α₀ : J₀.Ch j), J₀.Reads ∧ _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj = _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J₀ j hj α₀ := by
  have h : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2.some, h.choose_spec.choose_spec.1, ?_⟩
  unfold _root_.GlobalTheory.PenLev.baseLevelSubgroup
  rw [dite_eq_left h]
end GlobalTheory.PenLev
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKO
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKO
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.LevProd.SamePlace
open GlobalTheory.FinPl (Lat latV Moves SplitPt)
open GlobalTheory.IwaPlace (hermAt)
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) {L : Lat V}
set_option maxHeartbeats 1000000 in
theorem phi_mem_KO_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i₀ i, (J₀.G i₀).q.v = (J.G i).q.v → ∀ g ∈ GfC _, _root_.GlobalTheory.LevProd.localHomProduct J₀ j hj g i₀ ∈ KO (J₀.G i₀).k _ → _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ j hj t₀ J₀ _ t J _ i₀ i hv g _ h0
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L :=
    (ha.x j (by have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)).sd
  have hm := moves_of_mem_KO (J₀.G i₀).q ((J₀.G i₀).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J₀ i₀ hj; omega)) hsd
    ((J₀.G i₀).latX j _) h0
  exact GlobalTheory.SplitInt.mem_KO_of_moves (J.G i).q _ ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)) (a.g.x j).L
    (· = (J₀.G i₀).q.v) hv.symm ((J.G i).latX j _) g hm _ ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
end GlobalTheory.LevProd.SamePlace
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKOStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_closed_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i₀ i, (J₀.G i₀).q.v = (J.G i).q.v → ∀ g ∈ GfC _, _root_.GlobalTheory.LevProd.localHomProduct J₀ j hj g i₀ ∈ KO (J₀.G i₀).k _ → _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  first | exact @_root_.GlobalTheory.LevProd.SamePlace.phi_mem_KO_alt | exact _root_.GlobalTheory.LevProd.SamePlace.phi_mem_KO_alt | (intros; apply _root_.GlobalTheory.LevProd.SamePlace.phi_mem_KO_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumbersAtPoint
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumbersAtPoint
set_option synthInstance.maxHeartbeats 200000

section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.RefSum.NumPt
section Cols
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
end Cols
theorem _root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → JetNum (Fm.D x ι) (DF (dat p i) (aOf p i u1)) (1 / 2500) ∧ 2 * (Fm.D x ι).R.r ≤ nCol (dat p i) ∧ (lenT p i PP : ℝ) * (Real.log ((Fm.D x ι).host.g 0) + Real.log ((Fm.D x ι).host.g 1)) ≤ C * unitE p := by
  intro hS
  refine Closed.imp (Closed.and (_root_.GlobalTheory.T.quotient_weight_gap_bounds' hS) (_root_.GlobalTheory.T.lenT_zBase_unitE_nCol_bounds hS)) ?_
  rintro eps Fm CH - ⟨⟨_, _, hA⟩, ⟨_, _, hB⟩⟩
  obtain ⟨x0, h⟩ := _root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and hA hB
  refine ⟨max 0 (2 + 2 * Fm.CYL), le_max_left _ _, x0, fun x hx hle ι p hp i hi u1 hu => ?_⟩
  obtain ⟨hA, hB⟩ := h x hx hle ι p hp
  obtain ⟨a1, -, a3, a4, a5, a6, -⟩ := hA i hi u1 hu
  obtain ⟨b1, b2, -, -, b5, b6⟩ := hB i
  refine ⟨jetNum_of_sizes (Fm.sizes x hx ι) ?_, a3 ▸ two_mul_rank_le_nCol _, ?_⟩
  · have hev : Even (nCol (dat p i)) := even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) eight_dvd_nCol)
    have := (GlobalTheory.T.thetaExponents_dominant_lastEntry_one_degree _ _ (dat p i) u1 (nCol (dat p i)) _ a1 hev a4 a5 a6).2.2.2.2
    rw [finrank_host, a3, Nat.mul_div_cancel_left _ two_pos] at this
    exact this
  · have hg := log_g_le (Fm.params x hx ι) b2 b5 b6
    rw [Fm.params_CYL x hx ι] at hg
    have hZ : 0 ≤ zBase (Fm.L x ι) ^ 12 := by positivity
    have hT : (0 : ℝ) ≤ lenT p i (Fm.parT x hx ι).PP := Nat.cast_nonneg _
    have hg' := hg.trans (mul_le_mul_of_nonneg_right (le_max_right 0 _) hZ)
    have h1 := mul_le_mul_of_nonneg_left hg' hT
    have h2 := mul_le_mul_of_nonneg_left b1 (le_max_left 0 (2 + 2 * Fm.CYL))
    linarith [mul_left_comm (lenT p i (Fm.parT x hx ι).PP : ℝ) (max 0 (2 + 2 * Fm.CYL)) (zBase (Fm.L x ι) ^ 12)]
end GlobalTheory.RefSum.NumPt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumbersAtPointStatement
set_option synthInstance.maxHeartbeats 200000

section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetNum_nCol_lenT_bounds_of_quo : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → JetNum (Fm.D x ι) (DF (dat p i) (aOf p i u1)) (1 / 2500) ∧ 2 * (Fm.D x ι).R.r ≤ nCol (dat p i) ∧ (lenT p i PP : ℝ) * (Real.log ((Fm.D x ι).host.g 0) + Real.log ((Fm.D x ι).host.g 1)) ≤ C * unitE p := by
  first | exact @_root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point | exact _root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point | (intros; apply _root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKOOfNotTwAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKOOfNotTwAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.LevProd.OffTwist
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.LevProd.OffTwist
theorem GlobalTheory.LevProd.phi_mem_KO_of_not_twAt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ j hj t₀ J₀ hJ₀ α₀ t J _ i _
  have hjm : j ≤ B.R.m := by omega
  obtain ⟨ε, hε, hε'⟩ := (J.G i).q.above
  have und : (J.pl i).under (𝓞 (I.rec7 l Z).host.F) = (J.G i).q.v :=
    GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε hε'
  have hv := (GlobalTheory.Mem.Col2.TC.underQ_notMem I hW.tr.ok l u (W.P.I.tup t) (J.G i).q.v
    ⟨J.pl i, (hW.tq.Q t _).1 (J.mem i), und⟩).1
  have hlb := (hJ₀.is.reads j hjm).lb (J₀.ι j α₀)
  refine GlobalTheory.LevProd.OffTwist.locHom_mem_KO (J.G i).q _ (rankN (I.rec7 l Z) j hjm) _ ((ha.stdQ _ _).1 j _) (B.T u) hv
    (J₀.A.K j hjm (J₀.ι j α₀)).lev.Lb (fun x hx r => ?_) (fun s => ?_) (σ := sigD _) (J := gramN (I.rec7 l Z) j hjm) _ (fun g hg => ?_)
  · obtain ⟨c, hc, -⟩ := (hlb x).1 hx r
    exact ⟨c, hc⟩
  · refine (hlb _).2 fun r => ?_
    by_cases h : r = s
    · subst h
      refine ⟨(B.T u : ℕ), (Pi.single_eq_same _ _).trans (map_natCast (algebraMap (𝓞 B.host.E) B.host.E) _).symm, fun _ => ⟨_, (l.pr.piT_norm u).symm⟩⟩
    · exact ⟨0, (Pi.single_eq_of_ne h _).trans (map_zero (algebraMap (𝓞 B.host.E) B.host.E)).symm, fun _ => dvd_zero _⟩
  · obtain ⟨κ, hκ⟩ := ((hJ₀.is.U j hjm _ g).1 hg).2
    exact ⟨κ.1, hκ, (J₀.A.K j hjm (J₀.ι j α₀)).lev.Uloc_lev _
      ((((J₀.A.K j hjm (J₀.ι j α₀)).lev.U_eq κ.1).1 κ.2).2 _)⟩
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKOOfNotTwAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_final_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  first | exact @_root_.GlobalTheory.LevProd.phi_mem_KO_of_not_twAt_alt | exact _root_.GlobalTheory.LevProd.phi_mem_KO_of_not_twAt_alt | (intros; apply _root_.GlobalTheory.LevProd.phi_mem_KO_of_not_twAt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlMemLevel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlMemLevel
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd.OffTwist
set_option maxHeartbeats 2000000 in
theorem gl_mem_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t₂ (J₂ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₂), J₂.Reads → ∀ i : Fin J₂.r, ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J (J₂.G i).q.v → ∀ (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J₂.G i).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (∀ y, SuppAt (J₂.G i).q.e _ (gl y) ∧ (mt _ (gl y)).map (J₂.G i).q.pr = ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))).β * y.val * ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))).γ) → ∀ y ∈ KO (J₂.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j), gl y ∈ J.A.U j (J.ι j α) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α t₂ J₂ hJ₂ i hv gl hgl y hy
  have hjm : j ≤ B.R.m := by omega
  have hok : I.Ok := hW.tr.ok
  have hsup : gl y ∈ GlobalTheory.FinPl.grpAt _ (· = (J₂.G i).q.v) :=
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ (J₂.G i).q _ _ (hgl y).1 _ rfl
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L := (ha.x j hjm).sd
  have hKO : GlobalTheory.LevIdx.locHom (J₂.G i).q _ ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))) (gl y) ∈ KO _ _ :=
    (GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgl y).2 ▸ hy
  have hm := GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J₂.G i).q _ hsd ((J₂.G i).latX j _) hKO
  haveI : Submodule.IsLattice (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (a.g.x j).L := hsd.1
  have hfg : (a.g.x j).L.FG := Submodule.IsLattice.fg (A := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (a.g.x j).L
  have hu₂ : I.UnderQ (W.P.I.tup t₂) (J₂.G i).q.v :=
    ⟨J₂.pl i, (hW.tq.Q t₂ (J₂.pl i)).1 (J₂.mem i), ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t₂ J₂ hJ₂).2 i).symm⟩
  obtain ⟨hTv, hgv⟩ := GlobalTheory.Mem.Col2.TC.underQ_notMem I hok l u _ _ hu₂
  have hbad : (J₂.G i).q.v ∉ J.A.bad j := fun h => by
    rcases hJ.is.bad_le j hjm _ h with (h0 | h0) | ⟨P, hP, e⟩
    · exact hgv 0 h0
    · exact hgv 1 h0
    · obtain ⟨i', hi'⟩ := hJ.surj P ((hW.tq.Q t P).2 hP)
      refine hv ⟨i', ?_⟩
      rw [(_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).2 i', hi']
      exact e
  have hlb := (hJ.is.reads j hjm).lb (J.ι j α)
  refine (hJ.is.U j hjm _ _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hsup, ?_⟩
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hd : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := ⟨_, (hPr.piT_norm u).symm⟩
  exact exists_mem_level (I.rec7 l Z) _ _ _ (J.A.K j hjm (J.ι j α)).lev (X.piT u) hd hlb (a.g.x j).L hfg
    (fun x => ((hat.pinX.xs j hjm).2.2 x).trans
      (forall_congr' fun r => ⟨fun h => ⟨⟨x r, h⟩, rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.2⟩)) _ hbad hTv _ hsup hm
end GlobalTheory.LevProd.OffTwist
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlMemLevelStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_open_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t₂ (J₂ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₂), J₂.Reads → ∀ i : Fin J₂.r, ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J (J₂.G i).q.v → ∀ (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J₂.G i).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (∀ y, SuppAt (J₂.G i).q.e _ (gl y) ∧ (mt _ (gl y)).map (J₂.G i).q.pr = ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))).β * y.val * ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))).γ) → ∀ y ∈ KO (J₂.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j), gl y ∈ J.A.U j (J.ι j α) := by
  first | exact @_root_.GlobalTheory.LevProd.OffTwist.gl_mem_level_alt | exact _root_.GlobalTheory.LevProd.OffTwist.gl_mem_level_alt | (intros; apply _root_.GlobalTheory.LevProd.OffTwist.gl_mem_level_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocLevel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocLevel
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
theorem loc_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) i, _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ KO (J.G i).k _ ∧ MeasurableSet (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).relIndex (KO (J.G i).k _) ≠ 0 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α i
  have hs := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj
  have hjm : j < B.R.m := by omega
  have hL := hW.tr.ok.idx_ok (W.P.I.tup t)
  have hrep := hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' hs) hjm (J.ι j α)
  rw [hJ.sec j (by omega) α i] at hrep
  have hle : _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ KO (J.G i).k _ :=
    prX_le_KO_of_prCat _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _
      (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by omega) _ _ hrep (hL.int _ _ _)
  have hreg := (J.E i).reg
  have hJo : IsOpen ((((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1)
      (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)).J : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin ((J.G i).s - j + 1)) (J.G i).k)) :=
    (hreg.2.2 _ _ _).1
  set g₀ := (J.E i).rep j ((J.G i).s - j) (Nat.add_sub_cancel' hs) (α i) with hg₀
  have hOo : IsOpen {w : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin ((J.G i).s - j + 1)) (J.G i).k |
      g₀⁻¹ * w * g₀ ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1)
        (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)).J} :=
    hJo.preimage (by fun_prop)
  have hpo : IsOpen (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) := by
    refine GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [one_mem]) ?_
    intro z hz hzO
    exact GlobalTheory.StepData.mem_Cgrp.2 ⟨hz, hzO⟩
  haveI : BorelSpace (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) := GlobalTheory.SplitFlip.borel_GL
  refine ⟨hle, hpo.measurableSet, ?_⟩
  have hc := GlobalTheory.SplitFlip.isCompact_KO (k := (J.G i).k) (n := XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)
  haveI : CompactSpace (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)) := isCompact_iff_compactSpace.1 hc
  have ho' : IsOpen (((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _) : Subgroup _) : Set (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j))) :=
    hpo.preimage continuous_subtype_val
  haveI : Finite (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ⧸ (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _)) :=
    ((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _)).quotient_finite_of_isOpen ho'
  haveI : ((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.FiniteIndex.index_ne_zero
end GlobalTheory.LevProd
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocLevelStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_transport_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) i, _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ KO (J.G i).k _ ∧ MeasurableSet (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).relIndex (KO (J.G i).k _) ≠ 0 := by
  first | exact @_root_.GlobalTheory.LevProd.loc_level_alt | exact _root_.GlobalTheory.LevProd.loc_level_alt | (intros; apply _root_.GlobalTheory.LevProd.loc_level_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatIoAt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BigOn.Exp.SerBase
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
section BaseChange
variable {E K₀ K ι : Type} [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Fintype ι]
  {n : ℕ}
end BaseChange
end GlobalTheory.BigOn.Exp.SerBase
namespace GlobalTheory.BigOn.Exp.SerBase
theorem latIoAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.LatticeInclusionAt := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hR hM w hw j => ?_
  intro ρ hρ hpin c hc hs
  obtain ⟨gramR, c0R, c0L, hft, u, hu, hsc⟩ := hs
  refine ⟨u, hu, fun h hh P hP => ?_⟩
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hio : IoExt (R2 p) := hR.ioExt
  have hB := hρ.base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have hlam := hBo.lam
  have hMlat := GlobalTheory.LatFull.latAt_isFullLattice _ ρ hρ ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h
  obtain ⟨hPh, hPF⟩ := (mem_harmLat _ _ _).1 hP
  rw [hlam] at hPF
  have key : ∀ φ ∈ coefLatFn (embLL0 (Fm.D x i)) (labLL0 (Fm.D x i)) (smallInt (Fm.D x i)) (lamV (Fm.D x i) j)
      ((ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h)),
      ∃ F : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j), F ∈ nabAtr (labLL (Fm.D x i)) (lamV (Fm.D x i) j)
        ((ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h)) ∧
        φ = coefFn (Fm.D x i).what₂.embLL (lamV (Fm.D x i) j) (F : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨F₀, hF₀, rfl⟩ := hφ
      refine ⟨⟨MvPolynomial.map (Fm.D x i).LL0.val.toRingHom F₀.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ F₀.2⟩,
        map_mem_nabAtr_comp (Fm.D x i).LL0.val.toRingHom (labLL0 (Fm.D x i)) _ _ hMlat hF₀, ?_⟩
      funext y
      rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]
      rfl
    | zero => exact ⟨0, zero_mem _, funext fun y => by simp [coefFn]⟩
    | add φ ψ _ _ h1 h2 =>
      obtain ⟨F1, m1, rfl⟩ := h1
      obtain ⟨F2, m2, rfl⟩ := h2
      exact ⟨F1 + F2, add_mem m1 m2, funext fun y => by simp [coefFn, mul_add]⟩
    | smul a φ _ h1 =>
      obtain ⟨F1, m1, rfl⟩ := h1
      obtain ⟨t, ht⟩ := a.2
      refine ⟨RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t • F1, Submodule.smul_mem _ _ m1, funext fun y => ?_⟩
      have e1 : ((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t • F1 : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j)) :
          Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) =
          MvPolynomial.C (((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t : 𝓞 (Fm.D x i).what₂.LL)) :
            (Fm.D x i).what₂.LL) * (F1 : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) := by
        rw [← MvPolynomial.smul_eq_C_mul]
        rfl
      have e2 : (Fm.D x i).what₂.embLL (((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t : 𝓞 (Fm.D x i).what₂.LL)) :
          (Fm.D x i).what₂.LL) = (a : ℂ) := by
        rw [← ht]
        rfl
      show (a : ℂ) * coefFn _ _ (F1 : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) y = _
      rw [e1, coefFn, coefFn, map_mul, MvPolynomial.eval₂Hom_C, e2]
      ring
  obtain ⟨F, hF, hFe⟩ := key _ hPF
  have hM' : (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h) =
      Bridge.hLat (Vc (Fm.D x i) j) (fin (Vc (Fm.D x i) j) h) :=
    GlobalTheory.LatAtHLat.latAt_eq_hLat _ _ _ _ (GlobalTheory.LatFull.baseFrame_one_eq _ _ _ (hρ.latS _ j _)) _
  refine ⟨c0L j F, ⟨gramR, c0R, c0L, hft, F, by rw [← hM']; exact hF, rfl⟩, ?_⟩
  obtain ⟨u', w₀, hu', -, hw₀⟩ := IsChosenExtremalVector.io _ ((fw2 p).hv₀ j _) hio
  have huu : u' = (u : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ) :=
    funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  rw [huu] at hw₀
  have hm : ∀ τ, (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).w.p τ +
      (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).w.q τ ≤ (Wc (Fm.D x i) j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE (Fm.D x i) τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function _ _ _ _ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).F.BS hB.wt hm
  exact IsScaleAt.ioP_eq (Rl := p.R) hsc hinj hPh
    (GlobalTheory.SeriesTie.UnivRat.ioP_mem_harmonic hC.lev hC.thP (hC.models.cV j) hB (hpin.psi _ j _) (hpin.inf _ j _)
      (hpin.cartT _ j _) (hpin.onbS _ j _) (hpin.onbT _ j _) (hpin.mu0 _ j _) (hpin.eta _ j _) (hpin.ap _ j _) (hpin.am _ j _)
      _ w₀ hw₀ _) hFe
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOf
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatUnframe
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatUnframe
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnframePt
open GlobalTheory.RealGeo GlobalTheory.Unframe Formalism.IndefR.FWT
set_option maxHeartbeats 3200000 in
theorem rat_unframe_alt : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p →
  ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m), RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j →
  ∃ (T' : CoreJ (Fm.D x i)) (_ : Algebra T'.Q.c.F (Fm.D x i).what₂.LL) (Rl' : RealDat3 (Fm.D x i) p.P.A3 T'.Q.c.F)
    (cG' : G0 Rl'.Pg (Fm.D x i).R.r ≃* G0g (Fm.D x i).nd) (S' : NX.RatDat (Fm.D x i).ntw) (YS' : NX.NExpRealS Rl' cG' S')
    (F' : Face (Fm.D x i) p.P.A3.A) (κ' : ∀ j : Fin (Fm.D x i).R.m, WeightFamilies.Wt (Fm.D x i) ((j : ℕ) + 1))
    (v₀' : ∀ (j : Fin (Fm.D x i).R.m) (σ : (Fm.D x i).what₂.LL →+* ℂ), (Rl'.MW j σ).Vec)
    (O' : ∀ j, OMDat T'.toCore Rl'.toRealDat j Unit (fun _ => p.P.A3.A.μ0)) (hV' : T'.V ((j : ℕ) + 1) T'.σ₀ = Wc (Fm.D x i) j),
    RatHyp T' Rl' F' κ' v₀' O' t j hV' ∧ (∀ ρ : Setup (Fm.D x i).ntw, RealPin p.R p.cG ρ → RealPin Rl' cG' ρ) ∧
      ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool), RatRow YS' v₀' hρ t j b → RatRow p.nexp p.v₀ hρ t j b := by
  intro hP eps Fm x hx i p hR hM t j h0
  obtain ⟨c', w, hw, hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (_root_.GlobalTheory.T.inGeo_half_of_ratHyp0 hP Fm x hx i p hR hM t j h0)
  obtain ⟨S', YS', hY⟩ := GlobalTheory.T.seriesRationality_back_from_movedReadings p.R p.cG p.Sx p.nexp w hw
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w).toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w hw h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w).toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w).phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w) (F2 p) B'.κ B'.v₀ B'.O t j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  refine ⟨setCE p.T c', iA, fullHeckeRealDatMovedReadings p.R w, p.cG, S', YS', F2 p, B'.κ, B'.v₀, B'.O, hV', hRat, fun ρ h =>
    ⟨h.psi, h.inf, h.cartT, h.onbS, h.onbT, h.latS, h.latT, h.frS, h.frT, h.vac, h.Pg, h.grp, h.mu0, h.eta, h.delta, h.deltaPl,
      h.ap, h.am⟩, fun ρ hρ b h => ?_⟩
  have h1 := hY B'.v₀ ρ hρ t j b h
  rw [hv] at h1
  exact h1
end GlobalTheory.UnframePt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatUnframeStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_data_realization_alt : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p →
  ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m), RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j →
  ∃ (T' : CoreJ (Fm.D x i)) (_ : Algebra T'.Q.c.F (Fm.D x i).what₂.LL) (Rl' : RealDat3 (Fm.D x i) p.P.A3 T'.Q.c.F)
    (cG' : G0 Rl'.Pg (Fm.D x i).R.r ≃* G0g (Fm.D x i).nd) (S' : NX.RatDat (Fm.D x i).ntw) (YS' : NX.NExpRealS Rl' cG' S')
    (F' : Face (Fm.D x i) p.P.A3.A) (κ' : ∀ j : Fin (Fm.D x i).R.m, WeightFamilies.Wt (Fm.D x i) ((j : ℕ) + 1))
    (v₀' : ∀ (j : Fin (Fm.D x i).R.m) (σ : (Fm.D x i).what₂.LL →+* ℂ), (Rl'.MW j σ).Vec)
    (O' : ∀ j, OMDat T'.toCore Rl'.toRealDat j Unit (fun _ => p.P.A3.A.μ0)) (hV' : T'.V ((j : ℕ) + 1) T'.σ₀ = Wc (Fm.D x i) j),
    RatHyp T' Rl' F' κ' v₀' O' t j hV' ∧ (∀ ρ : Setup (Fm.D x i).ntw, RealPin p.R p.cG ρ → RealPin Rl' cG' ρ) ∧
      ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool), RatRow YS' v₀' hρ t j b → RatRow p.nexp p.v₀ hρ t j b := by
  first | exact @_root_.GlobalTheory.UnframePt.rat_unframe_alt | exact _root_.GlobalTheory.UnframePt.rat_unframe_alt | (intros; apply _root_.GlobalTheory.UnframePt.rat_unframe_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem rowAt_of_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace := by
  intro hP hA hR hS hL hT
  refine _root_.GlobalTheory.BigOn.Exp.twist_at_statement_of_ratHypAt ?_ (GlobalTheory.T.thetaSeries_base_twisted_universal_rational hA hR hS)
  exact _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hL hT) fun Fm x hx i p hp hM w _ j h =>
    _root_.GlobalTheory.T.exists_rational_data_realization_alt hP Fm x hx i p hp hM _ j (_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hp hM _ h.2.2.2 h.1 j)
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnivL
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))
theorem real_pin_setup_local (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) : GlobalTheory.SeriesTie.RealPin (datL x L).R (datL x L).cG (setupL L l.b.ser.ex.ρ) :=
  have p := l.b.ser.ex.pin
  ⟨(by with_unfolding_all exact (p.psi :)), (by with_unfolding_all exact (p.inf :)), (by with_unfolding_all exact (p.cartT :)), (by with_unfolding_all exact (p.onbS :)), (by with_unfolding_all exact (p.onbT :)), (by with_unfolding_all exact (p.latS :)), (by with_unfolding_all exact (p.latT :)), (by with_unfolding_all exact (p.frS :)), (by with_unfolding_all exact (p.frT :)), (by with_unfolding_all exact (p.vac :)), (by with_unfolding_all exact (p.Pg :)),
    (by with_unfolding_all exact (p.grp :)), (by with_unfolding_all exact (p.mu0 :)), (by with_unfolding_all exact (p.eta :)), (by with_unfolding_all exact (p.delta :)), (by with_unfolding_all exact (p.deltaPl :)), (by with_unfolding_all exact (p.ap :)), (by with_unfolding_all exact (p.am :))⟩
theorem is_univ_char_local (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) : GlobalTheory.UnivChar.IsUnivChar (DL x L).nexp := (by with_unfolding_all exact (l.b.ser.ex.univ :))
end GlobalTheory.HeightCounting.Fin3
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigHkDatBack
set_option synthInstance.maxHeartbeats 200000

section
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
end Gen
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (L : LocAll (lay0 (Dof x)))
theorem hkDat_of_hkDat_datL (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {i k Q α Rr} (h : HkDat (datL x L).R (_root_.GlobalTheory.HeightCounting.Fin3.smallPlaceSet L l) i k Q α Rr) :
    HkDat x.m.z.R l.rat.In.Sb ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(h.split), (h.offS), (h.odd), (h.le), (h.elt), (h.reps)⟩
theorem eigVec_eW_of_hkDat_good_index (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (i σ k Q α Rr) (hd : HkDat x.m.z.R l.rat.In.Sb i k Q α Rr) (hσ : (Dof x).nd.goodRow σ) (y)
    (hy : y ∈ (Dof x).what₂.isot (i.1 + 1) σ) : EigVec x.m.z.R i k Q Rr (l.rat.In.eig (i.1 + 1) σ k Q) (x.r.Y.mj.eW i y) :=
  (by with_unfolding_all exact (eigAd_iff_eigVec x.r.Y l.rat.In.Sb l.rat.In.eig).mp l.rat.rat.eig i σ k Q α Rr hd hσ y hy)
theorem eigAd_smallPlaceSet_of_yRel (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    EigAd Y (smallPlaceSet L l) (localEigenvalueDegree L l) := by
  apply (eigAd_iff_eigVec Y (smallPlaceSet L l) (localEigenvalueDegree L l)).2
  intro i σ k Q α Rr hd hσ y hy
  with_unfolding_all
    exact EigVec.congr (v' := Y.mj.eW i y)
      (eigVec_loc L (eigVec_eW_of_hkDat_good_index l i σ k Q α Rr
        (hkDat_of_hkDat_datL L l hd) hσ y hy)) (hY.eW i y)
end GlobalTheory.HeightCounting.Fin3
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtTie
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FunObj.SqNum GlobalTheory.SignedHC
section Arith
variable {D : D7}
end Arith
theorem wt_tie_alt (h : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt) : _root_.GlobalTheory.BigTop.Fun.LeafWeightBound @Comparison₂ := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨0, fun CF _ => ⟨e, he, fun eps h1 h2 => ?_⟩⟩
  obtain ⟨K, hK⟩ := h eps h1 h2
  refine ⟨K, fun Fm CH hc hL _ => ⟨10, fun C hC => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := hK Fm CH hc hL
  refine ⟨x0, fun x hx hle i p hp d hd => ?_⟩
  have hs := hx0 x hx hle i p hp
  obtain ⟨-, a, ha⟩ := hd
  have hw : d.Bw = (maxWt _ 1 : ℝ) := ha.sq.weight
  obtain ⟨w1, w2, hb⟩ := maxWt_le hs
  have eb : p.Z.b = (Fm.L x i).sc.b := rfl
  show 1 ≤ d.Bw ∧ d.Bw ≤ C * p.Z.b ∧ Real.log d.Bw ≤ C * Real.log p.Z.b
  rw [hw, eb]
  have hb0 : 0 < (Fm.L x i).sc.b := by linarith
  have l10 : Real.log 10 ≤ Real.log (Fm.L x i).sc.b := Real.log_le_log (by norm_num) (by linarith)
  have l0 : 0 ≤ Real.log (Fm.L x i).sc.b := l10.trans' (Real.log_nonneg (by norm_num))
  refine ⟨w1, w2.trans (by nlinarith), ?_⟩
  calc Real.log (maxWt _ 1 : ℝ) ≤ Real.log (10 * (Fm.L x i).sc.b) := Real.log_le_log (by linarith) w2
    _ = Real.log 10 + Real.log (Fm.L x i).sc.b := Real.log_mul (by norm_num) hb0.ne'
    _ ≤ 2 * Real.log (Fm.L x i).sc.b := by linarith
    _ ≤ C * Real.log (Fm.L x i).sc.b := by nlinarith
end GlobalTheory.BigTop.Fun
end
end
end
