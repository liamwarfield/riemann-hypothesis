module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonvanishingFromTruePack
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealAtCols
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremFromPublishedResultsAltAltAltAltAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremPublishedResultsFinal
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePackOfBWit
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAtOfBWit
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DataOfBWit
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DataOfBWit
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TopVal.TwSet
section Gen
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix _root_.Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.SeeSaw.TopLevel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end Gen
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Args
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
end Args
set_option maxHeartbeats 2000000 in
theorem data_of_bWit_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (hw : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX = 1 ∧ (∀ t, (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Q t = q.w.I.Q ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) ∧
      ∀ g, g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)).H ↔ ∀ PP (h : PP ∈ (q.B.primes q.w.px).vGs) (h' : PP ∈ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg),
        g ⟨PP, h'⟩ ∈ (GlobalTheory.Mem.Col2.TC.Ps q.w.I ⟨PP, h⟩).H := by
  have hu := _root_.GlobalTheory.MiS.Check.used_all_alt (_root_.GlobalTheory.Fam.packB_alt b)
  obtain ⟨x, a, ax, y, -, -, -, -, -, -, -, -, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  subst hx
  obtain ⟨-, -, hl, -⟩ := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y → (∀ t, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) (k.P.I.tup t)) →
      (letI := k.B.alg
      k.B.Q.Rl.toRealDat.βX = 1 ∧ (∀ t, k.B.Q.Rl.toRealDat.Q t = q.w.I.Q (k.P.I.tup t)) ∧
      ∀ g, g ∈ (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true).H ↔
        ∀ PP (h : PP ∈ (q.B.primes q.w.px).vGs) (h' : PP ∈ k.B.Q.Rl.toRealDat.Pg),
        g ⟨PP, h'⟩ ∈ (GlobalTheory.Mem.Col2.TC.Ps q.w.I ⟨PP, h⟩).H) := by
    intro k hk
    subst hk
    intro hu
    letI := a.x.grp
    letI := a.x.fin
    letI := a.x.alg
    refine ⟨a.x.pins.keep.beta.2, fun t => ?_, fun g => ?_⟩
    · have h1 := eq_of_heq (hl _ (hu t)).1
      exact (congrArg a.x.R.Q (a.x.Y.tupT_tup t)).symm.trans h1
    · exact (by with_unfolding_all exact (lev_twArgs a g :))
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq hu
set_option maxHeartbeats 2000000 in
theorem levS_iff_cls_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X'), g ∈ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) ↔ ∃ κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1 := by
  intro hL p K q c b hw u t h g
  obtain ⟨hOk, ⟨hPins⟩, -, -, l0, tw, he, ht, -, -, s⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hw
  obtain ⟨hβ, hQ, hH⟩ := _root_.GlobalTheory.TopVal.TwSet.data_of_bWit_alt q b hw
  have hPg : (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg = (q.B.primes q.w.px).vGs := Finset.ext (_root_.GlobalTheory.Fam.BundleLev.levTrue_packB_of_bWit q b hw).2.1
  have key : ∀ (Tw : TwForms (q.w.D q.Z)) (t' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes (_root_.GlobalTheory.Fam.packB_alt b).R.T.n.tp (_root_.GlobalTheory.Fam.packB_alt b).R.T.cols Tw),
      Tw = GlobalTheory.Mem.Col2.TC.tw q.w.I q.w.l l0 q.Z → HEq t' tw →
      (g ∈ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) ↔
        ∃ κ : (t'.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1) := by
    rintro _ t' rfl rfl
    exact mem_levS_of_reads q.w.I hOk hPins q.w.l q.Z _ _ (s.what₂ u _ h) _ hβ _ _ hPg (hQ t) _ hH _ _ _ g
  exact key _ _ he ht
end GlobalTheory.TopVal.TwSet
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DataOfBWitStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_iff_twisted_class_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X'), g ∈ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) ↔ ∃ κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1 := by
  first | exact @_root_.GlobalTheory.TopVal.TwSet.levS_iff_cls_alt | exact _root_.GlobalTheory.TopVal.TwSet.levS_iff_cls_alt | (intros; apply _root_.GlobalTheory.TopVal.TwSet.levS_iff_cls_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevGBaseOfBWit
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevGBaseOfBWit
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.BaseLevel
open NumberField IsDedekindDomain GlobalTheory.Mem.Col2 _root_.Formalism.L2.Forms GlobalTheory.SeeSaw GlobalTheory.SeeSaw.TopLevel
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
set_option maxHeartbeats 2000000 in
theorem topLev_of_btw_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x)
    {u : D.what₂.Word} (K₀ : ClsPTied u) (h : PairDataBaseTupleLevelEqualsClassLevel x K₀) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (ht : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = D.what₂.mu0) :
    GlobalTheory.Core.Rk.Top.TopLev K₀ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t))
      (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y → ∀ t : k.P.T, k.P.I.tup t = D.what₂.mu0 →
      letI := k.B.alg
      GlobalTheory.Core.Rk.Top.TopLev K₀
        (levS _ k.B.Q.Rl.toRealDat.βX (datXP k.B.Q.Rl.toRealDat (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) t))
        (levChi _ k.B.Q.Rl.toRealDat.βX (datXP k.B.Q.Rl.toRealDat (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) t)) := by
    intro k hk
    subst hk
    exact h
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t ht
set_option maxHeartbeats 2000000 in
theorem pairDataBaseTupleLevel_eq_classLevel_of_stdF {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K)
    (a : R3.TwArgs q.O.ex q.x.what₂) (v : q.B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((q.w.D q.Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (q.w.D q.Z) v Ch chOf) (hF : TC.StdF q.w.I q.w.l q.Z v F) : PairDataBaseTupleLevelEqualsClassLevel (O := q.O) a.x F.clsP := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F' cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  intro t ht
  have hT' : Y.tup = q.x.what₂.r.Y.tup := eq_of_heq htup
  have z := q.x.what₂.r.z.lev
  have hix : R3.ixOf q.w.I _ t = q.w.I.mu0 :=
    (q.x.what₂.r.tup_ix t).symm.trans ((congrFun hT' t).symm.trans ht)
  have hQ : q.x.what₂.r.z.R.Q t = ∅ := (z.Q t).trans ((congrArg q.w.I.Q hix).trans q.w.I.twistPrimes_reference_tuple_eq_empty)
  have hc := z.is.chi
  rw [z.C] at hc
  exact topLev_levPOf q.w.I q.w.l q.Z q.w.ok q.w.pins v F hF r_le_X q.x.what₂.r.z.R.Pg (q.x.what₂.r.z.R.Q t) q.x.what₂.r.z.R.βX
    z.Pg hQ z.beta.2 q.x.what₂.r.z.R.eG q.x.what₂.r.z.idG q.x.what₂.r.z.R.chi (q.x.what₂.r.z.R.xiR t) hc
set_option maxHeartbeats 2000000 in
theorem levG_base_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = (q.w.D q.Z).what₂.mu0 → LevG ((_root_.GlobalTheory.Fam.packB_alt b).R.T.cols.forms u).clsP.toG 1 (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  intro hL p K q c b hw u t ht
  obtain ⟨-, -, -, ⟨hC⟩, -⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hw
  have hx : hw.a.x = hw.x := eq_of_heq hw.ax
  exact (levG_one_iff _ _ _).2 (_root_.GlobalTheory.Fam.BaseLevel.topLev_of_btw_alt b hw.x hw.y _ (hx ▸ _root_.GlobalTheory.Fam.BaseLevel.pairDataBaseTupleLevel_eq_classLevel_of_stdF q hw.a u _ (hC u)) t ht)
end GlobalTheory.Fam.BaseLevel
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevGBaseOfBWitStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_group_reference_tuple_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = (q.w.D q.Z).what₂.mu0 → LevG ((_root_.GlobalTheory.Fam.packB_alt b).R.T.cols.forms u).clsP.toG 1 (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  first | exact @_root_.GlobalTheory.Fam.BaseLevel.levG_base_of_bWit_alt | exact _root_.GlobalTheory.Fam.BaseLevel.levG_base_of_bWit_alt | (intros; apply _root_.GlobalTheory.Fam.BaseLevel.levG_base_of_bWit_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevReadOfBWit
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevReadOfBWit
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TopVal.LevTw
section Gen
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV Formalism.UG _root_.Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
end Gen
section Cols
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV Formalism.UG _root_.Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.AdT Matrix GlobalTheory.EX
open Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
variable {B : Base} {X : PreX B.toPre} (I : TC B X)
end Cols
section Pack
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem levRead_packB_of_bWit {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (hw : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    LevRead q.w.I q.w.l q.Z (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).toLevCh (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup := by
  obtain ⟨x, a, ax, y, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  have h0 := levRead_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a
  have h1 : LevRead q.w.I q.w.l q.Z x.R.toLevCh (x.R.toRealDat.levR x.F.lv2 true) x.Y.tup := by
    subst hx
    exact h0
  have h2 : (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => LevRead q.w.I q.w.l q.Z k.B.Q.Rl.toRealDat.toLevCh
      (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) k.P.I.tup) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := by
    rw [y.eq]
    exact h1
  exact h2
set_option maxHeartbeats 1000000 in
theorem levIs_of_bWit_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (hw : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T)
    (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) :
    LevIs ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev
      (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t))
      (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  have hxi : b.R.T.n.tp.xi = q.w.I.xi := (congrArg (fun s => s.2.xi) hw.recPin.s.chr).trans q.x.n.xi
  obtain ⟨l0, s, he, hs, -, -, hP⟩ := (_root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hw).2.2.2.2
  have key : ∀ (Tw : TwForms (q.w.D q.Z)) (s' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes b.R.T.n.tp b.R.T.cols Tw), Tw = TC.tw q.w.I q.w.l l0 q.Z →
      HEq s' s → LevIs (s'.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev
        (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t))
        (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
    rintro _ s' rfl rfl
    refine _root_.GlobalTheory.TopVal.LevTw.levRead_packB_of_bWit q b hw t h _ _ _ _ _ (fun v hv => hv.imp id fun hv => ?_) (s'.pt.chi_fin u _ h) (hP.what₂ u _ h)
    have h1 := (s'.ch.Q_iff _ v).1 hv
    unfold Formalism.L2.Host.TupTied.InQ' at h1
    rw [hxi] at h1
    exact underQ_of_ram q.w.ok _ v h1
  exact key _ _ he hs
theorem levChi_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X') (κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) g = star ((((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.chi κ : ℂˣ) : ℂ) :=
  fun q _ b hw u t h g κ hm => (_root_.GlobalTheory.TopVal.LevTw.levIs_of_bWit_alt q b hw u t h).2 g κ hm
end Pack
end GlobalTheory.TopVal.LevTw
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevReadOfBWitStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_character_twisted_class_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X') (κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) g = star ((((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.chi κ : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.TopVal.LevTw.levChi_of_bWit_alt | exact _root_.GlobalTheory.TopVal.LevTw.levChi_of_bWit_alt | (intros; apply _root_.GlobalTheory.TopVal.LevTw.levChi_of_bWit_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqZeroOfPkAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqZeroOfPkAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal.Inj
open NumberField IsDedekindDomain
open scoped TensorProduct
theorem eq_zero_of_pkAt_eq_zero_uni {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : Col2.TC B X} {l : I.Laws} {Z : Col2.TC.Later B (I.cols l)}
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
    (gP : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t)
    (hz : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x g = 0) : x = 0 := by
  exact eq_zero_of_hasMat (_root_.GlobalTheory.Fam.pk_z W) W.Q.charW.base.models.jX gP t x hz
set_option maxHeartbeats 1000000 in
theorem eq_zero_of_isRes_pkAt_eq_zero : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) (x : (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A.fam.amb.FR t), GlobalTheory.TopVal.IsRes φ x → (∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → GlobalTheory.TopVal.IsUni q.B y → _root_.GlobalTheory.TopVal.packageAtPoint (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) t x g = 0) → ∀ d, GlobalTheory.TopVal.val φ d = 0 := by
  intro hL p K q c b hw t φ x hx hz d
  have hx0 : x = 0 := _root_.GlobalTheory.TopVal.Inj.eq_zero_of_pkAt_eq_zero_uni (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b)
    (Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z).2.1 t x hz
  subst hx0
  obtain ⟨x, a, ax, y, -⟩ := hw
  have e : a.x = x := eq_of_heq ax
  subst e
  have h0 := eq_zero_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y →
      ∀ (s : k.P.T) (φ : Frm q.w.I (k.P.I.tup s)), IsRes φ (0 : k.P.A3.A.fam.amb.FR s) → φ = 0 := by
    intro k hk
    subst hk
    exact h0
  rw [key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t φ hx]
  rfl
end GlobalTheory.TopVal.Inj
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqZeroOfPkAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pk_at_vanishing_of_is_uni : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) (x : (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A.fam.amb.FR t), GlobalTheory.TopVal.IsRes φ x → (∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → GlobalTheory.TopVal.IsUni q.B y → _root_.GlobalTheory.TopVal.packageAtPoint (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) t x g = 0) → ∀ d, GlobalTheory.TopVal.val φ d = 0 := by
  first | exact @_root_.GlobalTheory.TopVal.Inj.eq_zero_of_isRes_pkAt_eq_zero | exact _root_.GlobalTheory.TopVal.Inj.eq_zero_of_isRes_pkAt_eq_zero | (intros; apply _root_.GlobalTheory.TopVal.Inj.eq_zero_of_isRes_pkAt_eq_zero <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecValPackB
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecValPackB
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix
noncomputable section
namespace GlobalTheory.TopVal.OneForm
section Generic
variable {D : D7} {O : Obj D} {c : ℝ}
set_option maxHeartbeats 800000 in
theorem row_of_btw_alt (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T)
    (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → D.what₂.LL)
    (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → D.what₂.LL) (hF : HEq F F') :
    ∃ (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = x.Y.tup s ∧
      HEq ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
      HEq ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 D (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) (x.Y.jA s v) := by
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y → ∀ (t : k.P.T)
      (F : Fin ((k.P.A3.side3 k.P.Ps k.P.ψs k.P.Zs).nV t) → D.what₂.LL)
      (F' : Fin ((k.B.Q.F.fc (k.B.Q.Rl.toCx3 k.B.Q.F).zs).Df1.nV t) → D.what₂.LL), HEq F F' →
      ∃ (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL), k.P.I.tup t = x.Y.tup s ∧
        HEq (k.B.Q.F.eV (k.B.Q.Rl.toCx3 k.B.Q.F).zs t F') (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
        HEq (k.P.I.jA t ((rV0 D k.P.A3.A k.P.Ps k.P.ψs t).mulVec F)) (x.Y.jA s v) := by
    intro k hk
    subst hk
    intro t F F' hF
    have e : F = F' := eq_of_heq hF
    subst e
    change x.T at t
    change (Fin ((x.A3.A.fam.R t).nV (x.A3.A.fam.lvl x.F.P1 x.F.ψ1)) → D.what₂.LL) at F
    refine ⟨t, (rV0 D x.A3.A x.F.P1 x.F.ψ1 t).mulVec F, rfl, heq_of_eq ?_, HEq.rfl⟩
    have hOk := y.intersectionNumber_baseChange.ok
    have hb : BlockHyp (x.A3.A.fam.R t) (x.A3.A.fam.lvl x.F.P1 x.F.ψ1) x.A3.A.fam.v0 1 :=
      ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
    unfold R3.rowForm rV0
    show (x.A3.A.fam.R t).S.basis.equivFun.symm (((x.A3.A.fam.R t).vE (x.A3.A.fam.lvl x.F.P1 x.F.ψ1)) *ᵥ F) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, BlockDat.lf_lvl_vE hb]
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t F F' hF
end Generic
section Rows
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl
end Rows
set_option maxHeartbeats 800000 in
theorem exists_frm_isRes_recVal {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) (x : R3.TwIn q.O.ex)
    (a : R3.TwArgs q.O.ex q.x.what₂) (ax : HEq a.x x) (rx : Bl.RXs q.x.what₂) (s : x.T)
    (v : Fin (rDim (q.w.D q.Z) x.A3.A x.F.P1 x.F.ψ1 s) → (q.w.D q.Z).what₂.LL) :
    ∃ φ : Frm q.w.I (x.Y.tup s), IsRes φ (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
      ∀ u, RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u (x.Y.tup s) φ (x.Y.jA s v) := by
  have e : a.x = x := eq_of_heq ax
  subst e
  obtain ⟨s', v', k1, k2, k3⟩ := row_of_args (w := q.w) (Z := q.Z) (ex := q.O.ex) (t := q.x.what₂) a s v
  exact one_form_congr (I := q.w.I) (l := q.w.l) (Z := q.Z) k1 k2 k3 (one_form_rows rx s' v')
set_option maxHeartbeats 800000 in
theorem recVal_packB_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → (q.w.D q.Z).what₂.LL) (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → (q.w.D q.Z).what₂.LL), HEq F F' → ∃ φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t), GlobalTheory.TopVal.IsRes φ ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') ∧ ∀ u, GlobalTheory.TopVal.RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) φ ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 (q.w.D q.Z) (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) := by
  intro hL p K q c b hb hR t F F' hF
  obtain ⟨rx⟩ := hR
  obtain ⟨s, v, h1, h2, h3⟩ := _root_.GlobalTheory.TopVal.OneForm.row_of_btw_alt b hb.x hb.y t F F' hF
  exact one_form_congr (I := q.w.I) (l := q.w.l) (Z := q.Z) h1 h2 h3 (_root_.GlobalTheory.TopVal.OneForm.exists_frm_isRes_recVal q hb.x hb.a hb.ax rx s v)
end GlobalTheory.TopVal.OneForm
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecValPackBStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_form_exists_heq_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (F : Fin (((_root_.GlobalTheory.Fam.packB_alt b).P.A3.side3 (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs (_root_.GlobalTheory.Fam.packB_alt b).P.Zs).nV t) → (q.w.D q.Z).what₂.LL) (F' : Fin (((_root_.GlobalTheory.Fam.packB_alt b).Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs).Df1.nV t) → (q.w.D q.Z).what₂.LL), HEq F F' → ∃ φ : GlobalTheory.TopVal.Frm q.w.I ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t), GlobalTheory.TopVal.IsRes φ ((_root_.GlobalTheory.Fam.packB_alt b).Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace (_root_.GlobalTheory.Fam.packB_alt b)).zs t F') ∧ ∀ u, GlobalTheory.TopVal.RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) φ ((_root_.GlobalTheory.Fam.packB_alt b).P.I.jA t ((rV0 (q.w.D q.Z) (_root_.GlobalTheory.Fam.packB_alt b).P.A3.A (_root_.GlobalTheory.Fam.packB_alt b).P.Ps (_root_.GlobalTheory.Fam.packB_alt b).P.ψs t).mulVec F)) := by
  first | exact @_root_.GlobalTheory.TopVal.OneForm.recVal_packB_alt | exact _root_.GlobalTheory.TopVal.OneForm.recVal_packB_alt | (intros; apply _root_.GlobalTheory.TopVal.OneForm.recVal_packB_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsJValSmul
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsJValSmul
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TopVal.Scalar
section Alg
open Formalism.BasicNotions _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms Matrix GlobalTheory.CoefSpace
variable {ι : Type} [Fintype ι] {n : ℕ}
end Alg
section Group
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.DefLift GlobalTheory.CoefSpace GlobalTheory.DefiniteMult Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}
end Group
end GlobalTheory.TopVal.Scalar
end
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.TopVal.exists_jVal_smul_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws} {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Formalism.L2.Forms.gramP (I.rec7 l Z) = 1 → ∀ (u : B.Word) (cv : GlobalTheory.TopVal.Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W), _root_.GlobalTheory.TopVal.ValEqvAlt W cv → cv ≠ 0 → ∀ j₀, GlobalTheory.Core.Rk.Top.IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j₀ → ∃ a : ℂ, a ≠ 0 ∧ _root_.GlobalTheory.TopVal.ValuationCompatible W cv (a • j₀) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u cv hcv h0 j₀ hJ
  have hm := W.Q.charW.base.models
  have hr := hJ.range
  rw [GlobalTheory.Core.Rk.Top.sgT_eq_perIn_sgT I l Z u I.mu0] at hr
  have e : (fun τ => ((GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  obtain ⟨a, ha, h⟩ := GlobalTheory.TopVal.Scalar.exists_scalar (D := I.rec7 l Z) (M := (_root_.GlobalTheory.Fam.pk_z W).MX) (θ := (_root_.GlobalTheory.Fam.pk_z W).θ) (c := (_root_.GlobalTheory.Fam.pk_z W).cX)
    (pr := (_root_.GlobalTheory.Fam.pk_z W).prX) hm.inf (GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) _) hm.cX hm.prX
    (Formalism.L2.Forms.rankP (I.rec7 l Z)) B.wts.sgTrue B.embLL B.fields.emb
    (fun τ x => DFunLike.congr_fun (B.fields_embC τ) x) cv hcv h0 _ _ _ e j₀ hJ.inj hr hJ.eqv
  refine ⟨a, ha, fun w v => (h w v).trans ?_⟩
  delta GlobalTheory.TopVal.pairVal
  rw [LinearMap.smul_apply]
  erw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rfl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsJValSmulStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_gram_family_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws} {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Formalism.L2.Forms.gramP (I.rec7 l Z) = 1 → ∀ (u : B.Word) (cv : GlobalTheory.TopVal.Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W), _root_.GlobalTheory.TopVal.ValEqvAlt W cv → cv ≠ 0 → ∀ j₀, GlobalTheory.Core.Rk.Top.IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j₀ → ∃ a : ℂ, a ≠ 0 ∧ _root_.GlobalTheory.TopVal.ValuationCompatible W cv (a • j₀) := by
  first | exact @_root_.GlobalTheory.TopVal.exists_jVal_smul_alt | exact _root_.GlobalTheory.TopVal.exists_jVal_smul_alt | (intros; apply _root_.GlobalTheory.TopVal.exists_jVal_smul_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkValOfBWit
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkValOfBWit
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Col GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top GlobalTheory.TopVal
namespace GlobalTheory.TopVal
set_option maxHeartbeats 1000000 in
theorem pkVal_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.x.what₂.r.z.Std → ∃ cv, _root_.GlobalTheory.TopVal.ValEqvAlt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv ∧ _root_.GlobalTheory.TopVal.PackageValuation (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv := by
  intro hL p K q c b hw hs
  have hx : hw.a.x = hw.x := eq_of_heq hw.ax
  have h1 : DatVal q.w.I q.w.l q.Z (aK := hw.x.alg) hw.x.R.toRealDat hw.x.Y.tup := by
    rw [← hx]
    exact datVal_twArgs K _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ hw.a hs
  have h2 : (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => DatVal q.w.I q.w.l q.Z (aK := k.B.alg) k.B.Q.Rl.toRealDat k.P.I.tup) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := by
    rw [hw.y.eq]
    exact h1
  obtain ⟨cv, h3, h4⟩ := h2
  exact ⟨cv, h3, h4⟩
end GlobalTheory.TopVal
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkValOfBWitStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valEqv_of_bWit_std : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.x.what₂.r.z.Std → ∃ cv, _root_.GlobalTheory.TopVal.ValEqvAlt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv ∧ _root_.GlobalTheory.TopVal.PackageValuation (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) cv := by
  first | exact @_root_.GlobalTheory.TopVal.pkVal_of_bWit_alt | exact _root_.GlobalTheory.TopVal.pkVal_of_bWit_alt | (intros; apply _root_.GlobalTheory.TopVal.pkVal_of_bWit_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAtOfBWit
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal
section True
open GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
theorem to_map_pr_x_eq_pk_at (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t) (g : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (hg : g ∈ GfC (I.rec7 l Z).sp.X')
    (v : SmT (_root_.GlobalTheory.Fam.pk_z W).MX) :
    (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x)) v g = (_root_.GlobalTheory.Fam.pk_z W).prX (_root_.GlobalTheory.TopVal.packageAtPoint W t x g) v := by
  have h1 : (_root_.GlobalTheory.Fam.pk_z W).cX.ρ g⁻¹ = 1 := W.Q.charW.base.models.cX.1 _ (inv_mem hg)
  show (_root_.GlobalTheory.Fam.pk_z W).prX ((_root_.GlobalTheory.Fam.pk_z W).cX.ρ g⁻¹ (_root_.GlobalTheory.TopVal.packageAtPoint W t x g)) v = _
  rw [h1]
  rfl
set_option maxHeartbeats 1000000 in
theorem exists_is_j_pair_val_of_vanishing (hg : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (u : B.Word) (cv : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (hE : _root_.GlobalTheory.TopVal.ValEqvAlt W cv)
    (hP : _root_.GlobalTheory.TopVal.PackageValuation W cv)
    (hi : ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x →
      (∀ g y, HasMat g y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x g = 0) → ∀ d, val φ d = 0) :
    ∃ j, IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j ∧ ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x → ∀ d v,
      (_root_.GlobalTheory.Fam.pk_z W).prX (cv (val φ d)) v = pairVal B (j v) (val φ d) := by
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.SeeSaw.exists_isJ_of_par (GlobalTheory.SeeSaw.sg_trueColumns I l Z u) (_root_.GlobalTheory.Fam.pk_z W).MX rfl
  by_cases h0 : cv = 0
  · refine ⟨j₀, hj₀, fun t φ x hx d v => ?_⟩
    have hz := hi t φ x hx (fun g y h1 h2 => (hP t φ x hx g y h1 h2).trans (by rw [h0]; rfl)) d
    rw [hz, map_zero, map_zero, LinearMap.zero_apply]
    unfold pairVal
    rw [Submodule.coe_zero, map_zero, map_zero]
  · obtain ⟨a, ha, hJ⟩ := _root_.GlobalTheory.T.unit_gram_family_property_alt W hg u cv hE h0 j₀ hj₀
    exact ⟨a • j₀, isJ_smul hj₀ ha, fun t φ x _ d v => hJ _ v⟩
set_option maxHeartbeats 1000000 in
theorem reads_pk_alt (hOk : I.Ok) (hC : I.StdC l Z W.R.T.cols) (hW : _root_.GlobalTheory.AdForm.TwStdAlt W) (u : B.Word)
    (cv : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (hP : _root_.GlobalTheory.TopVal.PackageValuation W cv) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ))
    (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t) (hx : IsRes φ x)
    (hV : ∀ d v, (_root_.GlobalTheory.Fam.pk_z W).prX (cv (val φ d)) v = pairVal B (j v) (val φ d))
    (G : (I.rec7 l Z).what₂.Amb (W.P.I.tup t)) (hG : RecVal u (W.P.I.tup t) φ G) :
    _root_.GlobalTheory.Fam.ReadsCoefficients W u j 1 (W.P.I.tup t) G ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x))) := by
  refine _root_.GlobalTheory.TopVal.reads_of_pairVal W hC hW u j _ φ G hG _ fun g y pt v hy hp => ?_
  refine (_root_.GlobalTheory.TopVal.to_map_pr_x_eq_pk_at W t x g hy.1 v).trans ?_
  rw [hP t φ x hx g y hy hp.uni, GlobalTheory.T.decoratedLatticeOfAdelicMatrix_eq_rowPoint I hOk _ y pt hp]
  exact hV _ v
end True
set_option maxHeartbeats 2000000 in
theorem exists_read_at_pack_b_of_b_wit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt (_root_.GlobalTheory.Fam.packB_alt b) u j 1 := by
  intro hL p K q c b hW ⟨rx⟩ u
  obtain ⟨hOk, ⟨hPins⟩, -, ⟨hC⟩, hTS⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hW
  have hg := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords q.w.I hOk hPins q.w.l q.Z).2.1
  obtain ⟨cv, hE, hP⟩ := _root_.GlobalTheory.T.exists_valEqv_of_bWit_std q b hW rx.std
  obtain ⟨j, hJ, hV⟩ := _root_.GlobalTheory.TopVal.exists_is_j_pair_val_of_vanishing (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) hg u cv hE hP (_root_.GlobalTheory.T.pk_at_vanishing_of_is_uni q b hW)
  refine ⟨j, hJ, one_mem _, fun t => ⟨⟨fun h => _root_.GlobalTheory.T.level_group_reference_tuple_alt q b hW u t h,
    fun h => levG_one _ (_root_.GlobalTheory.T.mem_level_iff_twisted_class_alt q b hW u t h) (_root_.GlobalTheory.T.level_character_twisted_class_alt q b hW u t h)⟩, fun F F' hF => ?_⟩⟩
  obtain ⟨φ, hφ, hR⟩ := _root_.GlobalTheory.T.one_form_exists_heq_alt q b hW ⟨rx⟩ t F F' hF
  exact _root_.GlobalTheory.TopVal.reads_pk_alt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) hOk hC hTS u cv hP j t φ _ hφ (hV t φ _ hφ) _ (hR u)
end GlobalTheory.TopVal
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAtOfBWitStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_read_at_packB_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt (_root_.GlobalTheory.Fam.packB_alt b) u j 1 := by
  first | exact @_root_.GlobalTheory.TopVal.exists_read_at_pack_b_of_b_wit | exact _root_.GlobalTheory.TopVal.exists_read_at_pack_b_of_b_wit | (intros; apply _root_.GlobalTheory.TopVal.exists_read_at_pack_b_of_b_wit <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkHypOfReal
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.PkOf
section Heq
open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef
variable {D : D7}
end Heq
end GlobalTheory.Fam.PkOf
namespace GlobalTheory.Fam
theorem pkHyp_of_real_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin W.R W.S W.Q) → (∀ u, Formalism.L2.SG.ColDict.LevelMatch W.S.X (W.S.tr u) W.S.Y.hK) → GlobalTheory.MiS.DcPtG W.P → _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx W.Q → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation W.Q → _root_.Formalism.IndefR.IndefiniteRealisationExtends W.Q → _root_.Formalism.IndefR.IndefiniteRealisationRecursion W.Q → W.Q.Rl.toRealDat.ExAt → Formalism.IndefR.Links.PrimRows3 W.Q.Rl W.Q.F → W.P.A3.fam3.TypesSep3 → (∃ s, W.P.A3.fam3.Ok3 s) → GlobalTheory.Core.Mi.IdE W.S.X → GlobalTheory.Count.GapGe W.S.X.B (100 * (B.R.r : ℝ) ^ 4) → Formalism.L2.SG.PackageTie2.FinX W.S.Y → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap (I.rec7 l Z) → _root_.GlobalTheory.Fam.ValidRealPackage W → _root_.GlobalTheory.Fam.GeometricFamilyConditions W → _root_.GlobalTheory.Fam.PackageHypotheses W := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hJ hLM hDc hFr hPins hSee hRec hEx hPrim hTS hOk3 hIdE hGap hFinX hNG hTW hTQ
  have hC3 := Formalism.IndefR.Links.RealDat3.characterisation_of_weak W.Q.charW hEx
  have hU : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 _ (W.P.I.tup t) := by
    apply Formalism.L2.DIV.tupAllUsed_of_cover
    intro t
    have hmu : W.Q.Rl.mu = W.P.S0.μ :=
      GlobalTheory.Fam.PkOf.mu_of_heq (congrArg (fun Z => W.P.A3.side3 W.P.P0 W.P.ψ0 Z) W.Q.zs) W.Q.s0
    rcases W.Q.charW.tup.mu_used t with h | ⟨w, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨(I.rec7 l Z).plEq.symm w, ?_⟩
      show t = W.P.S0.μ ((I.rec7 l Z).plEq ((I.rec7 l Z).plEq.symm w))
      rw [← hmu, Equiv.apply_symm_apply]
      exact h.symm
  refine ⟨⟨⟨hJ, hLM, hDc, hC3, W.Q.frames hFr⟩, hPins, hSee, hU, hIdE, hGap, hFinX⟩, ?lev, hEx, hRec.hTop, hNG, ?fin, ?sel, ?aa⟩
  case lev =>
    obtain ⟨s, hs⟩ := hOk3
    have hR := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hs hTS W.Q.charW hPrim
    exact ⟨⟨s, hs⟩, hR.ratZ, _, hR.gUnit, hR.gEquiv, hR.h2P, hR.lev0, hR.lev1⟩
  case fin =>
    classical
    have h1 := W.Q.charW.tup.mu_off
    have h2 := W.Q.charW.tup.mu_used
    have : (Set.univ : Set W.P.T) ⊆ insert W.P.A3.A.μ0 (W.Q.Rl.mu '' (W.Q.Rl.twPl : Set _)) := fun t _ => by
      rcases h2 t with h | ⟨w, rfl⟩
      · exact Or.inl h
      · by_cases hw : w ∈ W.Q.Rl.twPl
        · exact Or.inr ⟨w, hw, rfl⟩
        · exact Or.inl (h1 w hw)
    exact Set.finite_univ_iff.1 ((((W.Q.Rl.twPl).finite_toSet.image _).insert _).subset this)
  case sel =>
    rintro PP PP' ⟨t, ht⟩ ⟨t', ht'⟩ hu
    have hs := hTW.ok.sel_ok
    obtain ⟨v, rfl⟩ := GlobalTheory.Fam.PkOf.exists_of_mem_QE ((hTQ.Q t PP).1 ht)
    obtain ⟨v', rfl⟩ := GlobalTheory.Fam.PkOf.exists_of_mem_QE ((hTQ.Q t' PP').1 ht')
    have e1 := congrArg HeightOneSpectrum.asIdeal hu
    have hv : v = v' := by
      apply HeightOneSpectrum.ext
      rw [← hs v, ← hs v']
      exact e1
    rw [hv]
  case aa =>
    intro PP h hmem
    have hcop := (I.rec7 l Z).host.ccK_coprime
    rcases h with ⟨t, ht⟩ | hg | ⟨u, hu⟩
    · apply hPins.qGuard.2 t PP ht
      push_cast
      exact Ideal.mul_mem_left _ _ hmem
    · obtain ⟨plg, iso, -, -, -, -⟩ := hPins.grpRecPin
      set kv := plg.symm ⟨PP, hg⟩ with hkv
      have hPP : ((plg kv : W.Q.Rl.toRealDat.Pg) : Pl (I.rec7 l Z).host.E) = PP := by
        rw [hkv, Equiv.apply_symm_apply]
      have h0 : (((I.rec7 l Z).host.g kv.1 : ℕ) : kP (plg kv).1) = 0 := by
        rw [← map_natCast (iso kv), ZMod.natCast_self, map_zero]
      have hg' : (((I.rec7 l Z).host.g kv.1 : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
        rw [← hPP]
        exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using h0)
      exact GlobalTheory.Fam.PkOf.natCast_not_mem_of_coprime PP
        (hcop _ (by simp [(I.rec7 l Z).host.g_level kv.1])) hg' hmem
    · exact GlobalTheory.Fam.PkOf.natCast_not_mem_of_coprime PP
        (hcop _ (by simp [(I.rec7 l Z).T_level u])) hu hmem
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePackOfBWit
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem truePack_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → _root_.GlobalTheory.Fam.BundlePointConditions b → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b) := by
  intro hL p K q c b hW hX hR
  obtain ⟨hOk, hPins, hTw, hStdC, hTS⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hW
  obtain ⟨hChr, hXi, hQ, hLev, hRec, hRP, hOk3, hIdE, hLM⟩ := _root_.GlobalTheory.T.characters_match_bundle_alt q b hW
  have hTop := _root_.GlobalTheory.T.exists_read_at_packB_of_bWit q b hW hX
  have hTW : _root_.GlobalTheory.Fam.ValidRealPackage (_root_.GlobalTheory.Fam.packB_alt b) := ⟨hOk, hPins, hTw, hStdC, hChr, ⟨1, hTop⟩⟩
  have hTQ : _root_.GlobalTheory.Fam.GeometricFamilyConditions (_root_.GlobalTheory.Fam.packB_alt b) := ⟨hXi, hQ, hTop⟩
  obtain ⟨hRec'⟩ := hRec
  have hPk : _root_.GlobalTheory.Fam.PackageHypotheses (_root_.GlobalTheory.Fam.packB_alt b) := _root_.GlobalTheory.Fam.pkHyp_of_real_alt (_root_.GlobalTheory.Fam.packB_alt b) hR.join hLM hR.dc hR.frames hRP hR.see hRec' hR.ex hR.prim.1 hR.prim.2
    hOk3 hIdE hR.gapS hR.fin hR.gap hTW hTQ
  exact _root_.GlobalTheory.Fam.TruePackAlt.mk _ ⟨hPk, hTW, hTQ, hTS, hLev, ⟨hRec'⟩⟩
end GlobalTheory.Fam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePackOfBWitStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_pack_of_bundle_witness : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → _root_.GlobalTheory.Fam.BundlePointConditions b → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b) := by
  first | exact @_root_.GlobalTheory.Fam.truePack_of_bWit_alt | exact _root_.GlobalTheory.Fam.truePack_of_bWit_alt | (intros; apply _root_.GlobalTheory.Fam.truePack_of_bWit_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PuNZMember
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueDOfTruePack
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.MiTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
open GlobalTheory.MiTop
namespace GlobalTheory.Fam
theorem trueD_of_truePack_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.TruePackAlt W → GlobalTheory.Core.Rk.TrueD D := by
  intro D L hT Gi Gl Kc Yd cX ex W h
  cases h with
  | mk W hA =>
    obtain ⟨hpk, htr, -, -, -, -⟩ := hA
    obtain ⟨hok, ⟨pins⟩, -, ⟨std⟩, -, -⟩ := htr
    refine ⟨_, _, _, _, _, rfl, ⟨⟨hok, pins, W.R.T.cols, std, ?_⟩⟩⟩
    exact
      { toSTies := W.S.toSTies
        hF := hpk.bot.fin
        tr := W.S.tr
        into := W.S.into
        bij := W.S.bij
        lev := W.S.lev
        colPin := W.S.colPin hpk.bot.fin
        inst := W.S.inst
        locTied := W.S.locTied
        pin := hpk.bot.idE }
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PuNZMember
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MiTop
open GlobalTheory.Core.Rk
theorem puNZ_member_alt : GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.MiTop.PuNZ D) := by
  intro hRow hL p hTP
  have hR := fun Cg CT : ℝ => hRow Cg (1 / 4) 3 (1 / 2) CT (by norm_num) (by norm_num)
  choose Cf Af Bf hC hrow using hR
  have h1 := _root_.GlobalTheory.T.exists_constants_for_parameters_scale_bundle hL p (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
  have h2 := _root_.GlobalTheory.T.degHypL_all_linked_good_members hL p (fun C => Af (C.P.CYL + 1) C.CTu) (fun C => Bf (C.P.CYL + 1) C.CTu)
  have h3 : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
      (fun κ _ _ _ _ => Cf (κ.C.P.CYL + 1) κ.C.CTu + 1 ≤ κ.C.CGam) :=
    EvP.mono (fun _ _ _ h _ _ _ _ _ => h) (evP_cGam fun a b => Cf a b + 1)
  refine (((hTP.and h1).and h2).and h3).imp fun κ K β c b hk _ _ h => ?_
  obtain ⟨⟨⟨hT, -, -, -, -, -, -, -, ⟨t1, t2, -, t4, t5⟩, -, hmu, -⟩, hH⟩, hG⟩ := h
  have hD : TrueD β.D := _root_.GlobalTheory.Fam.trueD_of_truePack_alt _ hT
  have hCG : β.O.L.CGam = κ.C.CGam := by rw [← hk.1]; exact β.val.CGam_eq
  have hC1 := hC (κ.C.P.CYL + 1) κ.C.CTu
  refine puNZ_of_sDiag β.O.L hC1 (hCG ▸ hG) hD ⟨t1, t2, hH, t4, t5⟩ hmu fun u => ?_
  exact hrow _ _ _ _ (le_max_left _ _) (le_max_left _ _) β.D _ u (trueE_of_trueD hD)
    ⟨⟨β.O.L, rfl, by rw [hCG]; exact le_max_right _ _, by rw [hCG]; linarith⟩, hmu⟩ ⟨t1, t2, hH, t4, t5⟩
end GlobalTheory.MiTop
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PuNZMemberStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.puNZ_of_truePack : GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.MiTop.PuNZ D) := by
  first | exact @_root_.GlobalTheory.MiTop.puNZ_member_alt | exact _root_.GlobalTheory.MiTop.puNZ_member_alt | (intros; apply _root_.GlobalTheory.MiTop.puNZ_member_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem miStar_row_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hDiag hL p hRX hPt
  have hTrue : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b)) := by
    refine hPt.imp fun κ K β c b _ _ hl hP => ?_
    obtain ⟨q, b', ⟨w⟩, he⟩ := hl
    have key : ∀ s t : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), s = t →
        (_root_.GlobalTheory.Fam.BundlePointConditions t.2.2 → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt t.2.2)) → _root_.GlobalTheory.Fam.BundlePointConditions s.2.2 → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt s.2.2) := by
      rintro _ _ rfl h
      exact h
    exact key ⟨β.D, β.O, b⟩ ⟨q.w.D q.Z, q.O, b'⟩ he (fun hP' => _root_.GlobalTheory.T.true_pack_of_bundle_witness q b' w (hRX K q) hP') hP
  have hPu := _root_.GlobalTheory.T.puNZ_of_truePack hDiag hL p hTrue
  refine ((hPt.and hTrue).and hPu).imp fun κ K β c b _ _ _ H => ?_
  exact _root_.GlobalTheory.T.main_theorem_from_published_results_alt_alt_alt_alt_alt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (_root_.GlobalTheory.Fam.packB_alt b) H.1.2 H.1.1.rS H.2
end GlobalTheory.Fam
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_published_results_final_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  first | exact @_root_.GlobalTheory.Fam.miStar_row_alt_alt | exact _root_.GlobalTheory.Fam.miStar_row_alt_alt | (intros; apply _root_.GlobalTheory.Fam.miStar_row_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundlePackEqAdelicData
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundlePackEqAdelicData
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.PtRowsAt
section General
open NumberField IsDedekindDomain MeasureTheory
open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
section Args
open GlobalTheory.Mem.Top.Bl
variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}
end Args
set_option maxHeartbeats 1000000 in
theorem see_join_alt (h5 : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex)
    (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (S0 : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (hS : S0 = S.toRealSpectralMatching Rc)
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S0) (c : ℝ) (hH : Holds x.R x.F) (hP : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y))
    (h : Placed x.R.toRealDat x.F.lv2 x.Y.eE P S y.tS c) :
    _root_.Formalism.IndefR.IndefiniteRealisationExtends (_root_.GlobalTheory.Mem.R3.realisationOfInput y) ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc S0 (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) := by
  subst hS
  have hSch : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult h5.2.2.2.1 h5.2.2.2.2 D θ V S M J χ μ 𝓕).2
  have hL := (GlobalTheory.T.rowLattices_metrics_agree_of_realGroupTheorems h5 D _ _ _ _ x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.pins hH).1
  exact ⟨(_root_.GlobalTheory.Mem.JPin.seeEx_joinPin_alt _ _ _ _ _ _ _ _ _ x Rc P S y c hH h.1 h.2.1 h.2.2).1,
    (_root_.GlobalTheory.T.join_subspace_real_data_exists_alt _ _ _ _ _ _ _ _ _ x Rc P S y c 1 hSch hP hH hH.ok hH.sep hL
      (rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ x).2.1 h.1 h.2.1 h.2.2).1⟩
end General
section Wit
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} {q : Bl.WPt p.s K} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c}
theorem bundle_P_eq_divisionPair_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : b.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq
theorem dcPtG_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : DcPtG b.P := by
  rw [_root_.GlobalTheory.Fam.PtRowsAt.bundle_P_eq_divisionPair_of_bWit w]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).2.2.1
theorem realPins_of_bWit' (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := (_root_.GlobalTheory.T.characters_match_bundle_alt q b w).2.2.2.2.2.1
theorem framesEx_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx b.B.Q := by
  letI := b.B.alg
  exact _root_.GlobalTheory.FramesAtReal.framesEx_of_realisation_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b.B.Q (_root_.GlobalTheory.Fam.PtRowsAt.realPins_of_bWit' w)
theorem prim_links_and_typesSep3_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3 := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => Formalism.IndefR.Links.PrimRows3 r.B.Q.Rl r.B.Q.F ∧ r.P.A3.fam3.TypesSep3) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    ⟨w.y.intersectionNumber_baseChange.prim, w.y.intersectionNumber_baseChange.sep⟩
  rw [← w.y.eq] at h
  exact h
theorem exAt_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : b.B.Q.Rl.toRealDat.ExAt := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => r.B.Q.Rl.toRealDat.ExAt) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) := exAt_of_args w.a w.x w.ax
  rw [← w.y.eq] at h
  exact h
set_option maxHeartbeats 1000000 in
theorem seeEx_and_joinSI_nonempty_of_bWit (h5 : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    _root_.Formalism.IndefR.IndefiniteRealisationExtends b.B.Q ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S b.B.Q) := by
  obtain ⟨sP, sS, hP, hS, e⟩ := w.s
  have hpin : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisation r.B.Q) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := _root_.GlobalTheory.Fam.PtRowsAt.realPins_of_bWit' w
  rw [w.y.eq] at hpin
  have h0 := placed_of_args w.a w.x w.ax q.saturationAtWeightedPoint.P q.saturationAtWeightedPoint.S q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c ⟨q.saturationAtWeightedPoint.see, q.saturationAtWeightedPoint.ev, q.saturationAtWeightedPoint.rowJ⟩
  have ht : w.y.y.tS = q.saturationAtWeightedPoint.t := eq_of_heq w.pt.1
  have hF : (fun u => (b.R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 :=
    congrArg (fun C : type_of% q.x.col.C => fun u => (C.forms u).to0) w.recPin.s.cols
  have h1 := Placed.of_heq hF hP hS h0
  rw [← ht] at h1
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationExtends r.B.Q ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S r.B.Q)) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    _root_.GlobalTheory.Fam.PtRowsAt.see_join_alt h5 w.x b.R sP sS b.S e w.y.y q.saturationAtWeightedPoint.c w.y.intersectionNumber_baseChange hpin h1
  rw [← w.y.eq] at h
  exact h
end Wit
theorem good_linked_ptR_of_cuspRapidDecay : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) := by
  intro h1 h2 h3 h4 h5 hL p
  obtain ⟨Cl₀, hnc⟩ := GlobalTheory.Core.Rk.HdNc.hd_nc
  refine (_root_.GlobalTheory.T.exists_constants_for_parameters_scale_bundle hL p (fun _ _ => 0) (fun _ _ => max 1801 Cl₀) (fun _ _ => 0)).imp ?_
  rintro κ K β c b - - ⟨q, b', ⟨w⟩, he⟩ ⟨C', Cl, Cg, CT, -, hCl, -, hHD, -, -, hB, hrS⟩
  have key : ∀ s t : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), s = t →
      (Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin t.2.2.R t.2.2.S t.2.2.B.Q) ∧ DcPtG t.2.2.P ∧ _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx t.2.2.B.Q ∧
        _root_.Formalism.IndefR.IndefiniteRealisationExtends t.2.2.B.Q ∧ t.2.2.B.Q.Rl.toRealDat.ExAt ∧
        (Formalism.IndefR.Links.PrimRows3 t.2.2.B.Q.Rl t.2.2.B.Q.F ∧ t.2.2.P.A3.fam3.TypesSep3)) →
      (Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin s.2.2.R s.2.2.S s.2.2.B.Q) ∧ DcPtG s.2.2.P ∧ _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx s.2.2.B.Q ∧
        _root_.Formalism.IndefR.IndefiniteRealisationExtends s.2.2.B.Q ∧ s.2.2.B.Q.Rl.toRealDat.ExAt ∧
        (Formalism.IndefR.Links.PrimRows3 s.2.2.B.Q.Rl s.2.2.B.Q.F ∧ s.2.2.P.A3.fam3.TypesSep3)) := by
    rintro _ _ rfl h
    exact h
  have hsj := _root_.GlobalTheory.Fam.PtRowsAt.seeEx_and_joinSI_nonempty_of_bWit ⟨h1, h2, h3, h4, h5⟩ w
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := key ⟨β.D, β.O, b⟩ ⟨q.w.D q.Z, q.O, b'⟩ he
    ⟨hsj.2, _root_.GlobalTheory.Fam.PtRowsAt.dcPtG_of_bWit w, _root_.GlobalTheory.Fam.PtRowsAt.framesEx_of_bWit w, hsj.1, _root_.GlobalTheory.Fam.PtRowsAt.exAt_of_bWit w, _root_.GlobalTheory.Fam.PtRowsAt.prim_links_and_typesSep3_of_bWit w⟩
  exact ⟨a1, a2, a3, a4, a5, a6,
    GlobalTheory.Core.Rk.finX_of_gap _ b.S.toSTies (gapHyp_of_hd ((le_max_left _ _).trans hCl) hHD),
    hnc _ _ _ _ _ _ _ _ _ ((le_max_right _ _).trans hCl) hHD b.S.X,
    GlobalTheory.Core.Rk.GapOfNodes.harishChandraNodesFarApart_of_cubic_node_gap _ hB, hrS⟩
end GlobalTheory.Fam.PtRowsAt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundlePackEqAdelicDataStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_lines_of_cusp_rapid_decay : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) := by
  first | exact @_root_.GlobalTheory.Fam.PtRowsAt.good_linked_ptR_of_cuspRapidDecay | exact _root_.GlobalTheory.Fam.PtRowsAt.good_linked_ptR_of_cuspRapidDecay | (intros; apply _root_.GlobalTheory.Fam.PtRowsAt.good_linked_ptR_of_cuspRapidDecay <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem miStarRowClosing_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  intro hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hDiag hL p hRX
  exact _root_.GlobalTheory.T.main_theorem_published_results_final_alt_alt hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hDiag hL p hRX
    (_root_.GlobalTheory.T.point_lines_of_cusp_rapid_decay hDSC hHCM hCW hHCF hCusp hL p)
end GlobalTheory
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_published_inputs_variant_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  first | exact @_root_.GlobalTheory.miStarRowClosing_alt_alt | exact _root_.GlobalTheory.miStarRowClosing_alt_alt | (intros; apply _root_.GlobalTheory.miStarRowClosing_alt_alt <;> assumption)
end
end
