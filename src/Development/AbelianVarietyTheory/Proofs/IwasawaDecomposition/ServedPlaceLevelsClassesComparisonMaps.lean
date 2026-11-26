module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComparisonDataStepsNonReferenceTupleStatement
public import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LvSite
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepTiesD
noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv _root_.Formalism.L2.G _root_.Formalism.L2.G.Cmp _root_.Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}


set_option maxHeartbeats 4000000 in
def StepTiesD {i : ℕ} (hi : i + 1 ≤ D.R.m) (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (c : LatCmp D) : Prop :=
  (∀ (β : Fo.Ch) (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F)),
    x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F) →
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) →
    (∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) →
    x ∈ ulocOf Fo β w') ∧
  (∀ (β : Fo.Ch) (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F)), x ∈ ulocOf Fo β w' →
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) ∧
    (∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F)) ∧
  (∀ w' ∈ Fo.bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal) ∧
  cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (i + 1) hi) D.host.E S.B).1 * gramN D (i + 1) hi *
    (reGL (rankN D (i + 1) hi) D.host.E S.B).1 = 1 ∧
  (∀ β, UnitCharacterChartCompatibility hi (Fo.K β).lev (c.embW u w hg) (S.ψ β)) ∧
  (∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((Fo.tw β).ch ((Fo.K β).y cl) : ℂ)) ∧
  Fo.okW w ∧
  ¬ D.what₂.places.resChar w ∣ Fo.T

end GlobalTheory.Mem.Top.KerOne.CertEq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComparisonDataStepsUpToRank
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerTopStepChartConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerTopStepChartConditions
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq

noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq.TopStep

open Formalism _root_.Formalism.L2 _root_.Formalism.L2.G _root_.Formalism.L2.G.Cmp _root_.Formalism.L2.Forms Formalism.UG Formalism.MainNotions.G.CmpJ.PStabEq Matrix
open scoped TensorProduct

section Stab

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}


set_option maxHeartbeats 4000000 in
theorem stab_frB (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (β : Fo.Ch)
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (hT : ¬ D.what₂.places.resChar w ∣ Fo.T)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F))
    (hx : x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F)) :
    x ∈ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β) ↔
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x *
      frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x *
      frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F := by
  have hdual := (GlobalTheory.Port.formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi)
    (gramN_apply D (i + 1) hi) (Fo.K β).lev w').2.1 (GlobalTheory.Port.T_not_mem hg.1 hT w' h)
  have hs : SplitStabL D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h) :=
    splitStabL_of D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h)
      (fun y => (X0.g u w hg).spl_sig w' h y)
      (split_integral_completion D.host.F D.host.E w' ((X0.g u w hg).spl w' h) ((X0.g u w hg).spl_alg w' h)) hdual
      (fun s => S.B_lat β w' h s)
  have key : ∀ y : w'.adicCompletion D.host.F,
      y ∈ (algebraMap (w'.adicCompletionIntegers D.host.F) (w'.adicCompletion D.host.F)).range ↔
        y ∈ w'.adicCompletionIntegers D.host.F :=
    fun y => ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  rw [hs x hx, toFr_apply, mem_range_bc_iff _ (algMapV_injective D.host.F w')]
  simp only [key]

end Stab


set_option maxHeartbeats 4000000 in
theorem stepTies_top : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 = (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQp O hO' hunf E hE u v hg
  intro i hi h
  let F := t.C.forms u
  let dt := GlobalTheory.Port.detTieOf t.full.1.base (F.cls (i+1) hi (Or.inr h)).lev
  let Fo : FormsIn ((w.D Z).fm u) (i + 1) hi := GlobalTheory.Port.formsInOne (F.val (i+1) hi (Or.inr h)) dt
  let dtM : GlobalTheory.Port.MemDt F := ⟨fun j hj h' => GlobalTheory.Port.detTieOf t.full.1.base _, fun j h1 h2 β => GlobalTheory.Port.detTieOf t.full.1.base _⟩
  have hL0 := GlobalTheory.Port.base_lattice_self_dual_of_chain t.C u dtM i hi v hg
  rw [GlobalTheory.Port.formsInMem_top F dtM i hi h] at hL0
  have hL : GlobalTheory.Port.ChartBaseLatticeEqSelfDualAtP u Fo ((w.D Z).what₂.places.resChar v) := hL0
  obtain ⟨Cm, h1, h2, -⟩ := (F.val (i+1) hi (Or.inr h)).de
  obtain ⟨B0, hstd, hB⟩ := GlobalTheory.Port.baseEx_of t.g.herm u v hg Fo Cm h1 h2 hL
  haveI : IsFractionRing ((w.D Z).gat u v hg).O ((w.D Z).gat u v hg).Kf :=
    (((w.D Z).gat u v hg).P.setting (plc t.Gt u v hg)).frac_O
  have hfin := GlobalTheory.Port.chi_fin_top F (i + 1) hi h
  have hrat : Formalism.L2.G.Cmp.ChiRatAll (F.cls (i+1) hi (Or.inr h)).lev (w.D Z).what₂.embLL := by
    obtain ⟨k, hR⟩ := (t.std u).ends (i+1) hi (Or.inr h)
    exact GlobalTheory.ChiRatStd.chiRatAll_of_reads w.I w.ok w.pins w.l Z u w.I.mu0 (i+1) hi (badG (w.D Z)) (fun _ => ())
      _ rfl (fun β => Formalism.MainNotions.G.CmpJ.oneChart (F.cls (i+1) hi (Or.inr h)) β) k hR (fun _ => hfin) ()
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Mem.Top.KerTwPsi.exists_psiTiedJ hi (F.cls (i+1) hi (Or.inr h)).lev
    (Formalism.MainNotions.G.ChartsLv.sameU_of Fo ()) (t.cmp.embW u v hg) hrat hfin
  let S : StepD t.g.herm u v hg Fo :=
    { B := B0
      B_lat := fun _ => hB ()
      ψ := fun _ => ψ
      fin := fun β => GlobalTheory.Port.fin_of Fo β _ }
  have hT : ¬ (w.D Z).what₂.places.resChar v ∣ Fo.T := hg.2.2.2.2.2
  refine ⟨Fo, (inferInstance : Finite Unit), S, ?_, ?_, ?_, hstd, fun _ => hψ, ?_, trivial, hT⟩
  · intro β w' hw x hx hx1 hx2
    exact (GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram (gramN (w.D Z) (i + 1) hi)
      (gramN_apply (w.D Z) (i + 1) hi) (Fo.K β).lev w').2.2 (fun hb => Formalism.L2.G.bad_notOver u v hg w' hb hw)
      (GlobalTheory.Port.T_not_mem hg.1 hT w' hw) ((stab_frB Fo S β w' hw hT x hx).2 ⟨hx1, hx2⟩)
  · intro β w' hw x hx
    have hle := (GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram (gramN (w.D Z) (i + 1) hi)
      (gramN_apply (w.D Z) (i + 1) hi) (Fo.K β).lev w').1 hx
    exact (stab_frB Fo S β w' hw hT x hle.1).1 hle
  · exact Formalism.L2.G.bad_notOver u v hg
  · intro β cl
    exact GlobalTheory.Port.chRat_ofChiD (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1 _ _ _

end GlobalTheory.Mem.Top.KerOne.CertEq.TopStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerTopStepChartConditionsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberFormsLayer_topStep_chart_conditions : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 = (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  first | exact @GlobalTheory.Mem.Top.KerOne.CertEq.TopStep.stepTies_top | exact GlobalTheory.Mem.Top.KerOne.CertEq.TopStep.stepTies_top | (intros; apply GlobalTheory.Mem.Top.KerOne.CertEq.TopStep.stepTies_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerMidStepChartsConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerMidStepChartsConditions
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open _root_.Formalism.L2.Forms _root_.Formalism.L2.G Formalism.UG Matrix
open scoped TensorProduct

section Hyp

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}


set_option maxHeartbeats 2000000 in
theorem stab_iff_frB (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (β : Fo.Ch)
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (hdual : SelfDualAt D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β))
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F))
    (hx : x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F)) :
    x ∈ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β) ↔
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F := by
  have hs : SplitStabL D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β)
      (frB X0 u w hg S.B w' h) :=
    splitStabL_of D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h)
      (fun y => (X0.g u w hg).spl_sig w' h y)
      (split_integral_completion D.host.F D.host.E w' ((X0.g u w hg).spl w' h) ((X0.g u w hg).spl_alg w' h)) hdual
      (fun s => S.B_lat β w' h s)
  have key : ∀ y : w'.adicCompletion D.host.F,
      y ∈ (algebraMap (w'.adicCompletionIntegers D.host.F) (w'.adicCompletion D.host.F)).range ↔
        y ∈ w'.adicCompletionIntegers D.host.F :=
    fun y => ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  rw [hs x hx, toFr_apply, mem_range_bc_iff _ (algMapV_injective D.host.F w')]
  simp only [key]

end Hyp

section Main


set_option maxHeartbeats 8000000 in
theorem stepTiesD_mid : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 + 1 ≤ (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  intro K B f T w _ _ _ Z t Wt nch n Y _ _ O _ _ E _ u v hg i hi hi2
  have h1 : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
  let F := t.C.forms u
  let dt : GlobalTheory.Port.MemDt F :=
    ⟨fun j hj _ => GlobalTheory.Port.detTieOf t.full.1.base _, fun j _ _ β => GlobalTheory.Port.detTieOf t.full.1.base _⟩
  have hB : GlobalTheory.Port.BaseEx t.g.herm u v hg (GlobalTheory.Port.formsInMem F dt i hi) := by
    obtain ⟨Cm, hC1, hC2, -⟩ := F.deC (i + 1) h1 hi2
    exact GlobalTheory.Port.baseEx_of t.g.herm u v hg _ Cm hC1 hC2 (GlobalTheory.Port.base_lattice_self_dual_of_chain t.C u dt i hi v hg)
  have hrat : ∀ β, Formalism.L2.G.Cmp.ChiRatAll ((GlobalTheory.Port.formsInMem F dt i hi).K β).lev (w.D Z).what₂.embLL := by
    rw [GlobalTheory.Port.formsInMem_mid F dt i hi hi2]
    intro β
    obtain ⟨k, hR⟩ := (t.std u).mid (i + 1) h1 hi2
    exact GlobalTheory.ChiRatStd.chiRatAll_of_reads w.I w.ok w.pins w.l Z u w.I.mu0 (i + 1) (le_of_succ_m hi2) _ _ _ rfl
      (F.ch (i + 1) h1 hi2) k hR
      (fun β => GlobalTheory.Port.chi_fin_of_glevH (F.glevC (i + 1) h1 hi2 β) fun a => ((w.D Z).host.g_prime a).ne_zero) β
  have hψ : GlobalTheory.Port.PsiEx (GlobalTheory.Port.formsInMem F dt i hi) (t.cmp.embW u v hg) :=
    GlobalTheory.Port.psiEx_of _ (t.cmp.embW u v hg) (((w.D Z).gat u v hg).P.setting (plc t.Gt u v hg)).frac_O hrat
      (GlobalTheory.Port.finMem_of F dt i hi)
  haveI : ∀ j, Finite (t.C.herm.base.Ch u j) := fun j => t.C.herm.base.ChFin u j
  let S : StepD t.g.herm u v hg (GlobalTheory.Port.formsInMem F dt i hi) :=
    ⟨hB.choose, hB.choose_spec.2, fun β => (hψ β).choose, fun β => GlobalTheory.Port.fin_of _ β _⟩
  refine ⟨GlobalTheory.Port.formsInMem F dt i hi, GlobalTheory.Port.formsInMem_fin F dt i hi, S, ?_⟩
  have hT : ¬ (w.D Z).what₂.places.resChar v ∣ (GlobalTheory.Port.formsInMem F dt i hi).T := by
    rw [GlobalTheory.Port.memberChainForms_levelPrime_eq_member]; exact hg.2.2.2.2.2
  have hbad : ∀ w' ∈ (GlobalTheory.Port.formsInMem F dt i hi).bad,
      (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal := by
    rw [GlobalTheory.Port.formsInMem_bad]; exact Formalism.L2.G.bad_notOver u v hg
  have hre := fun β w' => GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram
    (gramN (w.D Z) (i + 1) hi) (gramN_apply (w.D Z) (i + 1) hi) ((GlobalTheory.Port.formsInMem F dt i hi).K β).lev w'
  refine ⟨fun β w' h x hx ha hb => ?_, fun β w' h x hx => ?_, hbad, hB.choose_spec.1, fun β => (hψ β).choose_spec,
    GlobalTheory.Port.chRat_mem (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1 F dt i hi,
    GlobalTheory.Port.formsInMem_ok F dt i hi v, hT⟩
  · have hTw := GlobalTheory.Port.T_not_mem hg.1 hT w' h
    exact (hre β w').2.2 (fun hb' => hbad w' hb' h) hTw
      ((stab_iff_frB (GlobalTheory.Port.formsInMem F dt i hi) S β w' h ((hre β w').2.1 hTw) x hx).2 ⟨ha, hb⟩)
  · have hTw := GlobalTheory.Port.T_not_mem hg.1 hT w' h
    have hl := (hre β w').1 hx
    exact (stab_iff_frB (GlobalTheory.Port.formsInMem F dt i hi) S β w' h ((hre β w').2.1 hTw) x hl.1).1 hl

end Main

end GlobalTheory.Mem.Top.KerOne.CertEq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerMidStepChartsConditionsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberFormsLayer_midStep_charts_conditions : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 + 1 ≤ (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  first | exact @GlobalTheory.Mem.Top.KerOne.CertEq.stepTiesD_mid | exact GlobalTheory.Mem.Top.KerOne.CertEq.stepTiesD_mid | (intros; apply GlobalTheory.Mem.Top.KerOne.CertEq.stepTiesD_mid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComparisonDataStepsUpToRank
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.ChF _root_.Formalism.L2.G _root_.Formalism.L2.Forms

theorem fillTie_of {D : D7} (Gt : GatTies D) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) (Fl : Fills (D.gat u v hg))
    (hw : ∀ (x : Fin (D.gat u v hg).P.nV) (s : Fin ((D.gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts D,
      ((Fl.w x j s : ℝ)) = wj D j (Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ D j) : FillTie Gt u v hg Fl := by
  intro x s b hb
  have h := hw x s (b + 1) (by simp only [SizeData₂.lifts, Finset.mem_Icc]; omega)
  have e1 : wj D (b + 1) (Gt.gat_pos u v hg ⟨x, s⟩) = (((D.hc (Gt.gat_pos u v hg ⟨x, s⟩)).e ⟨b, hb⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (by omega)]
    rfl
  rw [e1] at h
  rw [D.hcW_e]
  apply Rat.cast_injective (α := ℝ)
  unfold wG
  unfold G.kaJ at h
  push_cast
  rw [h]
  push_cast
  ring

theorem reL_reL_symm {a b : ℕ} (h : a = b) {E : Type} [Field E] [NumberField E] (L : Submodule (𝓞 E) (Fin b → E)) :
    reL h (reL h.symm L) = L := by
  subst h
  rw [reL_rfl, reL_rfl]

theorem site_of {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Gt : GatTies D) (c : LatCmp D)
    (H : ∀ i (hi : i + 1 ≤ D.R.m), ∃ (Fo : FormsIn (D.fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD X0 u w hg Fo),
      StepTiesD X0 u w hg hi Fo S c) :
    ∃ Z : SiteD X0 u w hg (D.fm u), ∀ (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (i : ℕ) (hi : i + 1 ≤ D.R.m),
      StepTies hi (Z.Fo i hi) (Z.loc Fl ht i hi) Gt c := by
  choose Fo hfin S hS using H
  refine ⟨⟨Fo, hfin, S⟩, fun Fl ht i hi => ?_⟩
  obtain ⟨hT, hC, hbad, hstd, hpsi, hch, hok, hpT⟩ := hS i hi
  exact
    { frRat := SiteD.frRat _ Fl ht i hi
      sameU := SiteD.sameU _ Fl ht i hi
      hypT := hT
      bad_p := hbad
      std := hstd
      psi := hpsi
      chRat := hch
      hypC := hC
      ok := hok
      siteGood_prime_torsion := hpT
      Lb_eq := fun β => (reL_reL_symm _ _).symm }

theorem exists_comparisonData_steps_at_baseCharacter : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      have : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  intro K B f T w hO hF hP Z t Wt nch hn Y hMu hQ O hStd hUnf E hE Fl hFl hW u v hg _ hμ
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  have ht : (Fl u v hg).t = (w.D Z).R.t := (hFl u v hg).1
  have hFt : FillTie t.Gt u v hg (Fl u v hg) := fillTie_of t.Gt u v hg (Fl u v hg) (hW u v hg)
  obtain ⟨S, hS⟩ := site_of t.g.herm u v hg t.Gt t.cmp (fun i hi => by
    by_cases h2 : i + 1 + 1 ≤ (w.D Z).R.m
    · exact GlobalTheory.T.memberFormsLayer_midStep_charts_conditions w hO hF hP Z t Wt nch hn Y hMu hQ O hStd hUnf E hE u v hg i hi h2
    · exact GlobalTheory.T.memberFormsLayer_topStep_chart_conditions w hO hF hP Z t Wt nch hn Y hMu hQ O hStd hUnf E hE u v hg i hi (by omega))
  have A : HypTiesI t.g.herm (S.inMem (w.tw Z) (Fl u v hg) ht t.Gt) t.Gt t.cmp :=
    ⟨ht, hFt, fun j hj => ⟨S.Fo j hj, S.loc (Fl u v hg) ht j hj, rfl, hS (Fl u v hg) ht j hj⟩⟩
  rw [hμ]
  exact ⟨S.lv (Fl u v hg) ht, S.inMem (w.tw Z) (Fl u v hg) ht t.Gt, A.hyp t.g.cmp,
    fun j hj => ((w.D Z).memberColumns_twistedChain_base u).symm, fun j hj => A.chX j hj, fun j hj => ⟨fun c => absurd c.1 (by omega)⟩⟩

end GlobalTheory.Mem.Top.KerOne.CertEq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComparisonDataStepsUpToRankStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comparisonData_steps_upTo_rank : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.CertEq.exists_comparisonData_steps_at_baseCharacter | exact GlobalTheory.Mem.Top.KerOne.CertEq.exists_comparisonData_steps_at_baseCharacter | (intros; apply GlobalTheory.Mem.Top.KerOne.CertEq.exists_comparisonData_steps_at_baseCharacter <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceLevelsClassesComparisonMaps
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.KerOne

theorem levels_cls_cmp_at_served : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg))
        (clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1))
        (up : Formalism.L2.G.Cmp.CmpUp t.cmp (w.tw Z) u v hg Lv),
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ (a a' : Lv.compS j) (L L' : ((Fl u v hg).Pj (j + 1)).Tup),
          ((Fl u v hg).Pj (j + 1)).IsLatTup L → ((Fl u v hg).Pj (j + 1)).IsLatTup L' →
          (clsS j a L = clsS j a' L' ↔ a = a' ∧ ∃ γ : (Lv.levS j a).Γ, L' = (Lv.levS j a).smul γ L)) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ x, ∃ a L, ((Fl u v hg).Pj (j + 1)).IsLatTup L ∧ clsS j a L = x) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → Submodule.span ((w.D Z).gat u v hg).O
          (up.cmpS j '' ((((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).L :
            Set (((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).V)) = Lv.Int (j + 1)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨Lv, I, H, hC, hX, hE0⟩ : ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
    by_cases hμ : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0
    · exact GlobalTheory.T.exists_comparisonData_steps_upTo_rank w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ
    · exact GlobalTheory.T.comparison_data_steps_non_reference_tuple w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ
  classical
  let S := Formalism.MainNotions.G.CmpJ.stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds t.Gt
  let clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1) :=
    fun j a L => if hj : j + 1 ≤ (w.D Z).R.m then
      Formalism.MainNotions.G.KAat.castCls (hC j hj) (j + 1) (Formalism.MainNotions.G.KAat.clsOf (S := (I.at' j hj).st) (H.core j hj) a L)
    else (hE0 j (by omega)).elim a
  have hcls : ∀ j (hj : j + 1 ≤ (w.D Z).R.m) a L, clsS j a L =
      Formalism.MainNotions.G.KAat.castCls (hC j hj) (j + 1) (Formalism.MainNotions.G.KAat.clsOf (S := (I.at' j hj).st) (H.core j hj) a L) :=
    fun j hj a L => dif_pos hj
  refine ⟨Lv, clsS, Formalism.L2.G.Cmp.CmpUp.ofRat S.cmpS S.injS S.ratS, ?_, ?_, ?_⟩
  · intro j hj a a' L L' hL hL'
    rw [hcls j hj, hcls j hj, (Formalism.MainNotions.G.KAat.castCls_inj _ _).eq_iff]
    exact Formalism.MainNotions.G.KAat.clsOf_iff (S := (I.at' j hj).st) (H.core j hj) (hX j hj) a a' L L' hL hL'
  · intro j hj x
    obtain ⟨x0, rfl⟩ := Formalism.MainNotions.G.KAat.castCls_surj (hC j hj) (j + 1) x
    obtain ⟨a, L, hL, e⟩ := Formalism.MainNotions.G.KAat.clsOf_surj (S := (I.at' j hj).st) (H.core j hj) x0
    exact ⟨a, L, hL, (hcls j hj a L).trans (congrArg _ e)⟩
  · intro j hj
    exact S.intS (Formalism.MainNotions.G.CmpJ.descUp H t.Gt) j hj

end GlobalTheory.Mem.Top.KerOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceLevelsClassesComparisonMapsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.served_place_levels_classes_comparison_maps : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg))
        (clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1))
        (up : Formalism.L2.G.Cmp.CmpUp t.cmp (w.tw Z) u v hg Lv),
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ (a a' : Lv.compS j) (L L' : ((Fl u v hg).Pj (j + 1)).Tup),
          ((Fl u v hg).Pj (j + 1)).IsLatTup L → ((Fl u v hg).Pj (j + 1)).IsLatTup L' →
          (clsS j a L = clsS j a' L' ↔ a = a' ∧ ∃ γ : (Lv.levS j a).Γ, L' = (Lv.levS j a).smul γ L)) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ x, ∃ a L, ((Fl u v hg).Pj (j + 1)).IsLatTup L ∧ clsS j a L = x) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → Submodule.span ((w.D Z).gat u v hg).O
          (up.cmpS j '' ((((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).L :
            Set (((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).V)) = Lv.Int (j + 1)) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.levels_cls_cmp_at_served | exact GlobalTheory.Mem.Top.KerOne.levels_cls_cmp_at_served | (intros; apply GlobalTheory.Mem.Top.KerOne.levels_cls_cmp_at_served <;> assumption)
end
