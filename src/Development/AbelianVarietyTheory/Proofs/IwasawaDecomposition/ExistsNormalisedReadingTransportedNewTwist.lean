module

public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsReadingTransportLaterHeckeGaloisStage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RawPackEqPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormFieldSquareClass
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeParametersNumericaStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreFrameCompatibleConstructedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up

theorem cenTw_read {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : ∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, nTw x N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, nTw x N, x.o.G⟩ : P.q.Over))).nd)).coeff ((sgTw x N).iso g)) → (sideTw x N).cen μ c = x.s.cen μ c0 := by
  intro μ c c0 h
  have e : (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)) = (((by with_unfolding_all exact (c :)) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))) : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)) :=
    MonoidAlgebra.coeff_injective (Finsupp.ext fun g => (by with_unfolding_all exact ((h g) :)))
  have e2 : c0 = ((by with_unfolding_all exact (c :)) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))) := Subtype.ext e
  exact (by with_unfolding_all exact ((congrArg (x.s.cen μ) e2).symm :))

theorem readTw_ex {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) :
    ∃ r : ReadPk m (sideTw x N), r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y) := (by with_unfolding_all exact (
  (GlobalTheory.T.adelicRowsReading_transport_laterHeckeGaloisStage x (nTw x N) x.fits.grp (fitsTw x N).grpAt (fitsTw x N).cen m hc hh (sgTw x N) (sideTw x N) rfl HEq.rfl
    (cenTw_read x N)) :))

theorem jMtTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin) :
    ∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1 := by
  cases m with
  | mk z intersectionNumber_baseChange exAt inGeo Xg tr core eta W1 y tup t tA =>
    obtain rfl : z = datTw x N := hm
    have e : HEq t.lf.jMt x.m.t.lf.jMt := (by with_unfolding_all exact ((hh.jMt.trans x.coh.jMt.symm) :))
    have e2 : t.lf.jMt = ((by with_unfolding_all exact (x.m.t.lf.jMt :)) : type_of% t.lf.jMt) := eq_of_heq ((by with_unfolding_all exact (e :)))
    intro μ h i y
    exact (by with_unfolding_all exact (((hp.jMt μ h i y).trans ((heq_of_eq (congrArg (fun φ : type_of% t.lf.jMt => φ μ i y) e2)).trans (x.pin.jMt μ h i y).symm)) :))

theorem eWTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin) :
    ∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y) := by
  cases m with
  | mk z intersectionNumber_baseChange exAt inGeo Xg tr core eta W1 y tup t tA =>
    obtain rfl : z = datTw x N := hm
    have e : HEq t.lf.eW x.m.t.lf.eW := (by with_unfolding_all exact ((hh.eW.trans x.coh.eW.symm) :))
    have e2 : t.lf.eW = ((by with_unfolding_all exact (x.m.t.lf.eW :)) : type_of% t.lf.eW) := eq_of_heq ((by with_unfolding_all exact (e :)))
    intro i y
    exact (by with_unfolding_all exact (((hp.eW i y).trans ((heq_of_eq (congrArg (fun φ : type_of% t.lf.eW => φ i y) e2)).trans (x.pin.eW i y).symm)) :))

theorem readTw : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)), m.z = datTw x N → m.Copy → m.Coh → ∃ r : ReadPk m (sideTw x N), r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y) ∧ (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) ∧ (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) := by
  intro K B f T w P x N m hm hc hh
  have H := readTw_ex x N m hc hh
  refine H.elim fun r h => ?_
  exact Exists.intro r (And.intro h.1 (And.intro h.2 (And.intro (jMtTw x N m hm hh r h.1) (eWTw x N m hm hh r h.1))))

end GlobalTheory.HeightCounting.Up
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwistStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedReading_transported_newTwist : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)), m.z = datTw x N → m.Copy → m.Coh → ∃ r : ReadPk m (sideTw x N), r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y) ∧ (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) ∧ (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) := by
  first | exact @GlobalTheory.HeightCounting.Up.readTw | exact GlobalTheory.HeightCounting.Up.readTw | (intros; apply GlobalTheory.HeightCounting.Up.readTw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwist
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.Mv

namespace GlobalTheory.HeightCounting.Up.MvTw

section Gen

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C)
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
variable {A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m}

section Comp
variable (R : RealDat3 a.D A3 Ks)

def once : @RealDat3 c.D G _ _ Pl0 I0 T₀ (famInThreeCoefficientChange c A3) Ks _ _ (alg c iK) := real3 c R

def thru : @RealDat3 c.D G _ _ Pl0 I0 T₀ (famInThreeCoefficientChange c A3) Ks _ _ (alg c iK) :=
  (by with_unfolding_all exact ((real3 (a := b) c (iK := alg b iK) (real3 b R)) :))

def thruY : letI := alg c iK; type_of% (once c R).ioY := letI := alg c iK; (by with_unfolding_all exact ((thru b c R).ioY :))

def thruX : letI := alg c iK; type_of% (once c R).ioX := letI := alg c iK; (by with_unfolding_all exact ((thru b c R).ioX :))

theorem thruY_eq : letI := alg c iK; (once c R).ioY = thruY b c R :=
  letI := alg c iK
  eq_of_heq (HEq.trans ((by with_unfolding_all exact ((real_ioY c R.toRealDat).symm :)) : HEq (once c R).ioY R.ioY)
    ((by with_unfolding_all exact ((HEq.trans (real_ioY b R.toRealDat) ((by with_unfolding_all exact ((real_ioY (a := b) c (iK := alg b iK) (real b R.toRealDat)) :))) :
    HEq _ (thruY b c R)) :))))

theorem thruX_eq : letI := alg c iK; (once c R).ioX = thruX b c R :=
  letI := alg c iK
  eq_of_heq (HEq.trans ((by with_unfolding_all exact ((real_ioX c R.toRealDat).symm :)) : HEq (once c R).ioX R.ioX)
    ((by with_unfolding_all exact ((HEq.trans (real_ioX b R.toRealDat) ((by with_unfolding_all exact ((real_ioX (a := b) c (iK := alg b iK) (real b R.toRealDat)) :))) :
    HEq _ (thruX b c R)) :))))

theorem thru_eq : once c R = thru b c R :=
  letI := alg c iK
  (by with_unfolding_all exact ((congrArg₂ (DatCopy.setIo (once c R)) (thruY_eq b c R) (thruX_eq b c R)) :))

end Comp

variable {R : RealDat3 a.D A3 Ks} (F : Face3 a.D A3) (y : Hd R.toRealDat) (y' : HdB b R.toRealDat)


set_option maxHeartbeats 1000000 in
theorem pkT_move (hs : Same b y y') {mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G} {p : PkD a.D G} (t : PkT F y mA p) :
    letI := alg b iK
    ∃ t' : PkT (R := real3 b R) (face3 b F) (hd3 b y y') (mCp b mA) (pCp b p),
      HEq t'.tA t.tA ∧ HEq t'.rep t.rep ∧ (∀ c, HEq (t'.ch c).jE (t.ch c).jE) ∧ (∀ c, HEq (t'.ch c).jM (t.ch c).jM) ∧
        (∀ c, HEq (t'.ch c).jX (t.ch c).jX) ∧ HEq t'.lf.eW t.lf.eW ∧ HEq t'.lf.jMt t.lf.jMt := by
  letI := alg b iK
  have hs' := fixTup_same b hs
  have h1 := (GlobalTheory.Mem.R3.Tr.reps_parts_tr B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs').1 p.Φ t.rep t.reps
  have h2 := fun c => GlobalTheory.Mem.R3.Rw.chT_tr B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' c p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ => (p.sA c μ).A) :))) ((by with_unfolding_all exact ((p.ch c) :))) ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :))) ((by with_unfolding_all exact ((t.ch c) :)))
    ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x)) :)))
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.Mem.R3.Rw.lfT_of_same B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ j => (p.sL μ j).A) :))) ((by with_unfolding_all exact (p.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :))) ((by with_unfolding_all exact (t.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x)) :)))
  have h4 := (GlobalTheory.Mem.R3.Rw.rr_eta_tr B C a b G Pl0 I0 T₀ Ks A3 R F).2 y (hd3 b y y') true (p.ch true).EE (t.ch true).jE
    ((by with_unfolding_all exact ((h2 true).choose.jE :))) p.nR p.cR p.Xo ((by with_unfolding_all exact ((h2 true).choose_spec.1 :))) t.rr
  refine ⟨{ rep := (by with_unfolding_all exact (t.rep :))
            reps := (by with_unfolding_all exact (h1 :))
            tA := (by with_unfolding_all exact (t.tA :))
            lawsA := (by with_unfolding_all exact (t.lawsA :))
            lawsL := (by with_unfolding_all exact (t.lawsL :))
            hA := (by with_unfolding_all exact (t.hA :))
            hL := (by with_unfolding_all exact (t.hL :))
            ch := fun c => (by with_unfolding_all exact ((h2 c).choose :))
            lf := (by with_unfolding_all exact (l :))
            dall := (by with_unfolding_all exact ((dall_tr b F t.dall) :))
            rr := (by with_unfolding_all exact (h4 :)) }, ?_, ?_, fun c => ?_, fun c => ?_, fun c => ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl t.tA) :))
  · exact (by with_unfolding_all exact ((HEq.refl t.rep) :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.2 :))
  · exact (by with_unfolding_all exact (hl1 :))
  · exact (by with_unfolding_all exact (hl2 :))

end Gen

section Dat

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}


set_option maxHeartbeats 1000000 in
theorem transportModuliCoreWithConstants_comp (z₀ : Dat a.st I hX T Wt) (Xg : Finset (Gc b.st.B px → b.st.B.LL)) (tr : TrI b.st.B px)
    (co : Formalism.L2.Pj.CoreJ b.st.toD7) (al : Algebra co.Q.c.F b.st.toD7.what₂.LL)
    (ale : ∀ y : co.Q.c.F, b.st.B.embLL (algebraMap co.Q.c.F b.st.toD7.what₂.LL y) = y)
    (R : RealDat3 b.st.toD7 (famR b.st I hX (usedOf I T Wt) Xg tr) co.Q.c.F)
    (hXg : Xg = z₀.Xg) (htr : tr = z₀.tr)
    (hc : HEq co (coreJ (a := a) b z₀.core)) (hR : HEq R (real3 (a := a) b (iK := z₀.alg) z₀.R)) :
    HEq (coreJ (a := b) c co) (coreJ (a := a) c z₀.core) ∧
      HEq (real3 (a := b) c (iK := al) R) (real3 (a := a) c (iK := z₀.alg) z₀.R) := by
  have hc' := eq_of_heq hc
  subst hXg htr hc'
  have e : al = ((by with_unfolding_all exact ((alg (a := a) b z₀.alg) :))) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    refine Eq.trans (ale y) ?_
    exact (by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :))
  subst e
  have hR' : R = ((by with_unfolding_all exact ((real3 (a := a) b (iK := z₀.alg) z₀.R) :))) := eq_of_heq ((by with_unfolding_all exact (hR :)))
  subst hR'
  refine ⟨?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl (coreJ (a := a) c z₀.core)) :))
  · exact (by with_unfolding_all exact ((heq_of_eq (thru_eq (a := a) b c (iK := z₀.alg) z₀.R).symm) :))


set_option maxHeartbeats 1000000 in
theorem copy_comp (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (hXg : z.Xg = z₀.Xg) (htr : z.tr = z₀.tr)
    (hc : HEq z.core (coreJ (a := a) b z₀.core)) (hR : HEq z.R (real3 (a := a) b (iK := z₀.alg) z₀.R)) :
    HEq (coreJ (a := b) c z.core) (coreJ (a := a) c z₀.core) ∧
      HEq (real3 (a := b) c (iK := z.alg) z.R) (real3 (a := a) c (iK := z₀.alg) z₀.R) :=
  (by with_unfolding_all exact ((transportModuliCoreWithConstants_comp b c z₀ z.Xg z.tr z.core z.alg z.alg_eq z.R hXg htr hc hR) :))

end Dat

section Main

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}


set_option maxHeartbeats 2000000 in
theorem moved_again (o o' : q.Over) (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) (m : Moved o) (hc : m.Copy) (hh : m.Coh) :
    ∃ m' : Moved o', m'.z = DatCopy.copy (a := o.Z) o'.Z s m.z ∧ m'.Copy ∧ m'.Coh := by
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ m.z.alg _ m.z.R.toRealDat m.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := pkT_move (a := o.Z) o'.Z (iK := m.z.alg) m.z.F m.y y' hy m.t
  have he := (@GlobalTheory.Mem.R3.Rw.rr_eta_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ _ m.z.alg _ m.z.R m.z.F).1
  letI : Algebra m.z.core.Q.c.F (Late.D o'.Z).what₂.LL := alg (a := o.Z) o'.Z m.z.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% m.t.tA) = m.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have hk := copy_comp (a := Z₀) o.Z o'.Z z₀ m.z m.Xg m.tr ((by with_unfolding_all exact (hc.core :))) ((by with_unfolding_all exact (hc.R :)))
  have hW := forcedContentPlaces_eq_transport_sameFiniteGroup (a := o.Z) o'.Z s m.z
  refine ⟨{ z := DatCopy.copy (a := o.Z) o'.Z s m.z
            intersectionNumber_baseChange := (by with_unfolding_all exact ((cp_holds (a := o.Z) o'.Z s m.z m.intersectionNumber_baseChange) :))
            exAt := DatCopy.copy_exAt (a := o.Z) o'.Z s m.exAt
            inGeo := (by with_unfolding_all exact ((cp_inGeo (a := o.Z) o'.Z s m.z m.inGeo) :))
            Xg := (by with_unfolding_all exact (m.Xg :))
            tr := (by with_unfolding_all exact (m.tr :))
            core := fun h => ⟨(by with_unfolding_all exact ((lawsCore_tr (a := o.Z) o'.Z (m.core h).1) :)), (by with_unfolding_all exact ((m.core h).2.1 :)), (by with_unfolding_all exact ((m.core h).2.2.1 :)),
              (by with_unfolding_all exact ((m.core h).2.2.2 :))⟩
            eta := fun j v => Eq.trans ((by with_unfolding_all exact ((he j ((by with_unfolding_all exact (v :)))) :)) : _ = etaOf m.z.R m.z.F j v) (m.eta j v)
            W1 := fun F0 => Eq.trans ((by with_unfolding_all exact ((hW ((by with_unfolding_all exact (F0 :)))) :)) : _ = m.z.W1 ((by with_unfolding_all exact (F0 :)))) ((by with_unfolding_all exact ((m.W1 ((by with_unfolding_all exact (F0 :)))) :)))
            y := (by with_unfolding_all exact ((hd3 (a := o.Z) o'.Z (iK := m.z.alg) m.y y') :))
            tup := (by with_unfolding_all exact (m.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := fun c u => (by with_unfolding_all exact ((HEq.trans (heq_of_eq (congrArg (fun r : type_of% m.t.tA => (r c ((by with_unfolding_all exact (u :)))).j) hA))
              (m.tA c ((by with_unfolding_all exact (u :))))) :)) }, rfl, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (hk.1 :))
  · exact (by with_unfolding_all exact (hk.2 :))
  · exact (by with_unfolding_all exact (hh.tupT :))
  · exact (by with_unfolding_all exact ((HEq.trans ((by with_unfolding_all exact (hy.PY :)) : HEq (fixTup (a := o.Z) o'.Z (iK := m.z.alg) m.y y').PY.ψ m.y.PY.ψ) hh.PY) :))
  · exact (by with_unfolding_all exact ((HEq.trans ((by with_unfolding_all exact (hy.PW :)) : HEq (fun i => ((fixTup (a := o.Z) o'.Z (iK := m.z.alg) m.y y').PW i).ψ) (fun i => (m.y.PW i).ψ)) hh.PW) :))
  · exact (by with_unfolding_all exact ((a2.trans hh.rep) :))
  · exact (by with_unfolding_all exact ((fun c => (a3 c).trans (hh.jE c)) :))
  · exact (by with_unfolding_all exact ((fun c => (a4 c).trans (hh.jM c)) :))
  · exact (by with_unfolding_all exact ((fun c => (a5 c).trans (hh.jX c)) :))
  · exact (by with_unfolding_all exact ((a6.trans hh.eW) :))
  · exact (by with_unfolding_all exact ((a7.trans hh.jMt) :))

end Main

theorem moved_tw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (N : TwNew (Dof x)) : ∃ m : Moved (oTw x N), m.z = datTw x N ∧ m.Copy ∧ m.Coh :=
  moved_again x.o (oTw x N) (sgTw x N) x.m x.copy x.coh

end GlobalTheory.HeightCounting.Up.MvTw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwistStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_movedData_laterStagesWithNewTwist : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)), ∃ m : Moved (oTw x N), m.z = datTw x N ∧ m.Copy ∧ m.Coh := by
  first | exact @GlobalTheory.HeightCounting.Up.MvTw.moved_tw | exact GlobalTheory.HeightCounting.Up.MvTw.moved_tw | (intros; apply GlobalTheory.HeightCounting.Up.MvTw.moved_tw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadOfEigenLabeling
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

noncomputable section

namespace GlobalTheory.HeightCounting.Up.IdempotentAdelicReading


set_option maxHeartbeats 4000000 in
theorem gaL_jV {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hr : R.grp_red_L)
    (hj : R.models_jV) (j : Fin D.R.m) (hc : (R.cV j).Is) (t : T) (y : (A.fam.L j t).S.Forms)
    (l : (R.cV j).W →ₗ[ℂ] ℂ) :
    gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A) (sg0 D A)) (fun g => l (R.extV j t (R.jV j t y) g)) =
      fun g => l (R.extV j t (R.jV j t (∑ a, (idemOf A.X).coeff a • (A.fam.L j t).r a y)) g) := by
  let Φ : (R.HV j t).H →ₗ[ℂ] (GA D (Vc D j) → ℂ) := l.compLeft (GA D (Vc D j)) ∘ₗ R.extV j t
  have hs : ∀ a, RealDat.eC (A := A) (sg0 D A) a = D.what₂.embLL ((idemOf A.X).coeff a) := fun a => by
    show sg0 D A _ = _
    rw [sg0, sgAt_mk D.what₂.embLL R.hv0]
  have key : ∀ a, Φ (R.jV j t ((A.fam.L j t).r a y)) =
      Formalism.IndefR.Links.actL (Vc D j) (R.βV j) (R.datVt j t) (R.eG a) (Φ (R.jV j t y)) := fun a =>
    (GlobalTheory.GoodModelVec.actL_coord R hr hj j hc t a y l).symm
  show gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A) (sg0 D A)) (Φ (R.jV j t y)) =
    Φ (R.jV j t (∑ a, (idemOf A.X).coeff a • (A.fam.L j t).r a y))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp only [LinearMap.map_smulₛₗ, key, gaL, LinearMap.sum_apply, LinearMap.smul_apply, hs, RingHom.id_apply]
  rfl


set_option maxHeartbeats 4000000 in
theorem act_of_read {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    (hg : GlobalTheory.LiftRows.Given R F) {s : ℕ} (hok : A3.A.fam.Ok s) (j : Fin D.R.m) :
    ∀ (μ : D.what₂.Tup) (t : T), Y.tup t = μ → ∀ (h : Used0 D μ) (f : D.what₂.Mt μ (j.1 + 1)) (l : (R.cV j).W →ₗ[ℂ] ℂ),
      gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A3.A) (sg0 D A3.A)) (fun g => l ((Y.IL.jMt μ h j f).1 g)) =
        fun g => l ((Y.IL.jMt μ h j (D.what₂.eMt μ (j.1 + 1) f)).1 g) := by
  intro μ t ht h f l
  subst ht
  let Ψ : D.what₂.Mt (Y.tup t) (j.1 + 1) →ₗ[ℂ] (GA D (Vc D j) → ℂ) :=
    l.compLeft (GA D (Vc D j)) ∘ₗ
      ((((toLiftReal R F Y.tupT Y.hm Y.hTop Y.hinj).Amt (Y.tup t) j).subtype :
        _ →ₗ[ℂ] (GA D (Vc D j) → (R.cV j).W)) ∘ₗ (Y.IL.jMt (Y.tup t) h j).toLinearMap)
  have hΨ : ∀ f, Ψ f = fun g => l ((Y.IL.jMt (Y.tup t) h j f).1 g) := fun _ => rfl
  have hF := Y.formsL j t
  have main : gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A3.A) (sg0 D A3.A)) ∘ₗ Ψ =
      Ψ ∘ₗ D.what₂.eMt (Y.tup t) (j.1 + 1) := by
    refine LinearMap.ext_on_range hF.span fun k => ?_
    have hop := hF.op_eq (Pi.single k 1)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hop ⊢
    rw [hop, hΨ, hΨ, Y.mtRead j t h, Y.mtRead j t h]
    generalize (Pi.single k 1 : Fin _ → D.what₂.LL) = x
    have hl : liftForm A3.A F.P0 F.ψ0 j t ((lE D A3.A F.P0 F.ψ0 j t).mulVec x) =
        ∑ g, (idemOf A3.A.X).coeff g • (A3.A.fam.L j t).r g (liftForm A3.A F.P0 F.ψ0 j t x) :=
      GlobalTheory.ClassSumIdentity.lvlE_lvlOp hok.conj _ ((hok.lifts j t).hpos _) _ (hok.lifts j t).act _ _ _
        (fun b => (idempotent_central _ _ A3.A.X hok.irr).2 b) x
    rw [hl]
    exact gaL_jV R hg.core.grp.red_L hg.core.models.jV j (hg.core.models.cV j) t _ l
  exact LinearMap.congr_fun main f

theorem goodIdempotent_eq_goodProjector_adelicReading {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    {cf : CharFrame D} {nch : NChoice D} (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd)
    (labPi : E.Pi → A3.A.fam.base.Ix) (hbase : R.BaseW F)
    (htup : ∀ μ, Used0 D μ → R.toLevCh.xiH (Y.tupT μ) = tp.xi μ) (hg : GlobalTheory.LiftRows.Given R F) (hf : R.FullP)
    {s : ℕ} (hok : A3.A.fam.Ok s) :
    GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead R F Y tp hC Xd E labPi hbase htup hg hf) := by
  apply GlobalTheory.NRows.Model.unitaryRealisationReading_of_idempotent_acts_via_levelGroup
  intro μ hμ j f l
  rw [← D.nStage_trivialCharacter_compat.2]
  exact act_of_read R F Y hg hok j μ (Y.tupT μ) (Y.tupTie μ hμ) hμ f l

end GlobalTheory.HeightCounting.Up.IdempotentAdelicReading
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStates
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeoOfLevels
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie.CuspLev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) (j : Fin D.R.m)

theorem heckeIs_of_levels (Z : GlobalTheory.SeriesTie.ExportTie YS v₀) (hev : fw.Evaluates)
    (hLev : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hHW : Rl.toRealDat.models_HW) (hU : Rl.toRealDat.LUnif) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (hRd' : ∀ hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j,
      GlobalTheory.HeckeSup.ReadsCusp T0 Rl.toRealDat κ j (res T0 (sg0 D A3.A)) hV)
    (hS : ∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E)))
    (hHT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P) :
    ∃ (c : FractionRing (D.ntw.O i)),
      Z.ρ.e i b c = (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) ^ k ∧ (∃ n : ℕ, n ≠ 0 ∧ c ^ n = 1) ∧
      ‖embC YS iC b (hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV)‖ = 1 ∧
      HeckeIs YS fw iC b j k P ((iC c)⁻¹ * embC YS iC b (hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV)) := by
  obtain ⟨hk1, hkr, hPs, hPS0⟩ := hk

  have hsg : sg0 D A3.A = D.what₂.embLL := RingHom.ext fun c => congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)
  have hres : res T0 (sg0 D A3.A) = T0.σ₀ := by
    rw [hsg]; exact res_embLL T0 fw.alg_eq fw.laws.pins.2.2.1
  have hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j :=
    fw.laws.spaceW _ (inR j) _ (base_embedding_good T0 Rl.toRealDat fw.alg_eq fw.laws.pins.2.2.1)
  have hRd := hRd' hV
  have hν : Z.ν i j b ≠ 0 := (Z.scalar i j b).ne
  have hinj : Function.Injective (Z.rd i j b) :=
    (GlobalTheory.SeriesTie.realRd_faithful D Γ Pl0 I0 T1 A3 T0.Q.c.F Rl cG S YS v₀ Z.ρ Z.good i j b (Z.ν i j b) hν hU
      hHW (Z.vec j) hK).injective

  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    rw [Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hPS0 (D.ntw.placesOver_subset_exceptional i 0 h)
    · exact hPS0 (D.ntw.placesOver_subset_exceptional i 1 h)
  have hoff : ¬ charAt P ∣ T0.Q.l.M' := GlobalTheory.HeckeSup.not_dvd_level fw.laws (charAt_mem P) hg
  have hso := hS P hPs hPS0
  have hsplit : P.asIdeal ⊔ P.asIdeal.map (T0.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ :=
    GlobalTheory.HeckeSup.split_of_ne hso.1
  have hSO : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.IsSplitOff T0.Q.l P.asIdeal (charAt P) :=
    ⟨P.isMaximal, hsplit, charAt_prime P, charAt_mem P, hoff⟩
  have hHP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T0.Q.l P.asIdeal (charAt P) :=
    GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, hsplit, charAt_prime P, charAt_mem P, hoff⟩

  have hn : (κ j).n = D.R.nV := (fw.kap j (D.eTau.symm 1)).2.2
  set cq : T0.Q.c.F := ((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2) with hcq
  set s : T0.Q.c.F := hkScal T0.Q.c cq P.asIdeal k D.R.nV with hs
  have htr : ∀ x : NX.FmK S ((j : ℕ) + 1), ∃ g ∈ T0.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T0 ((j : ℕ) + 1) P.asIdeal (charAt P) k s (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) g := by
    intro x
    obtain ⟨g, hg, hfg⟩ := GlobalTheory.HeckeSup.exists_transform hHT GlobalTheory.HeckePointLaw.heckePointLaws fw.laws j hSO hkr cq
      (dom_wtA (κ j)) _ (cuspOf YS fw j x).2
    rw [show hkScal T0.Q.c cq P.asIdeal k (κ j).n = s by rw [hn]] at hfg
    exact ⟨g, hg, hfg⟩
  choose G hG hGt using htr
  let x' : NX.FmK S ((j : ℕ) + 1) → NX.FmK S ((j : ℕ) + 1) := fun x => (cuspOf YS fw j).symm ⟨G x, hG x⟩
  have hx' : ∀ x, (cuspOf YS fw j (x' x) : T0.R ((j : ℕ) + 1)) = G x := fun x => by
    simp only [x', AddEquiv.apply_symm_apply]

  obtain ⟨α₀, R₀, z₀, d₀⟩ := GlobalTheory.HeckeDatumExists.exists_isHeckeDatum D D.nd D.ntw Z.ρ Z.good i j b k P ⟨hk1, hkr, hPs, hPS0⟩
  obtain ⟨c, hc, N, hN, hcN⟩ := exists_delta_root Z.good i j b z₀
  have hPg : Bridge.SplitOff P (((Z.ρ.B i j b).G.Pg : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main Z.good i _ (fun P' hP' => by
      obtain ⟨k', hk'⟩ := Z.good.Pg i j b P' hP'
      exact D.ntw.placesOver_subset_exceptional i k' hk') P hPs hPS0
  have hdQ : Bridge.SplitOff P (((Z.ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main Z.good i _ (fun P' hP' => by
      rw [Z.good.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (GlobalTheory.SeriesTie.mem_half.1 hP').1) P hPs hPS0

  have hPgS : GlobalTheory.ExportSeries.SplitSet (Z.ρ.B i j b).G.Pg := by
    obtain ⟨Q', hPgQ, -, hQs⟩ := (Z.good.base i j b).places.split
    exact hQs.mono hPgQ
  have hde : ∀ α R z, Z.ρ.IsHeckeDatum i j b k P α R z → (((Z.ρ.B i j b).de.chi z : Circle) : ℂ) = Z.ρ.e i b c :=
    fun α R z d => by
      rw [hc, GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α z (Z.pin.delta i j b) (Z.good.base i j b).de.unram
          (Z.good.base i j b).de.split hdQ d.elt d.det,
        GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α₀ z₀ (Z.pin.delta i j b) (Z.good.base i j b).de.unram
          (Z.good.base i j b).de.split hdQ d₀.elt d₀.det]
  have hchr' : ChrEq (Z.ρ.B i j b).mu0 (Rl.C.mu0 j) := by rw [Z.pin.mu0 i j b]; exact hLev.mu0 j
  have hmu0 : ∀ α R z, Z.ρ.IsHeckeDatum i j b k P α R z →
      (((Z.ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k :=
    fun α R z d => GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α z hchr' (Z.good.base i j b).unram hPgS hPg d.elt d.det
  have hrank : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hdiv : k * D.R.nV / 2 = k * (D.R.nV / 2) := Nat.mul_div_assoc _ (even_iff_two_dvd.1 (kapDom D).2)

  have hkey : ∀ (a : NX.KB S i b) (x : NX.FmK S ((j : ℕ) + 1)),
      D.nexp.hkF i _ b k P ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x)) = c⁻¹ • (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x' x) := by
    intro a x
    refine GlobalTheory.SeriesTie.HeckeTie.eq (Z.hecke i j b) hinj ⟨hk1, hkr, hPs, hPS0⟩ d₀ ?_
    intro α R z d
    have hdc := d.reps
    rw [GlobalTheory.SeriesTie.levK_eq_levG_triv Rl Z.pin i j b] at hdc
    have hset : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T0 Rl.toRealDat j P (charAt P) k α R :=
      ⟨hso, charAt_prime P, charAt_mem P, hoff, hkr, d.elt, hdc⟩
    have hread := hRd P (charAt P) k α R ⟨hso, hg, hkr, d.elt, hdc⟩ hset _ (cuspOf YS fw j x).2 _ (hG x) (hGt x)
    simp only [← GlobalTheory.HeckeSup.hkC_eq (T := T0)] at hread
    funext h
    rw [GlobalTheory.SeriesTie.Setup.hecke_apply, map_smulₛₗ]
    simp only [GlobalTheory.SeriesTie.ExportTie.rd, Pi.smul_apply, smul_eq_mul]
    rw [realRd_eq_phiC YS fw Z.good i j b (Z.ν i j b) hV hev, realRd_eq_phiC YS fw Z.good i j b (Z.ν i j b) hV hev]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx', hread, GlobalTheory.ExportSeries.Base.mu, MonoidHom.mul_apply, Circle.coe_mul, hmu0 α R z d, hde α R z d,
      show Formalism.ConjugateSelfDual.normV P = Nat.card (kP P) from rfl, hrank, ← hdiv, map_inv₀, ← Finset.mul_sum]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt]
    ring
  have hsn : ‖embC YS iC b s‖ = 1 := by
    obtain ⟨p', f', hp', hp'P, hq'⟩ := GlobalTheory.HeckeSup.exists_prime_under P
    have hl : p' ≠ D.ntw.l i := by
      rintro rfl
      exact hPS0 (D.ntw.twistExcludedPlaces_contains_residueChar i hp'P)
    have e1 : Ideal.absNorm P.asIdeal = p' ^ f' := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq']
    have e2 : Nat.card (kP P) = p' ^ f' := hq'
    have hp1 : ‖((p' : ℕ) : ℂ_[D.ntw.l i])‖ = 1 := by
      rw [← map_natCast (algebraMap ℚ_[D.ntw.l i] ℂ_[D.ntw.l i]) p', norm_algebraMap', Padic.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes (Fact.out : (D.ntw.l i).Prime) hp').2 (Ne.symm hl)
    rw [hs, hkScal, hcq, e1, e2]
    simp only [map_mul, map_pow, map_inv₀, map_natCast, norm_mul, norm_pow, norm_inv, Nat.cast_pow, hp1, one_pow, inv_one,
      mul_one]
  refine ⟨c, hc.trans (GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α₀ z₀ (Z.pin.delta i j b) (Z.good.base i j b).de.unram
    (Z.good.base i j b).de.split hdQ d₀.elt d₀.det), ⟨N, hN, hcN⟩, hsn, ?_⟩
  intro z quot hq f
  have hfin : Finite (HkKer P.asIdeal (charAt P) k z.1) :=
    GlobalTheory.HeckePointLaw.heckePointLaws.1 _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hHP _ z.1
  obtain ⟨y, rfl⟩ := (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm.surjective f
  rw [LinearEquiv.apply_symm_apply]
  have key : ∀ y : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      valAt YS fw j z.1 (YS.eF i _ b (Nat.le_add_left _ _) j.2
        (D.nexp.hkF i _ b k P ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y))) =
        (iC c)⁻¹ * embC YS iC b s * ∑ᶠ C, valAt YS fw j (quot C) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      have e0 : (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (0 : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) = 0 :=
        map_zero _
      have e1 : ∀ C, valAt YS fw j (quot C) (0 : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) = 0 := fun C => map_zero _
      rw [e0, map_zero, map_zero, map_zero, finsum_congr e1, finsum_zero, mul_zero]
    | add y y' hy hy' =>
      have ea : (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (y + y') =
          (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y + (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y' := map_add _ _ _
      have eb : ∀ C, valAt YS fw j (quot C) (y + y') = valAt YS fw j (quot C) y + valAt YS fw j (quot C) y' :=
        fun C => map_add _ _ _
      rw [ea, map_add (f := _), map_add (f := _), map_add (f := _), hy, hy', finsum_congr eb, finsum_add_distrib (Set.toFinite _) (Set.toFinite _),
        mul_add]
    | tmul a x =>
      have ea : (YS.eF i _ b (Nat.le_add_left _ _) j.2) ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x' x)) =
          a ⊗ₜ[S.Ks] x' x := LinearEquiv.apply_symm_apply _ _
      rw [hkey, map_smul, ea]
      refine (valAt_smul YS fw j z.1 c⁻¹ _).trans ?_
      rw [valAt_tmul, hx',
        valC_geoHecke YS iC b j hHP s (cuspOf_mem_sec YS fw j x) (hGt x) z.1 quot hq]
      simp only [valAt_tmul]
      rw [← mul_finsum, map_inv₀]
      ring
  exact key y

theorem heckeGeo_of_levels (Z : GlobalTheory.SeriesTie.ExportTie YS v₀) (hev : fw.Evaluates)
    (hLev : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hHW : Rl.toRealDat.models_HW) (hU : Rl.toRealDat.LUnif) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (hRd : ∀ hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j,
      GlobalTheory.HeckeSup.ReadsCusp T0 Rl.toRealDat κ j (res T0 (sg0 D A3.A)) hV)
    (hS : ∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E)))
    (hHT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform)
    (hδ : ∀ P, P ∉ D.ntw.S0 i → ∃ s : T0.Q.c.F,
      D.what₂.embLL (algebraMap T0.Q.c.F D.what₂.LL s) = (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)) :
    HeckeGeo YS fw iC b j := by
  intro k P hk
  obtain ⟨c, hc, ⟨N, hN, hcN⟩, hsn, h⟩ := heckeIs_of_levels YS fw iC b j Z hev hLev hHW hU hK hRd hS hHT hk
  obtain ⟨s₁, hs₁⟩ := hδ P hk.2.2.2
  have hs : Z.ρ.e i b (sideK YS i b (s₁ ^ k)) = Z.ρ.e i b c := by
    obtain ⟨a, rfl⟩ := (eKs YS).surjective s₁
    rw [hc, ← hs₁, map_pow, map_pow, sideK_eKs, eKs_LL, ← S.kKs_spec]
    exact congrArg (· ^ k) (Z.good.e_LL0 i b (S.kKs a))
  have hcs : embC YS iC b (s₁ ^ k) = iC c := congrArg iC ((Z.ρ.e i b).injective hs)
  have h1 : ‖iC c‖ ^ N = 1 := by rw [← norm_pow, ← map_pow, hcN, map_one, norm_one]
  have hc1 : ‖iC c‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).1 h1
  refine ⟨(s₁ ^ k)⁻¹ * hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV, ?_, ?_⟩
  · rw [map_mul, map_inv₀, norm_mul, norm_inv, hcs, hc1, hsn, inv_one, one_mul]
  · rw [map_mul, map_inv₀, hcs]
    exact h

end GlobalTheory.GeoTie.CuspLev

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.HeckeLaw

theorem delAt_unr {D : D7} (C : CharFrame D) (i : D.ntw.Tw) {P : PlE D.host} (hP : P ∉ D.ntw.S0 i) :
    (C.delAt (D.ntw.l i)).UnrAt P := by
  have h : ¬ OverP D.host (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) P := fun hk =>
    hP (D.ntw.primes_subset_exceptional i (by rw [← Finset.mem_coe, D.ntw.pD_eq]; exact hk))
  unfold CharFrame.delAt
  split_ifs at h ⊢
  · exact C.isDel'.unr P h
  · exact C.isDel.unr P h

theorem del_values {B : Base} {δ : Fld.FieldDat B.toPre} {f : Fr B.toPre} (h : B.KsExact δ f) :
    f.del.ValuesIn 0 B.KstoC ∧ f.del'.ValuesIn 0 B.KstoC := by
  have h1 : Fld.charField f ≤ B.KsC := ((Fld.listField_le_iff δ f).1 (le_of_eq (Eq.symm h))).2.2.2.2.1
  rw [Fld.valuesIn_iff, Fld.valuesIn_iff, B.imField_KstoC]
  exact ⟨((le_sup_right.trans le_sup_left).trans le_sup_left).trans h1, (le_sup_right.trans le_sup_left).trans h1⟩

theorem delAt_mem {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (i : (w.st Z).toD7.ntw.Tw) (P : PlE (w.st Z).toD7.host) (hP : P ∉ (w.st Z).toD7.ntw.S0 i) :
    ∃ s : z.core.Q.c.F, (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL s) =
      (((z.R.C.delAt ((w.st Z).toD7.ntw.l i)).val P : ℂˣ) : ℂ) := by
  have hC : z.R.C = Fr.at (w.st Z) f := z.lev.C.trans (congrArg _ w.C_eq)
  have hu := delAt_unr z.R.C i hP
  have hv : (z.R.C.delAt ((w.st Z).toD7.ntw.l i)).ValuesIn 0 B.KstoC := by
    rw [hC]
    unfold CharFrame.delAt
    split_ifs
    · exact (del_values w.exact).2
    · exact (del_values w.exact).1
  obtain ⟨y, hy⟩ := hv P hu
  obtain ⟨s, hs⟩ := z.Ks_le y.1 y.2
  refine ⟨s, ?_⟩
  rw [hs]
  refine Eq.trans (show _ = B.KstoC y from rfl) (hy.trans ?_)
  simp [HChar.valTw]

end GlobalTheory.HeightCounting.HeckeLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisorAll
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.LargeBaseRayCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFinsetContainsRayField
open NumberField IsDedekindDomain GlobalTheory.Mem

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RayOnto

theorem containsRayField_comp {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field L'] [NumberField L']
    (φ : K →+* L) (τ : L →+* L') (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (τ.comp φ) n := by
  intro P hP
  letI : Algebra L L' := τ.toAlgebra
  let Q : HeightOneSpectrum (𝓞 L) := P.under (𝓞 L)
  have hQ : Q.asIdeal = P.asIdeal.comap (RingOfIntegers.mapRingHom τ) := rfl
  haveI hPo : P.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hn : ((n : ℕ) : 𝓞 L) ∉ Q.asIdeal := fun h' => hP (by
    rw [hQ, Ideal.mem_comap, map_natCast] at h'
    exact h')
  obtain ⟨f, α, h1, h2, h3⟩ := h Q hn
  have hf := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal Q.asIdeal Q.isPrime Q.ne_bot
  have hcm : P.asIdeal.comap (RingOfIntegers.mapRingHom (τ.comp φ)) =
      Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    ext x
    rfl
  rw [hcm]
  refine ⟨f * Q.asIdeal.inertiaDeg' P.asIdeal, α ^ Q.asIdeal.inertiaDeg' P.asIdeal, ?_, ?_, ?_⟩
  · rw [hf, h1, ← pow_mul]
  · rw [pow_mul, h2, Ideal.span_singleton_pow]
  · have := sub_dvd_pow_sub_pow α 1 (Q.asIdeal.inertiaDeg' P.asIdeal)
    rw [one_pow] at this
    exact dvd_trans h3 this

theorem exists_finset_containsRayField : GlobalTheory.NT.RayField → ∀ (P : Pre) (M : ℕ), M ≠ 0 → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (φ : P.host.K →+* L), σ.comp φ = P.host.φ₀.comp (algebraMap P.host.K P.host.E) → (∀ z ∈ S, ∃ x, σ x = z) → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ M := by
  intro hR P M hM
  let φK : P.host.K →+* ℂ := P.host.φ₀.comp (algebraMap P.host.K P.host.E)
  obtain ⟨Rf, hRf⟩ := GlobalTheory.Mem.Fld.exists_isRayFieldIn φK hR (GlobalTheory.Mem.Fld.natIdeal_ne_bot (E := P.host.K) hM)
  haveI : NumberField Rf := hRf.numberField
  let b := Module.finBasis ℚ Rf
  refine ⟨Finset.univ.image (fun i => (b i : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    have h : IsAlgebraic ℚ (b i) := Algebra.IsAlgebraic.isAlgebraic _
    exact h.algHom Rf.val
  · intro L _ _ σ φ hσφ hS
    obtain ⟨hm, hNF, hray⟩ := hRf
    letI := GlobalTheory.Mem.Fld.algOf φK Rf hm
    obtain ⟨hab, hun, -, hart⟩ := hray
    haveI : IsGalois P.host.K Rf := hab.toIsGalois
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.K Rf) M :=
      GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (K := P.host.K) (L := Rf) M hun
        (fun I hI hc hχ => (hart I hI hc).1 hχ)
    have hle : Rf ≤ σ.toRatAlgHom.fieldRange := by
      intro z hz
      have hsum := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
      rw [IntermediateField.coe_sum] at hsum
      simp only [IntermediateField.coe_smul] at hsum
      rw [← hsum]
      refine sum_mem fun i _ => IntermediateField.smul_mem _ ?_
      obtain ⟨y, hy⟩ := hS (b i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
      exact ⟨y, hy⟩
    let e : L ≃ₐ[ℚ] σ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField σ.toRatAlgHom
    let τ : Rf →+* L := (e.symm : σ.toRatAlgHom.fieldRange →+* L).comp
      (IntermediateField.inclusion hle : Rf →+* σ.toRatAlgHom.fieldRange)
    have key : ∀ w, σ (e.symm w) = (w : ℂ) := fun w => by
      conv_rhs => rw [← e.apply_symm_apply w]
      rfl
    have hτ : τ.comp (algebraMap P.host.K Rf) = φ := by
      ext x
      apply σ.injective
      have h1 : σ (φ x) = φK x := RingHom.congr_fun hσφ x
      rw [h1]
      exact key _
    rw [← hτ]
    exact containsRayField_comp _ τ M hc

end GlobalTheory.RayOnto
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Plug.RayLarge

open _root_.Formalism.L2.Host

def raySet (hR : GlobalTheory.NT.RayField) (P : Pre) (M : ℕ) : Finset ℂ :=
  if h : M ≠ 0 then Classical.choose (GlobalTheory.RayOnto.exists_finset_containsRayField hR P M h) else ∅

theorem raySet_alg (hR : GlobalTheory.NT.RayField) (P : Pre) (M : ℕ) : ∀ z ∈ raySet hR P M, IsAlgebraic ℚ z := by
  unfold raySet
  split_ifs with h
  · exact (Classical.choose_spec (GlobalTheory.RayOnto.exists_finset_containsRayField hR P M h)).1
  · simp

def levels (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) : Finset ℕ :=
  Classical.choose (GlobalTheory.Plug.TwistLevels.levels_bounded P f Ξ)

def raySets (hR : GlobalTheory.NT.RayField) (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) : Finset ℂ :=
  (levels P f Ξ).biUnion (raySet hR P)

theorem raySets_alg (hR : GlobalTheory.NT.RayField) (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) :
    ∀ z ∈ raySets hR P f Ξ, IsAlgebraic ℚ z := by
  intro z hz
  obtain ⟨M, -, hz⟩ := Finset.mem_biUnion.1 hz
  exact raySet_alg hR P M z hz

theorem rayRec_of_has (hR : GlobalTheory.NT.RayField) {K : Ctx} (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T)
    (hH : ∀ z ∈ raySets hR X.B.toPre f (T.set f), ∃ x : X.B.LL, X.B.embLL x = z) : RayRec X.toD7 c.O.nch := by
  intro w Sp hSp
  have hspec := Classical.choose_spec (GlobalTheory.Plug.TwistLevels.levels_bounded X.B.toPre f (T.set f))
  have hM : X.B.host.g 0 * X.B.host.g 1 * ∏ q ∈ Sp.image (fun Q => Nat.card (kP Q)), q ∈ levels X.B.toPre f (T.set f) := by
    refine hspec.2 X.B rfl T HEq.rfl w Sp ?_
    intro P hP
    rcases hSp P hP with ⟨h1, -⟩ | ⟨hmu, hmem⟩
    · exact Or.inl h1
    · right
      have hw : w ∈ c.Wt := by_contra fun h => hmu (c.mu.off w h)
      rw [← (c.nch_Q w hw).1]
      exact hmem
  have hM0 := hspec.1 _ hM
  have hrs := (Classical.choose_spec (GlobalTheory.RayOnto.exists_finset_containsRayField hR X.B.toPre _ hM0)).2
  refine hrs X.B.LL X.B.embLL (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK X.toD7) ?_ ?_
  · ext x
    exact DFunLike.congr_fun X.B.embE_φ₀ _
  · intro z hz
    refine hH z (Finset.mem_biUnion.2 ⟨_, hM, ?_⟩)
    rw [raySet, dite_eq_left hM0]
    exact hz

end GlobalTheory.Plug.RayLarge


open GlobalTheory.Plug.RayLarge in
theorem GlobalTheory.Plug.largeBaseProperty_rayProperty : GlobalTheory.NT.RayField → ∀ (KP : ∀ B : Base, Fr B.toPre → Prop) (Q : V4.Slot), LargeBaseCondition KP Q RayPosition := by
  intro hR KP Q
  exact ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    ⟨0, fun K _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B f _ _ Ξ => raySets hR B f Ξ, by simp,
      fun B f _ _ Ξ => raySets_alg hR B f Ξ,
      fun B f T _ hH _ _ _ C W V S N G c _ => rayRec_of_has hR ⟨B, C, W, V, S, N, G⟩ f T c fun z hz => hH.2 z hz⟩⟩⟩⟩⟩⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreSlotRX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug

theorem coreCondition_RX : ∀ (𝒮 : Slots), 𝒮.Rx = RX → CoreSlot 𝒮 := by
  intro 𝒮 h K B f T w Z Wt p0 t hx
  rw [h] at hx
  exact ⟨hx.laws, hx.canon, hx.rank, hx.pb⟩

end GlobalTheory.Plug
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoTies

theorem twAllAt_tr {D : D7} (N : ∀ u, Submodule (NumberField.RingOfIntegers D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    {x : NChoice D} {y : ThData D} (H : DQ.TwAllAt D x y) : DQ.TwAllAt (setDiv D N h) (nchTr N h x) (xdTr N h y) := by
  obtain ⟨hc, N0, S, H⟩ := H
  refine ⟨hc, N0, S, fun w hw => ⟨(H w hw).1, fun a ha => ?_⟩⟩
  obtain ⟨h1, h2, h3, ⟨e, h4, h4', h4''⟩, h5, h6⟩ := (H w hw).2 a ha
  exact ⟨h1, h2, h3, ⟨e, h4, h4', fun s hs => (sLen_tr N h _ s _ _ _).trans_le (h4'' s hs)⟩, h5, h6⟩

theorem twAll_pt {K : Ctx} (β : BPt K) : DQ.TwAllAt β.D β.O.ex.nch β.O.ex.xd := twAllAt_tr (nPrime β.p.L) β.p.ht β.twAll


end GlobalTheory.GeoTies
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up.LiTw

section Gen

variable {D : D7} (N : TwNew D)

theorem goodL_eq (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) :
    goodL N.toD7 (N.rat S) θ j = goodL D S θ j := by
  have h : N.ex.eLL0 = D.nexp.eLL0 := funext fun g =>
    Subtype.ext (D.what₂.embLL.injective ((N.h0 g).trans (D.nStage_trivialCharacter_coeff_eq g).symm))
  exact congrArg (fun e : G0g D.nd → ↥D.LL0 =>
    Module.End.eigenspace (∑ᶠ g : G0g D.nd, ((e g : ↥D.LL0) : D.what₂.LL) • actL D S j g) 1 ⊓
    ⨅ u : Formalism.IndefR.NX.U D.nd, Module.End.eigenspace (actL D S j u)
      (((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) h

def ratIn {S : RatDat D.ntw} (I : RatIn D S) : RatIn N.toD7 (N.rat S) where
  Sb := I.Sb
  rho := I.rho
  chi := I.chi
  ks := I.ks
  fd := I.fd
  mk_fg := I.mk_fg
  hL := I.hL
  hs := I.hs
  hL_zero := I.hL_zero
  θ := I.θ
  θ_ne := I.θ_ne
  eig := I.eig
  span := fun j h1 h2 => by rw [goodL_eq N S I.θ j]; exact I.span j h1 h2
  hL_int := fun j k P h1 h2 => by rw [goodL_eq N S I.θ j]; exact I.hL_int j k P h1 h2

theorem cusp {Rw : RowSide D} (h : RowCusp D Rw) : RowCusp N.toD7 (N.row Rw) := h

theorem mtIn {M tup Q} (h : MtInput D M tup Q) : MtInput N.toD7 (N.mt M) tup Q := { h with }

end Gen

end GlobalTheory.HeightCounting.Up.LiTw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QPlacesOfAdmissibleTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ParaPlace

theorem unr_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt u) (h' : χ'.UnrAt u) : (χ * χ').UnrAt u := fun y hy => by
  change χ.loc u y * χ'.loc u y = 1
  rw [h y hy, h' y hy, one_mul]

end GlobalTheory.LevCmp.ParaPlace
end
