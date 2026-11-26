module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvZrOfInputsRows

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace GlobalTheory.Cp
open _root_.Formalism _root_.Formalism.L2 _root_.Formalism.L2.DIV Formalism.DivisionValues Formalism.EigenvalueLevelCeiling _root_.Formalism.L2.Indef
section ColRec
open Formalism.BasicNotions _root_.Formalism.L2.Col
variable {X : Fields} {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 X.K G Pl0 I0 Ty T m} {P1 : Subgroup G} {ψ1 : P1 →* X.Kˣ}
end ColRec
section IndefiniteRowSideFullHecke
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions _root_.Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
def ColumnRecordCompatible (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL))
    (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs) : Prop :=
  T.ker.X = fieldsLL D X e ∧ c.Rk = D.R ∧ HEq c.Pr T.ker.Pr ∧ HEq c.Ch T.ker.Ch ∧ HEq c.sel T.ker.sel ∧ HEq c.Sg T.ker.S ∧
    HEq c.mu (fun t => T.ker.tup (P.I.tup t)) ∧ HEq c.cst (fun t => T.ker.cst (P.I.tup t)) ∧
    HEq c.Li (fun t => T.ker.idx (P.I.tup t)) ∧ c.m2 = T.ker.m2 ∧ HEq c.Gc T.ker.glob ∧
    HEq c.Am (Formalism.L2.Ker.ambOf T.ker.seam T.ker.B T.ker.χ T.ker.cD) ∧ c.Mem = D.what₂.Word ∧ HEq c.wd T.ker.word
structure SquareIntegrableColumns (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) : Type 1 where
  X : Formalism.L2.Col.Fields
  e : X.Tau → (X.E →+* D.what₂.LL)
  c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs
  Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)
  colTie : ColTie3 P X e c Sp
  kerTie : _root_.GlobalTheory.Cp.ColumnRecordCompatible T P X e c
  wTie : ∀ u, HEq (P.I.wU u) u
  lvTie : c.Lv = Formalism.L2.Col.rPsymF (R := c.Rk) c.Ch
  sgTie : c.Am.σ₀ = D.what₂.embLL
  v0 : InfinitePlace D.what₂.LL
  TU : Finset (Tup X.F X.E D.what₂.LL c.Sg)
  xiVal : Tup X.F X.E D.what₂.LL c.Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ
  trIv : Fin c.Rk.m → (Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL
  famEq : HEq P.A3 (colIn3 c.W c.Ch c.sel c.hX v0 TU c.Xg ∅ xiVal trIv)
  gEq : P.Gp = Formalism.L2.Col.G0 X.E c.Pr.vGs c.Rk.r
  plEq : P.Pl0 = Formalism.L2.Col.LevOff ∅ c.Pr.vGs ∅
  i0Eq : P.I0 = Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅
  tEq : P.T = TupF (X := fieldsLL D X e) TU
  muTie : ∀ t, c.mu t = (cast tEq t).1
  ok1 : P.A3.fam3.Ok3 1
end IndefiniteRowSideFullHecke
end GlobalTheory.Cp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVRecBridgeSel
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV
section Congr
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ} {A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m}
  {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ} {X0 : Formalism.BasicNotions.BaseLevelRowSide D}
end Congr
section Sel
open Formalism.MainNotions Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
def ColumnRecordCompatible (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL))
    (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs) : Prop :=
  T.ker.X = fieldsLL D X e ∧ c.Rk = D.R ∧ HEq c.Pr T.ker.Pr ∧ HEq c.Ch T.ker.Ch ∧ HEq c.sel T.ker.sel ∧ HEq c.Sg T.ker.S ∧
    HEq c.mu (fun t => T.ker.tup (P.I.tup t)) ∧ HEq c.cst (fun t => T.ker.cst (P.I.tup t)) ∧
    HEq c.Li (fun t => T.ker.idx (P.I.tup t)) ∧ c.m2 = T.ker.m2 ∧ HEq c.Gc T.ker.glob ∧
    HEq c.Am (Formalism.L2.Ker.ambOf T.ker.seam T.ker.B T.ker.χ T.ker.cD) ∧ c.Mem = D.what₂.Word ∧ HEq c.wd T.ker.word
end Sel
section RowsK
open Formalism.MainNotions Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
structure DivisionKernelData (ex : Extra D L hT Gi Gl Kc Y cX) : Type 1 where
  T : _root_.Formalism.L2.TiedDataSKAlt ex
  P : RowSideFamily ex
  hr : RowsHold0_3 P
  X : Formalism.L2.Col.Fields
  e : X.Tau → (X.E →+* D.what₂.LL)
  c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs
  Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)
  Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3
  colTie : ColTie3 P X e c Sp
  kerTie : _root_.Formalism.L2.DIV.ColumnRecordCompatible T P X e c
  wTie : ∀ u, HEq (P.I.wU u) u
  lvTie : c.Lv = Formalism.L2.Col.rPsymF (R := c.Rk) c.Ch
  sgTie : c.Am.σ₀ = D.what₂.embLL
  v0 : InfinitePlace D.what₂.LL
  TU : Finset (Tup X.F X.E D.what₂.LL c.Sg)
  xiVal : Tup X.F X.E D.what₂.LL c.Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ
  trIv : Fin c.Rk.m → (Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL
  famEq : HEq P.A3 (colIn3 c.W c.Ch c.sel c.hX v0 TU c.Xg ∅ xiVal trIv)
  gEq : P.Gp = Formalism.L2.Col.G0 X.E c.Pr.vGs c.Rk.r
  plEq : P.Pl0 = Formalism.L2.Col.LevOff ∅ c.Pr.vGs ∅
  i0Eq : P.I0 = Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅
  tEq : P.T = TupF (X := fieldsLL D X e) TU
  muTie : ∀ t, c.mu t = (cast tEq t).1
  ok1 : P.A3.fam3.Ok3 1
structure SquareIntegrableColumns (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) : Type 1 where
  X : Formalism.L2.Col.Fields
  e : X.Tau → (X.E →+* D.what₂.LL)
  c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs
  Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)
  colTie : ColTie3 P X e c Sp
  kerTie : _root_.Formalism.L2.DIV.ColumnRecordCompatible T P X e c
  wTie : ∀ u, HEq (P.I.wU u) u
  lvTie : c.Lv = Formalism.L2.Col.rPsymF (R := c.Rk) c.Ch
  sgTie : c.Am.σ₀ = D.what₂.embLL
  v0 : InfinitePlace D.what₂.LL
  TU : Finset (Tup X.F X.E D.what₂.LL c.Sg)
  xiVal : Tup X.F X.E D.what₂.LL c.Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ
  trIv : Fin c.Rk.m → (Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL
  famEq : HEq P.A3 (colIn3 c.W c.Ch c.sel c.hX v0 TU c.Xg ∅ xiVal trIv)
  gEq : P.Gp = Formalism.L2.Col.G0 X.E c.Pr.vGs c.Rk.r
  plEq : P.Pl0 = Formalism.L2.Col.LevOff ∅ c.Pr.vGs ∅
  i0Eq : P.I0 = Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅
  tEq : P.T = TupF (X := fieldsLL D X e) TU
  muTie : ∀ t, c.mu t = (cast tEq t).1
  ok1 : P.A3.fam3.Ok3 1
def SquareIntegrableColumns.toK {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) (hr : RowsHold0_3 P)
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) : _root_.Formalism.L2.DIV.DivisionKernelData ex where
  T := T
  P := P
  hr := hr
  X := K.X
  e := K.e
  c := K.c
  Sp := K.Sp
  Zsc := Zsc
  colTie := K.colTie
  kerTie := K.kerTie
  wTie := K.wTie
  lvTie := K.lvTie
  sgTie := K.sgTie
  v0 := K.v0
  TU := K.TU
  xiVal := K.xiVal
  trIv := K.trIv
  famEq := K.famEq
  gEq := K.gEq
  plEq := K.plEq
  i0Eq := K.i0Eq
  tEq := K.tEq
  muTie := K.muTie
  ok1 := K.ok1
def DivisionKernelData.toT (R : _root_.Formalism.L2.DIV.DivisionKernelData ex) : DivisionRowsColumns L :=
  { DivisionRowsColumns.split_model_to_place_model (L := L) R.P R.hr R.X R.e R.c R.Sp R.Zsc with s := 1, hOk := R.ok1 }
structure DivisionPackageKernel' (Q : _root_.Formalism.L2.DIV.DivisionKernelData ex) (C Cabs : ℝ) extends DivisionPackageColumns Q.toT C Cabs where
  tupTie : ∀ t, tup t = Q.P.I.tup t
  evTie : ∀ t (F : Fin ((Q.P.A3.side3 Q.P.Ps Q.P.ψs Pk.Zs).nV t) → D.what₂.LL),
    HEq (eV t F) (Q.P.I.jA t ((rV0 D Q.P.A3.A Q.P.Ps Q.P.ψs t).mulVec F))
  wuTie : ∀ u, HEq (wU u) u
theorem pkg_of_rowsK_alt (R : _root_.Formalism.L2.DIV.DivisionKernelData ex)
    (hR : DivRows3 D R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.P.Zs R.P.S0 R.P.S1 ex.p0 R.P.C R.P.NuC R.P.I) (C Cabs Cp CHp : ℝ) (cf : ConvFace R.P.A3.fam3.base3)
    (Pk : IndefPkgR R.P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.c.face R.Sp R.Zsc) cf Cp CHp)
    (hZs : Pk.Zs = R.P.Zs) (hRows : HEq Pk.core.base.toIndefRows (Classical.choose R.hr.rows0))
    (hS1 : HEq Pk.core.cols.toIndefData R.P.S1) (hCol : HEq Pk.core.cols.col R.P.C)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : R.P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (hOpen : ∀ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((R.c.face Pk.Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs Pk.Zs Pk.core.base.toIndefData Pk.core.cols.toIndefData ex.p0
        (R.c.face Pk.Zs)),
      DivTied3 D R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs Pk.Zs Pk.core.base.toIndefData Pk.core.cols.toIndefData ex.p0 Pk.core.cols.col
        NuC I →
      HEq I R.P.I →
      (Formalism.L2.G.ServJointF.ColBrF.mk R.P.A3.fam3.base3 (R.P.A3.side3 R.P.Ps R.P.ψs Pk.Zs) (R.c.face Pk.Zs) I.wU
        (fun u x => I.eNu u x) I.tup (fun t F => I.jA t ((rV0 D R.P.A3.A R.P.Ps R.P.ψs t).mulVec F)) Pk.core.cols.μ).Tied ∧
      ∃ inp : ∀ u, DivInputs0R Pk.core
          (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
          (I.wU u) (Cons.nuOf L u (I.eNu u)) (sgRec L u),
        ∃ hQ : ∀ u, ChainTie (inp u).ch (R.c.memQ (I.wU u)), ∀ u, FirstCols R.c.hE (hQ u))
    (hN : NprimeDef D L) (Z : DivX D) (hk : ∀ σ, Z.kapR σ = Pk.core.cols.κ (InfinitePlace.mk σ))
    (tH : ∀ u, NumRecTieH (ofRecord D L Del h0) L u (letterOf D L Del h0 u) ((D.mem u).A.T) Del h0)
    (hh : ∀ u, D.div.h u = hExpl6 D L Z Ch u)
    (hF : FTie L ((Formalism.IndefR.Cx.faceOf3 R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.c.face R.Sp R.Zsc Pk.Zs).Z.num Cp CHp) eJ)
    (hC0 : 0 ≤ C) (hC1 : 50 * C0 + 10 ≤ C) (hC2 : 60 * ce ≤ C) (hCabs : 1 ≤ Cabs) (hLa : 0 ≤ L.La) :
    Nonempty (_root_.Formalism.L2.DIV.DivisionPackageKernel' R C Cabs) := by
  obtain ⟨C', NuC', I', hT', hC', -, hI'⟩ := ColTie3.transport R.colTie hR
  have hS0 : HEq R.P.S0 Pk.core.base.toIndefData := by
    have key : ∀ (Z1 Z2 : DefSub R.P.A3.fam3.amb3) (R1 : IndefRows (R.P.A3.side3 R.P.P0 R.P.ψ0 Z1))
        (R2 : IndefRows (R.P.A3.side3 R.P.P0 R.P.ψ0 Z2)), Z1 = Z2 → HEq R1 R2 → HEq R1.toIndefData R2.toIndefData := by
      rintro Z1 _ R1 R2 rfl h
      cases h
      rfl
    have h1 := key _ _ _ _ hZs hRows
    rw [Classical.choose_spec R.hr.rows0] at h1
    exact h1.symm
  have hF2 : ∀ Z1 Z2 : DefSub R.P.A3.fam3.amb3, Z1 = Z2 → HEq (R.c.face Z1) (R.c.face Z2) ∧ HEq (R.Sp Z1) (R.Sp Z2) := by
    rintro _ _ rfl
    exact ⟨HEq.rfl, HEq.rfl⟩
  obtain ⟨NuC'', I'', hT'', -, hI''⟩ := divTied3_congr hZs.symm hS0 hS1.symm (hF2 _ _ hZs.symm).1 (hF2 _ _ hZs.symm).2
    (hC'.trans hCol.symm) hT'
  have hII : HEq I'' R.P.I := hI''.trans hI'
  obtain ⟨htup, hjA, hwU⟩ := divTieDat3_heq hZs hS0.symm hS1 ((hF2 _ _ hZs).1.trans (heq_of_eq R.colTie.1)) hII
  obtain ⟨hbr, inp, hQ, h0c⟩ := hOpen NuC'' I'' hT'' hII
  let x := DivisionPackageColumns.ofTied R.P R.hr R.X R.e R.c R.Sp R.Zsc C Cabs Cp CHp cf Pk hZs hRows NuC'' I'' hT'' hbr Del h0 lam0 C0 ce Ch Sw C1
    eJ H inp hQ h0c hN Z hk tH hh hF hC0 hC1 hC2 hCabs hLa
  refine ⟨{ toDivisionPackageFace := x.toDivisionPackageFace, hQ := x.hQ, h0 := x.h0, tupTie := ?_, evTie := ?_, wuTie := ?_ }⟩
  · exact fun t => congrFun htup t
  · exact fun t F => hjA t _
  · exact fun u => (hwU u).trans (R.wTie u)
abbrev divisionKernelToColumns {eps : ℝ} {Fm : FamP eps}
    (Rk : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.DIV.DivisionKernelData (Fm.ex x hx i)) :
    Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsColumns (Fm.L x i) :=
  ⟨Rk.1, fun x hx h i => (Rk.2 x hx h i).toT⟩
structure DivisionKernelConstantBounds {eps : ℝ} (Fm : FamP eps)
    (Rk : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.DIV.DivisionKernelData (Fm.ex x hx i)) (Cabs CH : ℝ) : Prop where
  pkg : DIVinN Fm → ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Rk.1 ≤ x) (i : Fm.Ix x), Nonempty (_root_.Formalism.L2.DIV.DivisionPackageKernel' (Rk.2 x hx h i) C Cabs)
  adm2 : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i)
  cut : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ μ, Formalism.BasicNotions.DV.Used (Fm.D x i) μ → Formalism.L2.G.ServJoint.CutUp (Fm.D x i) μ
  c3 : ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Compl3 (Fm.L x i) (Fm.X x i) Fm.Csz C
  hh : DIVinN Fm → Formalism.MainNotions.LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH
  c2 : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm
  c5 : Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm
  bu : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational
  rr : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull
  la : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La
theorem DivisionKernelConstantBounds.toT {eps : ℝ} {Fm : FamP eps}
    {Rk : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.DIV.DivisionKernelData (Fm.ex x hx i)} {Cabs CH : ℝ}
    (B : _root_.Formalism.L2.DIV.DivisionKernelConstantBounds Fm Rk Cabs CH) : BridgeRowsT Fm (_root_.Formalism.L2.DIV.divisionKernelToColumns Rk) Cabs CH := by
  refine {
    pkg := ?_
    adm2 := B.adm2
    cut := B.cut
    c3 := B.c3
    hh := B.hh
    c2 := B.c2
    c5 := B.c5
    bu := B.bu
    rr := B.rr
    la := B.la }
  intro hN
  obtain ⟨C, x0, h⟩ := B.pkg hN
  exact ⟨C, x0, fun x hx0 hx h' i => (h x hx0 hx h' i).map _root_.Formalism.L2.DIV.DivisionPackageKernel'.toDivisionPackageColumns⟩
theorem linkDIVt_of_bridge_kernel {eps : ℝ} (Fm : FamP eps)
    (Rk : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.DIV.DivisionKernelData (Fm.ex x hx i)) (Cabs CH : ℝ)
    (B : _root_.Formalism.L2.DIV.DivisionKernelConstantBounds Fm Rk Cabs CH) : LinkDIVt Fm Cabs CH :=
  linkDIVt_of_rowsT Fm (_root_.Formalism.L2.DIV.divisionKernelToColumns Rk) Cabs CH B.toT
theorem closed_linkDIVt_of_closed_bridge_kernel (𝒟 : FamClass) (Cabs : ℝ)
    (Rk : ∀ {eps : ℝ} (Fm : FamP eps), 𝒟 Fm →
      Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.DIV.DivisionKernelData (Fm.ex x hx i))
    (h : Closed 𝒟 (fun Fm CH => ∀ hc : 𝒟 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm → _root_.Formalism.L2.DIV.DivisionKernelConstantBounds Fm (Rk Fm hc) Cabs CH)) :
    Closed 𝒟 (fun Fm CH => TuSize Fm → Formalism.MainNotions.DGamSize Fm → LinkDIVt Fm Cabs CH) := by
  obtain ⟨e1, he1, hP⟩ := h
  refine ⟨e1, he1, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hP e he hle
  exact ⟨K, fun Fm CH hc hL hT hG => _root_.Formalism.L2.DIV.linkDIVt_of_bridge_kernel Fm (Rk Fm hc) Cabs CH (hK Fm CH hc hL hc hT hG)⟩
end RowsK
end Formalism.L2.DIV
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.NLink
variable {D : D7}
structure SetupAlt (L : SizeData₂ D) (nch : NChoice D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (C₂ : ℝ) : Prop where
  facts : _root_.GlobalTheory.NFacts.NormChoiceFacts D nch
  canon : GlobalTheory.HubX.Canon L HW (rowC C₂) X
  par : AdmissibleParameterJ.AdmPar L
  par67 : EmbeddingTypeJumps.ParametersPolynomiallyBounded L
  big : 8 ≤ L.sc.L
  split : 60 ≤ D.host.splitBound
  kill : KillingConditions.KillAt X.ρ
  sha : TwistedPlaces.ShaFinOdd D
def ExtraAlt (D : D7) (C : ℝ) (CT : ℕ) : Prop := KillingConditions.CommutingEndomorphismCondition D ∧ _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT
def FactsFAlt {eps : ℝ} (Fm : FamP eps) (C : ℝ) (CT : ℕ) : Prop :=
  ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x i) (Fm.ex x hx i).nch ∧ _root_.GlobalTheory.NLink.ExtraAlt (Fm.D x i) C CT
def BoundAtTwoThreeFamilyFonAlt {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ → BoundAtTwoThree (Fm.L x i) X.ρ C
end GlobalTheory.NLink
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsRowPin
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
namespace Formalism.L2.Rows
open Formalism.L2.DIV Formalism.L2.Indef
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
def LowerMapTieTwAlt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSKAlt ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m) : Prop :=
  IsUnit (Formalism.L2.Forms.bZ u (T.tw.pt.til u μ hμ h1).z0).det → ∀ (ψ : (D.PTw u μ).Wz) (c : (ex.tw.fm u μ).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, T.tw.ptE.eWz u μ ψ c s =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u D.R.m)) (Formalism.L2.Forms.mZ u (T.tw.pt.til u μ hμ h1).z0) P
        (Formalism.L2.Forms.twYS T.tw.ch T.cols.forms u μ D.R.m le_rfl s)) →
    (T.tw.pt.val u μ hμ).eW ((D.PTw u μ).lowerMap ψ) c =
      Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen D u P)
end Formalism.L2.Rows
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvZrOfInputsRowsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedMultiplicity_of_inputs : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → _root_.GlobalTheory.NRows.PointConditions' D → SumRepresentations.ReducedMultiplicityStatement D := by
  first | exact @_root_.GlobalTheory.PtSt.reducedMultiplicity_of_rows' | exact _root_.GlobalTheory.PtSt.reducedMultiplicity_of_rows' | (intros; apply _root_.GlobalTheory.PtSt.reducedMultiplicity_of_rows' <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHostDatum
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Published GlobalTheory.Mem.HD
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.HostDatumExists
theorem exists_hostDatum_alt : GlobalArtinReciprocity → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (T : _root_.Formalism.L2.TiedDataSAlt ex), HostPins D ex.nch → ∀ B : PlacesOverCommonPrime D.host, ∃ hd : _root_.Formalism.L2.HostDatumWithTies T, hd.d3b = B := by
  intro hA D L hT Gi Gl K Y cX ex T hP B
  obtain ⟨M, hM, hO⟩ := hP.hilb
  have hφ : T.host.fr.ι.comp T.host.fr.j.toRingHom = D.host.φ₀ := RingHom.ext T.host.fr.phi0
  have hE : IsTotallyComplex D.host.E := inferInstance
  obtain ⟨nf, h1, h2, h3⟩ := GlobalTheory.HilbertInClosure.rayField_top_maximal_unramified hA D.host.E T.host.fr.j T.host.fr.ι M
    (by rw [hφ]; exact hM)
  rw [T.host.fr.range] at h1 h3
  have hS : (⋃ w ∈ {w | D.what₂.muAt w ≠ D.what₂.mu0},
      (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.under (𝓞 D.host.K)) '' (ex.nch.Q w : Set (PlE D.host))).Finite :=
    hP.fin.biUnion fun w _ => (ex.nch.Q w).finite_toSet.image _
  choose rep hrep hcop hpr using exists_reps D.host.K (fun u => (D.mem u).A.T) (fun u => (D.mem u).A.T_prime.ne_zero) _ hS
  have hgal : IsGalois ℚ T.host.LLQ := by
    have := hP.gal
    exact IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField T.host.jLL.toRatAlgHom)
  refine ⟨{ d3b := B
            Tu_g := hP.Tu_g
            Qw_Tu := hP.Qw_Tu
            clsK := ⟨rep, hrep⟩
            clsK_Tu := hcop
            clsK_Qw := fun w hw v hv c => hpr c _ (Set.mem_biUnion hw ⟨v, hv, rfl⟩)
            LLgal := hgal
            HE := qb T.host.fr.ι M
            HE_fd := inferInstance
            HE_hilb := ⟨h1, h2, fun L' _ hL hU => @h3 L' {} hL hU⟩
            HE_le := le_of_integral fun x hx hi => ?_ }, rfl⟩
  obtain ⟨y, hy⟩ := hO (T.host.fr.ι x) hx (hi.map T.host.fr.ι.toIntAlgHom)
  refine ((T.what₂.O.range x).1 ⟨y, T.host.fr.ι.injective ?_⟩).1
  rw [T.host.embLL, hy]
end GlobalTheory.HostDatumExists
end
end
