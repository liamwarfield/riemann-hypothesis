module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedFlatBundleRanks
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfRead

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRowsKCColPins
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRowsKCColPins
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.SelC
section Gen
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
  (P : LevFam X.E X.K R.r Pr.vGs)
end Gen
section Main
variable {B : Base} {X : PreX B.toPre} {I : TC B X}
variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
  {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
  {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX}
def squareIntegrableColumnsOfKernel (hOk : (famC I hX U Xg tr).fam3.Ok3 1) (T : _root_.Formalism.L2.TiedDataSKAlt ex) (hS : I.StdKer l Z T.ker)
    (Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs))
    (R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp)
    (htup : R.I.tup = ixOf I U) (hw : ∀ u, R.I.wU u = u) : _root_.Formalism.L2.DIV.SquareIntegrableColumns T R.extendedDatum where
  X := B.fields
  e := B.tauLL
  c := colRecK h hp l Z ht hJ hX U Xg tr T.ker
  Sp := Sp
  colTie := ⟨rfl, HEq.rfl⟩
  kerTie := by
    obtain ⟨h1, h2, h3⟩ := tup_heq ht U T.ker.X hS.X_eq T.ker.Pr T.ker.sel T.ker.S T.ker.tup T.ker.cst T.ker.idx hS.Pr hS.sel hS.S hS.tup
      hS.cst hS.idx
    rw [← htup] at h1 h2 h3
    exact ⟨hS.X_eq, rfl, hS.Pr.symm, hS.Ch.symm, hS.sel.symm, heq_of_eq hS.S.symm, h1, h2, h3, hS.m2.symm, hS.glob.symm, hS.amb.symm, rfl,
      hS.word.symm⟩
  wTie := fun u => heq_of_eq (hw u)
  lvTie := rfl
  sgTie := rfl
  v0 := InfinitePlace.mk B.embLL
  TU := tuOf I U
  xiVal := xiValOf I
  trIv := tr
  famEq := HEq.rfl
  gEq := rfl
  plEq := rfl
  i0Eq := rfl
  tEq := rfl
  muTie := fun _ => rfl
  ok1 := hOk
section Pins
variable {h hp l Z ht hJ hX U Xg tr} {hOk : (famC I hX U Xg tr).fam3.Ok3 1} {T : _root_.Formalism.L2.TiedDataSKAlt ex} {hS : I.StdKer l Z T.ker}
  {Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)}
  {R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp}
  {htup : R.I.tup = ixOf I U} {hw : ∀ u, R.I.wU u = u}
theorem lamOfCol_colK_eq_lamTrue : _root_.Formalism.L2.DIV.lamOfCol_alt (_root_.GlobalTheory.Mem.R3.SelC.squareIntegrableColumnsOfKernel h hp l Z ht hJ hX U Xg tr hOk T hS Sp R htup hw) = fun u i τ => B.wts.lamTrue u i τ := by
  funext u i τ
  exact congrArg (B.wts.lamTrue u i) (eq_of_heq ((cast_heq _ _).trans (iT_heq l Z hS τ)))
theorem colPins_colK' : _root_.Formalism.L2.DIV.ColumnCharactersCompatible (_root_.GlobalTheory.Mem.R3.SelC.squareIntegrableColumnsOfKernel h hp l Z ht hJ hX U Xg tr hOk T hS Sp R htup hw) := by
  have hM := rowG_ok (Pr := B.primes X) B.wts I.Ch I.sel _ hX I.Ps
    (Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := B.fields) (S := I.S) I.sel)
  exact {
    grpTie := HEq.rfl
    psTie := ⟨HEq.rfl, HEq.rfl⟩
    pointCharacterEq := ⟨HEq.rfl, HEq.rfl⟩
    wOk := (base_fields_primes_ok B X).2.2.1
    chOk := h.ch_ok
    hcTie := fun u τ => heq_of_eq (congrArg (B.hcW u) (eq_of_heq ((cast_heq _ _).trans (iT_heq l Z hS τ))))
    wtTie := by
      rw [_root_.GlobalTheory.Mem.R3.SelC.lamOfCol_colK_eq_lamTrue]
      exact ⟨_, _, wtTie_base I l Z T.ker⟩
    xgTie := fun χ => @mem_iff_XgE _ _ _ _ _ _ _ _ (_) B.embLL R.I.eG _ Xg hOk.ok2.irr R.tied.div.grp.e0 χ
    qNF := fun t => of_forall_ix ht (fun _ _ L => GlobalTheory.QNF.IdxMatNF L) (RcHyp.idxMatNF_of_isTw I h ht) t
    columnEvaluationOk := ⟨hM, fun u => by
      have H := exists_read_fam (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr
        I.Ps hOk.ok2 B.embLL hM
        (A := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Amb) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).eMt u) R.I.tup R.tied.div.tup.mu0 R.tied.div.tup.inj R.I.jA
        (fun t => (R.tied.div.sharp.forms t).li) (fun t => (R.tied.div.sharp.forms t).span) R.Zs
      exact H⟩
  }
end Pins
end Main
set_option maxHeartbeats 1000000 in
theorem exists_rowsKC_colPins_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL))
    (tr : TrI B X) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z))
    (Kc : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX),
    (famC I hX U Xg tr).fam3.Ok3 1 → ∀ (T : _root_.Formalism.L2.TiedDataSKAlt ex), I.StdKer l Z T.ker →
    ∀ (Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)) (P : Formalism.L2.Rows.RowSideFamily ex),
    P.Gp = Gc B X → HEq P.grp (inferInstance : Group (Gc B X)) → P.Pl0 = PlS B X → P.I0 = PlI B X → P.T = TupU I U →
    HEq P.A3 (famC I hX U Xg tr) → HEq P.P0 (lev0 I) → HEq P.ψ0 (chr0 I) → HEq P.Ps (lev1 I) → HEq P.ψs (chr1 I) →
    HEq P.I.tup (ixOf I U) → (∀ u, HEq (P.I.wU u) u) →
    ∀ Zs : DefSub (famC I hX U Xg tr).fam3.amb3, HEq P.Zs Zs → HEq P.Dc ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs) →
    HEq P.Sp (Sp Zs) →
    ∃ K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P, _root_.Formalism.L2.DIV.ColumnCharactersCompatible K ∧ HEq K.c (colRecK h hp l Z ht hJ hX U Xg tr T.ker) ∧ HEq K.Sp Sp ∧ HEq K.c.W B.wts ∧
      HEq (fun Zs => K.c.face Zs) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face ∧ HEq K.c.Xg Xg := by
  intro B X I h hp l Z ht hJ hX U Xg tr L hT Gi Gl Kc Y cX ex hOk T hS Sp P
  obtain @⟨Gp, grp, fin, Pl0, I0, Tt, A3, P0, ψ0, Ps, ψs, Zs', S0, S1, Dc, Sp', C, NuC, J, JA, JM, tied⟩ := P
  intro e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 Zs e13 e14 e15
  dsimp only at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  subst e1 e3 e4 e5
  obtain rfl := eq_of_heq e2
  obtain rfl : fin = fintype_GLs B.fields.E (B.primes X).vGs B.R.r := Subsingleton.elim _ _
  cases e6
  cases e7
  cases e8
  cases e9
  cases e10
  cases e13
  cases e14
  cases e15
  exact ⟨_root_.GlobalTheory.Mem.R3.SelC.squareIntegrableColumnsOfKernel h hp l Z ht hJ hX U Xg tr hOk T hS Sp ⟨Zs, S0, S1, C, NuC, J, JA, JM, tied⟩ (eq_of_heq e11) fun u => eq_of_heq (e12 u),
    _root_.GlobalTheory.Mem.R3.SelC.colPins_colK', HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
end GlobalTheory.Mem.R3.SelC
end
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.Mem.R3.SelC
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
set_option maxHeartbeats 1000000 in
theorem jA_row_alt {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) (r : RXs t) (pin : ColPin w)
    (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (w.D Z) 𝔞 → χ 𝔞 = w.I.chi 𝔞) (a : w.I.ι) (ha)
    (j : (Fin (rDim (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩) → B.LL) → Z.W.Amb a)
    (hj : SameOn (r.all.jA a) j) (Zs : DefSub (famT t).fam3.amb3)
    (F : Fin (((famT t).side3 (lev1 w.I) (chr1 w.I) Zs).nV ⟨w.I.tup a, ha⟩) → B.LL) :
    ∃ z : GlobalTheory.Core.Ht2.RowsK w.I a,
      z.1 = ((colRecC w.ok w.pins w.l Z pin.isTw pin.jets χ hχ t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).ev Zs ⟨w.I.tup a, ha⟩ F).1.1 ∧
      j ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩).mulVec F) = r.e a (Df.toCx w.I t.hX a z) := by
  obtain ⟨z, ⟨F', hF', e1, e2⟩, e3⟩ := r.crd a ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩).mulVec F)
  have e4 := evC_res_lvl (X := B.fields) (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel t.hX (InfinitePlace.mk B.embLL)
    (tuOf w.I (usedOf w.I T Wt)) t.r.z.Xg ∅ (xiValOf w.I) t.r.z.tr (TC.Ps w.I) t.r.intersectionNumber_baseChange.ok.ok2 Zs ⟨w.I.tup a, ha⟩ F
  have e5 := LinearEquiv.injective _ (eq_of_heq (e1.trans (heq_of_eq e4.symm)))
  refine ⟨z, ?_, (hj.2 _ _ fun i i' e => congrArg _ (Fin.ext e)).symm.trans e3⟩
  rw [e2]
  exact congrArg Subtype.val e5
variable {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
set_option maxHeartbeats 1000000 in
theorem exists_readC_wU_eq_id (t : RowsT K w Z Wt ex.p0) (r : RXs t) (pin : ColPin w) (k : Formalism.L2.Ker.KerEntTied ex) (Sp Zsc) :
    ∃ C : ReadC t.r.z.R (reFace t.r.z.F
      (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr k).face Sp Zsc) ex.p0 t.r.Y,
      C.wU = fun u => u := by
  choose e he hn using exists_eNu w.ok w.l Z t.hX w.l0
  refine ⟨{ wU := fun u => u
            bij := Function.bijective_id
            eNu := e
            NuC := fun u => (Z.V.div.Nu u).L.comap ((e u).toLinearMap.restrictScalars (𝓞 B.LL))
            nu := fun u => ⟨(Submodule.map_comap_eq_of_surjective (f := (e u).toLinearMap.restrictScalars (𝓞 B.LL)) (e u).surjective _).symm, he u⟩
            pt := fun u s x F => ?_ }, rfl⟩
  have key : ∀ (a : w.I.ι) (s : TupU w.I (usedOf w.I T Wt)) (_ : w.I.tup a = s.1)
      (j : (Fin (rDim (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) s) → B.LL) → Z.W.Amb a) (_ : SameOn (r.all.jA a) j)
      (Zs : DefSub (famT t).fam3.amb3) (F : Fin (((famT t).side3 (lev1 w.I) (chr1 w.I) Zs).nV s) → B.LL),
      B.embLL (((colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr k).face Zs).Pt u s x F) =
        Z.W.perCol u a (Z.V.jN u (e u x)) (j ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) s).mulVec F)) := by
    rintro a ⟨τ, ha⟩ (rfl : w.I.tup a = τ) j hj Zs F
    obtain ⟨z, hz, e1⟩ := _root_.GlobalTheory.Mem.R3.SelC.jA_row_alt t r pin k.χ (ker_chi_eq w.I w.l Z k) a ha j hj Zs F
    rw [e1]
    exact face_pt w.ok w.pins w.l Z pin.isTw pin.jets k.χ (ker_chi_eq w.I w.l Z k) t.hX w.l0 r.e r.eMt0 r.eMtTw _ _ _ Zs u a ha x _
      (hn u x) F z hz
  exact key (t.r.Y.tup s) s ((congrArg w.I.tup (t.r.tup_ix s)).trans (tup_ixOf w.I s)) (t.r.Y.jA s) (r.jA_use s) _ F
set_option maxHeartbeats 400000 in
theorem args_pinned_heq_zsOf_mem_eq (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t) :
    (a.x.G = Gc B w.px ∧ HEq a.x.grp (inferInstance : Group (Gc B w.px)) ∧ a.x.Pl0 = PlS B w.px ∧ a.x.I0 = PlI B w.px ∧
      a.x.T = TupU w.I (usedOf w.I T Wt) ∧ HEq a.x.A3 (famC w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr)) ∧
    (HEq a.x.F.P0 (lev0 w.I) ∧ HEq a.x.F.ψ0 (chr0 w.I) ∧ HEq a.x.F.P1 (lev1 w.I) ∧ HEq a.x.F.ψ1 (chr1 w.I) ∧ HEq a.x.F.Dc a.Dc ∧
      HEq a.x.F.Sp a.Sp) ∧
    ∃ Zs : DefSub (famT t).fam3.amb3, HEq (zsOf a.x.R a.x.F) Zs ∧ HEq (a.x.F.Dc (zsOf a.x.R a.x.F)) (a.Dc Zs) ∧
      HEq (a.x.F.Sp (zsOf a.x.R a.x.F)) (a.Sp Zs) ∧ (a.x.F.Dc (zsOf a.x.R a.x.F)).Mem = (a.Dc Zs).Mem := by
  have hpack := @pack_heq (w.st Z).toD7 _ _ a.pack
  dsimp only at hpack
  with_unfolding_all exact ⟨hpack.1, hpack.2.1,
    zsOf ((t.r.z.R.updS t.r.z.R.kap a.lam).withErr a.err) (reFace t.r.z.F a.Dc a.Sp a.Zsc), hpack.2.2⟩
set_option maxHeartbeats 400000 in
theorem exists_square_integrable_columns_of_data (t : RowsT K w Z Wt ex.p0) (pin : ColPin w) (S : _root_.Formalism.L2.TiedDataSKAlt ex) (hS : TC.StdKer w.I w.l Z S.ker)
    (a : TwArgs ex t) (hD : a.Dc = (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face)
    (hw : HEq a.x.C.wU fun u : B.Word => u) :
    ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns S (divisionPairOfAdelicFormsFaceColumnsData a.x), HEq (fun Zs => C.c.face Zs) a.x.F.Dc ∧ HEq C.Sp a.x.F.Sp ∧ HEq C.c.W B.wts ∧
      HEq C.c.Xg t.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, g11, g12⟩, Zs, g13, g14, g15, g16⟩ := _root_.GlobalTheory.Mem.R3.SelC.args_pinned_heq_zsOf_mem_eq t a
  obtain ⟨Sp, hSp⟩ : ∃ Sp : ∀ Zs, SPer ((colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face Zs),
      HEq a.Sp Sp ∧ ∀ Zs, HEq (a.Sp Zs) (Sp Zs) := by
    have key : ∀ Dc : type_of% a.Dc, a.Dc = Dc → ∃ Sp : ∀ Zs, SPer (Dc Zs), HEq a.Sp Sp ∧ ∀ Zs, HEq (a.Sp Zs) (Sp Zs) := by
      rintro _ rfl
      exact ⟨a.Sp, HEq.rfl, fun _ => HEq.rfl⟩
    exact (key (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face hD)
  have e1 := congrFun hD Zs
  have e2 : (a.x.F.Dc (zsOf a.x.R a.x.F)).Mem = B.Word := by
    rw [g16, e1]
    rfl
  have e3 : HEq a.x.Y.tup (ixOf w.I (usedOf w.I T Wt)) := by
    have htup := funext t.r.tup_ix
    with_unfolding_all exact a.tup.trans (heq_of_eq htup)
  have e4 : ∀ u, HEq (a.x.C.wU u) u := fun u => heq_app e2 hw u
  have e5 := g14.trans (heq_of_eq e1)
  have e6 := g15.trans (hSp.2 Zs)
  obtain ⟨C, c1, -, c3, c4, c5, c6⟩ := _root_.GlobalTheory.Mem.R3.SelC.exists_rowsKC_colPins_alt w.I w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr
    L hT Gi Gl Kc Yd cX ex t.r.intersectionNumber_baseChange.ok S hS Sp (divisionPairOfAdelicFormsFaceColumnsData a.x) ((h1)) ((h2)) ((h3)) ((h4)) ((h5))
    ((h6)) ((h7)) ((h8)) ((h9)) ((h10)) ((e3)) ((e4)) Zs ((g13))
    ((e5)) ((e6))
  have d1 := (heq_of_eq hD.symm).trans g11.symm
  refine ⟨_root_.GlobalTheory.Cp.SquareIntegrableColumns.ofS C, HEq.trans (b := (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face)
    ?_ ?_, ?_, ?_, ?_, ?_⟩
  · exact (c5)
  · exact (d1)
  · with_unfolding_all exact c3.trans (hSp.1.symm.trans g12.symm)
  · exact (c4)
  · exact (c6)
  · exact (c1)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem square_integrable_columns_of_witnesses : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex), KPin q t → Nonempty (RXs q.x.what₂) → ∃ Dc Sp₀ Zsc₀, ∃ C₀ : ReadC q.x.what₂.r.z.R (reFace q.x.what₂.r.z.F Dc Sp₀ Zsc₀) q.O.ex.p0 ((q.x.what₂.r.Y)), ∀ (T : _root_.Formalism.L2.TiedDataSKAlt q.O.ex), T.ker = t → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → a.Dc = Dc → HEq x.C.wU C₀.wU → HEq x.C.eNu C₀.eNu → ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns T (divisionPairOfAdelicFormsFaceColumnsData x), HEq (fun Zs => C.c.face Zs) x.F.Dc ∧ HEq C.Sp x.F.Sp ∧ HEq C.c.W q.B.wts ∧ HEq C.c.Xg q.x.what₂.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS := by
  intro 𝒮 K q t hk ⟨r⟩
  obtain ⟨C₀, hC⟩ := _root_.GlobalTheory.Mem.R3.SelC.exists_readC_wU_eq_id (ex := q.O.ex) q.x.what₂ r q.x.pin t (fun _ => ⟨ℂ, inferInstance, inferInstance, fun _ => 0, ⊥⟩)
    q.x.what₂.r.z.F.Zsc
  refine ⟨_, _, _, C₀, fun S hS a x hx hD hw _ => ?_⟩
  subst hS
  cases hx
  exact _root_.GlobalTheory.Mem.R3.SelC.exists_square_integrable_columns_of_data (ex := q.O.ex) q.x.what₂ q.x.pin S hk.std a hD (hw.trans (heq_of_eq hC))
end GlobalTheory.Mem.R3.SelC
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRowsKCColPinsStatement
theorem GlobalTheory.T.exists_square_integrable_columns_of_heq_data :
    type_of% @GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses :=
  @GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingOfSize
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun.SetFromSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
set_option maxHeartbeats 1600000 in
theorem setting_of_size_alt (p : PtAt ex Csz) (hp : p.PointConditions') (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (he : GlobalTheory.GLq.ESerTie D) :
    HidaSetting L p.R.toRealDat p.F.lv2 :=
  { size := hs
    eser := he
    host := p.host
    hF := p.hF
    core := (GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D _ _ _ _ _ _ p.R p.F p.charW hp.exAt).1
    mu_off := p.charW.tup.mu_off
    mu_used := p.charW.tup.mu_used
    mu_ne := p.charW.tup.mu_ne
    mu_conj := p.charW.tup.mu_conj
    mu_on := p.charW.tup.mu_on
    grp := p.charW.base.grp.record
    guard := p.qGuard
    fin := finite_tup p
    fullY := p.charW.fullY
    fullX := p.charW.fullX
    std := p.stdChar
    stdX := p.stdX
    betaX := p.betaStd.2 }
end GlobalTheory.BigTop.Fun.SetFromSize
namespace GlobalTheory.BigTop.Fun
theorem setAt_of_sizeAt_alt (h : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt) : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint :=
  h.imp fun _ _ _ a => _root_.GlobalTheory.BigTop.Fun.evPt_mono a fun _ _ _ p hp b he => _root_.GlobalTheory.BigTop.Fun.SetFromSize.setting_of_size_alt p hp b he
end GlobalTheory.BigTop.Fun
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatBoundOfAnchor
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.FlatLine GlobalTheory.FlatTw
namespace GlobalTheory.FlatSplit
section Congr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}
end Congr
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ)
end Weights
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
theorem flat_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.FlatnessCondition := by
  intro hP hDG hFD hA
  refine Closed.imp (Closed.and (Closed.and (Closed.and (Closed.and hDG (_root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le hFD)) hA) _root_.GlobalTheory.T.lift_weight_numerator)
    (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨⟨C1, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨CA, hCA, h3⟩⟩, ⟨C4, -, h4⟩⟩, ⟨C5, -, h5⟩⟩
  refine ⟨11 * CA + 83, by positivity, ?_⟩
  obtain ⟨x0, hx⟩ := (((h1.and h2).and h3).and h4).and h5
  refine ⟨x0, fun x hx' hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hx x hx' hle ι p hp
  exact _root_.GlobalTheory.FlatSplit.flat_at_of_split_covering p i Y hY hP (a1 i hi Y hY) (a2 i hi Y hY) (a3 i) (a4 i) (a5 i)
end GlobalTheory.FlatSplit
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_prints_deepGood_flatDeg_anchor : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.FlatnessCondition := by
  first | exact @_root_.GlobalTheory.FlatSplit.flat_alt_alt | exact _root_.GlobalTheory.FlatSplit.flat_alt_alt | (intros; apply _root_.GlobalTheory.FlatSplit.flat_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExOfClaims
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExOfClaims
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
open NumberField IsDedekindDomain GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.LeafRestExamples
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000 in
theorem ex_of_claims_alt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.SumOKK → GlobalTheory.RowClaim.SumRatK → GlobalTheory.RowClaim.ConstK → (_root_.GlobalTheory.BigTop.Fun.CharacterAtPoint fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) → GlobalTheory.NormSum.IntSt → FieldDat → TorEx → DenEx → BotEx → BotSmall → _root_.GlobalTheory.BigTop.Fun.ExistsFunctionIn @Fld @Comparison₂ := by
  intro hSet hdl hS hR hC hr hI hFD hT hD hB hBS
  obtain ⟨c1, h1⟩ := hSet.atPt hS
  obtain ⟨c2, h2⟩ := hSet.atPt hR
  obtain ⟨c3, h3⟩ := hSet.atPt hC
  obtain ⟨c4, h4⟩ := hr
  obtain ⟨c5, h5⟩ := Model.gBig_and (Model.gBig_and hT hD) (Model.gBig_and (Model.gBig_and hB hBS) hFD)
  obtain ⟨CI, -, hI⟩ := exists_isIntExp hI
  refine ⟨max (max (max c1 c2) (max c3 c4)) (max c5 CI), fun CF hCF => ?_⟩
  have k1 : c1 ≤ CF := le_trans (by simp) hCF
  have k2 : c2 ≤ CF := le_trans (by simp) hCF
  have k3 : c3 ≤ CF := le_trans (by simp) hCF
  have k4 : c4 ≤ CF := le_trans (by simp) hCF
  have k5 : c5 ≤ CF := le_trans (by simp) hCF
  have k6 : CI ≤ CF := le_trans (by simp) hCF
  obtain ⟨e0, he0, H⟩ := (((h1 CF k1).and (h2 CF k2)).and ((h3 CF k3).and (h4 CF k4))).and (hdl.and hSet)
  refine ⟨e0, he0, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  obtain ⟨C0, x₀, hg⟩ := h5 eps CF k5
  refine ⟨K, fun Fm CH hc hL _ => ?_⟩
  obtain ⟨⟨⟨⟨y1, g1⟩, ⟨y2, g2⟩⟩, ⟨⟨y3, g3⟩, ⟨y4, g4⟩⟩⟩, ⟨y5, g5⟩, ⟨y6, g6⟩⟩ := hK Fm CH hc hL
  refine ⟨max (max (max y1 y2) (max y3 y4)) (max (max y5 y6) x₀), fun x hx hle i p hp G W hW _ hF => ?_⟩
  have l1 : y1 ≤ x := le_trans (by simp) hle
  have l2 : y2 ≤ x := le_trans (by simp) hle
  have l3 : y3 ≤ x := le_trans (by simp) hle
  have l4 : y4 ≤ x := le_trans (by simp) hle
  have l5 : y5 ≤ x := le_trans (by simp) hle
  have l6 : y6 ≤ x := le_trans (by simp) hle
  have l7 : x₀ ≤ x := le_trans (by simp) hle
  obtain ⟨n, a, ha⟩ := hF
  have hset := g6 x hx l6 i p hp ha.eser
  have hrec : Rec (Fm.L x i) := ⟨hset.size, hset.host, hset.hF, g5 x hx l5 i p hp⟩
  obtain ⟨⟨hTor, hDen⟩, ⟨hBot, hSm⟩, hFd⟩ := hg C0 le_rfl _ (Fm.L x i) (Fm.L_eps x i)
    (by rw [Fm.L_x x i hx]; exact l7) hrec _ _ _ hset.core.lev G
  have hb : Real.log (Fm.L x i).sc.b = (Fm.L x i).sc.L := Real.log_exp _
  have hL1 : 1 ≤ (Fm.L x i).sc.L :=
    Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hlog1 : 1 ≤ Real.log (Fm.L x i).sc.b := hb ▸ hL1
  have hrd : Real.log (Fm.D x i).host.rdE ≤ Real.log (Fm.L x i).sc.b := by
    have e1 := hset.size.2.2.2.2.2.2.2.2.2.1
    have e2 := hset.size.2.2.2.2.2.2.2.2.2.2.1
    rw [hb]; linarith
  obtain ⟨dl, hdl⟩ := hI _ _ _ _ G hSm.1 hlog1 hrd
  obtain ⟨δ, t0, hBot'⟩ := hBot
  obtain ⟨_, _, _, _, Λ, hΛ⟩ := hFd
  refine TieModel.exists_tie hW a ha (g1 x hx l1 i p hp G W n a ha) (g2 x hx l2 i p hp G W n a ha ha.field)
    (g3 x hx l3 i p hp G W n a ha) (g4 x hx l4 i p hp G W n a ha)
    ⟨δ, t0, fun ij => let ⟨P, P', h⟩ := hBot' ij; ⟨P, P', h, trivial, trivial⟩⟩ (fun ij s hs1 hs2 => ?_)
    ⟨dl, TieModel.isIntExp_mono (zero_le_one.trans hlog1) hdl k6⟩
  obtain ⟨nn, hnn, hfin⟩ := hDen ij.1 ij.2 s hs1 hs2
  obtain ⟨x0', hx0, hx0ne, -, halg⟩ := hTor ij.1 ij.2 s hs1 hs2 none
  have hz : ∀ c : Bool, ∃ z, IsTor G ij.1 ij.2 s (nuH G p.P.A3.A.μ0 ij.1 ij.2 * delOf _ c)
      ((Fm.D x i).what₂.embLL z * x0') := fun c => by
    obtain ⟨y, hy, -⟩ := hTor ij.1 ij.2 s hs1 hs2 (some c)
    obtain ⟨z, hz⟩ := ha.sq.toric ij.1 ij.2 s c x0' y hs1 hs2 hx0 hy
    exact ⟨z, by rw [hz, div_mul_cancel₀ _ hx0ne]; exact hy⟩
  choose zd hzd using hz
  obtain ⟨pp, hpp⟩ := exists_isMinPol (σ := (Fm.D x i).what₂.embLL) (halg Λ hΛ)
  exact ⟨zd, fun w => truncZero (meanVal_vw w pp / 12), nn, ⟨x0', hx0, hx0ne, hzd, Λ, pp, hΛ, hpp, fun w => rfl⟩, hnn, hfin⟩
end GlobalTheory.BigTop.Fun
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExOfClaimsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsFunctionIn_of_sqRatio_range : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.SumOKK → GlobalTheory.RowClaim.SumRatK → GlobalTheory.RowClaim.ConstK → (_root_.GlobalTheory.BigTop.Fun.CharacterAtPoint fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) → GlobalTheory.NormSum.IntSt → FieldDat → TorEx → DenEx → BotEx → BotSmall → _root_.GlobalTheory.BigTop.Fun.ExistsFunctionIn @Fld @Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.ex_of_claims_alt | exact _root_.GlobalTheory.BigTop.Fun.ex_of_claims_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.ex_of_claims_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShapeAlt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Fc
section Shape
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory _root_.Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT _root_.Formalism.L2.Top3 _root_.Formalism.L2.Top4
set_option linter.unusedVariables false in
def TopShapeAlt (V NR : Prop) (N : FamClass → Prop) (G : Prop) : Prop :=
  ∀     (𝒜 : FamClass)
    (cT : ℝ → ℝ → ℝ)
    (hEx : MinkDiv → UpperTheory.Top.ExS 𝒜 cT)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows (selB Fm hc x hx h i))
    (hTw : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.TieTwRec (Fm.L x i) (selP Fm hc x hx h i).1.S0.Tw)
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hLamP : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.Rows.RowsHoldLam3 (selP Fm hc x hx h i).1)
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (hTu : Closed (WithTw (WithSm (WithChN 𝒜))) fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm)
    (hn4 : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hLit : LitThin)
    (hVC : V)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hTF : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3)
    (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (sTy : Formalism.L2.SG.RowsPos.TypeP)
    (sNG : Formalism.L2.SG.RowsPos.RowNGP)
    (sM : Formalism.L2.SG.RowsPos.RowMainEqP)
    (sLp : Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩))
    (sO : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩)
    (h30 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (hInstR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank)
    (selJ : _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationSelection 𝒜 sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (jOn : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.L2.SG.JoinSISel.BaseVectorImageFull (Fm.D x i))
    (hMt : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (μ : (Fm.D x i).what₂.Tup) (a : NumberField.RingOfIntegers (Fm.D x i).what₂.LL),
      ∀ y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier, (Fm.D x i).what₂.embLL (a : (Fm.D x i).what₂.LL) • y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH)
    (aPt0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u)
    (aPtTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw)
    (aPer0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i))
    (aPerTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw)
    (aP10 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u)
    (aAtG : Closed (D3 3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1)
    (aC2 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm)
    (hServ : _root_.Formalism.L2.G.ServT.SelectionServed (D3 3 𝒜) fun Fm hc => sel Fm (d3_a hc))
    (nR : NR)
    (nRest : N (D3 3 𝒜))
    (cIc : ℝ)
    (hcI : 0 < cIc)
    (irrC : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f))
    (zL : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) (selP Fm (d3_a hc) x hx h i).1.A3.A (selP Fm (d3_a hc) x hx h i).1.P0
          (selP Fm (d3_a hc) x hx h i).1.ψ0 ((selP Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 (selP Fm (d3_a hc) x hx h i).1.Zs) k
          (selP Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec)
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm)
    (hU : ∀ D, MassRatioUnderVolume D)
    (hG : ∀ D, GenusMassVolumes.GenusMassAt D 2) ,
    G
end Shape
end GlobalTheory.Fc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QVecPinTup
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QVecPinTup
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section General
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QVecJoin
open GlobalTheory.QVec GlobalTheory.LocMod.StepVec
end GlobalTheory.QVecJoin
end General
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.QVecJoin
theorem qVec_pinTup_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t,
    _root_.GlobalTheory.Fam.RationalVectorCondition (a.fam row col) ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat J hJ row col hCh sc cT t
  have hC3 := hW.pk.bot.hyp.2.2.2.1
  have hL := hC3.lev
  obtain ⟨hinj, hund⟩ := _root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t (J t) (hJ t)
  have hV := (ha.tie row col).1
  have hQS : ∀ p, p ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q ↔ ∃ i, ((J t).G i).q.v = p := by
    intro p
    simp only [QFam.pinTup, _root_.GlobalTheory.Fam.familyOfRowColumnChoices, Finset.mem_image]
    exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ _, h⟩⟩
  have hSQ : ∀ p, (∃ i, ((J t).G i).q.v = p) ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := by
    intro p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(J t).pl i, (J t).mem i, hund i⟩
    · rintro ⟨PP, hPP, rfl⟩
      obtain ⟨i, rfl⟩ := (hJ t).surj PP hPP
      exact ⟨i, hund i⟩
  have hQiff : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t ↔ ∃ i, (J t).pl i = PP := fun PP =>
    ⟨fun h => (hJ t).surj PP h, by rintro ⟨i, rfl⟩; exact (J t).mem i⟩
  have hrk : ∀ i, (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + (((J t).G i).s + 1) := by
    intro i
    have e1 : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + (I.rec7 l Z).R.m - 1 := rfl
    have e2 : ((J t).G i).s + 1 + 1 = (I.rec7 l Z).R.m := ((J t).G i).hs
    omega
  have gIn : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, ∃ k, (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    refine ⟨k, ?_⟩
    have hmemK : (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.K) ∈ (PP.under (𝓞 (I.rec7 l Z).host.K)).asIdeal := by
      have hk' : PP.under (𝓞 (I.rec7 l Z).host.K) = (_root_.GlobalTheory.Fam.pk_z W).C.P.pb k := hk
      rw [hk']
      exact (_root_.GlobalTheory.Fam.pk_z W).C.P.pb_over k
    have h2 : algebraMap (𝓞 (I.rec7 l Z).host.K) (𝓞 (I.rec7 l Z).host.E) (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  have hoff : ∀ p, (∃ i, ((J t).G i).q.v = p) → p ∉ a.v.gP := by
    intro p hp hxg
    obtain ⟨PP, hPP, rfl⟩ := (hSQ p).1 hp
    obtain ⟨PP', hPP', e⟩ := (hV.gP _).1 hxg
    obtain ⟨k, hk⟩ := gIn PP' hPP'
    have hg : (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal :=
      (natCast_mem_under PP _).1 (e ▸ (natCast_mem_under PP' _).2 hk)
    obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP hPP
    haveI : PP.asIdeal.IsPrime := PP.isPrime
    haveI : Finite (Formalism.L2.DIV.kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
    haveI : Fintype (Formalism.L2.DIV.kP PP) := Fintype.ofFinite _
    have hq0 : ((q : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
      have h0q : ((q : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
        rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (Formalism.L2.DIV.kP PP)
      exact (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).1 (by simpa using h0q)
    exact false_of_coprime_mem PP ((Nat.coprime_primes hq ((I.rec7 l Z).host.g_prime k)).2 (hne k)) hq0 hg
  have hS : (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) = (fun p => ∃ i, ((J t).G i).q.v = p) :=
    funext fun p => propext (hQS p)
  have hmv : ∀ j, j < (I.rec7 l Z).R.m → GlobalTheory.FinPl.Moves _ (a.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (a.v.N j) (fun p => ∃ i, ((J t).G i).q.v = p) :=
    fun j hj => hV.moves j hj _ hoff
  have hb : ∀ j, a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := fun j => (hV.b j) ▸ ha.vis.b j
  have hS' : (fun p => ∃ i, ((J t).G i).q.v = p) = fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) :=
    funext fun p => propext (hSQ p)
  have sdY : ∀ j, j < (I.rec7 l Z).R.m → IsSelfDualC (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) := fun j hj =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hL.βY j hj)
  have sdX : IsSelfDualC (I.rec7 l Z).sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hL.βX
  refine ⟨?_, ?_⟩
  · intro j hj d hd g hg
    have hmid : ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQ j = aconv (List.ofFn fun i => ((J t).E i).eL j) := if_pos hj
    rw [hmid]
    rw [hS] at hg
    exact step_mid (I.rec7 l Z) (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g) a.v (baseOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g) (_root_.GlobalTheory.Fam.chrK_alt W t) ha.vis (J t).r (J t).pl
      (fun i => (J t).G i) (fun i => (J t).E i) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).Q t) _ hinj hQiff (fun p => Iff.rfl) (hJ t).res hrk j hj
      (hmv j (by omega)) (hmv (j + 1) hj) (hb j) (hb (j + 1)) (sdY j (by omega)) (sdY (j + 1) hj) _ _ _ _ _ d rfl rfl
      (GlobalTheory.SeeSaw.Inh.vac_ne_zero hd.2.1) (by rw [hS']; exact hd.1) hd.2 _ _ _ (hC3.chain.ωY t j hj) g hg
  · intro j hj d hd g hg
    rw [hS] at hg
    have hmT : GlobalTheory.FinPl.Moves _ a.g.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX a.v.NT (fun p => ∃ i, ((J t).G i).q.v = p) := by
      rw [hV.bT.2]; exact hV.movesT _
    have hbT : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := by
      have h1 := ha.vis.bT
      rwa [hV.bT.1] at h1
    exact step_top (I.rec7 l Z) (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g) a.v (baseOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g) (_root_.GlobalTheory.Fam.chrK_alt W t) ha.vis (J t).r (J t).pl
      (fun i => (J t).G i) (fun i => (J t).E i) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).Q t) _ hinj hQiff (fun p => Iff.rfl) (hJ t).res hrk j hj
      (hmv (j + 1) (by omega)) hmT (hb (j + 1)) hbT (sdY (j + 1) (by omega)) sdX _ _ _ _ _ d rfl rfl
      (GlobalTheory.SeeSaw.Inh.vac_ne_zero hd.2.1) (by rw [hS']; exact hd.1) hd.2 _ _ _
      (isWeilDatum_cast ((_root_.GlobalTheory.Fam.pk_z W).ωX t) (hC3.chain.ωX t) (j + 1) (idx_top hj)) g hg
end GlobalTheory.QVecJoin
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QVecPinTupStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_identity_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t,
    _root_.GlobalTheory.Fam.RationalVectorCondition (a.fam row col) ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT) := by
  first | exact @_root_.GlobalTheory.QVecJoin.qVec_pinTup_alt | exact _root_.GlobalTheory.QVecJoin.qVec_pinTup_alt | (intros; apply _root_.GlobalTheory.QVecJoin.qVec_pinTup_alt <;> assumption)
end
end
end
