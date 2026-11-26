module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationIdentity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfRead
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPoint

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsLow
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
structure QuadraticExtensionData.ReadsStd (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) : Prop where
  is : J.A.Is
  inj : Function.Injective J.pl
  surj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, J.pl i = PP
  chr : ∀ j, j < B.R.m → J.A.chr (j + 1) = _root_.GlobalTheory.Fam.chrK_alt W t j
  res : ∀ i, (J.G i).Res (J.E i).δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t (J.pl i))
  eq : ∀ i, (J.P i).1 = J.pl i
  sg : ∀ i, J.sg i = 1 ∨ J.sg i = -1
  tw : ∀ i, GlobalTheory.TwBridge.AtTwist (R := B.R) (k := (J.G i).k) I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
    ((J.G i).q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i))
  M : ∀ i, (J.E i).M = (I.cst (W.P.I.tup t)).M
  rep : ∀ i j d (h : j + d = (J.G i).s) (hj : j < B.R.m) β,
    GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := (J.G i).k) ((J.G i).q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)))
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) ((J.E i).rep j d h (J.π i j β))
  orb : ∀ i β (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e →
      SameOrb (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (box _ ((J.G i).ϖ ^ (J.E i).M))
        ((J.E i).cos (J.π i ((J.G i).s + 1) β))
        (Submodule.Quotient.mk fun r => (ofSplit (J.G i).q).pr (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2 (e r)))
  std : ∀ j, j < B.R.m → ∀ β, J.A.kb j β = TC.kStd X u (B.R.N j)
  last : Nonempty (Unique (J.Ch₀ B.R.m))
  sec : ∀ j, j ≤ B.R.m → ∀ y i, J.π i j (J.ι j y) = y i
  cosG : ∀ (n : Fin a.n) y (e : XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ r,
      (ofSplit (a.G n).q).pr (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ y)).1.2 (e r)) - (a.G n).S.y0 (Fin B.R.t) r ∈ 𝒪[(a.G n).k]
  live : J.A.Live J.ι
structure QuadraticExtensionData.ReadsLow (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) : Prop where
  is : J.A.Is
  inj : Function.Injective J.pl
  surj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, J.pl i = PP
  chr : ∀ j, j < B.R.m → J.A.chr (j + 1) = _root_.GlobalTheory.Fam.chrK_alt W t j
  res : ∀ i, (J.G i).Res (J.E i).δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t (J.pl i))
  eq : ∀ i, (J.P i).1 = J.pl i
  sg : ∀ i, J.sg i = 1 ∨ J.sg i = -1
  tw : ∀ i, GlobalTheory.TwBridge.AtTwist (R := B.R) (k := (J.G i).k) I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
    ((J.G i).q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i))
  M : ∀ i, (J.E i).M = (I.cst (W.P.I.tup t)).M
  rep : ∀ i j d (h : j + d = (J.G i).s) (hj : j < B.R.m) β,
    GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := (J.G i).k) ((J.G i).q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)))
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) ((J.E i).rep j d h (J.π i j β))
  std : ∀ j, j < B.R.m → ∀ β, J.A.kb j β = TC.kStd X u (B.R.N j)
  last : Nonempty (Unique (J.Ch₀ B.R.m))
  sec : ∀ j, j ≤ B.R.m → j + 1 ≠ B.R.m → ∀ y i, J.π i j (J.ι j y) = y i
  injCh : ∀ j, j + 1 ≠ B.R.m → Function.Injective (J.ι j)
  first : Function.Surjective (J.ι 0)
  onto : Function.Surjective (J.ι B.R.m)
  dead : ∀ j (hj : j + 1 ≤ B.R.m), j + 1 + 1 ≠ B.R.m → ∀ γ, γ ∉ Set.range (J.ι (j + 1)) → ∀ α z, J.A.xi j hj α γ z = 0
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenMovedOfReadsStdAtLast
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowZero
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.Fam.TopLoc.LocalIdempotentDensity
open GlobalTheory.SymBridge _root_.Formalism.L2.Col
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
def levelZeroCharacter (hstd : Formalism.L2.Theta.IsStdChar (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ (-1)) (g : Geo (I.rec7 l Z)) (t : W.P.T) :
    RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g t where
  vP := fun _ => 0
  vT := fun _ _ => 0
  sBF := fun _ _ _ => Classical.choice (GlobalTheory.Unf.Inhab.nonempty_stepBF hstd _ _)
  sFB := fun _ _ _ => Classical.choice (GlobalTheory.Unf.Inhab.nonempty_stepFB hstd _ _)
  io := fun _ => 0
  ioT := fun _ _ => 0
theorem isIdemAt_G_pl (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (ha : a.Is) (n : Fin a.n) :
    Formalism.L2.NTheta.IsIdemAt (a.G n).q.e (a.pl n).1 :=
  ((ha.tie (fun t => _root_.GlobalTheory.Fam.TopLoc.LocalIdempotentDensity.levelZeroCharacter W.Q.stdChar a.g t) (fun t => _root_.GlobalTheory.Fam.trivialColumnChoice t)).2.idem n).1
end GlobalTheory.Fam.TopLoc.LocalIdempotentDensity
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenMovedOfReadsStdAtLast
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.Rebase
open ValuativeRel
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
open _root_.Formalism.L2.Col GlobalTheory.StepData GlobalTheory.SymBridge
def QuadraticExtensionCarry (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (i : Fin J.r) (β : J.Ch₀ ((J.G i).s + 1))
    (r : Sp B.fields.E (B.R.N ((J.G i).s + 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N ((J.G i).s + 1))) : Prop :=
  ∀ e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1)), IsOrd xPos e →
    ∃ g ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J,
      g.val.toBlocks₁₁ = toLoc ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e e r.toLinearMap ∧
      ∀ y : Sp B.fields.E (B.R.N ((J.G i).s + 1)),
        ((qOf (J.P i).1 : B.fields.E) ^ (J.E i).M)⁻¹ • (r.symm y - repY (J.A.p0 ((J.G i).s + 1) β).1.2) ∈
          stdAt B.fields.E (B.R.N ((J.G i).s + 1)) (J.P i).1 →
        (J.E i).cos (J.π i ((J.G i).s + 1) β) = Submodule.Quotient.mk fun x => (ofSplit (J.G i).q).pr (y (e x))
set_option maxHeartbeats 1000000 in
theorem exists_GLint_carry {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (i : Fin J.r) (β : J.Ch₀ ((J.G i).s + 1)) :
    ∃ r ∈ GLint B.fields.E (B.R.N ((J.G i).s + 1)) (J.P i).1, _root_.GlobalTheory.Fam.Rebase.QuadraticExtensionCarry J i β r := by
  obtain ⟨e, he⟩ := GlobalTheory.QTw.exists_xOrd B.R ((J.G i).s + 1)
  obtain ⟨r, hr, g, hg, h1, h2⟩ := GlobalTheory.QPl.RatOrb.exists_rat_of_sameOrb (E := B.fields.E) (J.P i).1
    ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).ϖ (hJ.tw i).compl e _ ((J.E i).reg.2.2 ((J.G i).s + 1) 0 rfl).1
    ((J.E i).le ((J.G i).s + 1) 0 rfl) (J.E i).M _ (repY (J.A.p0 ((J.G i).s + 1) β).1.2) (hJ.orb i β e he)
  refine ⟨r, hr, fun e' he' => ?_⟩
  obtain rfl : e = e' := Equiv.ext fun y => Fin.ext ((he y).trans (he' y).symm)
  exact ⟨g, hg, h1, h2⟩
theorem exists_index_place_eq_of_readsStd_of_mem (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) {P : HeightOneSpectrum (𝓞 B.fields.E)}
    (hP : P ∈ I.Q (W.P.I.tup t)) : ∃ i, (J.P i).1 = P := by
  obtain ⟨i, hi⟩ := hJ.surj P ((hW.tq.Q t P).2 hP)
  exact ⟨i, (hJ.eq i).trans hi⟩
theorem P_mem_Q_of_readsStd {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (i : Fin J.r) : (J.P i).1 ∈ I.Q (W.P.I.tup t) :=
  (Finset.mem_union.1 (J.P i).2).resolve_left (hJ.tw i).nmem
set_option maxHeartbeats 1000000 in
theorem exists_chPt_moves_of_readsStd (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (j : ℕ) (β : J.Ch₀ j) :
    ∃ (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup (W.P.I.tup t)) u j) (κ : TC.GA B (B.R.N j)), j + 1 = B.R.m →
      q.deco = (J.A.p0 j β).1.1.deco ∧ (∀ v, ¬ I.UnderQ (W.P.I.tup t) v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) κ = 1) ∧
      TC.PtOf (J.A.kb j β * κ) (extTo I.SQ q) ∧
      ∀ i β' r', HEq β' β → HEq r' (q.fr ⟨(J.P i).1, _root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i⟩) → _root_.GlobalTheory.Fam.Rebase.QuadraticExtensionCarry J i β' r' := by
  by_cases hm : j + 1 = B.R.m
  swap
  · exact ⟨(J.A.p0 j β).1.1, 1, fun h => absurd h hm⟩
  have H : ∀ P : I.Q (W.P.I.tup t), ∃ r ∈ GLint B.fields.E (B.R.N j) P.1,
      ∀ i, (J.P i).1 = P.1 → ∀ β' r', HEq β' β → HEq r' r → _root_.GlobalTheory.Fam.Rebase.QuadraticExtensionCarry J i β' r' := by
    rintro ⟨P, hP⟩
    obtain ⟨i, rfl⟩ := _root_.GlobalTheory.Fam.Rebase.exists_index_place_eq_of_readsStd_of_mem hW hJ hP
    have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
    obtain rfl : j = (J.G i).s + 1 := by omega
    obtain ⟨r, hr, hc⟩ := _root_.GlobalTheory.Fam.Rebase.exists_GLint_carry hJ i β
    refine ⟨r, hr, fun i' hi' β' r' h1 h2 => ?_⟩
    obtain rfl : i' = i := hJ.inj ((hJ.eq i').symm.trans (hi'.trans (hJ.eq i)))
    rw [eq_of_heq h1, eq_of_heq h2]
    exact hc
  choose r hr hc using H
  obtain ⟨hb1, hb2⟩ := hJ.is.base j (by omega) β
  obtain ⟨q, κ, h1, h2, h3, h4⟩ := GlobalTheory.AdForm.Rebase.exists_frames hW.tr.ok (J.A.p0 j β).1.1 (J.A.kb j β) hb1 hb2 r hr
  refine ⟨q, κ, fun _ => ⟨h1, h3, h4, fun i β' r' e1 e2 => hc ⟨(J.P i).1, _root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i⟩ i rfl β' r' e1 ?_⟩⟩
  rw [← h2]
  exact e2
set_option maxHeartbeats 1000000 in
theorem frsF_p0_eq_one_of_readsStd (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (i : Fin J.r) (j : ℕ) (hj : j < B.R.m) (β : J.Ch₀ j) :
    frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 (J.P i) = 1 := by
  have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
  have key : ∀ r' b' : Fin (B.R.N j), frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 (J.P i) (Pi.single b' 1) r' =
      if r' = b' then (1 : B.host.E) else 0 := by
    intro r' b'
    apply (algebraMap B.host.E ((J.P i).1.adicCompletion B.host.E)).injective
    rw [← GlobalTheory.Fam.MovedJoin.adAt_kb_eq_frsF J.A hJ.is (J.P i) hPn j hj.le β r' b', hJ.std j hj β,
      GlobalTheory.Fam.MovedJoin.adAt_kStd_of_twist hW.tr.ok _ (J.P i) hPn u _ r' b']
  refine LinearEquiv.toLinearMap_injective ((Pi.basisFun B.fields.E (Fin (B.R.N j))).ext fun b => funext fun r => ?_)
  rw [Pi.basisFun_apply]
  exact (key r b).trans (Pi.single_apply b (1 : B.fields.E) r).symm
set_option maxHeartbeats 1000000 in
theorem cos_pi_eq_mk_pr_repY (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (i : Fin J.r) (β : J.Ch₀ ((J.G i).s + 1))
    (p' : PtAt B.R I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) u ((J.G i).s + 1))
    (hc : cosetIn p' = cosetIn (J.A.p0 ((J.G i).s + 1) β)) (hr : _root_.GlobalTheory.Fam.Rebase.QuadraticExtensionCarry J i β (p'.1.1.fr ⟨(J.P i).1, _root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i⟩))
    (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))) (he : IsOrd xPos e) :
    (J.E i).cos (J.π i ((J.G i).s + 1) β) = Submodule.Quotient.mk fun x => (ofSplit (J.G i).q).pr (repY p'.1.2 (e x)) := by
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
  obtain ⟨g, -, -, h⟩ := hr e he
  refine h _ ?_
  have h1 := GlobalTheory.AdForm.Rebase.repY_cong hs (J.A.p0 ((J.G i).s + 1) β) p' hc (J.P i)
  have h2 : frsF I.sel (I.tup (W.P.I.tup t)) p'.1.1 (J.P i) = p'.1.1.fr ⟨(J.P i).1, _root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i⟩ := by
    unfold frsF
    exact dif_neg hPn
  rw [_root_.GlobalTheory.Fam.Rebase.frsF_p0_eq_one_of_readsStd hW hJ i _ (by omega) β, h2, if_neg hPn] at h1
  rw [hJ.M i]
  exact h1
set_option maxHeartbeats 1000000 in
theorem pr_repY_sub_mem_integers (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (n : Fin a.n) {b : I.ι}
    (p p' : PtAt B.R I.sel (I.tup b) (I.cst b) u ((a.G n).s + 1)) (hc : cosetIn p' = cosetIn p) (hd : p'.1.1.deco = p.1.1.deco)
    (hN : p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N ((a.G n).s + 1))) (x : Fin (B.R.N ((a.G n).s + 1))) :
    (ofSplit (a.G n).q).pr (repY p'.1.2 x) - (ofSplit (a.G n).q).pr (repY p.1.2 x) ∈ 𝒪[(a.G n).k] := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hP : (a.pl n).1 ∈ (B.primes X).vGs := (hW.lev.2.1 _).1 (a.pl n).2
  let P : rowSG (B.primes X) I.sel (I.tup b) := ⟨(a.pl n).1, Finset.mem_union_left _ hP⟩
  have hP' : P.1 ∈ (B.primes X).vGs := hP
  have h1 := GlobalTheory.AdForm.Rebase.repY_cong hs p p' hc P
  have h2 : frsF I.sel (I.tup b) p'.1.1 P = frsF I.sel (I.tup b) p.1.1 P := by
    unfold frsF
    rw [dite_eq_left hP', dite_eq_left hP', hd]
  rw [h2, if_pos hP', pow_zero, inv_one, one_smul, ← map_sub] at h1
  have h3 := (isFr_ptFr p.1.1 P.1 _).2 h1
  rw [← frsF_eq_ptFr, LinearEquiv.apply_symm_apply, hN] at h3
  have h4 := (mem_localization_standardLattice P.1 _).1 h3 x
  have h5 := pr_mem_of_intAt (D := I.rec7 l Z) (a.G n).q (_root_.GlobalTheory.Fam.TopLoc.LocalIdempotentDensity.isIdemAt_G_pl hW a ha n) h4
  have h6 := map_sub ((a.G n).q.pr.comp (incA (I.rec7 l Z))) (repY p'.1.2 x) (repY p.1.2 x)
  exact h6 ▸ h5
set_option maxHeartbeats 2000000 in
theorem pen_moved_of_readsStd_at_last (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (j : ℕ) (hj : j + 1 = B.R.m) (β : J.Ch₀ j)
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup (W.P.I.tup t)) u j) (κ : TC.GA B (B.R.N j))
    (hoff : ∀ v, ¬ I.UnderQ (W.P.I.tup t) v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) κ = 1)
    (hpt : TC.PtOf (J.A.kb j β * κ) (extTo I.SQ q))
    (hc : ∀ i β' r', HEq β' β → HEq r' (q.fr ⟨(J.P i).1, _root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i⟩) → _root_.GlobalTheory.Fam.Rebase.QuadraticExtensionCarry J i β' r')
    (kA : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (h1 : kA ∈ GfC _)
    (h2 : finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) kA = (J.A.kb j β * κ).1) :
    ∃ k₀ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j),
      k₀ ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) k₀ = (TC.kStd X u (B.R.N j)).1 ∧ kA = k₀ * h ∧
      h ∈ GlobalTheory.FinPl.grpAt _ (fun p => ∃ i, (J.G i).q.v = p) ∧
      ∀ i (e : (J.G i).s + 1 = j), ∃ g ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J,
        (mt _ (e ▸ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1)))).map (J.G i).q.pr =
          ((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁ * ((J.G i).FX ((J.G i).s + 1) le_rfl).γ := by
  have hI := hW.tr.ok
  have hle : j ≤ B.R.m := by omega
  obtain ⟨k1, k2, -⟩ := hJ.is.kA j hle β
  have hstd := hJ.std j (by omega) β
  have hidem : ∀ i, Formalism.L2.NTheta.IsIdemAt (J.G i).q.e (J.P i).1 := fun i => by rw [hJ.eq i]; exact (J.G i).idem
  have hfin : finM _ (rankN (I.rec7 l Z) j hle) ((J.A.kA j β)⁻¹ * kA) = κ.1 := by
    have e1 := GlobalTheory.AdForm.StabMove.finM_mul _ (rankN (I.rec7 l Z) j hle) (J.A.kA j β) ((J.A.kA j β)⁻¹ * kA)
    rw [mul_inv_cancel_left, h2, k2] at e1
    exact ((Units.mul_right_inj (J.A.kb j β)).1 e1).symm
  refine ⟨J.A.kA j β, (J.A.kA j β)⁻¹ * kA, k1, by rw [← hstd]; exact k2, (mul_inv_cancel_left _ _).symm,
    mem_grpAt_of_bc _ (rankN (I.rec7 l Z) j hle) _ _ (mul_mem (inv_mem k1) h1) κ hfin fun v hv => hoff v ?_, fun i e => ?_⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨i, rfl⟩ := _root_.GlobalTheory.Fam.Rebase.exists_index_place_eq_of_readsStd_of_mem hW hJ hP
    exact hv ⟨i, GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under _ (hidem i)⟩
  · subst e
    obtain ⟨e, he⟩ := GlobalTheory.QTw.exists_xOrd B.R ((J.G i).s + 1)
    obtain ⟨g, hg, hgm, -⟩ := hc i β _ HEq.rfl HEq.rfl e he
    refine ⟨g, hg, ?_⟩
    rw [hgm]
    refine map_pr_eq (J.G i).q (hidem i) _ (rankN (I.rec7 l Z) _ hle) _ _ (fun r s => ?_) xPos _
      ((ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 _ le_rfl) e he
    have hSQ : (J.P i).1 ∈ I.SQ := I.Q_subset_SQ _ (_root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i)
    have hTn := GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u (J.P i).1 (Finset.mem_union_right _ hSQ)
    have hb := (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) l.pr u (B.R.N ((J.G i).s + 1))).2.1 _ hTn
    have e1 : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) ((J.P i).1.under (𝓞 B.host.F))) κ =
        Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) ((J.P i).1.under (𝓞 B.host.F))) (J.A.kb _ β * κ) := by
      rw [map_mul, hstd, hb, one_mul]
    have e2 := GlobalTheory.Mem.Col2.ZeroMove.adAt_entry_of_bc (F := B.host.F) (E := B.host.E) (J.P i).1 e1 r s
    have e3 := hpt.fr ⟨(J.P i).1, hSQ⟩ r s
    rw [extTo_fr, ptFr_of_mem q (hJ.tw i).nmem (_root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i)] at e3
    rw [hfin]
    exact e2.trans e3
end GlobalTheory.Fam.Rebase
namespace GlobalTheory.Fam
open GlobalTheory.Fam.Rebase
set_option maxHeartbeats 2000000 in
theorem readsOfStd_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.ReadsStd → ∃ J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J'.Reads := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ _ t J hJ
  choose q κ hq using fun j β => _root_.GlobalTheory.Fam.Rebase.exists_chPt_moves_of_readsStd hW hJ j β
  obtain ⟨A', hA', hchr, hb0, hne, heq⟩ := GlobalTheory.AdForm.Rebase.exists_moved hW.tr.ok hW.tr.pins.some J.A hJ.is q κ
    (fun j hj β => (hq j β hj).2.1) (fun j hj β => (hq j β hj).2.2.1)
    (fun j hj β => by rw [(hq j β hj).1]; exact (hJ.is.base j (by omega) β).2)
  have hdeco : ∀ j, j + 1 = B.R.m → ∀ β, (A'.p0 j β).1.1.deco = (J.A.p0 j β).1.1.deco := fun j hj β => by
    rw [(heq j hj β).2.1]
    exact (hq j β hj).1
  refine ⟨{ J with A := A' }, hA', hJ.inj, hJ.surj, fun j hj => ?_, hJ.res, hJ.eq, hJ.sg, hJ.tw, hJ.M, fun i j d h hj β => ?_,
    fun i β e he => ?_, fun j hj β => ?_, fun j hj β => ?_, hJ.last, hJ.sec, fun n y e he r => ?_, ?_⟩
  · show A'.chr (j + 1) = _
    rw [hchr]
    exact hJ.chr j hj
  · have h' := hJ.rep i j d h hj β
    rw [← hb0] at h'
    exact h'
  · have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
    refine _root_.GlobalTheory.Fam.Rebase.cos_pi_eq_mk_pr_repY hW hJ i β (A'.p0 _ β) (heq _ hs β).2.2 ?_ e he
    rw [(heq _ hs β).2.1]
    exact (hq _ β hs).2.2.2 i β _ HEq.rfl HEq.rfl
  · show A'.kb j β = _
    rw [(hne j (by omega)).1]
    exact hJ.std j (by omega) β
  · obtain ⟨k1, k2, -⟩ := hA'.kA j (by omega) β
    rw [(heq j hj β).1] at k2
    exact _root_.GlobalTheory.Fam.Rebase.pen_moved_of_readsStd_at_last hW ha hJ j hj β (q j β) (κ j β) (hq j β hj).2.1 (hq j β hj).2.2.1 (hq j β hj).2.2.2 (A'.kA j β) k1 k2
  · have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
    have h1 := _root_.GlobalTheory.Fam.Rebase.pr_repY_sub_mem_integers hW ha n (J.A.p0 _ (J.ι _ y)) (A'.p0 _ (J.ι _ y)) (heq _ hs _).2.2 (hdeco _ hs _)
      (hJ.is.base _ (by omega) _).2 (e r)
    have h2 := add_mem h1 (hJ.cosG n y e he r)
    rw [sub_add_sub_cancel] at h2
    exact h2
  · exact dead_moved hW.tr.ok hJ.live hb0 (fun j hj => (hne j hj).2) fun j hj β => ⟨hdeco j hj β, (heq j hj β).2.2⟩
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenMovedOfReadsStdAtLastStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_commutation_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.ReadsStd → ∃ J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J'.Reads := by
  first | exact @_root_.GlobalTheory.Fam.readsOfStd_alt | exact _root_.GlobalTheory.Fam.readsOfStd_alt | (intros; apply _root_.GlobalTheory.Fam.readsOfStd_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReadsStd
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReadsStd
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PenChart
section Orbits
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
end Orbits
section Restr
variable {D : D7} {c : Comm D} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl D.host.E} {G : QGeo v Bs PP} {χ : ℕ → (AE D)ˣ →* Circle}
end Restr
section Place
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀)
  {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E} {G : QGeo v Bs PP}
  {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle} (E : QExt G χ)
variable {A E} {P : BadPr I a} {hψ : Continuous G.ψk} {sg : ℂ}
end Place
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Level
set_option maxHeartbeats 4000000 in
theorem exists_readsStd_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.ReadsLow → ∃ J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J'.ReadsStd := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ha' hc t J h
  have hI := hW.tr.ok
  have ht := hW.tr.tw
  have h2 := B.R.two_le_m
  have hs : ∀ i, (J.G i).s + 1 + 1 = B.R.m := fun i => (J.G i).hs
  have hPi : Function.Injective J.P := fun i i' e => h.inj ((h.eq i).symm.trans ((congrArg Subtype.val e).trans (h.eq i')))
  have hPs : ∀ P : BadPr I (W.P.I.tup t), P.1 ∈ I.Q (W.P.I.tup t) → ∃ i, J.P i = P := fun P hP => by
    obtain ⟨i, e⟩ := h.surj P.1 ((hW.tq.Q t P.1).2 hP)
    exact ⟨i, Subtype.ext ((h.eq i).trans e)⟩
  have hQ : ∀ i, (J.P i).1 ∈ I.Q (W.P.I.tup t) := fun i => (Finset.mem_union.1 (J.P i).2).resolve_left (h.tw i).nmem
  have hbox : ∀ i j, j + 1 ≠ B.R.m → ∀ y, InBox (J.E i) j y := fun i j hj y e => hj ((congrArg (· + 1) e).trans (hs i)) |>.elim
  have kπ : ∀ i j (β : J.Ch₀ j), ∃ y : {y : (J.E i).Ch j // InBox (J.E i) j y},
      (j + 1 ≠ B.R.m → y.1 = J.π i j β) ∧ OrbAt J.A (J.E i) j y.1 β := fun i j β => by
    by_cases hj : j + 1 = B.R.m
    · obtain ⟨y, h1, h3⟩ := exists_orbAt hI h.is (h.tw i) (h.M i) hj β (h.std j (by omega) β)
      exact ⟨⟨y, h1⟩, fun e => absurd hj e, h3⟩
    · exact ⟨⟨J.π i j β, hbox i j hj _⟩, fun _ => rfl, fun e => (hj ((congrArg (· + 1) e).trans (hs i))).elim⟩
  choose π hπ hπ' using kπ
  have kι : ∀ j (y : ∀ i, {y : (J.E i).Ch j // InBox (J.E i) j y}), ∃ β : J.Ch₀ j,
      (j + 1 ≠ B.R.m → β = J.ι j fun i => (y i).1) ∧
      (j + 1 = B.R.m → Good (J.A.p0 j β) ∧ ∀ i, OrbAt J.A (J.E i) j (y i).1 β) := fun j y => by
    by_cases hj : j + 1 = B.R.m
    · let b := J.A.b0 j (J.ι j fun i => (y i).1)
      choose z hz hz' using fun i => exists_vec hI h.is (h.tw i) (h.M i) hj b (y i).2
      obtain ⟨β, hβ, hβ'⟩ := exists_chart hI ht h.is hj b (Function.extend J.P z 0) fun P hP => by
        obtain ⟨i, rfl⟩ := hPs P ((Finset.mem_union.1 P.2).resolve_left hP)
        rw [hPi.extend_apply]
        exact hz i
      refine ⟨β, fun e => absurd hj e, fun _ => ⟨hβ, fun i => hz' i (hQ i) β (h.std j (by omega) β) ?_⟩⟩
      have := hβ' (J.P i) (hQ i)
      rwa [hPi.extend_apply] at this
    · exact ⟨_, fun _ => rfl, fun e => absurd e hj⟩
  choose ι hι hι' using kι
  have hsec : ∀ j, j ≤ B.R.m → ∀ y i, π i j (ι j y) = y i := fun j hj y i => by
    refine Subtype.ext ?_
    by_cases e : j + 1 = B.R.m
    · exact orbAt_unique e (hπ' i j _) ((hι' j y e).2 i)
    · rw [hπ i j _ e, hι j y e]
      exact h.sec j hj e _ i
  have hlift : ∀ j, j + 1 ≠ B.R.m → ∀ y, J.ι j y ∈ Set.range (ι j) := fun j hj y =>
    ⟨fun i => ⟨y i, hbox i j hj _⟩, hι j _ hj⟩
  let J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t := ⟨J.Ch₀, J.A, J.r, J.pl, J.mem, fun i => restr (J.E i), J.P, J.hψ, J.sg, π, ι⟩
  refine ⟨J', h.is, h.inj, h.surj, h.chr, h.res, h.eq, h.sg, h.tw, h.M, fun i j d e hj β => ?_, fun i β => hπ' i _ β rfl, h.std, h.last,
    hsec, fun n y e he r => ?_, fun j => ?_, fun β => ?_, fun β => ?_, fun j hj γ hγ α z => ?_⟩
  · have e' : j + d = (J.G i).s := e
    have := h.rep i j d e hj β
    rw [← hπ i j β (by have := hs i; omega)] at this
    exact this
  · have hn : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
    have hP : (a.pl n).1 ∈ (B.primes X).vGs := (hW.lev.2.1 _).1 (a.pl n).2
    obtain ⟨h3, h4⟩ := _root_.GlobalTheory.T.true_geometry_commutation_twist_alt W hW u a ha ha' hc n
    exact couplingCoset_sub_basePoint_integral_typePrime hI h.is hn (a.G n).S ((a.G n).q.pr.comp (incA (I.rec7 l Z))) ⟨(a.pl n).1, Finset.mem_union_left _ hP⟩ hP h3 h4 _
      (h.std _ (by omega) _) (hι' _ y hn).1 e he r
  · by_cases e : j + 1 = B.R.m
    · exact fun y y' hy => funext fun i => (hsec j (by omega) y i).symm.trans
        ((congrArg (π i j) hy).trans (hsec j (by omega) y' i))
    · intro y y' hy
      have h3 := h.injCh j e ((hι j y e).symm.trans (hy.trans (hι j y' e)))
      exact funext fun i => Subtype.ext (congrFun h3 i)
  · obtain ⟨y, rfl⟩ := h.first β
    exact hlift 0 (by omega) y
  · obtain ⟨y, rfl⟩ := h.onto β
    exact hlift _ (by omega) y
  · by_cases e : j + 1 + 1 = B.R.m
    · by_contra hz
      refine hγ ⟨fun i => π i (j + 1) γ, ?_⟩
      refine chart_ext hI ht h.is e (J.A.b0 _ γ) _ _ (hι' _ _ e).1 (good_of_xi hI ht e hj α γ z hz) fun P hP => ?_
      obtain ⟨i, rfl⟩ := hPs P hP
      exact lev_of_orbAt hI h.is (h.tw i) (h.M i) e _ hP (h.std _ (by omega) _) (h.std _ (by omega) _) ((hι' _ _ e).2 i) (hπ' i _ γ)
    · refine h.dead j hj e γ ?_ α z
      rintro ⟨y, rfl⟩
      exact hγ (hlift _ e y)
end GlobalTheory.PenChart
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReadsStdStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_commutation_identity_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.ReadsLow → ∃ J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J'.ReadsStd := by
  first | exact @_root_.GlobalTheory.PenChart.exists_readsStd_alt | exact _root_.GlobalTheory.PenChart.exists_readsStd_alt | (intros; apply _root_.GlobalTheory.PenChart.exists_readsStd_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReadsLow
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReadsLow
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LowJoin
open GlobalTheory.TwBridge GlobalTheory.StepData GlobalTheory.SplitWeil
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
section Place
variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E}
end Place
set_option maxHeartbeats 2000000 in
theorem exists_quadratic_extension_readsLow : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.ReadsLow := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ ha hc t
  have hI := hW.tr.ok
  have hm := B.R.two_le_m
  obtain ⟨Ch₀, -, A, hA, hlast, hne, -, hstd, -⟩ := GlobalTheory.T.exists_tupleAdelicData_standardBasePoints I hI hW.tr.pins.some l Z u (W.P.I.tup t)
  have hχ : ∀ j (hj : j < B.R.m), ChrEq (D := I.rec7 l Z) (_root_.GlobalTheory.Fam.chrK_alt W t j) (I.C.mu0 ⟨j, hj⟩ * I.xi (W.P.I.tup t)) := fun j hj =>
    GlobalTheory.Mem.TupChar.chrEq_mul (hW.tr.chr ⟨j, hj⟩) (hW.tq.xi t)
  let e := ((_root_.GlobalTheory.Fam.pk_z W).Q t).equivFin
  let pl : Fin ((_root_.GlobalTheory.Fam.pk_z W).Q t).card → Pl (I.rec7 l Z).host.E := fun i => (e.symm i).1
  have mem : ∀ i, pl i ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t := fun i => (e.symm i).2
  have plinj : Function.Injective pl := Subtype.val_injective.comp e.symm.injective
  have plsurj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, pl i = PP := fun PP h => ⟨e ⟨PP, h⟩, by simp [pl]⟩
  let P : Fin ((_root_.GlobalTheory.Fam.pk_z W).Q t).card → BadPr I (W.P.I.tup t) := fun i => ⟨pl i, Finset.mem_union_right _ ((hW.tq.Q t _).1 (mem i))⟩
  have hoff : ∀ i, (P i).1 ∉ (B.primes X).vGs := fun i => TC.Q_notMem_of_ok hI _ _ ((hW.tq.Q t _).1 (mem i))
  let G := fun i => a.Q (pl i) ⟨t, mem i⟩
  have hs : ∀ i, (G i).s + 1 + 1 = B.R.m := fun i => (G i).hs
  choose E hψ sg hE using fun i => exists_good hI hW.tr.tw (P i) (hoff i) (G i) rfl hc ha.pinX.std (_root_.GlobalTheory.Fam.chrK_alt W t) hχ
  let Rel : ∀ i j, Formalism.L2.Col.AutY B.fields B.R j → (E i).Ch j → Prop := fun i j γ y => ∀ d (h : j + d = (G i).s),
    IsGL (X := B.fields) (R := B.R) (k := (G i).k) ((G i).q.pr.comp (incA (I.rec7 l Z))) γ ((E i).rep j d h y)
  have hrel : ∀ i j d (h : j + d = (G i).s) γ y, IsGL (X := B.fields) (R := B.R) (k := (G i).k)
      ((G i).q.pr.comp (incA (I.rec7 l Z))) γ ((E i).rep j d h y) → Rel i j γ y := fun i j d h γ y h1 d' h' => by
    obtain rfl : d' = d := by omega
    exact h1
  have hd : ∀ i j, j ≤ B.R.m - 2 → ∃ d, j + d = (G i).s := fun i j hj => ⟨(G i).s - j, by have := hs i; omega⟩
  have hbij := exists_bij (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr hI.ch_ok hI.sel_ok (hI.sharp _) (hI.idx_ok (W.P.I.tup t))
    (GlobalTheory.T.twistIndexSet_eq_prod_localRepresentatives _ _ _ _ _ _ _ _ _ _ _ (hI.idx_ok _) (idxProd hI hW.tr.tw _)) (h_one hW.tr.tw _) P
    (fun i i' h => plinj (congrArg (fun Q : BadPr I (W.P.I.tup t) => Q.1) h)) hoff
    (fun Q hQ => (plsurj Q.1 ((hW.tq.Q t _).2 ((Finset.mem_union.1 Q.2).resolve_left hQ))).imp fun i h => Subtype.ext h)
    (fun i => (E i).Ch) Rel
    (fun i j hj b => by
      obtain ⟨d, h⟩ := hd i j hj
      obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_completionMatrix_of_rationalTwistAut B.fields B.R (G i).k ((G i).q.pr.comp (incA (I.rec7 l Z))) j (d + 1)
        (by have := hs i; simp only [Formalism.L2.Col.cOf]; omega) ((I.idx _).h j b (P i))
      obtain ⟨y, -, rfl⟩ := ((E i).rep_bij j d h).surjOn (((hE i).rat j d h ⟨b⟩).ge ⟨b, hg⟩)
      exact ⟨y, hrel i j d h _ _ hg⟩)
    (fun i j hj h0 y => by
      obtain ⟨d, h⟩ := hd i j hj
      obtain ⟨b, hb⟩ := ((hE i).rat j d h h0).le (((E i).rep_bij j d h).mapsTo (Set.mem_univ y))
      exact ⟨b, hrel i j d h _ _ hb⟩)
    (fun i j hj γ γ' y y' h1 h2 => by
      obtain ⟨d, h⟩ := hd i j hj
      exact (isGL_unique (h1 d h) (h2 d h)).trans
        ⟨fun e => ((E i).rep_bij j d h).injOn (Set.mem_univ _) (Set.mem_univ _) e, fun e => e ▸ rfl⟩)
    (fun i j hj h0 ⟨y⟩ => by
      obtain ⟨d, h⟩ := hd i (j + 1) hj
      exact (hE i).next j d h h0 ⟨_, ((E i).rep_bij (j + 1) d h).mapsTo (Set.mem_univ y)⟩)
    (fun i j hj ⟨y⟩ => by
      obtain ⟨d, h⟩ := hd i (j + 1) hj
      obtain ⟨g, hg, -⟩ := Set.mem_iUnion₂.1
        (((E i).reps.bij j d h).mapsTo (((E i).rep_bij (j + 1) d h).mapsTo (Set.mem_univ y)))
      obtain ⟨y', -, -⟩ := ((E i).rep_bij j _ _).surjOn hg
      exact ⟨y'⟩)
  have hup : ∀ j, B.R.m ≤ j → ∀ i, Nonempty (Unique ((E i).Ch j)) := fun j hj i => by
    rcases hj.eq_or_lt with h | h
    · rw [← h, ← hs i]
      exact Fintype.card_eq_one_iff_nonempty_unique.1 (E i).one
    · exact (hE i).up j (by rw [hs i]; exact h)
  have key : ∀ j, ∃ (π : ∀ i, Ch₀ j → (E i).Ch j) (ι : (∀ i, (E i).Ch j) → Ch₀ j),
      (∀ i d (h : j + d = (G i).s) (hj : j < B.R.m) β, IsGL (X := B.fields) (R := B.R) (k := (G i).k)
        ((G i).q.pr.comp (incA (I.rec7 l Z))) ((I.idx (W.P.I.tup t)).h j ((A.b0 j β).get hj) (P i)) ((E i).rep j d h (π i β))) ∧
      (j + 1 ≠ B.R.m → (∀ y i, π i (ι y) = y i) ∧ (j ≤ B.R.m → Function.Surjective ι)) := by
    intro j
    rcases lt_trichotomy (j + 1) B.R.m with hj | hj | hj
    · obtain ⟨φ, h1, h2⟩ := hbij j (by omega)
      let f := Equiv.ofBijective _ (h1.comp (get_bij hA j hj))
      exact ⟨fun i β => f β i, f.symm, fun i d h _ β => h2 _ i d h, fun _ =>
        ⟨fun y i => congrFun (f.apply_symm_apply y) i, fun _ => f.symm.surjective⟩⟩
    · have h1 : ∀ i, Nonempty ((E i).Ch j) := fun i => by
        rw [show j = (G i).s + 1 by have := hs i; omega]
        exact ⟨((E i).cos_all 0 (zero_mem _)).choose⟩
      have h2 : Nonempty ((I.idx (W.P.I.tup t)).β j) := by
        rw [show j = B.R.m - 2 + 1 by omega]
        exact ⟨(hI.idx_ok _).last_uniq.choose⟩
      exact ⟨fun i _ => (h1 i).some, fun _ => (hne j ⟨Idx.of h2.some (by omega)⟩).some,
        fun i d h => by have := hs i; omega, fun h => absurd hj h⟩
    · have h1 := fun i => (hup j (by omega) i).some
      refine ⟨fun i _ => default, fun _ => (hne j ⟨Idx.top _ _ _ (by omega)⟩).some, fun i d h hj' => by omega,
        fun _ => ⟨fun y i => Subsingleton.elim _ _, fun hj' β => ⟨default, ?_⟩⟩⟩
      obtain rfl : j = B.R.m := by omega
      exact hlast.some.instSubsingleton.elim _ _
  choose π ι k1 k2 using key
  refine ⟨⟨Ch₀, A, _, pl, mem, E, P, hψ, sg, fun i j => π j i, ι⟩, hA, plinj, plsurj,
    fun j hj => (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ (hA.chr ⟨j, hj⟩) (hχ j hj), fun i => ?_, fun _ => rfl,
    fun i => (hE i).sign, fun i => (hE i).tw, fun i => (hE i).M, fun i j => k1 j i, hstd, hlast, fun j _ hj => (k2 j hj).1,
    fun j hj y y' h => funext fun i => ?_, (k2 0 (by omega)).2 (by omega), (k2 _ (by omega)).2 le_rfl,
    fun j hj hj' γ hγ => absurd ((k2 _ hj').2 hj γ) hγ⟩
  · exact res_of_tw hI (hE i).tw (hW.lev.2.2 t ▸ hW.pk.bot.hyp.2.2.2.1.lev.xiR t _ (mem i))
  · exact ((k2 j hj).1 y i).symm.trans ((congrArg (π j i) h).trans ((k2 j hj).1 y' i))
end GlobalTheory.LowJoin
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReadsLowStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quadratic_extension_reads_low_of_true : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.ReadsLow := by
  first | exact @_root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow | exact _root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow | (intros; apply _root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsExists
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem readsExists_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT hc t
  obtain ⟨J, hJ⟩ := _root_.GlobalTheory.T.exists_quadratic_extension_reads_low_of_true W hW u a ha haT hc t
  obtain ⟨J', hJ'⟩ := _root_.GlobalTheory.T.true_geometry_commutation_identity_alt W hW u a ha haT hc t J hJ
  exact _root_.GlobalTheory.T.true_geometry_commutation_property_alt W hW u a ha haT hc t J' hJ'
end GlobalTheory.Fam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsExistsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quadratic_extension_reads_of_true : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads := by
  first | exact @_root_.GlobalTheory.Fam.readsExists_alt | exact _root_.GlobalTheory.Fam.readsExists_alt | (intros; apply _root_.GlobalTheory.Fam.readsExists_alt <;> assumption)
end
end
