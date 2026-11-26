module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainCommutationValid
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedAt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxLeSup
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutMemU
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CosetLevelEqOfReads
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CosetLevelEqOfReads
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLevTyp
section Main
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
set_option maxHeartbeats 2000000 in
theorem cosetIn_p0_eq_of_reads (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 1 = B.R.m) {t t' : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.Reads)
    (α : J.Ch j) {J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'} (hJ' : J'.Reads) (α' : J'.Ch j) (w : (B.primes X).vGs) :
    cosetIn (J.A.p0 j (J.ι j α)) ⟨w.1, Finset.mem_union_left _ w.2⟩ =
      cosetIn (J'.A.p0 j (J'.ι j α')) ⟨w.1, Finset.mem_union_left _ w.2⟩ := by
  obtain ⟨n, hn⟩ := a.pl.surjective ⟨w.1, (hW.lev.2.1 _).2 w.2⟩
  have hP : w.1 = (a.pl n).1 := by rw [hn]
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain rfl : j = (a.G n).s + 1 := by omega
  have hint : ∀ x : B.fields.E, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt w.1 x := by
    have hR := (ha.tie (fun t => (TopLocFac.nonempty_rowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g hTr.pinX.std t).some)
      fun t => (TopLocFac.nonempty_colCh _ _).some).2
    rw [hP]
    exact (GlobalTheory.LocMod.PinEx.place_facts _ (hR.idem n).1).2.1
  have hqv : HeightOneSpectrum.valuation B.fields.E w.1 (Formalism.L2.Col.qOf w.1 : B.fields.E) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨i, g1, -, -, g4, -⟩ := GlobalTheory.SeeSaw.LevelData.type_prime w.2
    exact GlobalTheory.AtTypeExists.valuation_norm w.1 (g1 ▸ g4)
  obtain ⟨e, he⟩ := exists_xOrd B.R ((a.G n).s + 1)
  have key : ∀ {t : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (_ : J.Reads) (α : J.Ch ((a.G n).s + 1)), ∃ z : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1)),
      cosetIn (J.A.p0 _ (J.ι _ α)) ⟨w.1, Finset.mem_union_left _ w.2⟩ =
        {z' | z' - z ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N ((a.G n).s + 1)) w.1} ∧
      ∀ r, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (z (e r)) - (a.G n).S.y0 (Fin B.R.t) r ∈ 𝒪[(a.G n).k] := by
    intro t J hJ α
    refine ⟨_, (coset_at (J.A.p0 _ (J.ι _ α)) hj ((J.A.p0 _ (J.ι _ α)).repY_mem hj) w).1, fun c => ?_⟩
    have hF := _root_.GlobalTheory.Fam.TopFrames.valuation_frs_sub_kronecker_lt_one hW hJ ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2 hj (J.ι _ α)
    have hq := TopFrames.intAt_q_mul (A := J.A) ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2 hj (J.ι _ α)
    have hco := hJ.cosG n α e he c
    have hfr : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ α)).1.1 ⟨w.1, Finset.mem_union_left _ w.2⟩ =
      (J.A.p0 _ (J.ι _ α)).1.1.deco.1.liftFr w := dif_pos w.2
    rw [hfr] at hF hq
    generalize (J.A.p0 _ (J.ι _ α)).1.1.deco.1.liftFr w = f at hF hq ⊢
    generalize Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2 = y at hq hco ⊢
    have h1 := (hint _).2 (TopFrames.intAt_sub_of_near hqv hF hq (e c))
    rw [LinearEquiv.apply_symm_apply, map_sub] at h1
    have h2 : _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y (e c)) - (a.G n).S.y0 (Fin B.R.t) c ∈ 𝒪[(a.G n).k] := hco
    have h3 := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at h3
  obtain ⟨z, hz, h1⟩ := key hJ α
  obtain ⟨z', hz', h1'⟩ := key hJ' α'
  have hd : z - z' ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N ((a.G n).s + 1)) w.1 := by
    refine GlobalTheory.TopStep.mem_stdAt.2 fun i => ?_
    obtain ⟨r, rfl⟩ := e.surjective i
    have h := sub_mem (h1 r) (h1' r)
    rw [sub_sub_sub_cancel_right, ← map_sub] at h
    exact (hint _).1 h
  rw [hz, hz']
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have := add_mem h hd
    rwa [sub_add_sub_cancel] at this
  · intro h
    have := sub_mem h hd
    rwa [sub_sub_sub_cancel_right] at this
set_option maxHeartbeats 2000000 in
theorem mem_UAd_iff_of_not_plF (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 1 = B.R.m) [NeZero (B.R.N j)] {t : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t}
    (hJ : J.Reads) (β : J.Ch₀ j) (v : HeightOneSpectrum (𝓞 B.host.F)) (hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal)
    (hv : ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J v) (x : TC.GA B (B.R.N j)) (hxU : x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j))
    (hx : ∀ w, w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) w) x = 1) :
    x ∈ (J.A.K j (show j ≤ B.R.m by omega) β).lev.U ↔
      x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
      (GlobalTheory.Mem.Col2.MemChart.chG (X := B.fields) (Formalism.L2.Col.colLevSym I.Ch j) (GlobalTheory.Mem.Col2.MemChart.bar (J.A.p0 j β))) := by
  have hm : j ≤ B.R.m := by omega
  obtain ⟨c, rfl⟩ := (hJ.is.reads j hm).onto β
  have h6 := (TrueColsTest.kStd_spec X u (B.R.N j)).2.1 v hT
  have hk : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (J.A.kb j (J.A.chOf j c)) = 1 := by
    obtain ⟨k₀, h, -, h1, h2, h3, -⟩ := hJ.pen j hj (J.A.chOf j c)
    have h5 := TopFrames.finM_map_prV _ (rankN (I.rec7 l Z) j hm) h3 hv
    refine Units.ext ?_
    have h7 := (hJ.is.kA j hm (J.A.chOf j c)).2.1
    rw [h2, GlobalTheory.AdForm.Model.finM_mul, h1] at h7
    have h8 : (J.A.kb j (J.A.chOf j c)).1.map (Formalism.UG.prV (E := B.host.E) v) = 1 := by
      rw [← h7]
      refine Matrix.map_mul.trans ?_
      have h6' : (TC.kStd X u (B.R.N j)).1.map (Formalism.UG.prV (E := B.host.E) v) = 1 := congrArg Units.val h6
      exact (congrArg₂ (fun x y : Matrix (Fin (B.R.N j)) (Fin (B.R.N j))
        (B.host.E ⊗[B.host.F] v.adicCompletion B.host.F) => x * y) h6' h5).trans (one_mul _)
    exact h8
  have h1 : ∀ P ∈ I.Q (W.P.I.tup t), x.1.map (GlobalTheory.Mem.Col2.adAt B.host.F P) = 1 := fun P hP => by
    refine GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV P (hx _ fun h => hv ?_)
    obtain ⟨i, hi⟩ := hJ.surj P ((hW.tq.Q t P).2 hP)
    exact ⟨i, (((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t J hJ).2 i).trans (congrArg _ hi)).trans h⟩
  refine (mem_lev_iff I hW.tr.ok hW.tr.tw l.pr u _ j hj (hJ.is.reads j hm) c x hxU (commute_of_off hx hk)
    (commute_of_off hx h6) h1).trans ?_
  have hb : GlobalTheory.Mem.Col2.MemChart.bar (show PtAt B.R I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) u j from
      (I.stp u (W.P.I.tup t) j).rep c) = GlobalTheory.Mem.Col2.MemChart.bar (J.A.p0 j (J.A.chOf j c)) := funext fun w =>
    (cos_iff_bar hj w (GlobalTheory.Mem.Col2.MemChart.hqG l.pr w.1 w.2) _ _).1 (congrFun (hJ.is.rep j hm c).2 _)
  exact Iff.of_eq (congrArg (fun C => x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
    (GlobalTheory.Mem.Col2.MemChart.chG (X := B.fields) (Formalism.L2.Col.colLevSym I.Ch j) C)) hb)
end Main
set_option maxHeartbeats 2000000 in
theorem uloc_le_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) → ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J v → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' v → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' v _ hTv hv hv'
  have hm : j ≤ B.R.m := by omega
  haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
  obtain ⟨hPins⟩ := hW.tr.pins
  have hg1 : gramN (I.rec7 l Z) j hm = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hW.tr.ok hPins l Z).2.2.2 j hm).1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hm) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := by rw [hg1]; rfl
  refine GlobalTheory.stepLevel_uloc_le_of_agree _ _ {w | w ≠ v} (fun x hx hxU => ?_) v (fun h => h rfl)
  have hxA : x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := eU ▸ (((J.A.K j hm (J.ι j α)).lev.U_eq x).1 hxU).1
  have hb : GlobalTheory.Mem.Col2.MemChart.bar (J.A.p0 j (J.ι j α)) = GlobalTheory.Mem.Col2.MemChart.bar (J'.A.p0 j (J'.ι j α')) := funext fun w =>
    (cos_iff_bar hj w (GlobalTheory.Mem.Col2.MemChart.hqG l.pr w.1 w.2) _ _).1 (_root_.GlobalTheory.PenLevTyp.cosetIn_p0_eq_of_reads hW ha hTr j hj hJ α hJ' α' w)
  have h1 := (_root_.GlobalTheory.PenLevTyp.mem_UAd_iff_of_not_plF hW ha hTr j hj hJ (J.ι j α) v hTv hv x hxA hx).1 hxU
  rw [hb] at h1
  exact (_root_.GlobalTheory.PenLevTyp.mem_UAd_iff_of_not_plF hW ha hTr j hj hJ' (J'.ι j α') v hTv hv' x hxA hx).2 h1
end GlobalTheory.PenLevTyp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CosetLevelEqOfReadsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_coset_relation_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) → ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J v → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' v → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  first | exact @_root_.GlobalTheory.PenLevTyp.uloc_le_alt | exact _root_.GlobalTheory.PenLevTyp.uloc_le_alt | (intros; apply _root_.GlobalTheory.PenLevTyp.uloc_le_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UlocLeLevelPrime
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UlocLeLevelPrime
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLevPrime
section Comp
set_option synthInstance.maxHeartbeats 200000
variable {D : D7}
end Comp
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word}
end Level
set_option maxHeartbeats 2000000 in
theorem uloc_le_levelPrime_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' v hv
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  exact uloc_le_of_std hW.tr.ok hW.tr.pins.some hJ.is hJ'.is hTr.std a.o.I ha.shape.pre.nodup ha.shape.pre.all j _ _ _ v
    (exists_splitPt hTr.std v hv)
end GlobalTheory.PenLevPrime
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UlocLeLevelPrimeStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_coset_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)), ((B.T u : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  exact @_root_.GlobalTheory.PenLevPrime.uloc_le_levelPrime_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutMemU
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLevOff
section Cut
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut
set_option synthInstance.maxHeartbeats 200000
variable {D : D7}
end Cut
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}
end Level
end GlobalTheory.PenLevOff
end
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.PenLevOff.uloc_le_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J v → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' v → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hv hv'
  have hjm : j ≤ B.R.m := by omega
  by_cases hTv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal
  · exact _root_.GlobalTheory.T.true_geometry_coset_value_alt W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hTv
  by_cases hb : v ∈ J'.A.bad j
  · rcases hJ'.is.bad_le j hjm v hb with hg | hq
    · exact _root_.GlobalTheory.T.true_geometry_coset_relation_alt W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hg hTv hv hv'
    · exfalso
      obtain ⟨P, hP, hPv⟩ := hq
      obtain ⟨i, hi⟩ := hJ'.surj P ((hW.tq.Q t' P).2 hP)
      exact hv' ⟨i, (((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha haT t' J' hJ').2 i).trans (congrArg _ hi)).trans hPv⟩
  · rw [(J'.A.K j hjm (J'.ι j α')).lev.Uloc_hyp v hb hTv]
    refine ((J.A.K j hjm (J.ι j α)).lev.Uloc_lev v).trans (le_of_eq ?_)
    congr 1
    ext z
    exact ((hJ.is.reads j hjm).lb _ z).trans ((hJ'.is.reads j hjm).lb _ z).symm
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.PenLevOff.cut_mem_U_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p → p ∈ Q) → (∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p → p ∈ Q) → ∀ x ∈ J.A.U j (J.ι j α), GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) x ∈ J'.A.U j (J'.ι j α') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj t J hJ α t' J' hJ' α' Q hQ hQ' x hx
  have hjm : j ≤ B.R.m := by omega
  have hxG : x ∈ GfC _ := ((hJ.is.U j hjm _ x).1 hx).1
  have h1 := GlobalTheory.FinPl.SetCut.cutG_mem_Q _ Q x
  have h2 := GlobalTheory.FinPl.SetCut.cutG_mem_Qc _ Q hxG
  have e := GlobalTheory.FinPl.SetCut.cutG_mul_cutG _ Q x
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.idemQ_mul_self Q) x = g₁ at h1 e
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) x = g₂ at h2 e ⊢
  refine (GlobalTheory.PenLevOff.mem_U_iff hJ'.is j hjm _ g₂).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h2, fun v => ?_⟩
  by_cases hv : v ∈ Q
  · rw [GlobalTheory.PenLevOff.cutAt_eq_one _ (P := (· ∉ Q)) (not_not.2 hv) h2]
    exact one_mem _
  · have h4 := ((GlobalTheory.PenLevOff.mem_U_iff hJ.is j hjm _ x).1 hx).2 v
    rw [← e, map_mul, GlobalTheory.PenLevOff.cutAt_eq_one _ (P := (· ∈ Q)) hv h1, one_mul] at h4
    exact GlobalTheory.PenLevOff.mem_of_uloc_le hJ.is hJ'.is j hjm _ _ v
      (_root_.GlobalTheory.PenLevOff.uloc_le_alt W hW u a ha haT j hj t J hJ α t' J' hJ' α' v (fun h => hv (hQ v h)) (fun h => hv (hQ' v h)))
      (GlobalTheory.PenLevOff.cutAt_mem _ v _) h4
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutMemUStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_step_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p → p ∈ Q) → (∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p → p ∈ Q) → ∀ x ∈ J.A.U j (J.ι j α), GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) x ∈ J'.A.U j (J'.ι j α') := by
  first | exact @_root_.GlobalTheory.PenLevOff.cut_mem_U_alt | exact _root_.GlobalTheory.PenLevOff.cut_mem_U_alt | (intros; apply _root_.GlobalTheory.PenLevOff.cut_mem_U_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SuppMemLevel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SuppMemLevel
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenBridge.SuppLev
end GlobalTheory.PenBridge.SuppLev
open GlobalTheory.PenBridge in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.PenBridge.supp_mem_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (P : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p ∈ P, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p ∧ ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p) → ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ P), (∀ i, (J.G i).q.v ∈ P → _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj x i ∈ KO (J.G i).k _) → x ∈ J'.A.U j (J'.ι j α') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ t' J' hJ' α' P hP x hx hrd
  have hjm : j ≤ B.R.m := by omega
  have hok : I.Ok := hW.tr.ok
  have hsd : IsSelfDualC ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (a.g.x j).L := (ha.x j hjm).sd
  haveI : Submodule.IsLattice (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (a.g.x j).L := hsd.1
  have hfg : (a.g.x j).L.FG := Submodule.IsLattice.fg (A := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (a.g.x j).L
  have hlb := (hJ'.is.reads j hjm).lb (J'.ι j α')
  refine (hJ'.is.U j hjm _ _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hx, ?_⟩
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hd : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := ⟨_, (hPr.piT_norm u).symm⟩
  refine GlobalTheory.PenBridge.SuppLev.exists_mem_level_set (I.rec7 l Z) _ _ _ (J'.A.K j hjm (J'.ι j α')).lev (X.piT u) hd hlb
    (a.g.x j).L hfg
    (fun y => ((hat.pinX.xs j hjm).2.2 y).trans
      (forall_congr' fun r => ⟨fun h => ⟨⟨y r, h⟩, rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.2⟩)) (· ∈ P) x hx ?_
  intro v hvP
  obtain ⟨⟨i, hi⟩, hn'⟩ := hP v hvP
  subst hi
  have hu : I.UnderQ (W.P.I.tup t) (J.G i).q.v :=
    ⟨J.pl i, (hW.tq.Q t (J.pl i)).1 (J.mem i), ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).2 i).symm⟩
  obtain ⟨hTv, hgv⟩ := GlobalTheory.Mem.Col2.TC.underQ_notMem I hok l u _ _ hu
  refine ⟨fun h => ?_, hTv, ?_⟩
  · rcases hJ'.is.bad_le j hjm _ h with (h0 | h0) | ⟨Q, hQ, e⟩
    · exact hgv 0 h0
    · exact hgv 1 h0
    · obtain ⟨i', hi'⟩ := hJ'.surj Q ((hW.tq.Q t' Q).2 hQ)
      refine hn' ⟨i', ?_⟩
      rw [(_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t' J' hJ').2 i', hi']
      exact e
  · have h1 := hrd i hvP
    rw [_root_.GlobalTheory.PenBridge.reductionHomAtLastLevel, MonoidHom.pi_apply, _root_.GlobalTheory.PenBridge.rd_at_apply, toSum0_mem_KO_iff] at h1
    exact GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J.G i).q _ hsd (_root_.GlobalTheory.PenBridge.int_in_frame_at_level J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) h1
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SuppMemLevelStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_step_relation_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (P : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p ∈ P, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p ∧ ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p) → ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ P), (∀ i, (J.G i).q.v ∈ P → _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj x i ∈ KO (J.G i).k _) → x ∈ J'.A.U j (J'.ι j α') := by
  exact @_root_.GlobalTheory.PenBridge.supp_mem_level_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxLeSup
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut
variable {D : D7}
end GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
end
noncomputable section
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut GlobalTheory.PenLev.CongruenceSubgroupLevelSupport in
theorem GlobalTheory.PenLev.relax_le_sup_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j), ∀ g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α, g ∈ J'.A.U j (J'.ι j α') ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α t' J' hJ' α' g hg
  classical
  rw [_root_.GlobalTheory.PenLev.mem_relax_iff'] at hg
  obtain ⟨hsup, -, hint⟩ := hg
  let QJ : Finset (Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J.G i).q.v
  let QJ' : Finset (Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J'.G i).q.v
  have hQJ : ∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p ↔ p ∈ QJ := fun p => by simp [QJ, _root_.GlobalTheory.PenBridge.finitePlaceCondition]
  have hQJ' : ∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p ↔ p ∈ QJ' := fun p => by simp [QJ', _root_.GlobalTheory.PenBridge.finitePlaceCondition]
  set Q := QJ ∪ QJ' with hQ
  set P := QJ \ QJ' with hP
  have hN : (grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)).Normal := by
    unfold grpAt congGrp
    infer_instance
  have hmul := Subgroup.mul_normal (J.A.U j (J.ι j α)) (grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J))
  have hg' : g ∈ ((J.A.U j (J.ι j α) ⊔ grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) : Subgroup _) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := hsup
  rw [hmul] at hg'
  obtain ⟨x, hx, n, hn, rfl⟩ := hg'
  beta_reduce at hint ⊢
  have hxf : x ∈ GfC ((I.rec7 l Z).sp.X j) := ((hJ.is.U j (by omega) _ x).1 hx).1
  have huo : cutG ((I.rec7 l Z).sp.X j) _ (one_sub_idemQ_mul_self Q) x ∈ J'.A.U j (J'.ι j α') :=
    _root_.GlobalTheory.T.true_geometry_row_step_value_alt W hW u a ha hat j hj t J hJ α t' J' hJ' α' Q (fun p hp => Finset.mem_union_left _ ((hQJ p).1 hp))
      (fun p hp => Finset.mem_union_right _ ((hQJ' p).1 hp)) x hx
  set uo := cutG ((I.rec7 l Z).sp.X j) _ (one_sub_idemQ_mul_self Q) x
  set uq := cutG ((I.rec7 l Z).sp.X j) _ (idemQ_mul_self Q) x
  have huq : uq ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := cutG_mem_Q ((I.rec7 l Z).sp.X j) Q x
  have huoQ : uo ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ Q) := cutG_mem_Qc ((I.rec7 l Z).sp.X j) Q hxf
  have hnQ : n ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := grpAt_mono ((I.rec7 l Z).sp.X j) (fun p hp => Finset.mem_union_left _ ((hQJ p).1 hp)) hn
  set w := uq * n
  have hw : w ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := mul_mem huq hnQ
  have hgw : uq * uo * n = uo * w := by
    rw [comm_Q ((I.rec7 l Z).sp.X j) Q huq huoQ, mul_assoc]
  have hx' : x = uq * uo := (cutG_mul_cutG ((I.rec7 l Z).sp.X j) Q x).symm
  set wp := cutG ((I.rec7 l Z).sp.X j) _ (idemQ_mul_self P) w
  set wr := cutG ((I.rec7 l Z).sp.X j) _ (one_sub_idemQ_mul_self P) w
  have hwp : wp ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ P) := cutG_mem_Q ((I.rec7 l Z).sp.X j) P w
  have hwrP : wr ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ P) := cutG_mem_Qc ((I.rec7 l Z).sp.X j) P (grpAt_le_GfC ((I.rec7 l Z).sp.X j) _ hw)
  have hwrQ : wr ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := cutG_mem_congGrp ((I.rec7 l Z).sp.X j) _ _ _ hw
  have hwr : wr ∈ grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J') :=
    grpAt_inf_le ((I.rec7 l Z).sp.X j) (· ∈ Q) (· ∈ P) _ (fun p h1 h2 => by
      rw [hQJ']
      rw [hQ, Finset.mem_union] at h1
      rw [hP, Finset.mem_sdiff] at h2
      tauto) hwrQ hwrP
  have hww : w = wp * wr := (cutG_mul_cutG ((I.rec7 l Z).sp.X j) P w).symm
  have hgeq : x * n = uo * wp * wr := by
    rw [hx', hgw, hww, mul_assoc]
  have hwp' : wp ∈ J'.A.U j (J'.ι j α') := by
    refine _root_.GlobalTheory.T.true_geometry_row_step_relation_alt W hW u a ha hat j hj t J hJ t' J' hJ' α' P (fun p hp => ?_) wp hwp (fun i hi => ?_)
    · rw [hP, Finset.mem_sdiff] at hp
      exact ⟨(hQJ p).2 hp.1, fun h => hp.2 ((hQJ' p).1 h)⟩
    · have hiQ : (J.G i).q.v ∈ Q := by
        rw [hP, Finset.mem_sdiff] at hi
        exact Finset.mem_union_left _ hi.1
      have e1 : _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj uo i = 1 := by
        show _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i _ uo = 1
        rw [_root_.GlobalTheory.PenBridge.rd_at_apply, locHom_eq_one (J.G i).q ((I.rec7 l Z).sp.X j) _ (P := (· ∈ Q)) hiQ
          (grpAt_le_grpOff ((I.rec7 l Z).sp.X j) (· ∉ Q) (· ∈ Q) (fun p h h' => h h') huoQ), map_one]
      have e2 : _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj wr i = 1 := by
        show _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i _ wr = 1
        rw [_root_.GlobalTheory.PenBridge.rd_at_apply, locHom_eq_one (J.G i).q ((I.rec7 l Z).sp.X j) _ (P := (· ∈ P)) hi
          (grpAt_le_grpOff ((I.rec7 l Z).sp.X j) (· ∉ P) (· ∈ P) (fun p h h' => h h') hwrP), map_one]
      have h := hint i
      rw [hgeq, map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, e1, e2, one_mul, mul_one] at h
      exact h
  rw [hgeq]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem huo hwp')) (Subgroup.mem_sup_right hwr)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxLeSupStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_free_level_step_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j), ∀ g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α, g ∈ J'.A.U j (J'.ι j α') ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J') := by
  first | exact @_root_.GlobalTheory.PenLev.relax_le_sup_alt | exact _root_.GlobalTheory.PenLev.relax_le_sup_alt | (intros; apply _root_.GlobalTheory.PenLev.relax_le_sup_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RdMemKOOffTwist
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RdMemKOOffTwist
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
theorem GlobalTheory.PenBridge.rd_mem_KO_off_twist_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ j hj t₀ J₀ hJ₀ α₀ t J _ i _
  have hjm : j ≤ B.R.m := by omega
  obtain ⟨ε, hε, hε'⟩ := (J.G i).q.above
  have und : (J.pl i).under (𝓞 (I.rec7 l Z).host.F) = (J.G i).q.v :=
    GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε hε'
  have hv := (GlobalTheory.Mem.Col2.TC.underQ_notMem I hW.tr.ok l u (W.P.I.tup t) (J.G i).q.v
    ⟨J.pl i, (hW.tq.Q t _).1 (J.mem i), und⟩).1
  have hlb := (hJ₀.is.reads j hjm).lb (J₀.ι j α₀)
  have hfr : ∀ e : j = (J.G i).s + 1, ∃ pos, IsStdFr pos (_root_.GlobalTheory.PenBridge.frameAtLevel J j i e) := by
    intro e
    subst e
    exact ⟨_, (ha.stdQ _ _).1 _ _⟩
  obtain ⟨pos, hpos⟩ := hfr (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)
  have key : ∀ g ∈ J₀.A.U j (J₀.ι j α₀),
      GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) g ∈ KO (J.G i).k _ := by
    refine GlobalTheory.LevProd.OffTwist.locHom_mem_KO (J.G i).q _ (rankN (I.rec7 l Z) j hjm) _ hpos (B.T u) hv
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
  intro g hg
  exact (GlobalTheory.PenBridge.toSum0_mem_KO_iff _).2 (key g hg)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RdMemKOOffTwistStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_tuple_free_index_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ := by
  first | exact @_root_.GlobalTheory.PenBridge.rd_mem_KO_off_twist_alt | exact _root_.GlobalTheory.PenBridge.rd_mem_KO_off_twist_alt | (intros; apply _root_.GlobalTheory.PenBridge.rd_mem_KO_off_twist_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxedLevelEqTupleFree
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PenLev.rd_mem_KO_same_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i₀ i, (J₀.G i₀).q.v = (J.G i).q.v → ∀ g ∈ GfC _, _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J₀ j hj g i₀ ∈ KO (J₀.G i₀).k _ → _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ j hj t₀ J₀ _ t J _ i₀ i hv g _ h0
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L :=
    (ha.x j (by have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)).sd
  have h0' : GlobalTheory.LevIdx.locHom (J₀.G i₀).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J₀ j i₀ (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J₀ hj i₀)) g ∈ KO (J₀.G i₀).k _ :=
    (GlobalTheory.PenBridge.toSum0_mem_KO_iff _).1 h0
  have hm := GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J₀.G i₀).q _ hsd
    (_root_.GlobalTheory.PenBridge.int_in_frame_at_level J₀ j i₀ (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J₀ hj i₀)) h0'
  change GlobalTheory.PenBridge.toSum0 _ _ _ ∈ _
  rw [GlobalTheory.PenBridge.toSum0_mem_KO_iff]
  exact GlobalTheory.SplitInt.mem_KO_of_moves (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) (a.g.x j).L
    (· = (J₀.G i₀).q.v) hv.symm (_root_.GlobalTheory.PenBridge.int_in_frame_at_level J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) g hm _
    ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
theorem GlobalTheory.PenLev.rd_eq_one_of_grpAt_alt {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
    (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) {j : ℕ} (hj : j + 1 = B.R.m) (i : Fin J.r) {P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop} (hP : ¬ P (J.G i).q.v)
    {x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hx : x ∈ GlobalTheory.FinPl.grpAt _ P) : _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj x i = 1 := by
  have h1 : x ∈ GlobalTheory.FinPl.grpOff _ (· = (J.G i).q.v) :=
    GlobalTheory.FinPl.SetCut.grpAt_le_grpOff _ P (· = (J.G i).q.v) (fun p hp e => hP (e ▸ hp)) hx
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off (J.G i).q (P := (· = (J.G i).q.v)) rfl h1
  have h3 : GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) x = 1 := by
    symm
    rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
    simp [(_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)).βγ]
  change GlobalTheory.PenBridge.toSum0 _ _ _ = 1
  rw [h3, map_one]
theorem GlobalTheory.PenLev.relax_rd_mem_KO_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α, ∀ i, _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J' j hj g i ∈ KO (J'.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' g hg i
  obtain ⟨hsup, hgf, hrd⟩ := (_root_.GlobalTheory.PenLev.mem_relax_iff' J j hj α g).1 hg
  by_cases hv : _root_.GlobalTheory.PenBridge.finitePlaceCondition J (J'.G i).q.v
  · obtain ⟨i₀, hi₀⟩ := hv
    exact _root_.GlobalTheory.PenLev.rd_mem_KO_same_alt W hW u a ha hTr j hj t J hJ t' J' hJ' i₀ i hi₀ g hgf (hrd i₀)
  · have hle : J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) ≤
        (KO (J'.G i).k _).comap ((Pi.evalMonoidHom _ i).comp (_root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J' j hj)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact _root_.GlobalTheory.T.true_geometry_tuple_free_index_alt W hW u a ha hTr j hj t J hJ α t' J' hJ' i hv x hx
      · rw [Subgroup.mem_comap, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
          _root_.GlobalTheory.PenLev.rd_eq_one_of_grpAt_alt J' hj i hv hx]
        exact one_mem _
    exact hle hsup
theorem GlobalTheory.PenLev.relaxed_level_eq_tuple_free_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α = _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α
  have hle : ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j),
      _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α ≤ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J' j hj α' := by
    intro t J hJ α t' J' hJ' α' x hx
    have hx' := (_root_.GlobalTheory.PenLev.mem_relax_iff' J j hj α x).1 hx
    exact (_root_.GlobalTheory.PenLev.mem_relax_iff' J' j hj α' x).2
      ⟨_root_.GlobalTheory.T.tuple_free_level_step_alt W hW u a ha hTr j hj t J hJ α t' J' hJ' α' x hx, hx'.2.1,
        _root_.GlobalTheory.PenLev.relax_rd_mem_KO_alt W hW u a ha hTr j hj t J hJ α t' J' hJ' x hx⟩
  obtain ⟨t₀, J₀, α₀, hJ₀, h⟩ := _root_.GlobalTheory.PenLev.base_level_subgroup_eq_relax J j hj hJ α
  rw [h]
  exact le_antisymm (hle _ _ hJ α _ _ hJ₀ α₀) (hle _ _ hJ₀ α₀ _ _ hJ α)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxedLevelEqTupleFreeStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_tuple_free_relation_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α = _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj := by
  exact @_root_.GlobalTheory.PenLev.relaxed_level_eq_tuple_free_alt
end
end
