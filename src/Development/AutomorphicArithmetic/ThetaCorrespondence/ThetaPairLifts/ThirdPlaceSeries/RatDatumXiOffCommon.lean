module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfRead
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedAt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfGRead
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfGRead
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel
namespace GlobalTheory.LevUnif
theorem unif_of_gRead_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl → ∀ n : Fin a.n, valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a row col hR n
  exact _root_.GlobalTheory.LevelUnif.valuation_uniformizer_sub_q_lt (D := I.rec7 l Z) _ _ _ hR hW.lev.1 n
end GlobalTheory.LevUnif
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfGReadStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_line_choice_value : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl → ∀ n : Fin a.n, valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  first | exact @_root_.GlobalTheory.LevUnif.unif_of_gRead_alt | exact _root_.GlobalTheory.LevUnif.unif_of_gRead_alt | (intros; apply _root_.GlobalTheory.LevUnif.unif_of_gRead_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenXiIsLocFac
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
noncomputable section
namespace GlobalTheory.Fam.PenLoc
def penXi_alt {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (n : Fin a.n)
    (z : Matrix (Fin ((I.rec7 l Z).sp.X ((a.G n).s + 1)).rank) (Fin ((I.rec7 l Z).sp.X (a.G n).s).rank) (I.rec7 l Z).host.E) : ℂ :=
  ((a.G n).S.T (Fin B.R.t)).Psi 1
    (((a.G n).FX ((a.G n).s + 1) le_rfl).γ * z.map (ofSplit (a.G n).q).pr * ((a.G n).FX (a.G n).s (Nat.le_succ _)).β)
    ((a.G n).S.y0 (Fin B.R.t))
theorem penXi_isLocFac_of_allTrue : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (n : Fin a.n),
    GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg (a.G n).s) (_root_.GlobalTheory.Fam.PenLoc.penXi_alt a n) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col n
  have hR := (ha.tie row col).2
  letI := (a.G n).fld; letI := (a.G n).val; letI := (a.G n).top; letI := (a.G n).loc; letI := (a.G n).mea; letI := (a.G n).bor
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hid := (hR.idem n).1
  have hpf := GlobalTheory.LocMod.SymChainAt.place_facts (a.G n).q hid
  have hL : ∀ j, j ≤ B.R.m → IsSelfDualC _ (a.g.x j).L ∧
      ((a.g.x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec _ _ :=
    fun j hj => ⟨(ha.x j hj).sd, Set.ext (hat.pinX.xs j hj).2.2⟩
  exact ⟨(a.G n).k, _, _, _, _, ofSplit (a.G n).q, _, _, _, _, _, _, _, _, _, hpf.2, hid,
    GlobalTheory.SeeSaw.StdMatch.int_iff_up_mem (a.G n).q (a.G n).unit _ _ (hL _ (by omega)).1 (hL _ (by omega)).1 (hL _ (by omega)).2
      (hL _ (by omega)).2 ((a.G n).latX _ _) ((a.G n).latX _ _),
    GlobalTheory.LastTwoSteps.psi_mem_SB _ (Chain.ofType_regular _ _ _ _ _) _, (a.G n).cg_pen, fun _ => rfl⟩
end GlobalTheory.Fam.PenLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocXiEqMulMidXi
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
noncomputable section
namespace GlobalTheory.Fam.MidLoc
open _root_.Formalism.L2.Col (IntAt redP qOf)
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
end Loc
section Comparison₂
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Comparison₂
section Mat
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
end Mat
section Tuple
open _root_.Formalism.L2.Col
end Tuple
section World
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
set_option maxHeartbeats 1000000 in
theorem exists_sameData_atType (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) {row col} (hR : _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl) (n : Fin a.n)
    (hϖ : valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((qOf (a.pl n).1 : ℕ) : (a.G n).k)) <
      valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k)) :
    ∃ S' : SymData (a.G n).k (a.G n).s B.R.k, SameData S' (a.G n).S B.R.t (a.G n).ν ∧
      ∀ (b : I.ι) (P : BadPr I b), P.1 = (a.pl n).1 →
        AtType I.Ch I.sel (I.tup b) (I.cst b) B.embLL P ((a.G n).q.pr.comp (incA (I.rec7 l Z))) S' := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain ⟨hid, hv⟩ := hR.idem n
  obtain ⟨hi, hd⟩ := SymChainAt.place_facts (a.G n).q hid
  have hPm : (a.pl n).1 ∈ (B.primes X).vGs := (hW.lev.2.1 _).1 (a.pl n).2
  obtain ⟨i, g1, g2, -, g4, -⟩ := LevelData.type_prime hPm
  obtain ⟨ϖ, hϖq, -⟩ := LevelData.exists_unif (ι := (a.G n).q.pr.comp (incA (I.rec7 l Z))) hi hd (g1 ▸ g4)
  obtain ⟨S', e1, e2, e3, e4, e5⟩ := exists_normal (a.G n).S ϖ
    (by rw [hϖq, map_natCast, Valuation.map_sub_swap]; exact hϖ) B.R.t (a.G n).ν
  refine ⟨S', e5, fun b P hP => ?_⟩
  obtain ⟨PP, hPP⟩ := P
  obtain rfl : PP = (a.pl n).1 := hP
  have ok := hW.tr.ok
  have hok := ok.idx_ok b
  have f1 : Formalism.L2.Col.psi0P I.Ch (a.pl n).1 = I.Ch.psi0 ⟨_, hPm⟩ := dif_pos hPm
  have f2 : Formalism.L2.Col.chiP I.Ch (a.pl n).1 = Formalism.L2.Col.chiAt I.Ch ⟨_, hPm⟩ := dif_pos hPm
  refine ⟨hPm, hs.symm, hok.cst_ok, ok.sharp _, by rw [hW.tr.tw.cst_eq]; exact Nat.le_succ _,
    fun x hx => hok.psi0 ⟨_, hPP⟩ x hPm hx, ⟨hi, hd, rfl, e1 ▸ hϖq⟩, fun x hx => ?_, fun j x v h1 h2 h3 => ?_⟩
  · rw [e2]
    exact psi_tie (a.G n).q hv hi hd (g1 ▸ g2) (g1 ▸ g4) (hok.xiUnitAtPrime ⟨_, hPP⟩).1 (_root_.GlobalTheory.Fam.pk_z W).ψ W.Q.stdChar B.embLL _
      (fun z c h => f1 ▸ ok.weil ⟨_, hPm⟩ z c h) _ (a.G n).char x hx
  · rw [Formalism.L2.Col.LocE.unitV, dif_pos h2]
    by_cases hj : j < B.R.m
    · rw [e3 _ (by omega)]
      have key := chi_tie (a.G n).q hid hi hd (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta (j + 1)
        (c := (Units.map (B.embLL : B.fields.K →* ℂ)).comp (Formalism.L2.Col.chiP I.Ch (a.pl n).1 j)) (hW.tr.chr ⟨j, hj⟩)
        (fun y x c hx hy => Units.ext (by
          have h := hok.mu0G ⟨j, hj⟩ ⟨_, hPm⟩ x y c hx hy
          have e3 : Formalism.L2.Col.chiP I.Ch (a.pl n).1 j = I.Ch.chi ⟨j, hj⟩ ⟨_, hPm⟩ := (congrFun f2 j).trans (dif_pos hj)
          rw [e3]
          exact h.symm))
        W.Q.charW.base.lev.eta
        (fun y x c hx hy => ((_root_.GlobalTheory.Fam.pk_z W).C.isEta.unr (a.pl n).1 _ (by
          have hy' : y ∉ (a.pl n).1.asIdeal := fun h => by
            haveI := (a.pl n).1.isPrime
            exact c.ne_zero (hy.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
          change Valued.v (((x : (I.rec7 l Z).host.E)) : (a.pl n).1.adicCompletion (I.rec7 l Z).host.E) = 1
          rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hx]
          exact ((a.pl n).1.valuation_eq_one_iff_notMem (K := (I.rec7 l Z).host.E)).2 hy')).symm)
        _ (hR.mu n (j + 1) (by omega) hj) x v h2.unit h1 rfl h3
      rw [key]
      rfl
    · rw [e4 _ (by omega), ((congrFun f2 j).trans (dif_neg hj) : Formalism.L2.Col.chiP I.Ch (a.pl n).1 j = 1)]
      simp
end World
section Main
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
def intermediateXiValue (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (n : Fin a.n) (j c : ℕ) (H : j + 1 + c = (a.G n).s)
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E) : ℂ :=
  ((a.G n).S.T (Fin B.R.t)).entry (a.G n).S.ψ (a.G n).ν j c H 1 1
    (((a.G n).FX (j + 1) (by omega)).γ * z.map (ofSplit (a.G n).q).pr * ((a.G n).FX j (by omega)).β)
theorem midXi_isLocFac' {a : _root_.GlobalTheory.Fam.GeometricFamily W u} (ha : a.Is) (hat : a.True) {row col} (hR : _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl) (n : Fin a.n)
    (j c : ℕ) (H : j + 1 + c = (a.G n).s) :
    IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) (_root_.GlobalTheory.Fam.MidLoc.intermediateXiValue a n j c H) := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hid := (hR.idem n).1
  have hpf := SymChainAt.place_facts (a.G n).q hid
  have hL : ∀ j, j ≤ B.R.m → IsSelfDualC _ (a.g.x j).L ∧
      ((a.g.x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec _ _ :=
    fun j hj => ⟨(ha.x j hj).sd, Set.ext (hat.pinX.xs j hj).2.2⟩
  exact ⟨(a.G n).k, _, _, _, _, ofSplit (a.G n).q, _, _, _, _, _, _, _, _, _, hpf.2, hid,
    StdMatch.int_iff_up_mem (a.G n).q (a.G n).unit _ _ (hL _ (by omega)).1 (hL _ (by omega)).1 (hL _ (by omega)).2
      (hL _ (by omega)).2 ((a.G n).latX _ _) ((a.G n).latX _ _),
    (SB _).smul_mem _ (opE_mem_SB 1 _ _ (om_mem_SB _ _ _ ((Chain.ofType_regular _ _ _ _ _).1 _ _ _))), (a.G n).cg_mid j c H,
    fun _ => rfl⟩
set_option maxHeartbeats 1000000 in
theorem locXi_eq_mul_midXi_alt (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {a : _root_.GlobalTheory.Fam.GeometricFamily W u} (ha : a.Is) {row col} (hR : _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl) (n : Fin a.n)
    (hϖ : valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((qOf (a.pl n).1 : ℕ) : (a.G n).k)) <
      valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k))
    (j c : ℕ) (H : j + 1 + c = (a.G n).s) (hj : j + 1 ≤ B.R.m) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)) (P : BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
      ∀ z, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (homOf I l Z j hj z)) = C * _root_.GlobalTheory.Fam.MidLoc.intermediateXiValue a n j c H z := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  by_cases h0 : ∃ (b : I.ι) (P : BadPr I b), P.1 = (a.pl n).1
  swap
  · exact ⟨1, one_ne_zero, fun t _ _ _ _ P hP => absurd ⟨_, P, hP⟩ h0⟩
  obtain ⟨b₀, P₀, hP₀⟩ := h0
  obtain ⟨S', hS, hA⟩ := _root_.GlobalTheory.Fam.MidLoc.exists_sameData_atType hW a hR n hϖ
  obtain ⟨e', he', hF'⟩ := (ha.stdG n).1 j (by omega)
  obtain ⟨e, he, hF⟩ := (ha.stdG n).1 (j + 1) (by omega)
  have hr' := rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)
  have hr := rankN (I.rec7 l Z) (j + 1) hj
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.EntryBridge.entry_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a.G n).ν (a.G n).unitVol (hA b₀ P₀ hP₀) j c H
    (e'.trans (finCongr hr')) (e.trans (finCongr hr)) he' he
  refine ⟨C⁻¹, inv_ne_zero hC0, fun t J hJ α γ P hP z => ?_⟩
  have hPv : P.1 ∈ (B.primes X).vGs := (hA _ P hP).mem
  have hh : ∀ i b, (I.idx (W.P.I.tup t)).h i b P = 1 := by
    rw [(hW.tr.tw (W.P.I.tup t)).2]
    exact fun i b => StdMatch.twSt_h _ _ _ _ _ _ b P hPv
  have hlt := LevelData.val_lt_one_iff (hA _ P hP).tie.compl.int
  have hfr : ∀ i, i + 1 < B.R.m → ∀ β r s, _ := fun i hi β r s => (hlt _).2 (frame_cong hW.tr.ok (J.A.p0 i β).1.1
    (hJ.std i hi β ▸ (hJ.is.base i (by omega) β).1) P hPv r s)
  obtain ⟨g, hg, g', hg', hz⟩ := toLoc_inFr ((a.G n).q.pr.comp (incA (I.rec7 l Z))) hr' hr _ _ e' e hF' hF _ _
    (hfr j (by omega) (J.ι j α)) (hfr (j + 1) (by omega) (J.ι (j + 1) γ))
  have key := (congrArg _ (hz z)).symm.trans (hC _)
  rw [hS.1, hW.tr.tw.cst_eq, xiAt_tw_eq _ _ _ _ _ P₀ P (hP₀.trans hP.symm) (hA _ P₀ hP₀).mem] at key
  replace key := (entry_mul_KOne (a.G n).S (Fin B.R.t) (a.G n).ν j c H hg hg' _).symm.trans key
  unfold locXi
  rw [dif_pos (by omega), hh, hh, eq_inv_mul_iff_mul_eq₀ hC0]
  exact (congrArg (fun y => C * B.embLL (Formalism.L2.Col.XiAt I.Ch I.sel (I.tup (W.P.I.tup t)) y j P 1 1 _))
    (hW.tr.tw.cst_eq (W.P.I.tup t))).trans key.symm
end Main
end GlobalTheory.Fam.MidLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiLevEqConstMulLocFac
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MidLocFac
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MidLocFac
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MidLoc
theorem mid_locFac_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 2 < B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat n j hj hj2
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain ⟨c, H⟩ : ∃ c, j + 1 + c = (a.G n).s := ⟨(a.G n).s - (j + 1), by omega⟩
  have hR := (ha.tie (fun t => (nonempty_rowCh (_root_.GlobalTheory.Fam.complexLevelStructure W) hW.pk.bot.hyp.2.2.2.1.chain u a.g t).some)
    fun t => (nonempty_colCh (D := I.rec7 l Z) u _).some).2
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.Fam.MidLoc.locXi_eq_mul_midXi_alt hW ha hR n (_root_.GlobalTheory.T.true_geometry_line_choice_value W hW u a _ _ hR n) j c H hj
  exact ⟨C, hC0, fun t J hJ α γ => ⟨_root_.GlobalTheory.Fam.MidLoc.intermediateXiValue a n j c H, _root_.GlobalTheory.Fam.MidLoc.midXi_isLocFac' ha hat hR n j c H, hC t J hJ α γ⟩⟩
end GlobalTheory.Fam.MidLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MidLocFacStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_finite_index_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 2 < B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  first | exact @_root_.GlobalTheory.Fam.MidLoc.mid_locFac_alt | exact _root_.GlobalTheory.Fam.MidLoc.mid_locFac_alt | (intros; apply _root_.GlobalTheory.Fam.MidLoc.mid_locFac_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenLocFac
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenMatch
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrsFMemGlintRedVEq
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrsFMemGlintRedVEq
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
namespace GlobalTheory.Fam.LevelFrames
set_option maxHeartbeats 1000000 in
theorem frsF_mem_glint_redV_eq_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (j : ℕ), j + 1 ≤ B.R.m → ∀ (β : J.Ch₀ j) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
    Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1 ∧
    ∀ x ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N j) P.1, Formalism.L2.Col.redV P.1 (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P x) = Formalism.L2.Col.redV P.1 x := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ n t J hJ j hj β P hP
  letI := GlobalTheory.Mem.Col2.starE B
  have hPv : P.1 ∈ (B.primes X).vGs := hP ▸ (hW.lev.2.1 _).1 (a.pl n).2
  refine ⟨?_, fun x hx => redV_eq_of_near (fun r s => ?_) hx⟩
  · have e : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P = (J.A.p0 j β).1.1.deco.1.liftFr ⟨P.1, hPv⟩ :=
      dif_pos hPv
    have h := (GlobalTheory.TopStep.liftFr_spec (J.A.p0 j β).1.1.deco.2 ⟨P.1, hPv⟩).1
    have hN := (hJ.is.base j (by omega) β).2
    rw [e]
    intro x
    refine Iff.trans ?_ (h x)
    exact Iff.of_eq (congrArg (fun N => _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N) hN.symm)
  · rcases hj.eq_or_lt with h | h
    · exact _root_.GlobalTheory.Fam.TopFrames.valuation_frs_sub_kronecker_lt_one hW hJ P hPv h β r s
    · have key := MidLoc.frame_cong hW.tr.ok (J.A.p0 j β).1.1 (hJ.std j h β ▸ (hJ.is.base j (by omega) β).1) P hPv r s
      rwa [if_congr Fin.ext_iff rfl rfl] at key
end GlobalTheory.Fam.LevelFrames
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrsFMemGlintRedVEqStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_finite_family_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (j : ℕ), j + 1 ≤ B.R.m → ∀ (β : J.Ch₀ j) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
    Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1 ∧
    ∀ x ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N j) P.1, Formalism.L2.Col.redV P.1 (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P x) = Formalism.L2.Col.redV P.1 x := by
  first | exact @_root_.GlobalTheory.Fam.LevelFrames.frsF_mem_glint_redV_eq_alt | exact _root_.GlobalTheory.Fam.LevelFrames.frsF_mem_glint_redV_eq_alt | (intros; apply _root_.GlobalTheory.Fam.LevelFrames.frsF_mem_glint_redV_eq_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenMatch
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.Fam.PenLoc
theorem pen_match_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (n : Fin a.n) (hj : (a.G n).s + 1 ≤ B.R.m),
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads →
    ∀ (α : J.Ch (a.G n).s) (γ : J.Ch ((a.G n).s + 1)) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z,
      B.embLL (Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P 1
        (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 (a.G n).s (J.ι _ α)).1.1 P)
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P) (GlobalTheory.QTw.homOf I l Z (a.G n).s hj z))
        ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P).symm
          (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2))) = c * _root_.GlobalTheory.Fam.PenLoc.penXi_alt a n z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr row col n hj
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hd := GlobalTheory.TypePrimeUnif.intAt_div_qOf B.fields (B.primes X) (GlobalTheory.Mem.FieldsLaws.fields_ok B) (GlobalTheory.BasePrimes.primes_ok B X).1
  have hR := (hIs.tie row col).2
  have hϖ := _root_.GlobalTheory.T.true_geometry_line_choice_value W hW u a row col hR n
  obtain ⟨S', hSame, hA'⟩ := _root_.GlobalTheory.Fam.MidLoc.exists_sameData_atType hW a hR n hϖ
  have hA : ∀ t (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → GlobalTheory.SymBridge.AtType I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL P (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) S' :=
    fun t P hP => hA' _ P hP
  obtain ⟨e'₀, he'₀⟩ := GlobalTheory.QTw.exists_xOrd B.R (a.G n).s
  obtain ⟨e₀, he₀⟩ := GlobalTheory.QTw.exists_xOrd B.R ((a.G n).s + 1)
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℂ, C ≠ 0 ∧ ∀ (e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) (a.G n).s ≃ Fin (B.R.N (a.G n).s))
      (e : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))),
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e →
      ∀ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
      ∀ (x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N (a.G n).s) (B.R.N ((a.G n).s + 1))) (y' : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1))),
        (S'.T (Fin B.R.t)).Psi 1 (GlobalTheory.SymBridge.toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) e e' x₀) (fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y' (e r))) =
          C * B.embLL (Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P 1 x₀ y') := by
    by_cases h0 : ∃ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1
    · obtain ⟨t₀, P₀, hP₀⟩ := h0
      have hA₀ := hA t₀ P₀ hP₀
      obtain ⟨C, hC0, hC⟩ := GlobalTheory.SymBridge.psiAgree_of_atType _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a.G n).ν (a.G n).unitVol hA₀ e'₀ e₀ he'₀ he₀
      refine ⟨C, hC0, fun e' e he' he t P hP x₀ y' => ?_⟩
      obtain rfl : e' = e'₀ := Equiv.ext fun r => Fin.ext ((he' r).trans (he'₀ r).symm)
      obtain rfl : e = e₀ := Equiv.ext fun r => Fin.ext ((he r).trans (he₀ r).symm)
      rw [hC x₀ y']
      congr 2
      exact psiAt_one_eq I.Ch I.sel _ _ _ _ _ P₀ P (hP₀.trans hP.symm) hA₀.mem (hA₀.sharp.trans (hA t P hP).sharp.symm) x₀ y'
    · exact ⟨1, one_ne_zero, fun _ _ _ _ t P hP => absurd ⟨t, P, hP⟩ h0⟩
  refine ⟨C⁻¹, inv_ne_zero hC0, fun t J hJ α γ P hP z => ?_⟩
  have hAt := hA t P hP
  obtain ⟨hf1, hf2⟩ := _root_.GlobalTheory.T.true_geometry_finite_family_alt W hW u a hIs hTr n t J hJ (a.G n).s (by omega) (J.ι _ α) P hP
  obtain ⟨hg1, hg2⟩ := _root_.GlobalTheory.T.true_geometry_finite_family_alt W hW u a hIs hTr n t J hJ ((a.G n).s + 1) (by omega) (J.ι _ γ) P hP
  refine (congrArg B.embLL (GlobalTheory.T.penultimateDatum_unchanged_frames_congruent_one I.Ch I.sel _ _ (a.G n).s P hAt.mem hAt.steps (hd P.1 hAt.mem) _ _ hf1 hf2 hg1 hg2 (homOf I l Z _ hj z) (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2))).trans ?_
  rw [eq_inv_mul_iff_mul_eq₀ hC0]
  obtain ⟨e₁, he₁, hβ₁⟩ := (hIs.stdG n).1 (a.G n).s (Nat.le_succ _)
  obtain ⟨e₂, he₂, hβ₂⟩ := (hIs.stdG n).1 ((a.G n).s + 1) le_rfl
  have hr1 : ((I.rec7 l Z).sp.X (a.G n).s).rank = B.R.N (a.G n).s := rankN (I.rec7 l Z) _ (Nat.le_of_succ_le hj)
  have hr2 : ((I.rec7 l Z).sp.X ((a.G n).s + 1)).rank = B.R.N ((a.G n).s + 1) := rankN (I.rec7 l Z) _ hj
  set e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) (a.G n).s ≃ Fin (B.R.N (a.G n).s) := e₁.trans (finCongr hr1) with he'd
  set e : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1)) := e₂.trans (finCongr hr2) with hed
  have ho' : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' := fun r => he₁ r
  have ho : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e := fun r => he₂ r
  refine Eq.trans (hC e' e ho' ho t P hP (homOf I l Z _ hj z) (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2)).symm ?_
  have hq : ((S'.ϖ : (a.G n).kˣ) : (a.G n).k) = ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k) := by
    rw [hAt.tie.compl.unif, map_natCast]
    exact congrArg (fun Q => ((Formalism.L2.Col.qOf Q : ℕ) : (a.G n).k)) hP
  have hnear : valuation (a.G n).k (((S'.ϖ : (a.G n).kˣ) : (a.G n).k) - (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k)) <
      valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
    rw [hq, Valuation.map_sub_swap]; exact hϖ
  have hinv := GlobalTheory.SymChain.UnifChange.inv_sub_inv_mem (a.G n).S.unif hnear
  have hcos : (fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2 (e r))) -
      S'.y0 (Fin B.R.t) ∈ box (GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1)) (1 : (a.G n).kˣ) := fun r => by
    have h1 := hJ.cosG n γ e ho r
    have h2 := lastStepPoints_sub_integral_of_uniformiser_inv (a.G n).S S' (Fin B.R.t) hinv r
    have h4 := add_mem h1 h2
    rw [sub_add_sub_cancel] at h4
    exact h4
  refine ((GlobalTheory.SymChain.atMostOne_holds (a.G n).k (a.G n).ν (a.G n).unitVol _ _ S' (Fin B.R.t)).2.2.2.1 _ _ hcos).trans ?_
  refine (hSame.2.1 _).trans ?_
  have hb : ∀ {j : ℕ} (hjj : j ≤ (a.G n).s + 1) (hr : ((I.rec7 l Z).sp.X j).rank = B.R.N j) (e₃ : GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin B.R.t) j ≃ Fin ((I.rec7 l Z).sp.X j).rank),
      ((a.G n).FX j hjj).β = (1 : Matrix _ _ (a.G n).k).submatrix id e₃ → ∀ r c,
      ((a.G n).FX j hjj).β r c = _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n ((LinearEquiv.refl B.fields.E (Formalism.L2.Col.Sp B.fields.E (B.R.N j))) (Pi.single ((e₃.trans (finCongr hr)) c) 1) (finCongr hr r)) := by
    intro j hjj hr e₃ hβ r c
    rw [hβ]
    change (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (a.G n).k) r (e₃ c) = _
    rw [Matrix.one_apply, LinearEquiv.refl_apply, Pi.single_apply]
    show _ = _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (if (finCongr hr) r = (finCongr hr) (e₃ c) then 1 else 0)
    by_cases h : r = e₃ c
    · rw [if_pos h, if_pos (by rw [h]), map_one]
    · rw [if_neg h, if_neg (fun h' => h ((finCongr hr).injective h')), map_zero]
  have hfr : GlobalTheory.SymBridge.toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) e e' (homOf I l Z _ hj z) =
      ((a.G n).FX ((a.G n).s + 1) le_rfl).γ * z.map (ofSplit (a.G n).q).pr * ((a.G n).FX (a.G n).s (Nat.le_succ _)).β := by
    have h5 := GlobalTheory.SeeSaw.StdMatch.mul_toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) hr1 hr2 (LinearEquiv.refl _ _) (LinearEquiv.refl _ _) e' e _ _
      (hb (Nat.le_succ _) hr1 e₁ hβ₁) (hb le_rfl hr2 e₂ hβ₂) z
    let T : Matrix (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((a.G n).s + 1)) (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) (a.G n).s) (a.G n).k :=
      GlobalTheory.SymBridge.toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) e e' (homOf I l Z _ hj z)
    have h5' : ((a.G n).FX ((a.G n).s + 1) le_rfl).β * T =
        z.map (ofSplit (a.G n).q).pr * ((a.G n).FX (a.G n).s (Nat.le_succ _)).β := h5
    have h6 : ((a.G n).FX ((a.G n).s + 1) le_rfl).γ * (((a.G n).FX ((a.G n).s + 1) le_rfl).β * T) = T := by
      rw [← Matrix.mul_assoc, Frame.γβ, Matrix.one_mul]
    refine h6.symm.trans ?_
    refine (congrArg _ h5').trans ?_
    exact (Matrix.mul_assoc _ _ _).symm
  unfold _root_.GlobalTheory.Fam.PenLoc.penXi_alt
  exact congrArg (fun x => ((a.G n).S.T (Fin B.R.t)).Psi 1 x ((a.G n).S.y0 (Fin B.R.t))) hfr
end GlobalTheory.Fam.PenLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenMatchStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_line_family_value : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (n : Fin a.n) (hj : (a.G n).s + 1 ≤ B.R.m),
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads →
    ∀ (α : J.Ch (a.G n).s) (γ : J.Ch ((a.G n).s + 1)) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z,
      B.embLL (Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P 1
        (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 (a.G n).s (J.ι _ α)).1.1 P)
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P) (GlobalTheory.QTw.homOf I l Z (a.G n).s hj z))
        ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P).symm
          (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2))) = c * _root_.GlobalTheory.Fam.PenLoc.penXi_alt a n z := by
  first | exact @_root_.GlobalTheory.Fam.PenLoc.pen_match_alt | exact _root_.GlobalTheory.Fam.PenLoc.pen_match_alt | (intros; apply _root_.GlobalTheory.Fam.PenLoc.pen_match_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenLocFac
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
noncomputable section
namespace GlobalTheory.Fam.PenLoc
theorem pen_locFac_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 2 = B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat n j hj hj2
  have hstd := hat.pinX.std
  have row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t := fun t =>
    ⟨fun _ _ => 0, fun _ _ _ => 0, fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepBF hstd _ _).some,
      fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepFB hstd _ _).some, fun _ => 0, fun _ _ => 0⟩
  have col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)) :=
    fun t =>
      { kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => 0, eT := fun _ _ _ => 0,
        Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 }
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain rfl : j = (a.G n).s := by omega
  obtain ⟨c, hc, hmatch⟩ := _root_.GlobalTheory.T.true_geometry_line_family_value W hW u a ha hat row col n hj
  refine ⟨c, hc, fun t J hJ α γ => ⟨_root_.GlobalTheory.Fam.PenLoc.penXi_alt a n, _root_.GlobalTheory.Fam.PenLoc.penXi_isLocFac_of_allTrue W hW u a ha hat row col n, fun P hP z => ?_⟩⟩
  have hPv : P.1 ∈ (B.primes X).vGs := hP ▸ (hW.lev.2.1 _).1 (a.pl n).2
  have hh : ∀ b, (I.idx (W.P.I.tup t)).h (a.G n).s b P = 1 := by
    rw [(hW.tr.tw (W.P.I.tup t)).2]
    exact fun b => GlobalTheory.SeeSaw.StdMatch.twSt_h _ _ _ _ _ _ b P hPv
  rw [← hmatch t J hJ α γ P hP z]
  unfold GlobalTheory.QTw.locXi
  rw [dite_eq_right (by omega), dite_eq_left (by omega), hh]
end GlobalTheory.Fam.PenLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenLocFacStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_finite_index_alt_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 2 = B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  first | exact @_root_.GlobalTheory.Fam.PenLoc.pen_locFac_alt | exact _root_.GlobalTheory.Fam.PenLoc.pen_locFac_alt | (intros; apply _root_.GlobalTheory.Fam.PenLoc.pen_locFac_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAtTypeTop
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsLocFacXiStd
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.Fam.TopLocFac
theorem isLocFac_xiStd_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ n : Fin a.n,
   GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg ((a.G n).s + 1)) (_root_.GlobalTheory.Fam.TopLoc.standardXi a n) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ht n
  have hid := ((ha.tie (fun t => (nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g ht.pinX.std t).some) fun t => (nonempty_colCh (D := I.rec7 l Z) u _).some).2.idem n).1
  obtain ⟨hs, hX, -⟩ := hW.tr.ok.spaces
  have hsd : ∀ j, j ≤ B.R.m → IsSelfDualC _ (a.g.x j).L := fun j hj => by
    have e : ((a.g.x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ :=
      Set.ext (ht.pinX.xs j hj).2.2
    have h1 := GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq ((I.rec7 l Z).sp.X j) hs _ (hX j)
    have h2 : GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j) = (a.g.x j).L := SetLike.coe_injective (h1.trans e.symm)
    rw [← h2]
    exact GlobalTheory.PlaceModel.isSelfDualC_latFrame _
  have hm : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  exact ⟨(a.G n).k, _, _, _, _, ofSplit (a.G n).q, _, _, _, _, _, _, (a.G n).FX ((a.G n).s + 1) le_rfl, (a.G n).FM, _,
    (GlobalTheory.QTw.GeoInhab.int_dense (a.G n).q hid).2, hid,
    GlobalTheory.StdHomAt.int_iff_up_mem_stdHom _ _ (a.G n).q (a.G n).unit _ _ _ _ _ _ _ _ (hsd _ (by omega)) (hsd _ hm.le)
      (ht.pinX.xs _ (by omega)).2.2 (ht.pinX.xs _ hm.le).2.2 ((a.G n).latX _ _) (a.G n).latM,
    GlobalTheory.LastTwoSteps.xiTop_mem_SB _ (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _) (a.G n).S.cond (a.G n).unitVol (by simp) _,
    (a.G n).cg_top, fun _ => rfl⟩
end GlobalTheory.Fam.TopLocFac
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAtTypeTop
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000
namespace GlobalTheory.Fam.TopLoc
section Normal
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SymChain GlobalTheory.SymChain.UnifChange GlobalTheory.Fam.MidLoc
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
theorem exists_atType_with_same_psi_and_phi_max (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) {row col} (hR : _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl) (n : Fin a.n)
    (hϖ : valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) <
      valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k)) :
    ∃ S' : SymData (a.G n).k (a.G n).s B.R.k, S'.ψ = (a.G n).S.ψ ∧ (S'.T (Fin B.R.t)).PhiTop = ((a.G n).S.T (Fin B.R.t)).PhiTop ∧
      ∀ (b : I.ι) (P : BadPr I b), P.1 = (a.pl n).1 →
        AtType I.Ch I.sel (I.tup b) (I.cst b) B.embLL P (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) S' := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain ⟨hid, hv⟩ := hR.idem n
  obtain ⟨hi, hd⟩ := SymChainAt.place_facts (a.G n).q hid
  have hPm : (a.pl n).1 ∈ (B.primes X).vGs := (hW.lev.2.1 _).1 (a.pl n).2
  obtain ⟨i, g1, g2, -, g4, -⟩ := LevelData.type_prime hPm
  obtain ⟨ϖ, hϖq, -⟩ := LevelData.exists_unif (ι := (a.G n).q.pr.comp (incA (I.rec7 l Z))) hi hd (g1 ▸ g4)
  obtain ⟨S', e1, e2, e3, e4, e5⟩ := exists_normal_top (a.G n).S ϖ
    (by rw [hϖq, map_natCast, Valuation.map_sub_swap]; exact hϖ) B.R.t
  refine ⟨S', e2, e5, fun b P hP => ?_⟩
  obtain ⟨PP, hPP⟩ := P
  obtain rfl : PP = (a.pl n).1 := hP
  have ok := hW.tr.ok
  have hok := ok.idx_ok b
  have f1 : Formalism.L2.Col.psi0P I.Ch (a.pl n).1 = I.Ch.psi0 ⟨_, hPm⟩ := dif_pos hPm
  have f2 : Formalism.L2.Col.chiP I.Ch (a.pl n).1 = Formalism.L2.Col.chiAt I.Ch ⟨_, hPm⟩ := dif_pos hPm
  refine ⟨hPm, hs.symm, hok.cst_ok, ok.sharp _, by rw [hW.tr.tw.cst_eq]; exact Nat.le_succ _,
    fun x hx => hok.psi0 ⟨_, hPP⟩ x hPm hx, ⟨hi, hd, rfl, e1 ▸ hϖq⟩, fun x hx => ?_, fun j x v h1 h2 h3 => ?_⟩
  · rw [e2]
    exact psi_tie (a.G n).q hv hi hd (g1 ▸ g2) (g1 ▸ g4) (hok.xiUnitAtPrime ⟨_, hPP⟩).1 (_root_.GlobalTheory.Fam.pk_z W).ψ W.Q.stdChar B.embLL _
      (fun z c h => f1 ▸ ok.weil ⟨_, hPm⟩ z c h) _ (a.G n).char x hx
  · rw [Formalism.L2.Col.LocE.unitV, dif_pos h2]
    by_cases hj : j < B.R.m
    · rw [e3 _ (by omega)]
      have key := chi_tie (a.G n).q hid hi hd (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta (j + 1)
        (c := (Units.map (B.embLL : B.fields.K →* ℂ)).comp (Formalism.L2.Col.chiP I.Ch (a.pl n).1 j)) (hW.tr.chr ⟨j, hj⟩)
        (fun y x c hx hy => Units.ext (by
          have h := hok.mu0G ⟨j, hj⟩ ⟨_, hPm⟩ x y c hx hy
          have e3 : Formalism.L2.Col.chiP I.Ch (a.pl n).1 j = I.Ch.chi ⟨j, hj⟩ ⟨_, hPm⟩ := (congrFun f2 j).trans (dif_pos hj)
          rw [e3]
          exact h.symm))
        W.Q.charW.base.lev.eta
        (fun y x c hx hy => ((_root_.GlobalTheory.Fam.pk_z W).C.isEta.unr (a.pl n).1 _ (by
          have hy' : y ∉ (a.pl n).1.asIdeal := fun h => by
            haveI := (a.pl n).1.isPrime
            exact c.ne_zero (hy.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
          change Valued.v (((x : (I.rec7 l Z).host.E)) : (a.pl n).1.adicCompletion (I.rec7 l Z).host.E) = 1
          rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hx]
          exact ((a.pl n).1.valuation_eq_one_iff_notMem (K := (I.rec7 l Z).host.E)).2 hy')).symm)
        _ (hR.mu n (j + 1) (by omega) hj) x v h2.unit h1 rfl h3
      rw [key]
      rfl
    · rw [e4 _ (by omega), ((congrFun f2 j).trans (dif_neg hj) : Formalism.L2.Col.chiP I.Ch (a.pl n).1 j = 1)]
      simp
end Normal
theorem loc_top_common_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 1 = B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr hiA n j hj hjm
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain rfl : j = (a.G n).s + 1 := by omega
  have hR := (hIs.tie (fun t => (GlobalTheory.Fam.TopLocFac.nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g hTr.pinX.std t).some)
    fun t => (GlobalTheory.Fam.TopLocFac.nonempty_colCh (D := I.rec7 l Z) u _).some).2
  obtain ⟨S', hψ, hΦ, hAt⟩ := _root_.GlobalTheory.Fam.TopLoc.exists_atType_with_same_psi_and_phi_max hW a hR n (_root_.GlobalTheory.LevUnif.unif_of_gRead_alt W hW u a _ _ hR n)
  have hxi : ∀ yb, (S'.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) S'.ψ (a.G n).ν (-1) yb =
      ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1) yb := fun yb => by
    unfold Chain.xiTop
    rw [hΦ, hψ]
    rfl
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℂ, C ≠ 0 ∧ ∀ (e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1)))
      (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((a.G n).s + 1)) (Fin B.R.t) ((a.G n).s + 2) ⊕ Unit ≃ Fin (B.R.N B.R.m)),
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e →
      ∀ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
      ∀ (y : Formalism.L2.Col.HomE B.fields.E (B.R.N ((a.G n).s + 1)) (B.R.N B.R.m)) (y' : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1))),
       (∀ i, Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : B.fields.E) * y' i)) →
       ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1)
           (Submodule.Quotient.mk fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y' (e' r))) (GlobalTheory.SymBridge.toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) e e' y) =
         C * B.embLL (GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P y y') := by
    by_cases h0 : ∃ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1
    · obtain ⟨t₀, P₀, hP₀⟩ := h0
      have hA₀ := hAt _ P₀ hP₀
      obtain ⟨e'₀, he'₀⟩ := GlobalTheory.QTw.exists_xOrd B.R ((a.G n).s + 1)
      obtain ⟨e₀, he₀⟩ := GlobalTheory.QTw.exists_topOrd B.R (a.G n).s hs
      obtain ⟨C, hC0, hC⟩ := (GlobalTheory.SymBridge.matchAtType _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a.G n).ν (a.G n).unitVol hA₀).2.2 e'₀
        (e₀.trans (finCongr (congrArg B.R.N hs))) he'₀ (fun r => he₀ r)
      refine ⟨C, hC0, fun e' e he' he t P hP y y' hy => ?_⟩
      obtain rfl : e' = e'₀ := Equiv.ext fun r => Fin.ext ((he' r).trans (he'₀ r).symm)
      obtain rfl : e = e₀.trans (finCongr (congrArg B.R.N hs)) := Equiv.ext fun r => Fin.ext ((he r).trans (he₀ r).symm)
      have hA := hAt _ P hP
      have hPP : P₀.1 = P.1 := hP₀.trans hP.symm
      have hy₀ : ∀ i, Formalism.L2.Col.IntAt P₀.1 ((Formalism.L2.Col.qOf P₀.1 : B.fields.E) * y' i) := by rw [hPP]; exact hy
      refine ((congrFun (hxi _) _).symm.trans (hC y y' hy₀)).trans ?_
      exact congrArg (fun x => C * B.embLL x)
        (locTop_eq_of_type I.Ch I.sel _ _ _ _ P₀ P hPP hA₀.mem (hA₀.sharp.trans hA.sharp.symm) hA₀.psi0 hA.psi0 _ y y' hy₀)
    · exact ⟨1, one_ne_zero, fun _ _ _ _ t P hP => absurd ⟨t, P, hP⟩ h0⟩
  refine ⟨C⁻¹, inv_ne_zero hC0, fun t J hJ α γ => ⟨_root_.GlobalTheory.Fam.TopLoc.standardXi a n, _root_.GlobalTheory.Fam.TopLocFac.isLocFac_xiStd_alt W hW u a hIs hTr n, fun P hP z => ?_⟩⟩
  rw [_root_.GlobalTheory.Fam.TopFrames.xiStd_eq_const_mul_locXi_alt W hW u a hIs hTr hiA n t J hJ α γ P hP C (fun e' e he' he y y' hy => hC e' e he' he t P hP y y' hy) hj z,
    ← mul_assoc, inv_mul_cancel₀ hC0, one_mul]
end GlobalTheory.Fam.TopLoc
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAtTypeTopStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_pair_identity_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 1 = B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  first | exact @_root_.GlobalTheory.Fam.TopLoc.loc_top_common_alt | exact _root_.GlobalTheory.Fam.TopLoc.loc_top_common_alt | (intros; apply _root_.GlobalTheory.Fam.TopLoc.loc_top_common_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiLevEqConstMulLocFac
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.LocLev
theorem prod_bij_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (t : W.P.T) (f : GlobalTheory.QTw.BadPr I (W.P.I.tup t) → ℂ) (g : Fin a.n → ℂ), (∀ n (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → f P = g n) → ∏ P ∈ Finset.univ.filter (fun P : GlobalTheory.QTw.BadPr I (W.P.I.tup t) => P.1 ∈ (B.primes X).vGs), f P = ∏ n, g n := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a t f g hfg
  have hv : ∀ n : Fin a.n, (a.pl n).1 ∈ (B.primes X).vGs := fun n => (hW.lev.2.1 _).1 (a.pl n).2
  refine Finset.prod_bij' (fun P hP => a.pl.symm ⟨P.1, (hW.lev.2.1 _).2 (Finset.mem_filter.1 hP).2⟩)
    (fun n _ => (⟨(a.pl n).1, Finset.mem_union.2 (Or.inl (hv n))⟩ : GlobalTheory.QTw.BadPr I (W.P.I.tup t)))
    (fun _ _ => Finset.mem_univ _) (fun n _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, hv n⟩) ?_ ?_ ?_
  · intro P hP
    apply Subtype.ext
    simp
  · intro n _
    simp
  · intro P hP
    apply hfg
    simp
theorem loc_all_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat hi n j hj
  rcases lt_trichotomy (j + 2) B.R.m with h | h | h
  · exact _root_.GlobalTheory.T.true_geometry_finite_index_alt_alt W hW u a ha hat n j hj h
  · exact _root_.GlobalTheory.T.true_geometry_finite_index_alt_alt_alt W hW u a ha hat n j hj h
  · exact _root_.GlobalTheory.T.true_geometry_row_pair_identity_alt W hW u a ha hat hi n j hj (by omega)
theorem xiLev_eq_const_mul_locFac_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξl : Fin a.n → Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, (∀ n, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) (Ξl n)) ∧ ∀ z, B.embLL (∏ P ∈ Finset.univ.filter (fun P : GlobalTheory.QTw.BadPr I (W.P.I.tup t) => P.1 ∈ (B.primes X).vGs), GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = C j * ∏ n, Ξl n z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat hi
  choose c hc hspec using fun n j hj => _root_.GlobalTheory.Fam.LocLev.loc_all_alt W hW u a ha hat hi n j hj
  refine ⟨fun j => if h : j + 1 ≤ B.R.m then ∏ n, c n j h else 1, fun j hj => ?_, ?_⟩
  · dsimp only
    rw [dite_eq_left (by omega)]
    exact Finset.prod_ne_zero_iff.2 fun n _ => hc n j _
  · intro t J hR j hj α γ
    choose Ξ hΞ hΞe using fun n => hspec n j hj t J hR α γ
    refine ⟨Ξ, hΞ, fun z => ?_⟩
    rw [map_prod, _root_.GlobalTheory.Fam.LocLev.prod_bij_alt W hW u a t _ (fun n => c n j hj * Ξ n z) (fun n P hP => hΞe n P hP z),
      Finset.prod_mul_distrib]
    dsimp only
    rw [dite_eq_left hj]
end GlobalTheory.Fam.LocLev
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiLevEqConstMulLocFacStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_pair_symmetry_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξl : Fin a.n → Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, (∀ n, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) (Ξl n)) ∧ ∀ z, B.embLL (∏ P ∈ Finset.univ.filter (fun P : GlobalTheory.QTw.BadPr I (W.P.I.tup t) => P.1 ∈ (B.primes X).vGs), GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = C j * ∏ n, Ξl n z := by
  first | exact @_root_.GlobalTheory.Fam.LocLev.xiLev_eq_const_mul_locFac_alt | exact _root_.GlobalTheory.Fam.LocLev.xiLev_eq_const_mul_locFac_alt | (intros; apply _root_.GlobalTheory.Fam.LocLev.xiLev_eq_const_mul_locFac_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumDTLevelPrime
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumDTLevelPrime
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem ratDatum_dT_levelPrime_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ eT, IsIdemSum eT ((B.primes X).vT u) → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch₀ j) (γ : J.Ch₀ (j + 1)), IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ eT (fun z => B.embLL (Formalism.L2.Col.phiT B.fields.K (J.A.p0 j α).1.1.deco.1 (J.A.p0 (j + 1) γ).1.1.deco.1 (GlobalTheory.QTw.homOf I l Z j hj z))) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hAll u a ha hTr t J hJ eT heT j hj α γ
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  have hS := ha.shape
  have hP : (fun v => v ∈ a.v.tP) = (fun v => ∃ i, v = (a.o.p i).v) := funext fun x => propext (hS.pre.tP x)
  have hPl : GlobalTheory.FinPl.Places a.o.p a.o.I (fun v => ∃ i, v = (a.o.p i).v) :=
    ⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, fun _ => Iff.rfl, fun i => (hS.pre.char i).2⟩
  have hR : GlobalTheory.FinPl.Reps (_root_.GlobalTheory.Fam.pk_z W).ψ (a.o.β j) (a.o.β (j + 1)) (a.g.x j).L (a.g.x (j + 1)).L
      (fun i => GlobalTheory.LatPair.phiOne (a.o.Q j i) (a.o.Q (j + 1) i)) a.o.I (fun v => ∃ i, v = (a.o.p i).v) (a.v.dT j) := by
    rw [← hP]; exact ⟨(ha.vis.atT j).1, hS.rep j hj⟩
  exact GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime I hAll.tr.ok hAll.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is _ _ _ _ _ hTr.pinX a.k a.ι a.o.p a.o.β a.o.Q
    hTr.std a.o.I hPl j hj α γ (a.v.dT j) hR eT heT
end GlobalTheory.Fam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumDTLevelPrimeStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_reduction_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ eT, IsIdemSum eT ((B.primes X).vT u) → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch₀ j) (γ : J.Ch₀ (j + 1)), IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ eT (fun z => B.embLL (Formalism.L2.Col.phiT B.fields.K (J.A.p0 j α).1.1.deco.1 (J.A.p0 (j + 1) γ).1.1.deco.1 (GlobalTheory.QTw.homOf I l Z j hj z))) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  first | exact @_root_.GlobalTheory.Fam.ratDatum_dT_levelPrime_alt | exact _root_.GlobalTheory.Fam.ratDatum_dT_levelPrime_alt | (intros; apply _root_.GlobalTheory.Fam.ratDatum_dT_levelPrime_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VTDisjointVGs
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VTDisjointVGs
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.DisjProof
theorem vT_disjoint_vGs_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  exact Finset.disjoint_left.2 fun P h1 h2 =>
    Formalism.L2.Col.piT_notMem_vGs hPr u ⟨P, h2⟩ ((Formalism.L2.Col.mem_divs hT0 P).1 h1)
end GlobalTheory.Mem.Col2.DisjProof
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VTDisjointVGsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_primes_disjoint' : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  first | exact @_root_.GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs_alt | exact _root_.GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs_alt | (intros; apply _root_.GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumXiOffCommon
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam
theorem ratDatum_xiOff_common_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ e, IsIdemSum e ((B.primes X).vT u ∪ (B.primes X).vGs) → ∀ j (hj : j + 1 ≤ B.R.m) α γ, IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ e (fun z => C j * xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hAll u a ha haT hiA
  obtain ⟨C, hC, hloc⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_symmetry_alt W hAll u a ha haT hiA
  refine ⟨fun j => (C j)⁻¹, fun j hj => inv_ne_zero (hC j hj), ?_⟩
  intro t J hJ e he j hj α γ
  obtain ⟨Ξl, hΞl, hfac⟩ := hloc t J hJ j hj α γ
  obtain ⟨hv0, hvl, hvT⟩ := _root_.GlobalTheory.T.true_geometry_chain_descent_alt W hAll u a ha haT j hj
  have hinj : Function.Injective fun n : Fin a.n => ((a.pl n : (_root_.GlobalTheory.Fam.pk_z W).Pg) : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) :=
    fun n n' h => a.pl.injective (Subtype.ext h)
  have hmem : ∀ PP, PP ∈ (B.primes X).vGs ↔ ∃ n : Fin a.n, ((a.pl n : (_root_.GlobalTheory.Fam.pk_z W).Pg) : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) = PP := by
    intro PP
    refine Iff.trans (hAll.lev.2.1 PP).symm ⟨fun h => ⟨a.pl.symm ⟨PP, h⟩, by rw [Equiv.apply_symm_apply]⟩, ?_⟩
    rintro ⟨n, rfl⟩
    exact (a.pl n).2
  have hL : ∀ i, i ≤ B.R.m → IsSelfDualC _ (a.g.x i).L ∧
      ((a.g.x i).L : Set (Fin ((I.rec7 l Z).sp.X i).rank → (I.rec7 l Z).host.E)) = intVec _ _ :=
    fun i hi => ⟨(ha.x i hi).sd, Set.ext (haT.pinX.xs i hi).2.2⟩
  have key := GlobalTheory.T.rationalDatum_foldr_local_combinations (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ haT.pinX.std _ _ ((B.primes X).vT u) (B.primes X).vGs a.n _ hinj hmem
    (_root_.GlobalTheory.T.type_primes_disjoint' W hAll u) (fun n => (a.G n).cg j) Ξl hΞl (a.g.x j).L (a.g.x (j + 1)).L
    (hL j (by omega)).1 (hL (j + 1) hj).1 (hL j (by omega)).2 (hL (j + 1) hj).2 _ (a.g.vac j) _ hv0 hvl
    (fun e₀ he₀ => _root_.GlobalTheory.T.true_geometry_twist_reduction_alt W hAll u a ha haT t J hJ e₀ he₀ j hj (J.ι j α) (J.ι (j + 1) γ)) e he
  rw [← ha.gpin.dG j (by exact hj) _ hvT] at key
  have hCj : C j ≠ 0 := hC j (by omega)
  convert key using 2 with z
  simp only [xiOff, map_mul, hfac z]
  field_simp
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumXiOffCommonStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ e, IsIdemSum e ((B.primes X).vT u ∪ (B.primes X).vGs) → ∀ j (hj : j + 1 ≤ B.R.m) α γ, IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ e (fun z => C j * xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j))) := by
  first | exact @_root_.GlobalTheory.Fam.ratDatum_xiOff_common_alt | exact _root_.GlobalTheory.Fam.ratDatum_xiOff_common_alt | (intros; apply _root_.GlobalTheory.Fam.ratDatum_xiOff_common_alt <;> assumption)
end
end
