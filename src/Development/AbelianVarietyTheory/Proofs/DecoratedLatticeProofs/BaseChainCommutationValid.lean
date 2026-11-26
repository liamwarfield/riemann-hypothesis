module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainScalar
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainCommutationValid
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseChain

def levAt {D : D7} {T : Type} (L : LevCh D T) (t : T) : LevCh D Unit :=
  { L with xiH := fun _ => L.xiH t, xi := fun _ => L.xi t, Q := fun _ => L.Q t, xiR := fun _ => L.xiR t }

theorem levAt_is {D : D7} {T : Type} {L : LevCh D T} {t : T} (h : L.Is t) : (levAt L t).Is () :=
  { mu0 := h.mu0, eta := h.eta, xi := fun _ => h.xi t, xi_inj := fun _ _ _ => rfl, xi_base := h.xi_base,
    xi_fin := fun _ => h.xi_fin t, xi_triv := fun _ => h.xi_triv t, xi_tame := fun _ => h.xi_tame t, Pg := h.Pg,
    Q_pl := fun _ => h.Q_pl t, Q_off := fun _ => h.Q_off t,
    Q_de := fun p hp => (h.Q_de p hp).imp fun _ H _ => H t,
    Q_ram := fun _ => h.Q_ram t, chi := h.chi, xiR := fun _ => h.xiR t, βY := h.βY, βX := h.βX, βV := h.βV, βW := h.βW }

theorem chrEq_mu_base {D : D7} {T : Type} {L : LevCh D T} {t : T} (h : L.Is t) (j : Fin D.R.m) :
    ChrEq (L.mu t ((j : ℕ) + 1)) (L.C.mu0 j) := by
  have h1 := GlobalTheory.Mem.TupChar.chrEq_mul (h.mu0 j) (h.xi t)
  rw [h.xi_base, mul_one] at h1
  exact h1

end GlobalTheory.BaseChain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevTruePackOfPart
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ColTest

theorem isTypePlaces_vGs {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (h : I.Ok) :
    GlobalTheory.Core.Mi.IsTypePlaces (D := I.rec7 l Z) (B.primes X).vGs := by
  classical
  obtain ⟨L, hC, hL⟩ := GlobalTheory.LevelChoices.exists_levCh_unit (I.rec7 l Z) (TC.cf I l Z)
  have hP : L.Pg = (B.primes X).vGs := by
    ext w
    rw [hL.Pg w, hC]
    have hv : w ∈ (B.primes X).vGs ↔ (I.C.P.Div 0 w ∨ I.C.P.Div 1 w) := by
      rw [← h.pibar 0 w, ← h.pibar 1 w]
      exact @Finset.mem_union _ (_) _ _ _
    exact (hv.trans (Fin.exists_fin_two (p := fun k => I.C.P.Div k w)).symm).symm
  rw [← hP]
  exact GlobalTheory.SeeSaw.ComCols.isTypePlaces_of_levCh hL

end GlobalTheory.Fam.ColTest

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelStep
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

theorem cutG_mem_congGrp (V : HSp D) (I : Ideal (AE D)) (ε : AF D.host.F) (hε : ε * ε = ε) {g : GA D V}
    (hg : g ∈ congGrp V I) : cutG V ε hε g ∈ congGrp V I := by
  rw [mem_congGrp_iff] at hg ⊢
  intro i j
  rw [mt_cutG, cut_sub_one, Matrix.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_left _ _ (hg i j)

theorem grpAt_mono (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : grpAt V P ≤ grpAt V P' := by
  intro g hg
  rw [mem_grpAt_iff_parts] at hg ⊢
  exact fun i j => ⟨(hg i j).1, fun w hw => (hg i j).2 w fun h' => hw (h w h')⟩

theorem grpAt_inf_le (V : HSp D) (Q P R : Pl D → Prop) (h : ∀ p, Q p → ¬ P p → R p) {g : GA D V}
    (h1 : g ∈ grpAt V Q) (h2 : g ∈ grpAt V fun p => ¬ P p) : g ∈ grpAt V R := by
  rw [mem_grpAt_iff_parts] at h1 h2 ⊢
  refine fun i j => ⟨(h1 i j).1, fun w hw => ?_⟩
  by_cases hQ : Q w
  · by_cases hP : P w
    · exact (h2 i j).2 w (not_not.2 hP)
    · exact absurd (h w hQ hP) hw
  · exact (h1 i j).2 w hQ

theorem locHom_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y)
    {P : Pl D → Prop} (hP : P q.v) {g : GA D V} (hg : g ∈ grpOff V P) : GlobalTheory.LevIdx.locHom q V F g = 1 := by
  ext1
  rw [GlobalTheory.LevIdx.locHom_val, GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q hP hg, Matrix.mul_one, F.γβ]
  rfl

end GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
end

noncomputable section

end
end
