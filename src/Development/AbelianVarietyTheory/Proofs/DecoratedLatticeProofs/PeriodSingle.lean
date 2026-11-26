module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Formalism.LocalToGlobal.CarriedPlMap
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStep
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormTransportedColumnStepZeroStandard

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}

abbrev Val (B : GlobalTheory.Mem.Base) : Type := VV B.fields.K B.wts.sgTrue

abbrev Frm (I : TC B X) (a : I.ι) : Type := (mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a)).EqFun

def val {I : TC B X} {a : I.ι} (φ : Frm I a) (d : RowPt (B.primes X) B.R I.sel (I.tup a)) : Val B := φ.1 d

def IsRes {I : TC B X} {a : I.ι} (φ : Frm I a) {V : Type} (x : V) : Prop :=
  ∃ ok : (mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a)).Ok,
    HEq ((mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a)).res ok φ) x

def HasVal {I : TC B X} (l : I.Laws) (u : B.Word) {a : I.ι} (φ : Frm I a) (G : (I.per l u a).Mt) : Prop :=
  ∀ p : (I.stX a).D (), (show (I.perIn u a).Mt B.fields.emb B.embLL from G).1 () p =
    MvPolynomial.map B.embLL (val φ (toRow I.sel (I.tup a) p.1.1)).1

def latOf (I : TC B X) (a : I.ι) (y : TC.GA B (B.R.N B.R.m - 1)) : RowPt (B.primes X) B.R I.sel (I.tup a) :=
  letI := GlobalTheory.Mem.Col2.starE B
  decoOf (F := B.fields.F) (E := B.fields.E) ∅ (rowSG (B.primes X) I.sel (I.tup a)) y

def IsUni (B : GlobalTheory.Mem.Base) (y : TC.GA B (B.R.N B.R.m - 1)) : Prop := y ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N B.R.m - 1)

def pairVal (B : GlobalTheory.Mem.Base) (z : (GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m - 1)) → ℂ) (w : Val B) : ℂ :=
  pairB B.wts.sgTrue (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf B.wts.sgTrue)
    (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) z) (MvPolynomial.map B.embLL w.1)

variable {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

def RecVal (u : B.Word) (a : (I.rec7 l Z).what₂.Tup) (φ : Frm I a) (G : (I.rec7 l Z).what₂.Amb a) : Prop :=
  (∀ h : a = (I.rec7 l Z).what₂.mu0, HasVal (a := I.mu0) l u (Eq.rec (motive := fun (ν : (I.rec7 l Z).what₂.Tup) _ => Frm I ν) φ h)
    (((I.rec7 l Z).eMt u).symm (Eq.rec (motive := fun ν _ => (I.rec7 l Z).what₂.Amb ν) G h))) ∧
  HasVal l u φ (((I.rec7 l Z).eMtTw u a).symm G)

variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex)

end GlobalTheory.TopVal

end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem period_single (l : I.Laws) (u : B.Word) (a : I.ι) (φ : Frm I a) (G : (I.per l u a).Mt) (hG : HasVal l u φ G)
    (c : (I.stX a).Cl) (z : (GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m - 1)) → ℂ) (w : (I.per l u a).Wrow)
    (hw : w c = z) (hw' : ∀ c', c' ≠ c → w c' = 0) :
    (Nat.card ((I.stX a).Stab c) : ℂ) * (I.per l u a).period w G =
      pairVal B z (val φ (toRow I.sel (I.tup a) ((I.stX a).rep c).1.1)) := by
  letI := (I.perIn u a).clFin (l.per u a)
  have e : (I.per l u a).period w G = ∑ c' : (I.perIn u a).S'.Cl, (I.perIn u a).wt c' * pairB (K := ℂ) (I.perIn u a).sgT
      (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT)
        (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (w c')) ((I.perIn u a).rd B.fields.emb B.embLL G c') := by
    show ((∑ c' : (I.perIn u a).S'.Cl, _ : _ →ₗ[ℂ] _ →ₗ[ℂ] ℂ) w) G = _
    rw [LinearMap.sum_apply, LinearMap.sum_apply]
    rfl
  rw [e, Finset.sum_eq_single (show (I.perIn u a).S'.Cl from c)]
  · have hs : (I.perIn u a).sgT = B.wts.sgTrue := rfl
    have h1 : (I.perIn u a).rd B.fields.emb B.embLL G c =
        MvPolynomial.map B.embLL (val φ (toRow I.sel (I.tup a) ((I.stX a).rep c).1.1)).1 := hG _
    haveI : Finite ((I.stX a).Stab c) := (l.per u a).step.fin_stab c.1 _
    have h2 : (Nat.card ((I.stX a).Stab c) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have h3 : (Nat.card ((I.stX a).Stab c) : ℂ) * (I.perIn u a).wt c = 1 := mul_inv_cancel₀ h2
    rw [← mul_assoc]
    refine (congrArg (· * _) h3).trans ((one_mul _).trans ?_)
    subst hw
    exact congrArg _ h1
  · intro c' _ hc
    rw [hw' c' hc, map_zero, map_zero, LinearMap.zero_apply, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex)


end GlobalTheory.TopVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankConditionAllMembers
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.MemberCount

theorem rankMu_of_cols (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D) (hDu : StandardLattice.FactDuStar D)
    (u : D.what₂.Word) : GlobalTheory.Core.Rk.RankMu D u := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  have hr := h4 (GlobalTheory.first_type_prime_large_of_record D) (Formalism.MainNotions.Ext.Lw.splitsF_g_all D) u
    (Formalism.MainNotions.Ext.Lw.splitsF_T_all D u) (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
  have hfin : Module.finrank ℂ (D.s.Cu u) = Module.finrank ℂ (D.mem u).A.Mu0 := (D.s_Cu u).finrank_eq
  unfold GlobalTheory.Core.Rk.RankMu GlobalTheory.Core.Rk.d0
  rw [hfin, hDu u]
  exact hr

end GlobalTheory.Fam.MemberCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

variable {D : D7}

theorem rank_Yc_le_succ (j : ℕ) : (Yc D j).rank ≤ (Yc D (j + 1)).rank := by
  rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.Y_rank _ (min_le_right _ _)]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_min_right D.R.m (Nat.le_succ j))) _

end GlobalTheory.BaseChain

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterMatchesWitness
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem twistedAdelicData_characters_eq_frame (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) (j : Fin B.R.m) :
    Formalism.IndefR.Links.ChrEq (D := (w.st Z).toD7) (a.x.R.mu0 ((j : ℕ) + 1)) (w.I.C.mu0 j) := by
  have h1 : a.x.R.C = Fr.at (w.st Z) f := eq_of_heq (R3.twArgs_lev K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a).1
  have h2 := a.x.pins.char.base.lev.mu0 j
  have h3 : a.x.R.C.mu0 j = w.I.C.mu0 j :=
    (congrArg (fun C => C.mu0 j) h1).trans (congrArg (fun g : Fr B.toPre => g.mu0 j) w.C_eq).symm
  exact h3 ▸ h2

end GlobalTheory.Fam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDataOfWitness
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LinkedPins


set_option maxHeartbeats 4000000 in
theorem seeAt_twArgs {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf (w.st Z).toD7) (s : Formalism.L2.Theta.GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0))
    (hs : SeeAt (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 X h s) : SeeAt a.x.R.toRealDat a.x.F.lv2 X h s := by
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  refine ⟨hs.fin, ?_, ?_⟩
  · exact (hs.conj)
  · exact (hs.mat)

theorem setting_congr {D : D7} (M : ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Prop)
    {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (e : F0 = F0') {P : SPack D F0} {P' : SPack D F0'} (hP : HEq P P')
    (h : M P'.X P'.inst) : M P.X P.inst := by
  subst e
  cases hP
  exact h



open Classical in
theorem image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {Pr : Formalism.L2.Col.Primes X} {Pr' : Formalism.L2.Col.Primes X'} (hP : HEq Pr Pr') :
    Pr.vGs.image (Formalism.L2.Host.CT.plMap s.iE) = Pr'.vGs.image (Formalism.L2.Host.CT.plMap s'.iE) := by
  subst hX
  cases hs
  cases hP
  rfl


open Classical in
theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  have h : Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id := by
    funext P
    ext x
    exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x
  rw [h, Finset.image_id]

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}


end GlobalTheory.Fam.LinkedPins
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeOpen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd.OffTwist


set_option maxHeartbeats 1000000 in
theorem bc_prV_eq_one (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (κ : GA D S)
    (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hg : GlobalTheory.AdForm.finM S hn κ = g.1) (v w : HeightOneSpectrum (𝓞 D.host.F)) (hw : w ≠ v)
    (hκ : κ ∈ GlobalTheory.FinPl.grpAt S (· = v)) : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g = 1 := by
  subst hn
  have h1 : GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ = 1 :=
    ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff S _ κ).1 hκ).2 w hw
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram w κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ)).val i j =
        GlobalTheory.StabConjIndex.swap w ((GlobalTheory.AdelicU.matHom (Fv D.host.F w) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV w (g.1 i j) = GlobalTheory.StabConjIndex.swap w (GlobalTheory.AdelicU.compFin _ _ w _)
    rw [← hij]
    exact GlobalTheory.FamTrace.prV_toEAf_eq_swap D w _
  rw [hE, h1, map_one]


set_option maxHeartbeats 1000000 in
theorem exists_mem_level (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (K : StepLevel D.host.F D.host.E (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) T f bad)
    (t : 𝓞 D.host.E) (ht : t ∣ (T : 𝓞 D.host.E))
    (hLb : ∀ x, x ∈ K.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r))
    (L : GlobalTheory.FinPl.Lat S) (hfg : L.FG) (hL : ∀ x, x ∈ L ↔ ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hb : v ∉ bad) (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal)
    (κ : GA D S) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S (· = v)) (hm : GlobalTheory.FinPl.Moves S κ L L (· = v)) :
    ∃ x : K.U, x.1.1 = GlobalTheory.AdForm.finM S hn κ := by
  obtain ⟨g, hgU, hg⟩ : ∃ g ∈ Formalism.UG.UPts (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM S hn κ = g.1 := by
    obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D S n hn
    have hf := GlobalTheory.FinPl.SetCut.grpAt_le_GfC S _ hκ
    exact ⟨(e ⟨κ, hf⟩).1, (e ⟨κ, hf⟩).2, (he ⟨κ, hf⟩).symm⟩
  refine ⟨⟨g, (K.U_eq _).2 ⟨hgU, fun w => ?_⟩⟩, hg.symm⟩
  by_cases hw : w = v
  · subst hw
    subst hn
    have key : ∀ j i : Fin S.rank, ∃ r : 𝓞 D.host.E,
        (Pi.single j (T : D.host.E) : Fin S.rank → D.host.E) i = (r : D.host.E) ∧ t ∣ r := fun j i => by
      rw [Pi.single_apply]
      split_ifs
      · exact ⟨T, (map_natCast (algebraMap (𝓞 D.host.E) D.host.E) T).symm, ht⟩
      · exact ⟨0, rfl, dvd_zero _⟩
    have e := GlobalTheory.FamTrace.levelVL_eq_of_std (sigD D) (S.gram.reindex (finCongr rfl) (finCongr rfl)) (Lb := K.Lb) (Λ := L) hT
      (fun x hx j => let ⟨r, hr, _⟩ := (hLb x).1 hx j; ⟨r, hr⟩)
      (fun j => (hLb _).2 fun i => let ⟨r, hr, hd⟩ := key j i; ⟨r, hr, fun _ => hd⟩)
      (fun x hx => (hL x).1 hx) (fun j => (hL _).2 fun i => let ⟨r, hr, _⟩ := key j i; ⟨r, hr⟩)
    rw [K.Uloc_hyp w hb hT, e]
    exact GlobalTheory.FamTrace.bc_prV_mem_levelVL_of_moves D S _ rfl L L hfg (fun _ => Iff.rfl) κ g hg w hm
  · rw [bc_prV_eq_one D S n hn κ g hg v w hw hκ]
    exact one_mem _


end GlobalTheory.LevProd.OffTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembers
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnStabilizerTrivialLocal
section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TypePrimesOfLevel
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


end Generic

variable (D : D7)


def TypePrimesLarge : Prop := ∀ i, 2 * D.R.f * D.R.k + 1 < D.host.g i

end GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers

end
end

noncomputable section

namespace GlobalTheory.Proof.ColumnStabilizerTrivialLocal

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n n' : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem typePrimesLarge_iff (D : D7) :
    UnipotentLevelStabilisers.TypePrimesLarge D ↔ ∀ i, 2 * D.R.f * D.R.k < D.host.g i - 1 :=
  forall_congr' fun i => by omega

theorem gBig_of_large (h : UnipotentLevelStabilisers.TypePrimesLarge D) : Formalism.MainNotions.StandardLattice.GBig D :=
  ⟨0, (typePrimesLarge_iff D).mp h 0⟩

variable {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)

end GlobalTheory.Proof.ColumnStabilizerTrivialLocal
end
end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemberRanks

theorem typePrimesLarge_of_val {C} {cD ch : ℝ} {D : D7} (L : SizeData₂ D) (hv : Val C cD ch L) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers.TypePrimesLarge D := by
  intro i
  have h1 : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) := (hv.host.2.2.2.2.1 i).1
  have hb : 1 ≤ L.sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _)
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h2 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 :=
    pow_le_pow_left₀ hk0 (le_mul_of_one_le_right hk0 hb) 8
  have h3 : D.R.k ^ 8 ≤ D.host.g i := by exact_mod_cast h2.trans h1
  have hf : D.R.f ≤ D.R.k := D.R.f_le_k
  have hk : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have h4 : D.R.k ^ 3 ≤ D.R.k ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h5 : 2 * D.R.f * D.R.k + 1 < D.R.k ^ 3 := by
    have : D.R.f * D.R.k ≤ D.R.k * D.R.k := Nat.mul_le_mul_right _ hf
    have h6 : 5 * (D.R.k * D.R.k) ≤ D.R.k ^ 3 := by
      rw [pow_succ, pow_two, mul_comm 5]; exact Nat.mul_le_mul_left _ hk
    have h7 : 25 ≤ D.R.k * D.R.k := Nat.mul_le_mul hk hk
    rw [mul_assoc]; omega
  omega

theorem dstar_mass (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    X.toD7.what₂.Dstar =
      StandardLattice.DstarP X.toD7 (X.toD7.host.g 0) (X.toD7.host.g 1) (StandardLattice.massI X.toD7 X.toD7.R.r) X.toD7.dsig := by
  have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
  rw [e, hO.sizes.2]
  unfold DsPre StandardLattice.DstarP
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

theorem columnRowRanks_admissible_of_massFormula (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D)
    (hD : D.what₂.Dstar = StandardLattice.DstarP D (D.host.g 0) (D.host.g 1) (StandardLattice.massI D D.R.r) D.dsig)
    (hG : StandardLattice.GBig D) (hT : ∀ u, Formalism.MainNotions.S.SplitsE D (D.mem u).A.T) : LocalBesselAndTopKernel.FamilyMidVolume D := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  intro V _ _ _ _ h L _
  refine ⟨fun hL u => ?_, fun hL => ?_⟩
  · have e := h4 hG (Formalism.MainNotions.J.splitsF_g D) u (Formalism.MainNotions.J.splitsF_of_splitsE D _ (D.mem u).A.T_prime (hT u))
      (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
    have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.k := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.k)
    rw [em, ← Formalism.MainNotions.J.idxColTie_holds D]
    exact e
  · have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.r := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.r)
    rw [em, ← Formalism.MainNotions.J.idxRowTie_holds D, hD]
    rfl

end GlobalTheory.MemberRanks
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd

theorem locHom_eq_one_of_grpAt' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y)
    {P : GlobalTheory.FinPl.Pl D → Prop} (hP : ¬ P q.v) {x : GA D S} (hx : x ∈ GlobalTheory.FinPl.grpAt S P) :
    GlobalTheory.LevIdx.locHom q S F x = 1 := by
  have h1 : x ∈ GlobalTheory.FinPl.grpOff S (· = q.v) :=
    GlobalTheory.FinPl.SetCut.grpAt_le_grpOff S P (· = q.v) (fun p hp e => hP (e ▸ hp)) hx
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1
  symm
  rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
  simp [F.βγ]

end GlobalTheory.LevProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LargeGapAllMembers
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.GapAt

theorem poly_bound {M k m f r L T n t N : ℝ} (hM : 1 ≤ M) (hk1 : 1 ≤ k) (hk : k ≤ M) (hm1 : 1 ≤ m) (hm : m ≤ M)
    (hf0 : 0 ≤ f) (hf : f ≤ M) (hr0 : 0 ≤ r) (hr : r ≤ M) (hL0 : 0 ≤ L) (hL : L ≤ M) (hT : T ≤ M) (hn0 : 0 ≤ n)
    (hn : n ≤ 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) + 8) (ht0 : 0 ≤ t) (ht : t ≤ 8 * f * r + 4 + T * n)
    (hN : N = k + m * (t + 1)) : 4 * N ^ 3 + 2 * t + 6 ≤ 300000 * M ^ 30 := by
  have hM0 : 0 ≤ M := by linarith
  have hk' : 0 ≤ k - 1 := by linarith
  have hk'' : k - 1 ≤ M := by linarith
  have pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b := fun a b h => pow_le_pow_right₀ hM h
  have h1 : f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ M ^ 7 := by
    calc f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 := div_le_self (by positivity) hm1
      _ ≤ M ^ 2 * M ^ 3 * M ^ 2 := by gcongr
      _ = M ^ 7 := by ring
  have h10 : 0 ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m := by
    have : 0 ≤ m := by linarith
    positivity
  have h2 : n ≤ 28 * M ^ 8 := by
    have a1 : f ≤ M ^ 7 := by have := pw 1 7 (by norm_num); rw [pow_one] at this; linarith
    have a2 : r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) ≤ M * (2 * M ^ 7) :=
      mul_le_mul hr (by linarith) (by linarith) hM0
    have a3 : M * (2 * M ^ 7) = 2 * M ^ 8 := by ring
    have a4 := pw 0 8 (by norm_num)
    rw [pow_zero] at a4
    rw [mul_assoc] at hn
    linarith
  have h3 : t ≤ 40 * M ^ 9 := by
    have a1 : f * r ≤ M * M := mul_le_mul hf hr hr0 hM0
    have a2 : T * n ≤ M * (28 * M ^ 8) := mul_le_mul hT h2 hn0 hM0
    have a3 : M * (28 * M ^ 8) = 28 * M ^ 9 := by ring
    have a4 := pw 0 9 (by norm_num)
    have a5 := pw 2 9 (by norm_num)
    rw [pow_zero] at a4
    rw [pow_two] at a5
    rw [mul_assoc] at ht
    linarith
  have h4 : N ≤ 42 * M ^ 10 := by
    have a4 := pw 0 9 (by norm_num)
    rw [pow_zero] at a4
    have a1 : m * (t + 1) ≤ M * (41 * M ^ 9) := mul_le_mul hm (by linarith) (by linarith) hM0
    have a3 : M * (41 * M ^ 9) = 41 * M ^ 10 := by ring
    have a5 := pw 1 10 (by norm_num)
    rw [pow_one] at a5
    linarith
  have hN0 : 0 ≤ N := by
    rw [hN]
    have : 0 ≤ m * (t + 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have h5 : N ^ 3 ≤ 74088 * M ^ 30 := by
    calc N ^ 3 ≤ (42 * M ^ 10) ^ 3 := pow_le_pow_left₀ hN0 h4 3
      _ = 74088 * M ^ 30 := by ring
  have a4 := pw 0 30 (by norm_num)
  have a5 := pw 9 30 (by norm_num)
  rw [pow_zero] at a4
  linarith

theorem rank_bound (s : Scale) (R : Ranks) (h : RankVal s R) :
    4 * ((R.N R.m : ℕ) : ℝ) ^ 3 + 2 * R.t + 6 ≤ 300000 * (4 * s.x ^ (377 : ℝ)) ^ 30 := by
  obtain ⟨-, -, ⟨-, hk⟩, ht⟩ := h
  have hx := s.one_lt_alt.le
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hY : 1 ≤ s.x ^ (377 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hk2 : (R.k : ℝ) ≤ 2 * s.x ^ (377 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hx (show 9 / 2 + 10 * s.eps ≤ (377 : ℝ) by linarith)
    linarith
  have hL : s.L ≤ s.x ^ (377 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (show s.eps ≤ (377 : ℝ) by linarith)
  have hL0 : 0 ≤ s.L := Real.rpow_nonneg (by linarith) _
  have n1 := R.two_le_m
  have n2 := R.m_add_three_le_k
  have hm1 : (1 : ℝ) ≤ R.m := by exact_mod_cast (show 1 ≤ R.m by omega)
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (show 1 ≤ R.k by omega)
  have hmk : (R.m : ℝ) ≤ R.k := by exact_mod_cast (show R.m ≤ R.k by omega)
  have hfk : (R.f : ℝ) ≤ R.k := by exact_mod_cast (show R.f ≤ R.k from R.f_le_k)
  have hrk : (R.r : ℝ) ≤ 2 * R.k := by
    exact_mod_cast (show R.r ≤ 2 * R.k by unfold Ranks.r; omega)
  have hT : (TOv s : ℝ) ≤ 4 * s.x ^ (377 : ℝ) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ s.x ^ (377 : ℝ) by linarith)
    unfold TOv
    linarith
  have hn : (nWv R s : ℝ) ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) + 8 := by
    have hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    have := Nat.ceil_lt_add_one
      (show 0 ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 by positivity)
    unfold nWv
    push_cast
    linarith
  have ht' : (R.t : ℝ) ≤ 8 * (R.f : ℝ) * R.r + 4 + (TOv s : ℝ) * nWv R s := by
    exact_mod_cast (show R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s by omega)
  refine poly_bound (by linarith) hk1 (by linarith) hm1 (by linarith) (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _)
    (by linarith) hL0 (by linarith) hT (Nat.cast_nonneg _) hn (Nat.cast_nonneg _) ht' ?_
  unfold Ranks.N
  push_cast
  rfl

theorem nodeGap_of_val {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) : D.NodeGap (h0v L.sc ch : ℝ) := by
  intro u τ j hj
  obtain ⟨b1, hb, -⟩ := h.hc.2.2.1
  rw [D.hcW_b u τ, (hb τ _).1, (hb τ _).1]
  push_cast
  exact le_of_eq (by ring)

theorem bigGap_of_val {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) (hch : 11311 ≤ ch)
    (hx : 300000 * 4 ^ 30 ≤ L.sc.x) : BigGap D := by
  refine (nodeGap_of_val h).mono ((rank_bound L.sc D.R h.ranks).trans ?_)
  have h1 := L.sc.one_lt_alt
  have h0 : 0 < L.sc.x := by linarith
  have e1 : (L.sc.x ^ (377 : ℝ)) ^ 30 = L.sc.x ^ (11310 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; norm_num
  have e2 : L.sc.x * L.sc.x ^ (11310 : ℝ) ≤ L.sc.x ^ ch := by
    rw [mul_comm, ← Real.rpow_add_one h0.ne']
    exact Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
  have e3 : 0 ≤ L.sc.x ^ (11310 : ℝ) := Real.rpow_nonneg h0.le _
  have e4 := mul_le_mul_of_nonneg_right hx e3
  have e5 := Nat.le_ceil (L.sc.x ^ ch)
  have e6 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
  rw [mul_pow, e1, ← mul_assoc]
  unfold h0v
  push_cast
  linarith

end GlobalTheory.Core.Rk.GapAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartQuot

open GlobalTheory.FinPl GlobalTheory.FinPlLoc ValuativeRel

variable {D : D7}

theorem chrEq_div {a c : (AE D)ˣ →* Circle} {α γ : Formalism.L2.Host.HChar D.host.E} (ha : ChrEq a α) (hc : ChrEq c γ) :
    ChrEq (a * c⁻¹) (α * γ⁻¹) := by
  refine ⟨⟨ha.1.1.mul hc.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha.1.2, hc.1.2, inv_one, one_mul]
  · show ((a x * (c x)⁻¹ : Circle) : ℂ) = ((α.locK P k * (γ.locK P k)⁻¹ : ℂˣ) : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv, ha.2 P e he k x hx, hc.2 P e he k x hx,
      Units.val_mul, Units.val_inv_eq_inv_val]

theorem quot_triv {a c : (AE D)ˣ →* Circle} {α γ ξ : Formalism.L2.Host.HChar D.host.E} (ha : ChrEq a (α * ξ)) (hc : ChrEq c (γ * ξ))
    (hα : α.TrivOn D.host.F) (hγ : γ.TrivOn D.host.F) (b : (AF D.host.F)ˣ) : (a * c⁻¹) (idF D b) = 1 := by
  have h := chrEq_div ha hc
  rw [_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel_right] at h
  exact GlobalTheory.GridWeil.triv_base h (hα.mul hγ.inv) b

theorem eq_of_finM {V : HSp D} {n : ℕ} (hn : V.rank = n) {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V)
    (h : finM V hn g = finM V hn g') : g = g' := by
  subst hn
  have e0 : ∀ g : GA D V, finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := fun g => by simp [finM]
  rw [e0, e0] at h
  apply mt_inj
  ext i j
  have h1 : infPart D (Formalism.L2.Theta.mt V g i j) = infPart D (Formalism.L2.Theta.mt V g' i j) := by
    have a : infHom V g = infHom V g' := (show infHom V g = 1 from hg).trans (show infHom V g' = 1 from hg').symm
    exact congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => z.1 i j) a
  have h2 : finPart D (Formalism.L2.Theta.mt V g i j) = finPart D (Formalism.L2.Theta.mt V g' i j) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (congrFun (congrFun h i) j)
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · rw [RingHom.map_sub, h1, sub_self]
  · intro w
    rw [RingHom.map_sub]
    unfold GlobalTheory.FinPl.compAt
    rw [RingHom.comp_apply, RingHom.comp_apply, h2, sub_self]

section Pt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem sum_parts : infPart D (p.e + cA D p.e) = 0 ∧
    ∀ w, compAt D w (p.e + cA D p.e) = if w = p.v then 1 else 0 := by
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, he⟩ := p.above
  rw [he]
  change infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 ∧
    ∀ w, compAt D w (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _
  refine ⟨infPart_pair _ _, fun w => ?_⟩
  rw [compAt_pair]
  split_ifs with hw
  · rw [hw, h1]; rfl
  · rw [h0 w hw, TensorProduct.zero_tmul]

theorem idele_off {R : Type} [CommRing R] (φ : AE D →+* R) (h : φ (p.e + cA D p.e) = 0) (a : kˣ) :
    φ (p.idele a : AE D) = 1 ∧ φ (cA D (p.idele a : AE D)) = 1 := by
  have e1 := p.split.1
  have e2 := p.split.2.1
  have e3 : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, e1]
  have f1 : φ p.e = 0 := by
    have : p.e = p.e * (p.e + cA D p.e) := by rw [mul_add, e1, e2, add_zero]
    rw [this, map_mul, h, mul_zero]
  have f2 : φ (cA D p.e) = 0 := by
    rw [map_add (f := _), f1, zero_add] at h; exact h
  have s : p.sec a = p.e * p.sec a := by rw [← p.sec_pr, p.pr_sec]
  rw [p.idele_val, s]
  simp only [map_add (f := _), map_sub, map_mul, map_one, f1, f2]
  simp

theorem idele_on {R : Type} [CommRing R] (φ : AE D →+* R) (h : φ (p.e + cA D p.e) = 1) (a : kˣ) (δ : AE D)
    (hδ : cA D δ * δ = 1) (ha : p.pr δ = a) :
    φ (p.idele a : AE D) = φ δ * φ (cA D (p.idele a : AE D)) := by
  have s : p.sec a = p.e * δ := by rw [← ha, p.sec_pr]
  rw [p.idele_val, s]
  have h2 := congrArg φ hδ
  simp only [map_add (f := _), map_sub, map_mul, map_one] at h h2 ⊢
  linear_combination (φ δ - 1) * h - φ (cA D p.e) * h2

end Pt

theorem det_sub_one_mem {V : HSp D} {I : Ideal (AE D)} {h : GA D V} (hh : h ∈ congGrp V I) :
    (Formalism.L2.Theta.mt V h).det - 1 ∈ I := by
  rw [mem_congGrp] at hh
  rw [← Ideal.Quotient.eq, map_one, RingHom.map_det]
  have : (Ideal.Quotient.mk I).mapMatrix (Formalism.L2.Theta.mt V h) = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq]
    exact hh i j
  rw [this, map_one, Matrix.det_one]


set_option maxHeartbeats 1000000 in
theorem isDetRoot_prod {ι : Type} [Fintype ι] {k : ι → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (p : ∀ i, SplitPt D (k i))
    (hp : Function.Injective fun i => (p i).v) {V : HSp D} {h : GA D V} (hh : h ∈ grpAt V fun w => ∃ i, (p i).v = w)
    (d : ∀ i, (k i)ˣ) (hd : ∀ i, (p i).pr (Formalism.L2.Theta.mt V h).det = d i) :
    IsDetRoot V h (∏ i, (p i).idele (d i)) := by
  have hδ := det_sub_one_mem hh
  have hn := Formalism.L2.Theta.det_conj_mul V h
  show _ = (Formalism.L2.Theta.mt V h).det * cA D _
  have off : ∀ {R : Type} [CommRing R] (φ : AE D →+* R), (∀ i, φ ((p i).e + cA D (p i).e) = 0) →
      φ ((Formalism.L2.Theta.mt V h).det - 1) = 0 →
      φ (((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D) - (Formalism.L2.Theta.mt V h).det * cA D ((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D)) = 0 := by
    intro R _ φ h1 h2
    rw [map_sub, map_one, sub_eq_zero] at h2
    rw [Units.coe_prod, map_sub, map_mul, map_prod, map_prod, map_prod, h2,
      Finset.prod_eq_one fun i _ => (idele_off (p i) φ (h1 i) (d i)).1,
      Finset.prod_eq_one fun i _ => (idele_off (p i) φ (h1 i) (d i)).2, mul_one, sub_self]
  have on : ∀ {R : Type} [CommRing R] (φ : AE D →+* R) (i : ι), (∀ j, j ≠ i → φ ((p j).e + cA D (p j).e) = 0) →
      φ ((p i).e + cA D (p i).e) = 1 →
      φ (((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D) - (Formalism.L2.Theta.mt V h).det * cA D ((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D)) = 0 := by
    intro R _ φ i o h1
    rw [Units.coe_prod, map_sub, map_mul, map_prod, map_prod, map_prod,
      Finset.prod_eq_single i (fun j _ hj => (idele_off (p j) _ (o j hj) (d j)).1) (fun h => absurd (Finset.mem_univ i) h),
      Finset.prod_eq_single i (fun j _ hj => (idele_off (p j) _ (o j hj) (d j)).2) (fun h => absurd (Finset.mem_univ i) h), sub_eq_zero]
    exact idele_on (p i) _ h1 _ _ hn (hd i)
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · exact off (infPart D) (fun i => (sum_parts (p i)).1) (infPart_of_idAt hδ)
  · intro w
    by_cases hw : ∃ i, (p i).v = w
    · obtain ⟨i, rfl⟩ := hw
      refine on (compAt D (p i).v) i (fun j hj => ?_) ?_
      · rw [(sum_parts (p j)).2, if_neg fun e => hj (hp e).symm]
      · rw [(sum_parts (p i)).2, if_pos rfl]
    · refine off (compAt D w) (fun i => ?_) (compAt_of_idAt hδ hw)
      rw [(sum_parts (p i)).2, if_neg fun e => hw ⟨i, e.symm⟩]

theorem exists_unit_det {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (g : GL (Y ⊕ Fin 0) k)
    (hg : g ∈ GlobalTheory.SplitWeil.KO k (Y ⊕ Fin 0)) :
    ∃ d : kˣ, valuation k (d : k) = 1 ∧ (F.β * g.val.toBlocks₁₁ * F.γ).det = d := by
  refine ⟨Matrix.GeneralLinearGroup.det g, ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := hg
    have e : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀) : kˣ) : k) =
        algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g₀ : 𝒪[k]ˣ) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
      rfl
    rw [e]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  · rw [Matrix.det_conj_of_mul_eq_one F.βγ F.γβ, Matrix.GeneralLinearGroup.val_det_apply,
      ← Matrix.det_submatrix_equiv_self (Equiv.sumEmpty Y (Fin 0)).symm]
    rfl

theorem chr_eq_of_root {χ : (AE D)ˣ →* Circle} (hF : ∀ a, χ (idF D a) = 1) {V : HSp D} {g : GA D V} {x x' : (AE D)ˣ}
    (h : IsDetRoot V g x) (h' : IsDetRoot V g x') : χ x = χ x' := by
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g _ _ h h'
  rw [ha, map_mul, hF, mul_one]

theorem chr_eq_of_root_mul {χ : (AE D)ˣ →* Circle} (hF : ∀ a, χ (idF D a) = 1) {V : HSp D} {g h : GA D V} {x y z : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hy : IsDetRoot V h y) (h1 : χ y = 1) (hz : IsDetRoot V (g * h) z) : χ z = χ x := by
  rw [chr_eq_of_root hF hz ((GlobalTheory.Member.isDetRoot_laws D V).2.2.2 _ _ _ _ hx hy), map_mul, h1, mul_one]

theorem eq_on_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    {c c' : (AE D)ˣ →* Circle} {η η' δ : kˣ →* ℂˣ} (h : (ofSplit p).IsComp c⁻¹ (η * δ)) (h' : (ofSplit p).IsComp c'⁻¹ (η' * δ))
    (hη : GlobalTheory.SplitWeil.IsUnram η) (hη' : GlobalTheory.SplitWeil.IsUnram η') (d : kˣ) (hd : valuation k (d : k) = 1) :
    c (p.idele d) = c' (p.idele d) := by
  have e : (p.idele d : AE D) = (ofSplit p).ι d + (1 - (ofSplit p).e) := by
    rw [p.idele_val, add_comm]; rfl
  have a := h d _ e
  have a' := h' d _ e
  rw [MonoidHom.mul_apply, hη d hd] at a
  rw [MonoidHom.mul_apply, hη' d hd, a] at a'
  have := Circle.ext a'
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply] at this
  exact inv_injective this

theorem det_cast (n n' : ℕ) (e : n = n') (h : GA D (D.sp.X n')) :
    (Formalism.L2.Theta.mt _ (e ▸ h : GA D (D.sp.X n))).det = (Formalism.L2.Theta.mt _ h).det := by
  subst e; rfl


end GlobalTheory.ChartQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam

theorem conv_single_one_of_forall {G : Type} [Monoid G] (l : List (G →₀ ℂ))
    (h : ∀ x ∈ l, x = Finsupp.single 1 1) : GlobalTheory.QPl.conv l = Finsupp.single 1 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : x = Finsupp.single 1 1 := h x (by simp)
    have hl := ih (fun y hy => h y (by simp [hy]))
    show List.foldr _ _ (x :: l) = _
    simp only [List.foldr_cons]
    change (x.sum fun g a => (GlobalTheory.QPl.conv l).sum fun h b => Finsupp.single (g * h) (a * b)) = _
    rw [hx, hl, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
    simp

end GlobalTheory.Fam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeStepValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd

theorem locHom_eq_one_of_grpAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y)
    {P : GlobalTheory.FinPl.Pl D → Prop} (hP : ¬ P q.v) {x : GA D S} (hx : x ∈ GlobalTheory.FinPl.grpAt S P) :
    GlobalTheory.LevIdx.locHom q S F x = 1 := by
  exact @_root_.GlobalTheory.LevProd.locHom_eq_one_of_grpAt' D k _ _ _ _ Y _ _ q S F P hP x hx

end GlobalTheory.LevProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MidDat

theorem exists_o {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ o : WO S T →₀ ℂ, (∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x) ∧
      ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
        Tm Φ₁ = comb ψ S T o (Tm Φ₀) := by
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := GlobalTheory.SeeSaw.LocPlInhab.exists_latInd q FS FT hS hT
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨o, o1, fun Tm hTm a b hb ha => ?_⟩
  obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
  obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
  exact o2 Tm hTm

theorem idem_eq {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n : ℕ} (a : Fin n → AE D)
    (pl : Fin n ≃ P) (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i).1) : e = ∑ i, a i := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P, ← Equiv.sum_comp pl]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.LocMod.PinInhab.idem_unique (hes _ (pl i).2) (ha i)

theorem isThetaAt_smul {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ} {f₀ Φ f : Mx D m n → ℂ}
    {κ : ℂ} (hκ : κ ≠ 0) (h : IsThetaAt ψ B hs e Λ c f₀ (κ • Φ) f) : IsThetaAt ψ B hs e Λ c f₀ Φ (κ⁻¹ • f) := by
  obtain ⟨hex, hall⟩ := h
  refine ⟨hex, fun Tm hTm => ?_⟩
  rw [hall Tm hTm, map_smul, smul_smul, inv_mul_cancel₀ hκ, one_smul]

end GlobalTheory.MidDat
end
