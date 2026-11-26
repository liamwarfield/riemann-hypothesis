module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemSuppBarOfNe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitPeriodTranslatesMomentsFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
noncomputable section

namespace GlobalTheory.PerQ.Co

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def bP (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) : GL (Fin (B.R.N B.R.m - 1)) B.fields.E :=
  Classical.epsilon fun g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E =>
    Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) g

def bM (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) : GL (Fin (B.R.N B.R.m)) B.fields.E :=
  Classical.epsilon fun g : GL (Fin (B.R.N B.R.m)) B.fields.E =>
    (∀ x, iniH (N_m_succ B.R) ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) =
        ((bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧
      (∀ x, (I.perIn u a).tz * ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) =
        x (Br.iL (N_m_succ B.R))) ∧
      Formalism.L2.Forms.IsLocBasis (B.places.resChar w)
        (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) g

def coP (u : B.Word) (a : I.ι) (w : B.places.Pl) :
    ((I.perIn u a).S'.Cl → Fr B.fields.emb B.embLL (B.R.N B.R.m - 1) → ℂ) →ₗ[ℂ]
      ((I.perIn u a).S'.Cl → MvPolynomial (B.fields.Tau × Fin (B.R.N B.R.m - 1) × Fin (B.R.N B.R.m - 1)) ℂ) :=
  LinearMap.pi fun c =>
    actP (I.perIn u a).sgT (invTrK (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (bP I u a w c)⁻¹)) ∘ₗ
      polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) ∘ₗ
      LinearMap.proj c

def coM (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) :
    (Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ) →ₗ[ℂ]
      MvPolynomial (B.fields.Tau × Fin (B.R.N B.R.m) × Fin (B.R.N B.R.m)) ℂ :=
  actP (lamT (B.hcW u) B.R.m) (invTrK (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (bM I u a w c)⁻¹)) ∘ₗ
    polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m)) ∘ₗ
    (((I.chIn u a).S B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)).toLinearMap

end GlobalTheory.PerQ.Co

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueWeightsEqDescentShiftedWeightsInterlace
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueWeightsEqDescentShiftedWeightsInterlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ

theorem trueWeights_built : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (τ : B.fields.Tau), Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ ∧ Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = (I.perIn u a).sgT τ ∧ Br.Interlace (N_m_succ B.R) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  intro B X I _ l Z u a τ
  have hc : Formalism.MainNotions.product_first_zeroth_parts.cTw B.R = (B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
    have h2 : 2 ∣ B.R.t + 1 := B.R.t_odd.add_one.two_dvd
    unfold Formalism.MainNotions.product_first_zeroth_parts.cTw
    rw [Nat.mul_div_assoc _ h2]
    push_cast; rfl
  have key : ∀ {n : ℕ} (w : DomWeight n), Formalism.MainNotions.product_first_zeroth_parts.wSh w (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
      GlobalTheory.Mem.Col2.shW w (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) := by
    intro n w
    unfold Formalism.MainNotions.product_first_zeroth_parts.wSh GlobalTheory.Mem.Col2.shW
    congr 1
    funext i
    rw [hc]; ring
  have hs : ∀ τ, (I.perIn u a).sg τ = (RowPar.of (B.hcW u τ)).sg := fun τ =>
    congrArg RowPar.sg (B.wts_isOk.hc_row u τ).symm
  have hw := GlobalTheory.LvT.BuiltChain.weights_ok (I.perIn u a) (B.hcW u) B.fields.emb hs
  refine ⟨key _, key _, (hw τ).1, (hw τ).2, fun τ' i => ?_⟩
  obtain ⟨ha, hb⟩ := (hw τ').1 i
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, PerIn.sgT, GlobalTheory.Mem.Col2.lamT, GlobalTheory.Mem.Col2.shW] at ha hb
  constructor
  · show (B.wts.sgW τ').w i ≤ (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1, _⟩
    change 0 ≤ (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1, _⟩ + _ - ((B.wts.sgW τ').w i + _) at hb
    linarith
  · show (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1 + 1, _⟩ ≤ (B.wts.sgW τ').w i
    change 0 ≤ (B.wts.sgW τ').w i + _ - ((Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1 + 1, _⟩ + _) at ha
    linarith

end GlobalTheory.PerQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueWeightsEqDescentShiftedWeightsInterlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (τ : B.fields.Tau), Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ ∧ Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = (I.perIn u a).sgT τ ∧ Br.Interlace (N_m_succ B.R) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  exact @GlobalTheory.PerQ.trueWeights_built
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainInitialLatticeCompatibleTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainInitialLatticeCompatibleTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem valAt_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (φ : (I.stp u I.mu0 0).Cl → Fr B.fields.emb B.embLL (B.R.N 0) → ℂ)
    (b : (I.stp u I.mu0 0).β) (b' : (I.stp u a 0).β) (p : (I.stp u I.mu0 0).D b) (p' : (I.stp u a 0).D b')
    (h : p.1.1.deco = p'.1.1.deco) :
    valAt (I.stp u a 0) B.fields.emb B.embLL (fun c => φ ((I.eCls0 l u a).symm c)) b' p' =
      valAt (I.stp u I.mu0 0) B.fields.emb B.embLL φ b p := by
  have hc : I.eCls0 l u a ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p')) = (I.stp u a 0).cl b' p' :=
    (I.eCls0 l u a).apply_symm_apply _
  have hdeco : ((I.stp u a 0).rep ((I.stp u a 0).cl b' p')).1.1.deco =
      ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p'))).1.1.deco := by
    conv_lhs => rw [← hc]
    exact stepZero_corresponding_representatives_same_deco hI u a _ _
  show (I.stp u a 0).tr B.fields.emb B.embLL b' ((I.stp u a 0).mv b' p')
      (φ ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p'))) = _
  generalize (I.eCls0 l u a).symm ((I.stp u a 0).cl b' p') = c at hdeco ⊢
  obtain ⟨b₁, q⟩ := c
  obtain rfl : b = b₁ := stepZero_chartIndex_subsingleton hI _ _ _
  have hm := (I.stp u a 0).mv_smul b' p'
  have hy : ∀ N, (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) 0).ys N = {∅} := fun N => by rw [ys0]; rfl
  obtain ⟨g, g1, g2, g3⟩ := GlobalTheory.LvT.StartTie.exists_lift (y' := ysAt B.R I.sel (I.tup a) (I.cst a) 0) hy
    ((levelTypePrimes_stepZero_eq_colLev hI I.mu0 b).trans (levelTypePrimes_stepZero_eq_colLev hI a b').symm) (chartIndexLevelTwistPrimes_stepZero_eq_top hI I.mu0 b) (chartIndexLevelTwistPrimes_stepZero_eq_top hI a b')
    ((I.stp u a 0).mv b' p') ((I.stp u I.mu0 0).rep ⟨b, q⟩) p ((I.stp u a 0).rep ((I.stp u a 0).cl b' p'))
    hdeco.symm (h.trans (congrArg (fun r : (I.stp u a 0).D b' => r.1.1.deco) hm).symm)
  have h1 := valAt_eq B.fields.emb B.embLL (l.lev u I.mu0).free0 φ ⟨b, q⟩ g
  refine Eq.trans ?_ (h1.symm.trans (congrArg _ g1))
  have h2 : (I.stp u a 0).tr B.fields.emb B.embLL b' ((I.stp u a 0).mv b' p') =
      (I.stp u I.mu0 0).tr B.fields.emb B.embLL b g :=
    congrArg₂ (trFr B.fields.emb B.embLL) (congrArg (Formalism.L2.Col.ufGL B.fields.E (B.R.N 0)) g2.symm) g3.symm
  exact congrFun (congrArg DFunLike.coe h2) _

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem rep_eCls0_symm (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c' : (I.stp u a 0).Cl) :
    ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm c')).1.1.deco = ((I.stp u a 0).rep c').1.1.deco := by
  conv_rhs => rw [← (I.eCls0 l u a).apply_symm_apply c']
  exact (stepZero_corresponding_representatives_same_deco hI u a _ _).symm

theorem nm_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Nm (tw (I.tw l l0 Z) u I.mu0) 0 v φ) = Nm (tw (I.tw l l0 Z) u a) 0 v ((I.cols l).e0Tw u a φ) := by
  unfold Nm
  erw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  funext c'
  refine (valAt_eCls0 hI l u a φ _ _ _ _ ?_).symm
  exact (dia_deco _ v a').trans ((congrArg (Formalism.L2.Col.DecoSet.dia1 v a') (rep_eCls0_symm hI l u a c')).trans
    (dia_deco _ v a').symm)

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem up_deco0 (l : I.Laws) (u : B.Word) (a : I.ι) (b : (I.stp u a 0).β) (p : (I.stp u a 0).D b)
    (P : (I.atIn u a).ST) (x : Formalism.L2.Col.Sp B.fields.E (B.R.N 0)) (hx : x ∈ p.1.1.deco.1.N) (hf : p.1.1.deco.1.f P x = 1) :
    (((I.atIn u a).A 0).up b p P x).1.1.deco = p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x := by
  change (p.mv (p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x)).1.1.deco = _
  by_cases hc : (p.1.1.deco.1.up P ((I.atIn u a).T : 𝓞 B.fields.E) x).Ok
  · apply mv_deco
    have h1 := congrArg Formalism.L2.Col.Deco.N (((l.lev u a).tied 0).up_deco b p P x hx hf)
    refine Eq.trans h1 ?_
    unfold Formalism.L2.Col.DecoSet.up
    rw [dif_pos hc]
    rfl
  · have h1 : p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x = p.1.1.deco := dif_neg hc
    rw [h1]
    exact congrArg (fun q : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => q.1.1.deco) (dif_pos ⟨p.1.1.2, p.2⟩ : p.mv p.1.1.deco = _)

def onesAt {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v : Y.A.vT) (c : Y.C.cls 0) : Finset (Y.fm.lv 0 v c) :=
  Finset.univ.filter (fun x : Y.fm.lv 0 v c => Y.fm.fv 0 v c x = 1)

theorem mem_onesAt {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v : Y.A.vT) (c : Y.C.cls 0) (x : Y.fm.lv 0 v c) :
    x ∈ onesAt Y v c ↔ Y.fm.fv 0 v c x = 1 := by
  simp [onesAt]

theorem uop_apply {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v) (φ : Fn Y 0) :
    Uop Y 0 v φ = fun c => ∑ x ∈ onesAt Y v c, Y.fm.upT 0 v c x (φ (Y.fm.up 0 v c x)) := by
  funext c
  simp [Uop, LinearMap.sum_apply, onesAt]

theorem uop_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ) = Uop (tw (I.tw l l0 Z) u a) 0 v ((I.cols l).e0Tw u a φ) := by
  funext c'
  have hd := rep_eCls0_symm hI l u a c'
  have hN := congrArg (fun d : Formalism.L2.Col.DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := _) (SG := _) => d.1.N) hd
  have hF := congrArg (fun d : Formalism.L2.Col.DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := _) (SG := _) => d.1.f v) hd
  refine (show (I.cols l).e0Tw u a (Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ) c' =
    Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ ((I.eCls0 l u a).symm c') from rfl).trans ?_
  refine (congrFun (uop_apply (tw (I.tw l l0 Z) u I.mu0) v φ) _).trans
    (Eq.trans ?_ (congrFun (uop_apply (tw (I.tw l l0 Z) u a) v ((I.cols l).e0Tw u a φ)) c').symm)
  revert hd hN hF
  generalize (I.eCls0 l u a).symm c' = c
  intro hd hN hF
  refine Eq.trans ?e1 (up_match B.fields.emb B.embLL (l.lev u I.mu0).free0 ((l.lev u I.mu0).lev 0) ((l.lev u I.mu0).tied 0)
    ((l.lev u a).lev 0) ((l.lev u a).tied 0) v (onesAt (tw (I.tw l l0 Z) u I.mu0) v) ?hs c' _ ?hs' φ ((I.cols l).e0Tw u a φ) c.1 ((I.stp u I.mu0 0).rep c)
    hN hF ?hup)
  case e1 =>
    exact (valAt_rep B.fields.emb B.embLL (l.lev u I.mu0).free0 (fun c => ∑ x ∈ onesAt (tw (I.tw l l0 Z) u I.mu0) v c,
      valAt (I.stp u I.mu0 0) B.fields.emb B.embLL φ c.1 (((I.atIn u I.mu0).A 0).upPt v c x)) c).symm
  case hs => exact fun c x => mem_onesAt (tw (I.tw l l0 Z) u I.mu0) v c x
  case hs' => exact fun x => mem_onesAt (tw (I.tw l l0 Z) u a) v c' x
  case hup =>
    intro x hx h1
    refine valAt_eCls0 hI l u a φ _ _ _ _ ?_
    refine (up_deco0 l u I.mu0 _ _ v x hx h1).trans ((congrArg (fun d : Formalism.L2.Col.DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := _) (SG := _) =>
      d.up v ((I.atIn u a).T : 𝓞 B.fields.E) x) hd).trans
        (up_deco0 l u a _ _ v x (hN ▸ hx) (by rw [← congrFun hF x]; exact h1)).symm)

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem uop_mem (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) {φ : Fn (tw (I.tw l l0 Z) u a) 0} (hφ : φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0) :
    Uop (tw (I.tw l l0 Z) u a) 0 v φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0 := by
  erw [uop_apply]
  exact DiaStab.mem_Fi _ B.fields.emb B.embLL _ (l.lev u a).free0 _ fun _ => Submodule.sum_mem _ fun _ _ =>
    DiaStab.tr_mem _ B.fields.emb B.embLL _ _ _ (hφ _).1

theorem ulist_mem (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (ls : List (tw (I.tw l l0 Z) u a).A.vT) {φ : Fn (tw (I.tw l l0 Z) u a) 0} (hφ : φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0) :
    Ulist (tw (I.tw l l0 Z) u a) ls φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0 := by
  induction ls with
  | nil => exact hφ
  | cons v ls ih => exact uop_mem l l0 Z u a v ih

theorem ulist_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (ls : List (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Ulist (tw (I.tw l l0 Z) u I.mu0) ls φ) = Ulist (tw (I.tw l l0 Z) u a) ls ((I.cols l).e0Tw u a φ) := by
  induction ls with
  | nil => rfl
  | cons v ls ih => exact (uop_eCls0 hI l l0 Z u a v _).trans (congrArg (Uop (tw (I.tw l l0 Z) u a) 0 v) ih)

theorem step0Tie_trueCols : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), Step0Tie (I.tw l l0 Z) u a := by
  intro B X I hI l l0 Z u a w _
  refine ⟨rfl, fun x hx => ?_⟩
  refine nlam_map (X := tw (I.tw l l0 Z) u I.mu0) (Y := tw (I.tw l l0 Z) u a)
    (e := (I.cols l).e0Tw u a) (eL := (I.tw l l0 Z).e0 u a) w rfl ((I.tw l l0 Z).embed_mul_block_embedding u a)
    (fun x hx => ((I.tw l l0 Z).twist_preserves_base_lattice u a x).1 hx) (fun v => ⟨v, fun φ _ => nm_eCls0 hI l l0 Z u a v φ⟩) rfl
    (fun φ hφ => ulist_mem l l0 Z u I.mu0 _ hφ) (fun φ _ => ulist_eCls0 hI l l0 Z u a _ φ) hx

end GlobalTheory.LvT.TrueStep0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainInitialLatticeCompatibleTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedChain_initialLattice_compatible_trueColumns : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), Step0Tie (I.tw l l0 Z) u a := by
  first | exact @GlobalTheory.LvT.TrueStep0.step0Tie_trueCols | exact GlobalTheory.LvT.TrueStep0.step0Tie_trueCols | (intros; apply GlobalTheory.LvT.TrueStep0.step0Tie_trueCols <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelEqPointKernelAtRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelEqPointKernelAtRepresentatives
noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
open _root_.Formalism.L2.Col

attribute [local instance] GlobalTheory.Mem.Col2.starE

instance datNumberField {B : Base} {X : PreX B.toPre} (I : TC B X)
    (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    @NumberField (dat I l Z u a).E (dat I l Z u a).fE :=
  (dat I l Z u a).nE

theorem kmap_dat : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c') F) := by
  intro B X I h hJ l Z hv u a i hi c c' F
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := KMap.laHyp_of_vecP I (I.cols l) Z.W Z.V Z.S Z.N Z.G h hv a u i (i + 1)
  have h0 : I.A.AA ≠ ⊥ := by
    rw [I.A_AA, Ne, FractionalIdeal.coeToSubmodule_eq_bot]
    refine inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 fun h0 => ?_)
    have h1 := B.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact (differentIdeal_ne_bot : differentIdeal (𝓞 B.host.K) (𝓞 B.host.E) ≠ ⊥) h1
  have hJa : GlobalTheory.KerT.JetsAll (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a) I.A u i (i + 1) := fun L L' hL hL' =>
    (GlobalTheory.MoveCompare.jetsIn_iff _ _ _ _ _ _ _ (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi) L L').2
      (GlobalTheory.MoveCompare.jetsAll_of_deg _ _ _ _ _ (hJ a u i hi) (GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u) hL hL')
  have hr := KMap.rhoIs I h a u hi
  refine KMap.kmap_of_jet (I.chIn u a) I.A.σ₀ (l.ch u a) (B.hcW u) hi c c' F _ ?_
  have hV := GlobalTheory.GO.ChSrc.jetInVV_trueWt (X := B.fields) (B.hcW u) hi
  have hnu : GlobalTheory.GO.ChSrc.nuEnd (B.hcW u) i = nuLast (Pr := B.primes X) B.wts u i := GlobalTheory.GO.ChSrc.nuEnd_eq (Pr := B.primes X) B.wts u hi
  rw [hnu] at hV ⊢

  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) := pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB := GlobalTheory.MoveCompare.cBof_pos hPr I.sel (I.tup a) (I.cst a) u
  have hLa' : I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u) := hLa
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i
    hX hPr h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1
  have key := fun (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)) =>
    KMap.map_kerOf (X := B.fields) I.A (Sall (Pr := B.primes X) I.sel (I.tup a) u) (rowSG (B.primes X) I.sel (I.tup a)) hA hB I.sel
      (mUof (R := B.R) I.Ch (I.tup a) i) (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) (B.wts.lamTrue u i) (B.wts.lamTrue u (i + 1))
      (nuLast (Pr := B.primes X) B.wts u i) hV hLa' h0 hE
      (frsF I.sel (I.tup a) p.1.1) (frsF I.sel (I.tup a) p'.1.1)
      ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
      (hJa _ _ ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩) (hbox p p') F
  refine (key (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c')).trans ?_
  rw [← hr c.1 (((dat I l Z u a).I.S i).rep c) c'.1 (((dat I l Z u a).I.S (i + 1)).rep c'), ColIn.A_cD]
  rfl

end GlobalTheory.LvT.Built.TrueLaws
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelEqPointKernelAtRepresentativesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

open _root_.Formalism.L2.Col

attribute [local instance] GlobalTheory.Mem.Col2.starE

local instance representativeDatNumberField {B : Base} {X : PreX B.toPre} (I : TC B X)
    (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    @NumberField (dat I l Z u a).E (dat I l Z u a).fE :=
  (dat I l Z u a).nE

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChainKernel_eq_pointKernel_at_representatives : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c') F) := by
  exact @_root_.GlobalTheory.LvT.Built.TrueLaws.kmap_dat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KernelJetsLevelPlaceIntegralMoments
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetMomentsOfUnitPeriod
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable


open Formalism.MainNotions.TaylorLogMetric in
theorem jetMoments_of_unitPeriod
    (hM : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc →
      IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ 2 →
      jacobiSym (-(D.host.d : ℤ)) p = 1 → Nat.Coprime (Ideal.absNorm cc) p →
      ∃ Ω : ℂ_[p], ‖Ω‖ = 1 ∧ GlobalTheory.MomT.MomentsAt D cc δ (B.eNat χ) lam Ω)
    (hE : MovesAll) (hL : LatticeFactsAll) : JetMoments := by
  intro D hD H s cc δ B χ cD ⟨hs, _, hcc, hδ, hχ, hcD⟩ u _ hcop w ι hw
  classical
  obtain ⟨lam, hlam⟩ := (_root_.GlobalTheory.MomPlace.places D.X.K (D.Pr.T u) s.σ₀ ι).1
  obtain ⟨⟨hTs, hTq⟩, -⟩ : (D.Pr.T u ∉ H.host.small ∧ D.Pr.T u ≠ H.host.q) ∧
      ∀ i, D.Pr.g i ∉ H.host.small ∧ D.Pr.g i ≠ H.host.q :=
    ⟨(_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).1 u, (_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).2⟩
  have hT2 : D.Pr.T u ≠ 2 := UpperTheory.Small.ne_two H.host hTs
  have hP := hD.primes
  have hp := hP.T_prime u
  have hn := hP.piT_norm u
  obtain ⟨Ω, hΩ, hmom⟩ := hM H cc δ B χ hcc hδ hχ (D.Pr.T u) lam hT2
    ((_root_.GlobalTheory.MomT.SplitK.splitk H D.X s (D.Pr.piT u) _ hs (hP.piT_Kq u)).2 hp hT2 hn (hP.piT_cop u)) hcop
  obtain ⟨M, _, hMe, hMs⟩ := hcD
  have hcQ : ∀ τ, cD τ ∈ TaylorLogMetric.Qbar := by
    intro τ
    obtain ⟨x, hx, -⟩ := hMs τ
    rw [← hx]
    exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (algebraMap M ℂ).toRatAlgHom)
  refine ⟨fun τ => TaylorLogMetric.lamC lam (cD (s.iT τ)) / Ω, fun τ => ?_, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := hMs (s.iT τ)
    rw [norm_div, hΩ, div_one, ← hx]
    exact GlobalTheory.EigenGenerator.norm_generator_eq_one H _ lam hTs hTq M hMe _ x hx'
  intro sel S mu cst hsel hS hcq i b _ hb SG SG' d d' hd hd' Ξ₀ hΞ
  have hev : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add ((D.R.t_odd.add_one).mul_left j)
  have ha := hev i
  have hb' : Even b := hb ▸ hev _
  obtain ⟨hla, hsm⟩ := hL H D.X s cc δ B χ cD hD.fields hs hcc hδ hχ _ _ ha hb'
  have hπ0 : D.Pr.piT u ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  have hπ0' : D.X.conjO (D.Pr.piT u) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  obtain ⟨hfree, hrow⟩ := _root_.GlobalTheory.Proof.AbsNormSplitPlace.main D u sel S mu hD hsel (hS (Or.inr ⟨u, rfl⟩))
    (fun k => hS (Or.inl (by fin_cases k <;> simp)))
  have hUT : ∀ P : HeightOneSpectrum (𝓞 D.X.E), ((D.Pr.T u : ℕ) : 𝓞 D.X.E) ∈ P.asIdeal →
      localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 D.X.E) D.X.E) :=
    fun P h => _root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.1 H D.X s cc δ B χ cD P _ hp hTs hTq h hcop
  have hmemS : ∀ P, P ∈ Sall sel mu u ↔ D.Pr.piT u ∈ P.asIdeal ∨ P ∈ rowSG D.Pr sel mu := by
    intro P
    unfold Sall
    rw [Finset.mem_union, Primes.vT, mem_divs hπ0]
  have hU : (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
    intro P hPS
    rcases (hmemS P).1 hPS with h | h
    · exact hUT P (hn ▸ Ideal.mul_mem_right _ _ h)
    · have bad := _root_.GlobalTheory.ThetaMove.BadPrimes.bad_primes D.X D.Pr sel S mu u hD.fields hP hsel (hS (Or.inr ⟨u, rfl⟩))
        (fun k => hS (Or.inl (by fin_cases k <;> simp))) P hPS
      exact _root_.GlobalTheory.PeriodIdealUnit.locP_AA_eq_one D.X H s cc δ B χ cD P bad.2.1 bad.2.2.1 (hcq P h)
  have hG : Nat.Coprime (∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) (D.Pr.T u) :=
    Nat.Coprime.prod_left fun P _ => (Nat.coprime_primes (hrow P.1 P.2).1 hp).2 (hrow P.1 P.2).2.1
  have hctx : Ctx (ambOf s B χ cD) (D.R.N i) b (Sall sel mu u) (rowSG D.Pr sel mu) (D.Pr.piT u) (D.Pr.T u)
      ((∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) ^ cst.B) (cAof sel mu cst) :=
    ⟨hD.fields, ⟨hla.1, hla.2.1, hfree, hU, hla.2.2.2.2⟩,
      fun P h => hUT P (hn ▸ Ideal.mul_mem_left _ _ ((mem_divs hπ0' P).1 h)), hsm, hp, hn, hP.piT_cop u, hmemS,
      fun P h => (hrow P h).2.2.1, hG.pow_left _, hG.pow_left _⟩
  have hN : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hN' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  obtain ⟨c1, c1'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d.1.N hD.fields hs hχ hn hN
    fun P h => hd ⟨P, (mem_divs hπ0 P).2 h⟩
  obtain ⟨c2, c2'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d'.1.N hD.fields hs hχ hn hN'
    fun P h => hd' ⟨P, (mem_divs hπ0 P).2 h⟩
  have hF : (ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar := mul_mem (zpow_mem c1 _) (zpow_mem c2 _)
  have hF1 : ‖TaylorLogMetric.lamC lam ((ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N)‖ = 1 := by
    refine (congrArg norm (lamC_mul lam (zpow_mem c1 _) (zpow_mem c2 _))).trans ?_
    rw [lamC_zpow lam c1, lamC_zpow lam c2, norm_mul, norm_zpow, norm_zpow, c1', c2', one_zpow, one_zpow, one_mul]
  refine ⟨fun hseen => ?_, fun hseen => ?_⟩
  · refine type_bar hctx hlam hw d d' hF hF1 Ξ₀ hΞ ?_
    have := _root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.X.conjO (D.Pr.piT u)) (D.R.N i) b hD.fields hs hcc hT2 hcop
      (fun k => (hlam k).2) hcQ (fun τ τ' => ?_) (by rw [conjO_conjO, mul_comm, hn])
      (by rw [conjO_conjO]; exact (hP.piT_cop u).symm) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rwa [e, star_star] at this
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rw [e, hD.fields.emb_star, hD.fields.emb_star, hP.piT_Kq u τ τ']
  · have hsq : ∀ P ∈ divs (D.Pr.piT u), D.Pr.piT u ∉ P.asIdeal ^ 2 := by
      intro P hPm h2
      refine GlobalTheory.SplitUnram.natCast_notMem_sq D.X.E D.X.conjO (D.Pr.piT u) _ conjO_conjO hp hn (hP.piT_cop u) ?_
        (hP.vT_norm u) P hPm (hn ▸ Ideal.mul_mem_right _ _ h2)
      have h1 : (divs (D.Pr.piT u)).card = Module.finrank ℚ D.X.F := (hP.vT_card u).trans hD.fields.card_Tau
      rw [h1, ← Module.finrank_mul_finrank ℚ D.X.F D.X.E, hD.fields.rankE, mul_comm]
    obtain ⟨N'', hN'', hc⟩ := _root_.GlobalTheory.MomT.MomentCompanion.companion D.X b SG' (D.Pr.piT u) d' hD.fields hπ0 (hP.piT_cop u) hsq
    have hval := _root_.GlobalTheory.MomT.ChiMove.chi_move H D.X s χ b SG' (D.Pr.piT u) d' N'' hD.fields hs hχ hπ0 (hP.piT_cop u) hsq hN'' hc
    set k : D.X.K := ∏ τ, (D.X.emb τ (((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) / star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E)))⁻¹ with hk
    have hval' : χ (TaylorLogMetric.detId H (s.lat d'.1.N) (s.lat N'')) = s.σ₀ k := by
      rw [hval, hk, map_prod]
      exact Finset.prod_congr rfl fun τ _ => (map_inv₀ _ _).symm
    have hk0 : k ≠ 0 := by
      have h0 : ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) ≠ 0 := by exact_mod_cast hπ0
      exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero ((map_ne_zero _).2 (div_ne_zero h0 (star_ne_zero.2 h0)))
    have hkn : ‖ι k‖ ≤ (D.Pr.T u : ℝ) ^ D.X.f := by
      rw [hk, map_prod, norm_prod]
      refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_).trans_eq
        (Finset.prod_const (D.Pr.T u : ℝ))
      rw [map_inv₀]
      exact norm_ratio_le (ι.comp (D.X.emb τ)) hn
    have hcard : (divs (D.Pr.piT u)).card = D.X.f := hP.vT_card u
    have key := type_p hctx hlam hw d d' hd hF hF1 Ξ₀ hΞ
      (_root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.Pr.piT u) (D.R.N i) b hD.fields hs hcc hT2 hcop
        (fun k => (hlam k).2) hcQ (hP.piT_Kq u) hn (hP.piT_cop u) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom)
      (hP.vT_norm u) N'' hN'' hc (s.σ₀ (k ^ (D.R.N i / 2))) (hlam _).1 ?_ ?_
    · rw [hcard] at key
      exact key
    · rw [(hlam _).2, map_pow, norm_pow, ← pow_mul, Nat.div_two_mul_two_of_even ha, hcard, pow_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) hkn _
    · intro R hR z
      have hmv := _root_.GlobalTheory.MomT.Move.move H D.X s cc δ B χ cD _ b d.1.N d'.1.N N'' hD.fields hs (hE H cc δ B χ hcc hδ hχ) ha hb' hla
        hN hN' hN'' R hR z
      have hR0 : ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ) ≠ 0 := by
        obtain ⟨x, hx, -⟩ := hR.2.2 0 (zero_mem _)
        have : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩
        exact_mod_cast (Real.sqrt_pos.2 this).ne'
      have hσ : s.σ₀ k ≠ 0 := (map_ne_zero _).2 hk0
      rw [hmv, hval', map_pow, zpow_neg, zpow_natCast]
      field_simp

end GlobalTheory.MomT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeFactsAll
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.MomLat

theorem latticeFactsAll : GlobalTheory.MomT.LatticeFactsAll := by
  intro D X s cc δ B χ cD hX hs hcc hδ hχ a b ha hb
  have hL := GlobalTheory.ThetaMove.LatticeFacts.latAll B hcc hδ
  have hVm := B.vec_mem_ne hcc hδ (delta_ne_zero B) (B.stdOK hcc hδ) χ hχ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hVm a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hVm a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.MomLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KernelJetsLevelPlaceIntegralMoments
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomTop

theorem jetMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments :=
  GlobalTheory.MomT.jetMoments_of_unitPeriod
    (GlobalTheory.T.unitPeriodTranslates_moments_finite GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomEq.eq_and_alg.2)
    GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomLat.latticeFactsAll

end GlobalTheory.MomTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KernelJetsLevelPlaceIntegralMomentsStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelJets_levelPlace_integralMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments := by
  first | exact @GlobalTheory.MomTop.jetMoments | exact GlobalTheory.MomTop.jetMoments | (intros; apply GlobalTheory.MomTop.jetMoments <;> assumption)
end
end
