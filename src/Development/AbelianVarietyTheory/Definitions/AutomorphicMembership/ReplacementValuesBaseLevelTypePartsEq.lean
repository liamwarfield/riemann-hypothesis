module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ValTransOfEq
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Generic

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {N : Type} [AddCommGroup N] [Module ℂ N] {P P' : Submodule ℂ N}
  {ip : N → N → ℂ} {j : X ≃ₗ[ℂ] P}

theorem hilbTie_ofEq (e : P = P') (h : HilbTie P ip j) : HilbTie P' ip (j.trans (LinearEquiv.ofEq _ _ e)) := fun x y => h x y

theorem projTie_ofEq {Y : Type} {f : Y → X} {g g' : Y → N} (e : P = P') (h : ProjTie P ip j f g) (hg : ∀ y, g' y = g y) :
    ProjTie P' ip (j.trans (LinearEquiv.ofEq _ _ e)) f g' := fun x y => (h x y).trans (congrArg (ip (j x)) (hg y).symm)


omit [NormedAddCommGroup X] [InnerProductSpace ℂ X] in
theorem le_of_eqs {Q Q' : Submodule ℂ N} (e : P = P') (e' : Q = Q') (h : P ≤ Q) : P' ≤ Q' := e ▸ e' ▸ h

theorem val_trans_ofEq (e : P = P') (x : X) : ((j.trans (LinearEquiv.ofEq _ _ e)) x).1 = (j x).1 := rfl

theorem map_incl {Q Q' : Submodule ℂ N} {Z : Type} (e : P = P') (e' : Q = Q') (h : P ≤ Q) (j : X ≃ₗ[ℂ] P) {f : Q → Z} (f' : Q' → Z)
    (hf : ∀ v, f' (LinearEquiv.ofEq _ _ e' v) = f v) (y : X) :
    f' (Submodule.inclusion (le_of_eqs e e' h) ((j.trans (LinearEquiv.ofEq _ _ e)) y)) = f (Submodule.inclusion h (j y)) := by
  subst e e'
  exact hf (Submodule.inclusion h (j y))

end Generic

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A} {tupT : a.D.what₂.Tup → T}
  {hm : 0 < a.D.R.m} {hTop : TopMultH R}

def stepB (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : spCC c F tupT hm hTop l μ (k + 1)) : (toChainReal R F tupT hm hTop).Amb k :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioC l ((μ)) k ((v))).1 : _))

theorem stepB_eq (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) :
    stepB c l μ k (LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v) =
      ((toChainReal R F tupT hm hTop).ioC l μ k v).1 := (ioCB_eq c l μ k v)

def topB (l : Bool) (μ : a.D.what₂.Tup) (v : spCCX c F tupT hm hTop l μ) : (toChainReal R F tupT hm hTop).Amb (a.D.R.m - 1) :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioX l ((μ)) ((v))).1 : _))

theorem topB_eq (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) :
    topB c l μ (LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v) =
      ((toChainReal R F tupT hm hTop).ioX l μ v).1 := (ioXB'_eq c l μ v)

section Rows

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {X : RowSide a.D EE} {l : Bool}

def rowIds (I : RowIds X (toChainReal R F tupT hm hTop) l) : RowIds (rowSide c X) (chainB c.to F tupT hm hTop) l :=
  @RowIds.mk c.to.D EE _ _ _ (rowSide c X) (chainB c.to F tupT hm hTop) l
    ((by with_unfolding_all exact ((I.jE.trans (LinearEquiv.ofEq _ _ (congrFun (spEEc_eq c F tupT hm hTop) l))) :)))
    ((by with_unfolding_all exact ((fun (μ : a.D.what₂.Tup) (h : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) => (I.jM μ h j h1 h2).trans
      (LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j))) :)))
    ((by with_unfolding_all exact ((fun (μ : a.D.what₂.Tup) (h : Used0 a.D μ) => (I.jX μ h).trans
      (LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ))) :)))
    ((I.prt))


set_option maxHeartbeats 4000000 in
theorem rowSideReal_tr {I : RowIds X (toChainReal R F tupT hm hTop) l} {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE}
    {ty : Fin n → a.D.what₂.FT} (H : RowSideReal X (toChainReal R F tupT hm hTop) l I bs ty) :
    RowSideReal (rowSide c X) (chainB c.to F tupT hm hTop) l (rowIds c I) bs ((ty)) := by
  refine @RowSideReal.mk _ _ _ _ _ _ _ _ _ _ _ _ ?parY ?lvl ?lvlP ?lvlX ?ee ?mult ?multX ?io0 ?io0X ?io ?ioTop ?ft ?prt_disj
  case parY =>
    exact (H.parY)
  case lvl =>
    exact (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) => le_of_eqs (congrFun (spEEc_eq c F tupT hm hTop) l) (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) 0) (H.lvl μ hμ))
  case lvlP =>
    exact (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) =>
      le_of_eqs (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) j) (H.lvlP μ hμ j h1 h2))
  case lvlX =>
    exact (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) => le_of_eqs (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) (H.lvlX μ hμ))
  case ee =>
    exact (hilbTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) H.ee)
  case mult =>
    intro μ hμ j h1 h2
    letI := X.instMult μ j
    letI := X.instMulti μ j
    have t := hilbTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (H.mult μ hμ j h1 h2)
    with_unfolding_all exact t
  case multX =>
    intro h μ hμ
    letI := X.instMult μ a.D.R.m
    letI := X.instMulti μ a.D.R.m
    have t := hilbTie_ofEq (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (H.multX h μ hμ)
    with_unfolding_all exact t
  case io0 =>
    have t := (fun (h : 2 ≤ a.D.R.m) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) (H.io0 h μ hμ (okB_imp c ok)) fun y =>
        map_incl (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (0 + 1))
          (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (0 + 1)) (H.lvlP μ hμ 1 le_rfl (by omega))
          (I.jM μ hμ 1 le_rfl (by omega)) (stepB c l μ 0) (stepB_eq c l μ 0) y)
    with_unfolding_all exact t
  case io0X =>
    have t := (fun (h : a.D.R.m = 1) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) (H.io0X h μ hμ (okB_imp c ok)) fun y =>
        congrArg (cast (congrArg (toChainReal R F tupT hm hTop).Amb (show a.D.R.m - 1 = 0 by omega)))
          (map_incl (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ)
            (H.lvlX μ hμ) (I.jX μ hμ) (topB c l μ) (topB_eq c l μ) (cast (congrArg (X.Mult μ) h.symm) y)))
    with_unfolding_all exact t
  case io =>
    intro μ hμ ok j h1 h2
    letI := X.instMult μ j
    letI := X.instMulti μ j
    letI := X.instMult μ (j + 1)
    letI := X.instMulti μ (j + 1)
    have t := projTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (H.io μ hμ (okB_imp c ok) j h1 h2) fun y =>
        map_incl (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (j + 1))
          (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (j + 1)) (H.lvlP μ hμ (j + 1) (by omega) h2)
          (I.jM μ hμ (j + 1) (by omega) h2) (stepB c l μ j) (stepB_eq c l μ j) y
    with_unfolding_all exact t
  case ioTop =>
    have t := (fun (h : 2 ≤ a.D.R.m) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (a.D.R.m - 1)) (H.ioTop h μ hμ (okB_imp c ok)) fun y =>
        map_incl (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ)
          (H.lvlX μ hμ) (I.jX μ hμ) (topB c l μ) (topB_eq c l μ) y)
    with_unfolding_all exact t
  case ft =>
    exact (fun σ => cast (congrArg (· ∈ I.prt (ty σ)) (val_trans_ofEq (j := I.jE) (congrFun (spEEc_eq c F tupT hm hTop) l) (bs σ)).symm) (H.ft σ))
  case prt_disj =>
    exact (H.prt_disj)

end Rows

variable {hinj : ∀ i t, Function.Injective (R.extV i t)}


variable (F tupT hm hTop hinj) in
def spWc : type_of% (toLiftReal R F tupT hm hTop hinj).Wc := ((liftB c.to F tupT hm hTop hinj).Wc)


variable (F tupT hm hTop hinj) in
theorem spWc_eq : (toLiftReal R F tupT hm hTop hinj).Wc = spWc c F tupT hm hTop hinj := (lift_Wc c.to F tupT hm hTop hinj)


variable (F tupT hm hTop hinj) in
def spMultW : type_of% (toLiftReal R F tupT hm hTop hinj).MultW := ((liftB c.to F tupT hm hTop hinj).MultW)


variable (F tupT hm hTop hinj) in
theorem spMultW_eq : (toLiftReal R F tupT hm hTop hinj).MultW = spMultW c F tupT hm hTop hinj := (lift_MultW c.to F tupT hm hTop hinj)

def liftIds (I : LiftIds (toLiftReal R F tupT hm hTop hinj)) : LiftIds (liftB c.to F tupT hm hTop hinj) :=
  @LiftIds.mk c.to.D (chainB c.to F tupT hm hTop) (liftB c.to F tupT hm hTop hinj)
    ((by with_unfolding_all exact ((fun i : Fin a.D.R.m => (I.jMj i).trans (LinearEquiv.ofEq _ _ (congrFun (spWc_eq c F tupT hm hTop hinj) i))) :)))
    ((I.jMt)) ((I.prtW))

theorem liftTie_tr {I : LiftIds (toLiftReal R F tupT hm hTop hinj)} (H : LiftTie (toLiftReal R F tupT hm hTop hinj) I) :
    LiftTie (liftB c.to F tupT hm hTop hinj) (liftIds c I) := by
  refine @LiftTie.mk _ _ _ _ ((H.hol)) (by with_unfolding_all exact (fun i => hilbTie_ofEq (congrFun (spWc_eq c F tupT hm hTop hinj) i) (H.mj i))) ((H.mt)) ?_ (by with_unfolding_all exact H.isot) ((H.prtW_disj)) ((H.lamP))
  with_unfolding_all exact (cast (congrArg₂ (fun (P : type_of% (toLiftReal R F tupT hm hTop hinj).MultW) (Q : type_of% (toLiftReal R F tupT hm hTop hinj).Wc) =>
    ∀ μ (hμ : Used0 a.D μ) (i : Fin a.D.R.m) (x : a.D.what₂.Mt μ (i + 1)) (w : (toLiftReal R F tupT hm hTop hinj).AmbW i),
      Lift.IsThetaP ((toLiftReal R F tupT hm hTop hinj).measV μ i) ((toLiftReal R F tupT hm hTop hinj).fdV μ i)
        ((toLiftReal R F tupT hm hTop hinj).thW μ i) ((toLiftReal R F tupT hm hTop hinj).ptW μ i) ((toLiftReal R F tupT hm hTop hinj).ioK i)
        ((toLiftReal R F tupT hm hTop hinj).Amt μ i) ((toLiftReal R F tupT hm hTop hinj).thC μ i) → w ∈ P i →
      w ∘ₗ (toLiftReal R F tupT hm hTop hinj).embK i = (toLiftReal R F tupT hm hTop hinj).thC μ i (I.jMt μ hμ i x) →
      (toLiftReal R F tupT hm hTop hinj).eW i ∘ₗ w ∈ Q i →
      (I.jMj i (a.D.what₂.thetaP μ (i + 1) x)).1 = (toLiftReal R F tupT hm hTop hinj).eW i ∘ₗ w)
    (spMultW_eq c F tupT hm hTop hinj) (spWc_eq c F tupT hm hTop hinj)) H.theta)

theorem recTied_tr {X0 : BaseLevelRowSide a.D} {Ish : RowIds (RowSide.sharp a.D) (toChainReal R F tupT hm hTop) true}
    {Iz : RowIds X0.s (toChainReal R F tupT hm hTop) false} {IL : LiftIds (toLiftReal R F tupT hm hTop hinj)} {K : ColReal a.D}
    (H : RecTied a.D X0 (toChainReal R F tupT hm hTop) Ish Iz (toLiftReal R F tupT hm hTop hinj) IL K) :
    RecTied c.to.D (baseLevelRowSideTransport c X0) (chainB c.to F tupT hm hTop) ((rowIds c Ish)) ((by with_unfolding_all exact @rowIds B C a c G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R F tupT hm hTop (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X0) false Iz)) (liftB c.to F tupT hm hTop hinj)
      (liftIds c IL) (colReal c K) :=
  @RecTied.mk _ _ _ _ _ _ _ _ ((rowSideReal_tr c H.sharp)) ((by with_unfolding_all exact @rowSideReal_tr B C a c G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R F tupT hm hTop (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X0) false Iz (@Rows.Data.D0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.onb0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.ft0 (@Late.D B C a).R (@Late.D B C a).what₂) (@RecTied.base (@Late.D B C a) X0 (@toChainReal (@Late.D B C a) G ‹Group G› ‹Fintype G› Pl0 T A Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK R F tupT hm hTop) Ish Iz (@toLiftReal (@Late.D B C a) G ‹Group G› ‹Fintype G› Pl0 T A Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK R F tupT hm hTop hinj) IL K H))) (liftTie_tr c H.lift)
    (@ColTieR.mk _ _ _ ((H.col.tup)) ((H.col.xi0)) ((H.col.bu)))

def mjTie (x : MjTie R F) : @MjTie c.to.D G _ _ Pl0 T (famM c.to A) Ks _ _ (alg c.to iK) (real c.to R) (face c.to F) :=
  @MjTie.mk c.to.D G _ _ Pl0 T (famM c.to A) Ks _ _ (alg c.to iK) (real c.to R) (face c.to F) ((x.eW))
    ((by with_unfolding_all exact ((cast (congrArg (fun W : type_of% R.Wat => ∀ i, LinearMap.range (x.eW i) =
      (W i (sg0 a.D A) (R.levL F false (sg0 a.D A))).comap (R.HW i (sg0 a.D A)).e) (wat_eq c.to R)) x.eW_range) :)))
    ((x.eW_norm)) ((x.eW_lat))

end Chain

end GlobalTheory.Mem.R3.Tr

end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

theorem finTypRep_trans_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S S' : Set (Formalism.L2.NG.FinTyp E n)}
    (e : S = S') {α : Type} (f : α ≃ Formalism.L2.Col.FinTypCls S) (x : α) :
    Formalism.L2.Col.finTypRep S (f x) = Formalism.L2.Col.finTypRep S' (f.trans (Equiv.cast (congrArg Formalism.L2.Col.FinTypCls e)) x) := by
  subst e
  rfl

local instance instCMHostTr (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m}

section Two

variable {R : RealDat a.D A.A Ks} {F : Face a.D A.A} {X0 : BaseLevelRowSide a.D} (Y : Read (A3 := A) R F X0)

abbrev occA : Set (Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) :=
  principalLevelFrame.OccRows R.θ Y.PY (R.MY 0) (fun l => levS _ (R.βY 0) (R.dat0 (R.levR F l)))
    (fun l => levChi _ (R.βY 0) (R.dat0 (R.levR F l))) fun _ => R.e0

def occB : Set (Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) :=
  {π | ∃ l, isotLB c.to a R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F l))) (levChi _ (R.βY 0) (R.dat0 (R.levR F l))) R.e0
    (principalLevelFrame.FinTyp.conjT π) ≠ ⊥}

theorem occ_eq : occA Y = occB c Y :=
  (by with_unfolding_all exact ((congrArg (fun m : type_of% (@principalLevelFrame.isotL a.D) => {π : Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r | ∃ l,
    m R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F l))) (levChi _ (R.βY 0) (R.dat0 (R.levR F l))) R.e0
      (principalLevelFrame.FinTyp.conjT π) ≠ ⊥}) (isotL_eq c.to a)) :))

def eFTB : a.D.what₂.FT ≃ Formalism.L2.Col.FinTypCls (occB c Y) :=
  Equiv.trans (β := Formalism.L2.Col.FinTypCls (occA Y)) Y.eFT (Equiv.cast (congrArg Formalism.L2.Col.FinTypCls (occ_eq c Y)))

theorem rep_eq (π : a.D.what₂.FT) : principalLevelFrame.rowRepR R.θ (Y.eFT π) = Formalism.L2.Col.finTypRep (occB c Y) (eFTB c Y π) :=
  (by with_unfolding_all exact ((finTypRep_trans_cast (occ_eq c Y) Y.eFT π) :))

theorem prtE_tr (π : a.D.what₂.FT) : Y.Ish.prt π = (isotLB c.to a R.θ Y.PY (R.MY 0)
    (levS _ (R.βY 0) (R.dat0 (R.levR F true))) (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) R.e0
    (principalLevelFrame.FinTyp.conjT (Formalism.L2.Col.finTypRep (occB c Y) (eFTB c Y π)))).map
      (PiTensorProduct.lift : MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap :=
  (Y.prtE π).trans ((by with_unfolding_all exact ((congrArg₂ (fun (m : type_of% (@principalLevelFrame.isotL a.D)) (ρ : Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) =>
    (m R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true))) (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) R.e0
      (principalLevelFrame.FinTyp.conjT ρ)).map (PiTensorProduct.lift : MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap) (isotL_eq c.to a) (rep_eq c Y π)) :)))

theorem replacementValues_baseLevelTypeParts_eq (π : a.D.what₂.FT) : Y.Iz.prt π = (isotLB c.to a R.θ Y.PY (R.MY 0)
    (levS _ (R.βY 0) (R.dat0 (R.levR F false))) (levChi _ (R.βY 0) (R.dat0 (R.levR F false))) R.e0
    (principalLevelFrame.FinTyp.conjT (Formalism.L2.Col.finTypRep (occB c Y) (eFTB c Y π)))).map
      (PiTensorProduct.lift : MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap :=
  (Y.prtE0 π).trans ((by with_unfolding_all exact ((congrArg₂ (fun (m : type_of% (@principalLevelFrame.isotL a.D)) (ρ : Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) =>
    (m R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F false))) (levChi _ (R.βY 0) (R.dat0 (R.levR F false))) R.e0
      (principalLevelFrame.FinTyp.conjT ρ)).map (PiTensorProduct.lift : MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap) (isotL_eq c.to a) (rep_eq c Y π)) :)))

theorem prtWE_tr (i : Fin a.D.R.m) (π : a.D.what₂.FT) : Y.IL.prtW i π = (isotLB c.to a R.θ (Y.PW i) (R.MW i (sg0 a.D A.A))
    (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 a.D A.A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 a.D A.A))))
    (R.eWf i (sg0 a.D A.A)) (Formalism.L2.Col.finTypRep (occB c Y) (eFTB c Y π))).map
      (PiTensorProduct.lift : MMap (R.MW i (sg0 a.D A.A)) ≃ₗ[ℂ] _).toLinearMap :=
  (Y.prtWE i π).trans ((by with_unfolding_all exact ((congrArg₂ (fun (m : type_of% (@principalLevelFrame.isotL a.D)) (ρ : Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) =>
    (m R.θ (Y.PW i) (R.MW i (sg0 a.D A.A))
      (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 a.D A.A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 a.D A.A))))
      (R.eWf i (sg0 a.D A.A)) ρ).map (PiTensorProduct.lift : MMap (R.MW i (sg0 a.D A.A)) ≃ₗ[ℂ] _).toLinearMap)
    (isotL_eq c.to a) (rep_eq c Y π)) :)))

theorem isomFin_tr (i : Fin a.D.R.m) : @principalLevelFrame.IsIsomFin c.to.D (Yc c.to.D 0) (Wc c.to.D ((i))) ((Y.ιW i)) := by
  constructor
  case bij => exact (by with_unfolding_all exact ((Y.isomFin i).bij :))
  case conj => exact (by with_unfolding_all exact ((Y.isomFin i).conj :))
  case lat => exact (by with_unfolding_all exact ((Y.isomFin i).lat :))


set_option maxHeartbeats 800000 in
def read : @Read c.to.D G _ _ Pl0 I0 T (famInThreeCoefficientChange c.to A) Ks _ _ (alg c.to iK) ((by with_unfolding_all exact ((real c.to R) :))) ((by with_unfolding_all exact ((face c.to F) :))) (baseLevelRowSideTransport c X0) :=
  @Read.mk c.to.D G _ _ Pl0 I0 T (famInThreeCoefficientChange c.to A) Ks _ _ (alg c.to iK) ((by with_unfolding_all exact ((real c.to R) :))) ((by with_unfolding_all exact ((face c.to F) :))) (baseLevelRowSideTransport c X0)
    (tup := (by with_unfolding_all exact (Y.tup :)))
    (tupT := (by with_unfolding_all exact (Y.tupT :)))
    (tupT_tup := (by with_unfolding_all exact (Y.tupT_tup :)))
    (tupTie := (by with_unfolding_all exact (Y.tupTie :)))
    (tup0 := (by with_unfolding_all exact (Y.tup0 :)))
    (muAt := (by with_unfolding_all exact (Y.muAt :)))
    (hm := (by with_unfolding_all exact (Y.hm :)))
    (hTop := (by with_unfolding_all exact ((topMult_tr c.to Y.hTop) :)))
    (hinj := (by with_unfolding_all exact ((inj_tr c.to Y.hinj) :)))
    (Ish := (by with_unfolding_all exact ((rowIds c Y.Ish) :)))
    (Iz := (by with_unfolding_all exact ((rowIds c Y.Iz) :)))
    (IL := (by with_unfolding_all exact ((liftIds c Y.IL) :)))
    (Kc := colReal c Y.Kc)
    (PY := (by with_unfolding_all exact ((rowPsi c.to Y.PY) :)))
    (PW := (by with_unfolding_all exact ((fun i => rowPsi c.to (Y.PW i)) :)))
    (eFT := (by with_unfolding_all exact ((eFTB c Y) :)))
    (ιW := (by with_unfolding_all exact (Y.ιW :)))
    (tied := (by with_unfolding_all exact ((recTied_tr c Y.tied) :)))
    (prtE := (by with_unfolding_all exact ((prtE_tr c Y) :)))
    (prtE0 := (by with_unfolding_all exact ((replacementValues_baseLevelTypeParts_eq c Y) :)))
    (prtWE := by with_unfolding_all exact (prtWE_tr c Y :))
    (xi := (by with_unfolding_all exact (Y.xi :)))
    (isomFin := (by with_unfolding_all exact ((isomFin_tr c Y) :)))
    (frameMatch := (by with_unfolding_all exact (Y.frameMatch :)))
    (hF := (by with_unfolding_all exact (Y.hF :)))
    (stdPsi := (by with_unfolding_all exact (Y.stdPsi :)))
    (jA := (by with_unfolding_all exact (Y.jA :)))
    (jA0 := (by with_unfolding_all exact (Y.jA0 :)))
    (eMt := (by with_unfolding_all exact (Y.eMt :)))
    (formsA := (by with_unfolding_all exact (Y.formsA :)))
    (latA := (by with_unfolding_all exact (Y.latA :)))
    (formsAtBottomLevel := (by with_unfolding_all exact (Y.formsAtBottomLevel :)))
    (latA0 := (by with_unfolding_all exact (Y.latA0 :)))
    (formsL := (by with_unfolding_all exact (Y.formsL :)))
    (latL := (by with_unfolding_all exact (Y.latL :)))
    (topRead := (by with_unfolding_all exact ((fun t h x => (val_trans_ofEq (j := Y.Ish.jX (Y.tup t) h)
      (congrFun (congrFun (spCCXP_eq c F Y.tupT Y.hm Y.hTop) true) (Y.tup t)) _).trans (Y.topRead t h x)) :)))
    (topRead0 := (by with_unfolding_all exact ((fun t h x => (val_trans_ofEq (j := Y.Iz.jX (Y.tup t) h)
      (congrFun (congrFun (spCCXP_eq c F Y.tupT Y.hm Y.hTop) false) (Y.tup t)) _).trans (Y.topRead0 t h x)) :)))
    (mtRead := (by with_unfolding_all exact (Y.mtRead :)))
    (mj := (by with_unfolding_all exact ((mjTie c Y.mj) :)))
    (mjRead := (by with_unfolding_all exact ((fun i y => (val_trans_ofEq (j := Y.IL.jMj i) (congrFun (spWc_eq c F Y.tupT Y.hm Y.hTop Y.hinj) i) y).trans
      (Y.mjRead i y)) :)))
    (stable := (by with_unfolding_all exact (Y.stable :)))
    (stable0 := (by with_unfolding_all exact (Y.stable0 :)))
    (eE := (by with_unfolding_all exact (Y.eE :)))
    (eE_read := (by with_unfolding_all exact ((fun x => (val_trans_ofEq (j := Y.Ish.jE) (congrFun (spEEc_eq c F Y.tupT Y.hm Y.hTop) true) x).trans (Y.eE_read x)) :)))
    (dall := (by with_unfolding_all exact ((Y.dall.trans (congrArg (fun m : type_of% (@Mult.Mult a.D) => Module.finrank ℂ
      (m R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true))) (levChi _ (R.βY 0) (R.dat0 (R.levR F true))))) (mult_eq c.to a))) :)))
    (junk := (by with_unfolding_all exact (Y.junk :)))
    (cen0 := fun cG h => (by with_unfolding_all exact ((Y.cen0 _ (keep_back c.to c.same' (cG := (by with_unfolding_all exact (cG :))) ((by with_unfolding_all exact (h :))))) :)))
    (cen1 := fun cG h => (by with_unfolding_all exact ((Y.cen1 _ (keep_back c.to c.same' (cG := (by with_unfolding_all exact (cG :))) ((by with_unfolding_all exact (h :))))) :)))
    (lam := (by with_unfolding_all exact (Y.lam :)))
    (occ := (by with_unfolding_all exact (Y.occ :)))
    (kap := (by with_unfolding_all exact (Y.kap :)))
    (bu := (by with_unfolding_all exact (Y.bu :)))
    (ze := (by with_unfolding_all exact (Y.ze :)))

end Two

section Three

variable {R : RealDat3 a.D A Ks} {F : Face3 a.D A} {X0 : BaseLevelRowSide a.D} {Y : Read (A3 := A) R.toRealDat F.lv2 X0}


variable (R) in
def partsB : Parts R :=
  ((by with_unfolding_all exact ((letI := alg c.to iK; (real3 c.to R).EEp3) :)), (by with_unfolding_all exact ((letI := alg c.to iK; (real c.to R.toRealDat).EEat) :)),
    (by with_unfolding_all exact ((letI := alg c.to iK; (real3 c.to R).Wp3) :)))

variable (Z : ReadL R F X0 Y) (u : Parts R)

def eRRu : (Fin ((cxW R F u).data F.cr true).D → a.D.what₂.LL) ≃ₗ[a.D.what₂.LL] a.D.div.RR.V := (by with_unfolding_all exact (Z.eRR :))

def riemannRochSpaceCoordinateEquiv : (Fin ((cxW R F u).data F.cr false).D → a.D.what₂.LL) ≃ₗ[a.D.what₂.LL] X0.s.RR.V := (by with_unfolding_all exact (Z.eRR0 :))

def jWu (i : Fin a.D.R.m) :
    (Fin (((cxW R F u).data F.cr false).dW i) → a.D.what₂.LL) →ₛₗ[a.D.what₂.embLL] a.D.what₂.Mj ((i : ℕ) + 1) := (by with_unfolding_all exact ((Z.jW i) :))

theorem jEEu : ∀ y, (Y.Ish.jE (a.D.jEE (eRRu Z u y))).1 =
    PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt a.D.what₂.embLL A.A.v0) (E := R.HE.H)
      ((cxW R F u).iC F.cr true A.A.μ0 (Cx.cpt A.A.v0.embedding y)))) := (by with_unfolding_all exact (Z.jEE :))

theorem jEE0u : ∀ y, (Y.Iz.jE (X0.s.jEE (riemannRochSpaceCoordinateEquiv Z u y))).1 =
    PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt a.D.what₂.embLL A.A.v0) (E := R.HE.H)
      ((cxW R F u).iC F.cr false A.A.μ0 (Cx.cpt A.A.v0.embedding y)))) := (by with_unfolding_all exact (Z.jEE0 :))

theorem metu : ∀ v, v ≠ A.A.v0 → ∀ x y, Formalism.HermitianLatticesTheory.majAt a.D.div.RR.b a.D.div.RR.X v (eRRu Z u x) (eRRu Z u y) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun a.D.what₂.LL _) ((cxW R F u).data F.cr true).XE v x y := (by with_unfolding_all exact (Z.met :))

theorem met0u : ∀ v, v ≠ A.A.v0 → ∀ x y, Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X v (riemannRochSpaceCoordinateEquiv Z u x) (riemannRochSpaceCoordinateEquiv Z u y) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun a.D.what₂.LL _) ((cxW R F u).data F.cr false).XE v x y := (by with_unfolding_all exact (Z.met0 :))


open Classical in
include Z in
theorem etaJu : ∀ (i : Fin a.D.R.m) w, a.D.what₂.etaJ ((i : ℕ) + 1) w =
    if a.D.plEq w ∈ R.twPl then A.A.fam.etaJ F.P0 F.ψ0 (A.fam3.toSub2 (cxW R F u).zs) i (R.mu (a.D.plEq w)) (a.D.plEq w) else 0 :=
  (by with_unfolding_all exact (Z.etaJ :))

def readL : @ReadL c.to.D G _ _ Pl0 I0 T (famInThreeCoefficientChange c.to A) Ks _ _ (alg c.to iK) (real3 c.to R) (face3 c.to F) (baseLevelRowSideTransport c X0)
    ((read c Y)) :=
  @ReadL.mk c.to.D G _ _ Pl0 I0 T (famInThreeCoefficientChange c.to A) Ks _ _ (alg c.to iK) (real3 c.to R) (face3 c.to F) (baseLevelRowSideTransport c X0) ((by with_unfolding_all exact ((read c Y) :)))
    (eRR := (by with_unfolding_all exact ((eRRu Z (partsB c R)) :)))
    (eRR0 := (by with_unfolding_all exact ((riemannRochSpaceCoordinateEquiv Z (partsB c R)) :)))
    (jEE := (by with_unfolding_all exact ((fun y => (val_trans_ofEq (j := Y.Ish.jE) (congrFun (spEEc_eq c F.lv2 Y.tupT Y.hm Y.hTop) true) _).trans
      (jEEu Z (partsB c R) y)) :)))
    (jEE0 := (by with_unfolding_all exact ((fun y => (val_trans_ofEq (j := Y.Iz.jE) (congrFun (spEEc_eq c F.lv2 Y.tupT Y.hm Y.hTop) false) _).trans
      (jEE0u Z (partsB c R) y)) :)))
    (met := (by with_unfolding_all exact ((metu Z (partsB c R)) :)))
    (met0 := (by with_unfolding_all exact ((met0u Z (partsB c R)) :)))
    (rr := by
      set_option smartUnfolding false in
        with_unfolding_all exact (Z.rr :))
    (rr0 := by
      set_option smartUnfolding false in
        with_unfolding_all exact (Z.rr0 :))
    (jW := (by with_unfolding_all exact ((jWu Z (partsB c R)) :)))
    (jW_read := (by with_unfolding_all exact (Z.jW_read :)))
    (etaJ := (by with_unfolding_all exact ((etaJu Z (partsB c R)) :)))

end Three

end GlobalTheory.Mem.R3.Tr

end
