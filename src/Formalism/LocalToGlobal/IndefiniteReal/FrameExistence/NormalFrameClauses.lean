module

public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOKg2
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistGOfFramesExist
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.IndefR.Mi IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
def NormalClausesG (Pg : Finset (Pl D.host.E)) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D))
    (βW : ∀ i : Fin D.R.m, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E),
    (NormalFrames (betaYOf βY) e ev z κ s Pg Pg ∧ NormalFrame0 (betaYOf βY 0) Pg Pg) ∧
    ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf βY 0) (βW i) eW ι Pg



end Formalism.IndefR.Seed.Frm

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.IndefR.Mi IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def XBasesG (Pg : Finset (Pl D.host.E)) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) : Prop :=
  ∀ j : ℕ, j < D.R.m → ∃ βX : GL (Fin (D.sp.X j).rank) (EAf D), Formalism.L2.DIV.IsFrame βX (l0X (D.sp.X j)) ∧
    ∀ PP ∈ Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      ∀ (col : Fin (D.sp.Y j).rank) (l : Fin (D.sp.X j).rank), IsXCol (D := D) j col l →
        ∀ r : Fin (D.sp.Y j).rank, toEAf D ei * (betaYOf βY j).val r col =
          toEAf D ei * (xMat (D := D) j).mulVec (fun i => βX.val i l) r

def NormalFrameConditionsDiagonal (Pg : Finset (Pl D.host.E)) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D))
    (βW : ∀ i : Fin D.R.m, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  NormalClausesG Pg βY βW ∧ XBasesG Pg βY


variable (D) in
def FramesExistDiagonal (Pg : Finset (Pl D.host.E)) : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    SDFrames ΛY ΛX ΛV ΛW βY βX βV βW ∧ NormalFrameConditionsDiagonal Pg βY βW

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem framesOKg2_iff (Rl : RealDat3 D A3 Ks) :
    FramesOKg2 Rl ↔ NormalFrameConditionsDiagonal Rl.toRealDat.Pg Rl.toRealDat.βY Rl.toRealDat.βW := by
  first
  | exact Iff.rfl
  | (unfold FramesOKg2 NormalFrameConditionsDiagonal; done)

end Formalism.IndefR.Seed.Frm

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Seed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

section Pieces

variable (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)

def TupL (L : LevCh D T) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop :=
  (∀ w, w ∉ twPl → mu w = A3.A.μ0) ∧ (∀ t, t = A3.A.μ0 ∨ ∃ w, mu w = t) ∧ (∀ w ∈ twPl, mu w ≠ A3.A.μ0) ∧
    (∀ w, mu (DivisionValues.conjPl w) = mu w) ∧
    ∀ w ∈ twPl, ∃ (ψw : Formalism.L2.Host.HChar D.host.E) (Qw : Finset (Pl D.host.E)),
      Formalism.L2.Host.IsPsi (H := D.host) (Formalism.EigenvalueLevelCeiling.plc w) Qw ψw ∧ L.xiH (mu w) = L.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψw

def RecL (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) : Prop :=
  ∃ (eR : G ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ L.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff (eR g)) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧
      ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)

def LevelsL (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (F : Face D A3.A) : Prop :=
  ∃ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi L.Pg ψ0 ∧
    levPOf eG D.what₂.embLL (F.lvl false).P (F.lvl false).ψ = P0 L.Pg D.R.r ψ0 ∧
    ∃ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π ∧
      (∀ g, g ∈ (levPOf eG D.what₂.embLL (F.lvl true).P (F.lvl true).ψ).H ↔ reord π g ∈ (PsharpSym L.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧
      ∀ g hg hg', (levPOf eG D.what₂.embLL (F.lvl true).P (F.lvl true).ψ).chi ⟨g, hg⟩ =
        (PsharpSym L.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨reord π g, hg'⟩

def GrpAt (L : LevCh D T) (F : Face3 D A3) : Prop := ∃ eG : G ≃* G0 L.Pg D.R.r, RecL A3 L eG ∧ LevelsL A3 L eG F.lv2

abbrev BType (L : LevCh D T) (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) : Type :=
  Bridge.FamReal D A3.A cX.coef (fun i => (cV i).coef) (fun t => levEnvOf D.sp.X' L.βX (L.datXt t) pl (A3.A.ok t))
    (fun i t => levEnvOf (Vc D i) (L.βV i) (L.datVt i t) pl (A3.A.ok t))

structure BrgL (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E)
    (Sb : Finset (Pl D.host.E)) (B : BType A3 L cX cV pl) (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Prop where
  red_R : ∀ t (q : (levEnv D.sp.X' L.βX (L.datXt t)).Q),
    eG ((B.R t).act_tie.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf D.sp.X') : GL _ _))
  red_L : ∀ i t (q : (levEnv (Vc D i) (L.βV i) (L.datVt i t)).Q),
    eG ((B.L i t).act_tie.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _))
  tie : ∃ gramR c0R c0L, Bridge.FamTie B pl (Sb : Set (Pl D.host.E)) L.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L
  sb : Sb = L.Pg
  roots : ∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP))
  pl_onto : ∀ PP, Bridge.SplitOff PP (Sb : Set (Pl D.host.E)) → ∃ P, pl P = PP
  degR : ∀ t P, A3.A.heckeR t (P, 0) = 1 ∧ ∀ k, D.sp.X'.rank < k → A3.A.heckeR t (P, k) = 0
  degL : ∀ i t P, A3.A.heckeL i t (P, 0) = 1 ∧ ∀ k, (Vc D i).rank < k → A3.A.heckeL i t (P, k) = 0
  muVal : ∀ (i : Fin D.R.m) t, ∀ P ∈ A3.A.ok t,
    D.what₂.embLL (A3.A.muVal i t P : D.what₂.LL) = (((L.C.mu0 i * L.xiH t).val (pl P) : ℂˣ) : ℂ)
  etaVal : ∀ P ∈ A3.A.ok A3.A.μ0, D.what₂.embLL (A3.A.etaVal P : D.what₂.LL) = Formalism.L2.Host.etaAlg D.host L.C.eta (pl P)
  in_tie : Bridge.InertTie A3 plI (Sb : Set (Pl D.host.E)) L.Q
  in_onto : ∀ PP, Bridge.InertOff PP (Sb : Set (Pl D.host.E)) → ∃ Q, plI Q = PP
  in_R : ∀ t, Nonempty (Bridge.HeckeTie (Bridge.ratF D.sp.X') (B.R t).pres (A3.heckeRI t)
    (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2) (fun i => IsLabElt D.sp.X' (plI i.1) (labIn D.sp.X'.rank i.2))
    fun i => IsLocElt D.sp.X' (plI i.1))
  in_L : ∀ i t, Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc D i)) (B.L i t).pres (A3.heckeLI i t)
    (fun k => Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2) (fun k => IsLabElt (Vc D i) (plI k.1) (labIn (Vc D i).rank k.2))
    fun k => IsLocElt (Vc D i) (plI k.1))
  in_SF : ∀ v, v ∈ SF ↔ ∃ PP ∈ Sb, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

end Pieces


variable (D) in
def ModY : Prop :=
  (∀ j, Nonempty (DSModel (Yc D j) (parB (Ptw D) (min j D.R.m)))) ∧ Nonempty (DSModel D.sp.X' (parB (Ptw D) D.R.m))

def ModWAt (σ0 : D.what₂.LL →+* ℂ) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)) : Prop :=
  ∀ i τ a, (MW i σ0).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)


variable (D) in
def VPos : Prop := ∀ i, (Vc D i).IsPosDef

section Junk

def hZ (X : Type) [AddCommGroup X] [Module ℂ X] : HMod X where
  H := ℂ
  e := 0

end Junk

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]






end Formalism.IndefR.Seed

end
end
