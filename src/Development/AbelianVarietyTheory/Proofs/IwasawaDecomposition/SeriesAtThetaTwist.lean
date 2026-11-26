module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsSameGeometricHalf
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewTwistLamFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealMoveOfLink

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtThetaTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.Up.SerCp
open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions.TH _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ExportSeries hiding Base

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false

section L1
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)

end L1

section L2
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)

end L2

private abbrev lt {B : Base} {C : Cols B} (c : Late B C) (n : NStage B C c.W) : Late B C := ⟨c.W, c.V, c.S, n, c.G⟩

section L2
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {c : Late B C} {a : NStage B C c.W} (b : NStage B C c.W)

section
variable {N : NData (lt c a).D.R (lt c a).D.host (lt c a).D.what₂} {X : NTw (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N}

end

section
variable {N : NData (lt c a).D.R (lt c a).D.host (lt c a).D.what₂} {X : NTw (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N} {ρ : Setup X}
  {Y : NExp (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N X} {i : X.Tw} {j : Fin (lt c a).D.R.m} {s : Bool} {rd : Rd ρ Y i j s}

end

end L2

section L3
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {c : Late B C} {a : NStage B C c.W} (b : NStage B C c.W)
  {Γ : Type} [i1 : Group Γ] [i2 : Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 (lt c a).D.what₂.LL Γ Pl0 I0 (List ℕ) T (lt c a).D.R.m} {Ks : Type} [i3 : Field Ks] [i4 : NumberField Ks]
  [iK : Algebra Ks (lt c a).D.what₂.LL] {Rl : RealDat3 (lt c a).D A3 Ks}
  {v₀ : ∀ (j : Fin (lt c a).D.R.m) (σ : (lt c a).D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec} {j : Fin (lt c a).D.R.m}
  {X : ExportSeries.Base (Vc (lt c a).D j) (Wc (lt c a).D j)} {ν : ℂ}

end L3

section L4
open GlobalTheory.SeriesTie
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  (x : St P) (l : SeriesLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp)

end L4

end GlobalTheory.HeightCounting.Up.SerCp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeptChoiceUpperLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowReadingsSameRowsIdentifyDefiniteForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowReadingsSameRowsIdentifyDefiniteForms
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.R3.Rw.JmtUp

theorem agree {D : D7} {T : Type} {W : Type} [AddCommGroup W] [Module ℂ W] (U U' : D.what₂.Tup → Prop) {n : Fin D.R.m → T → ℕ}
    (tup tup' : T → D.what₂.Tup) (e1 : HEq tup' tup)
    (eM : ∀ (i : Fin D.R.m) t, (Fin (n i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (eM' : ∀ (i : Fin D.R.m) t, (Fin (n i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup' t) ((i : ℕ) + 1)) (e2 : HEq eM' eM)
    (i : Fin D.R.m) (val : ∀ t, (Fin (n i t) → D.what₂.LL) → W)
    (g : ∀ μ, U μ → D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] W) (g' : ∀ μ, U' μ → D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] W)
    (hs : ∀ t, Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t (Pi.single k 1))) = ⊤)
    (hg : ∀ t h y, g (tup t) h (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t y)) = val t y)
    (hg' : ∀ t h y, g' (tup' t) h (D.what₂.jMt (tup' t) ((i : ℕ) + 1) (eM' i t y)) = val t y)
    (μ : D.what₂.Tup) (τ : T) (hτ : tup τ = μ) (h : U μ) (h' : U' μ) (x : D.what₂.Mt μ ((i : ℕ) + 1)) : HEq (g' μ h' x) (g μ h x) := by
  cases e1
  cases e2
  subst hτ
  refine heq_of_eq (LinearMap.congr_fun (LinearMap.ext_on_range (hs τ) fun k => ?_) x)
  rw [hg, hg']

section Side

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

abbrev Val (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0) (i : Fin D.R.m) : Type :=
  GA D ((toLiftReal R F Y.tupT Y.hm Y.hTop Y.hinj).V i) → (toLiftReal R F Y.tupT Y.hm Y.hTop Y.hinj).TauV i

noncomputable def gOf (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0) (i : Fin D.R.m) (μ : D.what₂.Tup) (h : Used0 D μ) :
    D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] Val Y i := (Submodule.subtype _).comp (Y.IL.jMt μ h i).toLinearMap

theorem side (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0) (i : Fin D.R.m) (U : D.what₂.Tup → Prop) (tup : T → D.what₂.Tup) (e1 : HEq Y.tup tup)
    (eM : ∀ (i : Fin D.R.m) t, (Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (e2 : HEq Y.eMt eM) (g : ∀ μ, U μ → D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] Val Y i)
    (hs : ∀ t, Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t (Pi.single k 1))) = ⊤)
    (hg : ∀ t h y, g (tup t) h (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t y)) =
      R.extV i t (R.jV i t (GlobalTheory.Mem.R3.liftForm A3.A F.P0 F.ψ0 i t y)))
    (μ : D.what₂.Tup) (τ : T) (hτ : tup τ = μ) (h : U μ) (h' : Used0 D μ) (x : D.what₂.Mt μ ((i : ℕ) + 1)) :
    HEq (gOf Y i μ h' x) (g μ h x) :=
  agree U (Used0 D) tup Y.tup e1 eM Y.eMt e2 i _ g (gOf Y i) hs hg (fun t h y => Y.mtRead i t h y) μ τ hτ h h' x

end Side

theorem jMt_rowsSame : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1 := by
  intro K B f T w Z Wt S' N h p0 t p0' t' hs μ hμ hμ' i x
  have H := side t'.r.Y ((by with_unfolding_all exact (i :)))
  have a1 := hs.tup
  have a2 := hs.eMt
  cases t' with | mk hX' r' exAt' inGeo' grpAt' grp' mu' exact' untw' emt0' emt' etaF' rowInt' idx' => ?_
  cases r' with | mk z' holds' Y' ZZ' tupix' => ?_
  cases z' with | mk Xg' tr' core' alg_eq' R' cG' geo' pins' lev' idG' good' muz' le' ks' => ?_
  rename_i alg'
  have e1 : Xg' = t.r.z.Xg := hs.Xg
  have e2 : tr' = t.r.z.tr := hs.tr
  subst e1 e2
  have e3 : core' = R3.Tr.coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) t.r.z.core := eq_of_heq hs.core
  subst e3
  have e4 : alg' = t.r.z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.D Z).what₂.embLL.injective
    exact (alg_eq' y).trans (t.r.z.alg_eq y).symm
  subst e4
  have e5 : R' = R3.Tr.real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.R := eq_of_heq hs.R
  subst e5
  have e6 : cG' = t.r.z.cG := eq_of_heq hs.cG
  subst e6
  exact (by with_unfolding_all exact ((H ((by with_unfolding_all exact ((Formalism.IndefR.RecTie.Used0 (w.D Z)) :))) ((by with_unfolding_all exact (t.r.Y.tup :))) ((by with_unfolding_all exact (a1 :))) ((by with_unfolding_all exact (t.r.Y.eMt :))) ((by with_unfolding_all exact (a2 :))) ((by with_unfolding_all exact ((gOf t.r.Y i) :)))
    ((by with_unfolding_all exact ((fun τ => (t.r.Y.formsL i τ).span) :))) ((by with_unfolding_all exact ((t.r.Y.mtRead i) :))) ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact ((t.r.Y.tupT μ) :))) ((by with_unfolding_all exact ((t.r.Y.tupTie μ hμ) :))) ((by with_unfolding_all exact (hμ :)))
    ((by with_unfolding_all exact (hμ' :))) ((by with_unfolding_all exact (x :)))) :))

end GlobalTheory.Mem.R3.Rw.JmtUp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowReadingsSameRowsIdentifyDefiniteFormsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowReadings_sameRows_identify_definiteForms : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1 := by
  first | exact @GlobalTheory.Mem.R3.Rw.JmtUp.jMt_rowsSame | exact GlobalTheory.Mem.R3.Rw.JmtUp.jMt_rowsSame | (intros; apply GlobalTheory.Mem.R3.Rw.JmtUp.jMt_rowsSame <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000

theorem tupTied_ext {D : D7} {cf : CharFrame D} {C : NChoice D} {p q : TupTied D cf C} (h1 : p.xi = q.xi) (h2 : p.psi = q.psi) :
    p = q := by
  cases p; cases q; cases h1; cases h2; rfl

section
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {nch : NChoice (w.D Z)}
  {xd : ThData (w.D Z)}

theorem nchT_up (n : NchT w Z Wt nch) : Nonempty (NchT w (upL Z S' N h) Wt (nchUp S' N h nch)) :=
  ⟨{ tp := {
       xi := by with_unfolding_all exact (n.tp.xi :)
       xi_inj := by with_unfolding_all exact (n.tp.xi_inj :)
       xi_fin := by with_unfolding_all exact (n.tp.xi_fin :)
       xi_triv := by with_unfolding_all exact (n.tp.xi_triv :)
       xi_tame := by with_unfolding_all exact (n.tp.xi_tame :)
       psi := by with_unfolding_all exact (n.tp.psi :)
       trueColumnChoices_heckeChar_reference_eq_one := by with_unfolding_all exact (n.tp.trueColumnChoices_heckeChar_reference_eq_one :)
       xi_star := by with_unfolding_all exact (n.tp.xi_star :)
       xi_star' := by with_unfolding_all exact (n.tp.xi_star' :)
       xi_tw := by with_unfolding_all exact (n.tp.xi_tw :)
       psi_is := by with_unfolding_all exact (n.tp.psi_is :)
       psi_un := by with_unfolding_all exact (n.tp.psi_un :) }
     xi := by with_unfolding_all exact (n.xi :)
     psi := by with_unfolding_all exact (n.psi :)
     tie := {
       twOf_eq := by with_unfolding_all exact (n.tie.twOf_eq :)
       twSide_eq := by with_unfolding_all exact (n.tie.twSide_eq :)
       Q_eq := by with_unfolding_all exact (n.tie.Q_eq :)
       psi_eq := by with_unfolding_all exact (n.tie.psi_eq :)
       embedding_baseField_condition := by with_unfolding_all exact (n.tie.embedding_baseField_condition :) }
     Q := n.Q
     chrPsi := by with_unfolding_all exact (n.chrPsi :) }⟩

theorem kept_up (nch : NChoice (w.D Z)) : Kept nch (nchUp S' N h nch) := by
  refine ⟨?_, ?_, ?_, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩ <;> constructor <;> first | rfl | exact HEq.rfl

theorem goodO_up (g : GoodO (w.D Z) nch xd) : GoodO (w.D (upL Z S' N h)) (nchUp S' N h nch) (xdUp S' N h xd) := by
  obtain ⟨⟨E, N0, S⟩, h1, h2, h3⟩ := g.tw
  cases h1
  exact ⟨⟨⟨twEOf (xdUp S' N h xd), N0, S⟩, rfl, (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :))⟩, g.sep⟩
end

end GlobalTheory.LayerMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBoundOfPrimitive
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SeriesStep
open GlobalTheory.Mem.R3.Tr
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem listPin_oTw (x : St P) (N : TwNew (Dof x))
    (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
    (c b : ℝ) {I : Type}
    (Lc : Formalism.IndefR.Links.LevCh (Dof x) I) (h : ListPin (Dof x) Lc c b) :
    ListPin (w.st (oTw x N).Z).toD7 (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z Lc) c b := by
  obtain ⟨G, h1, h2⟩ := h
  exact ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x N).Z G) :)), ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩, (by with_unfolding_all exact ((hN _ h2) :))⟩

theorem listSt_oTw (cDep : ℝ) (x : St P) (N : TwNew (Dof x))
    (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
    (x' : St P) (ho : x'.o = oTw x N)
    (hR : HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh))
    (h : ListSt cDep x) : ListSt cDep x' := by
  unfold ListSt
  generalize x'.m.z.R.toRealDat.toLevCh = Lc' at hR ⊢
  revert Lc'
  unfold Dof
  rw [ho]
  intro Lc' hR
  rw [eq_of_heq hR]
  exact listPin_oTw x N hN _ _ _ h

end GlobalTheory.HeightCounting.Up.SeriesStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMove
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeoExtN
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.StateChecks

namespace GlobalTheory.HeightCounting.SerMove.ReGeo

variable {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

set_option maxHeartbeats 4000000 in
theorem geo_copy {Z Z' : w.Lt} (z₀ : Dat (w.st Z) w.I hX T Wt) (z : Dat (w.st Z') w.I hX T Wt) (h1 : z.Xg = z₀.Xg)
    (h2 : z.tr = z₀.tr) (h3 : HEq z.core (coreJ (a := Z) Z' z₀.core)) (h4 : HEq z.R (real3 (a := Z) Z' (iK := z₀.alg) z₀.R))
    (hg : GlobalTheory.RealGeo.InGeo z₀.geo) :
    ∃ g : GlobalTheory.RealGeo.GeoHalf z.core z.R.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo g ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z₀ z' → ExtN { z with geo := g } z') ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z' z₀ → ExtN z' { z with geo := g }) := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4 ⊢
  subst h1 h2
  obtain rfl : core = coreJ (a := Z) Z' z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg (a := Z) Z' z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR (a := Z) Z' z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR (a := Z) Z' z₀)) :))))
  refine ⟨?_, ?_, ?_, ?_⟩
  · with_unfolding_all
      exact GlobalTheory.Mem.R3.Tr.geoHalf (a := Z) Z' (iK := z₀.alg) z₀.geo
  · with_unfolding_all
      exact GlobalTheory.Mem.R3.Tr.inGeo_tr (a := Z) Z' (iK := z₀.alg) hg
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }

end GlobalTheory.HeightCounting.SerMove.ReGeo

namespace GlobalTheory.HeightCounting.SerMove

theorem exists_geo_extN : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}, Ext P.z P'.z → ∀ (x : St P) (x' : St P'), ∃ (g : Geo x) (g' : Geo x'), GlobalTheory.RealGeo.InGeo g ∧ GlobalTheory.RealGeo.InGeo g' ∧ ExtN (datAt x g) (datAt x' g') := by
  intro K B B' f f' T T' w w' P P' e x x'
  obtain ⟨g, hg, hL, -⟩ := ReGeo.geo_copy (Z := P.Z₀) (Z' := x.o.Z) P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :))) P.inGeo
  obtain ⟨g', hg', -, hR⟩ :=
    ReGeo.geo_copy (Z := P'.Z₀) (Z' := x'.o.Z) P'.z x'.m.z x'.m.Xg x'.m.tr ((by with_unfolding_all exact (x'.copy.core :))) ((by with_unfolding_all exact (x'.copy.R :))) P'.inGeo
  exact ⟨g, g', hg, hg', hR _ (hL _ e.extN)⟩

end GlobalTheory.HeightCounting.SerMove
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove GlobalTheory.HeightCounting.SideCopy GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.SerGlue

theorem copyAll_ex {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}
    (h : CopyN D N ι e) (hp : HEq D.naut.plGw D'.naut.plGw) {D'' : D7} (hD : D'' = N.toD7) :
    ∃ ι' e', CopyAll D D'' ι' e' := by
  subst hD
  exact ⟨ι, e, h.cp, h.jL, h.s2, h.lamG, h.Xv, h.qs, hp⟩

theorem fr_same {A A' : Pre} (h : A' = A) {f : Top.Fr A} {f' : Top.Fr A'} (hf : HEq f' f) :
    HEq f.mu0 f'.mu0 ∧ HEq f.eta f'.eta ∧ HEq f.del f'.del ∧ HEq f.del' f'.del' := by
  subst h; cases hf; exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem choice_heq {A A' : Pre} (h : A' = A)
    {p : HeightOneSpectrum (𝓞 (maximalRealSubfield A.host.E)) → HeightOneSpectrum (𝓞 A.host.E)}
    {p' : HeightOneSpectrum (𝓞 (maximalRealSubfield A'.host.E)) → HeightOneSpectrum (𝓞 A'.host.E)}
    (hp : ∀ v, NG.OverPl (p v) v) (hp' : ∀ v, NG.OverPl (p' v) v)
    {s : HeightOneSpectrum (𝓞 A.host.F) → HeightOneSpectrum (𝓞 A.host.E)}
    {s' : HeightOneSpectrum (𝓞 A'.host.F) → HeightOneSpectrum (𝓞 A'.host.E)} (hs : HEq s' s)
    (r : Set.range p = Set.range s) (r' : Set.range p' = Set.range s') : HEq p p' := by
  subst h; cases hs
  refine heq_of_eq (funext fun v => ?_)
  obtain ⟨u, hu⟩ : p v ∈ Set.range p' := by rw [r', ← r]; exact ⟨v, rfl⟩
  have h1 := hp' u
  rw [hu] at h1
  obtain rfl : u = v := HeightOneSpectrum.ext (h1.symm.trans (hp v))
  exact hu.symm

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B}
  {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}

theorem bigHost_st (hO : K.Over B.toPre)
    (hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV)
    (x : St P) : BigHost (Dof x) :=
  ⟨(hB (w.st x.o.Z) hO).1, GlobalTheory.HeightCounting.FirstFacts.vstd_of_over (w.st x.o.Z) hO, (hB (w.st x.o.Z) hO).2⟩

end GlobalTheory.HeightCounting.SerGlue

end
end
