module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

section Alg

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}

def Anchored (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ)
    (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  ∀ u, ∃ p b : ℂ, p ≠ 0 ∧ b ≠ 0 ∧ ∀ t (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K),
    c u t * Bs.v0.embedding ((fc X.zs).Dc.Pt u t φ F) * b =
      p * ⟪sEE (V (X.Θ t (X.jR t (eV t F)))), (fc X.zs).Sp.Pu u ((U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ

def UnitAt (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  (∀ u t, c u t ≠ 0) ∧ ∀ u w (k : K), Bs.v0.embedding k = c u (X.μ w) / c u Bs.μ0 → vw w k = 0

end Alg

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

abbrev rJ : Set (GA D (D.sp.Y 0)) :=
  levS (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))

abbrev rChi : GA D (D.sp.Y 0) → ℂ :=
  Formalism.IndefR.Lev.levChi (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))

def rowOf (e : W.Q.Rl.HE.H) : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) := PiTensorProduct.lift (W.Q.Rl.HE.e e)

def rowAt (t : W.P.T) (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  rowOf W (W.Q.Rl.Th t (W.Q.Rl.jX t (W.Q.F.eV (cxW W).zs t F)))

abbrev F0 (u : D.what₂.Word) : Formalism.L2.Forms.Forms0 D u := (W.R.T.cols.forms u).to0

structure BotDat (u : D.what₂.Word) where
  B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)
  b : GA D (D.sp.Y 0)
  a₀ : GA D (D.sp.X 0)
  a : GA D (D.sp.X 0)
  k : GA D (D.sp.Y 0)

variable {W}

variable (W)

structure BotHyp : Prop where
  hyp : HypAt W
  pins : RealPins W.Q
  see : SeeEx W.Q
  used : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t)
  idE : GlobalTheory.Core.Mi.IdE W.S.X
  gap : GlobalTheory.Count.GapGe W.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  fin : Formalism.L2.SG.PackageTie2.FinX W.S.Y

end GlobalTheory.MiTop

namespace GlobalTheory.MiTop

def PuNZ (D : D7) : Prop :=
  ∀ u, ∃ φ : (D.mem u).A.Mram, D.s.Pu u ((D.s_Cu u).symm ⟨φ.1, φ.2.1⟩) ≠ 0

end GlobalTheory.MiTop

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def inN (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {n : ℕ} (hn : V.rank = n) (g : GA D V) :
    D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ => (inB θ V B g τ).reindex (finCongr hn) (finCongr hn)

def castP {p q a b : ℕ} (hp : p = a) (hq : q = b) : PolF D q p →ₐ[ℂ] FP D.what₂.Tau a b :=
  MvPolynomial.rename fun v => (v.1, Fin.cast hq v.2.1, Fin.cast hp v.2.2)

structure RealD (c : Comm D) where

  N : ℕ → ℕ
  hN : ∀ j, j ≤ D.R.m → (c.X j).rank = N j

  NT : ℕ
  hT : c.T.rank = NT

  fr : ∀ j, c.Fr j ≃ FrN D (N j)

  lam : ∀ j, D.what₂.Tau → DomWeight (N j)
  n : ℕ → D.what₂.Tau → ℕ
  sS : ℕ → D.what₂.Tau → ℤ
  sD : ℕ → D.what₂.Tau → ℤ
  sc : ℕ → D.what₂.Tau → ℂ

  BT : D.what₂.Tau → Matrix (Fin c.T.rank) (Fin c.T.rank) ℂ
  sg : D.what₂.Tau → DomWeight NT

  J : SmT c.MT → GA D c.T → FrN D NT → ℂ

  low : ∀ n, n = D.R.m → ((FrN D (N n) → ℂ) →ₗ[ℂ] (FrN D NT → ℂ))

namespace RealD

variable {c : Comm D} (ρ : RealD c)

abbrev r (j : ℕ) (hj : j ≤ D.R.m) (g : GA D (c.X j)) := inN c.θ (c.X j) (c.x j).B (ρ.hN j hj) g

abbrev rT (g : GA D c.T) := inN c.θ c.T ρ.BT ρ.hT g

structure Is : Prop where
  uni : ∀ j hj, OntoUni fun k : GinfC (c.X j) => ρ.r j hj k.1
  uniT : OntoUni fun k : GinfC c.T => ρ.rT k.1
  rk : ∀ j, j < D.R.m → 0 < ρ.N j ∧ ρ.N j ≤ ρ.N (j + 1)
  sc : ∀ j τ, ρ.sc j τ ≠ 0
  n : ∀ j, j < D.R.m → ∀ τ, (ρ.n j τ : ℤ) = shiftOf (ρ.lam j) τ + ρ.sS j τ
  J : ∀ v, ρ.J v 1 ∈ ValC _ ρ.sg ∧ ∀ k ∈ GinfC c.T, ∀ z z', IsTr (ρ.rT k) z z' → ρ.J v k z' = ρ.J v 1 z
  low : ∀ n (h : n = D.R.m), ∃ hN : ρ.N n = ρ.NT + 1,
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (ρ.lam n τ) (ρ.sg τ)) ∧ BrEqv hN _ _ (ρ.lam n) ρ.sg (ρ.low n h) ∧
    (∃ Φ ∈ ValC _ (ρ.lam n), ρ.low n h Φ ≠ 0) ∧
    ∀ k ∈ GinfC c.T, ∀ τ, GlobalTheory.BranchFormula.IsBlock hN (ρ.r n h.le ((c.oT n h).emb (k, 1)) τ) (ρ.rT k τ) 1

end RealD

structure ClsK {c : Comm D} (ρ : RealD c) (t : Tup c) where
  cl : ∀ j, t.Ch j → Type
  [fin : ∀ j β, Fintype (cl j β)]
  U : ∀ j, t.Ch j → Subgroup (GA D (c.X j))
  chi : ∀ j β, U j β →* ℂˣ
  h : ∀ j β, cl j β → GA D (c.X j)

  val : ∀ j β, t.Col j → cl j β → FrN D (ρ.N j) → ℂ

  abelian₂ : ∀ j α γ, cl j α → cl (j + 1) γ → (FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ)

attribute [instance] ClsK.fin

namespace ClsK

variable {c : Comm D} {ρ : RealD c} {t : Tup c} (A : ClsK ρ t)

structure Forms : Prop where
  reps : ∀ j, j ≤ D.R.m → ∀ β, IsReps (c.X j) (A.U j β) (A.h j β)
  chi : ∀ j, j ≤ D.R.m → ∀ β, Continuous fun κ => ((A.chi j β κ : ℂˣ) : ℂ)
  valC : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ β a, A.val j β ψ a ∈ ValC _ (ρ.lam j)

  rd : ∀ j hj, ∀ ψ ∈ t.Ram j, ∀ β y, ∀ γ ∈ GQ (c.X j), ∀ a, ∀ k ∈ GinfC (c.X j), ∀ (κ : A.U j β) y',
    IsTr (ρ.r j hj k) (ρ.fr j y) y' → t.rd j β ψ y (γ * (A.h j β a * k) * κ.1) = (A.chi j β κ : ℂ) * A.val j β ψ a y'

def Real (_A : ClsK ρ t) : Prop :=
  ∀ j (hj : j + 1 ≤ D.R.m) α γ, ∀ k ∈ GinfC (c.X j), ∀ k' ∈ GinfC (c.X (j + 1)), ∀ P P',
    castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P' =
      mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k τ)⁻¹) (ρ.r (j + 1) hj k')
        (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P) →
    t.kom j (k, k') ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      (∏ τ, (ρ.r j (Nat.le_of_succ_le hj) k τ).det ^ ρ.sS j τ * (ρ.r (j + 1) hj k' τ).det ^ (-ρ.sD j τ)) •
        (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P'

def Lev : Prop :=
  ∀ j, j < D.R.m → ∀ α γ (κ : A.U j α) (κ' : A.U (j + 1) γ),
    t.kom j (κ.1, κ'.1) (comb c.ψ _ _ (t.dd j α γ) (c.vac j)) =
      (((A.chi j α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) γ κ' : ℂˣ) : ℂ)) • comb c.ψ _ _ (t.dd j α γ) (c.vac j)

def Core : Prop :=
  ∀ j (hj : j + 1 ≤ D.R.m) α γ a a' P,
    (volLev (c.x j).vol (A.U j α) : ℂ) *
        thetaKO (t.kom j) (A.h j α a) (A.h (j + 1) γ a') ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      t.cK j * A.abelian₂ j α γ a a' (mvZ (fun _ => 1) (fun τ => ρ.sc j τ • 1)
        (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P))

def Kval : Prop :=
  ∀ j, j < D.R.m → ∀ (hab : ρ.N j ≤ ρ.N (j + 1)), ∀ ψ ∈ t.Ram j,
    ∀ F : ∀ α, A.cl j α → PY D.what₂.Tau (ρ.N j), (∀ α a, F α a ∈ Vn (ρ.lam j) (ρ.n j)) →
      (∀ α a y, A.val j α ψ a y = evalAt y.1 (F α a) * ∏ τ, (y.1 τ).det ^ (-ρ.sS j τ)) →
      ∀ γ a' y', A.val (j + 1) γ (t.K j ψ) a' y' =
        ∑ α, ∑ a, ((stabOrd (A.U j α) (A.h j α a) : ℕ) : ℂ)⁻¹ * A.abelian₂ j α γ a a' (subY hab y'.1 (F α a)) *
          ∏ τ, (y'.1 τ).det ^ (-ρ.sD j τ)

def Is : Prop := A.Forms ∧ A.Real ∧ A.Lev ∧ A.Core ∧ A.Kval

end ClsK

structure ClsT {c : Comm D} (ρ : RealD c) (t : Tup c) where
  cl : Type
  [fin : Fintype cl]
  U : Subgroup (GA D c.T)
  h : cl → GA D c.T

  ell : ∀ n, n = D.R.m → t.Ch n → cl → t.CT → ((FrN D ρ.NT → ℂ) →ₗ[ℂ] ℂ)

attribute [instance] ClsT.fin

structure ClsT.Is {c : Comm D} {ρ : RealD c} {t : Tup c} (A : ClsT ρ t) : Prop where
  reps : IsReps c.T A.U A.h

  inv : ∀ n (h : n = D.R.m), ∀ ψ ∈ t.Ram n, ∀ (G : t.CT) v y β g, ∀ κ ∈ A.U,
    trc (t.eT n h β) (G.1 v) (g * κ) * t.rd n β ψ y ((c.oT n h).emb (g * κ, 1)) =
      trc (t.eT n h β) (G.1 v) g * t.rd n β ψ y ((c.oT n h).emb (g, 1))

  top : ∀ n (h : n = D.R.m) (G : t.CT) v β a, ∀ k ∈ GinfC c.T,
    trc (t.eT n h β) (G.1 v) (A.h a * k) = A.ell n h β a G (ρ.J v k)

  tail : ∀ n (h : n = D.R.m), ∀ ψ ∈ t.Ram n, ∀ G : t.CT,
    (volLev c.volT A.U : ℂ) * ∑ β, ∑ a, ((stabOrd A.U (A.h a) : ℕ) : ℂ)⁻¹ *
        A.ell n h β a G (ρ.low n h fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h a, 1))) =
      t.cP * t.tail n h ψ G

def ClsPinD {c : Comm D} {𝒯 : Type} (t : 𝒯 → Tup c) : Prop :=
  ∃ ρ : RealD c, ρ.Is ∧ ∀ s, (∃ A : ClsK ρ (t s), A.Is) ∧ ∃ A : ClsT ρ (t s), A.Is

namespace Sized

theorem castP_rank {p q : ℕ} (P : PolF D q p) : castP (D := D) (rfl : p = p) (rfl : q = q) P = P := by
  have : (fun v : FVar D q p => ((v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2) : FVar D q p)) = id := by funext v; rfl
  unfold castP
  rw [this]; exact MvPolynomial.rename_id_apply P

theorem castP_bijective {p q a b : ℕ} (hp : p = a) (hq : q = b) : Function.Bijective (castP (D := D) hp hq) := by
  subst hp; subst hq
  have : (castP (D := D) (rfl : p = p) (rfl : q = q) : _ → _) = id := funext castP_rank
  rw [this]; exact Function.bijective_id

end Sized

@[reducible] def Comm.onFrames (c : Comm D) (N : ℕ → ℕ) : Comm D := { c with Fr := fun j => FrN D (N j) }

@[reducible] def Tup.onFrames {c : Comm D} (t : Tup c) {N : ℕ → ℕ} (fr : ∀ j, j ≤ D.R.m → (c.Fr j ≃ FrN D (N j))) :
    Tup (c.onFrames N) where
  om := t.om
  omT := t.omT
  pt := t.pt
  ptT := t.ptT
  sBF := t.sBF
  sFB := t.sFB
  CC := t.CC
  CT := t.CT
  io := t.io
  ioT := t.ioT
  kom := t.kom
  Ch := t.Ch
  dd := t.dd
  e := t.e
  eT := t.eT
  Col := t.Col
  Ram := t.Ram
  S := t.S
  K := t.K
  rd := fun j β ψ z => if hj : j ≤ D.R.m then t.rd j β ψ ((fr j hj).symm z) else 0
  tail := t.tail
  cI := t.cI
  cV := t.cV
  cK := t.cK
  cP := t.cP

def ClsPinF {c : Comm D} {𝒯 : Type} (t : 𝒯 → Tup c) : Prop :=
  ∃ (N : ℕ → ℕ) (fr : ∀ j, j ≤ D.R.m → (c.Fr j ≃ FrN D (N j))), ClsPinD fun s => (t s).onFrames fr

section Frames

variable {c : Comm D} {N : ℕ → ℕ} (fr : ∀ j, j ≤ D.R.m → (c.Fr j ≃ FrN D (N j)))

variable {𝒯 : Type} {t : 𝒯 → Tup c}

end Frames

@[reducible] def RealD.onFrames {c : Comm D} (ρ : RealD c) : RealD (c.onFrames ρ.N) :=
  ⟨ρ.N, ρ.hN, ρ.NT, ρ.hT, fun _ => Equiv.refl _, ρ.lam, ρ.n, ρ.sS, ρ.sD, ρ.sc, ρ.BT, ρ.sg, ρ.J, ρ.low⟩

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw

variable {D : D7}

structure TDat (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) where

  p : ι → SplitPt D k
  I : List ι

  q : Unif k
  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1

  β : ∀ j i, Frame (p i) (c.X j) (Fin (c.X j).rank)
  Q : ∀ j, ι → Pair k (Fin (c.X j).rank)

  β₀ : ∀ j ρ h i, Frame (p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)
  M : ∀ j ρ h, Lat (c.bes j ρ h).V₀

  ζ₀ : Fin c.Lz.rank → D.host.E
  γ : ∀ i, Frame (p i) c.T (Fin c.T.rank)
  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (c.X n) (Fin c.T.rank ⊕ Fin 1)

variable {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

def TDat.Ram (o : TDat c k ι) (j : ℕ) : Set (GA D (c.X j) → ℂ) := {φ | IsContAut (c.X j) φ ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ}

def TDat.S (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) (φ : GA D (c.X j) → ℂ) : GA D (c.X j) → ℂ :=
  o.I.foldr (fun i φ' => sOp (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (ε j i) φ') φ

def TDat.mono (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ) (μ : (AE D)ˣ →* Circle) : ℂ :=
  (o.I.map fun i => (r i : ℂ) * chrPow μ ((o.p i).idele o.q.unit) (e i)).prod

@[reducible] def VCom.withT (v : VCom c) (Sad : ∀ j, (GA D (c.X j) → ℂ) → GA D (c.X j) → ℂ)
    (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) : VCom c := { v with Sad := Sad, op := op }

variable (v : VCom c) (o : TDat c k ι)

structure GoodAt (x : Pl D) : Prop where
  bf : ∀ j ρ h, GoodBF c.ψ (c.B j ρ h) (c.J j ρ h) (v.N j) (o.M j ρ h) (v.N (j + 1)) (c.x (j + 1)).L x
  fb : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), AdaptFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (v.N (j + 1))
    (c.x (j + 1)).L (v.N (j + 1 + 1)) (o.M (j + 1 + 1) σ (idx_step h)) x

structure SplitAt (x : Pl D) : Prop where
  core : ∀ j ρ h, ∃ LL, IsSelfDualC (c.bes j ρ h).L LL ∧ OrthAt (c.bes j ρ h).o (o.M j ρ h) (c.x j).L LL x
  top : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (LL : Lat (c.bes j 0 h).L) (LZ : Lat c.Lz),
    IsSelfDualC _ LL ∧ IsSelfDualC _ LZ ∧ OrthAt (c.bes j 0 h).o (o.M j 0 h) (c.x j).L LL x ∧
    OrthAt (c.oT (j + 1 + 1) h) (c.x (j + 1 + 1)).L v.NT LZ x ∧
    ∀ w ∈ latO (c.X (j + 1)) c.Lz ((c.x (j + 1)).L : Set _) (LZ : Set _) (· = x),
      kap (v.τ j h) (c.X (j + 1)) w ∈ latO (c.bes j 0 h).L (c.X (j + 1)) (LL : Set _) ((c.x (j + 1)).L : Set _) (· = x)

structure PreT : Prop where
  nodup : o.I.Nodup
  all : ∀ i, i ∈ o.I
  inj : Function.Injective fun i => (o.p i).v
  tP : ∀ x, x ∈ v.tP ↔ ∃ i, x = (o.p i).v
  char : ∀ i, (o.p i).IsChar c.ψ (o.χ i) ∧ (o.p i).UnitAA
  latT : ∀ j, j ≤ D.R.m → ∀ i, (o.β j i).IsLat (c.x j).L (o.Q j i).lat
  line : IsLineVec c.Lz o.ζ₀
  tau : ∀ j h, (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram

  lam : ∀ j h, ∃ lam : D.host.E, v.τ j h *ᵥ o.ζ₀ = lam • (c.bes j 0 h).ζ ∧
    ∀ i, valuation k ((o.p i).pr (incA D lam)) = 1 ∧ valuation k ((o.p i).pr (incA D (star lam))) = 1
  normT : ∀ i, valuation k ((o.p i).pr (incA D (star o.ζ₀ ⬝ᵥ c.Lz.gram *ᵥ o.ζ₀))) = valuation k ((o.q.1 : 𝒪[k]) : k)

  topT : ∀ n (h : n = D.R.m) i, IsSumFrame (c.oT n h) o.ζ₀ (o.γ i) (o.γ₀ n h i) ∧
    ∃ (Λ : Submodule 𝒪[k] (Fin c.T.rank → k)) (s : 𝓀[k]ˣ), (o.γ i).IsLat v.NT Λ ∧
      (∀ y, y ∈ (o.Q n i).ker ↔ ((o.γ₀ n h i).b' * (o.β n i).b) *ᵥ y ∈ lastKer Λ) ∧
      (o.Q n i).HasVal (((o.β n i).b' * (o.γ₀ n h i).b) *ᵥ (o.q.inv • avec k (Fin c.T.rank) 1 1)) s

structure ShapeOff : Prop where
  pre : PreT v o
  good : ∀ x, GoodAt v o x
  split : ∀ x, x ∉ v.tP → SplitAt v o x
  glued : ∀ j ρ h i, GluedCore (c.B j ρ h) (o.M j ρ h) o.q (o.β j i) (o.β₀ j ρ h i) (o.Q j i)
  rep : ∀ j, j < D.R.m → ∀ f, Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L (· ∈ v.tP) f →
    OverAll c.ψ (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
      (comb c.ψ _ _ (v.dT j) f)
  ram : ∀ j, v.RamAd j = o.Ram j

structure Tup.UnrOn (t : Tup c) (P : Pl D → Prop) : Prop where
  bf : ∀ j ρ h x, P x → UnrAt (t.sBF j ρ h) x
  fb : ∀ j σ h x, P x → UnrAt (t.sFB j σ h) x
  top : ∀ j h, ∃ χS χT, IsWeilDatumO c.ψ _ _ χS χT (t.omT j h) ∧ ∀ x, P x → CharUnramAt D χS x ∧ CharUnramAt D χT x

def Tup.UnrK (t : Tup c) (P : Pl D → Prop) : Prop :=
  ∀ j, j < D.R.m → ∃ χS χT, IsWeilDatumO c.ψ _ _ χS χT (t.kom j) ∧ ∀ x, P x → CharUnramAt D χS x ∧ CharUnramAt D χT x

def OffOfShape (D : D7) : Prop :=
  ∀ (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
    c.Is → v.Is → ShapeOff v o → ∀ (t : Tup c) (w : VTup t), t.Is → Disjoint w.Q v.tP → t.UnrOn (offP v w) → OffLaw v w

def VacOfShape (D : D7) : Prop :=
  ∀ (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
    c.Is → v.Is → ShapeOff v o → ∀ t : Tup c, VacLaw (t := t) v

def TOfShape (D : D7) : Prop :=
  ∀ (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
    c.Is → v.Is → ShapeOff v o →
    ∃ (ε : ℕ → ι → 𝓀[k]ˣ) (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ℕ → ι → ℝ) (e : ℕ → ι → ℤ),
      (∀ j i, 0 < r j i) ∧ (v.withT (o.S ε) op).Is ∧
      ∀ (t : Tup c) (w : VTup t), t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) →
        (∀ j ρ h, w.cT j = o.mono (r j) (e j) (t.sBF j ρ h).χW) → TLaw (v.withT (o.S ε) op) w

def ShapeEx (D : D7) : Prop :=
  ∀ (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
    c.Is → Disjoint v.gP v.tP → IsSelfDualC c.T v.NT → PreT v o → (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j)) →
    (∀ x ∈ v.gP, GoodAt v o x ∧ SplitAt v o x) →
    (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT n h) (c.x n).L v.NT LZ x) →
    ∃ (N : ∀ j, Lat (c.V j)) (dT : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀)
      (β₀ : ∀ j ρ h i, Frame (o.p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)),
      (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j) ∧ ∀ x ∈ v.gP, latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) ∧
      (∀ j ρ h, ∀ x ∈ v.gP, latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) ∧
      (∀ j, CombAt (· ∈ v.tP) (dT j)) ∧
      ShapeOff { v with N := N, dT := dT, RamAd := o.Ram } { o with M := M, β₀ := β₀ }

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
noncomputable section

namespace GlobalTheory.Core.Rk.IP.Model

open scoped ComplexConjugate Matrix NNReal ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_cartan {m : Type} [Fintype m] [DecidableEq m] {n : ℕ} (e : Fin n ≃ m) {C : Matrix m (Fin n) ℂ}
    {J : Matrix m m ℂ} {G : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hJ' : Jᴴ = J) (hG : IsUnit G.det)
    (h : Cᴴ * J * C = G) : ∃ s, IsCartanInv G s ∧ C * s = J * C := by
  have h1 : G⁻¹ * Cᴴ * J * C = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Cᴴ, h, Matrix.nonsing_inv_mul _ hG]
  generalize G⁻¹ * Cᴴ * J = C' at h1
  have h2 : C * C' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  have h3 : C * (C' * J * C) = J * C := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h4 : G * (C' * J * C) = Cᴴ * C := by
    rw [← h, Matrix.mul_assoc, h3, Matrix.mul_assoc, ← Matrix.mul_assoc J, hJ, Matrix.one_mul]
  refine ⟨C' * J * C, ⟨?_, ?_, ?_⟩, h3⟩
  · rw [Matrix.mul_assoc (C' * J), h3, Matrix.mul_assoc C', ← Matrix.mul_assoc J, hJ, Matrix.one_mul, h1]
  · rw [Matrix.mul_assoc, h4, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_mul, hJ', h]
  · rw [h4]
    refine Matrix.PosDef.conjTranspose_mul_self _ fun x y hxy => ?_
    have := congrArg (C' *ᵥ ·) hxy
    simpa [Matrix.mulVec_mulVec, h1] using this

theorem gramAt_unit (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det _ _).symm
  rw [this]
  exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).map _

theorem isSplit_two (v : FinPl D) (h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal) : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    haveI := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rcases (LFun.exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w, hw⟩
  · exact hs
  · exfalso
    unfold Formalism.UG.IsInertAt at hw
    obtain ⟨ω, k, hω, hc⟩ := GlobalTheory.SplitIdem.exists_omega D
    let c : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom D.sp.cm.sig.toRingHom
    have hst : ∀ x ∈ w.asIdeal, c x ∈ w.asIdeal := by
      have : w.asIdeal ≤ w.asIdeal.comap c := by
        conv_lhs => rw [← hw]
        refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
        have e : c (algebraMap _ _ a) = algebraMap _ _ a := Subtype.ext (D.sp.cm.sig.commutes a)
        rw [Ideal.mem_comap, Ideal.mem_comap, e, ← hw]
        exact Ideal.mem_map_of_mem _ ha
      exact this
    have hcω : c ω = 1 - ω := RingOfIntegers.ext (by
      change star (ω : D.host.E) = _
      rw [GlobalTheory.SplitIdem.star_eq_conj, hc]; simp)
    have h2' : (2 : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← hw, ← map_ofNat (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) 2]
      exact Ideal.mem_map_of_mem _ h2
    have hp : ω * (1 - ω) = 2 * k := RingOfIntegers.ext (by
      push_cast at hω ⊢
      simp only [map_mul, map_sub, map_one, map_ofNat, map_natCast]
      linear_combination -hω)
    have hone : ω ∈ w.asIdeal → False := fun h =>
      w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by have := add_mem h (hcω ▸ hst ω h); rwa [add_sub_cancel] at this))
    rcases w.isPrime.mem_or_mem (hp ▸ Ideal.mul_mem_right _ _ h2') with h | h
    · exact hone h
    · have := hst _ h
      rw [map_sub, map_one, hcω, sub_sub_cancel] at this
      exact hone this

theorem isSphOff_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : RealMat S} {sT : RealMat T}
    {LS : Lat S} {LT : Lat T} {Φ : WO S T → ℂ} (h : IsVacO ψ θ S T sS sT LS LT Φ) (Sf : Finset (FinPl D)) :
    IsFockVec ψ θ S T sS sT Φ ∧ IsSphOff ψ S T LS LT Sf Φ ∧ Φ ≠ 0 := by
  have hle : latO S T LS LT (fun v => v ∉ Sf) ≤ latO S T LS LT fun _ => True :=
    AddSubgroup.closure_mono fun _ ⟨α, h1, _, h3⟩ => ⟨α, h1, fun _ h => absurd trivial h, h3⟩
  refine ⟨⟨h.2.theta, 1, fun l hl => ?_⟩, ⟨fun u hu => h.2.lat.1 u (hle hu), fun e he u hu => h.2.lat.2 e he u (hle hu)⟩, ?_⟩
  · obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
    exact h.2.fock p.1 p.2
  · rintro rfl
    obtain ⟨⟨p, hp⟩, h'⟩ := h.2.norm
    simpa [nrm2] using h' p hp

section Coef

variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χA χB : (AE D)ˣ →* Circle} {om : WRep A B} {ν : Measure (WO A B)}
  {𝓕 : Set (WO A B)} {Φ₁ Φ₂ : WO A B → ℂ}

end Coef

end GlobalTheory.Core.Rk.IP.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaDens

variable {D : D7}

def Sobolev₂ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T S' T' : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (μ' : Measure (WO S' T')) (𝓕' : Set (WO S' T')) (Z : (WO S T → ℂ) → WO S' T' → ℂ) : Prop :=
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ U' : AddSubgroup (WO S' T'), IsOpen (U' : Set (WO S' T')) ∧
    (∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, Z f ∈ GlobalTheory.Size.thetaLevel ψ S' T' U') ∧
    ∀ d : ℕ, ∃ (d' : ℕ) (C : ℝ≥0), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, sobO ψ θ μ' 𝓕' d (Z f) ≤ C * sobO ψ θ μ 𝓕 d' f

theorem sobCont_id (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) :
    Sobolev₂ ψ θ μ 𝓕 μ 𝓕 id := fun U hU => ⟨U, hU, fun _ h => h, fun d => ⟨d, 1, fun _ _ => by simp⟩⟩

def SobBdd (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (L : (WO S T → ℂ) → GA D S → ℝ≥0∞) : Prop :=
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ K : Set (GA D S), IsCompact K →
    ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x ∈ K, L f x ≤ C * sobO ψ θ μ 𝓕 d f

end GlobalTheory.ThetaDens

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.CornerCoordinateAutomatic
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mi

namespace GlobalTheory.MiS.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem used_base (P : RowSideFamily ex) : Formalism.IndefR.RecTie.Used0 D (P.I.tup P.A3.A.μ0) := Or.inl P.tied.div.tup.mu0

theorem mu_eq_of_heq (P : RowSideFamily ex) {Zs : DefSub P.A3.fam3.amb3} (h : Zs = P.Zs)
    (S : IndefData (P.A3.side3 P.P0 P.ψ0 Zs)) (hS : HEq S P.S0) : S.μ = P.S0.μ := by
  subst h
  rw [eq_of_heq hS]

end GlobalTheory.MiS.Check

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Diag

def OneOn (S : Set ℝ) (gen : Bool) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (if gen then (Y.tO u u).genSet else (Y.tO u u).ngSet)) ≤
        gamL D large₂.sc.L C * ddC X Y u u

def SDiagOn (S : Set ℝ) (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), 1 ≤ large₂.CGam → TrueS D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → TFrameAt D →
      ∀ u, SDiagAt D u (gamL D large₂.sc.L CD) c

def GamRange (D : D7) (L : ℝ) : Prop :=
  (D.R.m : ℝ) ^ 5 * D.R.f * L ≤ Real.log (AdmissibleBoundsFromSource.Gam D) ∧ 8 * Real.log (AdmissibleBoundsFromSource.Gam D) ≤ D.R.k

theorem pow_five_mul_f_pos (D : D7) : (0 : ℝ) < (D.R.m : ℝ) ^ 5 * D.R.f := by
  have hf : 0 < D.R.f := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    unfold Ranks.f; omega
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  positivity

end GlobalTheory.Core.Diag
end
end
