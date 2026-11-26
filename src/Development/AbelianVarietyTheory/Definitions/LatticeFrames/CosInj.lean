module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Formalism.LocalToGlobal.KernelLattices.TopPin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl

variable {D : D7} {c : Comm D}

def SameOrb {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n] (J : Subgroup (GL (n ⊕ Fin 0) k))
    (M : Submodule 𝒪[k] (n → k)) (yb yb' : (n → k) ⧸ M) : Prop :=
  ∃ g ∈ J, ∃ y, Submodule.Quotient.mk y = yb ∧ Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) = yb'


set_option maxHeartbeats 4000000 in
structure QAt (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  unit : q.UnitAA
  ψk : AddChar k Circle
  char : (ofSplit q).IsChar c.ψ ψk
  cond : HasConductor ψk 1

  s : ℕ
  hs : s + 1 + 1 = D.R.m
  X : ℕ → Type
  [fX : ∀ j, Fintype (X j)]
  [dX : ∀ j, DecidableEq (X j)]
  Z : Type
  [fZ : Fintype Z]
  [dZ : DecidableEq Z]

  T : Chain k s X Z
  reg : T.Regular
  laws : T.Laws
  bas : ∀ j d h, T.bas j d h = 1
  le : ∀ j d h, (T.lev j d h).J ≤ KO k _
  leT : T.levTop.J ≤ KO k Z
  openT : IsOpen (T.levTop.J : Set (GL Z k))
  mu : ∀ j, j ≤ s + 1 → (ofSplit q).IsComp (χ j)⁻¹ (T.mu (j + 1)) ∧ IsOpen ((T.mu (j + 1)).ker : Set kˣ)

  FX : ∀ j, j ≤ s + 1 → Frame k (c.X j).rank (X j)
  FT : Frame k c.T.rank Z
  FM : Frame k (c.X (s + 1 + 1)).rank (Z ⊕ Unit)
  FY : ∀ j d, j + d = s + 1 → Frame k (c.V j).rank (X j ⊕ Fin d)
  sc : ℕ → k
  sc_ne : ∀ j, sc j ≠ 0
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi
  bes : ∀ j ρ h d (hd : j + d = s + 1), (ofSplit q).IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) (FY j d hd)
  jac : ∀ j ρ h d (hd : j + 1 + d = s + 1), (ofSplit q).IsJacFrame (c.J j ρ h) (sc j) ((ofSplit q).hz (c.B j ρ h))
    (FX (j + 1) (by omega)) (FY (j + 1) d hd)
  z₀ : Fin c.Lz.rank → k
  last : FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  tau : ∀ h, (v.τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i)
  latY : ∀ j d hd (y : X j ⊕ Fin d → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FY j d hd).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.V j) (v.N j) (· = q.v)
  latT : ∀ y : Z → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV c.T v.NT (· = q.v)

  gl : ∀ j d, j + d = s + 1 → GL (X j ⊕ Fin d) k →* GA D (c.V j)
  gl_loc : ∀ j d hd g, (ofSplit q).IsLoc (FY j d hd) (gl j d hd g) g

  A : RepFam k s X
  reps : T.IsRepSystem A ψk ν
  Ch : ℕ → Type
  [fC : ∀ j, Fintype (Ch j)]
  rep : ∀ j d, j + d = s → Ch j → GL (X j ⊕ Fin (d + 1)) k
  rep_bij : ∀ j d h, Set.BijOn (rep j d h) Set.univ (A j d h)
  c₁ : kˣ
  c₂ : kˣ
  adapt : T.Adapted A (box _ c₁) (box _ c₂)
  cos : Ch (s + 1) → (X (s + 1) → k) ⧸ box (X (s + 1)) c₂
  cos_inj : ∀ y y', SameOrb (T.lev (s + 1) 0 rfl).J (box _ c₂) (cos y) (cos y') → y = y'
  cos_cov : ∀ yb ∈ T.coupIdx A (box _ c₁) (box _ c₂), ∃ y, SameOrb (T.lev (s + 1) 0 rfl).J (box _ c₂) (cos y) yb
  one : Fintype.card (Ch (s + 1 + 1)) = 1

  eL : ∀ j, WO (c.V j) (c.V (j + 1)) →₀ ℂ
  eLT : WO (c.V (s + 1)) c.T →₀ ℂ
  eL_at : ∀ j d (h : j + d = s), (ofSplit q).IsCombAt c.ψ (FY j (d + 1) (by omega)) (FY (j + 1) d (by omega)) (eL j) (T.Phi j d h)
  eLT_at : (ofSplit q).IsCombAt c.ψ (FY (s + 1) 0 rfl) FT eLT T.PhiTop

  dL : ∀ j, Ch j → Ch (j + 1) → WO (c.X j) (c.X (j + 1)) →₀ ℂ
  dL_mid : ∀ j d (H : j + 1 + d = s) α γ, (ofSplit q).IsCombAt c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (dL j α γ)
    (T.entry ψk ν j d H (rep j (d + 1) (by omega) α) (rep (j + 1) d H γ))
  dL_pen : ∀ α y, (ofSplit q).IsCombAt c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (dL s α y)
    (T.xiPen (box _ c₂) (rep s 0 rfl α) (cos y))
  dL_top : ∀ y u, (ofSplit q).IsCombAt c.ψ (FX (s + 1) le_rfl) FM (dL (s + 1) y u) (T.xiTop (box _ c₂) ψk ν (-1) (cos y))

  εL : ∀ j, Ch j → GA D (c.V j) →₀ ℂ
  εL_at : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∀ d (h : j + d = s) α, ∃ e,
    IsOneComb ψk ν (ρ + 1) (T.lev j (d + 1) (by omega)) (rep j d h α) e ∧ εL j α = e.mapDomain (gl j (d + 1) (by omega))

  idx : ℕ → ℕ
  idx_mid : ∀ j d h, idx j = (T.lev j d h).J.relIndex (KO k _)
  idx_top : idx (s + 1 + 1) = T.levTop.J.relIndex (KO k Z)

  m : ∀ j, Measure (GL (X j) k)
  haar : ∀ j, (m j).IsHaarMeasure ∧ m j (KO k (X j)) = 1
  wt : ∀ j, Ch j → ℂ
  wt_mid : ∀ j d (h : j + d = s) α,
    wt j α = (((m j (prX (Cgrp (T.lev j (d + 1) (by omega)).J (rep j d h α)))).toReal⁻¹ : ℝ) : ℂ)
  wt_pen : ∀ y, wt (s + 1) y = idx (s + 1) * Nat.card {yb | SameOrb (T.lev (s + 1) 0 rfl).J (box _ c₂) (cos y) yb}
  wt_top : ∀ u, wt (s + 1 + 1) u = idx (s + 1 + 1)

attribute [instance] QAt.fld QAt.val QAt.top QAt.loc QAt.mea QAt.bor QAt.fX QAt.dX QAt.fZ QAt.dZ QAt.fC

def QAt.Typed {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) (j : ℕ) (f : GA D (c.V j) → ℂ) : Prop :=
  ∀ d (h : j + d = Q.s + 1) (x : (Q.T.lev j d h).J), rTrans (Q.gl j d h x.1) f = ((Q.T.lev j d h).lam x : ℂ) • f

def QAt.eT {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    WO (c.V (j + 1)) c.T →₀ ℂ :=
  (show Q.s = j by have := Q.hs; omega) ▸ Q.eLT

structure QFam (v : VCom c) (t : Tup c) where
  χ : ℕ → (AE D)ˣ →* Circle
  r : ℕ
  Q : Fin r → QAt v χ
  eqv : ∀ j, t.Ch j ≃ ∀ i, (Q i).Ch j

structure QFam.Pins {v : VCom c} {t : Tup c} (F : QFam v t) (w : VTup t) : Prop where
  inj : Function.Injective fun i => (F.Q i).q.v
  places : ∀ p, p ∈ w.Q ↔ ∃ i, (F.Q i).q.v = p
  kom : ∀ j, j < D.R.m → IsWeilDatumO c.ψ _ _ (F.χ j) (F.χ j) (t.kom j)
  mid : ∀ j σ h, ∃ χz : (AE D)ˣ →* Circle, (t.sBF j (σ + 1) h).χV = F.χ j * χz ∧ (t.sBF j (σ + 1) h).χW = F.χ j ∧
    (t.sFB j σ h).χV = F.χ (j + 1) ∧ (t.sFB j σ h).χW = F.χ (j + 1) * χz
  lastc : ∀ j h, (t.sBF j 0 h).χW = F.χ j
  eQ : ∀ j, j + 1 < D.R.m → w.eQ j = aconv (List.ofFn fun i => (F.Q i).eL j)
  eQT : ∀ j h, w.eQT j h = aconv (List.ofFn fun i => (F.Q i).eT j h)
  dQ : ∀ j, j < D.R.m → ∀ α γ, w.dQ j α γ =
    (∏ i, (F.Q i).wt j (F.eqv j α i)) • aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i))
  ε : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∀ α, w.ε j α =
    (∏ i, (F.Q i).wt j (F.eqv j α i)) • conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i))
  εT : ∀ n h β, w.εT n h β = Finsupp.single 1 (∏ i, (F.Q i).wt n (F.eqv n β i))
  FY : ∀ j, j < D.R.m → ∀ f ∈ w.FY j, ∀ i, (F.Q i).Typed j f
  cQ : ∀ j, j + 2 ≤ D.R.m → w.cQ j = ∏ i, (((F.Q i).idx (j + 1) : ℂ) * ((F.Q i).idx (j + 1 + 1) : ℂ))⁻¹

def QPin (v : VCom c) {t : Tup c} (w : VTup t) : Prop := ∃ F : QFam v t, F.Pins w

end GlobalTheory.QPl
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {D : D7}

def realPt (θ : InfFam D) {m n : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Classical.epsilon fun w : Mx D m n => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = z τ

variable (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)

def xiN (f : WO S T → ℂ) (z : VCx D.what₂.Tau a b) : ℂ :=
  Complex.exp ((Real.pi : ℂ) / 2 * HV sc z z) *
    f (realPt θ fun τ => Matrix.of fun i j => -(δ⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j)))

def toHom (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : (Fin a → D.host.E) →ₗ[D.host.E] (Fin b → D.host.E) :=
  Matrix.toLin' (γ.reindex (finCongr hT) (finCongr hS))

def jetP (s : ℂ) (G : VCx D.what₂.Tau a b → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : ℂ :=
  ∑ k ∈ P.support, P.coeff k * jetC (fun _ => s) G (k.mapDomain fun v => (v.1, Fin.cast hT v.2.1, Fin.cast hS v.2.2))

def latFr (V : HSp D) {n : ℕ} (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin V.rank → D.host.E) :=
  {x | (fun i => x (Fin.cast hn.symm i)) ∈ N}

def Moves (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∀ x : Fin n → D.host.E, x ∈ N ↔ ∀ i, (finM V hn g⁻¹ *ᵥ fun j => eToEAf D (x j)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E

structure StdPair (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  gS : S.gram = 1
  gT : T.gram = 1
  sigS : S.SigOK
  sigT : T.SigOK
  rk : 0 < S.rank ∧ S.rank < T.rank ∧ Even S.rank ∧ Even T.rank
  cc : D.host.ccK = ⊤
  ne : δ ≠ 0
  xi : ∀ τ, tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ)
  scale : sc * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹

def IsHol (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f

def splitPart (V : HSp D) : Subgroup (GA D V) := Subgroup.closure {g | ∃ e, IsSplitIdem D e ∧ SuppAt e V g}

def IsRatFin (V : HSp D) (g : GA D V) : Prop := g ∈ GfC V ∧ ∃ γ ∈ GQ V, finHom V γ = finHom V g

end Gen

section World
variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {Ch : ℕ → Type}
  (A : ColDat I l Z u Ch) (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i + 1 ≤ B.R.m)

abbrev ColDat.xiS (f : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) : VCx (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ :=
  xiN θ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc f

end World

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

structure LocPl (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  q : GlobalTheory.FinPl.SplitPt D k
  unit : q.UnitAA
  Y : Type
  Y' : Type
  [fY : Fintype Y]
  [dY : DecidableEq Y]
  [fY' : Fintype Y']
  [dY' : DecidableEq Y']
  FS : Frame k S.rank Y'
  FT : Frame k T.rank Y
  Φ : SB (Matrix Y Y' k)
  e : WO S T →₀ ℂ
  e_is : (ofSplit q).IsCombAt ψ FS FT e Φ.1
  o : WO S T →₀ ℂ
  o_at : ∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x
  o_is : ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
    Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
    Tm Φ₁ = comb ψ S T o (Tm Φ₀)

attribute [instance] LocPl.fld LocPl.val LocPl.top LocPl.loc LocPl.fY LocPl.dY LocPl.fY' LocPl.dY'


open Classical in
def prodDat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} {n : ℕ}
    (L : Fin n → LocPl ψ S T M M') (x : WO S T) : ℂ :=
  if IsHalf (∑ i, (L i).q.e) x then ∏ i, (L i).Φ.1 ((ofSplit (L i).q).down (L i).FS (L i).FT x) else 0

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.StepData GlobalTheory.SymBridge
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

section Gen
variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}
  {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

end Gen

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {Ch : ℕ → Type}
  (A : ColDat I l Z u Ch) {d : Dat (I.rec7 l Z) u}
  {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) (I.rec7 l Z).host.E}

def baseFr (i : ℕ) (hi : i ≤ B.R.m) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0)) :
    Matrix (Fin ((I.rec7 l Z).sp.X i).rank) (Fin (B.R.N i)) (I.rec7 l Z).host.E := fun r a =>
  Formalism.L2.Col.frsF I.sel (I.tup I.mu0) (A.p0 i).1.1 P (Pi.single a 1) (finCongr (rankN (I.rec7 l Z) i hi) r)

end GlobalTheory.LocMod
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFoldr
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.GModel
variable {D : D7} {c : Comm D} {v : VCom c}

section Rel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Rel

section Mu
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Mu


attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {D : _root_.Formalism.BasicNotions.D7} {c : _root_.GlobalTheory.SeeSaw.Comm D} {v : _root_.GlobalTheory.SeeSaw.VCom c} in
theorem _root_.GlobalTheory.SeeSaw.GModel.phi_sb (G : _root_.GlobalTheory.SeeSaw.GLoc v) :
    (∀ j a H, (G.S.T (Fin D.R.t)).Phi j a H ∈
      _root_.GlobalTheory.SplitWeil.SB _) ∧
    (G.S.T (Fin D.R.t)).PhiTop ∈ _root_.GlobalTheory.SplitWeil.SB _ := by
  have hreg : (G.S.T (Fin D.R.t)).Regular := by
    unfold _root_.GlobalTheory.SymChain.SymData.T _root_.GlobalTheory.StepData.typeChain
    exact _root_.GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _
  obtain ⟨hstep, htop, -⟩ := hreg
  exact ⟨hstep, htop⟩

end GlobalTheory.SeeSaw.GModel
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne
noncomputable section

namespace GlobalTheory.Core.Cls

open _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2 NumberField IsDedekindDomain Matrix _root_.Formalism.UG

def LowerTie {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Forms.FormsTiedSym D u Ch chOf) : Prop :=
  IsUnit (Forms.bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      Forms.fnOf _ (Forms.shiftOf (Forms.lamT u D.R.m)) (Forms.mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c = Forms.fnOf _ (Forms.shiftOf (Forms.sgT u)) 1 (Ker.brTen D u P)

def RootsG (D : D7) : Prop :=
  ∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

structure SelC (ex : Extra D L hT Gi Gl K Y cX) : Type 1 where

  host : Host.HostTied D

  real : Theta.RealTied D

  cols : Forms.ColsTiedSym D

  full : Forms.ColsFullS cols

  extra : Forms.ColsExtraTiedS full ex

  cf : Host.CharFrame D

  tp : Host.TupTied D cf ex.nch

  chrVal : Host.ValLL0 D cf

  chrDt : Host.DtTied D cf

  roots : RootsG D

  tw : Forms.SymmetricTwistedColumnsAtPrimes tp cols ex.tw

  emt : Rows.EMtTied D cols tw

  g : G.GroupCompatibilityAll D hT ex.cmp

  herm_eq : g.herm = full.1.to0

  forms_eq : g.forms = fun u => (cols.forms u).to0

  beOn : ∀ u, Ker.BeOnTie D u

  lower : ∀ u, LowerTie (cols.forms u)

  ambMetric : ∀ u, Rk.AmbMetric D u ex.amb

  ambLattice : ∀ u, Rk.AmbLattice D u ex.amb

structure SelB (ex : Extra D L hT Gi Gl K Y cX) : Type 1 extends SelC ex where

  ker : Ker.KerEntTied ex

  crd : ∀ (u : D.what₂.Word) i, i ≤ D.R.m → GL (Fin (D.R.N i)) D.host.E

  crd_gram : ∀ u i (hi : i ≤ D.R.m),
    cT (Forms.sigD D : D.host.E →+* D.host.E) (crd u i hi).1 * (crd u i hi).1 = Forms.gramN D i hi

  crd_lat : ∀ u i (hi : i ≤ D.R.m) (x : Fin (D.R.N i) → D.host.E),
    x ∈ Forms.selfDualLatticeCoords D i hi ↔ ∀ a, ((crd u i hi).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

  ker_sharp : ∀ μ, (ker.cst μ).sharp = true

  ker_frm : ∀ u μ i (hi : i ≤ D.R.m) (y : (D.chTw u μ).Y i) (τ : D.what₂.Tau),
    (ker.O u μ).frm i y τ = Forms.atInf (Forms.embT D) (crd u i hi).1 τ * (Forms.twYS tw.ch cols.forms u μ i hi y).1 τ

  aaUnit : ker.AAUnit

  unfAll : ker.UnfAll

  adapted : ker.Adapted

  top : ker.TopPinned

  chTie : ker.ChTie

  memSide : ker.MemSideU

  mtTw : ker.MtTwTie

  om : Formalism.L2.GlobalTheoryTheory.OmegaCompatible D ker.δ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {ex : Extra D L hT Gi Gl K Y cX}

end GlobalTheory.Core.Cls

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NonemptyOffDatOfTrueD
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffInh

variable {D : D7} {u : D.what₂.Word} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}

attribute [local instance] GlobalTheory.FinPl.Model.relAt GlobalTheory.FinPl.Model.locAt

section Empty

variable {P : Pl D → Prop}

theorem mem_GinfC_of_all (hP : ∀ v, P v) {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) : g ∈ GinfC S := by
  rw [grpOff, congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff] at hg
  rw [GinfC, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  intro i j
  have e : Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
      (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idOff D P)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have h1 : Formalism.L2.Theta.mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D P :=
    Ideal.Quotient.eq.1 ((hg i j).trans e.symm)
  have h2 := GlobalTheory.SelfDualAt.eq_zero_of_compFin (finPart D _) fun w => (Submodule.mem_iInf _).1 h1 ⟨w, hP w⟩
  rw [RingHom.map_sub, sub_eq_zero] at h2
  refine h2.trans ?_
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end Empty

end GlobalTheory.FinPl.OffInh

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTop
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word}

structure XPart (D : D7) (u : D.what₂.Word) where
  c : GlobalTheory.ChainOnto.Com D
  top : StAt D.sp.X'
  x : ∀ j, DefSp (D.sp.X j)
  k : ∀ j, KerDat (D.sp.X j) (D.sp.X (j + 1))
  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (D.sp.X n) D.sp.X' Lz
  Ram : ∀ j, Submodule ℂ (Col D u j)
  rd : ∀ j, Col D u j → (D.mem u).C.Y j → GA D (D.sp.X j) → ℂ
  eT : (D.mem u).P.Mt →ₗ[ℂ] top.st.CC c

@[reducible] def XPart.geo (a : XPart D u) (bot : StAt (D.sp.Y 0)) (mid : ℕ → GlobalTheory.ChainOnto.PiLocalization₂ D) : Geo D := ⟨a.c, bot, mid, a.top⟩


set_option maxHeartbeats 1000000 in
structure YPart (a : XPart D u) where
  bot : StAt (D.sp.Y 0)
  mid : ℕ → GlobalTheory.ChainOnto.PiLocalization₂ D
  p : ∀ j, GlobalTheory.ChainOnto.Step a.c ((a.geo bot mid).st j) ((a.geo bot mid).st (j + 1))
  pT : ∀ j, j + 2 * 0 + 2 = D.R.m → GlobalTheory.ChainOnto.Step a.c ((a.geo bot mid).st (j + 1)) a.top.st
  t : ∀ j, GA D ((a.geo bot mid).st j).V
  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt ((a.geo bot mid).st j).V (D.sp.X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt ((a.geo bot mid).st (j + 1)).V (D.sp.X (j + 1)) ρ
  sBF : ∀ j ρ h, StepBF a.c.ψ ((bes j ρ h).lev (a.x j).vol) ((jac j ρ h).lev (a.x (j + 1)).vol)
  sFB : ∀ j σ h, StepFB a.c.ψ ((jac j (σ + 1) h).lev (a.x (j + 1)).vol)
    ((bes (j + 1 + 1) σ (idx_step h)).lev (a.x (j + 1 + 1)).vol)
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (a.x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (D.sp.X (j + 1)).rank

section Off

open GlobalTheory.FinPl

structure OffX (a : XPart D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where
  p : ι → SplitPt D k
  I : List ι
  q : Unif k
  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1
  β : ∀ j i, Frame (p i) (D.sp.X j) (Fin (D.sp.X j).rank)
  Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)
  cT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  ζ₀ : Fin a.Lz.rank → D.host.E
  γ : ∀ i, Frame (p i) D.sp.X' (Fin D.sp.X'.rank)
  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (D.sp.X n) (Fin D.sp.X'.rank ⊕ Fin 1)

variable {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

def OffX.atT (o : OffX a k ι) (v : Pl D) : Prop := ∃ i, v = (o.p i).v

end Off

section AtLevel

open GlobalTheory.LocMod

structure GX (a : XPart D u) (ζ₀ : Fin a.Lz.rank → D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  idem : Formalism.L2.NTheta.IsIdemAt q.e PP
  unit : q.UnitAA
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  S : SymData k s D.R.k
  char : (ofSplit q).IsChar a.c.ψ S.ψ
  mu : ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (a.c.chS j)⁻¹ (S.μ j)
  FX : ∀ j, j ≤ s + 1 → Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  z₀ : Fin a.Lz.rank → k
  z₀_unit : ∃ c : k, valuation k c = 1 ∧ z₀ = c • fun i => (ofSplit q).pr (ζ₀ i)
  last : FM.β = fromCols ((a.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((a.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X j) (a.x j).L (· = q.v)
  latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (a.x (s + 1 + 1)).L (· = q.v)
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 a.top.β (FT.β.submatrix id e.symm)
  cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt a.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1)
  cg_pen : (ofSplit q).IsCombAt a.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt a.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GX.fld GX.val GX.top GX.loc GX.mea GX.bor

variable {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E}

end AtLevel

section World

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (w : World I l Z) {v : B.Word}
  (a : XPart (I.rec7 l Z) v) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

end World

end GlobalTheory.SeeSaw

end
end
