module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure Com (D : D7) where
  θ : InfFam D
  ψ : AddChar (AF D.host.F) ℂ
  μ : ℕ → ((AE D)ˣ →* Circle)
  η : (AE D)ˣ →* Circle
  Pg : Finset (Pl D.host.E)
  P : LevelP Pg D.R.r ℂ
  chi : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ


open Classical in
def Com.S (c : Com D) : Finset (HeightOneSpectrum (𝓞 D.host.F)) := c.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def Com.chS (c : Com D) (j : ℕ) : (AE D)ˣ →* Circle := (Lift.chrStep c.μ c.η j).1

def Com.chT (c : Com D) (j : ℕ) : (AE D)ˣ →* Circle := (Lift.chrStep c.μ c.η j).2

structure Com.Is (c : Com D) : Prop where
  inf : IsInfFam c.θ
  std : IsStdChar D c.ψ (-1)
  chars : Lift.CharsOK c.μ c.η D.R.m
  exp : ∀ (j : Fin D.R.m) (τ : D.what₂.Tau), HasInfExp D (c.μ ((j : ℕ) + 1)) τ (-(D.hc τ).e j)
  unr : ∀ j : Fin D.R.m, GlobalTheory.LFun.UnrOff (c.μ ((j : ℕ) + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  res : ∀ j : Fin D.R.m, ∃ H : Formalism.L2.Host.HChar D.host.E, ChrEq (c.μ ((j : ℕ) + 1)) H ∧
    ∀ PP ∈ c.Pg, IsRes H PP (c.chi ((j : ℕ) + 1) PP)⁻¹
  split : ∃ e : AE D, IsIdemSum e c.Pg

structure PiLocalization₂ (D : D7) where
  V : HSp D
  par : D.what₂.Tau → SPar
  M : DSModel V par
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  β : GL (Fin V.rank) (Lev.EAf D)
  L : LevDat D.host.E ℂ V.rank
  ν : Measure (GA D V)
  fd : Set (GA D V)

structure PiLocalization₂.Is (c : Com D) (j : ℕ) (s : PiLocalization₂ D) : Prop where
  rank : s.V.rank = D.R.rankY j
  sigOK : s.V.SigOK
  sig : ∀ τ : D.host.E →+* ℂ, s.V.sig τ = sigYD D.R j
  par : s.par = parB (Ptw D) j
  selfDual : IsSelfDualC s.V s.Λ
  frame : Formalism.L2.DIV.IsFrame s.β s.Λ
  base : ∃ N : ℕ, Lev.IsBaseFrame s.V s.β s.Λ N ∧
    ∀ P : Pl D.host.E, P.under (𝓞 D.host.F) ∉ c.S → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal
  lev : ∃ hr ξ, s.L = Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi ξ Lev.Frm.B
  haar : s.ν.IsHaarMeasure
  fund : IsFundamentalDomain (GQ s.V) s.fd s.ν

abbrev PiLocalization₂.CC (c : Com D) (s : PiLocalization₂ D) : Submodule ℂ (SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) :=
  MultT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)

abbrev PiLocalization₂.val {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) : GA D s.V → ℂ :=
  (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v

def PiLocalization₂.KF (s : PiLocalization₂ D) : Submodule ℂ (SmT s.M) :=
  Submodule.span ℂ {w | ∃ v : s.M.Vec, (∀ τ, (v τ : s.M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin s.M τ) ∧ w = PiTensorProduct.tprod ℂ v}

abbrev PiLocalization₂.pet (s : PiLocalization₂ D) (f₁ f₂ : GA D s.V → ℂ) : ℂ := Lift.pet s.ν s.fd f₁ f₂

structure Step (c : Com D) (s s' : PiLocalization₂ D) where
  ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ)
  f : WO s.V s'.V → ℂ
  It : PolF D s'.V.rank s.V.rank →ₗ[ℂ] SmT s'.M →ₗ[ℂ] SmT s.M
  io : s'.CC c →ₗ[ℂ] s.CC c

variable {c : Com D} {s s' : PiLocalization₂ D}

def Step.pt (p : Step c s s') : PolF D s'.V.rank s.V.rank → (WO s.V s'.V → ℂ) :=
  pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f

structure Step.Is (j : ℕ) (p : Step c s s') : Prop where
  weil : IsWeilDatumO c.ψ s.V s'.V (c.chS j) (c.chT j) p.ω
  vec : ∃ ξ f₀, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi j) ∅ ξ f₀ p.f
  theta : ∀ φ, IsThetaFunO c.ψ s.V s'.V (p.pt φ)
  it : IsItW c.θ s.M s'.M p.ω p.pt p.It
  io : Lift.IsIo s'.ν s'.fd (thetaKO p.ω) p.pt p.It (s'.CC c) (s.CC c) p.io

inductive Reach (c : Com D) (s₀ : PiLocalization₂ D) : ℕ → ∀ s : PiLocalization₂ D, (s.CC c →ₗ[ℂ] s₀.CC c) → Prop
  | zero : Reach c s₀ 0 s₀ LinearMap.id
  | step {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (h : Reach c s₀ k s Θ) {s' : PiLocalization₂ D} (hs' : s'.Is c (k + 1))
      (p : Step c s s') (hp : p.Is (k + 1)) : Reach c s₀ (k + 1) s' (Θ ∘ₗ p.io)

def OntoAll (D : D7) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ c : Com D, c.Is → ∀ s₀ : PiLocalization₂ D, s₀.Is c 0 →
    ∀ k ≤ D.R.m, ∀ (s : PiLocalization₂ D) (Θ : s.CC c →ₗ[ℂ] s₀.CC c), Reach c s₀ k s Θ → Function.Surjective Θ

structure IsMet (c : Com D) (s : PiLocalization₂ D) (ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ) (ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ) : Prop where
  pure : ∀ v v' : s.M.Vec, ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') = ∏ τ, ⟪(v' τ : s.M.H τ), (v τ : s.M.H τ)⟫_ℂ
  hermD : ∀ w w', ipD w w' = conj (ipD w' w)
  posD : ∀ w, w ≠ 0 → 0 < (ipD w w).re
  herm : ∀ x y, ip x y = conj (ip y x)
  pos : ∀ x, x ≠ 0 → 0 < (ip x x).re
  integ : ∀ (x y : s.CC c) w w', IntegrableOn (fun g => PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g)) s.fd s.ν
  schur : Lift.IsSchur s.ν s.fd ipD (s.CC c) ip

def ParFun (c : Com D) (s : PiLocalization₂ D) (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E) : Prop :=
  GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) (fun g => conj (f g)) B

def IsPar (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E) : Prop := u ≠ 0 ∧ ∀ v, PiLocalization₂.val u v ≠ 0 → ParFun c s (PiLocalization₂.val u v) B

def stepPar (χS χT : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) : GlobalTheory.LFun.Fam D.host.E := fun w =>
  (B w).map (GlobalTheory.LFun.val (F := D.host.F) χS w * (GlobalTheory.LFun.val (F := D.host.F) χT w)⁻¹ * ·) +
    GlobalTheory.LFun.seg w (GlobalTheory.LFun.val (F := D.host.F) χS w) t

def chainPar (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) : GlobalTheory.LFun.Fam D.host.E :=
  Nat.rec B (fun i B' => stepPar (c.chS (i + 1)) (c.chT (i + 1)) D.R.t B') k

def LNe (c : Com D) (χ : (AE D)ˣ →* Circle) (B : GlobalTheory.LFun.Fam D.host.E) : Prop :=
  ∃ l : ℂ, l ≠ 0 ∧ GlobalTheory.Cont.HolValueAt (fun z => GlobalTheory.LFun.LSD D c.S B χ (z + 1 / 2)) ((D.R.t : ℂ) / 2) l

def Step.up (p : Step c s s') (φ : PolF D s'.V.rank s.V.rank) (F : GA D s.V → ℂ) : GA D s'.V → ℂ :=
  fun h => ∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * F g ∂s.ν

def intOff (c : Com D) (s : PiLocalization₂ D) : Set (GA D s.V) :=
  {g | ∀ v ∉ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v}

def hgtS (c : Com D) (s : PiLocalization₂ D) (a : GL (Fin s.V.rank) (AE D)) (g : GA D s.V) : ℝ :=
  (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w g)) *
    ∏ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g)

def coefW (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ)) (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V))
    (Φ : WO s.V s'.V → ℂ) (g : GA D s.V) : ℂ := ∫ w in X, ω (g, 1) Φ w * conj (Φ w) ∂m

def Step.zint (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (F : GA D s.V → ℂ) (g : GA D s.V) : ℂ := coefW p.ω m X (p.pt φ) g * conj (s.pet (rTr s.V g F) F)

def ForStage (D : D7) (Φ : ∀ (_ : Com D) (_ : ℕ) (_ : PiLocalization₂ D), Prop) : Prop :=
  ∀ c : Com D, c.Is → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, s.Is c j → Φ c j s

def FinDim (D : D7) : Prop := ForStage D fun c _ s => FiniteDimensional ℂ (s.CC c)

def MetEx (D : D7) : Prop := ForStage D fun c _ s => ∃ ipD ip, IsMet c s ipD ip

def EigSpan (D : D7) : Prop := ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ B, IsPar u B} = ⊤

def ParBound (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B s.V.rank (((s.V.rank : ℝ) - 1) / 2)

def ParOfVal (D : D7) : Prop := ForStage D fun c _ s => ∀ (x : s.CC c) w B, PiLocalization₂.val x w ≠ 0 → ParFun c s (PiLocalization₂.val x w) B → IsPar x B

def ParIndep (D : D7) : Prop := ForStage D fun c _ s => ∀ (ι : Type) (x : ι → s.CC c) (B : ι → GlobalTheory.LFun.Fam D.host.E),
  (∀ i, IsPar (x i) (B i)) →
  (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) → LinearIndependent ℂ x

def LevFacts (D : D7) : Prop := ForStage D fun c _ s =>
  (∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧
    ∀ k ∈ U, k ∈ GfC s.V → k ∈ levS s.V s.β s.L ∧ Lev.levChi s.V s.β s.L k = 1) ∧
  (∀ v ∉ c.S, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v,
    GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v k ∈ Lev.levG s.V s.β s.L ∧
      Lev.levChi s.V s.β s.L (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v k) = 1) ∧
  (∀ k ∈ Lev.levG s.V s.β s.L, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧
  (∀ k ∈ GfC s.V, k ∈ intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) →
    k ∈ Lev.levG s.V s.β s.L ∧ Lev.levChi s.V s.β s.L k = 1) ∧
  (∀ k ∈ Lev.levG s.V s.β s.L, ∀ k' ∈ Lev.levG s.V s.β s.L,
    Lev.levChi s.V s.β s.L (k * k') = Lev.levChi s.V s.β s.L k * Lev.levChi s.V s.β s.L k') ∧
  ∀ k ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L k‖ = 1

def ForStep (D : D7) (Φ : ∀ (c : Com D) (_ : ℕ) (s s' : PiLocalization₂ D) (_ : Step c s s'), Prop) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ c : Com D, c.Is → ∀ k < D.R.m, ∀ s s' : PiLocalization₂ D, s.Is c k → s'.Is c (k + 1) →
    ∀ p : Step c s s', p.Is (k + 1) → Φ c k s s' p

def LevelLaw (D : D7) : Prop := ForStep D fun _ _ s s' p => ∀ φ,
  VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L) (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) (p.pt φ)

def UpSpan (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ (u : s.CC c) φ, ∀ v ∈ s.KF,
  p.up φ (PiLocalization₂.val u v) ∈ Submodule.span ℂ {F | ∃ (y : s'.CC c), ∃ w ∈ s'.KF, F = PiLocalization₂.val y w}

def UpAdj (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ (u : s.CC c) (y : s'.CC c) φ, ∀ v ∈ s.KF, ∀ w ∈ s'.KF,
  s'.pet (PiLocalization₂.val y w) (p.up φ (PiLocalization₂.val u v)) = s.pet (PiLocalization₂.val (p.io y) (p.It φ w)) (PiLocalization₂.val u v)

def UpPar (D : D7) : Prop := ForStep D fun c k s s' p => ∀ (u : s.CC c) B φ, IsPar u B → ∀ v ∈ s.KF,
  p.up φ (PiLocalization₂.val u v) ≠ 0 → ParFun c s' (p.up φ (PiLocalization₂.val u v)) (stepPar (c.chS (k + 1)) (c.chT (k + 1)) D.R.t B)

def CoefSupp (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ φ, ∀ g ∈ intOff c s,
  Lev.finE s.V g ∉ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L → coefW p.ω m X (p.pt φ) g = 0

def ZetaNe (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∃ φ, ∃ v ∈ s.KF,
  ∀ u : s.CC c, u ≠ 0 → (∫ g in intOff c s, p.zint m X φ (PiLocalization₂.val u v) g ∂s.ν) ≠ 0 ∧
    ∀ a : GL (Fin s.V.rank) (AE D), GlobalTheory.Doubling.IsMaj s.V a →
      (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) →
      ∃ s₁ : ℝ, s₁ < (D.R.t : ℝ) / 2 ∧
        IntegrableOn (fun g => p.zint m X φ (PiLocalization₂.val u v) g * (hgtS c s a g : ℂ) ^ ((s₁ : ℂ) - (D.R.t : ℂ) / 2)) (intOff c s) s.ν

def RealZeta (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∃ φ, ∃ v : s.M.Vec,
  (∀ τ, (v τ : s.M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin s.M τ) ∧ ∀ mR : Measure (GinfC s.V), mR.IsHaarMeasure →
    let z : GinfC s.V → ℂ := fun g => coefW p.ω m X (p.pt φ) g *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)
    (∫ g, z g ∂mR) ≠ 0 ∧
    ∀ a : GL (Fin s.V.rank) (AE D), GlobalTheory.Doubling.IsMaj s.V a →
      (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) →
      ∃ s₁ : ℝ, s₁ < (D.R.t : ℝ) / 2 ∧ Integrable (fun g : GinfC s.V => z g *
        ((∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) : ℝ) : ℂ) ^
          ((s₁ : ℂ) - (D.R.t : ℂ) / 2)) mR

def UpNe (D : D7) : Prop := ForStep D fun c k s _ p => ∀ (u : s.CC c) B, IsPar u B → LNe c (c.chT (k + 1)) B →
  ∃ φ, ∃ v ∈ s.KF, p.up φ (PiLocalization₂.val u v) ≠ 0

def StepUp (D : D7) : Prop := ForStep D fun c k s s' p => ∀ ipD ip ipD' ip', IsMet c s ipD ip → IsMet c s' ipD' ip' →
  ∀ (u : s.CC c) B, IsPar u B → LNe c (c.chT (k + 1)) B →
    ∃ x : s'.CC c, (∀ y, ip' y x = ip (p.io y) u) ∧ IsPar x (stepPar (c.chS (k + 1)) (c.chT (k + 1)) D.R.t B)

def ChainL (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ B : GlobalTheory.LFun.Fam D.host.E,
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r (((D.R.r : ℝ) - 1) / 2) →
  ∀ k < D.R.m, LNe c (c.chT (k + 1)) (chainPar c B k)

theorem chainPar_succ (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B (k + 1) = stepPar (c.chS (k + 1)) (c.chT (k + 1)) D.R.t (chainPar c B k) := rfl

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
noncomputable section

namespace GlobalTheory.Core.Rk.IP

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev WRep (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

section Objects

variable {A B : HSp D} (om : WRep A B) (m : Measure (GA D A))

def up (Φ : WO A B → ℂ) (u : GA D A → ℂ) : GA D B → ℂ :=
  fun h => ∫ q, AutomorphicL2Unitary.descend (GQ A) (fun g => thetaKO om g h Φ * u g) q ∂autMeasure A m

def UpConv (mH : Measure (GA D B)) (Φ : WO A B → ℂ) (u : GA D A → ℂ) : Prop :=
  (∀ h, Integrable (AutomorphicL2Unitary.descend (GQ A) fun g => thetaKO om g h Φ * u g) (autMeasure A m)) ∧
    MemL2Quotient (GQ B) mH (up om m Φ u)

def wcoef (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (Φ₁ Φ₂ : WO A B → ℂ) : GA D A → ℂ :=
  fun g => ip A B ν 𝓕 (om (g, 1) Φ₁) Φ₂

def rcoef (u₁ u₂ : GA D A → ℂ) : GA D A → ℂ := fun g => petersson A m (rTr A g u₁) u₂


variable (A) in
def hgtL (L : Lat A) (a : GL (Fin A.rank) (AE D)) (g : GA D A) : ℝ≥0 :=
  hgtAd D.sp.cm.sig (dblSp A).gram L a (io A (g, 1))

def integrand (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (L : Lat A) (a : GL (Fin A.rank) (AE D)) (Φ₁ Φ₂ : WO A B → ℂ)
    (u₁ u₂ : GA D A → ℂ) (s : ℂ) : GA D A → ℂ :=
  fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * npow (hgtL A L a g) (s - sZero A B) * rcoef m u₁ u₂ g


variable (A) in
def openOff (L : Lat A) (Sf : Finset (FinPl D)) : Set (GA D A) :=
  {g | ∀ v ∉ Sf, proj D.sp.cm.sig A.gram v g ∈ stabLoc D.sp.cm.sig A.gram L v}


variable (A) in
def SphFun (L : Lat A) (Sf : Finset (FinPl D)) (u : GA D A → ℂ) : Prop :=
  ∀ v ∉ Sf, ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ∀ g, u (g * emb D.sp.cm.sig A.gram v k) = u g

end Objects

structure Pair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)) : Prop where

  setting : HidaSetting θ A B sA sB t cA

  maj : IsMaj A a

  maj_eq : ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1

  weil : IsWeilDatumO ψ A B χA χB om

  covol : IsCovolOne (ratL B A) ν 𝓕

structure Unram (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (LA : Lat A) (LB : Lat B)
    (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ) : Prop where

  sdA : IsSelfDualC A LA

  sdB : IsSelfDualC B LB

  two : ∀ v ∉ Sf, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v

  unr : LFun.UnrOff χB (Sf : Set (FinPl D))

  sph₁ : IsSphOff ψ A B LA LB Sf Φ₁

  sph₂ : IsSphOff ψ A B LA LB Sf Φ₂

def GlobalFormAt (A : HSp D) (L : Lat A) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA,
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    (∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s) m) ∧
    ∃ z, HolValueAt (fun s => ∫ g, integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s g ∂m) (sZero A B) z ∧
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * z

def GlobalForm (D : D7) : Prop := ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → GlobalFormAt A L

def IsSphSecAt (A : HSp D) (L : Lat A) (v : FinPl D) (μ : (AE D)ˣ →* Circle) (s : ℂ) (φ : Gv (dblSp A) v → ℂ) : Prop :=
  φ ∈ degPSFin D.sp.cm.sig (dblSp A).gram L v (charAt μ v) s ∧
    (∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram L v, ∀ g, φ (g * k) = φ g) ∧ φ 1 = 1

def ioAt (A : HSp D) (v : FinPl D) (y : Gv A v) : Gv (dblSp A) v := ioH _ D.sp.cm.sig (gram_hdbl A) (y, 1)

def SphFactor (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ →
    Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ v ∉ Sf, ∀ s : ℂ, ∃ φ, IsSphSecAt A LA v χB⁻¹ s φ ∧
    ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → ∀ y : Gv A v,
      wcoef om ν 𝓕 Φ₁ Φ₂ (x * emb D.sp.cm.sig A.gram v y) *
          npow (hgtL A LA a (x * emb D.sp.cm.sig A.gram v y)) (s - sZero A B) =
        wcoef om ν 𝓕 Φ₁ Φ₂ x * npow (hgtL A LA a x) (s - sZero A B) * φ (ioAt A v y)

def IsSphCoef (A : HSp D) (L : Lat A) (v : FinPl D) (par : LFun.Fam D.host.E) (c : Gv A v → ℂ) : Prop :=
  (∃ C : ℝ, ∀ y, ‖c y‖ ≤ C) ∧
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (Gv A v) V) (x : V) (ℓ : V →ₗ[ℂ] ℂ),
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v),
      LFun.IsParamVec D.sp.cm.sig A.gram L h ρ x (par w)) ∧
    (∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ∀ y, ℓ (ρ (k * y) x) = ℓ (ρ y x)) ∧ ∀ y, c y = ℓ (ρ y x)

def LocalZetaOn (D : D7) (C : FinPl D → Prop) : Prop :=
  ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D χ → ResEta D χ b →
  ∀ v, C v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → LFun.UnrAt χ w) →
  ∀ μ : Measure (Gv A v), μ.IsHaarMeasure → μ (stabLoc D.sp.cm.sig A.gram L v) = 1 →
  ∀ s : ℂ, (A.rank : ℝ) < s.re → ∀ φ, IsSphSecAt A L v χ⁻¹ s φ → ∀ par c, IsSphCoef A L v par c →
    Integrable (fun y => φ (ioAt A v y) * c y) μ ∧
      ∫ y, φ (ioAt A v y) * c y ∂μ =
        LFun.LvTw par (LFun.val χ) v (s + 1 / 2) / LFun.dv D.host.E A.rank b v s * c 1

def ParamBoundOn (D : D7) (C : FinPl D → Prop) : Prop :=
  ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v, C v → ∀ par c, IsSphCoef A L v par c → c 1 ≠ 0 →
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → (par w).card = A.rank ∧
      ∀ β ∈ par w, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((A.rank : ℝ) / 2)

def EulerRight (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ →
    Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
  ∀ s : ℂ, (A.rank : ℝ) + 1 < s.re → Integrable (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s) m →
    ∫ g, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m =
      LFun.LSD D Sf par χB (s + 1 / 2) / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank s *
        ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m

def HeckeForm (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

theorem integrand_sZero {A B : HSp D} (om : WRep A B) (m : Measure (GA D A)) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (L : Lat A) (a : GL (Fin A.rank) (AE D)) (Φ₁ Φ₂ : WO A B → ℂ) (u₁ u₂ : GA D A → ℂ) (g : GA D A) :
    integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ (sZero A B) g = wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g := by
  simp [integrand, GlobalTheory.Doubling.npow]

theorem one_mem_openOff (A : HSp D) (L : Lat A) (Sf : Finset (FinPl D)) : (1 : GA D A) ∈ openOff A L Sf :=
  fun v _ => by rw [map_one]; exact one_mem _

end GlobalTheory.Core.Rk.IP

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Core.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Dense

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar}


open Classical in
def SepCont (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ) : Prop :=
  ∀ τ (v : M.Vec), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w))

def KVecP (M : DSModel V S) (v : M.Vec) : Prop := ∀ τ, IsKFin (M.ε τ) (M.σ τ) (v τ : M.H τ)

def ItSpans (M : DSModel V S) (M' : DSModel W S') (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) : Prop :=
  ∀ v : M.Vec, KVecP M v → PiTensorProduct.tprod ℂ v ∈
    Submodule.span ℂ {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), KVecP M' y ∧ x = It P (PiTensorProduct.tprod ℂ y)}

end Dense

def PropTo {I : Type} (f τ : I → ℂ) : Prop := ∃ a : ℂ, ∀ i, f i = a * τ i

def DenseExt (D : D7) : Prop :=
  ∀ (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : D.what₂.Tau → SPar) (M : DSModel B.V S)
    (J : Set (GA D B.V)) (χ : GA D B.V → ℂ) (t : GA D B.V) (I : Type) (τ : I → ℂ) (φ : I → GA D B.A → ℂ)
    (T : I → SmT M →ₗ[ℂ] (GA D B.V → ℂ)), IsInfFam θ → IsStdChar D ψ (-1) → (∀ i, IsContAut B.A (φ i)) →
    (∀ i, T i ∈ MultT θ M J χ) →
    (∀ v : M.Vec, KVecP M v → PropTo (fun i => B.per ψ (φ i) (rTrans t (T i (PiTensorProduct.tprod ℂ v)))) τ) →
    ∀ x : SmT M, PropTo (fun i => B.per ψ (φ i) (rTrans t (T i x))) τ

def TowerSpans (W : Tower D) : Prop :=
  (∀ k, k + 1 < D.R.m → ItSpans (W.MY k) (W.MY (k + 1)) (W.ItY k)) ∧ ItSpans (W.MY (D.R.m - 1)) W.MX W.ItX

section Model

variable (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)

def IdE : Prop := ∀ x : X.B.I.E, HEq (X.ιE x) x

def rowJ : Set (GA D (D.sp.Y 0)) := iotaX X h ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}

def rowChi (k : GA D (D.sp.Y 0)) : ℂ := star (X.chi2 (iotaX X h k).2)

def Matches (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) : Prop :=
  t ∈ GfC (D.sp.Y 0) ∧ ConjLevel t⁻¹ J χ (rowJ X h) (rowChi X h)

def evS (t : GA D (D.sp.Y 0)) (F : GA D (D.sp.Y 0) → ℂ) : X.B.I.GA → ℂ := fun x => F ((iotaX X h).symm x * t)

def ConjVec (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (v₀ : M.Vec) : Prop :=
  ∃ c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ),
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) =
      X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧
    ∀ τ, c τ (v₀ τ : M.H τ) = X.B.w (X.pl.symm τ)

def RealSplit (θ : InfFam D) : Prop :=
  (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧
  (∀ k : GA D (D.sp.Y 0), k ∈ GinfC (D.sp.Y 0) ↔ (iotaX X h k).2 = 1) ∧
  (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
    (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧
    HEq (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ)))
      ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm)
        ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧
  ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
    (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y

def EvalAll (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0)))
    (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec) : Prop :=
  ∃ j : MultT θ M J χ →ₗ⋆[ℂ] HHX X, Function.Bijective j ∧ ∀ T : MultT θ M J χ,
    (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)

structure RowFun (f : X.B.I.GA → ℂ) : Prop where
  cont : Continuous f
  bdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  left : ∀ γ ∈ X.B.I.GFset, ∀ x, f (γ * x) = f x
  right : ∀ k ∈ X.K2, ∀ x, f (x * (1, k)) = star (X.chi2 k) * f x

structure SBes (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) where
  V₀ : HSp D
  L : HSp D
  d : HypDec (D.sp.Y 0) V₀ D.R.rS
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  cpt : CoCpt A
  vA : Vol A
  vN : VolN d
  tieN : ∀ n, n ∈ flagN d ↔ (iotaX X h n).1 ∈ X.NinfU u ∧ (iotaX X h n).2 ∈ X.NfinU u
  tieH : ∀ g, g ∈ (embA d o).range ↔ (iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u
  tieψ : ∀ n ∈ flagN d, star (psiBes ψ d 1 (vecB o ζ) n) = X.psiInfU u (iotaX X h n).1 * X.psiFinU u (iotaX X h n).2

namespace SBes

variable {X h} {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)

abbrev lev : BesLev D D.R.rS := ⟨D.sp.Y 0, B.V₀, A, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vA, B.vN⟩

def toH (a : GA D A) : Hinf X u × Hfin X u :=
  (⟨(iotaX X h (embA B.d B.o a)).1, ((B.tieH _).1 ⟨a, rfl⟩).1⟩, ⟨(iotaX X h (embA B.d B.o a)).2, ((B.tieH _).1 ⟨a, rfl⟩).2⟩)

def colForm (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (ξ : X.Vpi u) : GA D A → ℂ := fun a => T ξ (B.toH a)

def PerLaw (Y : Formalism.L2.SG.Full.Full X) : Prop :=
  ∃ c : ℂ, ∀ (T : Cu X u Y.hK) (f : X.B.I.GA → ℂ) (φ : L2X X), RowFun X f → (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f →
    ⟪star φ, PuFun X u Y.hK (Y.Dt u) T⟫_ℂ =
      c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u)

end SBes

theorem rank_eq (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : (D.sp.Y 0).rank = X.B.I.n := by
  rw [h]; rfl

def SBes.Adapted {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ k j, (B.d.i₀ * B.o.iA) k j = X.ιE (X.crd (Formalism.L2.SG.ColDict.qFr wt
    (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) (Fin.cast (rank_eq X h) k))

end Model

section MI

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (u : D.what₂.Word) (W : Tower D) (L : Link D u W)

end MI


end GlobalTheory.Core.Mi

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk

def IdE {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop := ∀ x : X.B.I.E, HEq (X.ιE x) x


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
def TrueE (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    D = I.rec7 l Z ∧ ∃ w : World I l Z, IdE w.S.X

theorem TrueE.trueD {D : D7} (h : TrueE D) : TrueD D :=
  let ⟨B, X, I, l, Z, e, w, _⟩ := h; ⟨B, X, I, l, Z, e, ⟨w⟩⟩


def HD (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  Formalism.BasicNotions.Ties D ∧ Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D ∧ Deg.HypL D L C' Cl Cg cb Cu cT CT ∧ Deg.DataNW D ∧ Formalism.L2.SG.RowsConc.TFrameAt D

def LedE (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C'

def GamLe (D : D7) (L C' : ℝ) : Prop := ∀ u : D.what₂.Word, 8 * Real.log (D.mem u).A.GamP ≤ C' * mfL D L

def Row (E : D7 → ℝ → ℝ → Prop) (Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C C'₀ Cl₀ : ℝ, 1 ≤ C ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ) (u : D.what₂.Word), TrueE D → E D L C' → HD D L C' Cl Cg cb Cu cT CT → Q D u L C

variable (E : D7 → ℝ → ℝ → Prop)

def RowDiag : Prop := Row E fun D u L C => SDiag D u L C

def RKRowAbs : Prop := Row E fun D u L C => RankMu D u → C * D.R.f * D.R.k * L ≤ Real.log (D.mem u).A.GamP → RK D u

def Inh (P : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop) : Prop :=
  ∃ Cg cb Cu cT CT : ℝ, 0 < cb ∧ 0 < cT ∧ ∀ C C'₀ Cl₀ : ℝ, ∃ (C' Cl L : ℝ) (D : D7), C'₀ ≤ C' ∧ Cl₀ ≤ Cl ∧
    TrueE D ∧ E D L C' ∧ HD D L C' Cl Cg cb Cu cT CT ∧ ∀ u, P D u L C

def InhAbs : Prop := Inh E fun D u L C => RankMu D u ∧ C * D.R.f * D.R.k * L ≤ Real.log (D.mem u).A.GamP

variable {E}

theorem Inh.reach {P Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} (h : Inh E P) (h' : Row E fun D u L C => P D u L C → Q D u L C) :
    ∃ (D : D7) (L C : ℝ), TrueE D ∧ 1 ≤ C ∧ ∀ u, Q D u L C :=
  let ⟨Cg, cb, Cu, cT, CT, h1, h2, h⟩ := h
  let ⟨C, a, b, hC, h'⟩ := h' Cg cb Cu cT CT h1 h2
  let ⟨C', Cl, L, D, ha, hb, hD, he, hH, hP⟩ := h C a b
  ⟨D, L, C, hD, hC, fun u => h' C' Cl ha hb D L u hD he hH (hP u)⟩

theorem Inh.not_row_false {P : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} (h : Inh E P) :
    ¬ Row E fun D u L C => P D u L C → False := fun h' =>
  let ⟨D, _, _, _, _, h⟩ := h.reach (Q := fun _ _ _ _ => False) h'
  h D.u₀

theorem one_le_mfL {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT) :
    1 ≤ mfL D L ∧ 16 ≤ D.R.k ∧ 1 ≤ D.R.f := by
  obtain ⟨h1, -, h3, h4, -⟩ := hH
  have hm := D.R.two_le_m
  have h16 : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hm' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))
  refine ⟨?_, by omega, by omega⟩
  unfold mfL
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm' hf) h1.le

theorem LedE.gamLe {D : D7} {L C' : ℝ} (h : LedE D L C') : GamLe D L C' := by
  obtain ⟨large₂, hL, h8⟩ := h
  intro u
  have hG := large₂.Gam_eq u
  have hL0 : 0 ≤ L := hL ▸ Real.rpow_nonneg (zero_le_one.trans large₂.sc.one_lt_alt.le) _
  rw [hL] at hG
  have hx : 0 ≤ mfL D L := by unfold mfL; positivity
  have e : Real.log (D.mem u).A.GamP = large₂.CGam * mfL D L := by rw [hG]; unfold mfL; ring
  rw [e]
  nlinarith

theorem GamLe.le_k {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (h : GamLe D L C') (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (u : D.what₂.Word) : 8 * Real.log (D.mem u).A.GamP ≤ D.R.k := by
  refine (h u).trans (le_trans (le_of_eq ?_) hH.2.1)
  unfold mfL
  ring

theorem GamLe.log_lt {D : D7} {L C C' Cl Cg cb Cu cT CT : ℝ} (h : GamLe D L C') (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (hC : 1 ≤ C) (u : D.what₂.Word) : Real.log (D.mem u).A.GamP < C * D.R.f * D.R.k * L := by
  have h1 := h.le_k hH u
  obtain ⟨-, hk, hf⟩ := one_le_mfL hH
  have hk' : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have a : (1 : ℝ) ≤ C * D.R.f * L := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hf') hH.1.le
  nlinarith

theorem RKRowAbs.of_gamLe (hE : ∀ D L C', E D L C' → GamLe D L C') : RKRowAbs E :=
  fun _ _ _ _ _ _ _ => ⟨1, 0, 0, le_rfl, fun _ _ _ _ _ _ u _ he hH _ h =>
    absurd h (not_le.2 ((hE _ _ _ he).log_lt hH.2.2.1 le_rfl u))⟩

theorem not_inhAbs_of_gamLe (hE : ∀ D L C', E D L C' → GamLe D L C') : ¬ InhAbs E := fun h =>
  Inh.not_row_false h fun _ _ _ _ _ _ _ => ⟨1, 0, 0, le_rfl, fun _ _ _ _ _ _ u _ he hH h =>
    absurd h.2 (not_le.2 ((hE _ _ _ he).log_lt hH.2.2.1 le_rfl u))⟩

end GlobalTheory.Core.Rk

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
noncomputable section

namespace GlobalTheory.CoreHt

open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2

def DelNat (D : D7) : Prop := ∃ n : ℕ, D.s.Del = n

def ThickUp {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → wj D j τ ≤ L.sc.b + L.etaSz + 1

end GlobalTheory.CoreHt
end
end
