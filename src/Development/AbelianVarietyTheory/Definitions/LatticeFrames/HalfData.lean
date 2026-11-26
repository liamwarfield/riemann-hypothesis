module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

variable {D : D7}

def IsSkew (μ : D.host.E) : Prop := μ ≠ 0 ∧ star μ = -μ

def Tm (A : HSp D) (μ : D.host.E) : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) D.host.E :=
  (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e')).submatrix id finSumFinEquiv.symm

def IsChart (A : HSp D) (μ : D.host.E) (κ : GA D (dblSp A) ≃* G D A.rank) : Prop :=
  ∀ g, (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) * mat (κ g) = mt (dblSp A) g * rat (Tm A μ)

def IntA (z : AE D) : Prop := ∀ v, compFin D.host.F D.host.E v z ∈ intLoc D.host.F D.host.E v

def IntGL {n : ℕ} (M : GL (Fin n) (AE D)) : Prop := (∀ i j, IntA (M.1 i j)) ∧ ∀ i j, IntA ((M⁻¹).1 i j)

def ScalData (μ : D.host.E) (u ε : (AE D)ˣ) : Prop :=
  (ε : AE D) * u * cA D u = incA D μ ∧ IntA (ε : AE D) ∧ IntA ((ε⁻¹ : (AE D)ˣ) : AE D) ∧
    ∀ w, compInf D.host.F D.host.E w (ε * cA D ε) = 4

def HalfData (t : AE D) : Prop := t + cA D t = 1 ∧ IntA t ∧ ∀ w, compInf D.host.F D.host.E w (2 * t) = 1

def IsConj (A : HSp D) (a : GL (Fin A.rank) (AE D)) (κ : GA D (dblSp A) ≃* G D A.rank) (p : siegel A) : Prop :=
  ∀ k : GA D (dblSp A), k ∈ Khat A a ↔ κ ((p : GA D (dblSp A))⁻¹ * k * p) ∈ K D A.rank

def hgtStd (A : HSp D) (a : GL (Fin A.rank) (AE D)) (κ : GA D (dblSp A) ≃* G D A.rank) (p : siegel A) :
    G D A.rank → ℝ≥0 := fun g => hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹) * absA D (aP A p)

def IsTransport (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B))
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (κ : GA D (dblSp A) ≃* G D A.rank)
    (ω : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank)) : Prop :=
  ∀ g f, IsThetaFunO ψ (dblSp A) B f → ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 f →
    (ω (κ g) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f)

def shift (ψ : AddChar (AF D.host.F) ℂ) (l : D.host.F) : AddChar (AF D.host.F) ℂ :=
  ψ.mulShift (algebraMap D.host.F (AF D.host.F) l)

def stdInv (n : ℕ) (μ : D.host.E) (τ : D.what₂.Tau) : Matrix (Fin (n + n)) (Fin (n + n)) ℂ :=
  (tauE D τ μ / (‖tauE D τ μ‖ : ℂ)) • blk4 0 1 (-1) 0

def IsStdInv (A : HSp D) (μ : D.host.E)
    (s : D.what₂.Tau → Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) ℂ) : Prop :=
  ∀ τ, s τ * (Tm A μ).map (tauE D τ) = (Tm A μ).map (tauE D τ) * stdInv A.rank μ τ

variable (V : HSp D) {n : ℕ} (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)

def linF (τ : D.what₂.Tau) (X z : Matrix (Fin V.rank) (Fin n) ℂ) : ℂ :=
  ((4 * Real.pi * |l τ| * (Matrix.trace (Xᴴ * (gramAt D V τ * s τ) * z)).re : ℝ) : ℂ)

def annS (θ : InfFam D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin n) ℂ) (φ : Mx D V.rank n → ℂ) :
    Mx D V.rank n → ℂ :=
  fun x => deriv (fun t : ℝ => φ (x + lineAt θ τ X t)) 0 + linF V l s τ X (compAt θ τ x) * φ x


open Classical in
def annC (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin n) ℂ) (f : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ) :
    (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ :=
  fun z => deriv (fun t : ℝ => f (z + t • (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ))) 0 + linF V l s τ X (Matrix.of (z τ)) * f z

end GlobalTheory.StdUnn

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def CombAt (P : Pl D → Prop) {S T : HSp D} (c : WO S T →₀ ℂ) : Prop := ∀ u ∈ c.support, MxAt P u

def extS {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) (c : WO A T →₀ ℂ) : WO S T →₀ ℂ :=
  c.mapDomain fun u => (o.resS T).symm (u, 0)

def extT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c : WO S A →₀ ℂ) : WO S T →₀ ℂ :=
  c.mapDomain fun u => (o.resT S).symm (u, 0)

def kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w : WO S L'') : WO L S :=
  GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)

def lastBi {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) : WO A S → WO S X → ℂ :=
  fun u => o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))

def BiVacAt (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (LA : Lat A) (LS : Lat S) (LA' : Lat A') (P : Pl D → Prop)
    (C : WO A S → WO S A' → ℂ) : Prop :=
  (∀ v, Vac ψ A S LA LS P fun u => C u v) ∧ ∀ u, Vac ψ S A' LS LA' P (C u)

variable {u : D.what₂.Word}

def offS (d : Dat D u) (v : Pl D) : Prop := v ∉ d.c.S

def onS (d : Dat D u) (v : Pl D) : Prop := v ∈ d.c.S

def xiBF (d : Dat D u) (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (P₁ : Formalism.IndefR.Links.PolF D (d.st (j + 1)).V.rank (d.st j).V.rank)
    (a : GA D (d.st (j + 1)).V) : WO (d.bes j ρ h).V₀ (D.sp.X (j + 1)) → ℂ :=
  flatBF (d.sBF j ρ h) ((d.p j).ω (d.t j, a * d.t (j + 1)) ((d.p j).pt P₁))

def xiFB (d : Dat D u) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (P₂ : Formalism.IndefR.Links.PolF D (d.st (j + 1 + 1)).V.rank (d.st (j + 1)).V.rank) (a : GA D (d.st (j + 1)).V)
    (a' : GA D (d.st (j + 1 + 1)).V) : WO (D.sp.X (j + 1)) (d.bes (j + 1 + 1) σ (idx_step h)).V₀ → ℂ :=
  flatFB (d.sFB j σ h) ((d.p (j + 1)).ω (a * d.t (j + 1), a' * d.t (j + 1 + 1)) ((d.p (j + 1)).pt P₂))

def xiTop (d : Dat D u) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m)
    (P₂ : Formalism.IndefR.Links.PolF D d.top.st.V.rank (d.st (j + 1)).V.rank) : WO (D.sp.X (j + 1)) D.sp.X' → ℂ :=
  fun w => (d.pT j h).ω (d.t (j + 1), 1) ((d.pT j h).pt P₂) ((d.jac j 0 h).d.ext0 D.sp.X' w)

structure OffDat (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where

  p : ι → SplitPt D k

  I : List ι

  q : Unif k

  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1

  β : ∀ j i, Frame (p i) (D.sp.X j) (Fin (D.sp.X j).rank)

  Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)

  β₀ : ∀ j ρ h i, Frame (p i) (d.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)

  L : ∀ j, Lat (d.st j).V

  M : ∀ j ρ h, Lat (d.bes j ρ h).V₀

  cT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ

  cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ

  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E

  ζ₀ : Fin d.Lz.rank → D.host.E

  γ : ∀ i, Frame (p i) D.sp.X' (Fin D.sp.X'.rank)

  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (D.sp.X n) (Fin D.sp.X'.rank ⊕ Fin 1)

variable {d : Dat D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : OffDat d k ι)

namespace OffDat

def atT (v : Pl D) : Prop := ∃ i, v = (o.p i).v

def pair (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) : PairDat o.p (D.sp.X j) (d.bes j ρ h).V₀ (Fin (D.sp.X j).rank) :=
  ⟨o.β j, o.β₀ j ρ h, o.Q j⟩

def mid (j : ℕ) : MidDat o.p (D.sp.X j) (Fin (D.sp.X j).rank) := ⟨o.β j, o.Q j⟩

def dbl (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) :
    DblLat (d.B j (σ + 1) h) ((d.jac j (σ + 1) h).lev (d.x (j + 1)).vol) (d.B (j + 1 + 1) σ (idx_step h)) :=
  ⟨o.L j, o.M j (σ + 1) h, o.L (j + 1), (d.x (j + 1)).L, o.L (j + 1 + 1), o.M (j + 1 + 1) σ (idx_step h)⟩

end OffDat

structure PinOff : Prop where

  nodup : o.I.Nodup
  all : ∀ i, i ∈ o.I
  inj : Function.Injective fun i => (o.p i).v
  off : ∀ i, offS d (o.p i).v

  char : ∀ i, (o.p i).IsChar d.c.ψ (o.χ i) ∧ (o.p i).UnitAA

  moves : ∀ j, j < D.R.m → IsSelfDualC (d.st j).V (o.L j) ∧ ∀ P, Moves (d.st j).V (d.t j) (d.st j).Λ (o.L j) P

  latT : ∀ j, j ≤ D.R.m → ∀ i, (o.β j i).IsLat (d.x j).L (o.Q j i).lat

  shape : ∀ j σ h, DblShape (d.sBF j (σ + 1) h) (d.sFB j σ h) (o.dbl j σ h) (offS d) o.q (o.pair j (σ + 1) h) (o.mid (j + 1))
    (o.pair (j + 1 + 1) σ (idx_step h))

  goodLast : ∀ j h v, offS d v → GoodBF d.c.ψ (d.B j 0 h) ((d.jac j 0 h).lev (d.x (j + 1)).vol) (o.L j) (o.M j 0 h) (o.L (j + 1))
    (d.x (j + 1)).L v ∧ UnrAt (d.sBF j 0 h) v

  gluedLast : ∀ j h i, GluedCore (d.B j 0 h) (o.M j 0 h) o.q (o.β j i) (o.β₀ j 0 h i) (o.Q j i)

  core : ∀ j ρ h v, offS d v → ¬ o.atT v → ∃ LL, IsSelfDualC (d.bes j ρ h).L LL ∧ OrthAt (d.bes j ρ h).o (o.M j ρ h) (d.x j).L LL v

  parts : ∀ j, j < D.R.m → CombAt o.atT (o.cT j) ∧ CombAt (onS d) (o.cG j) ∧
    ∀ f, comb d.c.ψ _ _ (d.k j).c f = comb d.c.ψ _ _ (o.cG j) (comb d.c.ψ _ _ (o.cT j) f)

  rep : ∀ j, j < D.R.m → ∀ f, Vac d.c.ψ _ _ (d.x j).L (d.x (j + 1)).L o.atT f →
    OverAll d.c.ψ (o.β j) (o.β (j + 1)) (d.x j).L (d.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
      (comb d.c.ψ _ _ (o.cT j) f)

  unrK : ∀ j, j < D.R.m → ∃ χS χT, IsWeilDatumO d.c.ψ _ _ χS χT (d.k j).om ∧
    ∀ i, CharUnramAt D χS (o.p i).v ∧ CharUnramAt D χT (o.p i).v

  weil : ∀ j σ h, ∃ (χA χA' χz : (AE D)ˣ →* Circle) (omz : Om (d.bes j (σ + 1) h).L (D.sp.X (j + 1)))
    (omz' : Om (D.sp.X (j + 1)) (d.bes (j + 1 + 1) σ (idx_step h)).L),
    (d.sBF j (σ + 1) h).χV = χA * χz ∧ (d.sFB j σ h).χW = χA' * χz ∧
    IsWeilDatumO d.c.ψ _ _ χA (d.sBF j (σ + 1) h).χW (d.k j).om ∧ IsWeilDatumO d.c.ψ _ _ χz (d.sBF j (σ + 1) h).χW omz ∧
    IsWeilDatumO d.c.ψ _ _ (d.sFB j σ h).χV χA' (d.k (j + 1)).om ∧ IsWeilDatumO d.c.ψ _ _ (d.sFB j σ h).χV χz omz'

  weilLast : ∀ j h, ∃ (χA χz χS' χT : (AE D)ˣ →* Circle) (omz : Om (d.bes j 0 h).L (D.sp.X (j + 1)))
    (omT : Om (D.sp.X (j + 1)) D.sp.X') (omz'' : Om (D.sp.X (j + 1)) d.Lz),
    (d.sBF j 0 h).χV = χA * χz ∧ IsWeilDatumO d.c.ψ _ _ χA (d.sBF j 0 h).χW (d.k j).om ∧
    IsWeilDatumO d.c.ψ _ _ χz (d.sBF j 0 h).χW omz ∧ IsWeilDatumO d.c.ψ _ _ χS' (χT * χz⁻¹) (d.k (j + 1)).om ∧
    IsWeilDatumO d.c.ψ _ _ χS' χT omT ∧ IsWeilDatumO d.c.ψ _ _ χS' χT (d.pT j h).ω ∧ IsWeilDatumO d.c.ψ _ _ χS' χz⁻¹ omz'' ∧
    ∀ i, CharUnramAt D χS' (o.p i).v ∧ CharUnramAt D χT (o.p i).v

  line : IsLineVec d.Lz o.ζ₀

  tau : ∀ j h, (o.τ j h)ᴴ ⬝ ((d.bes j 0 h).L.gram ⬝ o.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • d.Lz.gram ∧
    ∃ lam : D.host.E, o.τ j h *ᵥ o.ζ₀ = lam • (d.bes j 0 h).ζ ∧ ∀ i, valuation k ((o.p i).pr (incA D lam)) = 1

  top : ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, offS d v → ¬ o.atT v → ∃ (LL : Lat (d.bes j 0 h).L) (LZ : Lat d.Lz),
    IsSelfDualC _ LL ∧ IsSelfDualC _ LZ ∧ OrthAt (d.bes j 0 h).o (o.M j 0 h) (d.x j).L LL v ∧
    OrthAt (d.oT (j + 1 + 1) h) (d.x (j + 1 + 1)).L d.top.Λ LZ v ∧
    ∀ w ∈ latO (D.sp.X (j + 1)) d.Lz ((d.x (j + 1)).L : Set _) (LZ : Set _) (· = v),
      kap (o.τ j h) (D.sp.X (j + 1)) w ∈ latO (d.bes j 0 h).L (D.sp.X (j + 1)) (LL : Set _) ((d.x (j + 1)).L : Set _) (· = v)

  topT : ∀ n (h : n = D.R.m) i, IsSumFrame (d.oT n h) o.ζ₀ (o.γ i) (o.γ₀ n h i) ∧
    ∃ (Λ : Submodule 𝒪[k] (Fin D.sp.X'.rank → k)) (s : 𝓀[k]ˣ), (o.γ i).IsLat d.top.Λ Λ ∧
      (∀ y, y ∈ (o.Q n i).ker ↔ ((o.γ₀ n h i).b' * (o.β n i).b) *ᵥ y ∈ lastKer Λ) ∧
      (o.Q n i).HasVal (((o.β n i).b' * (o.γ₀ n h i).b) *ᵥ (o.q.inv • avec k (Fin D.sp.X'.rank) 1 1)) s

def IsS (j : ℕ) (ε : ι → 𝓀[k]ˣ) : Prop :=
  ∀ ψ ∈ d.Ram j, d.S j ψ ∈ d.Ram j ∧ ∀ y, d.rd j (d.S j ψ) y =
    o.I.foldr (fun i φ => sOp (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (ε i) φ) (d.rd j ψ y)

theorem rank_pos_of_le (D : D7) {j : ℕ} (h : j ≤ D.R.m) : 0 < (D.sp.X j).rank := by
  rw [D.sp.X_rank j h]
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  exact Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)

variable {o} {Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)}

namespace OffTest

theorem combAt_single_zero (P : Pl D → Prop) {S T : HSp D} (c : ℂ) : CombAt P (Finsupp.single (0 : WO S T) c) := by
  intro u hu
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
  intro i j
  exact Submodule.zero_mem _

theorem comb_single_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single 0 1) f = f := by
  simp [comb]
  exact GlobalTheory.MixPer.heisO_zero ψ S T f

end OffTest

end GlobalTheory.FinPl

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainTw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def trivAt (Pg P : Finset (Pl D.host.E)) (r : ℕ) : Subgroup (G0 P r) where
  carrier := {g | ∀ PP : P, PP.1 ∈ Pg → g PP = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb PP h => by rw [Pi.mul_apply, ha PP h, hb PP h, mul_one]
  inv_mem' := fun {a} ha PP h => by rw [Pi.inv_apply, ha PP h, inv_one]


open Classical in
def comR (t : T) : Com D :=
  ⟨R.θ, R.ψ, R.toLevCh.mu t, R.eta, R.Pg ∪ R.Q t, ⟨trivAt R.Pg (R.Pg ∪ R.Q t) D.R.r, 1⟩,
    fun j PP => if PP ∈ R.Q t then (R.xiR t PP)⁻¹ else R.chi j PP⟩

def twR (t : T) : Twist D := ⟨R.Pg, R.Q t, R.chi, R.xiR t⟩

def stY (t : T) (j : ℕ) : PiLocalization₂ D :=
  ⟨Yc D j, parB (Ptw D) (min j D.R.m), R.MY j, R.ΛY j, R.βY j, R.datYt t j R.triv, R.νY t j, R.fdY t j⟩

def stX (t : T) : PiLocalization₂ D := ⟨D.sp.X', parB (Ptw D) D.R.m, R.MX, R.ΛX, R.βX, R.datXt t, R.νX t, R.fdX t⟩

def RangeX : Prop := ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) =
  MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (Lev.levChi _ R.βX (R.datXt t))

def stepY (t : T) (k : ℕ) : Step (comR R t) (stY R t k) (stY R t (k + 1)) := ⟨R.ωY t k, R.vY t k, R.ItY k, R.ioY t k⟩

def stepX (h : RangeX R) (t : T) : Step (comR R t) (stY R t (D.R.m - 1)) (stX R t) :=
  ⟨R.ωX t, R.vX t, R.ItX, (R.ioX t ∘ₗ (LinearEquiv.ofEq _ _ (h t).symm).toLinearMap :
    MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (Lev.levChi _ R.βX (R.datXt t)) →ₗ[ℂ] R.CC t (D.R.m - 1))⟩

def toCC (h : RangeX R) (t : T) (x : (R.HX t).H) : (stX R t).CC (comR R t) :=
  LinearEquiv.ofEq _ _ (h t) ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict x)

def RChain (h : RangeX R) : Prop := ∀ t, (twR R t).Is (comR R t) ∧ (∀ j < D.R.m, IsStage (comR R t) (twR R t) j (stY R t j)) ∧
  IsStage (comR R t) (twR R t) D.R.m (stX R t) ∧ (∀ k, k + 1 < D.R.m → IsStep (twR R t) (k + 1) (stepY R t k)) ∧
  IsStep (twR R t) D.R.m (stepX R h t)

def NormX (h : RangeX R) : Prop := ∃ δ : ℝ, 0 < δ ∧ ∀ t, Function.Bijective (toCC R h t) ∧
  ∀ ipD ip, IsMet (comR R t) (stX R t) ipD ip → ∀ x y : (R.HX t).H, ⟪x, y⟫_ℂ = (δ : ℂ) * ip (toCC R h t y) (toCC R h t x)

def RMeas : Prop := ∀ j < D.R.m, ∃ mR : Measure (GinfC (Yc D j)), ∀ t, IsLevMeas (stY R t j) mR

def RVol : Prop := ∀ t, (∀ j < D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D j) (R.νY t j) =
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D j) (R.νY A.μ0 j) * ∏ PP ∈ R.Q t, idxQ PP j ∧ 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D j) (R.νY t j)) ∧
  GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX t) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX A.μ0) * ∏ PP ∈ R.Q t, idxQ PP D.R.m ∧
  0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX t)

def RNrm : Prop := ∀ t, (∀ k, k + 1 < D.R.m → ∀ m X, IsCovolOne (ratL (Yc D (k + 1)) (Yc D k)) m X →
    nrm2 m X (R.vY t k) = nrm2 m X (R.vY A.μ0 k) * ∏ PP ∈ R.Q t, volOne PP (k + 1)) ∧
  ∀ m X, IsCovolOne (ratL D.sp.X' (Yc D (D.R.m - 1))) m X → nrm2 m X (R.vX t) = nrm2 m X (R.vX A.μ0) * ∏ PP ∈ R.Q t, volOne PP D.R.m

def IsUnif (k : ℕ) (s s' : T → PiLocalization₂ D) (p : ∀ t, Step (comR R t) (s t) (s' t)) (K : ℂ)
    (P : ∀ t, PolF D (s' t).V.rank (s t).V.rank) (v : ∀ t, (s t).M.Vec) : Prop :=
  K ≠ 0 ∧ ∀ t, ∃ m X mR H₀, IsCovolOne (ratL (s' t).V (s t).V) m X ∧ IsLevMeas (s t) mR ∧
    RealConv (p t) m X (P t) (v t) mR ∧ IsHval (comR R t) (twR R t).S₀ k H₀ ∧ kapOf (twR R t) k (p t) m X mR (P t) (v t) H₀ = K

def RUnif (h : RangeX R) : Prop :=
  (∀ k, k + 1 < D.R.m → ∃ (K : ℂ) (φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank) (v : (R.MY k).Vec),
    IsUnif R k (fun t => stY R t k) (fun t => stY R t (k + 1)) (fun t => stepY R t k) K (fun _ => φ) fun _ => v) ∧
  ∃ (K : ℂ) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (v : (R.MY (D.R.m - 1)).Vec),
    IsUnif R (D.R.m - 1) (fun t => stY R t (D.R.m - 1)) (fun t => stX R t) (fun t => stepX R h t) K (fun _ => φ) fun _ => v

def RowPar : Prop := ∀ (t : T) (c : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.EigSys D),
  (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c ≠ ⊥ → ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B) ∧
  ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c, ∃ hu : PiTensorProduct.lift u ∈ (stY R t 0).CC (comR R t),
    u ≠ 0 → ∀ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B →
      IsPar (c := comR R t) (s := stY R t 0) ⟨_, hu⟩ B

def IPDict : Prop := ∀ t, ∀ k < D.R.m, ∀ ipD ip, IsMet (comR R t) (stY R t k) ipD ip → ∀ (x y : (stY R t k).CC (comR R t)) (a : ℂ),
  GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP R t k (PiTensorProduct.lift.symm x.1) (PiTensorProduct.lift.symm y.1) a ↔ a = ip y x

def StepExactNS (D : D7) : Prop := ForStepQ D fun c w k s s' p => ∀ ipD ip, IsMet c s ipD ip → ∀ m X, IsCovolOne (ratL s'.V s.V) m X →
  ∀ mR, IsLevMeas s mR → ∀ φ v, RealConv p m X φ v mR → ∀ (u₁ u₂ : s.CC c) B, IsPar u₁ B → IsQ w k u₁ →
    (∃ q ∉ c.S, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q ∧ GlobalTheory.Core.Rk.SW.NSAt B (c.chT (k + 1)) D.R.t q) →
    ∀ l, GlobalTheory.Cont.HolValueAt (fun z => GlobalTheory.LFun.LSD D c.S B (c.chT (k + 1)) (z + 1 / 2)) ((D.R.t : ℂ) / 2) l →
      s'.pet (p.up φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v))) (p.up φ (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v))) =
        conj ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℂ) * (l / dS (c.S : Set _) s s') * locQ c w k * ∫ g, zReal p m X φ v g ∂mR) * ip u₁ u₂

end GlobalTheory.ChainTw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.PinModel

variable {D : D7} {u : D.what₂.Word}

theorem exists_finM (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (V.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ a ∈ GfC V, GlobalTheory.AdForm.finM V hn a = y.1.1 := by
  subst hn
  obtain ⟨a, ha, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  refine ⟨a, ha, ?_⟩
  have e2 : (finE V a : GL _ _) = y.1 := congrArg Subtype.val e
  rw [← e2]
  rfl

theorem exists_transport_adelic_correction {X : HidaSetting D} {F : Formalism.L2.Forms.Forms0 D u} (tr : Formalism.L2.SG.ColDict.Transport X u F) :
    ∃ a, IsTransportAdelicCorrection tr a := by
  obtain ⟨a, ha, e⟩ := exists_finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) tr.h0
  exact ⟨a, ha, e⟩

theorem exists_isTypePlaces : ∃ Pg : Finset (Pl D.host.E), GlobalTheory.Core.Mi.IsTypePlaces Pg := by
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ PP : Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := fun v => by
    have := v.isMaximal
    obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    refine ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, ?_⟩
    exact HeightOneSpectrum.ext hQ'.over.symm
  choose s hs using key
  have hne : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hfin : {v : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)})
      (by rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hne)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  refine ⟨hfin.toFinset.image s, ?_, ?_⟩
  · intro PP hPP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP
    have hv' : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := hfin.mem_toFinset.1 hv
    rw [← hs v] at hv'
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (s v).asIdeal := hv'
    rwa [map_natCast] at h2
  · intro v hv
    refine ⟨s v, ⟨Finset.mem_image.2 ⟨v, hfin.mem_toFinset.2 hv, rfl⟩, hs v⟩, ?_⟩
    rintro PP ⟨hPP, e⟩
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hPP
    rw [hs w] at e
    rw [e]

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)

end GlobalTheory.Core.Mi.PinModel

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSphGL
noncomputable section

namespace GlobalTheory.Core.Rk.SWQ

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart)

section Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {m n N : ℕ}

def IntM {ι κ : Type} (x : Matrix ι κ (w.adicCompletion E)) : Prop := ∀ i j, x i j ∈ Ov E w

def mob (q r : ℕ) : ℂ := (-1) ^ r * (q : ℂ) ^ (r * (r - 1) / 2)

def cOne (q : ℕ) (z : ℂˣ) (σ : ℂ) (r : ℕ) : ℂ := mob q r * (z : ℂ) ^ r * (q : ℂ) ^ (-(σ * r))



end Local

section Adelic

variable {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

def cw (h : w.under (𝓞 D.host.F) = q) : AE D →+* w.adicCompletion D.host.E := (toCompl h).comp (compFin D.host.F D.host.E q)

def offM (q : FinPl D) {m n : ℕ} (x : Mx D m n) : Mx D m n :=
  x - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) • x

end Adelic

end GlobalTheory.Core.Rk.SWQ

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
  Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def scT {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) : PB.Terms τ Rw I H H₁ :=
  { X with scal := fun _ _ => True }

section Conc

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def cls1 (t : TauC Y u u) : Set (TauC Y u u) :=
  {t' | t' ∈ (Y.tO u u).genSet ∧ (Y.tO u u).rowOf t' = (Y.tO u u).rowOf t ∧ (Y.tO u u).s0 t t' = 1}

def NOf1 (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) :
    PN.NGData (TauC Y u u) D.host.E D.R.rS (Set (TauC Y u u)) (NuC D) :=
  { NOfG Y u νL νB ng with
    cls := cls1 Y u
    a2 := GlobalTheory.SnFam.a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL }

def GeneratorBoundAt (Γ : ℝ) : Prop := (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).genSet) ≤ Γ * ddC X Y u u

end Conc

def CorankOneIsEquivalenceOnRow : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    (∀ t ∈ (Y.tO u u').nzSet, (Y.tO u u').s0 t t = 1) ∧
    (∀ t ∈ (Y.tO u u').nzSet, ∀ t' ∈ (Y.tO u u').nzSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      (Y.tO u u').s0 t t' = 1 → (Y.tO u u').s0 t' t = 1) ∧
    (∀ t ∈ (Y.tO u u').nzSet, ∀ t' ∈ (Y.tO u u').nzSet, ∀ t'' ∈ (Y.tO u u').nzSet,
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' →
      (Y.tO u u').s0 t t' = 1 → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').s0 t t'' = 1)

def StepClass1 : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
      PN.ClassInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)

def StepNormals1 : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.NormalsInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)
          ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
            (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f))

def FamGen1 : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    GlobalTheory.SnFam.FamQ Y u u Not (Y.tO u u).genSet (cls1 Y u)

def StepFam1 : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u (sc s ν) ν (fun _ => 0)) γ →
          ∀ S : Finset (Set (TauC Y u u) × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u)) (NuC D),
            FamOKS (NOf1 Y u (sc s ν) ν (fun _ => 0)) γ S C0n
              (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)
              (fun L => ampG L) Fm

def StepLoc1 : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        LocalInputLeG (genT (scT (Y.tO u u))) (NOf1 Y u (sc s ν) ν (fun _ => 0)) C1 C0n
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)

def RowGen1P : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u → ConcTie X Y → (Y.tO u u).AbsConv →
      GeneratorBoundAt Y u (gamB D large₂ CB)

end GlobalTheory.Core.One
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.UpNeNSOfUpNe
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainNS

open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def invFam (B : GlobalTheory.LFun.Fam D.host.E) : GlobalTheory.LFun.Fam D.host.E := fun w => (B w).map (·⁻¹)

def ParBoundInv (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (invFam B) s.V.rank ((s.V.rank : ℝ) / 2)

def ChainNS (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ S' : Finset (HeightOneSpectrum (𝓞 D.host.F)), c.S ⊆ S' →
  ∀ B : GlobalTheory.LFun.Fam D.host.E,
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) →
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))) (invFam B) D.R.r ((D.R.r : ℝ) / 2) →
    ∀ k < D.R.m, ∃ q ∉ S', Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q ∧
      GlobalTheory.Core.Rk.SW.NSAt (chainPar c B k) (c.chT (k + 1)) D.R.t q

end GlobalTheory.ChainNS

end
end
