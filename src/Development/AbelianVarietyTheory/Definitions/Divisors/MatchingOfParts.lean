module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPToLiftReal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
namespace GlobalTheory.ThK

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def KDecay : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → Decay B G om om'

def KConst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om' R Rf, IsMatched B G X om om' R Rf → OneConst B G X om om' R Rf

def KCoinv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om' R Rf, IsMatched B G X om om' R Rf → Coinv B G X om om' Rf

def KBeta : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    StepBeta σ e₁ e₂ s

def KAlpha : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    StepAlpha σ e₁ e₂ s

def KReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ R, IsRealMaps B G om om' R

def KFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ Rf, IsFinMaps B G X om om' Rf

theorem agree_of_parts (h1 : KDecay) (h2 : KConst) (h3 : KCoinv) (h4 : KBeta) (h5 : KAlpha) : ThetaIntegralsAgree :=
  ⟨fun F E _ _ _ _ _ σ B a a' G X om om' h => ⟨h1 F E σ B a a' G X om om' h,
    fun R Rf m => ⟨h2 F E σ B a a' G X om om' R Rf m, h3 F E σ B a a' G X om om' R Rf m⟩⟩, h4, h5⟩

theorem matching_of_parts (h1 : KReal) (h2 : KFin) : LocalMatching := by
  unfold KReal at h1
  unfold KFin at h2
  intro F E _ _ _ _ _ σ B a a' G X om om' h
  obtain ⟨R, r⟩ := h1 F E σ B a a' G X om om' h
  obtain ⟨Rf, f⟩ := h2 F E σ B a a' G X om om' h
  exact ⟨R, Rf, h, r, f⟩

end GlobalTheory.ThK
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

abbrev Mt (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def frDom (Hm : Mt n) (q : ℕ) : Set (Mt n) :=
  {x | x.det ≠ 0 ∧ ∀ i : Fin (n + 1),
    0 < ReciprocityTheory.ChartRestriction.G.FD.psgn q i * (ReciprocityTheory.ChartRestriction.G.FD.lminor (-(xᴴ * Hm * x)) i).re}

def UpT (b : Mt n) : Prop := b.det ≠ 0 ∧ ∀ a c : Fin n, c < a → b a c = 0

def OrthFr (Hm : Mt n) (q : ℕ) (x₀ : Mt n) : Prop :=
  q ≤ n ∧ x₀ᴴ * Hm * x₀ = diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)

def UG (Hm : ι → Mt n) : Set (ι → Mt n) := {u | ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (Hm τ)}

def frDoms (Hm : ι → Mt n) (q : ι → ℕ) : Set (ι → Fin n → Fin n → ℂ) := {x | ∀ τ, Matrix.of (x τ) ∈ frDom (Hm τ) (q τ)}

def HolSec (Hm : ι → Mt n) (q : ι → ℕ) (w : ι → Fin n → ℤ) (P : (ι → Fin n → Fin n → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ P (frDoms Hm q) ∧
    ∀ x ∈ frDoms Hm q, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) →
      P (fun τ => (Matrix.of (x τ) * b τ : Mt n)) = (∏ τ, ∏ a, b τ a a ^ w τ a) * P x

def HolFn (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ) (f : (ι → Mt n) → ℂ) : Prop :=
  ∃ P, HolSec Hm q w P ∧ ∀ u ∈ UG Hm, f u = P fun τ => (u τ * x₀ τ : Mt n)

def lieH (Hm : Mt n) : Set (Mt n) := {X | Xᴴ * Hm + Hm * X = 0}

def SmFn (Hm : ι → Mt n) (f : (ι → Mt n) → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → ι) (Xs : Fin k → Mt n), (∀ i, Xs i ∈ lieH (Hm (τs i))) → ∀ u ∈ UG Hm,
    ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      f (u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod)

def der (τ : ι) (X : Mt n) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : ℂ :=
  deriv (fun t : ℝ => f (u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n))) 0

def conjH (Hm Z : Mt n) : Mt n := -(Hm⁻¹ * Zᴴ * Hm)

def derC (Hm : ι → Mt n) (τ : ι) (Z : Mt n) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : ℂ :=
  der τ ((1 / 2 : ℂ) • (Z + conjH (Hm τ) Z)) f u + Complex.I * der τ ((1 / (2 * Complex.I)) • (Z - conjH (Hm τ) Z)) f u

def KilledFn (Hm : ι → Mt n) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ) (f : (ι → Mt n) → ℂ) : Prop :=
  ∀ τ (a c : Fin n), a ≤ c → ∀ u ∈ UG Hm,
    derC Hm τ (x₀ τ * Matrix.single a c 1 * (x₀ τ)⁻¹) f u = if a = c then (w τ a : ℂ) * f u else 0

def torEl (x₀ : ι → Mt n) (s : ι → Fin n → ℝ) : ι → Mt n :=
  fun τ => x₀ τ * diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) * (x₀ τ)⁻¹

def torCh (w : ι → Fin n → ℤ) (s : ι → Fin n → ℝ) : ℂ := ∏ τ, ∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a

def dRepC {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (Z : Mt n) (v : H) : H :=
  dRep σ ((1 / 2 : ℂ) • (Z + conjH Hm Z)) v + Complex.I • dRep σ ((1 / (2 * Complex.I)) • (Z - conjH Hm Z)) v

def gelfRep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (k : ℕ) (v : H) : H :=
  ∑ idx : Fin (k + 1) → Fin n,
    (List.ofFn fun a : Fin (k + 1) => dRepC Hm σ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) v

def InZe (Hm : Mt n) (e : Fin n → ℂ) (m : Mt n) : Prop :=
  ∃ s : ℝ, m = 1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm)

end Local

section Adelic

variable {D : D7}

def HolShape {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Prop :=
  ∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ p ≤ V.rank, ∀ a, M.ε τ a = decide ((a : ℕ) < p)

def WtIs {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) : Prop :=
  ∀ τ c, (w τ c : ℝ) = extWt M τ (arr (nNeg (M.ε τ)) c)


open Classical in
def HolAd (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (φ : GA D V → ℂ) : Prop :=
  ∀ g, ∃ f, HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w f ∧
    ∀ u ∈ GinfC V, φ (g * u) = f fun τ => archM V (θ τ) u

def ZI (V : HSp D) (ξ : Fin V.rank → D.host.E) : Subgroup (GA D V) :=
  Subgroup.closure {g | ∃ a : AF D.host.F ⊗[D.host.F] D.host.E,
    ((matHom V g).1 - 1 : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
      a • (vecMulVec ξ ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram)).map (incA D)}

def IsoVec (V : HSp D) (ξ : Fin V.rank → D.host.E) : Prop :=
  ξ ≠ 0 ∧ (fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ⬝ᵥ V.gram.mulVec ξ = 0

def ZCusp (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ ξ, IsoVec V ξ → ∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure →
    IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → ∀ g, ∫ z in 𝓕, φ ((z : GA D V) * g) ∂μ = 0

structure HolForm (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (φ : GA D V → ℂ) : Prop where
  aut : IsAutFun V φ
  bdd : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C
  lev : ∀ k ∈ J, ∀ g, φ (g * k) = χ k * φ g
  hol : HolAd θ M w φ

structure FinPair (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop where
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  fd : IsFundamentalDomain (GQ V) 𝓕 μ
  fin : μ 𝓕 ≠ ⊤

def nuQ (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Measure (AutQ V) := (μ.restrict 𝓕).map (autMk V)

def Repr (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (F : Lp ℂ 2 (nuQ V μ 𝓕)) (ψ : GA D V → ℂ) : Prop :=
  ∀ᵐ x ∂μ, F (autMk V x) = ψ x

structure IsReg (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))) : Prop where
  val : ∀ g F, ∀ᵐ x ∂μ, ρ g F (autMk V x) = F (autMk V (x * g))
  iso : ∀ g F, ‖ρ g F‖ = ‖F‖
  cont : ∀ F, Continuous fun g => ρ g F

def IsSmoothVector' (θ : InfFam D) (V : HSp D) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (F : K) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod F

def dL2 (θ : InfFam D) (V : HSp D) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (p : D.what₂.Tau × Mt V.rank) (F : K) : K :=
  deriv (fun t : ℝ => ρ (oneP θ V p.1 p.2 t) F) 0

structure GoodDict (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    {r : ℕ} (hr : V.rank = r) {Comp : Type} (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r)
    (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) (Kf : Subgroup (GA D V)) : Prop where
  inf : IsInfFam θ
  base : BaseFr M θ hr dict
  unif : ∃ th, (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr
  model : ∀ k, ModelW V hr (X k)
  muUnit : MuUnit V dict mu
  muCont : Continuous mu
  chi : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1
  cNe : ∀ k, c k ≠ 0
  cBdd : ∃ C : ℝ, ∀ k, ‖c k‖ ≤ C
  fin : Finite Comp
  levFin : Kf ≤ GfC V
  levOpen : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ Kf
  muK : ∀ k ∈ Kf, mu k = 1
  wt : ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ e ρ) ∧
    ∀ k ρ (τ : (X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin V.rank, w ρ a = la k τ (Fin.cast hr a) + e ρ

end Adelic

end GlobalTheory.HolDict
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsPair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) : Prop where
  weil : IsWeilDatumO ψ V W χV χW om
  inf : IsInfFam θ
  std : V.gram = 1
  even : Even V.rank
  sigV : V.SigOK
  sigW : W.SigOK
  expV : ∀ τ, ∃ a : ℤ, HasInfExp D χV τ a
  expW : ∀ τ, ∃ b : ℤ, HasInfExp D χW τ ((b : ℚ) + (W.rank : ℚ) / 2)
  unr : ∀ v ε, NonSplitAt D v ε → UnramAt ε χV ∧ UnramAt ε χW
  eta : ∃ η, IsEtaTilde D η

def MarkAd {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (W : HSp D) {r : ℕ} (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (h : GA D W) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat W h,
    finVec W (mk a ∘ Fin.cast hr) - (finHom W h).1.mulVec (finVec W (ι a)) = (l.M : ℕ) • w

def hatC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H)
    {n : ℕ} (φ : (Fin n → LevQc Dw l) → ℂ) (q : Fin n → LevQ Dw l) : ℂ :=
  ∑ᶠ x : Fin n → LevQc Dw l, φ x * Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) ^
    pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b))

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def SerOf (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧
    ∀ (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
      RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) →
      ∀ (y : (R.HV i (tup t)).H) (x : O.Cl' t → VsV D i O.c'.F), Place R i (tup t) h O.c0' y x →
      ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank,
        IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f →
        ∀ g : GA D (Wc D i), ph * R.thF i (tup t) y v₀ g =
          cc (O.dict g).1 * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.mu g *
            rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2

end

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory.Cartier

namespace GlobalTheory.LogDR

section Algebra

abbrev abelian₂ (K : Type) [Field K] : Type := ExteriorAlgebra K Ω[K⁄ℤ]

variable {K : Type} [Field K]

abbrev dK (f : K) : Ω[K⁄ℤ] := KaehlerDifferential.D ℤ K f


variable (K) in
def extD : abelian₂ K →+ abelian₂ K := (CechDR.dDR ℤ K).toAddMonoidHom

theorem extD_apply (η : abelian₂ K) : extD K η = CechDR.dDR ℤ K η := rfl

def dlog (g : Kˣ) : Ω[K⁄ℤ] := ((g⁻¹ : Kˣ) : K) • dK (g : K)

def spanForms (M : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ) : AddSubgroup (abelian₂ K) :=
  AddSubgroup.closure
    {η | ∃ c ∈ M, ∃ v : Fin a → Ω[K⁄ℤ], (∀ i, v i ∈ H) ∧ η = c • ExteriorAlgebra.ιMulti K a v}

def frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) : Ω[K⁄ℤ] :=
  if i ∈ J then dlog (x i) else dK (x i : K)

def logWedge {n : ℕ} (x : Fin n → Kˣ) (I : Finset (Fin n)) : abelian₂ K :=
  ((I.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι K (dlog (x i))).prod

def chartForms (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) :
    AddSubgroup (abelian₂ K) :=
  spanForms {c | c * t ∈ A} (Set.range (frame x J)) a

def IsCoord {n : ℕ} (x : Fin n → Kˣ) : Prop :=
  LinearIndependent K (fun i => dK (x i : K)) ∧
    Submodule.span K (Set.range fun i => dK (x i : K)) = ⊤

structure AlgChart (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) : Prop where

  mem : ∀ i, (x i : K) ∈ A

  coord : IsCoord x

  deriv : ∀ f ∈ A, ∃ c : Fin n → K, (∀ i, c i ∈ A) ∧ dK f = ∑ i, c i • dK (x i : K)

  root : ∀ (S : Finset (Fin n)) (g : K) (m : ℕ), 0 < m →
    g ^ m / ∏ j ∈ S, (x j : K) ∈ A → g / ∏ j ∈ S, (x j : K) ∈ A

def IsCartierMap (p : ℕ) {n : ℕ} (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K) : Prop :=
  (∀ c : K, γ (algebraMap K (abelian₂ K) c) = algebraMap K (abelian₂ K) (c ^ p)) ∧
    ∀ i, γ (ExteriorAlgebra.ι K (dlog (x i))) = ExteriorAlgebra.ι K (dlog (x i))

def IsEulerContraction {n : ℕ} (x : Fin n → Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K) : Prop :=
  θ 1 = 0 ∧ (∀ (v : Ω[K⁄ℤ]) (η : abelian₂ K),
    θ (ExteriorAlgebra.ι K v * η) = θ (ExteriorAlgebra.ι K v) * η - ExteriorAlgebra.ι K v * θ η) ∧
    ∀ j, θ (ExteriorAlgebra.ι K (dlog (x j))) = if j = i then 1 else 0

end Algebra

section Scheme

variable {X : Scheme.{0}} [IsIntegral X]

def locRing (y : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk y) X.functionField).range

theorem mem_locRing {y : X} {f : X.functionField} : f ∈ locRing y ↔ RegAt y f := Iff.rfl

def LogUnit (Z : Set X) (y : X) (g : X.functionFieldˣ) : Prop :=
  ∀ z : X, z ⤳ y → z ∉ Z → UnitAt z (g : X.functionField)

def logAt (Z : Set X) (G : CartierDiv X) (a : ℕ) (y : X) : AddSubgroup (abelian₂ X.functionField) :=
  spanForms {c | G.RegularAt y c} (dlog '' {g | LogUnit Z y g}) a


omit [IsIntegral X] in
def latSec {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) (U : X.Opens) : AddSubgroup V :=
  ⨅ y ∈ U, M y

abbrev logSec (Z : Set X) (G : CartierDiv X) (a : ℕ) (U : X.Opens) :
    AddSubgroup (abelian₂ X.functionField) :=
  latSec (logAt Z G a) U

structure IsLogChart (Z : Set X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ)
    (J : Finset (Fin n)) : Prop where

  chart : ∀ y ∈ U, AlgChart (locRing y) x

  logUnit : ∀ y ∈ U, ∀ g : X.functionFieldˣ, LogUnit Z y g ↔
    ∃ (u : X.functionFieldˣ) (m : Fin n → ℤ), UnitAt y (u : X.functionField) ∧ g = u * ∏ j ∈ J, x j ^ m j

def IsSncOn {C : Type} (E : C → CartierDiv X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ)
    (J : Finset (Fin n)) : Prop :=
  ∃ e : C → Option (Fin n), (∀ c c' j, e c = some j → e c' = some j → c = c') ∧
    (∀ j, j ∈ J ↔ ∃ c, e c = some j) ∧
    ∀ c, ∀ y ∈ U, (E c).IsEqn y ((e c).elim 1 x)

def suppAll {C : Type} (E : C → CartierDiv X) : Set X := ⋃ c, ((E c).supp : Set X)

structure SncAtlas {C : Type} (E : C → CartierDiv X) (n : ℕ) (ι : Type) where

  U : ι → X.Opens

  x : ι → Fin n → X.functionFieldˣ

  J : ι → Finset (Fin n)

  affine : ∀ i, IsAffineOpen (U i)

  gen : ∀ i, genericPoint X ∈ U i

  cover : ⨆ i, U i = ⊤

  chart : ∀ i, IsLogChart (suppAll E) (U i) (x i) (J i)

  snc : ∀ i, IsSncOn E (U i) (x i) (J i)

structure LatModel {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V)
    (F : X.Modules) where

  val : ∀ U : X.Opens, genericPoint X ∈ U → (Γ(F, U) →+ V)

  inj : ∀ U h, Function.Injective (val U h)

  range : ∀ U h, (val U h).range = latSec M U

  res : ∀ (U W : X.Opens) (e : W ≤ U) (h : genericPoint X ∈ W) (s : Γ(F, U)),
    val W h (F.presheaf.map (homOfLE e).op s) = val U (e h) s

  smul : ∀ U h (r : Γ(X, U)) (s : Γ(F, U)), val U h (r • s) = fnOf U h r • val U h s

end Scheme

end GlobalTheory.LogDR
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped TensorProduct

namespace GlobalTheory.ResW

def blkE {r s N : ℕ} (h : r + s = N) : Fin r ⊕ Fin s ≃ Fin N := finSumFinEquiv.trans (finCongr h)

def blkM (R : Type) [CommRing R] {r s N : ℕ} (h : r + s = N) :
    Matrix (Fin r) (Fin r) R × Matrix (Fin s) (Fin s) R →* Matrix (Fin N) (Fin N) R where
  toFun p := Matrix.reindex (blkE h) (blkE h) (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def blk {R : Type} [CommRing R] {r s N : ℕ} (h : r + s = N) : GL (Fin r) R × GL (Fin s) R →* GL (Fin N) R :=
  (Units.map (blkM R h)).comp MulEquiv.prodUnits.symm.toMonoidHom

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N r s m a : ℕ}


variable (E) in
def nu (t : ℝ) : HChar E := GlobalTheory.HeckeGal.Model.absPow E t





section Passive

variable {M : Type} [AddCommGroup M] [Module ℂ M]

end Passive


variable (E) in
abbrev Letter : Type := Σ a : ℕ, CuspSub E a

def wsize (u : List (Letter E)) : ℕ := (u.map (·.1)).sum

noncomputable def Vec : List (Letter E) → Type
  | [] => PUnit
  | x :: u => x.2.V × Vec u


variable (E N) in
def zc : Module.End ℂ (Sm E N) := lie E N fun i j => if i = j then 1 else 0

def cex (x : Letter E) : ℂ := Classical.epsilon fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ

def rexp (x : Letter E) : ℝ := (cex x).re / (x.1 * Module.finrank ℚ E)

def tw (x : Letter E) (t : ℝ) : Letter E := ⟨x.1, x.2.twist (nu E t)⟩

def SatVec (φ : Sm E N) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop :=
  ∀ᶠ v in Filter.cofinite, GlobalTheory.LFun.IsSatVecGL v ((finRep E N).comp (locGL E N v)) φ (B v)

def SatFam (V : Submodule ℂ (Sm E N)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop := ∀ φ ∈ V, φ ≠ 0 → SatVec φ B


end GlobalTheory.ResW

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

variable {p : ℕ} [Fact p.Prime]

structure DPair (G : HTGroup p) where

  β : G.Cˣ

  γ : G.Cˣ

  c : ℚˣ
  sym : sh G β = β
  sim : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β
  reg : (minpoly G.F (γ : G.C)).natDegree = G.n ∧ (minpoly G.F (γ : G.C)).Separable
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t

  posR : ∀ v : InfinitePlace G.F, ∀ x : Fin G.n → ℂ, x ≠ 0 →
    (sigPosH (G.gram_herm v) = 1 → 0 < (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re < 0)

namespace DPair

variable {G : HTGroup p}

def pol (P : DPair G) : Polynomial G.F := minpoly G.F (P.γ : G.C)

def Rel (P Q : DPair G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y) ∧ Q.γ = y * P.γ * y⁻¹

def cent (P : DPair G) : Subgroup (G.Cˣ × ℚˣ) where
  carrier := {y | y.1 * P.γ = P.γ * y.1 ∧ (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C y.2 * P.β}
  one_mem' := ⟨by simp, by simp [sh]⟩
  mul_mem' := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, ?_⟩
    · change y * y' * P.γ = P.γ * (y * y')
      change y * P.γ = P.γ * y at h1
      change y' * P.γ = P.γ * y' at h1'
      rw [mul_assoc, h1', ← mul_assoc, h1, mul_assoc]
    · change (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β at h2
      change (y' : G.C) * P.β * sh G y' = algebraMap ℚ G.C s' * P.β at h2'
      change ((y * y' : G.Cˣ) : G.C) * P.β * sh G ((y * y' : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s * s' : ℚˣ) : ℚ) * P.β
      have e : sh G ((y * y' : G.Cˣ) : G.C) = sh G y' * sh G y := by
        simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
      rw [e, Units.val_mul, Units.val_mul, map_mul]
      calc (y : G.C) * y' * P.β * (sh G y' * sh G y) = y * (y' * P.β * sh G y') * sh G y := by
            simp only [mul_assoc]
        _ = algebraMap ℚ G.C s' * (y * P.β * sh G y) := by
            rw [h2']; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
        _ = _ := by rw [h2, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (s' : ℚ)]
  inv_mem' := by
    rintro ⟨y, s⟩ ⟨h1, h2⟩
    change y * P.γ = P.γ * y at h1
    change (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β at h2
    refine ⟨?_, ?_⟩
    · change y⁻¹ * P.γ = P.γ * y⁻¹
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_inv_cancel_right]
    · change ((y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * P.β
      have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        simp only [sh]
        rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
      have hs : algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ G.C (s : ℚ) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      calc ((y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y⁻¹ : G.Cˣ) : G.C)
          = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * (((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (s : ℚ) * P.β) *
              sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
            rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.commutes ((s⁻¹ : ℚˣ) : ℚ), mul_assoc ((y⁻¹ : G.Cˣ) : G.C) _ (algebraMap ℚ G.C (s : ℚ)), hs, mul_one]
        _ = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * ((((y⁻¹ : G.Cˣ) : G.C) * y) * P.β *
              (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
            rw [← h2]; simp only [mul_assoc]
        _ = _ := by rw [Units.inv_mul, e, one_mul, mul_one]

def self (P : DPair G) : P.cent := ⟨(P.γ, P.c), rfl, P.sim⟩

def toAf (P : DPair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) : P.cent →* G.GAf :=
  MonoidHom.codRestrict
    ((((MulAut.conj x).toMonoidHom.comp (Units.map (inC G (AfP p)).toMonoidHom)).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).comp P.cent.subtype) _ fun y => by
      have h := congrArg (inC G (AfP p)) y.2.2
      rw [map_mul, map_mul, map_mul] at h
      have e1 : inC G (AfP p) (sh G y.1.1) = (starT G.star (AfP p) (inC G (AfP p) y.1.1)).unop :=
        (starT_tmul G.star (AfP p) 1 _).symm
      have e2 : inC G (AfP p) (algebraMap ℚ G.C y.1.2) =
          algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) y.1.2) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
      rw [e1, e2] at h
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) P.β) x
        (Units.map (inC G (AfP p)).toMonoidHom y.1.1) t _ hx h

def atP (P : DPair G) : Gp G := locC G (P.γ, P.c)

def toQr (P : DPair G) (r : ℕ) (z : Gr G r) : P.cent →* Gr G r :=
  ((carry G r z).comp (locC G)).comp P.cent.subtype

def termAt (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r) : ℂ :=
  GlobalTheory.LKCount.pointSum (P.toAf x t hx) (P.toQr r z) (sigG G r) Kf K (P.toAf x t hx P.self) δ f φ

def term (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  if h : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 then
    P.termAt Kf f r K φ P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec
      h.choose.1 h.choose.2
  else 0

variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
private theorem lkMid_sh_mul_eq_sh_mul_sh_rev (a b : G.C) :
    _root_.GlobalTheory.LKMid.sh G (a * b) =
      _root_.GlobalTheory.LKMid.sh G b * _root_.GlobalTheory.LKMid.sh G a := by
  simp only [_root_.GlobalTheory.LKMid.sh, map_mul, MulOpposite.unop_mul]

variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
private theorem lkMid_sh_mul_sh_units_inv_eq_one (y : (G.C)ˣ) :
    _root_.GlobalTheory.LKMid.sh G y *
      _root_.GlobalTheory.LKMid.sh G ((y⁻¹ : (G.C)ˣ) : G.C) = 1 := by
  rw [← lkMid_sh_mul_eq_sh_mul_sh_rev, Units.inv_mul, _root_.GlobalTheory.LKMid.sh_one_eq]


variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.rel_equivalence (G : _root_.GlobalTheory.LKTrip.HTGroup p) :
    Equivalence (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) := by
  refine ⟨fun P => ?_, fun {P₁ P₂} h => ?_, fun {P₁ P₂ P₃} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, by simp⟩
    simp [_root_.GlobalTheory.LKMid.sh_one_eq]
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul,
        inv_mul_cancel₀ hs.ne', one_smul]
      simp only [mul_assoc, Units.inv_mul_cancel_left, lkMid_sh_mul_sh_units_inv_eq_one, mul_one]
      rw [mul_inv_cancel₀ hs.ne', one_smul]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, lkMid_sh_mul_eq_sh_mul_sh_rev]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
      rw [mul_comm s s']
    · rw [hγ', hγ]; group

theorem pol_eq_of_rel {P Q : DPair G} (h : P.Rel Q) : Q.pol = P.pol := by
  obtain ⟨y, s, _, _, hγ⟩ := h
  have h := minpoly.algEquiv_eq (Pair.innerAlgEquiv G.F y) (P.γ : G.C)
  simp only [pol, hγ, Units.val_mul]
  exact h


variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.mk_eq_iff (P Q : _root_.GlobalTheory.LKDef.DPair G) :
    Quot.mk (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) P = Quot.mk _ Q ↔
      P.Rel Q :=
  ⟨fun h => (_root_.GlobalTheory.LKDef.DPair.rel_equivalence G).eqvGen_iff.mp (Quot.eqvGen_exact h),
    Quot.sound⟩


variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.rel_out (P : _root_.GlobalTheory.LKDef.DPair G) :
    P.Rel
      (Quot.out (Quot.mk (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) P)) :=
  (_root_.GlobalTheory.LKDef.DPair.mk_eq_iff P _).mp (Quot.out_eq _).symm

end DPair

def DCls (G : HTGroup p) : Type := Quot (DPair.Rel (G := G))

def dSumIrr (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : DCls G, if Irreducible (Quot.out q).pol then wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

namespace Example

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example

end Example

end GlobalTheory.LKDef
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsoRows
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

section Coord

variable {R : Type} [CommRing R] {κ κ₁ : Type}

variable [Fintype κ] [Fintype κ₁] {W W₁ : Type} [AddCommGroup W] [Module R W] [AddCommGroup W₁] [Module R W₁]
  {B : W → W → R} {B₁ : W₁ → W₁ → R}

end Coord

section Frame

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α α₁ ν : Type} [Fintype α] [DecidableEq α] [Fintype α₁] [DecidableEq α₁] [Fintype ν] [DecidableEq ν]

structure IsFrame (J : Matrix α α A) (C D : Matrix α ν A) (ι : Matrix α α₁ A) : Prop where
  cc : Cᵀ * J * C.map c = 0
  dd : Dᵀ * J * D.map c = 0
  cd : Cᵀ * J * D.map c = 1
  ic : ιᵀ * J * C.map c = 0
  ci : Cᵀ * J * ι.map c = 0
  id : ιᵀ * J * D.map c = 0
  di : Dᵀ * J * ι.map c = 0
  basis : ∃ M : Matrix ((ν ⊕ ν) ⊕ α₁) α A, Matrix.fromCols (Matrix.fromCols C D) ι * M = 1 ∧
    M * Matrix.fromCols (Matrix.fromCols C D) ι = 1

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


def IsRat {α β κ : Type} [Fintype κ] {B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F} (d : Darboux B κ) : Prop :=
  ∀ x : Matrix α β E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

variable (σ : E →ₐ[F] E)

variable {σ}


end GlobalTheory.TowU

end
end
