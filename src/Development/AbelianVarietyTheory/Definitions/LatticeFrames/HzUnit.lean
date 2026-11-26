module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {c : Comm D}

def withMu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ)
    (μ : ℕ → kˣ →* ℂˣ) (h : ∀ j, IsTame (μ j)) : SymData k s κ := { S with μ := μ, tame := h }

def VCom.withCG (v : VCom c) (a : ℕ → ℂ) : VCom c := { v with cG := a }

def Comm.VolLast (c : Comm D) : Prop :=
  ∀ j (h : j + 2 * 0 + 2 = D.R.m), (c.vol (j + 1)).μ = Measure.map (c.jac j 0 h).d.emb0 (c.x (j + 1)).vol.μ

def IntIn {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k)
    (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (L : GlobalTheory.FinPl.Lat S) : Prop :=
  ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)

structure GLoc (v : VCom c) where
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
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  S : SymData k s D.R.k
  char : (ofSplit q).IsChar c.ψ S.ψ
  FX : ∀ j, j ≤ s + 1 → Frame k (c.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k c.T.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (c.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  FY : ∀ j a, j + a = s + 1 → Frame k (c.V j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin a)
  sc : ℕ → k
  sc_unit : ∀ j, valuation k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi
  hz_unit : ∀ j ρ h, valuation k ((ofSplit q).hz (c.B j ρ h)) = 1
  bes : ∀ j ρ h a (ha : j + a = s + 1), (ofSplit q).IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) (FY j a ha)
  jac : ∀ j ρ h a (ha : j + 1 + a = s + 1), (ofSplit q).IsJacFrame (c.J j ρ h) (sc j)
    ((ofSplit q).hz (c.B j ρ h)) (FX (j + 1) (by omega)) (FY (j + 1) a ha)
  z₀ : Fin c.Lz.rank → k
  last : FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  tau : ∀ h, (v.τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i)
  latX : ∀ j hj, IntIn q (c.X j) (FX j hj) (c.x j).L
  latM : IntIn q (c.X (s + 1 + 1)) FM (c.x (s + 1 + 1)).L
  latY : ∀ j a ha, IntIn q (c.V j) (FY j a ha) (v.N j)
  latT : IntIn q c.T FT v.NT

  eg : ∀ j, WO (c.V j) (c.V (j + 1)) →₀ ℂ
  eg_is : ∀ j a (H : j + a = s), (ofSplit q).IsCombAt c.ψ (FY j (a + 1) (by omega)) (FY (j + 1) a (by omega)) (eg j)
    ((S.T (Fin D.R.t)).Phi j a H)
  egT : WO (c.V (s + 1)) c.T →₀ ℂ
  egT_is : (ofSplit q).IsCombAt c.ψ (FY (s + 1) 0 rfl) FT egT (S.T (Fin D.R.t)).PhiTop

  cg : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j a (H : j + 1 + a = s), (ofSplit q).IsCombAt c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j a H 1 1)
  cg_pen : (ofSplit q).IsCombAt c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GLoc.fld GLoc.val GLoc.top GLoc.loc GLoc.mea GLoc.bor

variable {v : VCom c}

def GLoc.Mat (G : GLoc v) (j a : ℕ) (ha : j + a = G.s + 1) (g : GA D (c.V j))
    (x : GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin a) G.k) : Prop :=
  (mt (c.V j) g).map G.q.pr = (G.FY j a ha).β * x.val * (G.FY j a ha).γ

structure GPin {n : ℕ} (G : Fin n → GLoc v) : Prop where
  inj : Function.Injective fun i => (G i).q.v
  places : ∀ p, p ∈ v.gP ↔ ∃ i, p = (G i).q.v
  lev : ∀ j, j < D.R.m → ∀ g, g ∈ v.JG j ↔ g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ∈ v.gP) ∧
    ∀ i a ha x, (G i).Mat j a ha g x → x ∈ (((G i).S.T (Fin D.R.t)).lev j a ha).J
  eG : ∀ j, j + 1 < D.R.m → ∀ f, IsThetaFunO c.ψ _ _ f → comb c.ψ _ _ (v.eG j) f =
    (List.finRange n).foldr (fun i f' => comb c.ψ _ _ ((G i).eg j) f') f
  eGT : ∀ j h, ∃ e : Fin n → WO (c.V (j + 1)) c.T →₀ ℂ, (∀ i, HEq (e i) (G i).egT) ∧
    ∀ f, IsThetaFunO c.ψ _ _ f → comb c.ψ _ _ (v.eGT j h) f = (List.finRange n).foldr (fun i f' => comb c.ψ _ _ (e i) f') f
  dG : ∀ j, j < D.R.m → ∀ f, IsThetaFunO c.ψ _ _ f → comb c.ψ _ _ (v.dG j) f =
    (List.finRange n).foldr (fun i f' => comb c.ψ _ _ ((G i).cg j) f') f

def GLoc.Chars (G : GLoc v) (t : Tup c) : Prop :=
  ∃ μ : ℕ → G.kˣ →* ℂˣ, (∀ j, IsTame (μ j)) ∧ (∀ j (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ j x = G.S.μ j x) ∧
    (∀ j ρ h, (ofSplit G.q).IsComp (t.sBF j ρ h).χV⁻¹ (μ (j + 1)) ∧
      ∃ μ', (ofSplit G.q).IsComp (t.sBF j ρ h).χW μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1) ∧
    ∀ j σ h, (ofSplit G.q).IsComp (t.sFB j σ h).χV⁻¹ (μ (j + 1 + 1)) ∧
      ∃ μ', (ofSplit G.q).IsComp (t.sFB j σ h).χW μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1 + 1) x = 1

def GLam {n : ℕ} (G : Fin n → GLoc v) (j : ℕ) (g : GA D (c.V j)) (a : ℂ) : Prop :=
  ∃ (b : Fin n → ℕ) (hb : ∀ i, j + b i = (G i).s + 1) (x : ∀ i, (((G i).S.T (Fin D.R.t)).lev j (b i) (hb i)).J),
    (∀ i, (G i).Mat j (b i) (hb i) g (x i).1) ∧ a = ∏ i, ((((G i).S.T (Fin D.R.t)).lev j (b i) (hb i)).lam (x i) : ℂ)

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7}

def UnitRatio (S : ℕ → Prop) (x y : ℂ) : Prop :=
  y ≠ 0 ∧ ∃ n : ℕ, 0 < n ∧ ∃ r : ℚ, r ≠ 0 ∧ (x / y) ^ n = (r : ℂ) ∧ ∀ p : ℕ, p.Prime → padicValRat p r ≠ 0 → S p

structure Base (c : Comm D) where
  Λ : ∀ j, GlobalTheory.FinPl.Lat (c.V j)
  β : ∀ j, GL (Fin (c.V j).rank) (Lev.EAf D)
  b : ∀ j, GA D (c.V j)

  ΛT : GlobalTheory.FinPl.Lat c.T
  βT : GL (Fin c.T.rank) (Lev.EAf D)
  bT : GA D c.T
  LT : GlobalTheory.FinPl.Lat c.T
  Pg : Finset (Formalism.L2.DIV.Pl D.host.E)
  P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ

variable {c : Comm D}


open Classical in
def Base.S (B : Base c) : Finset (GlobalTheory.FinPl.Pl D) := B.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

section Off

open GlobalTheory.FinPl

structure Off (B : Base c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where
  p : ι → SplitPt D k

  I : List ι

  q : Unif k

  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1

  β : ∀ j i, Frame (p i) (c.X j) (Fin (c.X j).rank)

  Q : ∀ j, ι → Pair k (Fin (c.X j).rank)

  β₀ : ∀ j ρ h i, Frame (p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)

  L : ∀ j, Lat (c.V j)

  M : ∀ j ρ h, Lat (c.bes j ρ h).V₀

  cT : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ

  cG : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ

  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E

  ζ₀ : Fin c.Lz.rank → D.host.E

  γ : ∀ i, Frame (p i) c.T (Fin c.T.rank)

  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (c.X n) (Fin c.T.rank ⊕ Fin 1)

variable {B : Base c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : Off B k ι)

namespace Off

end Off

end Off

section AtLevel

open GlobalTheory.LocMod

structure GAt (B : Base c) (τ : ∀ j h, Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E)
    (PP : Formalism.L2.DIV.Pl D.host.E) where
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
  char : (ofSplit q).IsChar c.ψ S.ψ
  FX : ∀ j, j ≤ s + 1 → Frame k (c.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k c.T.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (c.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  FY : ∀ j cc, j + cc = s + 1 → Frame k (c.V j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin cc)
  sc : ℕ → k
  sc_unit : ∀ j, valuation k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi
  hz_unit : ∀ j ρ h, valuation k ((ofSplit q).hz (c.B j ρ h)) = 1
  bes : ∀ j ρ h cc (hc : j + cc = s + 1), (ofSplit q).IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) (FY j cc hc)
  jac : ∀ j ρ h cc (hc : j + 1 + cc = s + 1), (ofSplit q).IsJacFrame (c.J j ρ h) (sc j)
    ((ofSplit q).hz (c.B j ρ h)) (FX (j + 1) (by omega)) (FY (j + 1) cc hc)
  z₀ : Fin c.Lz.rank → k
  last : FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  tau : ∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i)
  latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.X j) (c.x j).L (· = q.v)
  latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.X (s + 1 + 1)) (c.x (s + 1 + 1)).L (· = q.v)
  frame : ∀ j cc (hc : j + cc = s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) j ≃ Fin (c.V j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) (c.V j) (B.b j) (B.β j)
      (((FY j cc hc).β * ((S.T (Fin D.R.t)).bas j cc hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j cc hc (e.symm i))
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin c.T.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) c.T B.bT B.βT (FT.β.submatrix id e.symm)
  cg : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j cc (H : j + 1 + cc = s), (ofSplit q).IsCombAt c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j cc H 1 1)
  cg_pen : (ofSplit q).IsCombAt c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GAt.fld GAt.val GAt.top GAt.loc GAt.mea GAt.bor

variable {B : Base c} {τ : ∀ j h, Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E}

end AtLevel



end GlobalTheory.Fam

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def intVec (D : D7) (n : ℕ) : Set (Fin n → D.host.E) := {x | ∀ k, IsIntegral ℤ (x k)}

def IsFinComb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO S T), (∀ k, (x k).map (infPart D) = 0) ∧ f = ∑ k, c k • heisO ψ S T (x k) f₀

abbrev stdHom {D : D7} (S T : HSp D) : AddSubgroup (WO S T) := latO S T (intVec D S.rank) (intVec D T.rank) fun _ => True

def IsRatDatum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ Φ : WO S T → ℂ, IsSBHalf e (stdHom S T) Φ ∧ (∀ γ, Φ (γ.map fun a => e * incA D a) = Ξ γ) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ Φ f

section Dat
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

structure ColDat (Ch : ℕ → Type) where

  ch : ∀ i, Ch i

  chr : ℕ → ((AE (I.rec7 l Z))ˣ →* Circle)

  om : ∀ i, Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))

  vac : ∀ i, WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ

  w : ∀ i, WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ

  μ : ∀ i, Measure (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))
  fd : ∀ i, Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))

  e : AE (I.rec7 l Z)

  kb : ∀ i, TC.GA B (B.R.N i)
  b0 : ∀ i, Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i
  p0 : ∀ i, PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i

variable {I l Z u} {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}

namespace ColDat
variable (A : ColDat I l Z u Ch) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
  (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))

def xi (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (γ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (xiAt I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) (I.idx I.mu0) u i (A.b0 i) (A.b0 (i + 1)) (A.p0 i) (A.p0 (i + 1))
    (Matrix.toLin' (γ.reindex (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))))))

abbrev Q (i : ℕ) (hi : i ≤ B.R.m) : Chart (I.rec7 l Z) u i hi := chart F i hi (A.ch i)

structure Is : Prop where
  std : IsStdChar (I.rec7 l Z) ψ (-1)
  inf : IsInfFam θ
  chr : ∀ j : Fin B.R.m, ChrEq (A.chr ((j : ℕ) + 1)) (I.C.mu0 j)
  om : ∀ i, i < B.R.m → IsWeilDatumO ψ _ _ (A.chr (i + 1)) (A.chr (i + 1)) (A.om i)
  vac : ∀ i, i < B.R.m → IsVacO ψ θ _ _ (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) (A.vac i)
  idem : IsIdemSum A.e (Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup I.mu0) u)
  datum : ∀ i (hi : i + 1 ≤ B.R.m), IsRatDatum ψ _ _ A.e (A.xi i hi) (A.vac i) (A.w i)
  comb : ∀ i, i < B.R.m → IsFinComb ψ _ _ (A.vac i) (A.w i)
  haar : ∀ i, i ≤ B.R.m → (A.μ i).IsHaarMeasure ∧ IsFundamentalDomain (GQ ((I.rec7 l Z).sp.X i)) (A.fd i) (A.μ i)

  base : ∀ i, i ≤ B.R.m → TC.PtOf (A.kb i) (A.p0 i).1.1 ∧ (A.p0 i).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)

  chart_ne : ∀ i hi, Nonempty (A.Q F i hi).cl
  rep : ∀ i hi (c : (A.Q F i hi).cl),
    TC.PtOf ((show TC.GA B (B.R.N i) from ((A.Q F i hi).K.y c).1) * A.kb i) ((I.stp u I.mu0 i).rep ((A.Q F i hi).inc c)).1.1 ∧
      (show (I.stp u I.mu0 i).Cl from (A.Q F i hi).inc c).1 = A.b0 i ∧
      cosetIn ((I.stp u I.mu0 i).rep ((A.Q F i hi).inc c)) = cosetIn (A.p0 i)

def IsForm (i : ℕ) (hi : i ≤ B.R.m) (φ : ((I.rec7 l Z).mem u).C.cls i → ((I.rec7 l Z).mem u).C.Y i → ℂ) : Prop :=
  φ ∈ ((I.rec7 l Z).fm u).Fi i ∧ OnChart F i hi (A.ch i) φ

def Keeps : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m) φ, A.IsForm F i (Nat.le_of_succ_le hi) φ → A.IsForm F (i + 1) hi (((I.rec7 l Z).mem u).C.K i φ)

abbrev rd (i : ℕ) (hi : i ≤ B.R.m) := (A.Q F i hi).rd θ

end ColDat
end Dat

def RamAt {D : D7} (u : D.what₂.Word) (i : ℕ) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) : Prop :=
  ∀ v c, ∑ a : ((D.mem u).A.Fv v)ˣ, (D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)) = 0

def IsEmbTop {D : D7} (z0 : Fin (D.R.N D.R.m) → D.host.E) (emb : GA D D.sp.X' →* GA D (D.sp.X D.R.m)) : Prop :=
  ∀ h, IsExt D z0 (incA D) ((mt _ h).reindex (finCongr (rankP D)) (finCongr (rankP D)))
    ((mt _ (emb h)).reindex (finCongr (rankN D _ le_rfl)) (finCongr (rankN D _ le_rfl)))

def TopForm {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    {par} (M : Formalism.IndefR.Mult.DSModel D.sp.X' par) (eT : (D.mem u).P.Mt → SmT M → GA D D.sp.X' → ℂ) : Prop :=
  ∃ J : SmT M →ₗ[ℂ] (FrP D → ℂ), Function.Injective J ∧ (∀ v, J v ∈ ValC (gramC (gramP D) (embT D)) (sgT u)) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      ∀ y y' : FrP D, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr (rankP D)) (finCongr (rankP D)))) y' y →
        J (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = J (PiTensorProduct.tprod ℂ v) y') ∧
    ∀ (G : (D.mem u).P.Mt) (c : (D.fm u).clsP) (v : SmT M) (h : GA D D.sp.X'), h ∈ GfC D.sp.X' →
      finM _ (rankP D) h = (F.clsP.y c).1.1 →
      eT G v h = (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) * (D.mem u).P.period (F.valP.eW.symm (Pi.single c (J v))) G

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk



def BigGap (D : D7) : Prop := D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)

def IsScaleWithBoundedGamma (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C' ∧ 1 ≤ large₂.CGam

end GlobalTheory.Core.Rk

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod.PinModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_isOne : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ ∧ Φ.1 0 = 1 := by
  refine ⟨⟨Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1, mem_SB_of_periodic (fun x hx => ?_) fun x y hy => ?_⟩, rfl, ?_⟩
  · exact (Set.mem_of_indicator_ne_zero hx)
  · have : (∀ r q, (x + y) r q ∈ 𝒪[k]) ↔ ∀ r q, x r q ∈ 𝒪[k] :=
      ⟨fun h r q => by simpa using sub_mem (h r q) (hy.intM r q), fun h r q => add_mem (h r q) (hy.intM r q)⟩
    by_cases hx : ∀ r q, x r q ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (by exact this.2 hx), Set.indicator_of_mem (by exact hx)]
    · rw [Set.indicator_of_notMem (by exact fun h => hx (this.1 h)), Set.indicator_of_notMem (by exact hx)]
  · simp

variable {u : D.what₂.Word}

end GlobalTheory.LocMod.PinModel
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def IsOneComb (ψ : AddChar k Circle) (ν : Measure k) (P : ℕ) (L : Level (GL (n ⊕ Fin c) k)) (α : GL (n ⊕ Fin c) k)
    (e : GL (n ⊕ Fin c) k →₀ ℂ) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A), IsSmoothRep σ →
    ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ P σ l → ∀ v : A, (∀ j : L.J, σ (j : GL (n ⊕ Fin c) k) v = (L.lam j : ℂ) • v) →
      toOne ν σ P l (σ α v) = GlobalTheory.PosOne.comb e fun g => l (σ g v)

end Local

def conv {G : Type} [Monoid G] (l : List (G →₀ ℂ)) : G →₀ ℂ :=
  l.foldr (fun e r => e.sum fun g a => r.sum fun h b => Finsupp.single (g * h) (a * b)) (Finsupp.single 1 1)

def aconv {G : Type} [AddMonoid G] (l : List (G →₀ ℂ)) : G →₀ ℂ :=
  l.foldr (fun e r => e.sum fun g a => r.sum fun h b => Finsupp.single (g + h) (a * b)) (Finsupp.single 0 1)

variable {D : D7}

structure Dbl2 (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) where
  B : BesLev D (σ + 1)
  J : JacLev D (σ + 1)
  B' : BesLev D σ
  s₁ : StepBF ψ B J
  s₂ : StepFB ψ J B'
  l : Link B B'.L B'.ζ
  vL : VolM D B'.L.rank J.W₀.rank
  χ₁ : (AE D)ˣ →* Circle
  χ₂ : (AE D)ˣ →* Circle
  χz : (AE D)ˣ →* Circle
  oma : Om B.A J.W₀
  omb : Om J.W₀ B'.A
  V₁ : s₁.χV = χ₁ * χz
  W₁ : s₁.χW = χ₁
  V₂ : s₂.χV = χ₂
  W₂ : s₂.χW = χ₂ * χz
  weila : IsWeilDatumO ψ B.A J.W₀ χ₁ χ₁ oma
  weilb : IsWeilDatumO ψ J.W₀ B'.A χ₂ χ₂ omb

variable {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ}

def Dbl2.con (S : Dbl2 ψ σ) (Φ₁ : WO S.B.V S.J.W → ℂ) (Φ₂ : WO S.J.W S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W)
    (h₂ : GA D S.B'.V) : WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ :=
  GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (flatBF S.s₁ (S.s₁.om (g, h₁) Φ₁)) (flatFB S.s₂ (S.s₂.om (h₁, h₂) Φ₂))

def Dbl2.val (S : Dbl2 ψ σ) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (Φ₁ : WO S.B.V S.J.W → ℂ)
    (Φ₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W)
    (h₂ : GA D S.B'.V) : ℂ :=
  S.B'.per ψ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ _ _ _ c₁ c₂ (S.con Φ₁ Φ₂ g h₁ h₂))) (rTrans h₂ f)


set_option maxHeartbeats 2000000 in
structure QStep (S : Dbl2 ψ σ) where
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
  ψk : AddChar k Circle
  char : (ofSplit q).IsChar ψ ψk
  cond : HasConductor ψk 1
  n₀ : Type
  n₁ : Type
  n₂ : Type
  [f₀ : Fintype n₀]
  [e₀' : DecidableEq n₀]
  [f₁ : Fintype n₁]
  [e₁' : DecidableEq n₁]
  [f₂ : Fintype n₂]
  [e₂' : DecidableEq n₂]
  c : ℕ
  F : Dbl (ofSplit q) S.B S.J S.B' n₀ n₁ n₂ c
  gl₀ : GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k →* GA D S.B.V
  gl₁ : GL (n₁ ⊕ Fin (c + 1 + 1)) k →* GA D S.J.W
  gl₂ : GL (n₂ ⊕ Fin (c + 1)) k →* GA D S.B'.V
  loc₀ : ∀ g, (ofSplit q).IsLoc F.G₀ (gl₀ g) g
  loc₁ : ∀ g, (ofSplit q).IsLoc F.G₁ (gl₁ g) g
  loc₂ : ∀ g, (ofSplit q).IsLoc F.G₂ (gl₂ g) g
  μ₁ : kˣ →* ℂˣ
  μ₂ : kˣ →* ℂˣ
  comp₁ : (ofSplit q).IsComp S.χ₁⁻¹ μ₁
  comp₂ : (ofSplit q).IsComp S.χ₂⁻¹ μ₂
  open₁ : IsOpen (μ₁.ker : Set kˣ)
  open₂ : IsOpen (μ₂.ker : Set kˣ)
  L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k)
  L₁ : Level (GL (n₁ ⊕ Fin (c + 1 + 1)) k)
  L₂ : Level (GL (n₂ ⊕ Fin (c + 1)) k)
  co₁ : IsCO L₁.J
  co₂ : IsCO L₂.J
  le₁ : L₁.J ≤ KO k _
  le₂ : L₂.J ≤ KO k _
  Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1 + 1)) (n₀ ⊕ Fin (c + 1 + 1 + 1)) k)
  Φ₂ : SB (Matrix (n₂ ⊕ Fin (c + 1)) (n₁ ⊕ Fin (c + 1 + 1)) k)
  ty₁ : HasTypes μ₁ L₀ L₁ Φ₁.1
  ty₂ : HasTypes μ₂ L₁ L₂ Φ₂.1
  D₁ : WO S.B.V S.J.W →₀ ℂ
  D₂ : WO S.J.W S.B'.V →₀ ℂ
  dat₁ : (ofSplit q).IsCombAt ψ F.G₀ F.G₁ D₁ Φ₁.1
  dat₂ : (ofSplit q).IsCombAt ψ F.G₁ F.G₂ D₂ Φ₂.1

  α : GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k
  A₁ : Finset (GL (n₁ ⊕ Fin (c + 1 + 1)) k)
  A₂ : Finset (GL (n₂ ⊕ Fin (c + 1)) k)
  cov₁ : Covers 1 L₁.J A₁ fun h => GlobalTheory.StepData.flat ψk ν μ₁ Φ₁.1 α h
  cov₂ : ∀ γ ∈ A₁, Covers 1 L₂.J A₂ fun h => GlobalTheory.StepData.flat ψk ν μ₂ Φ₂.1 γ h
  d₁ : A₁ → WO S.B.A S.J.W₀ →₀ ℂ
  d₂ : A₁ → A₂ → WO S.J.W₀ S.B'.A →₀ ℂ
  ent₁ : ∀ γ, (ofSplit q).IsCombAt ψ F.F₀ F.F₁ (d₁ γ) (xi ψk ν μ₁ Φ₁.1 L₁.J 1 α γ.1)
  ent₂ : ∀ γ β, (ofSplit q).IsCombAt ψ F.F₁ F.F₂ (d₂ γ β) (xi ψk ν μ₂ Φ₂.1 L₂.J 1 γ.1 β.1)
  e₀ : GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k →₀ ℂ
  e₂ : A₂ → GL (n₂ ⊕ Fin (c + 1)) k →₀ ℂ
  one₀ : IsOneComb ψk ν (σ + 1 + 1) L₀ α e₀
  one₂ : ∀ β, IsOneComb ψk ν (σ + 1) L₂ β.1 (e₂ β)
  m₁ : Measure (GL n₁ k)
  m₂ : Measure (GL n₂ k)
  haar₁ : m₁.IsHaarMeasure
  haar₂ : m₂.IsHaarMeasure
  vol₁ : m₁ (KO k n₁) = 1
  vol₂ : m₂ (KO k n₂) = 1

attribute [instance] QStep.fld QStep.val QStep.top QStep.loc QStep.mea QStep.bor QStep.f₀ QStep.e₀' QStep.f₁ QStep.e₁' QStep.f₂ QStep.e₂'

namespace QStep
variable {S : Dbl2 ψ σ} (Q : QStep S)

def w₁ (γ : Q.A₁) : ℂ := (((Q.m₁ (prX (Cgrp Q.L₁.J γ.1))).toReal⁻¹ : ℝ) : ℂ)

def w₂ (β : Q.A₂) : ℂ := (((Q.m₂ (prX (Cgrp Q.L₂.J β.1))).toReal⁻¹ : ℝ) : ℂ)

def volJ : ℂ := ((Q.L₁.J.relIndex (KO Q.k _) : ℂ) * (Q.L₂.J.relIndex (KO Q.k _) : ℂ))⁻¹

def Vac (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) : Prop :=
  (∃ T O, (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T ∧ IsOne O ∧ T O = f₁) ∧
    ∃ T O, (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T ∧ IsOne O ∧ T O = f₂

def Away {A T : HSp D} (c : WO A T →₀ ℂ) : Prop := ∀ u ∈ c.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u

def Typed (f : GA D S.B'.V → ℂ) : Prop :=
  ∀ j : Q.L₂.J, rTrans (Q.gl₂ j.1) f = (Q.L₂.lam j : ℂ) • f

end QStep

def IntAt {V : HSp D} {k Y : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype Y]
    [DecidableEq Y] (v : GlobalTheory.FinPl.Pl D) (gl : GL Y k →* GA D V) (x : GA D V) : Prop :=
  ∃ κ ∈ KO k Y, x * (gl κ)⁻¹ ∈ GlobalTheory.FinPl.grpOff V (· = v)

def ValOne (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (G₁ : Measure (GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k)) (G₂ : Measure (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)),
    G₁.IsHaarMeasure → G₂.IsHaarMeasure → G₁ (KO Q.k (Q.n₁ ⊕ Fin (Q.c + 1 + 1))) = 1 → G₂ (KO Q.k (Q.n₂ ⊕ Fin (Q.c + 1))) = 1 →
  ∀ c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → Q.Typed f →
  ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v), ∀ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v),
    ∃ u : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → ℂ,
      (∀ x, IsQuotInt Q.ν Q.m₂ G₂ (σ + 1) (fun y => GlobalTheory.PosOne.comb Q.e₀ fun a =>
        S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y)) (u x)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.IsQuotIntFJ Q.ν Q.m₁ G₁ (σ + 1) u
        (Q.volJ * ∑ γ : Q.A₁, ∑ β : Q.A₂, Q.w₁ γ * Q.w₂ β *
          S.val (aconv [c₁, Q.d₁ γ]) (aconv [c₂, Q.d₂ γ β]) f₁ f₂ φ (trc ((Q.e₂ β).mapDomain Q.gl₂) f) g h₁ h₂)

def ValQ (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ v, P v ↔ ∃ i, (Q i).q.v = v) →
  ∀ (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W P)) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W P)))
    (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V P)) (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V P))),
    μ₁.IsHaarMeasure → ρ₁.IsHaarMeasure → μ₂.IsHaarMeasure → ρ₂.IsHaarMeasure →
    μ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1} = 1 → ρ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1.1} = 1 →
    μ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1} = 1 → ρ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1.1} = 1 →
  ∀ c₁ c₂, (∀ i, (Q i).Away c₁ ∧ (Q i).Away c₂) → ∀ f₁ f₂, IsThetaFunO ψ _ _ f₁ → IsThetaFunO ψ _ _ f₂ → (∀ i, (Q i).Vac f₁ f₂) →
  ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → (∀ i, (Q i).Typed f) →
  ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V P, ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W P, ∀ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V P,
    Iter2 ρ₁ μ₁ ρ₂ μ₂
      (fun x y => GlobalTheory.PosOne.comb (conv (List.ofFn fun i => (Q i).e₀.mapDomain (Q i).gl₀)) fun a =>
        S.val c₁ c₂ (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₁)) f₁) (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₂)) f₂)
          φ f (g * a) (h₁ * x.1) (h₂ * y.1))
      ((∏ i, (Q i).volJ) * ∑ γ : ∀ i, (Q i).A₁, ∑ β : ∀ i, (Q i).A₂, (∏ i, (Q i).w₁ (γ i) * (Q i).w₂ (β i)) *
        S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ (γ i))) (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ (γ i) (β i))) f₁ f₂ φ
          (trc (conv (List.ofFn fun i => ((Q i).e₂ (β i)).mapDomain (Q i).gl₂)) f) g h₁ h₂)

def FinOne (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (a : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k),
    ∃ T₁ : Finset (GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k),
      (∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v), ∀ x,
        flatBF S.s₁ (S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) (comb ψ _ _ Q.D₁ f₁)) ≠ 0 →
          ∃ t ∈ T₁, ∃ r, Q.gl₁ r ∈ jacGrp S.J.d ∧ ∃ j ∈ Q.L₁.J, x = r * t * j) ∧
      ∀ x, ∃ T₂ : Finset (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k), ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v),
        ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v), ∀ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v), ∀ y,
          S.con (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) (g * Q.gl₀ a) (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) ≠ 0 →
            ∃ t ∈ T₂, ∃ r, Q.gl₂ r ∈ besGrp S.B'.d S.B'.o ∧ ∃ j ∈ Q.L₂.J, y = r * t * j

end GlobalTheory.QPl
end
end
