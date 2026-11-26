module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7}

structure XGeo (D : D7) where
  x : ∀ j, DefSp (D.sp.X j)
  vac : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) → ℂ
  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (D.sp.X n) D.sp.X' Lz
  ζ₀ : Fin Lz.rank → D.host.E
  bT : GA D D.sp.X'
  LT : GlobalTheory.FinPl.Lat D.sp.X'


set_option maxHeartbeats 1000000 in
structure YRat (a : XGeo D) where
  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt (Yc D (j + 1)) (D.sp.X (j + 1)) ρ
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (a.x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (D.sp.X (j + 1)).rank
  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (bes j 0 h).L.rank) (Fin a.Lz.rank) D.host.E

structure YMeas {a : XGeo D} (y : YRat a) where
  vol : ∀ j, Vol (Yc D j)
  volT : Vol D.sp.X'
  μf : ∀ j, Measure (GfC (Yc D j))
  μT : Measure (GfC D.sp.X')
  ρJ : ∀ j ρ h, Measure ((jacGrp (y.jac j ρ h).d).subgroupOf (GfC (Yc D (j + 1))))
  ρB : ∀ j ρ h, Measure ((besGrp (y.bes j ρ h).d (y.bes j ρ h).o).subgroupOf (GfC (Yc D j)))
  κ : ℕ → ℝ

@[reducible] def mkGeo {a : XGeo D} {y : YRat a} (m : YMeas y) (b : ∀ j, GA D (Yc D j)) : Geo D :=
  ⟨m.vol, m.volT, a.x, a.vac, y.bes, y.jac, y.lnk, y.vL, a.Lz, a.oT, m.μf, m.μT, m.ρJ, m.ρB, m.κ, b, a.bT, a.LT⟩

def YRat.Tau {a : XGeo D} (y : YRat a) (lam : D.host.E) : Prop :=
  ∀ j h, (y.τ j h)ᴴ * ((y.bes j 0 h).L.gram * y.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • a.Lz.gram ∧
    y.τ j h *ᵥ a.ζ₀ = lam • (y.bes j 0 h).ζ

structure LocX (a : XGeo D) (βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)) (PP : Pl D.host.E) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  q : GlobalTheory.FinPl.SplitPt D k
  idem : Formalism.L2.NTheta.IsIdemAt q.e PP
  under : q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  unit : q.UnitAA
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  FX : ∀ j, j ≤ s + 1 → Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)

  last : FM.β = fromCols ((a.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((a.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ fun i => (ofSplit q).pr (a.ζ₀ i)) r)
  latX : ∀ j hj, IntIn q (D.sp.X j) (FX j hj) (a.x j).L
  latM : IntIn q (D.sp.X (s + 1 + 1)) FM (a.x (s + 1 + 1)).L
  latT : IntIn q D.sp.X' FT a.LT
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' a.bT βT (FT.β.submatrix id e.symm)

attribute [instance] LocX.fld LocX.val LocX.top LocX.loc LocX.mea LocX.bor

structure LocY {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (y : YRat a)
    (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (β : ∀ j, GL (Fin (Yc D j).rank) (Lev.EAf D)) (b : ∀ j, GA D (Yc D j))
    (bas : ∀ j c, j + c = l.s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) l.k) where
  FY : ∀ j c, j + c = l.s + 1 → Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c)
  sc : ℕ → l.k
  sc_unit : ∀ j, valuation l.k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit l.q).xi
  hz_unit : ∀ j ρ h, valuation l.k ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) = 1
  bes : ∀ j ρ h c (hc : j + c = l.s + 1), (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j (by omega)) (FY j c hc)
  jac : ∀ j ρ h c (hc : j + 1 + c = l.s + 1), (ofSplit l.q).IsJacFrame ((y.jac j ρ h).lev (a.x (j + 1)).vol) (sc j)
    ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) (l.FX (j + 1) (by omega)) (FY (j + 1) c hc)
  tau : ∀ h, (y.τ l.s h).map (ofSplit l.q).pr *ᵥ (fun i => (ofSplit l.q).pr (a.ζ₀ i)) =
    (-((ofSplit l.q).xi * sc l.s)) • fun i => (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i)
  latY : ∀ j c hc, IntIn l.q (Yc D j) (FY j c hc) (N j)
  frame : ∀ j c (hc : j + c = l.s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (l.s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit l.q) (Yc D j) (b j) (β j)
      (((FY j c hc).β * (bas j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i))

section Real

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

def QAll (PP : Pl D.host.E) : Prop := ∃ t, PP ∈ (pk W).Q t

structure PkHyp : Prop where
  bot : GlobalTheory.MiTop.BotHyp W
  lev : LevHyp W
  ex : (pk W).ExAt
  hTop : ∀ t, LinearMap.range ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e) =
    MultT (pk W).θ (pk W).MX (levS _ (pk W).βX ((pk W).datXt t)) (levChi _ (pk W).βX ((pk W).datXt t))
  gap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D
  fin : Finite W.P.T

  sel : ∀ PP PP', QAll W PP → QAll W PP' → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP'

  aa : ∀ PP : Pl D.host.E, (QAll W PP ∨ PP ∈ (pk W).Pg ∨ ∃ u, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

variable {W} {u : D.what₂.Word} (f : FamCh W u)

structure VTie (v : VCom f.c) : Prop where
  b : ∀ j, v.b j = f.g.b j
  bT : v.bT = f.g.bT ∧ v.NT = f.g.LT
  gP : ∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  tP : ∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal
  moves : ∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) →
    GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((pk W).ΛY j) (v.N j) P
  movesT : ∀ P, GlobalTheory.FinPl.Moves D.sp.X' f.g.bT (pk W).ΛX f.g.LT P
  Ψ : ∀ j, j + 1 < D.R.m → ∃ o, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧ ∀ P a a', v.Ψ j P a a' = comb f.c.ψ _ _ o
    ((pk W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) (pureTensorO f.c.ψ f.c.θ (Yc D j) (Yc D (j + 1))
      (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P))
  ΨT : ∀ j h, ∃ o, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧ ∀ P, v.ΨT j h P = comb f.c.ψ _ _ o
    (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
      (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P))
  nz : (∀ j, j + 1 < D.R.m → ∃ P, v.Ψ j P 1 1 ≠ 0) ∧ ∀ j h, ∃ P, v.ΨT j h P ≠ 0

structure GRead {v : VCom f.c} {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg) : Prop where
  idem : ∀ i, Formalism.L2.NTheta.IsIdemAt (G i).q.e (pl i).1 ∧ (G i).q.v = (pl i).1.under (𝓞 D.host.F)
  mu : ∀ i j, 1 ≤ j → j ≤ D.R.m → (ofSplit (G i).q).IsComp (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹ ((G i).S.μ j)
  frame : ∀ i j c (hc : j + c = (G i).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((G i).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G i).q) (Yc D j) (f.g.b j) ((pk W).βY j)
      ((((G i).FY j c hc).β * (((G i).S.T (Fin D.R.t)).bas j c hc).val).submatrix id
        fun a => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm a))
  frameTop : ∀ i, ∃ e : Ix (Fin D.R.k ⊕ Fin ((G i).s + 1)) (Fin D.R.t) ((G i).s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G i).q) D.sp.X' f.g.bT (pk W).βX ((G i).FT.β.submatrix id e.symm)

  lev : ∀ (g : ∀ PP : (pk W).Pg, GL (Fin D.R.r) (kP PP.1)),
    (g ∈ (lvP W).H ↔ ∀ i, ∃ x : (G i).S.P.J, ∀ (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1) ∧
    ∀ (hg : g ∈ (lvP W).H) (x : ∀ i, (G i).S.P.J), (∀ i (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x i : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1) →
      (lvP W).chi ⟨g, hg⟩ = ∏ i, (G i).S.P.lam (x i)

end Real

section True

open GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end True

end GlobalTheory.Fam

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

section Coord

variable {K : Type} [Field K] {Y : Type} [Fintype Y] [DecidableEq Y] (V : HSp D) (pr : AE D →+* K)
  (β : Matrix (Fin V.rank) Y K) (γ : Matrix Y (Fin V.rank) K) (βγ : β * γ = 1) (γβ : γ * β = 1)

def coordHom (βγ : β * γ = 1) (γβ : γ * β = 1) : GA D V →* GL Y K :=
  MonoidHom.toHomUnits
    { toFun := fun κ => γ * (mt V κ).map pr * β
      map_one' := by simp [Formalism.L2.Theta.mt, γβ]
      map_mul' := fun κ κ' => by
        have h : (mt V (κ * κ')).map pr = (mt V κ).map pr * (β * γ) * (mt V κ').map pr := by
          rw [βγ, Matrix.mul_one, ← Matrix.map_mul]; simp [Formalism.L2.Theta.mt]
        rw [h]; simp only [Matrix.mul_assoc] }

theorem coordHom_val (κ : GA D V) : (coordHom V pr β γ βγ γβ κ).val = γ * (mt V κ).map pr * β := rfl

theorem eq_coordHom_iff (κ : GA D V) (g : GL Y K) :
    (mt V κ).map pr = β * g.val * γ ↔ g = coordHom V pr β γ βγ γβ κ := by
  constructor
  · intro h
    refine Units.ext ?_
    rw [coordHom_val, h]
    calc g.val = (γ * β) * g.val * (γ * β) := by simp [γβ]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rintro rfl
    rw [coordHom_val]
    calc (mt V κ).map pr = (β * γ) * (mt V κ).map pr * (β * γ) := by simp [βγ]
      _ = _ := by simp only [Matrix.mul_assoc]

end Coord

section AtLevel

variable {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP)

end AtLevel




end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)

abbrev ColT (i : ℕ) : Type := (I.chain l u a).cls i → (I.chain l u a).Y i → ℂ


set_option maxHeartbeats 1000000 in
structure TwDat (Ch : ℕ → Type) where
  bad : ℕ → Set (HeightOneSpectrum (𝓞 B.host.F))
  chOf : ∀ i, (I.stp u a i).Cl → Ch i
  K : ∀ i (hi : i ≤ B.R.m) (β : Ch i), LevelChart (I.rec7 l Z) (B.T u) (bad i) i hi
    (fun c : {c // chOf i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))

  kb : ∀ i, Ch i → TC.GA B (B.R.N i)
  kA : ∀ i, Ch i → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)
  xr : ∀ i, Ch i → (AE (I.rec7 l Z))ˣ
  b0 : ∀ i, Ch i → Idx I.sel (I.tup a) (I.idx a) i
  p0 : ∀ i, Ch i → PtAt B.R I.sel (I.tup a) (I.cst a) u i

  U : ∀ i, Ch i → Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))
  chi : ∀ i β, U i β →* ℂˣ
  h : ∀ i (β : Ch i), {c // chOf i c = β} → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)

  chr : ℕ → ((AE (I.rec7 l Z))ˣ →* Circle)
  e : AE (I.rec7 l Z)

variable {I l Z u a} {Ch : ℕ → Type}

namespace TwDat
variable (A : TwDat I l Z u a Ch)

structure Is : Prop where
  reads : ∀ i (hi : i ≤ B.R.m), I.Reads u a i (A.chOf i) (fun β => (A.K i hi β).lev.Lb) (fun β => (A.K i hi β).lev.U)
    (fun β => (A.K i hi β).lev.chi) (fun c => ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩).1)
    (fun c s => ((A.K i hi (A.chOf i c)).stabI ⟨c, rfl⟩ s).1) (A.kb i)
  top : ∀ β, I.TopPt l Z u a (A.kb B.R.m β)
  kA : ∀ i (hi : i ≤ B.R.m) β, A.kA i β ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (A.kA i β) = (A.kb i β).1 ∧
    IsDetRoot _ (A.kA i β) (A.xr i β)
  base : ∀ i, i ≤ B.R.m → ∀ β, TC.PtOf (A.kb i β) (extTo I.SQ (A.p0 i β).1.1) ∧
    (A.p0 i β).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)
  rep : ∀ i, i ≤ B.R.m → ∀ c, c.1 = A.b0 i (A.chOf i c) ∧ cosetIn ((I.stp u a i).rep c) = cosetIn (A.p0 i (A.chOf i c))
  U : ∀ i (hi : i ≤ B.R.m) β g, g ∈ A.U i β ↔ g ∈ GfC _ ∧ ∃ κ : (A.K i hi β).lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g
  chi : ∀ i (hi : i ≤ B.R.m) β (g : A.U i β) (κ : (A.K i hi β).lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 →
    A.chi i β g = (A.K i hi β).lev.chi κ
  h : ∀ i (hi : i ≤ B.R.m) β c, A.h i β c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (A.h i β c) = ((A.K i hi β).y c).1.1
  chr : ∀ j : Fin B.R.m, ChrEq (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a)
  idem : IsIdemSum A.e (Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u)

  fin : ∀ i (hi : i ≤ B.R.m) β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (A.K i hi β).lev.chi κ ^ n = 1

  bad_le : ∀ i, i ≤ B.R.m → ∀ v ∈ A.bad i, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v

def xi (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch i) (γ : Ch (i + 1))
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ)
    (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z))

def abelian₂ (_A : TwDat I l Z u a Ch) (i : ℕ) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    FP (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) →ₗ[ℂ] ℂ :=
  ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') •
    jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))

def rd (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (ψ : ColT I l u a i) (y : (I.chain l u a).Y i) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i) → ℂ :=
  rdS θ _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (fun c z => ψ c.1 ⟨z.1, z.2⟩) ⟨y.1, y.2⟩

end TwDat

def RamT (i : ℕ) (φ : ColT I l u a i) : Prop :=
  φ ∈ (I.fm l u a).Fi i ∧ ∀ v c, ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT i v s c (φ ((I.fm l u a).dil i v s c)) = 0

def VacT (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i + 1 ≤ B.R.m) (c₀ : ℂ)
    (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)))
    (vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) : Prop :=
  ∀ g ∈ GfC _, ∀ h ∈ GfC _, ∀ N N', Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g N →
    Moves _ (rankN (I.rec7 l Z) (i + 1) hi) h N' → ∀ x y, IsDetRoot _ g x → IsDetRoot _ h y →
      ColDat.xiS θ i hi (om (g, h) vac) = fun z => c₀ * (μ x : ℂ)⁻¹ * (μ y : ℂ) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' z

structure PinX (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))
    (x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (c₀ : ℕ → ℂ) : Prop where
  std : IsStdChar (I.rec7 l Z) ψ (-1)
  inf : IsInfFam θ
  xs : ∀ j, j ≤ B.R.m → (x j).s = (fun _ => 1) ∧ (x j).B = (fun _ => 1) ∧ ∀ z, z ∈ (x j).L ↔ z ∈ intVec (I.rec7 l Z) _
  vc : ∀ j, j < B.R.m → IsVacO ψ θ _ _ (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) (vac j)
  mv : ∀ j (hj : j + 1 ≤ B.R.m), c₀ j ≠ 0 ∧ ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨j, hj⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om →
    VacT I l Z θ j hj (c₀ j) μ om (vac j)

namespace TwDat.Is
variable {A : TwDat I l Z u a Ch}

theorem chOf_onto (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) : Function.Surjective (A.chOf i) := (hA.reads i hi).onto

theorem chart_ext (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (α β : Ch i) (hb : A.b0 i α = A.b0 i β)
    (hc : cosetIn (A.p0 i α) = cosetIn (A.p0 i β)) : α = β := by
  obtain ⟨c, rfl⟩ := hA.chOf_onto i hi α
  obtain ⟨c', rfl⟩ := hA.chOf_onto i hi β
  obtain ⟨h1, h2⟩ := hA.rep i hi c
  obtain ⟨h3, h4⟩ := hA.rep i hi c'
  exact ((hA.reads i hi).key c c').2 ⟨by rw [h1, h3, hb], by rw [h2, h4, hc]⟩

theorem chi_pow (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) : ∃ n : ℕ, 0 < n ∧ ∀ g, A.chi i β g ^ n = 1 := by
  obtain ⟨n, hn, h⟩ := hA.fin i hi β
  refine ⟨n, hn, fun g => ?_⟩
  obtain ⟨κ, hκ⟩ := ((hA.U i hi β g.1).1 g.2).2
  rw [hA.chi i hi β g κ hκ]
  exact h κ

theorem norm_chi (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (g : A.U i β) : ‖((A.chi i β g : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, h⟩ := hA.chi_pow i hi β
  have e : ((A.chi i β g : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h g, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one e hn.ne'

theorem lev_chi_eq_one (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (κ : (A.K i hi β).lev.U)
    (h : ∀ v, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v →
      Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) : (A.K i hi β).lev.chi κ = 1 :=
  (A.K i hi β).lev.chi_triv κ fun v hv => h v (hA.bad_le i hi v hv)

end TwDat.Is

section Pin
variable {A : TwDat I l Z u a Ch} {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {θ : InfFam (I.rec7 l Z)}
    {x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)} {vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ} {c₀ : ℕ → ℂ}
    {kom : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))}
    {dd : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ}
    {w : ∀ j, Ch j → Ch (j + 1) → ℂ} {Ram : ∀ j, Set (ColT I l u a j)}
    {rd : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ} {cK : ℕ → ℂ}

end Pin

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDoubleDescentRanksOneThreeFive
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.Model

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def sph (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n]
    [DecidableEq n] : Level (GL n k) := ⟨KO k n, 1⟩




theorem exists_haar (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] :
    ∃ m : Measure (GL n k), m.IsHaarMeasure ∧ m (KO k n) = 1 := by
  obtain ⟨h0, _, _, h1, h2, -⟩ := volGL_haar k n ν
  haveI : BorelSpace (GL n k) := h0
  haveI := (GlobalTheory.RootExchangeFixed.nonarchimedeanLocalField_secondCountable_t2Space (k := k)).2
  let K : TopologicalSpace.PositiveCompacts (GL n k) := ⟨⟨KO k n, h1⟩, by rw [h2.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩


end Local

variable {D : D7}

theorem exists_gl {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) :
    ∃ gl : GL Y k →* GA D V, ∀ g, (ofSplit q).IsLoc F (gl g) g :=
  let ⟨gl, h1, h2⟩ := GlobalTheory.GlEmbed.exists_gl D k q V Y F.β F.γ F.βγ F.γβ
  ⟨gl, fun g => ⟨h1 g, h2 g⟩⟩



end GlobalTheory.QPl.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotUnitRatioBase
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Core.Rk.Top GlobalTheory.Core.Rk.Top.Model
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Check

variable {D : D7}

section Read

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)

variable {S : D.what₂.Tau → SPar} {MX : DSModel D.sp.X' S} (eW : Pm.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ))
  (j : SmT MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X')

theorem ReadsG.period_eq {G G' : Pm.Mt} {f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)} (h : ReadsG K eW j x G f) (h' : ReadsG K eW j x G' f)
    (w : Pm.Wrow) (hw : ∀ c, eW w c ∈ LinearMap.range j) : Pm.period w G = Pm.period w G' := by
  choose v hv using hw
  have e : w = ∑ c, eW.symm (Pi.single c (j (v c))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, LinearEquiv.eq_symm_apply]
    simp only [hv]
    exact (Finset.univ_sum_single _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := hasMat_exists (K.y c)
  have hc : (Nat.card (M.stabilizer₂ c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := M.stabilizer₂ c)).ne'
  exact mul_left_cancel₀ hc ((h c _ g hg).symm.trans (h' c _ g hg))

end Read

section Package

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {P : LevelP R.Pg D.R.r ℂ} {u : D.what₂.Word} {g : Geo D}

theorem colCh_nonempty (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : ∃ k : ColCh u C, ∀ j, Nonempty (k.Ch j) :=
  by
    let k : ColCh u C :=
      { kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => Finsupp.single 1 1, eT := fun _ _ _ => Finsupp.single 1 1,
        Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 }
    exact ⟨k, fun _ => ⟨()⟩⟩

end Package

section Real

open GlobalTheory.MiS

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

end Real

end GlobalTheory.Fam.Check

end
end
