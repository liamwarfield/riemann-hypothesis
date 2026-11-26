module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def Placed : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
    (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg),
    f.c.Is ∧ v.Is ∧ VTie f v ∧ ShapeOff v o ∧ GPin G ∧ GRead f G pl ∧ BotTie f B v o G

def tOf (a₀ a : GA D (D.sp.X 0)) : GA D (D.sp.Y 0) :=
  ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0)

end GlobalTheory.MiTop

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

structure TwDat.Live {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) : Prop where
  inj : ∀ j, Function.Injective (ι j)
  first : Function.Surjective (ι 0)
  last : Function.Surjective (ι B.R.m)
  dead : ∀ j (hj : j + 1 ≤ B.R.m) γ, γ ∉ Set.range (ι (j + 1)) → ∀ α z, A.xi j hj α γ z = 0

def TwDat.RamL {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) (j : ℕ) (φ : ColT I l u a j) : Prop :=
  RamT j φ ∧ ∀ c, A.chOf j c ∉ Set.range (ι j) → φ c = 0

structure PinColL {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j)
    (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))
    (x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (c₀ : ℕ → ℂ)
    (kom : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)))
    (dd : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ)
    (w : ∀ j, Ch j → Ch (j + 1) → ℂ) (Ram : ∀ j, Set (ColT I l u a j))
    (rd : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ) (cK : ℕ → ℂ) : Prop where
  is : A.Is
  live : A.Live ι
  om : ∀ j, j < B.R.m → IsWeilDatumO ψ _ _ (A.chr (j + 1)) (A.chr (j + 1)) (kom j)
  dat : ∀ j (hj : j + 1 ≤ B.R.m) α γ, GlobalTheory.SeeSaw.IsFinComb (dd j α γ) ∧
    IsRatDatum ψ _ _ A.e (fun z => w j α γ * A.xi j hj (ι j α) (ι (j + 1) γ) z) (vac j) (comb ψ _ _ (dd j α γ) (vac j))
  cst : ∀ j (hj : j + 1 ≤ B.R.m) α γ, (∃ z, A.xi j hj (ι j α) (ι (j + 1) γ) z ≠ 0) →
    cK j = (volLev (x j).vol (A.U j (ι j α)) : ℂ) * w j α γ * c₀ j *
      (A.chr (j + 1) (A.xr j (ι j α)) : ℂ) * (A.chr (j + 1) (A.xr (j + 1) (ι (j + 1) γ)) : ℂ)⁻¹
  ram : ∀ j, j ≤ B.R.m → ∀ φ, φ ∈ Ram j ↔ A.RamL ι j φ
  rdq : ∀ j (hj : j ≤ B.R.m) β φ y, rd j β φ y = A.rd θ j hj (ι j β) φ y

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

@[reducible] def clsKL (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) {Ch₀ : ℕ → Type}
    (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) : ClsK (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := fun j β => {c // A.chOf j c = ι j β}
  fin := fun j _ => letI := (I.chain l u a).clsFin j; Subtype.fintype _
  U := fun j β => A.U j (ι j β)
  chi := fun j β => A.chi j (ι j β)
  h := fun j β => A.h j (ι j β)
  val := fun _ _ ψ c z => ψ c.1 ⟨z.1, z.2⟩
  abelian₂ := fun j _ _ c c' => A.abelian₂ j c.1 c'.1

def PinChL (c₀ : ℕ → ℂ) {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j)
    (w : ∀ j, k.Ch j → k.Ch (j + 1) → ℂ) : Prop :=
  PinColL A ι R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK

structure PinTopL (UT : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) (ε : ℂ) : Prop where
  emb : IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  lev : ∀ h, h ∈ UT ↔ g.bT⁻¹ * h * g.bT ∈ levS _ R.βX (datXP R P t)
  eT : ∀ n h β, k.eT n h β = Finsupp.single g.bT ε
  cP : k.cP = ε * (volLev g.volT UT : ℂ)

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StdEx' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ), IsStdChar (I.rec7 l Z) ψ (-1) →
    ∀ L : ∀ j, Lat ((I.rec7 l Z).sp.X j), (∀ j, j ≤ B.R.m → ∀ z, z ∈ L j ↔ z ∈ intVec (I.rec7 l Z) _) →
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
      (p : ι → SplitPt (I.rec7 l Z) k) (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle)
      (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
      (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)),
      Places p J (fun x => ∃ i, x = (p i).v) ∧ (∀ i, HasConductor (χ i) 1 ∧ (p i).IsChar ψ (χ i)) ∧ resCard k = B.T u ∧
      (∀ i, valuation k ((p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (X.piT u : B.fields.E)))) =
          valuation k ((q.1 : 𝒪[k]) : k) ∧
        valuation k ((p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E)))) = 1) ∧
      (∀ x : Pl (I.rec7 l Z), (∃ i, x = (p i).v) ↔ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ x.asIdeal) ∧
      (∀ j i, (β j i).b = 1) ∧ StdT I l Z u p β Q L

def TwLev' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) k) (β : ∀ j i, Frame (p i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank)) (L : ∀ j, Lat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ j, j ≤ B.R.m → ∀ b,
      (∀ i g, g • Q j i = Q j i → ∃ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1) ∧
      ∀ κ ∈ A.U j b, ∃ g : ι → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ i, g i • Q j i = Q j i) ∧
        ∃ κ' ∈ grpOff ((I.rec7 l Z).sp.X j) (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β j i).gl (g i)).prod * κ'

def TwRam' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) k) (β : ∀ j i, Frame (p i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank)) (L : ∀ j, Lat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y, IsContAut _ (A.rd θ j hj b φ y)) ∧ (RamT (I := I) (l := l) (u := u) (a := a) j φ ↔ ∀ b y i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y))

def TwTrans' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∃ φ' ∈ (I.fm l u a).Fi j, ∀ b y, A.rd θ j hj b φ' y = trc c (A.rd θ j hj b φ y)

def TwS' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) k) (β : ∀ j i, Frame (p i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank)) (L : ∀ j, Lat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j)),
    StdT I l Z u p β Q L → ∀ (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1),
    ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → ColT I l u a j → ColT I l u a j, ∀ j (hj : j ≤ B.R.m) φ, RamT (I := I) (l := l) (u := u) (a := a) j φ →
      (∀ b y, IsContAut _ (A.rd θ j hj b φ y) ∧ ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y)) ∧
      ∀ η, RamT (I := I) (l := l) (u := u) (a := a) j (S j η φ) ∧ ∀ b y, A.rd θ j hj b (S j η φ) y =
        J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y)

def TwVec' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ ψ θ x vac c₀, PinX I l Z ψ θ x vac c₀ →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)),
    StdT I l Z u p β Q (fun j => (x j).L) → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) α γ (cT : WO _ _ →₀ ℂ),
      Reps ψ (β j) (β (j + 1)) (x j).L (x (j + 1)).L (fun i => phiOne (Q j i) (Q (j + 1) i)) J (fun v => ∃ i, v = (p i).v) cT →
      ∀ e : AE (I.rec7 l Z), IsIdemSum e ((B.primes X).vT u) →
        IsRatDatum ψ _ _ e (fun z => B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z))) (vac j)
          (comb ψ _ _ cT (vac j))

end GlobalTheory.AdForm

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LiftModel

variable {D : D7} {u : D.what₂.Word}

def lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) : Lat L :=
  (𝔠 : Submodule (𝓞 D.host.E) D.host.E).map
    ((LinearMap.toSpanSingleton D.host.E (Fin L.rank → D.host.E) ζ).restrictScalars (𝓞 D.host.E))

theorem tmul_mul_incA (α : AF D.host.F) (x z : D.host.E) :
    (α ⊗ₜ[D.host.F] x : AE D) * incA D z = α ⊗ₜ[D.host.F] (x * z) := by
  change (α ⊗ₜ[D.host.F] x : AE D) * (1 ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem latV_lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (v : Pl D) :
    latV L (lineLat L ζ 𝔠) (· = v) =
      (idV 𝔠 v).map (LinearMap.toSpanSingleton (AE D) (Fin L.rank → AE D) (ratV ζ)).toAddMonoidHom := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul idV
  rw [AddMonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨α, h1, h2, a, rfl, x, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]
  · rintro ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, rfl⟩
    refine ⟨α, h1, h2, 1, rfl, _, ⟨c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]

theorem lineLatAt_lineLat (L : HSp D) {ζ : Fin L.rank → D.host.E} (hζ : ζ ≠ 0) (𝔠 : FI D) (v : Pl D) :
    LineLatAt L ζ 𝔠 (lineLat L ζ 𝔠) v := by
  intro a _
  rw [latV_lineLat]
  refine ⟨?_, fun h => ⟨a, h, rfl⟩⟩
  rintro ⟨a', h, e⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hζ
  have e1 : a' * incA D (ζ i) = a * incA D (ζ i) := congrFun e i
  have hu : IsUnit (incA D (ζ i)) := (IsUnit.mk0 _ hi).map _
  rwa [← hu.mul_right_cancel e1]

theorem idV_le_idAt (𝔞 : FI D) (v : Pl D) : ∀ a ∈ idV 𝔞 v, a ∈ idAt D (· = v) := by
  intro a ha
  refine (AddSubgroup.closure_le (idAt D (· = v)).toAddSubgroup).2 ?_ ha
  rintro _ ⟨α, -, h2, x, -, rfl⟩
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [h2 _ w.2, TensorProduct.zero_tmul]

theorem one_tmul_one_ne (F A E : Type) [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E] :
    (1 : A) ⊗ₜ[F] (1 : E) ≠ 0 := one_ne_zero (α := A ⊗[F] E)

theorem idV_ne_bot {𝔞 : FI D} (h : 𝔞 ≠ 0) (v : Pl D) : idV 𝔞 v ≠ ⊥ := by
  classical
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (FractionalIdeal.eq_zero_iff.2 hc)
  have ev : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
    exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1
  have ew : ∀ w, w ≠ v → evalV D.host.F w (singleV D.host.F v 1) = 0 := fun w hw => by
    exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw
  intro hb
  have hm : (pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] x ∈ idV 𝔞 v := by
    refine AddSubgroup.subset_closure ⟨_, fun w => ?_, ew, x, hx, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [ev]; exact one_mem _
    · rw [ew w hw]; exact zero_mem _
  rw [hb, AddSubgroup.mem_bot] at hm
  have h2 := congrArg (fun y => compAt D v (y * incA D x⁻¹)) hm
  simp only [tmul_mul_incA, mul_inv_cancel₀ hx0, zero_mul, map_zero] at h2
  change (evalV D.host.F v (singleV D.host.F v 1)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0 at h2
  rw [ev] at h2
  exact one_tmul_one_ne _ _ _ h2

theorem AA_ne (hP : FactPrincipalDatum) : D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ D.host.xi0 ≠ 0 := by
  have h1 := hP D.R D.host
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [h] at h1

variable {a : XPart D u} {b : YPart a}

theorem lineId_of_split {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (𝔠 : FI D) (v : Pl D) (h : LineLatAt L ζ 𝔠 LL v) (ho : OrthAt o M LA LL v) : LineId o ζ M 𝔠 v := by
  intro a ha
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, ← h a ha]
  rw [o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.SeeSaw.LiftModel

end
end
