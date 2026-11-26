module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFrLifts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
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

def LevTrace : Prop :=
  ∀ κ ∈ GfC (D.sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) κ = y.1.1 →
    ((y : GL _ _) ∈ (F0 W u).cls0.lev.U ↔
      (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ rJ W) ∧
    ∀ hy : (y : GL _ _) ∈ (F0 W u).cls0.lev.U, (((F0 W u).cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) *
      rChi W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0)) = 1

structure BotTie {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) : Prop where
  lev : ∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, B.lev = f.c.B 0 D.R.rS h₀
  adapted : B.Adapted (W.S.tr u).wt
  norm : ∃ μ lam : D.host.E, μ * lam = -D.host.xi0 ^ (D.R.m / 2) ∧
    (∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) ∧
    ∀ j h, v.τ j h *ᵥ o.ζ₀ = lam • (f.c.bes j 0 h).ζ
  last : ∀ i, (G i).z₀ = fun r => (ofSplit (G i).q).pr (o.ζ₀ r)
  lat : ∀ p, p ∉ v.tP → GlobalTheory.FinPl.latV (D.sp.X 0) (f.g.x 0).L (· = p) = GlobalTheory.FinPl.latV (D.sp.X 0)
    ((F0 W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E
      (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) (· = p)
  trace : LevTrace f B

end GlobalTheory.MiTop

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word}

abbrev FI (D : D7) : Type := FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

def idV (𝔞 : FI D) (v : Pl D) : AddSubgroup (AE D) :=
  AddSubgroup.closure {y | ∃ α ∈ intAf D.host.F, (∀ w, w ≠ v → evalV D.host.F w α = 0) ∧ ∃ a ∈ 𝔞,
    y = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] a}

def dI (D : D7) : FI D := FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AA * D.host.AAbar

def cI (D : D7) (j : ℕ) : FI D :=
  FractionalIdeal.spanSingleton _ (D.host.xi0 ^ (j / 2)) * (D.host.AA * D.host.AAbar⁻¹) ^ ((D.R.m - j) / 2)

def bI (D : D7) (j ρ i : ℕ) : FI D := dI D ^ (ρ - i) * cI D j

def MonoId {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D) : Prop :=
  MonoAt d L L₀ v ∧ ∀ (i : Fin ρ), ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ a ∈ idV (𝔟 i) v

def LineId {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV (vecB o ζ) ∈ latV S M (· = v) ↔ a ∈ idV 𝔠 v

def LineLatAt (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (LL : Lat L) (v : Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV ζ ∈ latV L LL (· = v) ↔ a ∈ idV 𝔠 v

variable {a : XPart D u}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {o : OffX a k ι} {b : YPart a}



theorem idV_mono {𝔞 𝔟 : FI D} (h : 𝔞 ≤ 𝔟) (v : Pl D) : idV 𝔞 v ≤ idV 𝔟 v := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, hv, x, hx, rfl⟩
  exact ⟨α, hα, hv, x, h hx, rfl⟩

theorem idV_zero (v : Pl D) : idV (0 : FI D) v = ⊥ := by

  rw [idV, AddSubgroup.closure_eq_bot_iff]
  rintro y ⟨α, -, -, x, hx, rfl⟩
  obtain rfl : x = 0 := by simpa using hx
  simp

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

section Conv

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

def conv (c c' : WO S T →₀ ℂ) : WO S T →₀ ℂ :=
  ∑ x ∈ c.support, ∑ y ∈ c'.support, Finsupp.single (x + y) (c x * c' y * ψ (symplOH S T x y))

def convList (l : List (WO S T →₀ ℂ)) : WO S T →₀ ℂ := l.foldr (conv ψ S T) (Finsupp.single 0 1)

theorem comb_conv (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (conv ψ S T c c') f = comb ψ S T c (comb ψ S T c' f) := by
  have h0 := fun u => zero_smul ℂ (heisO ψ S T u f)
  have h1 := fun u (a b : ℂ) => add_smul a b (heisO ψ S T u f)
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum, conv, ← Finsupp.sum_finsetSum_index h0 h1]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finsupp.sum_finsetSum_index h0 h1]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.sum_single_index (h0 _), GlobalTheory.WeilVacMove.heisO_heisO, smul_smul]

theorem comb_unit (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_single_index (h := fun u (a : ℂ) => a • heisO ψ S T u f) (zero_smul ℂ _), one_smul]
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem comb_convList {α : Type} (l : List α) (c : α → WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (convList ψ S T (l.map c)) f = l.foldr (fun i f' => comb ψ S T (c i) f') f := by
  induction l with
  | nil => exact comb_unit ψ S T f
  | cons i l ih => exact (comb_conv ψ S T _ _ f).trans (congrArg _ ih)

variable {ψ S T}

theorem mem_support_conv {c c' : WO S T →₀ ℂ} {w : WO S T} (hw : w ∈ (conv ψ S T c c').support) :
    ∃ x ∈ c.support, ∃ y ∈ c'.support, w = x + y := by
  classical
  rw [Finsupp.mem_support_iff, conv, Finsupp.finsetSum_apply] at hw
  obtain ⟨x, hx, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  rw [Finsupp.finsetSum_apply] at h2
  obtain ⟨y, hy, h3⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  have h4 : w ∈ (Finsupp.single (x + y) (c x * c' y * ψ (symplOH S T x y))).support := Finsupp.mem_support_iff.mpr h3
  exact ⟨x, hx, y, hy, Finset.mem_singleton.1 (Finsupp.support_single_subset h4)⟩

theorem support_convList {p : WO S T → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) {l : List (WO S T →₀ ℂ)}
    (hl : ∀ c ∈ l, ∀ x ∈ c.support, p x) : ∀ w ∈ (convList ψ S T l).support, p w := by
  induction l with
  | nil => exact fun w hw => Finset.mem_singleton.1 (Finsupp.support_single_subset hw) ▸ h0
  | cons c l ih =>
    intro w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_support_conv hw
    exact hadd x y (hl c List.mem_cons_self x hx) (ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) y hy)

end Conv

section Gen

open Formalism.L2.DIV (Pl kP LevelP)
open GlobalTheory.SymBridge GlobalTheory.LocMod

variable {D : D7} {u : D.what₂.Word}

def symLevel (Pg : Finset (Pl D.host.E)) (ψ₀ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) : LevelP Pg D.R.r ℂ :=
  LevelP.ofLocal (fun PP => Formalism.L2.Col.HPsymF (kP PP.1) D.R.r D.R.k D.R.rS)
    fun PP => Formalism.L2.Col.chiSymF (ψ₀ PP.1) D.R.r D.R.k D.R.rS

section At

variable {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Pl D.host.E} (G : GX a ζ₀ PP)

def GX.emb : D.host.E →+* G.k := G.q.pr.comp (incA D)

structure GX.Frames (fr : ∀ i, i ≤ D.R.m → Matrix (Fin (D.sp.X i).rank) (Fin (D.R.N i)) D.host.E) : Prop where
  under : G.q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  frX : ∀ i (hi : i ≤ G.s + 1) (hm : i ≤ D.R.m), ∃ e : XIx (Fin D.R.k) (Fin D.R.t) i ≃ Fin (D.R.N i), IsOrd xPos e ∧
    ∀ r c, (G.FX i hi).β r c = G.emb (fr i hm r (e c))
  frM : ∀ hm : G.s + 1 + 1 ≤ D.R.m,
    ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2) ⊕ Unit ≃ Fin (D.R.N (G.s + 1 + 1)),
      IsOrd (Sum.elim zPos fun _ => D.R.N D.R.m - 1) e ∧
        ∀ r c, valuation G.k (G.FM.β r c - G.emb (fr (G.s + 1 + 1) hm r (e c))) < 1

end At

structure StdSp (a : XPart D u) (ζ₀ : Fin a.Lz.rank → D.host.E) (π : D.host.E) : Prop where
  cart : ∀ j, j ≤ D.R.m → (a.x j).s = fun _ => 1
  onb : ∀ j, j ≤ D.R.m → (a.x j).B = fun _ => 1
  lat : ∀ j, j ≤ D.R.m → ∀ z, z ∈ (a.x j).L ↔ z ∈ GlobalTheory.AdForm.intVec D _
  lzRank : a.Lz.rank = 1
  lzGram : a.Lz.gram = 1
  lzSig : a.Lz.SigOK ∧ a.Lz.IsPosDef
  zeta : ζ₀ = fun _ => π
  iA : ∀ n h r c, (a.oT n h).iA r c = if r.val = c.val then 1 else 0
  iB : ∀ n h r c, (a.oT n h).iB r c = if r.val + 1 = (D.sp.X n).rank then 1 else 0
  topFr : a.top.β = 1
  topLat : ∀ z, z ∈ a.top.Λ ↔ z ∈ GlobalTheory.AdForm.intVec D _
  top : a.top.st.Is a.c D.R.m

namespace StdSp

variable {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E} {π : D.host.E} (H : StdSp a ζ₀ π)
include H

end StdSp

section Ker

variable {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

end Ker

end Gen

section World

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.SymBridge Formalism.L2.Forms Formalism.IndefR.Links

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

def psiC (P : HeightOneSpectrum (𝓞 B.fields.E)) : AddChar (𝓞 B.fields.E ⧸ P.asIdeal) ℂ :=
  (B.embLL : B.LL →* ℂ).compAddChar (Formalism.L2.Col.psi0P I.Ch P)

def chiC (i : ℕ) (P : HeightOneSpectrum (𝓞 B.fields.E)) : (𝓞 B.fields.E ⧸ P.asIdeal)ˣ →* ℂˣ :=
  (Units.map (B.embLL : B.LL →* ℂ)).comp (Formalism.L2.Col.chiP I.Ch P i)

theorem chiC_apply (i P x) : ((chiC I i P x : ℂˣ) : ℂ) = B.embLL ((Formalism.L2.Col.chiP I.Ch P i x : B.LLˣ) : B.LL) := rfl

structure IsComOf (c : GlobalTheory.ChainOnto.Com (I.rec7 l Z)) : Prop where
  std : IsStdChar (I.rec7 l Z) c.ψ (-1)
  inf : IsInfFam c.θ
  places : c.Pg = (B.primes X).vGs
  mu : ∀ j : Fin B.R.m, ChrEq (c.μ ((j : ℕ) + 1)) (I.C.mu0 j)
  eta : ChrEq c.η I.C.eta
  chi : ∀ i PP, c.chi (i + 1) PP = chiC I i PP
  lev : c.P = symLevel c.Pg (psiC I)

variable {I l Z}

variable {v : B.Word} {Ch : ℕ → Type} (A : ColDat I l Z v Ch)

def BaseCoset : Prop :=
  ∀ j, j + 1 = B.R.m → ∀ P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs →
    ∃ c : Fin (B.R.N j), c.val = B.R.k ∧
      (Pi.single c ((Formalism.L2.Col.qOf P.1 : B.fields.E))⁻¹ : Fin (B.R.N j) → B.fields.E) ∈ cosetIn (A.p0 j) P

def BaseOne (i : ℕ) (hi : i ≤ B.R.m) : Prop :=
  ∀ P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs → ∀ r c,
    HeightOneSpectrum.valuation (I.rec7 l Z).host.E (show HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E) from P.1)
      (baseFr A i hi P r c - if r.val = c.val then 1 else 0) < 1

def BaseEnds : Prop := BaseOne A 0 (Nat.zero_le _) ∧ BaseOne A B.R.m le_rfl


variable {a : XPart (I.rec7 l Z) v}

structure TiedX {ζ₀ : Fin a.Lz.rank → (I.rec7 l Z).host.E} {PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E} (G : GX a ζ₀ PP)
    (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0)) : Prop where
  eq : P.1 = PP
  type : letI := G.fld; letI := G.val; letI := G.top; letI := G.loc
    AtType (k := G.k) I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) B.embLL P G.emb G.S
  fr : G.Frames fun i hi => baseFr A i hi P

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open GlobalTheory.FinPl in
structure OffsetCompatibility (o : OffX a k ((B.primes X).vT v)) : Prop where
  idem : ∀ i, Formalism.L2.NTheta.IsIdemAt (o.p i).e i.1
  under : ∀ i, (o.p i).v = HeightOneSpectrum.under (𝓞 (I.rec7 l Z).host.F) (show Formalism.L2.DIV.Pl (I.rec7 l Z).host.E from i.1)
  nodup : o.I.Nodup
  all : ∀ i, i ∈ o.I
  unif : ((o.q.1 : 𝒪[k]) : k) = (B.T v : ℕ)
  char : ∀ i, (o.p i).IsChar a.c.ψ (o.χ i)
  frame : ∀ j, j ≤ B.R.m → ∀ i, (o.β j i).b = 1
  lat : ∀ j, j ≤ B.R.m → ∀ i, (o.Q j i).lat = GlobalTheory.LatPair.stdLat k _

  fn : ∀ j (hj : j ≤ B.R.m) i (x : Fin (B.R.N j) → 𝓞 B.fields.E) (z : 𝓞 B.fields.E),
    Ideal.Quotient.mk i.1.asIdeal z =
      (letI := GlobalTheory.Mem.Col2.starE B; (A.p0 j).1.1.deco.1.f i fun r => (x r : B.fields.E)) →
    ∃ s : 𝒪[k], (s : k) = (o.p i).pr (incA (I.rec7 l Z) (z : B.fields.E)) ∧
      (o.Q j i).HasVal (fun r => (o.p i).pr (incA (I.rec7 l Z) (x (finCongr (rankN (I.rec7 l Z) j hj) r) : B.fields.E)))
        (residue 𝒪[k] s)
  supp : ∀ j, j < B.R.m → CombAt o.atT (o.cT j)
  rep : ∀ j, j < B.R.m → ∀ f, Vac a.c.ψ _ _ (a.x j).L (a.x (j + 1)).L o.atT f →
    OverAll a.c.ψ (o.β j) (o.β (j + 1)) (a.x j).L (a.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
      (comb a.c.ψ _ _ (o.cT j) f)
  frameTop : ∀ i, (o.γ i).b = 1
  sum : ∀ n h i, IsSumFrame (a.oT n h) o.ζ₀ (o.γ i) (o.γ₀ n h i)


variable (a) in
structure StdCol {chOf : ∀ i, ((I.rec7 l Z).mem v).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) v Ch chOf) : Prop where
  is : A.Is F a.c.ψ a.c.θ
  keeps : A.Keeps F
  coset : BaseCoset A
  ends : BaseEnds A
  chr : ∀ j, j < B.R.m → A.chr (j + 1) = a.c.μ (j + 1)
  rd : ∀ j (hj : j ≤ B.R.m), a.rd j = A.rd F a.c.θ j hj
  ram : ∀ j (hj : j ≤ B.R.m) φ, φ ∈ a.Ram j ↔ A.IsForm F j hj φ ∧ GlobalTheory.AdForm.RamAt (D := I.rec7 l Z) v j φ
  om : ∀ j, j < B.R.m → (a.k j).om = A.om j
  vac : ∀ j, j < B.R.m → (a.k j).vac = A.vac j
  vol : ∀ j, j ≤ B.R.m → (a.x j).vol.μ = A.μ j ∧ (a.x j).vol.𝓕 = A.fd j
  top : TopForm F a.top.M fun G y => (a.eT G).1 y
  onto : Function.Surjective a.eT

variable (w : World I l Z) (a : XPart (I.rec7 l Z) v) (o : OffX a k ((B.primes X).vT v)) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

structure XStdBy (A : ColDat I l Z v (w.C.herm.base.Ch v)) : Prop where
  com : IsComOf I l Z a.c
  sp : StdSp a o.ζ₀ ((X.piT v : 𝓞 B.host.E) : B.host.E)
  col : StdCol A a (w.C.forms v)
  atT : OffsetCompatibility A o
  atG : ∀ PP, ∃ P, TiedX A (G PP) P
  cG : ∀ j, j < B.R.m → o.cG j = convList a.c.ψ _ _ (a.c.Pg.attach.toList.map fun PP => (G PP).cg j)
  cG_zero : ∀ j, B.R.m ≤ j → o.cG j = 0
  ker : ∀ j, j < B.R.m → (a.k j).c = conv a.c.ψ _ _ (o.cG j) (o.cT j)

def XStd : Prop := ∃ A, XStdBy w a o G A

namespace XStdBy

variable {w a o G} {A : ColDat I l Z v (w.C.herm.base.Ch v)} (H : XStdBy w a o G A)
include H

end XStdBy

end World

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colChar)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LevelTest

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

theorem val_lt_one_iff {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt q.e PP) (x : 𝓞 D.host.E) :
    valuation K (q.pr (incA D (x : D.host.E))) < 1 ↔ x ∈ PP.asIdeal := by
  by_cases hx : x = 0
  · subst hx; simp
  have h0 : (q.pr.comp (incA D)) (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [h.2 x hx, ← q.sec_pr, ← q.int_iff]
  change valuation K ((q.pr.comp (incA D)) x) < 1 ↔ ¬ valuation K ((q.pr.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1
  rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]


section Unif

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E}

theorem val_le_one (x : 𝓞 D.host.E) : valuation K (q.pr (incA D (x : D.host.E))) ≤ 1 := by
  have := GlobalTheory.FinPl.SplitApprox.val_le q 1 one_pos (incA D (x : D.host.E)) (finPart D (incA D (x : D.host.E)))
    (GlobalTheory.FinPl.SplitApprox.tmul_mem (a := 1) (fun v => by rw [map_one]; exact one_mem _) x.2) (by simp)
  simpa using this

theorem val_le_one_of (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {y : D.host.E} (hy : PP.valuation D.host.E y ≤ 1) :
    valuation K (q.pr (incA D y)) ≤ 1 := by
  obtain ⟨n, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hy
  have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
    le_antisymm (val_le_one q _) (not_lt.1 fun h' => d.2 ((val_lt_one_iff q h _).1 h'))
  have := val_le_one q n
  rw [show (n : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd, mul_one] at this
  exact this

theorem val_eq_unif (h : Formalism.L2.NTheta.IsIdemAt q.e PP) (ϖ : Unif K) {x : 𝓞 D.host.E} (h1 : x ∈ PP.asIdeal)
    (h2 : x ∉ PP.asIdeal ^ 2) : valuation K (q.pr (incA D (x : D.host.E))) = valuation K ((ϖ.1 : 𝒪[K]) : K) := by
  obtain ⟨c, hc, -⟩ := GlobalTheory.FinPl.SplitApprox.exists_unif_unit D K q ϖ
  have hq := (GlobalTheory.FinPl.SplitApprox.exists_nat ϖ).1
  have hx0 : (x : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h0 => h2 (h0 ▸ zero_mem _)
  refine le_antisymm ?_ ?_
  · have hm : (⟨_, val_le_one q x⟩ : 𝒪[K]) ∈ maximalIdeal 𝒪[K] :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 ((val_lt_one_iff q h x).2 h1)
    obtain ⟨r, hr⟩ := ϖ.mem_max_iff.1 hm
    have hr' : q.pr (incA D (x : D.host.E)) = ((ϖ.1 : 𝒪[K]) : K) * r := congrArg (fun x : 𝒪[K] => (x : K)) hr
    rw [hr', map_mul]; exact mul_le_of_le_one_right' r.2
  · have hc0 : c ≠ 0 := by
      rintro rfl
      exact ϖ.ne_zero (by simpa using hc.symm)
    have hc1 : PP.valuation D.host.E c < 1 := by
      by_contra hge
      have := val_le_one_of q h (y := c⁻¹) (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ (not_lt.1 hge))
      have h3 : valuation K (q.pr (incA D c)) * valuation K (q.pr (incA D c⁻¹)) = 1 := by
        rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ hc0]; simp
      have h4 : valuation K (q.pr (incA D c)) * valuation K (q.pr (incA D c⁻¹)) < 1 :=
        (mul_le_of_le_one_right' this).trans_lt (hc ▸ hq)
      exact h4.ne h3
    have hx : WithZero.exp (-1 : ℤ) ≤ PP.valuation D.host.E (x : D.host.E) := by
      have h5 : ¬ PP.intValuation x ≤ WithZero.exp (-(2 : ℕ) : ℤ) := fun h' =>
        h2 ((PP.intValuation_le_pow_iff_mem x 2).1 h')
      rw [show (x : D.host.E) = algebraMap _ _ x from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      have hne : PP.intValuation x ≠ 0 := PP.intValuation_ne_zero _ fun h0 => h2 (h0 ▸ zero_mem _)
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at h5 ⊢
      omega
    have hc2 : PP.valuation D.host.E c ≤ WithZero.exp (-1 : ℤ) := by
      have hne : PP.valuation D.host.E c ≠ 0 := (map_ne_zero _).2 hc0
      rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hc1
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      omega
    have h6 := val_le_one_of q h (y := c / x) (by
      rw [map_div₀]; exact div_le_one_of_le₀ (hc2.trans hx) zero_le')
    rw [← hc, show c = (x : D.host.E) * (c / x) by field_simp, map_mul, map_mul, map_mul]
    exact mul_le_of_le_one_right' h6

theorem unif_val (ϖ : Unif K) {π : Kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif π) : valuation K ((ϖ.1 : 𝒪[K]) : K) = valuation K (π : K) := by
  have hq := (GlobalTheory.FinPl.SplitApprox.exists_nat ϖ).1
  refine le_antisymm ((h _).1 hq) ?_
  have h1 := (h _).2 le_rfl
  have hm : (⟨(π : K), h1.le⟩ : 𝒪[K]) ∈ maximalIdeal 𝒪[K] := Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 h1
  obtain ⟨r, hr⟩ := ϖ.mem_max_iff.1 hm
  have hr' : (π : K) = ((ϖ.1 : 𝒪[K]) : K) * r := congrArg (fun x : 𝒪[K] => (x : K)) hr
  rw [hr', map_mul]; exact mul_le_of_le_one_right' r.2

end Unif

theorem exists_prime {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (q : GlobalTheory.FinPl.SplitPt D K) : ∃ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.NTheta.IsIdemAt q.e PP := by
  let φ : 𝓞 D.host.E →+* 𝒪[K] :=
    ((q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[K] fun x => val_le_one q x
  have hφ : ∀ x, x ∈ (maximalIdeal 𝒪[K]).comap φ ↔ valuation K (q.pr (incA D (x : D.host.E))) < 1 := fun x =>
    Valuation.Integer.not_isUnit_iff_valuation_lt_one
  obtain ⟨ϖ⟩ : Nonempty (Unif K) := inferInstance
  obtain ⟨hq, N, hN, hNq⟩ := GlobalTheory.FinPl.SplitApprox.exists_nat ϖ
  refine ⟨⟨(maximalIdeal 𝒪[K]).comap φ, Ideal.comap_isPrime _ _, fun h0 => ?_⟩, q.split, fun x hx => ?_⟩
  · have : (N : 𝓞 D.host.E) ∈ (maximalIdeal 𝒪[K]).comap φ := (hφ _).2 (by simpa using hNq.trans hq)
    rw [h0, Ideal.mem_bot] at this
    exact hN.ne' (by exact_mod_cast this)
  · have h0 : (q.pr.comp (incA D)) (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
    refine (hφ x).trans ?_
    rw [← q.sec_pr, ← q.int_iff]
    change valuation K ((q.pr.comp (incA D)) x) < 1 ↔ ¬ valuation K ((q.pr.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]

theorem notMem_sq {p : ℕ} (h : GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.SplitsCompletely D.host.E p) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : (p : 𝓞 D.host.E) ∈ P.asIdeal) : (p : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 := by
  obtain ⟨hp, h⟩ := h
  rw [GlobalTheory.HostSplit.ncard_placesOver _ hp] at h
  haveI := P.isPrime
  exact (GlobalTheory.LocSplit.split_prime hp h P.asIdeal hP).1

theorem unifT_of (p : GlobalTheory.FinPl.SplitPt D k) (ϖ : Unif k) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.v.asIdeal) :
    valuation k (p.pr (incA D (((D.mem u).A.T : ℕ) : D.host.E))) = valuation k ((ϖ.1 : 𝒪[k]) : k) := by
  obtain ⟨PP, hPP⟩ := exists_prime p
  obtain ⟨ε, hε, he⟩ := p.above
  have hv := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP _ ε hPP hε he
  have h1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rw [← hv] at h
    simpa using (Ideal.mem_comap.1 h)
  rw [← val_eq_unif p hPP ϖ h1 (notMem_sq (GlobalTheory.ColClassCompare.levelPrime_splitsCompletely_in_cmField D u) PP h1)]
  simp

theorem g_notMem_sq (P : HeightOneSpectrum (𝓞 D.host.E)) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 := by
  have key : ∀ i j : Fin 2, D.host.g i ≠ D.host.g j → ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      ((D.host.g i : ℕ) : 𝓞 D.host.E) * (D.host.g j : ℕ) ∉ P.asIdeal ^ 2 := fun i j hij hi h => by
    have hc := (Nat.coprime_primes (D.host.g_prime i) (D.host.g_prime j)).2 hij
    obtain ⟨x, y, hxy⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.E) hc)
    refine notMem_sq (GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.splitsCompletely_g D i) P hi ?_
    have e : ((D.host.g i : ℕ) : 𝓞 D.host.E) = x * (((D.host.g i : ℕ) : 𝓞 D.host.E) * (D.host.g i : ℕ)) +
        y * (((D.host.g i : ℕ) : 𝓞 D.host.E) * (D.host.g j : ℕ)) := by linear_combination (-((D.host.g i : ℕ) : 𝓞 D.host.E)) * hxy
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_mul hi hi)) (Ideal.mul_mem_left _ _ h)
  intro h
  rw [Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero h) with h0 | h1
  · exact key 0 1 D.host.g_ne h0 h
  · exact key 1 0 D.host.g_ne.symm h1 (by rwa [mul_comm])

theorem comp_map {F E : Type} [Field F] [Field E] [Algebra F E] {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    [CommRing R''] [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (z : R ⊗[F] E) :
    Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) z =
      Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]


set_option maxHeartbeats 1000000 in
theorem charUnramAt_of {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) : CharUnramAt D χ v := by
  have kf : ∀ w (z : AE D), GlobalTheory.AdelicU.compFin D.host.F D.host.E w z = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D z) :=
    fun w z => comp_map _ _ z
  have ki : ∀ w (z : AE D), infPart D z = 1 → GlobalTheory.AdelicU.compInf D.host.F D.host.E w z = 1 := fun w z hz =>
    (comp_map _ _ z).trans ((congrArg (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)) hz).trans
      (map_one _))
  have kint : ∀ y ∈ intAE D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v y ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => obtain ⟨α, hα, x, rfl⟩ := hy; exact GlobalTheory.AdelicU.tmul_mem_intLoc (hα v) x
    | zero => rw [RingHom.map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [RingHom.map_add (f := _)]; exact add_mem hy hz
    | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy
  have kin : ∀ z : (AE D)ˣ, finPart D (z : AE D) ∈ intAE D →
      (GlobalTheory.Doubling.unitFin D.host.F D.host.E v z).val ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := fun z hz =>
    Set.mem_of_eq_of_mem (s := GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) (kf v z) (kint _ hz)
  intro x h1 h2 h3 h4
  have hx : x = GlobalTheory.Doubling.ideleAt D.host.F D.host.E v (GlobalTheory.Doubling.unitFin D.host.F D.host.E v x) := by
    refine GlobalTheory.Doubling.idele_ext (fun w => ?_) fun w => ?_
    · rw [GlobalTheory.Doubling.unitInf_ideleAt]
      exact Units.ext (ki w x h1)
    · by_cases hw : w = v
      · subst hw; rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
      · rw [GlobalTheory.Doubling.unitFin_ideleAt_ne hw]
        exact Units.ext ((kf w x).trans (h2 w hw))
  rw [hx]
  refine GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum D χ v _ ?_ ?_ h
  · exact kin x h3
  · rw [← map_inv]
    exact kin x⁻¹ h4

end GlobalTheory.SeeSaw.LevelTest

section
open Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.SeeSaw.BaseLatTest

end GlobalTheory.SeeSaw.BaseLatTest

end

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTrans
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StdT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} (p : ι → SplitPt (I.rec7 l Z) k)
    (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)) : Prop :=
  (∃ e : ι ≃ (B.primes X).vT u, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (e i).1) ∧
    ∀ j, j ≤ B.R.m → (∀ z, z ∈ L j ↔ z ∈ intVec (I.rec7 l Z) _) ∧ ∀ i, (β j i).IsLat (L j) (Q j i).lat ∧
      ∀ z ∈ L j, ∀ r : Fin ((I.rec7 l Z).sp.X j).rank, r.1 + 1 = ((I.rec7 l Z).sp.X j).rank → ∃ s : 𝒪[k],
        (s : k) = (p i).pr (incA (I.rec7 l Z) ((show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E)) * z r)) ∧
        (Q j i).HasVal ((β j i).b' *ᵥ fun r' => (p i).pr (incA (I.rec7 l Z) (z r'))) (residue 𝒪[k] s)

end GlobalTheory.AdForm

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealOf
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

def JetS (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z)) (s : ℕ → ℂ) : Prop :=
  ∀ j (hj : j + 1 ≤ B.R.m), s j ≠ 0 ∧ ∀ f, IsHol θ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ψ f → ∀ P,
    pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
      jetP _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) (s j) (ColDat.xiS θ j hj f) P

def lowOf : (FrN (I.rec7 l Z) (B.R.N B.R.m) → ℂ) →ₗ[ℂ] (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) :=
  fnOf _ (shiftOf (sgT (D := I.rec7 l Z) u)) 1 ∘ₗ (I.perIn u I.mu0).br B.fields.emb B.embLL (B.hcW u) ∘ₗ
    Formalism.L2.Col.polOf _ (shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u B.R.m)) ⟨fun _ => 1, fun _ => by simp⟩

variable {I l Z} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))

@[reducible] def realOf (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) : RealD (commOf R u g) where
  N := B.R.N
  hN := rankN (I.rec7 l Z)
  NT := B.R.N B.R.m - 1
  hT := rankP (I.rec7 l Z)
  fr := fun _ => ⟨fun y => ⟨y.1, y.2⟩, fun y => ⟨y.1, y.2⟩, fun _ => rfl, fun _ => rfl⟩
  lam := Formalism.L2.Forms.lamT (D := I.rec7 l Z) u
  n := fun j τ => (shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j) τ + (I.chain l u I.mu0).sSharp j τ).toNat
  sS := (I.chain l u I.mu0).sSharp
  sD := (I.chain l u I.mu0).sDiv
  sc := fun j τ => if s j = 0 then 1 else s j / I.J.cD τ
  BT := fun _ => 1
  sg := sgT (D := I.rec7 l Z) u
  J := J
  low := fun _ h => Eq.rec (motive := fun n _ => (FrN (I.rec7 l Z) (B.R.N n) → ℂ) →ₗ[ℂ] (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ))
    (lowOf I l Z u) h.symm

def JOf (j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ))
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) : Prop :=
  ∀ v, ∀ k ∈ GinfC (I.rec7 l Z).sp.X', ∀ z z' : FrN (I.rec7 l Z) (B.R.N B.R.m - 1),
    IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' → J v k z' = j v ⟨z.1, z.2⟩

variable (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) {a : I.ι} (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.InfiniteQAtOfIs
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToOneSpherical
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOneSpherical

theorem toOne_spherical : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (_ : IsNEquiv ψ P σ l) (v : A), (∀ g ∈ KO k (n ⊕ Fin c), σ g v = v) → toOne ν σ P l v = l v := by
  intro k _ _ _ _ _ _ n _ _ c P hP hPc ψ hψc hcond ν hν A _ _ σ hσ l hl v hK
  have hne : ψ ≠ 1 := hcond.ne_one
  have hsd : IsSelfDual ψ ν := ((selfDual_measure k ψ hψc hne).2.1 hcond ν).1 hν
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
  have key : ∀ m : ℕ, m + 1 ≤ c → ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (m + 1) σ l →
      (Nat.rec (motive := fun _ => (A → ℂ) → A → ℂ) (fun l => l)
        (fun p rec l => rec (exDown ν (p + 1) σ l)) m : (A → ℂ) → A → ℂ) l v = l v := by
    intro m
    induction m with
    | zero => intro _ l _; rfl
    | succ m ih =>
      intro hm l hl
      have hlt : m + 1 < c := by omega
      obtain ⟨l', hl'v, hl'⟩ := (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) hlt ψ hψc hne ν A σ hσ).2.1 l hl
      have hfun : exDown ν (m + 1) σ l = l' := funext fun w => (hl'v w).symm
      show (Nat.rec (motive := fun _ => (A → ℂ) → A → ℂ) (fun l => l)
        (fun p rec l => rec (exDown ν (p + 1) σ l)) m : (A → ℂ) → A → ℂ) (exDown ν (m + 1) σ l) v = l v
      rw [hfun, ih (by omega) l' hl']
      have h1 := (exDown_exUp_and_exUp_exDown k n c (m + 1) (by omega) hlt ψ hψc hne ν hsd A σ hσ l v).2 hl
      rw [hfun] at h1
      have h2 := (GlobalTheory.RootExchangeFixed.exUp_fixed_vector k n c (m + 1) (by omega) hlt ψ hcond ν hν A σ l' hl' v).2 hK
      rw [← h2, h1]
  exact key m hPc l hl

end GlobalTheory.PosOneSpherical
end

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.PinTest
open GlobalTheory.QPl.Model

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem prX_KO {c : ℕ} : prX (Cgrp (KO k (n ⊕ Fin c)) 1) = KO k n := by
  have key : ∀ g : GL n k, g ∈ prX (Cgrp (KO k (n ⊕ Fin c)) 1) → IntM g.val := by
    rintro g ⟨u, hu, h⟩ i j
    have h2 := (mem_KO.1 (mem_Cgrp.1 h).2).1 (Sum.inl i) (Sum.inl j)
    have h3 : (u * embX c g).val.toBlocks₁₁ = g.val := by
      rw [Units.val_mul, mul_toBlocks₁₁, Radical.toBlocks₁₁_of_mem hu]
      change 1 * (fromBlocks g.val 0 0 1).toBlocks₁₁ + _ * (fromBlocks g.val 0 0 1).toBlocks₂₁ = _
      simp
    rw [inv_one, one_mul, mul_one] at h2
    rw [← h3]; exact h2
  ext g
  refine ⟨fun h => mem_KO.2 ⟨key g h, key _ (inv_mem h)⟩, fun h => ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, ?_⟩⟩⟩
  · rw [one_mul]; exact Subgroup.mem_sup_left ⟨g, rfl⟩
  · rw [inv_one, one_mul, one_mul, mul_one]
    refine mem_KO.2 ⟨intM_fromBlocks.2 ⟨(mem_KO.1 h).1, intM_zero, intM_zero, intM_of_mem_KO (one_mem _)⟩, ?_⟩
    rw [← map_inv]
    exact intM_fromBlocks.2 ⟨(mem_KO.1 h).2, intM_zero, intM_zero, intM_of_mem_KO (one_mem _)⟩

variable {s : ℕ} (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z]



variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν)
include hψ hν

theorem isOneComb_sph {c P : ℕ} (h1 : 1 ≤ P) (h2 : P ≤ c) : IsOneComb ψ ν P (sph k (n ⊕ Fin c)) 1 (Finsupp.single 1 1) :=
  fun A _ _ σ hσ l hl v hv => by
  rw [map_one, Module.End.one_apply, GlobalTheory.PosOneSpherical.toOne_spherical k n c P h1 h2 ψ hψ.continuous hψ ν hν A σ hσ l hl v
    fun g hg => (hv ⟨g, hg⟩).trans (one_smul ℂ v)]
  simp [GlobalTheory.PosOne.comb]

end Local

section Rat
variable {D : D7}

end Rat

variable {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}

section Rel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end Rel


end GlobalTheory.QPl.PinTest
end
end
