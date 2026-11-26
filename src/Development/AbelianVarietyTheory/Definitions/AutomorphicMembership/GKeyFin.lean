module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.RowEx
open Formalism.L2.Host (HChar)
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.LiteralAutomorphy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev GKey (P : Pre) : Type :=
  HeightOneSpectrum (𝓞 P.host.F) × HeightOneSpectrum (𝓞 P.host.E) × (Fin P.R.m → HChar P.host.E)

def gkeyOf {X : Stages} {T : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) : GKey X.B.toPre :=
  (G.pl.v0, G.pl.w G.pl.v0, fun a => G.ch.chiH (a.1 + 1))

def GKeyFin : Prop := ∀ (P : Pre) (c : ℝ), ∃ 𝒦 : Set (GKey P), 𝒦.Finite ∧
  ∀ (X : Stages) (T : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T) (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc), X.B.toPre = P → sc.cGap = c →
    ∃ κ ∈ 𝒦, HEq (gkeyOf G) κ

def WeilEx : Prop := BigR fun R sc => ∀ G : GridData R.toLevCh sc, ∃ W : G.Weil, W.Over R ∧ Nonempty (GridChoice W Set.univ)

def NFSq : Prop := ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
  GlobalTheory.SqTop.Rec large₂ → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh D T) (μ₀ : T), L.Is μ₀ → ∀ G : GridData L ⟨1, CF, large₂.sc.b⟩,
    InNF fun _ σ => GlobalTheory.BigTop.Fun.SqIn G μ₀ σ

def TrSq : Prop := OnAgree fun {_ _ _ _ _ _ _} G G' _ _ _ _ μ₀ μ₀' _ => ∀ (M : IntermediateField ℚ ℂ) (σ : M →+* ℂ),
  GlobalTheory.BigTop.Fun.SqIn G μ₀ σ → GlobalTheory.BigTop.Fun.SqIn G' μ₀' σ

def Full {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {sc : GlobalTheory.ChiGrid.Consts}
    (G : GridData R.toLevCh sc) : Prop :=
  ∃ W M ρ ξ cv rm S rp n e c, (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).Is ∧
    (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).FieldOK ∧ GlobalTheory.BigTop.Fun.SqIn G A.μ0 D.what₂.embLL

def GridAt (s : Scale) (CF : ℝ) (X : Stages) (f : Fr X.B.toPre) (Ξ : Set (HChar X.B.host.E)) : Prop :=
  ∀ large₂ : SizeData₂ X.toD7, large₂.sc = s → GlobalTheory.SqTop.Rec large₂ → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type)
    (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL]
    (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F → R.C = Fr.at X f → TwistPlacesOffPrimeQZero R.toLevCh →
    (∀ t, ∃ ξ ∈ Ξ, HEq (R.toLevCh.xiH t) ξ) → ∀ G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩,
      ∃ G : GridData R.toLevCh ⟨1, CF, s.b⟩, gkeyOf G = gkeyOf G₀ ∧ Full R G

def ExGrid : Prop := ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ s : Scale, s.eps = ε → x₀ ≤ s.x →
  ∀ (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)), Ξ.Finite → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ (X : Stages) (f' : Fr X.B.toPre) (Ξ' : Set (HChar X.B.host.E)), X.B.toPre = P → HEq f' f → HEq Ξ' Ξ →
      (∀ z ∈ S, z ∈ Set.range X.toD7.what₂.embLL) → GridAt s CF X f' Ξ'

def GridA (CF : ℝ) : AtP := fun K B f T => ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
  (N : NStage B C W) (G : GJStage B C), GridAt K.s CF ⟨B, C, W, V, S, N, G⟩ f (T.set f)

end GlobalTheory.Mem.LiteralAutomorphy

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx _root_.Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

def Mult0 : Prop := Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
  (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f →
    (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.Ok3 1 → z.R.toRealDat.ExAt → GlobalTheory.CuspMult.MultEq z.R.toRealDat

def MultL : Prop := StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo →
    GlobalTheory.CuspMult.MultEq z.R.toRealDat

def RowRatW : Prop := StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt →
    GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) →
    Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)

end GlobalTheory.Mem.LiteralAutomorphy

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyGrid
noncomputable section

namespace GlobalTheory.HeightCounting.Up.ListModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.Links NumberField IsDedekindDomain GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

section Guard

open _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR GlobalTheory.BigTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end Guard

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)






open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw in
theorem lev_at_state {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) :
    x.m.z.R.toRealDat.toLevCh.C = cfOf x ∧ ∃ μ0, x.m.z.R.toRealDat.toLevCh.Is μ0 :=
  by
    constructor
    · exact x.m.z.lev.C
    · exact ⟨_, x.m.z.lev.is⟩


open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 in
theorem nonempty_grid {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (sc : Consts) (h3 : ∀ k, q0 (w.st Z).toD7 ≠ B.host.g k) :
    Nonempty (GridData z.R.toRealDat.toLevCh sc) := by
  refine GlobalTheory.ChiGridModel.nonempty_gridData _ _ z.lev.is sc B.g_cond B.pde_cond.1 B.pde_cond.2 h3 fun t PP hP hq => ?_
  have hprime := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (w.st Z).toD7).1
  have two : ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 B.host.E) ∈ PP.asIdeal → q0 (w.st Z).toD7 = p := fun p hp hm => by
    by_contra hne
    have hc : IsCoprime ((q0 (w.st Z).toD7 : ℕ) : 𝓞 B.host.E) ((p : ℕ) : 𝓞 B.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hprime hp).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hm)))
  have hd : f.del.UnrAt PP := f.isDel.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).1 (two _ B.host.pde_prime h)
  have hd' : f.del'.UnrAt PP := f.isDel'.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).2 (two _ B.host.pde'_prime h)
  have hps : ∀ v, (T.psi v).UnrAt PP := fun v => by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 PP hn
    have hmem := Ideal.absNorm_mem PP.asIdeal
    have e := two _ h1 hmem
    exact h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e.symm))))))
  refine (z.lev.is.Q_ram t PP).2 (Or.inl hP) ?_
  rw [z.lev.xiH t]
  have hm : w.I.xi (GlobalTheory.Mem.R3.ixOf w.I _ t) ∈ T.set f := w.xi_range ▸ ⟨_, rfl⟩
  rcases hm with (h | h | h) | ⟨v, h⟩
  · rw [h]; intro x _; rfl
  · exact h ▸ hd
  · exact (h : _ = _) ▸ hd'
  · rw [← h]
    unfold TwDat.xiTw
    split_ifs
    · exact HChar.UnrAt.mul hd' (hps v)
    · exact HChar.UnrAt.mul hd (hps v)

end GlobalTheory.HeightCounting.Up.ListModel

end
end
