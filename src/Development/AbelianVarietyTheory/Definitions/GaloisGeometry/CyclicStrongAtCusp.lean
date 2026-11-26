module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Formalism.LocalToGlobal.KernelLattices.TopPin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ArthurClozelStrongSupp
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def ArthurClozelStrongSupp : Prop := StrongBC lbc

end GlobalTheory.Published

end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Unlinked (s : Multiset (IrrGL (k := k))) : Prop := ∀ y ∈ s, ∀ z ∈ s, y ≠ z.nu 1

def PlainTor (x : IrrGL (k := k)) : Prop := ∃ s, HasSupport x.rep s ∧ (∀ y ∈ s, y.1 = 1) ∧ Unlinked s

def Plain (x : IrrGL (k := k)) : Prop := PlainTor x ∨ (x.IsCusp ∧ UpperTheory.Zero.LLC.GoodCusp x)

def chars {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) : Multiset (IrrGL (k := k)) :=
  Finset.univ.val.map fun j => IrrGL.ofChar (ξ j) (hξ j)

end Classes

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def satWD {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (a : ℕ) (B : Multiset ℂˣ) : WD h :=
  (WD.lpUnr (h := h) (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpTw ((1 - (a : ℝ)) / 2)

variable [IsCMField E]

def PlainAt (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ → Plain (IrrGL.of σ.ρ σ.smooth σ.irred)

inductive Sph
  | unr | dR | crys | phi

def SphAt (c : Sph) (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E))
    (B : Multiset ℂˣ) : Prop :=
  match c with
  | .unr => ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)
  | .dR => ClauseAt .dR π ι r w
  | .crys => ClauseAt .crys π ι r w
  | .phi => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (satWD h a B).charPol g

def SphericalLevelCondition (s : Level) (c : Sph) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w →
    ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → SphAt c π ι r w B

def Core : Prop := Ex .csd ∧ ∀ c, SphericalLevelCondition .csd c

def CoreAll : Prop := Ex .all ∧ ∀ c, SphericalLevelCondition .all c

def CharLift {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    (π : CuspSub K a) (P : CuspSub M a) : Prop :=
  IsLift π P ∧ ∀ (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal]
    (τ : SmIrr (GL (Fin a) (v.adicCompletion K))) (T : SmIrr (GL (Fin a) (u.adicCompletion M))), π.IsLocComp v τ → P.IsLocComp u T →
    ∀ (ξ : Fin a → ((v.adicCompletion K)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport τ.ρ (chars ξ hξ) →
      HasSupport T.ρ (chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j))

def ToralGal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ →
    ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) σ,
      π.IsLocComp w σ →
    ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)),
      HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) →
    ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
      (wdOf h hl ι r).mono0 ∧ ∀ g : Weil h, (wdOf h hl ι r).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))

structure Inputs : Prop where

  js : GlobalTheory.Published.JacquetShalikaRigidity

  gk : GlobalTheory.Published.GelfandKazhdanDual

  adm : GlobalTheory.Published.IrreducibleAdmissibleGL

  len : GlobalTheory.Published.StandardFunctorsFiniteLength

  exh : GlobalTheory.Published.LanglandsExhaustionGL

  zel : GlobalTheory.Published.ZelevinskyPolynomialRing

  gen : GlobalTheory.Published.GenericUnitaryDualGL

  ac : GlobalTheory.Published.ArthurClozelStrongTC

  acs : GlobalTheory.Published.ArthurClozelStrongSupp

  loc : GlobalTheory.Published.ArthurClozelLocalSC

  hk : GlobalTheory.Published.HeckeLAdicCharacterAbove

  alg : GlobalTheory.Published.AlgebraicCharacterWD

  pst : GlobalTheory.Published.DeRhamPotSemistable

end GlobalTheory.RoadU

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms _root_.Formalism.L2.Col Formalism.L2.DIV NumberField IsDedekindDomain

def stabSet {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)
    (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) (q : UF X.E n → Prop) : Set (Matrix (Fin n) (Fin n) D.host.E × ℂ) :=
  {g | ∃ a : FrmG Λ Θ, a • p = p ∧ q a.1 ∧ g = (matE s a.1.1, s.σ₀ ((Λ.chr a.2.1 * Θ.chr a.2.2 : X.Kˣ) : X.K))}

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

def StabPin (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (G : StabDat (D.chTw u μ)) : Prop :=
  ∃ (pt : ∀ i, i ≤ t.m2 + 1 → (D.chTw u μ).cls i → ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i)
    (ix : ∀ i, i ≤ t.m2 → (D.chTw u μ).cls i → (t.idx μ).β i)
    (yb : (D.chTw u μ).cls (t.m2 + 1) → Set (Sp t.X.E (D.R.N (t.m2 + 1))))
    (pT : (D.chTw u μ).cls (t.m2 + 1 + 1) → ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1 + 1)),
    (∀ i (hi : i ≤ t.m2 + 1) c, (t.rd u μ).N i c = (pt i hi c).deco.1.N) ∧
    (∀ c', yb c' ∈ ybSet t.sel (t.tup μ) (t.cst μ) (pt (t.m2 + 1) le_rfl c').deco.1.N) ∧
    (∀ i (hi : i < t.m2) c c' x, (t.rd u μ).Xi i c c' x = t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (ix i hi.le c)
      (ix (i + 1) hi c') (pt i (by omega) c) (pt (i + 1) (by omega) c') x)) ∧
    (∀ c c' x, (t.rd u μ).Xi t.m2 c c' x = t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (ix t.m2 le_rfl c)
      (pt t.m2 (Nat.le_succ _) c) (pt (t.m2 + 1) le_rfl c') (yb c') x)) ∧
    (t.rd u μ).TopPinAt t.Ch t.sel (t.tup μ) (t.cst μ) t.seam.σ₀ (t.word u) t.m2 (pt (t.m2 + 1) le_rfl) yb pT ∧
    (∀ i, 1 ≤ i → ∀ (hi : i ≤ t.m2) c, G i c = stabSet t.seam ((t.idx μ).levG i (ix i hi c)) ((t.idx μ).levQ i (ix i hi c))
      (pt i (Nat.le_succ_of_le hi) c) fun _ => True) ∧
    (∀ (b : (t.idx μ).β (t.m2 + 1)) c, G (t.m2 + 1) c = stabSet t.seam ((t.idx μ).levG (t.m2 + 1) b) ((t.idx μ).levQ (t.m2 + 1) b)
      (pt (t.m2 + 1) le_rfl c) fun γ => (fun v => γ.1 v) '' yb c = yb c) ∧
    ∀ c, G (t.m2 + 1 + 1) c = stabSet t.seam (twLt t.Ch (t.m2 + 1 + 1)) (twTt (R := D.R) t.sel (t.tup μ) (t.m2 + 1 + 1)) (pT c) fun _ => True

def FormsPin (t : KerEntTied ex) : Prop :=
  ∀ u μ, DV.Used D μ → ∃ G : StabDat (D.chTw u μ), FormsAre (ex.tw.fm u μ) (t.O u μ) G ∧ StabPin t u μ G

structure ColSide (t : KerEntTied ex) : Prop where
  fields : t.X.Ok
  sel : IsSel t.X t.sel
  bad : (∀ i, t.Pr.g i ∈ t.S) ∧ (∀ v, t.Pr.T v ∈ t.S) ∧ (∀ l ∈ D.host.small, l ∈ t.S) ∧ D.host.q ∈ t.S
  chOk : t.Ch.Ok
  chars : ∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta
  sharp : ∀ μ, (t.cst μ).sharp = true
  deep : ∀ μ, D.R.m ≤ (t.cst μ).A ∧ 2 * (t.cst μ).M ≤ twTopDepth D.R
  repOne : ∀ μ j, j ≤ t.m2 + 1 → ∀ (b : (t.idx μ).β j) (P : rowSG t.Pr t.sel (t.tup μ)), P.1 ∈ t.Pr.vGs → (t.idx μ).h j b P = 1

end GlobalTheory.KerJ
end
end
