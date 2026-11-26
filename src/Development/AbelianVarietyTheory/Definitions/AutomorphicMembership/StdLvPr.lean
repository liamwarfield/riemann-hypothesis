module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure CarH {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) : Prop where
  eV : ∀ u, (F u).atT.eV = H.vT u
  fv : ∀ u v (a : 𝓞 D.host.F), H.Fv u v ((F u).atT.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a
  car0 : ∀ u, SameCar (rank_eq_first_level D.R) (H.lev0 u).Lb ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
    (H.lev0 u).Uloc ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
    (H.lev0 u).U ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
    (fun c => ((H.lev0 u).y c).1) (fun c => (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
    (fun c s => ((H.lev0 u).stabI c s).1) (fun c s => (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1)
  carC : ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : H.Ch u i),
    SameCar (rankN D i (le_of_succ_m h2)) (H.lev u i h1 (le_of_succ_m h2) β).Lb ((F u).ch i h1 h2 β).lev.Lb
      (H.lev u i h1 (le_of_succ_m h2) β).Uloc ((F u).ch i h1 h2 β).lev.Uloc
      (H.lev u i h1 (le_of_succ_m h2) β).U ((F u).ch i h1 h2 β).lev.U
      (fun c => ((H.cls u i h1 (le_of_succ_m h2) β).y c).1) (fun c => (((F u).ch i h1 h2 β).y c).1)
      (fun c s => ((H.cls u i h1 (le_of_succ_m h2) β).stabI c s).1) (fun c s => (((F u).ch i h1 h2 β).stabI c s).1)
  carM : ∀ u, SameCar (rankN D D.R.m le_rfl) (H.lev u D.R.m (one_le_m D.R) le_rfl (chM H u)).Lb
      ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.Lb
      (H.lev u D.R.m (one_le_m D.R) le_rfl (chM H u)).Uloc ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.Uloc
      (H.lev u D.R.m (one_le_m D.R) le_rfl (chM H u)).U ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.U
      (fun c => ((H.cls u D.R.m (one_le_m D.R) le_rfl (chM H u)).y ⟨c, chOf_m H u c⟩).1)
      (fun c => (((F u).cls D.R.m le_rfl (Or.inr rfl)).y c).1)
      (fun c s => ((H.cls u D.R.m (one_le_m D.R) le_rfl (chM H u)).stabI ⟨c, chOf_m H u c⟩ s).1)
      (fun c s => (((F u).cls D.R.m le_rfl (Or.inr rfl)).stabI c s).1)
  sp : ∀ u, (F u).gl.sp = (H.lev0 u).splitG
  fr0 : ∀ u i v h, (F u).glev0.fr i v h = reGL (rank_eq_first_level D.R) _ ((H.lev0 u).frG i v h)

structure CarT {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) : Prop where
  piU : ∀ u, (F u).atT.piU = (A u).piU
  res : ∀ u, (F u).atT.res = (A u).res
  carP : ∀ u, SameCar (rankP D) (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) (F u).clsP.lev.Lb
    (A u).levP.Uloc (F u).clsP.lev.Uloc (A u).levP.U (F u).clsP.lev.U
    (fun c => ((A u).clsP.y c).1) (fun c => ((F u).clsP.y c).1)
    (fun c s => ((A u).clsP.stabI c s).1) (fun c s => ((F u).clsP.stabI c s).1)
  lattice₂ : ∀ u c, (F u).clsP.lat c = ((A u).lattice₂ c).map
    ((crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E))
  pr : ∀ u (i : ℕ) (hi : i ≤ D.R.m) v c (z : Formalism.L2.Herm.Ld D u i c) (z' : Ld D u i hi c),
    z'.1 = crdN D i hi z.1 → ((F u).lv i hi).pr v c z' = (A u).pr i v c z
  prk : ∀ u (i : ℕ) (hi : i ≤ D.R.m) v c (z : Formalism.L2.Herm.Lk D u ((A u).Pv v) i c) (z' : Lk (F u).atT i hi v c),
    z'.1 = crdN D i hi z.1 → ((F u).lv i hi).prk v c z' = (A u).prk i v c z
  prC : ∀ u (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) v c (z : Formalism.L2.Herm.Ld D u i c)
    (z' : LdG D i (le_of_succ_m h2) (clsCrd D u i (le_of_succ_m h2) c)),
    z'.1 = crdN D i (le_of_succ_m h2) z.1 → ((F u).lvC i h1 h2).pr v c z' = (A u).pr i v c z
  z0 : ∀ u, (F u).til.z0 = crdN D D.R.m le_rfl (A u).z0
  ga : ∀ u c, ((F u).til.ga c).1 = reGL (rankN D D.R.m le_rfl) _
    (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame ((A u).tilG c).1)

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def StdLvPr (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) : Prop := ∀ i h1 h2,
  (∀ v c z (h : z.1 ∈ ((I.stp u I.mu0 i).rep c).1.1.deco.1.N), (F.lvC i h1 h2).pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩) ∧
    ∀ v c z (h : z.1 ∈ ((I.stp u I.mu0 i).rep c).1.1.deco.1.dnN v), (F.lvC i h1 h2).prk v c z = Submodule.Quotient.mk ⟨z.1, h⟩

def StdLvC (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) : Prop :=
  I.StdLvPr l Z u F ∧ ∀ j v h, F.glevJ.fr j v h = 1

def StdDt (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) : Prop :=
  ∀ (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm) (a : GlobalTheory.Mem.Chr.Ideles B.host.E), IsDetLift B.sp.cm x.1 a →
    dt x = (QuotientGroup.mk a : DtQ B.host I.SQ)

def z0 (X : PreX B.toPre) (u : B.Word) : Fin (B.R.N B.R.m) → B.host.E :=
  fun j => if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0

def TopBase (u : B.Word) (a : I.ι) (U : Subgroup (GA B (B.R.N B.R.m))) (y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)) : Prop :=
  ∀ c (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)),
    ((I.stp u a B.R.m).rep c).1.1 = tilF I.sel (I.tup a) u d → PtOf g' d →
    IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → g⁻¹ * y c ∈ U

section Tw

variable (l0 : I.Law0 l) {inQ : (I.rec7 l Z).what₂.Tup → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}

structure StdW (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) : Prop where
  eCls0 : ∀ u a, T.eCls0 u a = I.eCls0 l u a
  eY : ∀ u a i hi, T.eY u a i hi = Equiv.refl _
  lat : ∀ u a i, T.lat u a i = I.latAt u a i
  eVT : ∀ u a, (W.atT u a).eVT = Equiv.refl _
  eFv : ∀ u a v (r : 𝓞 B.host.E), (W.atT u a).res (F u).atT v r = I.resT l u a v r
  reads : ∀ u a ha i h1 hm, ∃ k, I.Reads u a i (T.chOf u a i) (fun β => (W.ch u a ha i h1 hm β).lev.Lb)
    (fun β => (W.ch u a ha i h1 hm β).lev.U) (fun β => (W.ch u a ha i h1 hm β).lev.chi)
    (fun c => ((W.ch u a ha i h1 hm (T.chOf u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((W.ch u a ha i h1 hm (T.chOf u a i c)).stabI ⟨c, rfl⟩ s).1) k
  top : ∀ u a ha h1 β, I.TopBase l Z u a (W.ch u a ha B.R.m h1 le_rfl β).lev.U
    fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1

  topk : ∀ u a ha h1, ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
    (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
    (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
    (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)

  killed : ∀ u a ha i h1 hm β, FunKilled (W.ch u a ha i h1 hm β).lev (X.piT u)

def StdLv {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} (Lv : SymmetricTwistedLevelData W) : Prop := ∀ u a ha i h1 hm,
  (∀ v c z (h : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.N), (Lv.lv u a ha i h1 hm).pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩) ∧
    ∀ v c z (h : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.dnN v), (Lv.lv u a ha i h1 hm).prk v c z = Submodule.Quotient.mk ⟨z.1, h⟩

end Tw


open Classical in
def jStd (u : B.Word) (a : I.ι) (G : (I.per l u a).Mt) : (I.per l u a).Wrow :=
  Classical.epsilon fun z => z ∈ (I.fm l u a).ptC ∧ ∀ w, (I.per l u a).period w G = (I.fm l u a).ipP z w

def ipMt (u : B.Word) (a : I.ι) (G G' : (I.per l u a).Mt) : ℂ := (I.fm l u a).ipP (I.jStd l u a G') (I.jStd l u a G)

def cf : Formalism.L2.Host.CharFrame (I.rec7 l Z) :=
  ⟨I.C.P, I.C.W, I.C.mu0, I.C.eta, I.C.chiPsi, I.C.del, I.C.del', I.C.isMu0, I.C.isEta, I.C.isChi, I.C.isDel, I.C.isDel'⟩

def QpIs (Qp : I.ι → Finset ℕ) : Prop := ∀ a (p : ℕ), p ∈ Qp a ↔ p.Prime ∧ ∃ P ∈ I.Q a, (p : 𝓞 B.fields.E) ∈ P.asIdeal

structure StdO (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) : Prop where
  mt : ∀ u a, (O u a).mt = fun j => if 1 ≤ j ∧ j ≤ B.R.m then
    (I.rec7 l Z).muTil j * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) else (I.rec7 l Z).muTil j
  lat : ∀ u a i c, ((O u a).lat i c).1 = ((I.stp u a i).rep c).1.1.deco.1.N
  dt : ∀ u a i c, (O u a).dt i c = detPt B.host I.SQ ((I.stp u a i).rep c).1.1
  frm : ∀ u a i y, (O u a).frm i y = y.1
  dgen : ∀ u a, (O u a).dgen = I.J.cD
  S : ∀ u a, (O u a).S = insert (B.T u) ({B.host.g 0, B.host.g 1} ∪ Qp a)
  Th : ∀ u a i c c', (O u a).Th i c c' = I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')

structure StdKer {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where
  X_eq : t.X = B.fields
  seam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
  Pr : HEq t.Pr (B.primes X)
  Ch : HEq t.Ch I.Ch
  sel : HEq t.sel I.sel
  S : t.S = I.S
  word : HEq t.word fun u : B.Word => u
  tup : HEq t.tup I.tup
  cst : HEq t.cst I.cst
  idx : HEq t.idx I.idx
  m2 : t.m2 = B.R.m - 2
  glob : HEq t.glob I.glob
  amb : HEq t.amb (I.J.amb B t.χ)
  δ : t.δ = I.J.δ
  O : I.StdO l Z Y.Qp t.O

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerStd

def SeriesRatS : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → VStd D i →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
        SeriesRatOn T R i hV C (κ i) u (c0L i) ph

def UntwRatS : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → VStd D i →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
        ∀ s ∈ GfC (Vc D i), ∀ f : WO (Vc D i) (Wc D i) → ℂ,
          IsLevDatum R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (R.vacP i) f →
          ∀ w ∈ ratVec R i (c0L i) C.σ₂.fieldRange,
            IsRat T i hV C (κ i) (fun g => ph * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f))

theorem seriesRatS_of (h : SeriesRat) : SeriesRatS := by
  first
    | exact h
    | exact fun D G _ _ Pl0 T0 A T _ R F κ v₀ a b c d e f g i hV hp _ => h D G Pl0 T0 A T R F κ v₀ a b c d e f g i hV hp

end GlobalTheory.SerStd
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev MtCx (a : I.ι) : Type := MtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL

abbrev MtHL (hX : B.fields.Ok) (a : I.ι) : HLat B.LL := MtildeH B.wts I.Ch hX I.sel (I.tup a) I.Ps

def toCx (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V) : MtCx I a := toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL x

def SameForm (l : I.Laws) (u : B.Word) (a : I.ι) (F : MtCx I a) (G : (I.per l u a).Mt) : Prop :=
  ∀ p : (I.stX a).D (), (show (I.perIn u a).Mt B.fields.emb B.embLL from G).1 () p = F.1 (toRow I.sel (I.tup a) p.1.1)

variable (l : I.Laws) (hX : B.fields.Ok)

structure DefTrue (W : RowsRest B (I.cols l)) (e : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] W.Amb a) : Prop where
  muAt : ∀ w, W.muAt w = I.mu0
  muTw : ∀ w, W.muTw w = if B.places.resChar w = B.host.pde then I.muStar' else I.muStar
  eMt0 : ∀ u F, SameForm I l u I.mu0 F ((W.eMt0 u).symm (e (I.cols l).mu0 F))
  eMtTw : ∀ u (a : (I.cols l).Tup) F, SameForm I l u a F ((W.eMtTw u a).symm (e a F))
  norm : ∀ (a : (I.cols l).Tup) x, Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x = ‖e a (toCx I hX a x)‖
  lat : ∀ a y, y ∈ (W.Mtilde a).carrier ↔ ∃ x ∈ (MtHL I hX a).L, e a (toCx I hX a x) = y
  gen : ∀ a, ∀ y ∈ (W.Mtilde a).gen, y ∈ (W.Mtilde a).carrier
  eOp : ∀ a, W.eOp a = LinearMap.id
  ze : ∀ u a, W.ze u a = 1

structure StandIn {C : Cols B} (W : RowsRest B C) : Prop where
  drows : W.Drows = 0
  d0 : W.D0 = 0
  dall : W.Dall = 0
  delp : W.delp = 0
  ft : IsEmpty W.FT
  mult : ∀ a j, j ≠ B.R.m → Subsingleton (W.Mult a j)
  io : ∀ a j, W.io a j = 0
  mj : ∀ j, Subsingleton (W.Mj j)
  mt : ∀ a j, Subsingleton (W.Mt a j)
  eMt : ∀ a j, W.eMt a j = LinearMap.id
  bu : ∀ u φ F, W.Bu u φ F = 0
  ij : ∀ a j w, W.Ij a j w = 0 ∧ W.jw a j w = 0
  eta : ∀ j w, W.etaJ j w = 0
  sha : GlobalTheory.MemN.ShaOK B.toPre W.shaLen
  kap : ∀ V S N G, DV.KapDef (assemble B C W V S N G)

structure RowsDef : Type 1 where
  W : RowsRest B (I.cols l)
  e : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] W.Amb a
  tru : DefTrue I l hX W e
  std : StandIn W

structure AmbTrue (Z : TC.Later B (I.cols l)) (e : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (A : AmbForm (I.rec7 l Z) (RowSide.sharp (I.rec7 l Z))) : Prop where
  mt : ∀ a : (I.cols l).Tup, (⟨A.MtH a, fun x => A.jAmb a x⟩ : Σ H : HLat B.LL, (H.V → Z.W.Amb a)) = ⟨MtHL I hX a, fun x => e a (toCx I hX a x)⟩

end GlobalTheory.Mem.Df

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.L2.Host

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def ndLab (N : NData R H what₂) (lab : ∀ k, what₂.FT → N.PlG k → Polynomial (ZMod (H.g k)))
    (h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) : NData R H what₂ :=
  { N with lab := lab, lab_monic := h }

structure CGK {N : NData R H what₂} (A : NAut N) where
  CG : ℕ → Type
  csd : ∀ {a}, CG a → Prop
  ralg : ∀ {a}, CG a → Prop
  locG : ∀ {a}, CG a → ∀ w, A.LP w
  locG_dim : ∀ {a} (π : CG a) w, A.lpDim (locG π w) = a
  locG_unr_ae : ∀ {a} (π : CG a), ∀ᶠ w in Filter.cofinite, A.unr (locG π w)
  tw : ∀ {a}, CG a → CG 1 → CG a
  locG_tw : ∀ {a} (π : CG a) (χ : CG 1) w, locG (tw π χ) w = A.lpChar (locG π w) (locG χ w)
  infG : ∀ {a}, CG a → (H.E →+* ℂ) → Multiset ℂ
  infG_card : ∀ {a} (π : CG a) τ, Multiset.card (infG π τ) = a
  ralg_def : ∀ {a} (π : CG a), ralg π ↔ ∀ τ, (infG π τ).Nodup ∧
    ∀ z ∈ infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  infG_tw : ∀ {a} (π : CG a) (χ : CG 1) τ (s : ℂ), infG χ τ = {s} → infG (tw π χ) τ = (infG π τ).map (· + s)
  csd_tw : ∀ {a} (π : CG a) (χ : CG 1), csd χ → csd π → csd (tw π χ)
  csd_unr : ∀ {a} (π : CG a) w w', csd π → IsConjPl H w w' → A.unr (locG π w) →
    A.unr (locG π w') ∧ A.frobEig (locG π w') = (A.frobEig (locG π w)).map (·⁻¹)
  etaT : CG 1
  etaTinv : CG 1
  etaT_unr : ∀ w, A.unr (locG etaT w)
  etaT_inert : ∀ w, ¬ IsSplitPl H w → A.frobEig (locG etaT w) = {-1}
  etaTinv_def : ∀ w, A.unr (locG etaTinv w) ∧ A.frobEig (locG etaTinv w) = (A.frobEig (locG etaT w)).map (·⁻¹)
  etaT_split : ∀ w w', IsSplitPl H w → IsConjPl H w w' → ∀ a b : ℂ, A.frobEig (locG etaT w) = {a} →
    A.frobEig (locG etaT w') = {b} → a * b = 1

def CGK.naut {N : NData R H what₂} {A : NAut N} (K : CGK A) (hE : IsEmpty N.Loc) : NAut N :=
  { A with
    CG := K.CG
    csd := K.csd
    ralg := K.ralg
    locG := K.locG
    locG_dim := K.locG_dim
    locG_unr_ae := K.locG_unr_ae
    tw := K.tw
    locG_tw := K.locG_tw
    infG := K.infG
    infG_card := K.infG_card
    ralg_def := K.ralg_def
    infG_tw := K.infG_tw
    csd_tw := K.csd_tw
    csd_unr := K.csd_unr
    etaT := K.etaT
    etaTinv := K.etaTinv
    etaT_unr := K.etaT_unr
    etaT_inert := K.etaT_inert
    etaTinv_def := K.etaTinv_def
    etaT_split := K.etaT_split
    muC := fun i => hE.elim i
    muC_csd := fun i => hE.elim i
    jumpsInf := fun i => hE.elim i
    jumpsInf_def := fun i => hE.elim i
    chi_mu := fun i => hE.elim i }

end

structure RowWD (D : D7) where
  par : D.what₂.FT → ∀ w : PlE D.host, GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w)
  sat : D.what₂.FT → PlE D.host → Multiset ℂ
  dim : ∀ σ w, (par σ w).lpDim = D.R.r
  tame : ∀ σ k v, (par σ (D.naut.plGw k v)).tame


set_option maxHeartbeats 2000000 in
def setAut (D : D7) (hE : IsEmpty D.nd.Loc) (lab : ∀ k, D.what₂.FT → D.nd.PlG k → Polynomial (ZMod (D.host.g k)))
    (h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = D.R.r) (A : NAut (ndLab D.nd lab h)) (C : NBC A)
    (tg_mem : ∀ k v, D.ntypes.tg k v ∈ Ine (F := D.host.E) (D.nd.plOm.1 (A.plGw k v)))
    (tg_gen : ∀ k v, TameGenAt (D.nd.plOm.1 (A.plGw k v)) (D.ntypes.tg k v))
    (hl : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod) : D7 :=
  { D with
    nd := ndLab D.nd lab h, ntw := { D.ntw with }, naut := A, nbc := C, nexp := { D.nexp with }, nth := { D.nth with }
    ntypes := { D.ntypes with
      tg_mem := tg_mem, tg_gen := tg_gen, heckeLoc_gamma_places := fun i => hE.elim i, inertiaCharpoly_type := hl, chiT_tg := fun i => hE.elim i
      Par := PEmpty, labPar := fun _ a => a.elim, labPar_monic := fun _ a => a.elim, locPar := fun a => a.elim
      locPar_dim := fun a => a.elim, labPar_def := fun _ a => a.elim, MtPar := fun _ _ a => a.elim
      AmbPar := fun _ a => a.elim }
    nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq, ntwbr := D.ntwbr, ntwbr_ind := D.ntwbr_ind
    nbr := fun i => hE.elim i, nbr_ind := fun i => hE.elim i, self_good := fun i => hE.elim i
    loc_tie := fun i => hE.elim i, bc_tie := fun i => hE.elim i, rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i, Z_tie := fun i => hE.elim i, Zgood_tie := fun i => hE.elim i
    etaJ_tie := D.etaJ_tie }


set_option maxHeartbeats 2000000 in
def setCG (D : D7) (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) : D7 :=
  { D with
    naut := K.naut hE, nbc := { D.nbc with }, ntypes := { D.ntypes with }, nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq
    nbr := fun i => hE.elim i, nbr_ind := fun i => hE.elim i, self_good := fun i => hE.elim i
    loc_tie := fun i => hE.elim i, bc_tie := fun i => hE.elim i, rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i, Z_tie := fun i => hE.elim i, Zgood_tie := fun i => hE.elim i }

def setBC (D : D7) (C : NBC D.naut) : D7 := { D with nbc := C }

def setTy (D : D7) (hE : IsEmpty D.nd.Loc) (X : NTypes D.naut) (h1 : X.IdempotentMatchesAction)
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) = X.e0.coeff g) : D7 :=
  { D with
    ntypes := X, nStage_trivialCharacter_compat := h1, nStage_trivialCharacter_coeff_eq := h0
    bc_tie := fun i => hE.elim i, rbar_tie := fun i => hE.elim i, mtpar_tie := fun i => hE.elim i }

def BlocksUnique (D : D7) : Prop :=
  ∀ Sig Sig' : List (Part D.naut.CG), (∀ p ∈ Sig ++ Sig', 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π ∧ ∀ τ, (D.naut.infG p.π τ).Nodup ∧
      ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2) →
    rankIso D.nd D.naut Sig = D.R.r → rankIso D.nd D.naut Sig' = D.R.r →
    (∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Sig w = isoLoc D.nd D.naut Sig' w) →
    Multiset.ofList (Sig.map fun p => (p.a, p.d)) = Multiset.ofList (Sig'.map fun p => (p.a, p.d))

def IsRepOf (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep ρ ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((ρ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
      galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)

def GalEx (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ ρ, IsRepOf D l ι π ((1 - (a : ℝ)) / 2) ρ

def RowCusp (D : D7) (Rw : RowSide D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∃ π : D.naut.CG D.R.r,
    D.naut.csd π ∧ D.naut.ralg π ∧ (∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w) ∧
    ∀ᶠ w in Filter.cofinite, ∃ p : Polynomial ↥D.LL0, p.map (embLL0 D) =
      galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2))

end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

def LabConj (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Prop :=
  ∀ k v (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → ∃ (c : D.nd.Om ≃+* D.nd.Om) (γ : G D.host.E D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
    (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ (∀ x, γ (c x) = c (D.ntypes.tg k v x)) ∧
    ∀ a : D.naut.LP w, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.naut.items₂ k w a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ (T.e w a)

end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingOneApplyDivThree
noncomputable section

open Formalism.BasicNotions NumberField Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.Mem.R3.MjModel

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem unitMap_norm (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (x : (unitLat K (Module.finrank ℂ W)).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (unitLat K (Module.finrank ℂ W)).b (unitLat K (Module.finrank ℂ W)).X
      (InfinitePlace.mk σ) x) = ‖unitMap σ W x‖ := by
  have h1 : unitMap σ W x = ∑ i, σ (x i) • stdOrthonormalBasis ℂ W i :=
    Fintype.linearCombination_apply ℂ (stdOrthonormalBasis ℂ W) (cpt σ x)
  have h2 : ‖unitMap σ W x‖ ^ 2 = ∑ i, ‖σ (x i)‖ ^ 2 := by
    rw [← (stdOrthonormalBasis ℂ W).sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, (stdOrthonormalBasis ℂ W).orthonormal.inner_right_fintype]
  rw [← Real.sqrt_sq (norm_nonneg (unitMap σ W x)), h2, Formalism.HermitianLatticesTheory.cnorm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : Formalism.HermitianLatticesTheory.fcoord (unitLat K (Module.finrank ℂ W)).b (unitLat K (Module.finrank ℂ W)).X (InfinitePlace.mk σ) x i =
      (InfinitePlace.mk σ).embedding (x i) := by
    have h4 : ∀ (n : ℕ) (u : Fin n → ℂ), Matrix.mulVec (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ u = u := fun n u => by
      rw [inv_one, Matrix.one_mulVec]
    exact congrFun (h4 _ _) i
  rw [h3, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

section Record

open Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} (Z : ReadL R F X0 Y)

theorem jM_metric_all (hH : Holds R F) (j : ℕ) (x : (mjH Z j).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (mjH Z j).b (mjH Z j).X (InfinitePlace.mk D.what₂.embLL) x) = ‖jM Z j x‖ :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW
    (fun _ A g => ∀ x : A.V, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord A.b A.X (InfinitePlace.mk D.what₂.embLL) x) = ‖g x‖)
    (fun i => MjCoord.jW_norm Z hH i) (fun _ => unitMap_norm _ _) j x

end Record

end GlobalTheory.Mem.R3.MjModel

end
end
