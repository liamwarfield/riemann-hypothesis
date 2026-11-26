module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JointApproxOfMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E)

abbrev UA (D : D7) (i : ℕ) (hi : i ≤ D.R.m) := UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

def iotaOf (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal :=
  Classical.epsilon fun ι => ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1

structure IsPtAd (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) : Prop where
  lat : t.seam.lat p.deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb
  frame : ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P)
    (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (frsF t.sel (t.tup μ) p P))
  fnl : ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
    IsOver v (seamP t.seam P.1) →
      FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x.1) p.deco.1

def y0At (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : SB t μ) : Sp t.X.E (D.R.N i) :=
  if h : i = t.m2 + 1 then (by subst h; exact A.y0 β P) else 0

def cosetOf (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) : Set (Sp t.X.E (D.R.N i)) :=
  {y | ∀ P : SB t μ, SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm y) (y0At A i hi β P)}

def xiPt (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1))
    (z : HomE t.X.E (D.R.N i) (D.R.N (i + 1))) : t.X.K :=
  if h : i < t.m2 then
    XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) (by have := m_eq t μ; omega) β') p p' z
  else if i = t.m2 then XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) p p' (cosetOf A (i + 1) hi β' p') z
  else XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p (cosetOf A i (Nat.le_of_succ_le hi) β p) p' z


open Classical in
def xiAd : AdDatum St := fun i hi β β' x x' z =>
  if h : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' then
    t.seam.σ₀ (xiPt A i hi β β' h.1.choose h.2.choose (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z)))
  else 0


variable (t u μ) in
open Classical in
def muOf (j : ℕ) (x : (AfE D.host.F D.host.E)ˣ) : ℂ :=
  if h : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x then (((t.O u μ).mt j (dtU h.choose) : ℂˣ) : ℂ) else 0

def PtEx : Prop := ∀ i hi β x, ∃ p, IsPtAd A a i hi β x p

def PtAway (i : ℕ) (hi : i + 1 ≤ D.R.m) : Prop :=
  ∀ β β' x x' x₁ x₁' p p' p₁ p₁', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (i + 1) hi β' x₁' p₁' →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧
      bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1) → xiPt A i hi β β' p₁ p₁' = xiPt A i hi β β' p p'

def LevAt (i : ℕ) (hi : i + 1 ≤ D.R.m) : Prop :=
  ∀ β β' x x' x₁ x₁' (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 → ∀ z,
    muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i _).K β).lev.chi κ : ℂˣ) : ℂ) * xiAd A a i hi β β' x₁ x₁' z =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * xiAd A a i hi β β' x x' z

def RatLaw : Prop :=
  ∀ i hi β β' x x' x₁ x₁', ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)),
    ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), x₁.1 = ratA D.host.F γ * x.1 → x₁'.1 = ratA D.host.F γ' * x'.1 →
    ∀ z, xiAd A a i hi β β' x₁ x₁' z = xiAd A a i hi β β' x x' (inFr
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)

def SizeLaw : Prop :=
  ∀ i hi β β' x x', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev
      (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i _).K β).lev.Lb)
      (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb) (xiAd A a i hi β β' x x') ∧
    ∀ z, xiAd A a i hi β β' x x' z ≠ 0 → z ∈ divLat (t.rd u μ).lev (homAt (ssRec t u μ)
      (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i _).K β).lev.Lb)
      (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb))


variable (t u μ) in
def MuLaw : Prop :=
  ∀ i (hi : i < D.R.m),
    (∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ)) ∧
    (muOf t u μ dtU (i + 1) 1 = 1 ∧ ∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D),
      muOf t u μ dtU (i + 1) (x * y) = muOf t u μ dtU (i + 1) x * muOf t u μ dtU (i + 1) y) ∧
    (∀ x ∈ U1 (sigD D), muOf t u μ dtU (i + 1) x ∈ TaylorLogMetric.Qbar) ∧
    (∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E →
      (∀ v, UnderSB t μ v → prV (E := D.host.E) v (x : AfE D.host.F D.host.E) = 1) → muOf t u μ dtU (i + 1) x = 1) ∧
    ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧
      ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 →
        muOf t u μ dtU (i + 1) (ratId D.host.F D.host.E z) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

end GlobalTheory.TwV

def GlobalTheory.TwV.UnderTie (Q : ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX}
    {t : Formalism.L2.Ker.KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : GlobalTheory.TwU.ChainCharts D u μ}, GlobalTheory.TwU.AdData t u μ St →
    ((letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) → NumberField.RingOfIntegers D.host.E → Prop) : Prop :=
  ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX}
    {t : Formalism.L2.Ker.KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : GlobalTheory.TwU.ChainCharts D u μ} (A : GlobalTheory.TwU.AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : NumberField.RingOfIntegers D.host.E),
    GlobalTheory.TwU.AdPins A dtU → GlobalTheory.TwU.AdTie A dtU a → Q A dtU a

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
noncomputable section

namespace GlobalTheory.Pdv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def ColNorm : Prop :=
  ∀ a, B.R.m ≤ (I.cst a).A ∧ (I.cst a).M ≤ B.R.m ∧
    ∀ j, j ≤ B.R.m - 2 + 1 → ∀ (b : (I.idx a).β j) (P : rowSG (B.primes X) I.sel (I.tup a)), P.1 ∈ (B.primes X).vGs → (I.idx a).h j b P = 1

variable (l : I.Laws) (Z : TC.Later B (I.cols l))

def stabStd (u : B.Word) (a : I.ι) : GlobalTheory.KerJ.StabDat ((I.rec7 l Z).chTw u a) := fun i c =>
  {g | ∃ s : (I.stp u a i).Stab c, g = ((((I.stp u a i).gam c.1 s.1 : GL (Fin (B.R.N i)) B.host.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E),
    B.embLL (((I.stp u a i).chr c.1 s.1 : B.LLˣ) : B.LL))}

def RdStd (u : B.Word) (a : I.ι) (r : KerRead ((I.rec7 l Z).chTw u a) B.fields) : Prop :=
  (∀ i c, r.N i c = ((I.stp u a i).rep c).1.1.deco.1.N) ∧
    ∀ i, i < B.R.m → ∀ c c' x, r.Xi i c c' x = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1
      ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') x)

def StdRd {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u a, ∃ r : KerRead ((I.rec7 l Z).chTw u a) B.fields, HEq (t.rd u a) r ∧ RdStd I l Z u a r

end GlobalTheory.Pdv

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
noncomputable section

namespace GlobalTheory.Pdv

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host NumberField IsDedekindDomain

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def At (ex : Extra D L hT Gi Gl K Y cX) (E : KerEnt D Y ex.tw) : Prop :=
  (E.UnUnit ∧ OrbitPlaces.KmapRat E ∧ OrbitPlaces.KFi D ex.tw ∧ OrbitPlaces.Stab0 D) ∧
    ∃ (ep : _) (be : _) (sg : _),
      OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧ OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧
      OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Gi K ∧ OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧
      OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧ OrbitPlaces.Shape D L Gi (OrbitPlaces.ofKer (nuRowOK D) E ep be sg)

variable {ex : Extra D L hT Gi Gl K Y cX}

def IsEntC (t : KerEntTied ex) : Prop :=
  ∃ (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (h : KerEntHyp P t.O B Y ex.tw), t.ent = kerEntC P t.O B h

structure Duty (t : KerEntTied ex) : Prop where
  col : GlobalTheory.KerJ.ColSide t
  entC : IsEntC t
  rk : t.RK
  forms : ∃ t' : KerEntTied ex, GlobalTheory.KerJ.ColSide t' ∧ GlobalTheory.KerJ.FormsPin t'

end GlobalTheory.Pdv

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasLevelOffOf
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def PhiAt (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hBw : Pst.Induces Bw),
    ∀ (σ : Weil hA) (n : ℕ), GlobalTheory.CongPhi.phiSum (wdAt P ι Bw hA hBw (r.comp (Dec (F := E) A).subtype)) σ n =
      GlobalTheory.CongPhi.phiSum (GlobalTheory.RoadU.satWD hA a B) σ n

def HasLevelOff (w₀ v' : HeightOneSpectrum (𝓞 E)) (Kw : Levels E a) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
    IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → GlobalTheory.PRep.fixed σ.ρ (Kw w) ≠ ⊥


open Classical in
def PowSatU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (n : ℤ) : ℂ :=
  if h : ∃ B, SatU U w B then ((UpperTheory.V.Af.algSat a (normV w) h.choose).map (fun z => z ^ n)).sum else 0

end GlobalTheory.CongL

end
end
