module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OpIsDVR

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CompHt
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

abbrev WtR (E : Type) [Field E] : Type := ((E →+* ℂ) × ℕ → ℕ) × ℕ

abbrev valG (h : GenFrEx Xo c) (u : WtR E) (f : Rul Xo c) : ∀ Z : Comp Xo c, AC Z := valC h u.1 u.2 f

def dataOf (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ) :
    Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z) where
  D := Dd
  N := N
  T := T
  i := i
  g0 := g0
  cc := cc
  wL := wtZ uL.1 uL.2
  wF := wtZ uF.1 uF.2
  wde := wtZ ude.1 ude.2
  ord Z v := ordC (δ Z v) v
  nrm Z := nrmC fn (yP Z)
  M := letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
    Submodule.span (𝓞 c.F) (valG h uka '' MR)
  WW := letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
    Submodule.span (𝓞 c.F) (Set.range fun k => valG h uL (wR k))
  Thp := letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
    Submodule.span (𝓞 c.F) (Set.range fun k => valG h uF (thpR k))
  Th0 := letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
    Submodule.span (𝓞 c.F) (Set.range fun k => valG h uF0 (th0R k))
  Thk := letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
    Submodule.span (𝓞 c.F) (Set.range fun k => valG h uka (thkR k))
  w k := valG h uL (wR k)
  jc := jc
  np := np
  thp k := valG h uF (thpR k)
  n0 := n0
  th0 k := valG h uF0 (th0R k)
  nk := nk
  thk k := valG h uka (thkR k)
  et := valG h uet etR
  ta1 := valG h uta1 ta1R
  ta2 := valG h uta2 ta2R
  nu := nu
  ip := ip
  wsize := wsize
  DF := DF
  PN := PN
  PQ := PQ
  tableDegreeThreeBase := tableDegreeThreeBase
  PP0' := PP0'
  Pd := Pd
  Gc := Gc
  PI4 := PI4
  Pet := Pet
  tableLineDegreeFive := tableLineDegreeFive
  tableLineDegreeTwo := tableLineDegreeTwo
  Prw := Prw
  PO := PO
  f := f
  r := r

section Laws

variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))


variable (Xo c) in
def CompNe : Prop := Nonempty (Comp Xo c)


variable (Xo c) in
def FnFG : Prop := ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (Om Z)).FG


variable (Xo c) in
def FnTrdeg (Dd : ℕ) : Prop := ∀ Z : Comp Xo c, Algebra.trdeg c.F (Om Z) = Dd


variable (Xo c) in
def FnAlgClosed : Prop :=
  ∀ (Z : Comp Xo c) (a : Om Z), IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om Z)).range

def NZAt (h : GenFrEx Xo c) (f : Rul Xo c) : Prop := ∀ Z, evC h Z f ≠ 0

def LawBdd : Prop :=
  ∀ (sg : c.F →+* ℂ) (G : WTZ E) (f : ∀ Z, AC Z),
    ((f ∈ d.WW ∧ G = d.wL) ∨ (f ∈ d.Thp ∧ G = d.wF) ∨ (f = d.et ∧ G = d.n1 • d.wde) ∨
      (f = d.ta1 ∧ G = (2 : ℕ) • d.G1) ∨ (f = d.ta2 ∧ G = d.G2)) →
    BddAbove (Set.range fun p : (Σ Z, PT (Ω := Om Z) sg) => d.nrm p.1 G (f p.1) p.2)

def A1Bigness : Prop := ∀ Z, ∃ J : Fin d.D → Fin d.N,
    LinearIndependent (Om Z) fun k => KaehlerDifferential.D c.F (Om Z) (d.x Z (J k))

def A2RegularityOrders : Prop :=
  (∀ Z v, d.admitted Z v → ∀ f ∈ d.WW, f Z ≠ 0 → 0 ≤ d.ord Z v d.wL (f Z)) ∧
  (∀ Z v, d.admitted Z v → ∀ f ∈ d.Thp, f Z ≠ 0 → 0 ≤ d.ord Z v d.wF (f Z)) ∧
  (∀ Z v, d.admitted Z v → 0 ≤ d.ord Z v (d.n1 • d.wde) (d.et Z)) ∧
  (∀ Z v, d.admitted Z v → 0 ≤ d.ord Z v ((2 : ℕ) • d.G1) (d.ta1 Z)) ∧
  (∀ Z v, d.admitted Z v → 0 ≤ d.ord Z v d.G2 (d.ta2 Z))

def LawA3' : Prop := ∀ Z {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 → {v | d.admitted Z v ∧ d.ord Z v G f ≠ 0}.Finite

def A4Selection (sel : Fin d.del → Fin d.np) : Prop :=
  ∃ e : ∀ Z, AC Z, (∀ Z, e Z ∈ AG Z d.wF ∧ e Z ≠ 0) ∧
    (∀ p : Fin d.del → MvPolynomial (TVar d.D d.N) c.F,
      (∀ Z, ∑ k, d.sH Z (p k) *
        algebraMap (Om Z) (OmS (Om Z) d.D d.N) (ratio (Ω := Om Z) (d.thp (sel k) Z) (e Z)) = 0) →
      ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Om Z) d.D d.N, ∃ q : MvPolynomial (TVar d.D d.N) c.F, (∀ Z, d.sH Z q ≠ 0) ∧
      ∃ p : Fin d.del → MvPolynomial (TVar d.D d.N) c.F, ∀ Z, d.sH Z q * y Z = ∑ k, d.sH Z (p k) *
        algebraMap (Om Z) (OmS (Om Z) d.D d.N) (ratio (Ω := Om Z) (d.thp (sel k) Z) (e Z)))

def A13Measurable : Prop :=
  ∀ Z (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
      ∑ᶠ P ∈ d.ST Z sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
        Real.log (d.nrm Z G f P)) d.sphMeasure

def NumOK : Prop :=
  3 ≤ d.D ∧ 1 ≤ d.i ∧ 1 ≤ d.g0 ∧ 0 ≤ d.cc ∧ d.cc ≤ 1 ∧ d.cc * d.g0 ≤ 1 / 2 ∧ 1 ≤ d.wsize d.wL ∧
  d.DF ≤ d.wsize d.wL ∧ Real.log (d.N + 1 : ℕ) + 1 / 2 ≤ d.Prw * (d.wsize d.wL - 1) ∧
  Real.log (Module.finrank ℚ c.F) ≤ d.PO ∧
  Real.log (|(NumberField.discr c.F : ℝ)| ^ (1 / (Module.finrank ℚ c.F : ℝ))) ≤ d.PO ∧
  (1 ≤ d.PN ∧ 1 ≤ d.PQ ∧ 1 ≤ d.tableDegreeThreeBase ∧ 1 ≤ d.PP0' ∧ 1 ≤ d.Pd ∧ 1 ≤ d.Gc ∧ 1 ≤ d.PI4 ∧
    1 ≤ d.Pet ∧ 1 ≤ d.tableLineDegreeFive ∧ 1 ≤ d.tableLineDegreeTwo ∧ 1 ≤ d.Prw ∧ 1 ≤ d.PO)

end Laws

theorem valC_ne_zero {h : GenFrEx Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} {Z : Comp Xo c}
    (hf : evC h Z f ≠ 0) : valC h a n f Z ≠ 0 := by
  intro hz
  apply hf
  have := congrArg (fun x : AC Z => x.coeff (wtZ a n)) hz
  simpa [valC, AddMonoidAlgebra.coeff_single] using this

section AxHOf

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

def axHOf (hne : CompNe Xo c) (hfg : FnFG Xo c) (htr : FnTrdeg Xo c Dd) (hac : FnAlgClosed (Xo := Xo) (c := c))
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (het : NZAt h etR) (hta1 : NZAt h ta1R) (hta2 : NZAt h ta2R)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hfn : FnNe Xo c fn) (hconj : FnConj Xo c fn yP)
    (hbdd : LawBdd (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha1 : A1Bigness (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha2 : A2RegularityOrders (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha3' : LawA3' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (sel : Fin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).del → Fin np)
    (ha4 : A4Selection (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) sel)
    (hnum : NumOK (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha13 : A13Measurable (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r)) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).AxH (fun Z => AG Z) := by
  obtain ⟨hD, hi, hg, hc0, hc1, hcg, hL, hDF, hrw, hnK, hrd, hP⟩ := hnum
  exact
  { nonempty := hne
    tower := fun _ => inferInstance
    towerO := fun _ => inferInstance
    D_ge := hD
    fg := hfg
    trdeg := htr
    algClosed := hac
    graded := fun Z => gradedAG Z
    finrank_one := finrank_AG
    mul_ne_zero := fun _ _ _ _ _ hf hg hf0 hg0 => mul_ne_zero_AG hf hg hf0 hg0
    WW_span := rfl
    w_mem := fun k Z => valC_mem h uL.1 uL.2 (wR k) Z
    w_base := fun Z => valC_ne_zero (hwb Z)
    Thp_span := rfl
    thp_mem := fun k Z => valC_mem h uF.1 uF.2 (thpR k) Z
    et_mem := fun Z => by
      have := valC_mem h uet.1 uet.2 etR Z
      rw [huet] at this
      exact this
    firstSectionMem := fun Z => by
      have := valC_mem h uta1.1 uta1.2 ta1R Z
      rw [huta1] at this
      exact this
    secondSectionMem := fun Z => by
      have := valC_mem h uta2.1 uta2.2 ta2R Z
      rw [huta2] at this
      exact this
    et_ne := fun Z => valC_ne_zero (het Z)
    firstSectionNeZero := fun Z => valC_ne_zero (hta1 Z)
    secondSectionNeZero := fun Z => valC_ne_zero (hta2 Z)
    ord_mul := fun Z v _ _ _ _ _ hf hg hf0 hg0 => ordC_mul (δ Z v) v hf hg hf0 hg0
    ord_smul := fun Z v _ _ _ a hf hf0 ha => ordC_smul (δ Z v) v a hf hf0 ha
    nrm_pos := fun Z _ _ P hf hf0 => nrmC_pos fn (yP Z) hfn P hf hf0
    nrm_zero := fun Z G P => nrmC_zero fn (yP Z) G P
    nrm_mul := fun Z _ _ _ _ P hf hg _ _ => nrmC_mul fn (yP Z) hfn P hf hg
    nrm_smul := fun Z _ _ P a hf _ _ => nrmC_smul fn (yP Z) P a hf
    nrm_conj := fun Z G x P => hconj Z G x P
    bdd := hbdd
    a1 := ha1
    ord_nonneg_WW := ha2.1
    ord_nonneg_Thp := ha2.2.1
    ord_nonneg_et := ha2.2.2.1
    ordDoubleFirstSection_nonneg := ha2.2.2.2.1
    ordSecondSectionNonneg := ha2.2.2.2.2
    a3' := ha3'
    sel := sel
    a4 := ha4
    i_ge := hi
    g_zero_ge_ask_sum := hg
    cc_nonneg := hc0
    cc_le := hc1
    ccg0 := hcg
    size_L := hL
    DF_le := hDF
    rw_le := hrw
    nK_le := hnK
    rd_le := hrd
    P_ge := hP
    a13 := ha13 }

end AxHOf

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivCls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop :=
  fun T ι _ => ∀ a : c.F, a ≠ 0 → ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = ι a

structure QPt where
  T : CDVR
  ι : c.F →+* T.Fr
  y : IntFr Xo c T ι
  triv : trivCls Xo c T ι y

def ordQ (q : QPt Xo c) (f : Rul Xo c) : EReal := nval q.T.V 1 (evI q.y f)

def RegularityR1Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n,
    (∃ la : HeightOneSpectrum (𝓞 c.F), ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) →
      ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q f

def RegularityR2Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE k : ℕ) (ws : Fin k → Rul Xo c)
    (et : Rul Xo c) (c' : ℝ), 0 ≤ c' → (∀ i, ws i ∈ C aL nL) → et ∈ C aE nE →
    (∃ (la : HeightOneSpectrum (𝓞 c.F)) (nu : ℝ), ∀ v ∈ valSet Xo c (algCls Xo c) la,
      0 ≤ v et ∧ (∃ i, v (ws i) ≠ ⊤) ∧ (v et ≠ ⊤ → (⨅ i, v (ws i)) ≤ (nu : EReal) + (c' : EReal) * v et)) →
    ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q et ∧
      (ordQ Xo c q et ≠ ⊤ → (⨅ i, ordQ Xo c q (ws i)) ≤ (c' : EReal) * ordQ Xo c q et)

end Formalism.L2.PjFree
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

section Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)

theorem supE_add_le (P Q : FDSec X) : supE X la (P + Q) ≤ supE X la P + supE X la Q := by
  unfold supE
  refine iSup_le fun p => ?_
  have key : (X p.1).pnorm (la p.1) ((P + Q) p.1) p.2 ≤
      (X p.1).pnorm (la p.1) (P p.1) p.2 + (X p.1).pnorm (la p.1) (Q p.1) p.2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
      (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact ((ENNReal.ofReal_le_ofReal key).trans ENNReal.ofReal_add_le).trans
    (add_le_add (le_iSup_of_le p le_rfl) (le_iSup_of_le p le_rfl))

theorem supE_smul (a : ℂ) (P : FDSec X) : supE X la (a • P) = ENNReal.ofReal ‖a‖ * supE X la P := by
  unfold supE
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg a)]
  congr 1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

theorem supE_ne_top [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by
  unfold holSub at h
  induction h using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    unfold supE
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ c, |C c|))
      (iSup_le fun p => ENNReal.ofReal_le_ofReal ?_)
    calc _ ≤ C p.1 := hC p.1 p.2.1 p.2.2
      _ ≤ |C p.1| := le_abs_self _
      _ ≤ ∑ c, |C c| :=
        Finset.single_le_sum (f := fun c => |C c|) (fun c _ => abs_nonneg _) (Finset.mem_univ _)
  | zero =>
    unfold supE
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 0)) (iSup_le fun p => ?_)
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    simp
  | add P Q _ _ hP hQ =>
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hP, hQ⟩) (supE_add_le X la P Q)
  | smul a P _ hP =>
    rw [supE_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP

end Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)


open Classical in
def goodOf (σ : c.F →+* ℂ) : c.F →+* ℂ := if GoodEmb c σ then σ else (starRingEnd ℂ).comp σ

theorem goodEmb_goodOf (σ : c.F →+* ℂ) : GoodEmb c (goodOf c σ) := by
  unfold goodOf
  split_ifs with hσ
  · exact hσ
  · have hx : ((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ) ^ 2 + ((H.d : ℕ) : c.F) = 0 := by
      apply Subtype.ext
      have e : (((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
      push_cast [e]
      rw [H.sqrt_neg_disc_sq]
      ring
    have hy : (σ ((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ)) ^ 2 = H.rt0 ^ 2 := by
      have h0 := congrArg σ hx
      rw [map_add (f := _), map_pow, map_natCast, map_zero] at h0
      rw [H.sqrt_neg_disc_sq]
      linear_combination h0
    have hre : H.rt0.re = 0 := by
      have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
      have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
      simp [sq] at h1 h2
      have hd : (0 : ℝ) < H.d := Nat.cast_pos.mpr H.d_prime.pos
      have e2 : H.rt0.re * H.rt0.im = 0 := by linear_combination h2 / 2
      have e3 : H.rt0.re ^ 4 = -(H.d * H.rt0.re ^ 2) := by
        linear_combination (H.rt0.re ^ 2) * h1 + (H.rt0.re * H.rt0.im) * e2
      have h4 : H.rt0.re ^ 4 ≤ 0 := by
        rw [e3]
        exact neg_nonpos.mpr (mul_nonneg hd.le (sq_nonneg _))
      have h5 : H.rt0.re ^ 4 = 0 := le_antisymm h4 (by positivity)
      exact (pow_eq_zero_iff (by norm_num)).mp h5
    have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
      apply Complex.ext <;> simp [hre]
    unfold GoodEmb at hσ ⊢
    simp only [RingHom.comp_apply] at hσ ⊢
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h | h
    · exact absurd h hσ
    · rw [h, map_neg, hconj, neg_neg]

def lieFac (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieFac_pos (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : 0 < lieFac Dw x a := by
  unfold lieFac
  exact Real.exp_pos _

def supC (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  lieFac Dw x a * supN (U σ).X (laU (U σ) a n) (rdU (U σ) f)

def SupDef : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ f ∈ cusp Xo c U a n, supN (U σ).X (laU (U σ) a n) (rdU (U σ) f) = 0 → f = 0

variable {Xo c U}

theorem supE_cusp_ne_top {a n} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) :
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ := by
  unfold cusp at hf
  have h1 := (Submodule.mem_inf.mp hf).2
  have h2 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h1 σ) hσ
  exact supE_ne_top _ _ (Submodule.mem_comap.mp h2)

variable (U)

variable {U} {σ : c.F →+* ℂ}

end Formalism.L2.PjFree
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Dw) in
abbrev LaMod (l : Level H) : Type := Dw.La ⧸ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La))

variable (Dw) in
def G0 (l₁ l : Level H) : Subgroup (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) where
  carrier := {γ | ∀ q : LaMod Dw l, γ q - q ∈
    (l₁.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).map (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ}
  one_mem' := fun q => by simp
  mul_mem' := by
    intro γ δ hγ hδ q
    have h := Submodule.add_mem _ (hγ (δ q)) (hδ q)
    rwa [sub_add_sub_cancel] at h
  inv_mem' := by
    intro γ hγ q
    have h := Submodule.neg_mem _ (hγ (γ⁻¹ q))
    have e : γ (γ⁻¹ q) = q := γ.apply_symm_apply q
    rwa [e, neg_sub] at h

def liftLa (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) : Dw.La →ₗ[𝓞 E] Dw.La :=
  haveI := Dw.proj
  (Module.projective_lifting_property (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ
    (γ.toLinearMap ∘ₗ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ)
    (Submodule.mkQ_surjective _)).choose

theorem liftLa_spec (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (a : Dw.La) :
    (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ (liftLa γ a) = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a) := by
  have := Dw.proj
  exact LinearMap.congr_fun (Module.projective_lifting_property (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ
    (γ.toLinearMap ∘ₗ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ) (Submodule.mkQ_surjective _)).choose_spec a

def levG {l₁ : Level H} (γ : G0 Dw l₁ l) : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La) :=
  (liftLa (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l), LinearMap.id)

variable (Xo : Moduli Dw l) (c : Coeff l)

def hkScal (cq : c.F) (𝔓 : Ideal (𝓞 E)) (i n : ℕ) : c.F :=
  cq * ((Ideal.absNorm 𝔓 : c.F)⁻¹) ^ (i * n / 2)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivialClassCondition (T : CDVR) (io : c.F →+* T.Fr) (_y : IntFr Xo c T io) : Prop := True

theorem valSet_alg_subset (la : HeightOneSpectrum (𝓞 c.F)) :
    valSet Xo c (algCls Xo c) la ⊆ valSet Xo c (trivialClassCondition Xo c) la := by
  rintro _ ⟨y, rfl⟩
  exact ⟨PtV.widen (fun _ _ _ _ => trivial) y, rfl⟩

def trivSet : Set (Rul Xo c → EReal) :=
  {q | ∃ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
    (∀ a : c.F, a ≠ 0 → vV T.V (io a) = 0) ∧ q = fun f => nval T.V 1 (evI y f)}

def NoCommonZero {n : ℕ} (ws : Fin n → Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), ∃ i, evR Xo c (ws i) y ≠ 0

abbrev DomWt (E : Type) [Field E] : Type := {x : ((E →+* ℂ) × ℕ → ℕ) × ℕ // Dom x.1 x.2}

def regular₂ {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ReciprocityTheory.ChartRestriction.G.T0.RegLaw (Λ := HeightOneSpectrum (𝓞 c.F)) (Wt := DomWt E)
    (fun w => cusp Xo c U w.1.1 w.1.2)
    (fun la => valSet Xo c (algCls Xo c) la) (fun la => valSet Xo c (trivialClassCondition Xo c) la)
    (fun la v => ⟨v.1, valSet_alg_subset Xo c la v.2⟩) (fun _ v _ F => v.1 F.1)
    (trivSet Xo c) (fun q _ F => q.1 F.1) (fun ws => NoCommonZero Xo c fun i => (ws i).1) ∧
  ∀ a n, Dom a n → ∀ (m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ cusp Xo c U a n) → NoCommonZero Xo c ws →
    ∀ nu : HeightOneSpectrum (𝓞 c.F) → ℝ,
      (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)) →
        ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)

variable {Xo c}

end Formalism.L2.PjFree
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

section ChartG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)

abbrev jOG (m n : ℕ) : Over X0 := overAt x0 (Jet S (Fin n × Fin d) m)

abbrev tEpsG : Over X0 := Over.mk (spMap (algebraMap S (DualNumber S)) ≫ x0)

def IsTanAtG (v : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  v ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 ∧
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = (1 : Over.mk x0 ⟶ t.G).left

def IsCombAtG {m : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S)
    (w : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  ∃ u : Fin m → (tEpsG x0 ⟶ t.G), (∀ i, (u i).left = spMap (epsMul (cf i)) ≫ v i) ∧
    ((List.ofFn u).prod).left = w

def jptG (x : ∀ m, jOG x0 d m 1 ⟶ t.G) {n : ℕ} (m : ℕ) (i : Fin n) : jOG x0 d m n ⟶ t.G :=
  homAt x0 (jetCopy d m i) ≫ x m

structure IsChartG {κ : Type} [Fintype κ] (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) : Prop where
  zero : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m
  law : ∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m =
    jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ t.act.act a =
    homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act a p.2)) ≫ x m
  tan : ∀ ℓ : κ, IsCombAtG t x0
    (fun j : Fin d => (homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left) (uvec ℓ)
    (tg ℓ)

  basis : ∀ v : Fin d → S, ∃! a : κ → S, ∀ j, ∑ ℓ, a ℓ * uvec ℓ j = v j

end ChartG

section FrameG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

def cφG {T : Over X0} {n : ℕ} (xs : Fin n → (T ⟶ t.G)) :
    ULift (Finset (Fin n)) → (T.left ⟶ t.G.left) :=
  fun I => (psum t.G xs I.down).left

def scaleGenG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    LB.Gen (LB.LinComb t.PP.L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

def genPowG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (k : ℕ) :
    LB.Gen (LB.LinComb t.PP.L φ fun i => (k : ℤ) * ε i) :=
  ⟨fun j => g.s j ^ k⟩

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
variable (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

abbrev FrTyG (m : ℕ) : Type :=
  LB.Gen (cubeLB t.G ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] t.PP.L)

def peG (e : ∀ m, FrTyG t x0 d x m) (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :=
  LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left

structure IsFrameG (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) : Prop where
  gen : ∀ m, (e m).IsGen
  ph1 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  ph2 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  sy : ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (e m)
      (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))
  ad : ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
      LB.Gen.Corr t.PP.L _ _ _ _
        (LB.mulGen t.PP.L _ _ _ _
          (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
          (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)]))
        (scaleGenG t _ _ (unitΓ u)
          (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

end FrameG

section GermG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
variable (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def jBaseG (m n : ℕ) : jOG x0 d m n ⟶ Over.mk x0 :=
  Over.homMk (spMap (algebraMap S (Jet S (Fin n × Fin d) m))) rfl

abbrev PrimTyG : Type :=
  LB.Gen (LB.LinComb t.PP.L
    (Sum.elim (fun _ : Fin 1 => 𝟙 t.G.left) (cφG t ![𝟙 t.G, t.act.act H.w0]))
    (Sum.elim (fun _ => 1) fun I => -cε 2 I))

def IsPrimG (wP : PrimTyG t) : Prop :=
  wP.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _
    (LB.pullGen t.PP.L _ _ wP (eSec t.G)) t.PP.rig

def eLG (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t)
    (m : ℕ) :=
  LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wP (x m).left)
    (peG t x0 d x e m ![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)])

def IsGermG (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m)
    (wP : PrimTyG t) (k : ℕ)
    (F : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow t.G t.PP.L k (jOG x0 d m 1)))
    (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec t.G t.PP.L k (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr t.PP.L _ _ _ _ τ (genPowG t _ _ (eLG t x0 d x act e wP m) k) ∧
    IsValueAt t.G t.PP.L k F' (x m) τ (toΓ _ (psJet m f))

end GermG

section Link

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)

theorem isChart_iff (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) :
    IsChart y d F act uvec x ↔ IsChartG Xo.univ.t y.x d F act (fun ℓ => y.u ℓ.1 ℓ.2) uvec x :=
  ⟨fun h => ⟨h.zero, h.trunc, h.law, h.act, h.tan, h.basis⟩,
    fun h => ⟨h.zero, h.trunc, h.law, h.act, h.tan, h.basis⟩⟩


set_option maxHeartbeats 1000000 in
theorem isFrame_iff (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTy y d x m) :
    IsFrame y d x F act ph1 ph2 sy ad e ↔ IsFrameG Xo.univ.t y.x d x F act ph1 ph2 sy ad e :=
  ⟨fun h => ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩, fun h => ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩⟩

theorem isPrim_iff (wP : PrimTy H Xo) : IsPrim wP ↔ IsPrimG Xo.univ.t wP := Iff.rfl


set_option maxHeartbeats 1000000 in
theorem isGerm_iff (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo)
    (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f : MvPowerSeries (Fin 1 × Fin d) S) :
    IsGerm y d x act e wP k F f ↔ IsGermG Xo.univ.t y.x d x act e wP k F f := Iff.rfl

end Link

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.IsExpChart
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

section Exp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

abbrev dL (Dw : Datum H) : ℕ := Fintype.card (Lt1 Dw)

def ltIdx (Dw : Datum H) : Lt1 Dw ≃ Fin (dL Dw) := Fintype.equivFin _

def addP {S : Type} [CommRing S] : Fin 1 × Fin (dL Dw) → MvPolynomial (Fin 2 × Fin (dL Dw)) S :=
  fun p => X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2)

def actP {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S] (a : 𝓞 E) :
    Fin 1 × Fin (dL Dw) → MvPolynomial (Fin 1 × Fin (dL Dw)) S :=
  fun p => C (algebraMap c.F S (embK c ((ltIdx Dw).symm p.2).1 a)) * X p

variable {S : Type} [CommRing S] [Algebra c.F S]

variable (y : FrPt Xo c S)

structure IsExpChart (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G) : Prop where
  zero : ∀ m, homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m) ≫
    x (m + 1) = x m
  law : ∀ m, homAt y.x (jetSubstP m (addP (Dw := Dw) (S := S))) ≫ x m =
    jpt y (dL Dw) x m (0 : Fin 2) * jpt y (dL Dw) x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ Xo.univ.t.act.act a = homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a)) ≫ x m
  tan : ∀ ℓ : Lt1 Dw, IsCombAt y.x
    (fun j : Fin (dL Dw) => (homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left)
    (fun j => if j = ltIdx Dw ℓ then 1 else 0) (y.u ℓ.1 ℓ.2)

variable (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G)

abbrev ExpFr (m : ℕ) : Type :=
  LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (1 : ℤ))

def eAt (e : ∀ m, ExpFr y x m) (m : ℕ) (a : 𝓞 E) :=
  LB.pullGen Xo.univ.t.PP.L _ _ (e m) (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left

def betaφ (a : 𝓞 E) : Fin 4 → (Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) :=
  ![(Xo.univ.t.act.act (1 + a * H.bar a)).left, (Xo.univ.t.act.act a).left, 𝟙 _,
    (Xo.univ.t.act.act (a * H.bar a)).left]

def betaε : Fin 4 → ℤ := ![1, -2, -1, -1]

structure IsExpGauge (e : ∀ m, ExpFr y x m) : Prop where
  gen : ∀ m, (e m).IsGen
  trunc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (e (m + 1))
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left)
    (e m)
  rig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (e 0) (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left)
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)
  coc : ∀ a : 𝓞 E, ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) ∧
    ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eAt y x e m (1 + a * H.bar a))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eAt y x e m a) 2)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (e m) (eAt y x e m (a * H.bar a)))))

def IsExpGerm (e : ∀ m, ExpFr y x m) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y (dL Dw) m 1)))
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y (dL Dw) m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (e m) k) ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (x m) τ (toΓ _ (psJet m f))

end Exp

def expVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {S : Type} [CommRing S]
    (f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (α : Lt1 Dw →₀ ℕ) : S :=
  (α.prod fun _ n => (n.factorial : S)) *
    MvPowerSeries.coeff (Finsupp.mapDomain (fun ℓ => ((0 : Fin 1), ltIdx Dw ℓ)) α) f

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.IntAllFree
noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def IntAll : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → T.FinRes →
    ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr),
      ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧
        letI := io.toAlgebra; letI := io'.toAlgebra
        ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
          (∀ a : T.V, φ (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ∧ FrMap φ y z ∧ FrBor t z y'.1

end Formalism.L2.PjFree
end
end
