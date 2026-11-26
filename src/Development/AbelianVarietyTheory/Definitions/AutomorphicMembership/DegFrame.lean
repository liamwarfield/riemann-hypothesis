module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

abbrev Letter : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

def letters : List (Letter Dw) :=
  (List.finRange (Fintype.card (E →+* ℂ))).flatMap fun a =>
    (List.finRange (Dw.mult ((Fintype.equivFin (E →+* ℂ)).symm a))).map fun i => ⟨_, i⟩

abbrev Sym (E : Type) [Field E] : Type := (ℕ → Bool) × Option ℝ × (((E →+* ℂ) × ℕ) ⊕ ℕ)

def letterOf : ((E →+* ℂ) × ℕ) ⊕ ℕ → Option (Letter Dw)
  | .inl (τ, k) => if h : k < Dw.mult τ then some ⟨τ, ⟨k, h⟩⟩ else none
  | .inr k => (letters Dw)[k]?


open Classical in
def expo (w : Sym E →₀ ℤ) (x : Letter Dw) : ℤ := w.sum fun a n => if letterOf Dw a.2.2 = some x then n else 0


open Classical in
def parOf (w : Sym E →₀ ℤ) : Option ℝ := if h : w.support.Nonempty then h.choose.2.1 else none

variable {Dw}


open Classical in
def lnStep {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ) (b : Bool) :
    ((E →+* ℂ) × ℕ) ⊕ ℕ → ℝ
  | .inl (τ, k) => if h : k < Dw.mult τ then Real.log (grNorm t x (lat t p x b) (u τ) ⟨k, h⟩) -
      (if b ∧ τ (H.rt : E) = H.rt0 then vDiff E p * Real.log p else 0) else 0
  | .inr k => if h : k < (letters Dw).length then
      Real.log (grNorm t x (lat t p x b) (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, h⟩) else 0

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def divOf (n : Letter Dw → ℤ) : Y.Y.Dv := ∑ x, n x • Y.gr x.1 x.2

def resP (v : HeightOneSpectrum (𝓞 F)) : ℕ := ringChar (𝓞 F ⧸ v.asIdeal)

def ioOf (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v) : AlgebraicClosure F →+* ℂ_[p] :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans ℚ F _
  haveI : Nonempty (AlgebraicClosure F →+* ℂ_[p]) := ⟨(IsAlgClosed.lift : AlgebraicClosure F →ₐ[ℚ] ℂ_[p]).toRingHom⟩
  Classical.epsilon fun io => ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O


open Classical in
def lgOf (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) : ℝ :=
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let f := (Y.gr_spec (below y.1)).choose_spec.choose
    let t := (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose
    let ψ : Y.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2
  else 0

abbrev Mets (C : CxSt F) : Type := ∀ (_ : Option ℝ) (σ : F →+* ℂ) (n : Letter Dw → ℤ), C.Met Y.Y σ (divOf Y n)

def adlOf {C : CxSt F} (hm : Mets Y C) (w : Sym E →₀ ℤ) : Adl C Y.Y where
  D := divOf Y (expo Dw w)
  n := 1
  m σ := hm (parOf w) σ _
  ci := 0
  lg := lgOf Y w


variable (Dw) in
def rootSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) : Sym E →₀ ℤ :=
  if i < Dw.p then Finsupp.single (a, R, .inl (τ, i)) 1
  else Finsupp.single (a, R, .inl (conjEmb τ, Dw.p + Dw.q - 1 - i)) (-1)

def wholeSym (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} : Fin g ⊕ Fin g → (Sym E →₀ ℤ)
  | .inl k => Finsupp.single (a, R, .inr k) 1
  | .inr k => Finsupp.single (a, R, .inr (Fin.rev k)) (-1)


variable (Dw) in
def detSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) : Sym E →₀ ℤ :=
  ∑ i ∈ Finset.range (Dw.p + Dw.q), rootSym Dw a R τ i

def IsFlat (τ : E →+* ℂ) (σ : Y.Y.Fn) : Prop :=
  ∀ y : Y.Y.X, (divOf Y (expo Dw (detSym Dw (fun _ => false) none τ))).GeneratesAt y σ

def IsCoord {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (p : Sp k ⟶ Y.Y.X) (g : EigFrame Z φ x)
    (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : k) : Prop :=
  ∃ (y : Y.Y.X) (ψ : Y.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* Y.Y.X.presheaf.stalk y)
    (f : EigFrame Z φ₁ (stalkPt Y.Y y ≫ Y.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ) (r : Y.Y.X.presheaf.stalk y),
    p = spMap ψ ≫ stalkPt Y.Y y ∧ f.Tri (algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) Y.f0 t ∧
      f.Tri ψ g t' ∧
      algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField r =
        σ * ((∏ z : Letter Dw, t z.1 z.2 ^ n z : Y.Y.Fnˣ) : Y.Y.Fn) ∧
      a = ψ r * ((∏ z : Letter Dw, t' z.1 z.2 ^ (-n z) : kˣ) : k)

def FlagPt.frame {Ω : Type} [Field Ω] (y : FlagPt Z Ω) : EigFrame Z y.fK (y.y ≫ genι Z) :=
  ⟨y.u, y.tan, y.eig, y.basis⟩

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (fl : s.Flag)
  {C : CxSt D.what₂.LL} (hm : ∀ k, Mets (fl.C k) C)

def arIn : ArIn D.what₂.Tau N (D.R.f * N) s.Comp where
  A _ := Sym D.host.E →₀ ℤ
  num k := polar fun w => (adlOf (fl.C k) (hm k) w).arTop
  root a R x _ := rootSym S.Dw a (some R) (DV.tauEmb D x.1) x.2
  whole a R x _ := wholeSym a (some R) x

def setB (κ : Lv A) (B : ℝ) : Finset ℕ :=
  (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ (2 * (NumberField.discr D.host.E).natAbs * κ.l.M').primeFactors

def flatSec (k : s.Comp) (τ : D.what₂.Tau) : (fl.C k).Y.Fn := Classical.epsilon (IsFlat (fl.C k) (DV.tauEmb D τ))

def innerPt (k : s.Comp) : (fl.C k).Y.X :=
  Classical.epsilon fun x => IsClosed ({x} : Set (fl.C k).Y.X) ∧ (fl.C k).π x ∉ genBd s.T.Z

def flatSt : FlatSt s where
  sv τ y := Classical.epsilon fun a => ∃ (k : s.Comp) (p : Sp Qb ⟶ (fl.C k).Y.X), p ≫ (fl.C k).π = y.y ∧
    IsCoord (fl.C k) p y.frame (expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))) (flatSec s fl k τ) a
  ht B k τ := (adlOf (fl.C k) (hm k) (detSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D τ))).ht (innerPt s fl k)

def degFrame (k : s.Comp) (τ : D.what₂.Tau) : ℝ :=
  (adlOf (fl.C k) (hm k) (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))).ht (innerPt s fl k)

def degFlat (k : s.Comp) (τ : D.what₂.Tau) : ℝ :=
  degFrame s fl hm k τ + (S.Dw.q : ℝ) * (Real.log A.H.d -
    Real.log (NumberField.discr D.host.E).natAbs / (Module.finrank ℚ D.host.E : ℝ))

end GlobalTheory.ShFam.Pad
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet
open scoped ComplexOrder

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

section Manifold

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {d : ℕ}

def LiesIn (y : CxPts p σ) (C : Closeds Y) : Prop := y.1 (IsLocalRing.closedPoint ℂ) ∈ C

def IsDivNorm (R : AnRead p σ d) (C : Closeds Y) (n : CxPts p σ → ℝ) : Prop :=
  (∀ y, 0 ≤ n y ∧ n y ≤ 1) ∧ ∀ y, ∃ (V : Y.affineOpens) (t : Γ(Y, V.1)) (f : CxPts p σ → ℝ),
    y ∈ ptsIn p σ V.1 ∧ (Scheme.IdealSheafData.vanishingIdeal C).ideal V = Ideal.span {t} ∧
    R.SmoothOn (ptsIn p σ V.1) f ∧ ∀ z ∈ ptsIn p σ V.1, n z ^ 2 = ‖ev p σ V.1 t z‖ ^ 2 * Real.exp (-f z)

theorem ev_eq_zero_iff {C : Closeds Y} {V : Y.affineOpens} {t : Γ(Y, V.1)}
    (h : (Scheme.IdealSheafData.vanishingIdeal C).ideal V = Ideal.span {t}) {y : CxPts p σ} (hy : y ∈ ptsIn p σ V.1) :
    ev p σ V.1 t y = 0 ↔ LiesIn y C := by
  have h1 := Scheme.IdealSheafData.mem_support_iff_of_mem (I := Scheme.IdealSheafData.vanishingIdeal C)
    (U := V) (mem_ptsIn.1 hy)
  rw [h, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton] at h1
  have h2 : (Scheme.IdealSheafData.vanishingIdeal C).support = C :=
    SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal C)
  rw [h2] at h1
  rw [LiesIn, h1, ← not_ne_iff, ← mem_ptsIn_basicOpen hy, mem_ptsIn]
  rfl

theorem isOpen_not_liesIn (C : Closeds Y) : IsOpen {y : CxPts p σ | ¬ LiesIn y C} := by
  have : {y : CxPts p σ | ¬ LiesIn y C} = ptsIn p σ C.compl := Set.ext fun y => (mem_ptsIn (y := y) (U := C.compl)).symm
  exact this ▸ isOpen_ptsIn _

namespace IsDivNorm

variable {R : AnRead p σ d} {C : Closeds Y} {n : CxPts p σ → ℝ} (h : IsDivNorm R C n)
include h

end IsDivNorm

theorem isDivNorm_of_eqn [IsAffine Y] (R : AnRead p σ d) {C : Closeds Y} {t : Γ(Y, ⊤)}
    (h : (Scheme.IdealSheafData.vanishingIdeal C).ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {t}) :
    IsDivNorm R C fun y => ‖ev p σ ⊤ t y‖ / √(1 + ‖ev p σ ⊤ t y‖ ^ 2) := by
  have hp : ∀ y, 0 < 1 + ‖ev p σ ⊤ t y‖ ^ 2 := fun y => by positivity
  refine ⟨fun y => ⟨by positivity, ?_⟩, fun y => ⟨⟨⊤, isAffineOpen_top Y⟩, t,
    fun z => Real.log (1 + ‖ev p σ ⊤ t z‖ ^ 2), mem_ptsIn_top, h, fun i => ?_, fun z _ => ?_⟩⟩
  · exact (div_le_one (Real.sqrt_pos.2 (hp y))).2 (Real.le_sqrt_of_sq_le (by linarith))
  · exact (contDiffOn_const.add ((GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over _ (isOpen_ptsIn _))
      (R.holoOn_ev ⊤ t i)).norm_sq ℂ)).log fun _ _ => (hp _).ne'
  · rw [div_pow, Real.sq_sqrt (hp z).le, Real.exp_neg, Real.exp_log (hp z), div_eq_mul_inv]

abbrev ChartForm (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) : Type := AlgChart p σ d → CxPts p σ → (Fin d → ℂ) → ℝ

def ddcForm (f : CxPts p σ → ℝ) : ChartForm p σ d := fun c y ξ => c.levi f y ξ / Real.pi

def IsPotential (R : AnRead p σ d) (a : ChartForm p σ d) (W : Set (CxPts p σ)) (φ : CxPts p σ → ℝ) : Prop :=
  IsOpen W ∧ R.SmoothOn W φ ∧ ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, y ∈ W → ∀ ξ, a c y ξ = ddcForm φ c y ξ

def IsKaehlerForm (R : AnRead p σ d) (a : ChartForm p σ d) : Prop :=
  (∀ y, ∃ W φ, y ∈ W ∧ IsPotential R a W φ) ∧ ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ ξ, ξ ≠ 0 → 0 < a c y ξ

theorem ddcForm_coord (c : AlgChart p σ d) (j : Fin d) {y : CxPts p σ} (hy : y ∈ c.e.source) (ξ : Fin d → ℂ) :
    ddcForm (fun z => Complex.normSq (c.e z j)) c y ξ = Complex.normSq (ξ j) / Real.pi := by
  have hg : ContDiffAt ℂ 2 (fun v : ReciprocityTheory.L2DbarEstimates.V d => v j) (c.e y) :=
    (EuclideanSpace.proj j : ReciprocityTheory.L2DbarEstimates.V d →L[ℂ] ℂ).contDiff.contDiffAt
  have e := ReciprocityTheory.L2DbarEstimates.leviV_normSq_comp hg ξ
  have e1 : ∀ a, ReciprocityTheory.L2DbarEstimates.wd d a (fun v : ReciprocityTheory.L2DbarEstimates.V d => v j) (c.e y) = if j = a then 1 else 0 := fun a => by
    have : (fun v : ReciprocityTheory.L2DbarEstimates.V d => v j) =
        ((EuclideanSpace.proj j : ReciprocityTheory.L2DbarEstimates.V d →L[ℂ] ℂ).restrictScalars ℝ) := rfl
    rw [ReciprocityTheory.L2DbarEstimates.wd, this, ContinuousLinearMap.fderiv]
    by_cases h : j = a
    · simp [ReciprocityTheory.L2DbarEstimates.bas, h]
    · simp [ReciprocityTheory.L2DbarEstimates.bas, h]
  have e2 : ∑ a, ReciprocityTheory.L2DbarEstimates.wd d a (fun v : ReciprocityTheory.L2DbarEstimates.V d => v j) (c.e y) * ξ a = ξ j := by simp [e1]
  rw [e2] at e
  refine congrArg (· / Real.pi) (Eq.trans (congrArg Complex.re (Eq.trans ?_ e)) (Complex.ofReal_re _))
  refine ReciprocityTheory.L2DbarEstimates.leviV_congr (Filter.eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy))
    fun v hv => ?_) ξ
  simp only [c.e.right_inv hv]

theorem isKaehlerForm_ddcForm {R : AnRead p σ d} {φ : CxPts p σ → ℝ} (h : R.SmoothOn Set.univ φ)
    (hp : ∀ y, ∃ c : AlgChart p σ d, y ∈ c.e.source ∧ ∀ ξ, ξ ≠ 0 → 0 < ddcForm φ c y ξ) : IsKaehlerForm R (ddcForm φ) :=
  ⟨fun _ => ⟨_, φ, Set.mem_univ _, isOpen_univ, h, fun _ _ _ _ _ => rfl⟩, fun c y hy ξ hξ => by
    obtain ⟨c', hy', h'⟩ := hp y
    rw [ddcForm, AlgChart.levi_trans hy hy' (h.contDiffAt_two isOpen_univ hy' trivial)]
    exact h' _ (AlgChart.dtrans_ne_zero hy hy' hξ)⟩

def IsConjMap (m : CxPts p σ' → CxPts p σ) : Prop := ∀ z, (m z).1 = spMap (starRingEnd ℂ) ≫ z.1

end Manifold

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

namespace EigFrame

variable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)

def vec (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : TanM x Z.t.G := tanOf (f.tan τ i)

theorem act_vec (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (a : 𝓞 E) :
    actR Z.t.act a (f.vec τ i) = φ (embK c τ a) • f.vec τ i := tan_ext (f.eig τ i a)

theorem existsUnique_sum (τ : E →+* ℂ) (w : TanM x Z.t.G) (hw : ∀ a, actR Z.t.act a w = φ (embK c τ a) • w) :
    ∃! a : Fin (Dw.mult τ) → R, w = ∑ i, a i • f.vec τ i :=
  (existsUnique_congr fun a => isComb_iff (f.vec τ) a w).1
    (f.basis τ _ (isTan_tv w) fun a => congrArg (fun v => (tv v).left) (hw a))

theorem linearIndependent_vec (τ : E →+* ℂ) : LinearIndependent R (f.vec τ) :=
  Fintype.linearIndependent_iff.2 fun a ha => congrFun
    ((f.existsUnique_sum τ 0 fun a => by simp).unique ha.symm (y₂ := 0) (by simp))

def ofVec (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → TanM x Z.t.G)
    (he : ∀ τ i a, actR Z.t.act a (v τ i) = φ (embK c τ a) • v τ i)
    (hb : ∀ τ (w : TanM x Z.t.G), (∀ a, actR Z.t.act a w = φ (embK c τ a) • w) →
      ∃! a : Fin (Dw.mult τ) → R, w = ∑ i, a i • v τ i) : EigFrame Z φ x where
  v τ i := (tv (v τ i)).left
  tan τ i := isTan_tv _
  eig τ i a := congrArg (fun v => (tv v).left) (he τ i a)
  basis τ _ hw h := (existsUnique_congr fun a => isComb_iff (v τ) a (tanOf hw)).2 (hb τ _ fun a => tan_ext (h a))

end EigFrame

section FrPt

variable {S : Type} [CommRing S] [Algebra c.F S] (Z) (y : FrPt Xo c S) {x : Sp S ⟶ Z.X}
  (hx : GlobalTheory.AllWt.ptF y ≫ Z.jQ ≫ genι Z = x)

theorem ptF_fst : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _

theorem ptF_snd : GlobalTheory.AllWt.ptF y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

def lieEquiv : TanM y.x Xo.univ.t.G ≃ₗ[S] TanM x Z.t.G :=
  (pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y) (ptF_fst y)).symm.trans (pushE Z.m (GlobalTheory.AllWt.ptF y) hx)

theorem lieEquiv_act (a : 𝓞 E) (v : TanM y.x Xo.univ.t.G) :
    lieEquiv Z y hx (actR Xo.univ.t.act a v) = actR Z.t.act a (lieEquiv Z y hx v) := by
  obtain ⟨w, rfl⟩ := (pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y) (ptF_fst y)).surjective v
  rw [← pushE_act]
  simp only [lieEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact pushE_act _ _ _ _ _

def EigFrame.ofFrPt : EigFrame Z (algebraMap c.F S) x :=
  EigFrame.ofVec (fun τ i => lieEquiv Z y hx (tanOf (t := Xo.univ.t) (y.tan τ i)))
    (fun τ i a => by
      rw [← lieEquiv_act, ← map_smul]
      exact congrArg _ (tan_ext (y.eig τ i a)))
    fun τ w hw => by
      obtain ⟨w, rfl⟩ := (lieEquiv Z y hx).surjective w
      refine (existsUnique_congr fun a => ?_).1 (y.basis τ _ (isTan_tv w) fun a => congrArg (fun v => (tv v).left)
        ((lieEquiv Z y hx).injective (by rw [lieEquiv_act, hw, map_smul]) :
          actR Xo.univ.t.act a w = algebraMap c.F S (embK c τ a) • w))
      refine (isComb_iff (fun i => tanOf (t := Xo.univ.t) (y.tan τ i)) a w).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← (lieEquiv Z y hx).injective.eq_iff, map_sum]
      simp only [map_smul]

theorem EigFrame.ofFrPt_v (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : ∃ w : Sp (DualNumber S) ⟶ Z.oF.t.G.left,
    IsTanAtG Z.oF.t (GlobalTheory.AllWt.ptF y) w ∧ w ≫ Z.m0.toSABMap.φ = y.u τ i ∧
      w ≫ Z.m.φ = (EigFrame.ofFrPt Z y hx).v τ i :=
  ⟨_, isTan_tv _, congrArg (fun v => (tv v).left) ((pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y)
    (ptF_fst y)).apply_symm_apply (tanOf (t := Xo.univ.t) (y.tan τ i))), rfl⟩

end FrPt

variable {σ σ' : c.F →+* ℂ}


variable (Z) in
def cxPt (y : FrPt Xo c (CAt σ)) : CxPts (genStr Z) σ :=
  ⟨GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ,
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) Z.jQ_over).trans (ptF_snd y))⟩

theorem cxPt_congr {y y' : FrPt Xo c (CAt σ)} (h : y.x = y'.x) : cxPt Z y = cxPt Z y' :=
  Subtype.ext (congrArg (· ≫ Z.jQ) (pullback.hom_ext
    ((ptF_fst y).trans (h.trans (ptF_fst y').symm))
    ((ptF_snd y).trans (ptF_snd y').symm)))

theorem not_liesIn_cxPt (y : FrPt Xo c (CAt σ)) : ¬ LiesIn (cxPt Z y) (genBd Z) :=
  fun h => h ⟨GlobalTheory.AllWt.ptF y (IsLocalRing.closedPoint ℂ), rfl⟩


variable (Z) in
def cxFrame (y : FrPt Xo c (CAt σ)) : EigFrame Z σ ((cxPt Z y).1 ≫ genι Z) :=
  EigFrame.ofFrPt (S := CAt σ) Z y (Category.assoc _ _ _).symm

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]


variable (Z σ) in
abbrev manifold : AnRead (genStr Z) σ Dw.dim := AnRead.all _ _ _


variable (Z) in
structure OddPrimesWithRootsOfUnity : Type where

  m : ℕ

  cpt : Fin m → Closeds (gen Z)
  cpt_list : ReciprocityTheory.AnForm.R.FinalTheorems.CompList (genBd Z : Set (gen Z : Scheme.{0})) cpt

  nrm : ∀ σ : c.F →+* ℂ, Fin m → CxPts (genStr Z) σ → ℝ
  nrm_div : ∀ σ i, IsDivNorm (manifold Z σ) (cpt i) (nrm σ i)
  nrm_conj : ∀ σ σ' (j : CxPts (genStr Z) σ' → CxPts (genStr Z) σ), IsConjMap j → ∀ i z, nrm σ' i z = nrm σ i (j z)

  kae : ∀ σ : c.F →+* ℂ, ChartForm (genStr Z) σ Dw.dim
  kae_kaehler : ∀ σ, IsKaehlerForm (manifold Z σ) (kae σ)
  kae_conj : ∀ σ σ' (j : CxPts (genStr Z) σ' → CxPts (genStr Z) σ), IsConjMap j → ∀ W φ,
    IsPotential (manifold Z σ) (kae σ) W φ → IsPotential (manifold Z σ') (kae σ') (j ⁻¹' W) (φ ∘ j)

  cst : ℝ
  cst_pos : 0 < cst
  cst_small : ∀ σ i (ch : AlgChart (genStr Z) σ Dw.dim), ∀ y ∈ ch.e.source, ¬ LiesIn y (cpt i) → ∀ ξ,
    2 * m * cst * |ddcForm (fun z => Real.exp 1 - Real.log (nrm σ i z ^ 2)) ch y ξ| ≤ Real.exp 1 * kae σ ch y ξ

  met : ∀ (σ : c.F →+* ℂ) (y : CxPts (genStr Z) σ),
    TanM (y.1 ≫ genι Z) Z.t.G →ₗ[ℂ] TanM (y.1 ≫ genι Z) Z.t.G →ₗ⋆[ℂ] ℂ
  met_smooth : ∀ σ, IsLieMetric Z.t (genι Z) (manifold Z σ) (met σ)
  met_conj : ∀ σ σ' (y : CxPts (genStr Z) σ) (y' : CxPts (genStr Z) σ') (v w : TanM (y.1 ≫ genι Z) Z.t.G)
    (v' w' : TanM (y'.1 ≫ genι Z) Z.t.G), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 →
    (tv v').left = spMap (dualMap (starRingEnd ℂ)) ≫ (tv v).left →
    (tv w').left = spMap (dualMap (starRingEnd ℂ)) ≫ (tv w).left →
    met σ' y' v' w' = starRingEnd ℂ (met σ y v w)

namespace OddPrimesWithRootsOfUnity

variable (x : OddPrimesWithRootsOfUnity Z)

def r (σ : c.F →+* ℂ) (y : CxPts (genStr Z) σ) : ℝ := Real.exp 1 - Real.log ((∏ i, x.nrm σ i y) ^ 2)

def gram (y : CxPts (genStr Z) σ) (f : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ) :
    Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := gramOf (x.met σ y) (f.vec τ)

variable {y : CxPts (genStr Z) σ}

end OddPrimesWithRootsOfUnity

end Free

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

section Tr

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m}

abbrev HdB (R : RealDat a.D A Ks) : Type := @Hd b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)

structure Same {R : RealDat a.D A Ks} (y : Hd R) (y' : HdB b R) : Prop where
  tup : letI := alg b iK; HEq y'.tup y.tup
  tupT : letI := alg b iK; HEq y'.tupT y.tupT
  PY : letI := alg b iK; HEq y'.PY.ψ y.PY.ψ
  PW : letI := alg b iK; HEq (fun i => (y'.PW i).ψ) fun i => (y.PW i).ψ

end Tr

section Univ

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px)

def mAU (b : Bool) (a : I.ι) : Mat1 X.toD7.what₂.LL (Gc X.B px) :=
  rMat (D := X.toD7) (famR X I hX Set.univ Xg tr).A (levP (face0 X I hX Set.univ Xg tr).lv2 b).1
    (levP (face0 X I hX Set.univ Xg tr).lv2 b).2 (tAll I a)

def mLU (a : I.ι) (j : ℕ) : Mat1 X.toD7.what₂.LL (Gc X.B px) :=
  if h : 1 ≤ j ∧ j ≤ X.toD7.R.m then
    lMat (D := X.toD7) (famR X I hX Set.univ Xg tr).A (face0 X I hX Set.univ Xg tr).lv2.P0 (face0 X I hX Set.univ Xg tr).lv2.ψ0
      ⟨j - 1, by omega⟩ (tAll I a)
  else Mat1.zero _ _

end Univ

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)

structure PerT (Z : w.Lt) (hX : B.fields.Ok) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px) (p : PkB B w.C (Gc B w.px))
    (j : ∀ a : w.I.ι, (Fin (mAU (w.st Z) w.I hX Xg tr true a).n → B.LL) → (p.sA true a).A.T) (d : PerD p) : Type where
  e : ∀ a : w.C.Tup, Df.MtCx w.I a ≃ₗ[ℂ] (p.sA true a).A.T
  ref : ∀ u F, Df.SameForm w.I w.l u w.I.mu0 F ((d.e0 u).symm (e w.C.mu0 F))
  tw : ∀ u (a : w.C.Tup) F, Df.SameForm w.I w.l u a F ((d.eT u a).symm (e a F))
  crd : ∀ (a : w.C.Tup) y, IsCrd w.I hX a (e a)
    (rowForm (D := (w.st Z).toD7) (famR (w.st Z) w.I hX Set.univ Xg tr).A (lev1 w.I) (chr1 w.I) (tAll w.I a) y) (j a y)


variable {w} in
def CoreP {Z : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl} (z : Dat (w.st Z) w.I hX T Wt) : Prop :=
  Formalism.L2.Pj.LawsCore z.core.toCore ∧ z.core.Q.Canon ∧ (∀ j, 1 ≤ (z.core.Q.Dw j).p + (z.core.Q.Dw j).q) ∧ z.core.pb = f.P.pb


open Classical in
structure MuW (Wt : Set B.places.Pl) (W : RowsRest B w.C) : Prop where
  tw : ∀ v, w.I.xi (W.muTw v) = T.xiTw f v
  on : ∀ v, v ∈ Wt → W.muAt v = W.muTw v
  off : ∀ v, v ∉ Wt → W.muAt v = w.C.mu0


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in
structure RowPk {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl} (z : Dat (w.st Z₀) w.I hX T Wt) : Type 1 where
  y : Hd z.R.toRealDat
  tup : ∀ t, y.tup t = ixOf w.I (usedOf w.I T Wt) t
  p : PkB B w.C (Gc B w.px)
  t : PkT z.F y (mAU (w.st Z₀) w.I hX z.Xg z.tr) p
  mL : ∀ a j, p.mL a j = mLU (w.st Z₀) w.I hX z.Xg z.tr a j
  e : PerD p
  per : PerT w Z₀ hX z.Xg z.tr p (fun a x => (t.tA true a).j x) e
  W₀ : RowsRest B w.C
  mu : MuW w Wt W₀
  sha : GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen
  n : Nums p W₀
  kap : ∀ η hη V S N G, DV.KapDef (assemble B w.C (p.what₂ e W₀ n η hη) V S N G)
  num : ∀ η hη V S N G, NumOK (assemble B w.C (p.what₂ e W₀ n η hη) V S N G)

variable {w} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl} {z₀ : Dat (w.st Z₀) w.I hX T Wt} (q : RowPk w z₀)

abbrev RowPk.W (η : ℕ → B.places.Pl → ℚ) (hη : ∀ j v, 0 ≤ η j v) : RowsRest B w.C := q.p.what₂ q.e q.W₀ q.n η hη

def RowPk.eta (_q : RowPk w z₀) : ℕ → B.places.Pl → ℚ := etaOf z₀.R z₀.F

structure RowPk.Over : Type 1 where
  η : ℕ → B.places.Pl → ℚ
  hη : ∀ j v, 0 ≤ η j v
  V : DivStage B w.C (q.W η hη)
  S : SStage B w.C (q.W η hη)
  N : NStage B w.C (q.W η hη)
  G : GJStage B w.C

variable {q}

abbrev RowPk.Over.Z (o : q.Over) : w.Lt := ⟨q.W o.η o.hη, o.V, o.S, o.N, o.G⟩

def StdIso (X : Stages) (px : PreX X.B.toPre) (eR : Gc X.B px ≃* G0g X.toD7.nd) : Prop :=
  ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ (X.B.primes px).vGs)
    (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv).1 : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧
    ∀ g kv, g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) (eR g kv)

structure RowPk.Over.Fits (o : q.Over) : Prop where
  div : DivIs q.p o.V
  grp : GrpTrue o.N f
  grpAt : GrpAt (w.st o.Z) w.I
  cen : ∀ eR, StdIso (w.st o.Z) w.px eR → CenIs q.p o.N eR

structure Side0 (o : q.Over) : Type 1 where
  cen : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D o.Z).nd)) →ₐ[ℂ] Module.End ℂ (q.p.sA false μ).A.T
  tie : ∀ μ, (q.p.sA false μ).e = (open Classical in
    if h : (w.D o.Z).ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D o.Z).nd)) then cen μ ⟨(w.D o.Z).ntypes.e0, h⟩ else 0)
  is : ∀ eR, StdIso (w.st o.Z) w.px eR → ∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D o.Z).nd)))
    (c' : Subalgebra.center ℂ (MonoidAlgebra ℂ (Gc B w.px))),
    (∀ g, (c' : MonoidAlgebra ℂ (Gc B w.px)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D o.Z).nd)).coeff (eR g)) →
      ∀ x, cen μ c x = (q.p.sA false μ).act c' x
  RR : HLat B.LL
  frames : ∀ v, IsUnit (RR.X v).det
  jEE : RR.V →ₛₗ[B.embLL] (q.p.ch false).EE.T
  basis : LinearIndependent ℂ (fun i => jEE (RR.b i)) ∧ Submodule.span ℂ (Set.range (fun i => jEE (RR.b i))) = ⊤
  norm : ∀ x : RR.V, Formalism.HermitianLatticesTheory.normAt RR.b RR.X (InfinitePlace.mk B.embLL) x = ‖jEE x‖

@[reducible] def Side0.p0 {o : q.Over} (s : Side0 o) : BaseLevelRowSide (w.D o.Z) :=
  ⟨{ Amb := fun μ => (q.p.sA false μ).A.T
     instAmb := fun μ => (q.p.sA false μ).A.nacg
     instAmbi := fun μ => (q.p.sA false μ).A.ips
     instAmbf := fun μ => (q.p.sA false μ).A.fd
     Mult := fun μ j => ((q.p.ch false).Mult μ j).T
     instMult := fun μ j => ((q.p.ch false).Mult μ j).nacg
     instMulti := fun μ j => ((q.p.ch false).Mult μ j).ips
     instMultf := fun μ j => ((q.p.ch false).Mult μ j).fd
     multZero := (q.p.ch false).multZero
     multTop := (q.p.ch false).multTop
     io := (q.p.ch false).io
     Mtilde := fun μ => (q.p.sA false μ).lat
     cen := s.cen
     eOp := fun μ => (q.p.sA false μ).e
     eOp_idem := fun μ => (q.p.sA false μ).idem
     eOp_sa := fun μ => (q.p.sA false μ).sa
     eOp_tie := s.tie
     RR := s.RR
     RR_frames := s.frames
     jEE := s.jEE
     jEE_basis := s.basis
     jEE_norm := s.norm }⟩


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in
structure Moved (o : q.Over) : Type 1 where
  z : Dat (w.st o.Z) w.I hX T Wt
  intersectionNumber_baseChange : Holds z.R z.F
  exAt : z.R.toRealDat.ExAt
  inGeo : GlobalTheory.RealGeo.InGeo z.geo
  Xg : z.Xg = z₀.Xg
  tr : z.tr = z₀.tr
  core : CoreP z₀ → CoreP z
  eta : ∀ j v, etaOf z.R z.F j v = q.eta j v
  W1 : ∀ F0, z.W1 F0 = z₀.W1 F0
  y : Hd z.R.toRealDat
  tup : ∀ t, y.tup t = ixOf w.I (usedOf w.I T Wt) t
  t : PkT z.F y (mAU (w.st o.Z) w.I hX z.Xg z.tr) q.p
  tA : ∀ b a, HEq (t.tA b a).j (q.t.tA b a).j


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in
structure ReadPk {o : q.Over} (m : Moved o) (s : Side0 o) : Type 1 where
  Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0
  Z : RationalReadingWithoutCongruence m.z.R m.z.F s.p0 Y
  tup : Y.tup = m.y.tup
  tupT : Y.tupT = m.y.tupT
  PY : Y.PY = m.y.PY
  PW : Y.PW = m.y.PW
  jA : ∀ t, HEq (Y.jA t) ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).j
  jA0 : ∀ t, HEq (Y.jA0 t) ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).j
  eMt : ∀ (i : Fin (w.D o.Z).R.m) t x, HEq (Y.eMt i t x) x

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 1000000

def Reads {D : D7} (X : NExpTied D) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hA : NX.AdmTw D i k Q ψ)
    (e : FractionRing (D.ntw.Ok i k) →+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (r : D.nexp.MtV i j b k Q ψ → GAf D.host.E D.R.nV → V) : Prop :=
  ∃ ω : (X.mtV i j b k Q ψ h1 h2 hA).W →ₛₗ[e] V, Function.Injective ω ∧
    ∀ f g, r f g = ω (((X.mtV i j b k Q ψ h1 h2 hA).real f).1 g)

def plsOf {D : D7} (X : NExpTied D) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hA : NX.AdmTw D i k Q ψ) :
    Finset (PlE D.host) × Finset (PlE D.host) := ((X.mtV i j b k Q ψ h1 h2 hA).QP, (X.mtV i j b k Q ψ h1 h2 hA).DP)

structure ExpRel {D : D7} (L : LocAll (lay0 D)) (X : NExpTied D) (X' : NExpTied (withLoc L)) : Prop where
  tau : TauTrue X → TauTrue X'
  pl : ∀ i j b k Q ψ h1 h2 hA, plsOf X' i j b k Q ψ h1 h2 hA = plsOf X i j b k Q ψ h1 h2 hA
  reads : ∀ i j b k Q ψ h1 h2 hA e (V : Type) [AddCommGroup V] [Module ℂ V] r,
    Reads X i j b k Q ψ h1 h2 hA e V r → Reads X' i j b k Q ψ h1 h2 hA e V r

structure StA (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Type 1 where
  host : HostTied D
  jE : D.host.E →+* Qb
  frame : ∀ x, jE x = host.fr.j x
  A : SideA D cf jE
  cg : CGTrue hL D A.wdT
  au : AUTrue hL D A.wdT A.au
  row : RowTrue hL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR
  fr : OmFrame D
  fr_jE : fr.jE = jE
  pht : PhtOn A.wd fr fun _ _ _ _ => True
  depth : RowDepth D rep
  elem : Elem D
  val : ValLL0 D cf
  labc : LabConj D A.wdT
  zeta : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen
  omax : Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x

section Rows

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {cf : CharFrame D}

def repOf : D.what₂.FT → NG.FinTyp D.host.E D.R.r := fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)

structure InMt (cf : CharFrame D) (xi : D.what₂.Tup → HChar D.host.E) (Q : D.what₂.places.Pl → Finset (PlE D.host)) : Type 1 where
  M : MtFam D
  ad : MtAd Y M
  mt : MtInput D M (fun μ j => cf.mu0 j * xi μ) Q

structure InRat : Type 1 where
  kKs : C.Q.c.F →+* ↥D.LL0
  hk : ∀ x : C.Q.c.F, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap C.Q.c.F D.what₂.LL x
  In : RatIn D (ratDatR R cG kKs hk)
  rat : RatAd Y cG kKs hk In

variable {Y cG}

abbrev InRat.S (n : InRat Y cG) : RatDat D.ntw := ratDatR R cG n.kKs n.hk

structure SettingsFormsState (a : StA hL D cf (repOf Y)) (n : InRat Y cG)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  Bs : SideB D cf a.A.row (lowAll D) Pq n.S n.In.hL n.In.eig n.In.θ
  Sb_le : ∀ i, n.In.Sb ⊆ D.ntw.S0 i
  rootsOfUnityRing_le_wittIntegers : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D))
  lam : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z

variable (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1)

structure SeriesState (a : StA hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends SettingsFormsState a n Pq where
  YS : NExpRealS R cG n.S
  eF : YS.eF = Bs.eF
  fi : ∀ i x, HEq ((YS.fi i).e x) x
  ser : SerAt YS g.v₀ Bs.exp PV cf Pq
  tau : TauTrue Bs.exp

structure ModuliPointsState (a : StA hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends SeriesState g a n PV Pq where
  geo : Nonempty (GlobalTheory.GeoTie.ThetaTie YS g.fw D.nth)

variable {g}

structure StC {a : StA hL D cf (repOf Y)} {n : InRat Y cG} {xi : D.what₂.Tup → HChar D.host.E}
    {Q : D.what₂.places.Pl → Finset (PlE D.host)} (m : InMt Y cf xi Q)
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} (b : ModuliPointsState g a n m.ad.PV Pq)
    (k : D.what₂.places.Pl → ℕ) (psi : D.what₂.places.Pl → HChar D.host.E) : Type 1 where
  ch : NChoice D
  tp : TupTied D cf ch
  xi_eq : tp.xi = xi
  psi_eq : tp.psi = psi
  Q_eq : ch.Q = Q
  k_eq : ∀ w, TwistedAt D w → ch.k' w = k w
  side : ChoiceSide D cf m.M b.Bs.exp ch tp
  ok : ∀ w, TwistedAt D w → IntegralHeckeForms.TwOK (ch.twI w) (ch.k' w) (ch.Q w) ((ch.psi' w).comp (D.ntw.art (ch.twI w) (ch.Q w)))
  th : EMtTheta Y b.YS ch

end Rows


end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam

variable {D : D7} {A : Amb D}

structure CmList (A : Amb D) : Type where
  ψ : D.what₂.Tau ≃ GlobalTheory.AllWt.Psi A.H
  ψ_val : ∀ t, (ψ t).1 = DV.tauEmb D t

section One

variable {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A)

theorem Lv.good_σ₀ (κ : Lv A) : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl

theorem FinalTheorems.isUnf : Formalism.L2.PjFree.IsUnf (s.U κ.σ₀) := (s.unf _ κ.good_σ₀).1

instance FinalTheorems.compNe : Nonempty s.Comp := (s.unf _ κ.good_σ₀).2.1

abbrev FinalTheorems.Bd : Type :=
  ∀ k : s.Comp, GlobalTheory.HodgeDomain.BdData D.what₂.Tau j (N - j)
    (GlobalTheory.TrueCx.gammaU ((s.U κ.σ₀).X k) (GlobalTheory.TrueCx.le_of_isUnf _ s.isUnf S.p_eq) (GlobalTheory.TrueCx.cmEquiv _ s.isUnf L.ψ k))

def FinalTheorems.cx (B : s.Bd L) (fl : s.Comp → D.what₂.Tau → ℂˣ) : CxPkg D.what₂.Tau N j s.Comp :=
  GlobalTheory.TrueCx.cxTrue (s.U κ.σ₀) s.isUnf S.p_eq (lt_of_lt_of_le two_pos S.two_le) L.ψ B fl

def Sig.wt (S : Sig A N j) (L : CmList A) : (D.what₂.Tau → Fin N → ℤ) →+ GlobalTheory.AllWt.Weight S.Dw where
  toFun la := fun τ i => la (L.ψ.symm τ) (Fin.cast S.rank_eq i)
  map_zero' := rfl
  map_add' _ _ := rfl

def FinalTheorems.Lw (Φ : s.Flag) (k : s.Comp) : (D.what₂.Tau → Fin N → ℤ) →+ (Φ.C k).Y.Dv :=
  AddMonoidHom.mk' (fun la => (Φ.C k).Lw (S.wt L la)) fun a b => by
    have h := GlobalTheory.AllWt.exOf_add (Dw := S.Dw) (S.wt L a) (S.wt L b) 0 0
    rw [add_zero] at h
    simp only [FlagCpt.Lw, map_add (f := _), h]

variable (C : CxSt D.what₂.LL) (K : CutSt C) (R : ResSt C)

def FinalTheorems.alg (Φ : s.Flag) (hd : ∀ k, (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N)
    (Mb : ℝ → (D.what₂.Tau → Fin N → ℝ) → ℚ → ∀ k, Adl C (Φ.C k).Y) :
    AlgPkg (geoOf C K R) D.what₂.Tau N s.Comp where
  Yv k := (Φ.C k).Y
  Ybd k := (Φ.C k).Ybd
  bd k := (Φ.C k).bd
  bd_supp _ := rfl
  Lw k := s.Lw L Φ k
  dim_eq := hd
  degA _ M := Adl.deg M
  degA_ofW k Δ W ι := deg_ofW C _ Δ W ι
  degA_twist _ M ci cf := deg_twist M ci cf
  semipos M := ∀ k, Adl.SemiPos (M k)
  nefFib M := ∀ k, Adl.NefFib (M k)
  Mbar := Mb

structure Kit (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg) : Type 1 where
  Φ : s.Flag
  dim_eq : ∀ k, (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N
  key : KeySec s.Xo κ.c
  B : s.Bd L
  fl : s.Comp → D.what₂.Tau → ℂˣ
  Mb : ℝ → (D.what₂.Tau → Fin N → ℝ) → ℚ → ∀ k, Adl C (Φ.C k).Y
  pad : PadPkg D N j s.Comp jC ng
  levIn : ∀ M, pad.levIn M ↔ κ.inK M

end One

section Fam

variable (F : SrcFam A) (L : CmList A) (C : CxSt D.what₂.LL) (K : CutSt C) (R : ResSt C)
  (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg)

abbrev Kits : Type 1 := ∀ N j hN hj (κ : Lv A), Kit (F.src N j hN hj κ) L C jC ng

variable {F L C jC ng} (k : Kits F L C jC ng)

abbrev Kits.at (w : Dat D (Lv A)) : Kit (F.at w) L C jC ng := k w.N w.j w.two_le w.j_le w.κ

def shimOf (w : Dat D (Lv A)) : ShimU D (geoOf C K R) jC ng w where
  Comp := (F.at w).Comp
  cx := (F.at w).cx L (k.at w).B (k.at w).fl
  alg := (F.at w).alg L C K R (k.at w).Φ (k.at w).dim_eq (k.at w).Mb
  pad := (k.at w).pad

abbrev FormsOver : Type 1 :=
  FormsPkg D (geoOf C K R) (fun j => (datW D F.κg j).N) (fun j => (shimOf K R k (datW D F.κg j)).Comp)
    (fun j => (shimOf K R k (datW D F.κg j)).alg)
    (fun j p => ((shimOf K R k (datW D F.κg j)).pad.loc p).Pt ((shimOf K R k (datW D F.κg j)).pad.loc p).YY)

def famOf (hg : F.κg.primes = Finset.univ.image D.host.g) (P : FormsOver K R k) : ShimFam D (geoOf C K R) (Lv A) where
  levPr := Lv.primes
  levPr_prime _ _ hp := Nat.prime_of_mem_primeFactors hp
  κg := F.κg
  levPr_κg := hg
  jC := jC
  ng := ng
  U := shimOf K R k
  forms := P

end Fam

section Comparison₂

def ambOf (Q : Par D) (h : Q.PinHost) : Amb D := ⟨Q.H, h.1, h.2.1, h.2.2.1⟩

abbrev MD {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Type 1 :=
  Σ (l : Level H) (Dw : Datum H), Moduli Dw l

structure ParTie (Q : Par D) (h : Q.PinHost) (F : SrcFam (ambOf Q h)) : Prop where
  same : ∀ j, InR D j → (⟨Q.l, Q.Dw j, Q.Xo j⟩ : MD Q.H) =
    ⟨F.κg.l, (F.sig _ _ (datW D F.κg j).two_le (datW D F.κg j).j_le).Dw, (F.at (datW D F.κg j)).Xo⟩
  le : Q.c.F ≤ F.κg.c.F

variable {T : Top D} (h : LawsP T) {F : SrcFam (ambOf T.Q h.pins.1)} (t : ParTie T.Q h.pins.1 F) {L : CmList (ambOf T.Q h.pins.1)}
  {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C) {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (k : Kits F L C jC ng)

end Comparison₂

end GlobalTheory.ShFam
end
end
