module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
noncomputable section

namespace GlobalTheory.LevPull

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IntAt (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c) : Prop := ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f

def Pull (d : DeltaDat Xo c 0) (f : Rul Xo c) (g : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → evR d.Xo₂ d.c₂ g y₂ = evR Xo c f y

def FibConst (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → FrOver d y₂' y →
      evR d.Xo₂ d.c₂ g y₂ = evR d.Xo₂ d.c₂ g y₂'

theorem Pull.fibConst {d : DeltaDat Xo c 0} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g) : FibConst d g :=
  fun k _ _ _ _ hk y₂ y₂' y h₁ h₂ => (h k hk y₂ y h₁).trans (h k hk y₂' y h₂).symm


variable (Dw l) in
abbrev LaQ : Type := Dw.La ⧸ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)


variable (Dw l) in
abbrev Gam : Type := LaQ Dw l ≃ₗ[𝓞 E] LaQ Dw l

def IsLift (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ γ, (Submodule.mkQ _) ∘ₗ lift γ = γ.toLinearMap ∘ₗ Submodule.mkQ _

def CongMod (I : Ideal (𝓞 E)) (h h' : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ a, h a - h' a ∈ (I • ⊤ : Submodule (𝓞 E) Dw.La)

end GlobalTheory.LevPull
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

variable {k K L : Type} [Field k] [Field K] [Field L]

def NonUnit (R : Subring K) (f : K) : Prop := f ∈ R ∧ (f = 0 ∨ f⁻¹ ∉ R)

def RatRes (c : k →+* K) (R : Subring K) : Prop := ∀ r ∈ R, ∃ a, NonUnit R (r - c a)

def Dominates (ρ : K →+* L) (B : Subring L) (O : Subring K) : Prop :=
  ∀ f ∈ O, ρ f ∈ B ∧ (NonUnit O f → NonUnit B (ρ f))

structure IsEtTower (cK : k →+* K) (R : Subring K) (cL : k →+* L) (T : Subring L) {r : ℕ}
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) : Prop where

  base : IsLocModel cK R

  normal : IsIntegrallyClosed R

  top : IsLocModel cL T

  const : ∀ a, (ι ⟨cK a, base.const_mem a⟩ : L) = cL a

  retr : ∀ a, ψ (ι a) = a

  zero : ∀ i, ψ (τ i) = 0

  etale : (MvPolynomial.eval₂Hom ι τ).FormallyEtale


set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldPair.nonUnit_iff {R : Subring K} (f : R) :
    _root_.GlobalTheory.FieldPair.NonUnit R f ↔ ¬ IsUnit f := by
  constructor
  · rintro ⟨-, h0 | hinv⟩ hu
    · have hf : f = 0 := Subtype.ext (by simpa using h0)
      exact not_isUnit_zero (hf ▸ hu)
    · obtain ⟨u, rfl⟩ := hu
      have hmul : ((u : R) : K) * ((u⁻¹ : Rˣ) : R) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]
        rfl
      rw [inv_eq_of_mul_eq_one_right hmul] at hinv
      exact hinv (u⁻¹ : Rˣ).1.2
  · intro hnu
    refine ⟨f.2, ?_⟩
    by_contra h
    push_neg at h
    apply hnu
    exact IsUnit.of_mul_eq_one (b := (⟨_, h.2⟩ : R)) (Subtype.ext (by simp [h.1]))


set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldPair.nonUnit_zero (R : Subring K) : _root_.GlobalTheory.FieldPair.NonUnit R 0 :=
  ⟨R.zero_mem, Or.inl rfl⟩


set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldPair.not_nonUnit_one (R : Subring K) : ¬ _root_.GlobalTheory.FieldPair.NonUnit R 1 := by
  rintro ⟨-, h | h⟩
  · exact one_ne_zero h
  · exact h (by rw [inv_one]; exact R.one_mem)


set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldPair.Dominates.trans {M : Type} [Field M] {ρ : K →+* L} {σ : L →+* M}
    {O : Subring K} {B : Subring L} {C : Subring M} (h : _root_.GlobalTheory.FieldPair.Dominates ρ B O)
    (h' : _root_.GlobalTheory.FieldPair.Dominates σ C B) :
    _root_.GlobalTheory.FieldPair.Dominates (σ.comp ρ) C O := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  obtain ⟨h3, h4⟩ := h' (ρ f) h1
  exact ⟨h3, fun hn => h4 (h2 hn)⟩


set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldPair.ratRes_self : _root_.GlobalTheory.FieldPair.RatRes (RingHom.id k) ⊤ := by
  intro r _
  exact ⟨r, by rw [RingHom.id_apply, sub_self]; exact _root_.GlobalTheory.FieldPair.nonUnit_zero ⊤⟩

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspRep.ParLawsT

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

def locRecT (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) : IrrGL (k := w.adicCompletion E) → WD h :=
  (hT E Ω A w h).choose

theorem isRecT_locRecT (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) :
    UpperTheory.Zero.LLC.IsRecT h (locRecT hT h) :=
  (hT E Ω A w h).choose_spec

variable [_root_.NumberField.IsTotallyComplex E]

def locParT (hT : UpperTheory.Zero.LLC.RecTExists) (π : CG E a) (h : IsPlaceOver A w) : WD h :=
  locRecT hT h ⟨a, ParLaws.toCl (π.loc w)⟩

end GlobalTheory.CuspRep.ParLawsT

namespace GlobalTheory.CuspRep.ParLawsT

open Formalism.BasicNotions

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

def locGT (hT : UpperTheory.Zero.LLC.RecTExists) (pl : Formalism.GaloisCohomology.Places H.E Ω) {a : ℕ} (π : HostCGu H a) (w : PlE H) :
    WD (pl.2 w) :=
  haveI := host_isCMField H; locParT hT π.1 (pl.2 w)

end GlobalTheory.CuspRep.ParLawsT

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
noncomputable section

namespace GlobalTheory.DefPt

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames
  GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev Mats (Dw : Datum H) (S : Type) : Type := ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S

def part (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℕ := fun τ i => a (τ, i)

def Reads (Z : Comp Xo c) (y₀ : FrPt Xo c c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : TIdx (part Dw a) → c.F) (f : Rul Xo c) :
    Prop :=
  f ∈ suppOn Z ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (s : S),
    (∀ τ, IsUnit (Y τ).det) → IsUnit s → FrMap (Algebra.ofId c.F S) y₀ z → FrChg (fun τ => (Y τ)ᵀ) s z y →
      evR Xo c f y = s ^ n * tval (part Dw a) (fun I => algebraMap c.F S (x I)) Y

def LocFr (y₀ : FrPt Xo c c.F) (w : HeightOneSpectrum (𝓞 c.F)) (a : c.F) (B : Mats Dw c.F) : Prop :=
  a ≠ 0 ∧ (∀ τ, (B τ).det ≠ 0) ∧
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa w T.V io e → letI := io.toAlgebra
      ∀ y z : FrPt Xo c T.Fr, Integral T io y → FrMap (Algebra.ofId c.F T.Fr) y₀ z → y.x = z.x →
        ∃ (Y : Mats Dw T.V) (u : T.Vˣ), (∀ τ, IsUnit (Y τ).det) ∧
          FrChg (fun τ => ((B τ).map io * (Y τ).map (algebraMap T.V T.Fr))ᵀ) (io a * algebraMap T.V T.Fr u) z y

def ArchFr (y₀ : FrPt Xo c c.F) (σ : c.F →+* ℂ) (N : ℝ) (X : Mats Dw ℂ) : Prop :=
  0 < N ∧ (∀ τ, (X τ).det ≠ 0) ∧
    ∀ z y : FrPt Xo c (CAt σ), FrMap (Algebra.ofId c.F (CAt σ)) y₀ z → FrChg (S := CAt σ) (fun τ => (X τ)ᵀ) 1 z y →
      GlobalTheory.LamT.IsMetric y N fun _ => 1

structure PtData (Z : Comp Xo c) : Type where

  y₀ : FrPt Xo c c.F
  on : LiesOn Z y₀
  only : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x

  a : HeightOneSpectrum (𝓞 c.F) → c.F

  B : HeightOneSpectrum (𝓞 c.F) → Mats Dw c.F
  loc : ∀ w, LocFr y₀ w (a w) (B w)
  fin : {w | ¬ (a w = 1 ∧ B w = 1)}.Finite

  N : (c.F →+* ℂ) → ℝ

  X : (c.F →+* ℂ) → Mats Dw ℂ
  arch : ∀ σ, ArchFr y₀ σ (N σ) (X σ)

namespace PtData

variable {Z : Comp Xo c} (P : PtData Z)

def degLie (τ : E →+* ℂ) : ℝ := detDeg (fun w => P.B w τ) fun σ => P.X σ τ

def degTh : ℝ := lineDeg (fun σ => (Real.sqrt (P.N σ))⁻¹) fun w => (vAdd w (P.a w) : ℝ)

def matA (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (w : HeightOneSpectrum (𝓞 c.F)) :
    Matrix (TIdx (part Dw a)) (TIdx (part Dw a)) c.F := fibA (part Dw a) (P.a w ^ n) (P.B w)

def matY (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (σ : c.F →+* ℂ) :
    Matrix (TIdx (part Dw a)) (TIdx (part Dw a)) ℂ := fibY (part Dw a) ((Real.sqrt (P.N σ))⁻¹ ^ n) (P.X σ)

end PtData

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ)

def FibreAt (Z : Comp Xo c) (G : WTZ E) (s : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (_ : Nonempty ι) (L : Submodule (𝓞 c.F) (ι → c.F))
    (Y : (c.F →+* ℂ) → Matrix ι ι ℂ) (φ : (ι → c.F) →ₗ[c.F] Rul Xo c),
    Submodule.IsFullLattice c.F L ∧ (∀ σ, (Y σ).det ≠ 0) ∧ s ≤ slope_sq (matNorm Y) L / 2 ∧ Function.Injective φ ∧
    LinearMap.range φ = cuspOn U Z G ∧ (∀ x ∈ L, ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (φ x)) ∧
    ∀ σ x, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) ξ G (φ x) z ≤ matNorm Y σ x

def defBound (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ) : ℝ :=
  (∑ τ : Psi H, (((size (part Dw a τ.1) : ℝ) / Dw.p + (n : ℝ) / 2) * c₁ - Real.log (dim (part Dw a τ.1)) / 2)) +
    (n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)

structure DefCase : Prop where
  q : Dw.q = 0
  p : 1 ≤ Dw.p
  good : ∀ p : ℕ, p.Prime → l.GoodAt p
  A : l.A = 1
  geo : FnAlgClosed (Xo := Xo) (c := c)
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  xi : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ


variable (Xo c) in
def FreePt {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) : Prop :=
  ∀ (g : G) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), levR (lev g) y y' → y'.x = y.x → g = 1

end Point

section Eigen

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ)


set_option synthInstance.maxHeartbeats 400000 in
def eigSub : Submodule c.F (Rul Xo c) :=
  ⨅ g : G, LinearMap.ker (actLev (Xo := Xo) c lev g - ((χ g : (c.F)ˣ) : c.F) • (LinearMap.id : Rul Xo c →ₗ[c.F] Rul Xo c))

set_option synthInstance.maxHeartbeats 100000 in
def eigLat (W : WTZ D.host.E) : Submodule (𝓞 c.F) (cuspW Xo c U W) :=
  latW U W ⊓ ((eigSub lev χ).comap (cuspW Xo c U W).subtype).restrictScalars (𝓞 c.F)

end Eigen

end GlobalTheory.DefPt

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWLit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]


variable (F κ) in
def IsTamagawa [MeasurableSpace (κ → AF F)] (μ : Measure (κ → AF F)) : Prop :=
  μ.IsAddHaarMeasure ∧ ∃ 𝓕 : Set (κ → AF F), μ 𝓕 = 1 ∧
    IsAddFundamentalDomain (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ).range 𝓕 μ

end GlobalTheory.SWLit

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField

namespace GlobalTheory.IwLevel

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}}

def htAct {s : S ⟶ Sp R} (o : Obj b N s) : Out.RingAct o.A D.O :=
  ⟨o.act.act, o.act.hom, o.act.one, o.act.mul, o.act.add⟩

@[simp] theorem htAct_act {s : S ⟶ Sp R} (o : Obj b N s) (c : D.O) : (htAct o).act c = o.act.act c := rfl

abbrev HTIw {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) : Type 1 :=
  Chain (htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) (Ideal.absNorm w ^ D.m) D.n

section Basic₂

end Basic₂

end GlobalTheory.IwLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair

variable {k K : Type} [Field k] [Field K]

def AdjKlt (c : k →+* K) (n : ℕ) (T : Subring K) (S : Place c) (η : Forms c n) (φ : K →₀ ℚ) :
    Prop :=
  η ≠ 0 ∧ φ 0 = 0 ∧
  ∀ (Q : Subring K) (hQ : IsLocModel c Q) (t u : Q) (E : Place c), T ≤ Q →
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
    S.IsPrimeOf Q → E.IsPrimeOf Q → S.ord (t : K) = 1 → E.ord (u : K) = 1 →
    (∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring → P.disc η φ = 0) →
    -1 < E.disc η φ

namespace AdjKlt

variable {c : k →+* K} {n : ℕ} {T T' : Subring K} {S : Place c} {η : Forms c n} {φ : K →₀ ℚ}

theorem form_ne_zero (h : AdjKlt c n T S η φ) : η ≠ 0 := h.1

theorem apply_zero (h : AdjKlt c n T S η φ) : φ 0 = 0 := h.2.1

theorem mono (h : AdjKlt c n T S η φ) (hT : T ≤ T') : AdjKlt c n T' S η φ :=
  ⟨h.1, h.2.1, fun Q hQ t u E hQ' => h.2.2 Q hQ t u E (hT.trans hQ')⟩

def incl {Q : Subring K} {P : Place c} (h : P.Contains Q) : Q →+* P.ring :=
  Q.subtype.codRestrict P.ring fun q => h q q.2

theorem mem_maximalIdeal_iff (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0) :
    b ∈ IsLocalRing.maximalIdeal P.ring ↔ P.ord (b : K) ≠ 0 := by
  refine ⟨fun h h0 => h ?_, fun h hu => h (P.ord_eq_zero hu)⟩
  have h1 : (b : K)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h0]; rfl)
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))

theorem neighbour_ne {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q} {S E : Place c}
    (hm : Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q))
    (hd : ringKrullDim Q = 2) (hS : S.IsPrimeOf Q) (ht : S.ord (t : K) = 1)
    (hu : E.ord (u : K) = 1) : E ≠ S := by
  rintro rfl
  haveI := hQ.isLocalRing
  have h0 : E.ord (0 : K) = 0 := by simp [Place.ord]
  have hle : IsLocalRing.maximalIdeal Q ≤
      (IsLocalRing.maximalIdeal E.ring).comap (incl hS.1) := by
    rw [← hm, Ideal.span_le]
    rintro _ (h | h) <;> rw [h]
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (t : K) = 0 at h; rw [h, h0] at ht; omega).2 (by change E.ord (t : K) ≠ 0; omega)
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (u : K) = 0 at h; rw [h, h0] at hu; omega).2 (by change E.ord (u : K) ≠ 0; omega)
  have hb : Function.Bijective (incl hS.1) := by
    refine ⟨fun a b e => Subtype.ext (congrArg (fun z : E.ring => (z : K)) e), fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f f.2
    have hu : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact (mem_maximalIdeal_iff E _ hb0).1 (hle hn) hbo
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    refine ⟨⟨a, ha⟩ * g, Subtype.ext ?_⟩
    change a * (g : K) = f
    rw [← e, mul_assoc, hg', mul_one]
  have := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)
  rw [hd, IsPrincipalIdealRing.ringKrullDim_eq_one _ (IsDiscreteValuationRing.not_isField _)] at this
  exact absurd this (by decide)

end AdjKlt

variable {c : k →+* K} {n : ℕ} {T : Subring K} {η : Forms c n} {φ : K →₀ ℚ}

theorem adjKlt_of_lt_disc (S : Place c) (hη : η ≠ 0) (hφ : φ 0 = 0)
    (h : ∀ E : Place c, E.Contains T → E.ring ≠ S.ring → -1 < E.disc η φ) :
    AdjKlt c n T S η φ :=
  ⟨hη, hφ, fun _ hQ _ _ E hT hm hd hS hE ht hu _ =>
    h E (hE.1.mono hT) fun e => AdjKlt.neighbour_ne hQ hm hd hS ht hu (Place.ext e)⟩

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP OmP dMode)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ}

def PolyOnK (ε : Fin n → Bool) (f : Mat n → ℂ) : Prop := ∃ P : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, f k = ev k P

def trK {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : Mat n → (W →L[ℂ] W)) (k : Mat n) : ℂ :=
  LinearMap.trace ℂ W (T k : W →ₗ[ℂ] W)

def IsKIrr (ε : Fin n → Bool) (γ : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (T : Mat n → (W →L[ℂ] W)) : Prop :=
  Nontrivial W ∧ Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T ∧ Formalism.MainNotions.S.IsKTypeOf ε T γ ⊤

abbrev dD (ε : Fin n → Bool) {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    Module.End ℂ (TensorProduct ℂ M (Fock n)) := dOp ε (eT E) cpT + dOp' ε (eT E) cmT

abbrev tor (θ : Fin n → ℝ) : Fin n → ℂ := fun a => Complex.exp (θ a * Complex.I)

def BlockForm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : Poly n), ∃ (M : ℕ) (Q : Poly n), Q ∈ blockAlg ε ∧
    ∀ k ∈ Formalism.REAL.Kset ε, ev k P = ev k (detbP n ^ M * Q)

def CoefPoly : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
    ∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ

def TrPoly : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)), (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) → PolyOnK ε fun k => conj (trK T k)

def AvgMap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)) (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]
    (S : Mat n → (Z →L[ℂ] Z)) (Γ : Z →ₗ[ℂ] Z), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S →
    ∫ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) ∂(muK ε) ≠ 0 →
    ∃ Φ : W →ₗ[ℂ] Z, Φ ≠ 0 ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, Φ (T k v) = S k (Φ v)

def SchurOne : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
    ∫ k : KG ε, conj (trK T (toMK k)) * trK T (toMK k) ∂(muK ε) = 1

def SumTypes : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S →
    Formalism.MainNotions.S.IsKStableOn ε σ S → S ≤ sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'}

def PolyAvg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat n → (H →L[ℂ] H)),
      IsURepOn (UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧
        (∀ P : Poly n, P.totalDegree ≤ d → ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ S) ∧
        ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A

def DatumEquiv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StdGap ε lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat n → (H →L[ℂ] H)),
    IsURepOn (UJset ε) σ → Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ V : Submodule ℂ (smD ε σ), IsKIrrHW ε (smE ε σ) (lowK ε lam) V → V ≠ ⊥ →
    (∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v) →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Mat n → (X →L[ℂ] X)), Formalism.MainNotions.S.IsDS ε lam D →
    ∃ U : H ≃ₗᵢ[ℂ] X, ∀ g ∈ UJset ε, ∀ x, U (σ g x) = D g (U x)

def MatRep : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)),
    IsUnitaryRep π → IsTopIrreducible π → ∃ σ : Mat n → (U →L[ℂ] U), IsURepOn (UJset ε) σ ∧
      Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ ∧ ∀ g : UJ ε, σ (toM g) = π g

end GlobalTheory.PsCo.PcEF
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt.Test

open MvPolynomial NumberField IsDedekindDomain Module Filter GlobalTheory.ChowHt GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal


set_option autoImplicit false in
theorem _root_.GlobalTheory.CompHt.Test.imageDeg_zero {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [Field Ω] [Algebra K Ω] (D : ℕ) :
    _root_.GlobalTheory.CompHt.imageDeg (0 : V →ₗ[K] Ω) D = 0 := by
  by_contra hne
  obtain ⟨N, b, f, hf⟩ := (_root_.GlobalTheory.CompHt.imageDeg_pos_iff _ D).1 (Nat.pos_of_ne_zero hne)
  obtain ⟨y, hy, hI⟩ := hf.exists_point
  apply hy
  funext i
  have hX : (X i : MvPolynomial (Fin N) K) ∈ _root_.GlobalTheory.CompHt.imageIdeal (0 : V →ₗ[K] Ω) b := by
    unfold _root_.GlobalTheory.CompHt.imageIdeal
    rw [_root_.GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous _ (isHomogeneous_X K i)]
    simp
  simpa using hI _ hX

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

end GlobalTheory.CompHt.Test
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegCmp

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal

section Generic

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def hilb (ev : V →ₗ[K] Ω) (τ : ℕ) : ℕ∞ :=
  Cardinal.toENat (Module.rank K (↥((LinearMap.range ev) ^ τ : Submodule K Ω)))

def coneAlg (ev : V →ₗ[K] Ω) : Subalgebra K (Polynomial Ω) :=
  Algebra.adjoin K (Set.range fun v => Polynomial.X * Polynomial.C (ev v))

def IsIntDeg (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  IsIntegral (coneAlg ev) (Polynomial.X ^ τ * Polynomial.C t : Polynomial Ω)

def IsRatio (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  ∃ (e : ℕ) (h : Ω), h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω) ∧ h ≠ 0 ∧
    t * h ∈ ((LinearMap.range ev) ^ (τ + e) : Submodule K Ω)

end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

def UnfAll : Prop := ∀ σ, GoodEmb c σ → IsUnf (U σ)

def Proport : Prop :=
  ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (la τ)) →
    growthOn U Z (wtOf Dw la 0) = ENNReal.ofReal (topDeg U Z la)

def EqVolume : Prop := ∀ Z Z' : Comp Xo c, vZero U Z = vZero U Z'

set_option synthInstance.maxHeartbeats 100000 in
def RatioOn (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ (τ : ℕ), ∀ t ∈ cuspOn U Z (τ • G), IsRatio (genPoint Z (cuspOn U Z G)) τ (genVal Z t)

end GlobalTheory.DegCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsLocCompIffEquiv
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def SoleTerm {ι : Type} (C : ι → ℂ) (p q : ι → Prop) : Prop :=
  ∃ i, C i ≠ 0 ∧ p i ∧ ∀ i', C i' ≠ 0 → q i' → i' = i

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isLocComp_iff_equiv {ρc : CuspSub E n} {w : Pl E} {σ : SmIrr (GLw n w)} (h : ρc.IsLocComp w σ)
    (τ : SmIrr (GLw n w)) : ρc.IsLocComp w τ ↔ Nonempty (τ.ρ.Equiv σ.ρ) :=
  ⟨fun h' => GlobalTheory.CuspRep.LocUniq.isLocComp_unique ρc w τ σ h' h,
    fun ⟨e⟩ => h.congr ((CuspSub.setoid E n).iseqv.refl ρc) ⟨e.symm⟩⟩

end GlobalTheory.BCT
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
noncomputable section

namespace GlobalTheory.UPel.Sm.Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

section Univ
variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}

end Univ

section KS
variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]
  {ρ : O →+* Module.End k H} {φ : LinearMap.BilinForm k H} {Fil Z : Submodule k H}

def ksSub (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) :
    Submodule k (H →ₗ[k] H) where
  carrier := {f | IsKS ρ φ Fil Z f}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' {f g} hf hg := ⟨fun a x hx => by
      convert add_mem (hf.1 a x hx) (hg.1 a x hx) using 1
      simp only [LinearMap.add_apply, map_add (f := _)]; abel,
    fun x hx => add_mem (hf.2.1 x hx) (hg.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      have h2 := hg.2.2 x hx y hy
      simp only [LinearMap.add_apply, map_add (f := _)]
      linear_combination h1 + h2⟩
  smul_mem' c f hf := ⟨fun a x hx => by
      convert Fil.smul_mem c (hf.1 a x hx) using 1
      simp only [LinearMap.smul_apply, map_smul, smul_sub],
    fun x hx => Fil.smul_mem c (hf.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
      linear_combination c * h1⟩

def cls (Fil : Submodule k H) : (H →ₗ[k] H) →ₗ[k] (Fil →ₗ[k] H ⧸ Fil) where
  toFun f := Fil.mkQ ∘ₗ f ∘ₗ Fil.subtype
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

theorem cls_eq_iff (f g : H →ₗ[k] H) : cls Fil f = cls Fil g ↔ ∀ x ∈ Fil, f x - g x ∈ Fil := by
  simp [cls, LinearMap.ext_iff, Submodule.Quotient.eq]

theorem KSDim.rank_eq {d : ℕ} (h : KSDim ρ φ Fil Z d) :
    Module.rank k ((ksSub ρ φ Fil Z).map (cls Fil)) = d := by
  obtain ⟨f, hf, hu⟩ := h
  have key : ∀ (g : H →ₗ[k] H) (c : Fin d → k), (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
      cls Fil g = ∑ i, c i • cls Fil (f i) := fun g c => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  have li : LinearIndependent k fun i => cls Fil (f i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨c₀, -, h₀⟩ := hu 0 (ksSub ρ φ Fil Z).zero_mem
    have := (h₀ c ((key 0 c).2 (by rw [hc, map_zero]))).trans (h₀ 0 ((key 0 0).2 (by simp))).symm
    exact congrFun this
  have : (ksSub ρ φ Fil Z).map (cls Fil) = Submodule.span k (Set.range fun i => cls Fil (f i)) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc, -⟩ := hu g hg
      rw [(key g c).1 hc]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨f i, hf i, rfl⟩
  rw [this, rank_span li, ← Cardinal.lift_inj.{_, 0}, Cardinal.mk_range_eq_of_injective li.injective]
  simp

theorem KSDim.unique {d e : ℕ} (h : KSDim ρ φ Fil Z d) (h' : KSDim ρ φ Fil Z e) : d = e := by
  exact_mod_cast (KSDim.rank_eq h).symm.trans (KSDim.rank_eq h')

end KS

section Examples
variable (k : Type) [Field k]

end Examples

end GlobalTheory.UPel.Sm.Model
end
end
