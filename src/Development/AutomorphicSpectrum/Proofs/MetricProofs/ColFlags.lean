module

public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorIJConjTranspose
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricGrassmannChartLocal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar.FlagBun

section Pure

variable (Ψ : Type) (p q : ℕ)

abbrev rk : Ψ ⊕ Ψ → ℕ := Sum.elim (fun _ => p) (fun _ => q)

abbrev StepIx : Type := Σ s : Ψ ⊕ Ψ, Fin (rk Ψ p q s)

def stepOf (r : Ψ × Fin (p + q)) : StepIx Ψ p q :=
  if h : (r.2 : ℕ) < p then ⟨.inl r.1, ⟨r.2, h⟩⟩
  else ⟨.inr r.1, ⟨r.2 - p, by have := r.2.2; show _ < q; omega⟩⟩

variable {Ψ p q}

def idx {K₀ : Type} (J₀ : K₀ → Type) (n : Ψ ⊕ Ψ → ℕ) : K₀ ⊕ StepIx Ψ p q → Type :=
  Sum.elim J₀ fun t => Fin ((t.2 : ℕ) + 1) → Fin (n t.1)

instance {K₀ : Type} (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (n : Ψ ⊕ Ψ → ℕ) (k : K₀ ⊕ StepIx Ψ p q) :
    Fintype (idx J₀ n k) := by
  rcases k with k | t
  · exact inferInstanceAs (Fintype (J₀ k))
  · exact inferInstanceAs (Fintype (Fin ((t.2 : ℕ) + 1) → Fin (n t.1)))


open Classical in
def blkF (Ψ : Type) (p q : ℕ) (K₀ : Type) (r : Ψ × Fin (p + q)) : Option (K₀ ⊕ StepIx Ψ p q) :=
  if IsProperStep (p + q) p r.2 then some (.inr (stepOf Ψ p q r)) else none

variable (Ω : Type) [Field Ω]


variable (p q) in
def gMat (τ : Ψ) : Matrix (Fin (p + q)) (Fin (p + q)) (GenField Ω (rk Ψ p q)) :=
  (Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ)) 0 0 (genU Ω (rk Ψ p q) (.inl τ))).submatrix
    (blockEquiv p q).symm (blockEquiv p q).symm

variable {Ω}
variable {n : Ψ ⊕ Ψ → ℕ} (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)

def fMat (s : Ψ ⊕ Ψ) : Matrix (Fin (n s)) (Fin (rk Ψ p q s)) (GenField Ω (rk Ψ p q)) :=
  (A s).map (algebraMap Ω (GenField Ω (rk Ψ p q))) * genU Ω (rk Ψ p q) s

variable {K₀ : Type} {J₀ : K₀ → Type} (x₀ : (Σ k, J₀ k) → Ω)

def yv : (Σ k, idx (p := p) (q := q) J₀ n k) → GenField Ω (rk Ψ p q)
  | ⟨.inl k, i⟩ => algebraMap Ω _ (x₀ ⟨k, i⟩)
  | ⟨.inr t, J⟩ => ((fMat A t.1).submatrix J (Fin.castLE t.2.2)).det

def xv : (Σ k, idx (p := p) (q := q) J₀ n k) → Ω
  | ⟨.inl k, i⟩ => x₀ ⟨k, i⟩
  | ⟨.inr t, J⟩ => ((A t.1).submatrix J (Fin.castLE t.2.2)).det

variable [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)]

def xb : (Σ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k) → Ω :=
  fun r => xv A x₀ ⟨r.1.1, r.2⟩


variable (p q) in
def posOf : ∀ s : Ψ ⊕ Ψ, Fin (rk Ψ p q s) → Fin (p + q)
  | .inl _ => wEmb p q
  | .inr _ => omEmb p q


open Classical in
def aExt (s : Ψ ⊕ Ψ) : Matrix (Fin (n s)) (Fin (p + q)) Ω :=
  fun j a => ∑ l, if posOf p q s l = a then A s j l else 0

def coefF : (Σ k, idx (p := p) (q := q) J₀ n k) → Finset (Fin (p + q)) → Ω
  | ⟨.inl _, _⟩, _ => 0
  | ⟨.inr t, J⟩, I => if e : I.card = (t.2 : ℕ) + 1 then ((aExt A t.1).submatrix J (I.orderEmbOfFin e)).det else 0

def rkW (i : Fin (p + q)) : ℕ := min ((i : ℕ) + 1) p

def rkO (i : Fin (p + q)) : ℕ := (i : ℕ) + 1 - min ((i : ℕ) + 1) p


open Classical in
def twist (m : Ψ ⊕ Ψ → ℕ) (r : Ψ × Fin (p + q)) : K₀ ⊕ StepIx Ψ p q → ℤ
  | .inl _ => (rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1) : ℕ)
  | .inr t =>
    -((if t.1 = .inl r.1 ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (r.2 : ℕ) + 1 then 1 else 0) +
      (if t.1 = .inr r.1 ∧ (t.2 : ℕ) + 1 = q ∧ (r.2 : ℕ) + 1 = p + q then 1 else 0))

end Pure

section Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}

abbrev EE (A : HodgeCpt Y S x) : Type := A.Li × ∀ τ : CMType H, Module.Dual Ω (A.Vgen (.inr τ))

def inW (A : HodgeCpt Y S x) : A.Li →ₗ[Ω] EE A := LinearMap.inl Ω _ _


open Classical in
def inO (A : HodgeCpt Y S x) (τ : CMType H) : Module.Dual Ω (A.Vgen (.inr τ)) →ₗ[Ω] EE A :=
  (LinearMap.inr Ω _ _).comp (LinearMap.single Ω (fun τ : CMType H => Module.Dual Ω (A.Vgen (.inr τ))) τ)

def LL (A : HodgeCpt Y S x) : CMType H ⊕ CMType H → Lat A.ξ (EE A)
  | .inl τ => (A.V (.inl τ)).map (inW A)
  | .inr τ => (omBundle A τ).map (inO A τ)

def VV (A : HodgeCpt Y S x) : CMType H ⊕ CMType H → Submodule Ω (EE A)
  | .inl τ => (A.Vgen (.inl τ)).map (inW A)
  | .inr τ => (⊤ : Submodule Ω _).map (inO A τ)

def cc (A : HodgeCpt Y S x) (bW : WBases A) (bO : OmBases A) :
    ∀ s : CMType H ⊕ CMType H, Fin (rk (CMType H) D.p D.q s) → EE A
  | .inl τ => fun a => inW A (bW τ a)
  | .inr τ => fun a => inO A τ (bO τ a)

def aOf (A : HodgeCpt Y S x) (bW : WBases A) (bO : OmBases A) {n : CMType H ⊕ CMType H → ℕ}
    (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE A)) (s : CMType H ⊕ CMType H) :
    Matrix (Fin (n s)) (Fin (rk (CMType H) D.p D.q s)) Ω :=
  Matrix.of fun j a => φ s j (cc A bW bO s a)

abbrev seg {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] (x : (Σ k, J k) → Ω) : ((k : K) → J k) → Ω :=
  fun c' => ∏ k, x ⟨k, c' k⟩

def reTie (A : HodgeCpt Y S x) {K' : Type} [Fintype K'] {J' : K' → Type} (x' : (Σ k, J' k) → Ω)
    (h : CoordTie ℤ A.ξ (seg x')) : HodgeCpt Y S x' :=
  { A with tie := h }

end Bundles

section Model

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)

def bF (r : Ψ × Fin (p + q)) (k : NonPluckerBlocks (blkF Ψ p q K₀)) : ℤ := twist m r k.1

def FramesOK : Prop :=
  ∀ Q : Ideal (MRing (baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀))), Q.IsPrime → IsRelevant Q →
    mCoordIdeal (xb A x₀) ≤ Q →
    ∃ F : FrameData (idx (p := p) (q := q) J₀ n) Ψ (p + q) Ω (blkF Ψ p q K₀),
      ((∀ τ, IsBlockDiag p (F.T τ) ∧ (F.T τ).det ≠ 0) ∧
      (∀ r k, blkF Ψ p q K₀ r = some k → ∀ (i : idx J₀ n k) (h : Matrix (Fin (p + q)) (Fin (p + q)) Ω),
        IsBlockDiag p h →
        detFac p r.2 (F.T r.1) * ∑ I, coefF A ⟨k, i⟩ I * minorIJ (F.T r.1 * h) I (stepCols (p + q) p r.2) =
          (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') * ∑ I, F.u ⟨k, i⟩ I * minorIJ h I (stepCols (p + q) p r.2)) ∧
      (∀ r k, blkF Ψ p q K₀ r = some k → ∀ I I', IsStepRows (p + q) p r.2 I → IsStepRows (p + q) p r.2 I' →
        ∑ i : idx J₀ n k, F.u' I ⟨k, i⟩ * F.u ⟨k, i⟩ I' = if I = I' then 1 else 0) ∧
      ∀ r, blkF Ψ p q K₀ r = none →
        detFac p r.2 (F.T r.1) * 1 = (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') * F.υ r) ∧
      ((∀ k, (MvPolynomial.X ⟨k, F.c k⟩ : MRing (baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀))) ∉ Q) ∧
        (∀ r I, RegAt (xb A x₀) Q (F.u r I) ∧ RegAt (xb A x₀) Q (F.u' I r)) ∧
        ∀ r, blkF Ψ p q K₀ r = none → F.υ r ≠ 0 ∧ RegAt (xb A x₀) Q (F.υ r) ∧ RegAt (xb A x₀) Q (F.υ r)⁻¹)

def ModelOK : Prop :=
  (∀ r, blkF Ψ p q K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
  (∀ r r' k, blkF Ψ p q K₀ r = some k → blkF Ψ p q K₀ r' = some k → r = r') ∧
  (∀ k, ∃ i, xb A x₀ ⟨k, i⟩ ≠ 0) ∧
  (∀ r, basePart (blkF Ψ p q K₀) (yv A x₀) r = algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r)) ∧
  (∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ)) ∧
  IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) ∧
  (∀ r k, blkF Ψ p q K₀ r = some k → ∀ i : idx J₀ n k,
    yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) *
      minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2)) ∧
  FramesOK A x₀ m

def model [CharZero Ω] (h : ModelOK A x₀ m) : FlagModel (yv (p := p) (q := q) A x₀) Ψ (p + q) p where
  j_le := Nat.le_add_right _ _
  Ω := Ω
  blk := blkF Ψ p q K₀
  blk_none := h.1
  blk_inj := h.2.1
  x := xb A x₀
  x_ne := h.2.2.1
  y_base := h.2.2.2.1
  g := gMat p q Ω
  g_block := h.2.2.2.2.1
  g_indep := h.2.2.2.2.2.1
  coef := coefF A
  y_step := h.2.2.2.2.2.2.1
  b := bF m
  lam := fun _ => 1
  frames := h.2.2.2.2.2.2.2

end Model

section Forms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}

def FormsOK (A : HodgeCpt Y S x) (bW : WBases A) (bO : OmBases A) {n : CMType H ⊕ CMType H → ℕ}
    (m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE A)) : Prop :=
  (∀ s, (LL A s).IsVB (rk (CMType H) D.p D.q s) (VV A s)) ∧
  (∀ s, LinearIndependent Ω (cc A bW bO s) ∧ Submodule.span Ω (Set.range (cc A bW bO s)) = VV A s) ∧
  (∀ s, IsTwistGen A.ξ (seg x) (LL A s) (m s) (φ s)) ∧
  ∀ s, ∃ B : Matrix (Fin (rk (CMType H) D.p D.q s)) (Fin (n s)) Ω, B * aOf A bW bO φ s = 1

variable {K' : Type} [Fintype K'] {J' : K' → Type}
  {y : (Σ k, J' k) → GenField Ω (rk (CMType H) D.p D.q)}

def ColFlags (A : HodgeCpt Y S x) (bW : WBases A) (bO : OmBases A) {A' : HodgeCpt Y S y} (j : A.Li →+ A'.Li)
    (Fl : A'.Flag) : Prop :=
  (∀ τ (k : Fin D.p), Fl.b (.inl τ) k = colFrame (fun a => j (bW τ a)) (wBlock (gMat D.p D.q Ω τ)) k) ∧
    ∀ τ (v : Fin D.q → A.Vgen (.inr τ)), (∀ a b, bO τ a (v b) = if a = b then 1 else 0) →
      ∀ k : Fin D.q, Fl.b (.inr τ) k = colFrame (fun a => j (v a)) (omBlock (gMat D.p D.q Ω τ))ᵀ⁻¹ k.rev

end Forms

end GlobalTheory.CompanionTheory.Ar.PB.FMX
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (i : Fin N)
    (q : Σ k, ι k) (h : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ I, valAt M.x (F.u q I) b * minorIJ h I (stepCols N j i)

def stepCoord {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ)
    (p : Ψ × Fin N) (k' : K') (q : Σ k, ι k) : ℂ :=
  ∑ I, valAt M.x (F.u q I) (basePart M'.blk z ∘ Cv.v) *
    ∑ I', if IsStepRows N j p.2 I' then minorIJ (Cv.trans F' F (basePart M'.blk z) p.1) I I' *
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ else 0

def img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ) :
    (Σ k, ι k) → ℂ := fun q =>
  if hk : ∀ p, M.blk p ≠ some q.1 then basePart M'.blk z (Cv.v ⟨⟨q.1, hk⟩, q.2⟩)
  else
    have hp : ∃ p, M.blk p = some q.1 := by simpa using hk
    match M'.blk hp.choose with
    | none => 0
    | some k' => stepCoord Cv F' F z hp.choose k' q

theorem img_base {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ) :
    basePart M.blk (img Cv F' F z) = basePart M'.blk z ∘ Cv.v := by
  funext q
  obtain ⟨⟨k, hk⟩, m⟩ := q
  simp only [basePart, img, Function.comp]
  rw [dite_eq_left hk]

theorem img_step {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ)
    {p : Ψ × Fin N} {k : K} {k' : K'} (hp : M.blk p = some k) (hp' : M'.blk p = some k') (m : ι k) :
    img Cv F' F z ⟨k, m⟩ = stepCoord Cv F' F z p k' ⟨k, m⟩ := by
  have hk : ¬ ∀ p', M.blk p' ≠ some k := fun h => h p hp
  have hex : ∃ p', M.blk p' = some k := ⟨p, hp⟩
  have hch : hex.choose = p := M.blk_inj _ _ k hex.choose_spec hp
  simp only [img, dif_neg hk]
  split
  · next h =>
    rw [hch, hp'] at h
    exact absurd h (by simp)
  · next k'' h =>
    rw [hch, hp'] at h
    cases h
    rw [hch]

theorem exists_blk_cover {M : FlagModel y Ψ N j} (M' : FlagModel y' Ψ N j) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) : ∃ k', M'.blk p = some k' := by
  have h1 : ¬ (M.blk p = none) := by
    rw [hp]
    simp
  rw [M.blk_none] at h1
  have h2 : M'.blk p ≠ none := by
    rw [Ne, M'.blk_none]
    exact h1
  exact Option.ne_none_iff_exists'.mp h2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mCoordIdeal_le_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    mCoordIdeal z' ≤ mCoordIdeal z := by
  obtain ⟨c, hc, rfl⟩ := h
  let θ : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ := aeval fun k => C (c k) * X k
  have key : ∀ f : MRing ι, mConeMap (fun p => c p.1 * z' p) f = θ (mConeMap z' f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp]
      congr 1
      simp [mConeMap, θ, mul_assoc, mul_left_comm]
  intro f hf
  have hf' : mConeMap z' f = 0 := hf
  show mConeMap _ f = 0
  rw [key, hf', map_zero]

theorem mCoordIdeal_eq_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    mCoordIdeal z = mCoordIdeal z' :=
  le_antisymm (mCoordIdeal_le_of_sameOrbit (Cj.sameOrbit_symm h)) (mCoordIdeal_le_of_sameOrbit h)

theorem coord_ne_of_X_notMem {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) :
    z q ≠ 0 := fun e => h (by
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, e, map_zero, zero_mul])

end Orbit

section Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem comp_mem_mcPts {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) (φ : Ω →+* Ω')
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (hx : ∀ q, x' (v q) = φ (x q))
    {zb : (Σ k, ι' k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal x')) : zb ∘ v ∈ mcPts (mCoordIdeal x) := by
  have key : ∀ f : MRing ι, mConeMap x' (rename v f) = rename κ (map φ (mConeMap x f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, hx, hv.2.2.1 i]
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    obtain ⟨k₁, i₁⟩ := p
    have e : k₁ = k := hv.1 (by rw [← hv.2.2.1 ⟨k₁, i₁⟩, hp])
    subst e
    exact ⟨i₁, by simpa [Function.comp, hp] using hi⟩
  · have hf' : mConeMap x f = 0 := hf
    have h1 : rename v f ∈ mCoordIdeal x' := by
      show mConeMap x' (rename v f) = 0
      rw [key, hf', map_zero, map_zero]
    have h2 := hz.2 _ h1
    rwa [map_rename, eval_rename] at h2

end Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

theorem sameOrbit_of_isFlagOf (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk}
    {z z' : (Σ k, ι k) → ℂ} {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hb : SameOrbit (basePart M.blk z) (basePart M.blk z')) (H : M.IsFlagOf F z h) (H' : M.IsFlagOf F z' h) :
    SameOrbit z z' := by
  have hbase : basePart M.blk z = basePart M.blk z' := by
    obtain ⟨c, -, e⟩ := hb
    have hc : ∀ k, c k = 1 := fun k => by
      have := congrFun e ⟨k, F.c k⟩
      rw [H.1 k, H'.1 k, mul_one] at this
      exact this.symm
    rw [e]
    funext p
    simp [hc]
  have blockwise : ∀ k, ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = t * z' ⟨k, m⟩ := by
    intro k
    by_cases hk : ∀ p, M.blk p ≠ some k
    · exact ⟨1, one_ne_zero, fun m => by
        simpa [basePart] using congrFun hbase ⟨⟨k, hk⟩, m⟩⟩
    · push_neg at hk
      obtain ⟨p, hp⟩ := hk
      obtain ⟨a, ha, ea⟩ := H.2.2 p k hp
      obtain ⟨a', ha', ea'⟩ := H'.2.2 p k hp
      refine ⟨a / a', div_ne_zero ha ha', fun m => ?_⟩
      rw [ea m, ea' m, hbase]
      field_simp
  choose t ht e using blockwise
  exact ⟨t, ht, funext fun p => e p.1 p.2⟩

theorem isImg_unique : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w w', CovMap.IsImg Cv z w → CovMap.IsImg Cv z w' → SameOrbit w w' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ hA' z hz w w' hw hw'
  obtain ⟨-, fr, -⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨bs', fr', fl'⟩ := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨F', hF', hG'⟩ := fr' _ (bs' z hz)
  have hne : ∀ k : NonPluckerBlocks M'.blk, basePart M'.blk z ⟨k, F'.c k⟩ ≠ 0 := fun k =>
    coord_ne_of_X_notMem (hG'.1 k)
  let c : K' → ℂ := fun k =>
    if h : ∀ p, M'.blk p ≠ some k then (basePart M'.blk z ⟨⟨k, h⟩, F'.c ⟨k, h⟩⟩)⁻¹ else 1
  have hcb : ∀ k : NonPluckerBlocks M'.blk, c k.1 = (basePart M'.blk z ⟨k, F'.c k⟩)⁻¹ := fun k => dif_pos k.2
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M'.blk p ≠ some k
    · rw [hcb ⟨k, h⟩]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z₁ : (Σ k, ι' k) → ℂ := fun p => c p.1 * z p
  have h1 : SameOrbit z₁ z := ⟨c, hc, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y') := mcPts_smul hA'.2.1.2.1 c hc hz
  have hb1 : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z) :=
    ⟨fun k => c k.1, fun k => hc k.1, rfl⟩
  have hG₁ : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by
    rw [mCoordIdeal_eq_of_sameOrbit hb1]
    exact hG'
  have hnorm : ∀ k, basePart M'.blk z₁ ⟨k, F'.c k⟩ = 1 := fun k => by
    show c k.1 * basePart M'.blk z ⟨k, F'.c k⟩ = 1
    rw [hcb k]
    exact inv_mul_cancel₀ (hne k)
  obtain ⟨h, hh⟩ := (fl' F' hF' z₁ (bs' z₁ hz₁) hG₁ hnorm).1 hz₁
  obtain ⟨F, hF, hG⟩ := fr _ (comp_mem_mcPts Cv.block Cv.φ Cv.x_eq (bs' z₁ hz₁))
  obtain ⟨z₀, a, b, e⟩ := hw z₁ h1 F' F hF' hF hG₁ hG h hh
  obtain ⟨z₀', a', b', e'⟩ := hw' z₁ h1 F' F hF' hF hG₁ hG h hh
  exact Cj.sameOrbit_trans (Cj.sameOrbit_symm a) (Cj.sameOrbit_trans
    (sameOrbit_of_isFlagOf M (Cj.sameOrbit_trans b (Cj.sameOrbit_symm b')) e e') a')

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecondStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_arithmetic_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w w', CovMap.IsImg Cv z w → CovMap.IsImg Cv z w' → SameOrbit w w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def pairV {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) : (Σ k, Sum.elim ι ι' k) → R
  | ⟨.inl k, i⟩ => a ⟨k, i⟩
  | ⟨.inr k, i⟩ => b ⟨k, i⟩

theorem pairV_inl {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) (p : Σ k, ι k) :
    pairV a b (inlV p) = a p := rfl

theorem pairV_inr {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) (p : Σ k, ι' k) :
    pairV a b (inrV p) = b p := rfl

def stepOf (M : FlagModel y Ψ N j) (k : K) (h : ¬ ∀ p, M.blk p ≠ some k) : Ψ × Fin N :=
  Classical.choose (not_forall_not.1 (by simpa using h) : ∃ p, M.blk p = some k)

theorem blk_stepOf (M : FlagModel y Ψ N j) (k : K) (h : ¬ ∀ p, M.blk p ≠ some k) :
    M.blk (stepOf M k h) = some k := by
  unfold stepOf
  exact Classical.choose_spec (p := fun p => M.blk p = some k) _

def transPt {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) : (Σ k, ι k) → Φ' := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then algebraMap M'.Ω Φ' (Cv.φ (M.x ⟨⟨q.1, h⟩, q.2⟩))
  else ∑ I, algebraMap M'.Ω Φ' (Cv.φ (M.coef q I)) *
    minorIJ (M'.g (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

theorem transPt_base {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (q : Σ k, baseIdx ι M.blk k) :
    transPt Cv ⟨q.1.1, q.2⟩ = algebraMap M'.Ω Φ' (Cv.φ (M.x q)) :=
  dif_pos q.1.2

theorem transPt_step {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (m : ι k) :
    transPt Cv ⟨k, m⟩ = ∑ I, algebraMap M'.Ω Φ' (Cv.φ (M.coef ⟨k, m⟩ I)) * minorIJ (M'.g p.1) I (stepCols N j p.2) := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun H => H p hp
  have e : stepOf M k h = p := M.blk_inj _ _ k (blk_stepOf M k h) hp
  rw [transPt, dite_eq_right h, e]

def trMat {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) : Matrix (Fin N) (Fin N) M'.Ω :=
  ((F.T τ).map Cv.φ)⁻¹ * F'.T τ

def coE {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N)
    (q : Σ k, ι k) (r : Σ k, ι' k) : M'.Ω :=
  ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
    Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBounds
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBounds
set_option maxSynthPendingDepth 1

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
open ReciprocityTheory.AnForm.M.PLAux (analyticAt_compat)

section Charts

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem analyticAt_transition (P : PotentialCharts A) (j : Fin A.n) (k : Fin P.N) {y : Fin D → ℂ}
    (hy : y ∈ (A.chart j).target) (hk : (A.chart j).symm y ∈ (P.chart k).source) :
    AnalyticAt ℂ (P.chart k ∘ (A.chart j).symm) y := by
  have h := analyticAt_compat (P.compat k) j ((A.chart j).map_target hy) hk
  rwa [(A.chart j).right_inv hy] at h

theorem levi_th_add_chart (P : PotentialCharts A) (f : X → ℝ) (x : X) (j : Fin A.n) (k : Fin P.N)
    {y : Fin D → ℂ} (w : Fin D → ℂ) (hy : y ∈ (A.chart j).target)
    (hθ : (A.chart j).symm y ∈ P.th.U x) (hk : (A.chart j).symm y ∈ (P.chart k).source)
    (hcf : ContDiffAt ℝ 2 (P.chartFun f k) (P.chart k ((A.chart j).symm y))) :
    ContDiffAt ℝ 2 ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y ∧
      levi ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y w =
        levi (P.chartFun f k) (P.chart k ((A.chart j).symm y))
          (fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w) := by
  have hg := analyticAt_transition P j k hy hk
  obtain ⟨W, hWo, hpW, G, hG, hEq⟩ := P.q_th k x _ ⟨hθ, hk⟩
  have hN : W ∩ P.th.U x ∩ (P.chart k).source ∈ 𝓝 ((A.chart j).symm y) :=
    ((hWo.inter (P.th.isOpen_U x)).inter (P.chart k).open_source).mem_nhds ⟨⟨hpW, hθ⟩, hk⟩
  have hev : (fun z => P.th.φ x z + f z) ∘ (A.chart j).symm =ᶠ[𝓝 y]
      fun y' => (P.chartFun f k ∘ (P.chart k ∘ (A.chart j).symm)) y' +
        (-1) * (G ((A.chart j).symm y')).re := by
    filter_upwards [((A.chart j).continuousAt_symm hy).preimage_mem_nhds hN] with y' hy'
    have h1 := hEq _ hy'
    simp only [Function.comp, PotentialCharts.chartFun, (P.chart k).left_inv hy'.2]
    linarith
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hpW⟩
  have hcf' : ContDiffAt ℝ 2 (P.chartFun f k) ((P.chart k ∘ (A.chart j).symm) y) := hcf
  have hcg : ContDiffAt ℝ 2 (P.chartFun f k ∘ (P.chart k ∘ (A.chart j).symm)) y :=
    hcf'.comp y ((hg.contDiffAt (n := 2)).restrict_scalars ℝ)
  have hre : ContDiffAt ℝ 2 (fun y' => (G ((A.chart j).symm y')).re) y := by
    have := (Complex.reCLM.contDiff (𝕜 := ℝ) (n := 2)).contDiffAt.comp y
      ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)
    simpa [Function.comp_def] using this
  have h0 : levi (fun y' => (G ((A.chart j).symm y')).re) y w = 0 := levi_re_analytic hGa w
  refine ⟨(hcg.add (contDiffAt_const.mul hre)).congr_of_eventuallyEq hev, ?_⟩
  rw [levi_congr hev w, levi_add_smul (-1) hcg hre w, h0, levi_comp w hg hcf']
  simp

theorem isPshOn_th_ph (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) :
    ReciprocityTheory.AnForm.P.IsPshOn A R.Yo (R.th + LocPot.ofFun R.ph) := by
  intro x j y hy w
  have hyt : y ∈ (A.chart j).target := hy.1
  have hθ : (A.chart j).symm y ∈ R.th.U x := hy.2.1.1
  have hY : (A.chart j).symm y ∈ R.Yo := hy.2.2
  obtain ⟨k, hk⟩ := R.cover ((A.chart j).symm y)
  have hks := R.toPotentialCharts.mid_subset_source k (R.inner_subset_mid k hk)
  have hξ : R.chart k ((A.chart j).symm y) ∈
      (R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k) :=
    ⟨(R.chart k).map_source hks, (R.mem_Yo k _ hks).1 hY⟩
  have hUo : IsOpen ((R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k)) :=
    (R.chart k).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have hC2 : ContDiffOn ℝ 2 (R.u k) ((R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k)) :=
    fun ξ hξ => (RegChartData.contDiffAt_u R k hξ).contDiffWithinAt
  have hL := ((ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm _ _ _ hUo hC2).1 (R.u_psh k)).2
  have hcf : ContDiffAt ℝ 2 (R.chartFun R.ph k) (R.chart k ((A.chart j).symm y)) :=
    RegChartData.contDiffAt_u R k hξ
  have h := (levi_th_add_chart R.toPotentialCharts R.ph x j k w hyt hθ hks hcf).2
  change 0 ≤ levi ((fun z => R.th.φ x z + R.ph z) ∘ (A.chart j).symm) y w
  rw [h]
  exact hL _ hξ _

theorem exists_isPsh_of_chart_bound [CompactSpace X] (P : PotentialCharts A) (Θ : LocPot X)
    (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    ∃ c : Fin P.N → ℝ, (∀ k, 0 < c k) ∧ ∀ (f : X → ℝ) (a ε : ℝ), A.Smooth f → 0 ≤ ε →
      (∀ k : Fin P.N, ∀ x ∈ P.mid k, ∀ w : Fin D → ℂ,
        -a * ‖w‖ ^ 2 ≤ levi (P.chartFun f k) (P.chart k x) w) →
      (∀ k, a ≤ ε * c k) → IsPsh A (P.th + LocPot.ofFun f + Θ.rsmul ε) := by
  have hc : ∀ k : Fin P.N, ∃ c : ℝ, 0 < c ∧ ∀ p ∈ closure (P.mid k), ∀ x, p ∈ Θ.U x →
      ∀ v : Fin D → ℂ, c * ‖v‖ ^ 2 ≤ levi (Θ.φ x ∘ (P.chart k).symm) (P.chart k p) v := fun k =>
    exists_levi_lower hΘ hpos (P.compat k) isClosed_closure.isCompact (P.closure_mid k)
  choose c hc0 hc using hc
  refine ⟨c, hc0, fun f a ε hf hε hlev hac x j y hy w => ?_⟩
  have hyt : y ∈ (A.chart j).target := hy.1
  have hθ : (A.chart j).symm y ∈ P.th.U x := hy.2.1.1
  have hΘx : (A.chart j).symm y ∈ Θ.U x := hy.2.2
  have hpA : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyt
  obtain ⟨k, hk⟩ := P.cover ((A.chart j).symm y)
  have hkm := P.inner_subset_mid k hk
  have hks := P.mid_subset_source k hkm
  have hcf : ContDiffAt ℝ 2 (P.chartFun f k) (P.chart k ((A.chart j).symm y)) := by
    have hq : ContDiffAt ℝ 2 (P.q k) (P.chart k ((A.chart j).symm y)) :=
      ((P.q_smooth k).contDiffAt ((P.chart k).open_target.mem_nhds
        ((P.chart k).map_source hks))).of_le (WithTop.coe_le_coe.2 le_top)
    exact hq.add (contDiffAt_comp_symm isOpen_univ hf (P.compat k) (Set.mem_univ _) hks)
  obtain ⟨hF, hFl⟩ := levi_th_add_chart P f x j k w hyt hθ hks hcf
  have hG : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y := by
    have := contDiffAt_comp_symm (Θ.isOpen_U x) (hΘ.1 x) (compat_chart A j) hΘx hpA
    rwa [(A.chart j).right_inv hyt] at this
  have hg := analyticAt_transition P j k hyt hks
  have hGl : levi (Θ.φ x ∘ (A.chart j).symm) y w =
      levi (Θ.φ x ∘ (P.chart k).symm) (P.chart k ((A.chart j).symm y))
        (fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w) := by
    have hev := eventuallyEq_comp_chart (Θ.φ x) (P.chart k) (A.chart j) hyt hks
    have hcd : ContDiffAt ℝ 2 (Θ.φ x ∘ (P.chart k).symm) ((P.chart k ∘ (A.chart j).symm) y) :=
      contDiffAt_comp_symm (Θ.isOpen_U x) (hΘ.1 x) (P.compat k) hΘx hks
    rw [levi_congr hev w, levi_comp w hg hcd]
    rfl
  change 0 ≤ levi (fun y' => ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y' +
    ε * (Θ.φ x ∘ (A.chart j).symm) y') y w
  rw [levi_add_smul ε hF hG w, hFl, hGl]
  set v := fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w
  have h1 := hlev k _ hkm v
  have h2 := hc k _ (subset_closure hkm) x hΘx v
  have h3 := mul_le_mul_of_nonneg_left h2 hε
  have h4 := mul_le_mul_of_nonneg_right (hac k) (sq_nonneg ‖v‖)
  nlinarith

end Charts

theorem tied_regularisation_weak : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B) (Θ : LocPot M.Xc), S.IsTied → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → ReciprocityTheory.AnForm.P.IsPshOn M.atlas S.R.Yo (S.R.th + LocPot.ofFun S.R.ph) ∧ (∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧ ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x ∧ S.regWeight t x ≤ C) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsPsh M.atlas (S.R.th + LocPot.ofFun (S.regWeight t) + Θ.rsmul ε) := by
  intro K _ ι _ P n M Xo B S Θ hS hΘ hpos
  obtain ⟨C₀, t₀, ht₀, hb⟩ := GroundTheory.Heights₂.Heights.Regular.ChartMollifiedBounds.proof
    GroundTheory.Heights₂.Heights.Regular.TruncPsh.proof M.Xc n M.atlas S.R S.ρ
  refine ⟨isPshOn_th_ph S.R, ⟨C₀ + 1, ?_⟩, fun ε hε => ?_⟩
  · filter_upwards [S.eventually_chartLevi hS, self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀),
      hS.K_tendsto.eventually_ge_atTop 0,
      hS.e1_tendsto_zero.eventually (eventually_le_nhds one_pos)] with t hsm ht htt hK he
    have ht0 : (0 : ℝ) < t := ht
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    refine ⟨hsm.1, fun x hx => ⟨?_, ?_⟩⟩
    · obtain ⟨k, hk⟩ := S.R.cover x
      have hkm := S.R.inner_subset_mid k hk
      have h1 := ((hb t ht0 htt).2 (S.K t) hK k x hkm).2.2 hx
      have h2 := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.le_glue S.R.toPotentialCharts
        (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 hkm
      have h3 : S.regWeight t x = S.R.glue
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := rfl
      have hη := S.cutoff.eq_zero k x hk
      simp only [hη, mul_zero, add_zero] at h2
      rw [h3]
      linarith
    · have hg := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.glue_le S.R.toPotentialCharts
        (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 (c := C₀) (x := x)
        fun j hj => by
          have h1 := ((hb t ht0 htt).2 (S.K t) hK j x hj).2.1
          have h2 := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * S.e1 t)
            (S.cutoff.bounds j x hj).2
          show S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x ≤ C₀
          linarith
      have h3 : S.regWeight t x = S.R.glue
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := rfl
      rw [h3]
      linarith
  · obtain ⟨c, hc0, hc⟩ := exists_isPsh_of_chart_bound S.R.toPotentialCharts Θ hΘ hpos
    have hlim : Tendsto (fun t => 4 * S.Cη * S.e1 t) (𝓝[>] 0) (𝓝 0) := by
      simpa using hS.e1_tendsto_zero.const_mul (4 * S.Cη)
    have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, 4 * S.Cη * S.e1 t ≤ ε * c k :=
      Filter.eventually_all.2 fun k =>
        hlim.eventually (eventually_le_nhds (mul_pos hε (hc0 k)))
    filter_upwards [S.eventually_chartLevi hS, hall] with t ht hle
    exact hc (S.regWeight t) (4 * S.Cη * S.e1 t) ε ht.1 hε.le ht.2 hle

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBoundsStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_weight_psh_and_bounds : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B) (Θ : LocPot M.Xc), S.IsTied → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → ReciprocityTheory.AnForm.P.IsPshOn M.atlas S.R.Yo (S.R.th + LocPot.ofFun S.R.ph) ∧ (∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧ ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x ∧ S.regWeight t x ≤ C) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsPsh M.atlas (S.R.th + LocPot.ofFun (S.regWeight t) + Θ.rsmul ε) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tied_regularisation_weak | exact GlobalTheory.CompanionTheory.Ar.Giv.tied_regularisation_weak | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tied_regularisation_weak <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDrop
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDrop
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flag_isArithVar_and_image : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) ∧ ∀ q₀ : FlBlock Ψ N, Nonempty {q : FlBlock Ψ N // q ≠ q₀} → ∃ d₀ < antisymDegree Ψ N + 1, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (imageZ (fun p : Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1 => (⟨p.1.1, p.2⟩ : Σ q, FlIdx Ψ N q)) (PFl Ψ N)) d₀ :=
  @PositivityTheory.Xgp.t_fl_arith

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDropStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_boundary_dimension_drop : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) ∧ ∀ q₀ : FlBlock Ψ N, Nonempty {q : FlBlock Ψ N // q ≠ q₀} → ∃ d₀ < antisymDegree Ψ N + 1, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (imageZ (fun p : Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1 => (⟨p.1.1, p.2⟩ : Σ q, FlIdx Ψ N q)) (PFl Ψ N)) d₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image | exact GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeEstimate
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeEstimate
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = pPhi M F keep v bl h ε w ∧ basePart M.blk z = bl (pB ε w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hctx w hw
  have hT := GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hctx w hw
  have hc2 := hctx
  unfold GlobalTheory.CompanionTheory.Ar.PB.PFl.IsPCtx at hc2
  obtain ⟨-, -, hframe, hchart, -⟩ := hc2
  unfold GlobalTheory.CompanionTheory.Ar.PB.WMan.IsBaseChart at hchart
  have hwV : pB ε w ∈ V := hw
  obtain ⟨hmem, hnorm, hgood, -⟩ := hchart.2.2.2.2 (pB ε w) hwV
  have hbase : basePart M.blk (GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w)) =
      bl (pB ε w) := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    unfold GlobalTheory.CompanionTheory.Ar.PB.basePart GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ
    split
    next hex => exact absurd hex (fun ⟨p, hp⟩ => hk p hp)
    next hex => rfl
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w), ?_, rfl, hbase⟩
  have hmain := (GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M).2.2 F hframe
    (GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w))
    (by rw [hbase]; exact hmem) (by rw [hbase]; exact hgood) (by rw [hbase]; exact hnorm)
  refine hmain.2 ⟨fun τ => pH keep h ε τ w, ?_⟩
  refine ⟨fun k => by rw [hbase]; exact hnorm k, fun τ => hT.1 τ, ?_⟩
  intro p k hp
  refine ⟨1, one_ne_zero, fun m => ?_⟩
  rw [one_mul, hbase]
  unfold GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ
  split
  next hex =>
    have hc : hex.choose = p := M.blk_inj _ _ k hex.choose_spec hp
    rw [hc]
  next hex => exact absurd ⟨p, hp⟩ hex

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeEstimateStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_degree_estimate : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = pPhi M F keep v bl h ε w ∧ basePart M.blk z = bl (pB ε w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeEqGeometricDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeEqGeometricDegree
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem genDegGeomDeg_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement :=
  fun hI _ => GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.proof
    (degreeGeneric_of_degree (degree_of_system hI))

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeEqGeometricDegreeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_eq_geometric_degree : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricRowEchelonLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricRowEchelonLocal
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem stepCols_ne_empty_of_le {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hN := i.2
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have hlt : N - j < N := by omega
    have hm : (⟨N - j, hlt⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      omega
    rw [e] at hm
    simp at hm
  · have hlt : 0 < N := by omega
    have hm : (⟨0, hlt⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      omega
    rw [e] at hm
    simp at hm

theorem exists_plk_ne_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → ∃ I₀, IsStepRows N j p.2 I₀ ∧ plk M (BM.F l) k₀ z I₀ ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z hp hx hz hO
  obtain ⟨h, a, hb, -, ha, hpl, hzk⟩ := GlobalTheory.T.block_metric_grassmann_chart_local K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hx hz hO
  by_contra hcon
  push_neg at hcon
  have hmin : ∀ I, minorIJ h I (stepCols N j p.2) = 0 := fun I => by
    by_cases hI : IsStepRows N j p.2 I
    · have e := hpl I hI
      rw [hcon I hI] at e
      exact (mul_eq_zero.1 e.symm).resolve_left ha
    · exact ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 h I hb hI).resolve_right
        (stepCols_ne_empty_of_le M.j_le p.2)
  obtain ⟨m, hm⟩ := hz.1 k₀
  exact hm (by rw [hzk m]; simp [hmin])

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricRowEchelonLocalStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_metric_row_echelon_local : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → ∃ I₀, IsStepRows N j p.2 I₀ ∧ plk M (BM.F l) k₀ z I₀ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.exists_plk_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.exists_plk_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.exists_plk_ne_zero <;> assumption)
end
end
